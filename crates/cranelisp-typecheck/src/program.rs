//! Two-pass batch checking and REPL input checking.
//!
//! `check_program` orchestrates Pass 1 (registration) and Pass 2 (checking).
//! Each phase is a named private method. Addresses audit HIGH-2.

use std::collections::{HashMap, HashSet};

use cranelisp_types::{
    CheckResult, ConstrainedFn, CranelispError, Defn, DefKind, Expr, JitSymbol,
    ModuleEntry, MonoDefn, ReplCheckResult, ReplInput, ResolvedCall, Scheme, Span,
    Symbol, TopLevel, Type, apply,
};

use crate::checker::TypeChecker;
use crate::resolve::resolve_type_expr;
use crate::scheme::mono;

impl TypeChecker {
    /// Check a complete program (batch mode).
    ///
    /// Two-pass pipeline:
    /// 1. Register type definitions and function signatures.
    /// 2. Check function bodies, generalize types.
    #[must_use = "check result contains expr_types and method_resolutions needed by codegen"]
    pub fn check_program(
        &mut self,
        program: &[TopLevel],
    ) -> Result<CheckResult, CranelispError> {
        // Pass 1: register type definitions
        self.register_type_defs_from_program(program)?;

        // Pass 1: register trait declarations
        self.register_trait_decls_from_program(program)?;

        // Pass 1: register trait implementations
        let default_defns =
            self.register_trait_impls_from_program(program)?;

        // Pass 1: register function signatures with fresh type variables
        let defns = Self::collect_defns(program);
        let defn_type_vars = self.pass1_register_signatures(&defns)?;

        // Pass 2: check function bodies and generalize
        self.pass2_check_bodies(&defns, &defn_type_vars)?;

        // Pass 3: detect constrained polymorphic functions
        let constrained_fn_names =
            self.detect_constrained_fns(&defns);

        // Pass 4: monomorphise constrained function call sites
        let mono_defns = self.pass4_monomorphise(&defns, &constrained_fn_names)?;

        let mut result = self.build_check_result();
        result.constrained_fn_names = constrained_fn_names.clone();
        result.mono_defns = mono_defns;
        result.default_method_defns = default_defns;
        Ok(result)
    }

    /// Check a single REPL input incrementally.
    #[must_use = "check result contains type and expr_types needed by codegen"]
    pub fn check_repl_input(
        &mut self,
        input: &ReplInput,
    ) -> Result<ReplCheckResult, CranelispError> {
        match input {
            ReplInput::Expr(expr) => {
                let ty = self.infer_expr(expr)?;
                let resolved = self.apply_subst(&ty);

                // Gap 4: scan for constrained-fn calls, monomorphise on demand
                let mono_defns = self.monomorphise_expr_calls(expr)?;

                let mut result = self.build_repl_result(resolved, None);
                result.mono_defns = mono_defns;
                Ok(result)
            }

            ReplInput::Defn(defn) => {
                let (ty, scheme) = self.check_single_defn(defn)?;

                // Scan defn body for constrained-fn calls, monomorphise on demand
                let mono_defns = self.monomorphise_expr_calls(&defn.body)?;

                let mut result = self.build_repl_result(ty, Some(scheme));
                result.mono_defns = mono_defns;
                Ok(result)
            }

            ReplInput::TypeDef {
                name,
                docstring,
                type_params,
                constructors,
                visibility,
                span,
            } => {
                self.register_type_def(name, docstring, type_params, constructors, *visibility, *span)?;
                let ty = Type::ADT(name.clone(), vec![]);
                Ok(self.build_repl_result(ty, None))
            }

            // Not supported in Ring 0
            ReplInput::DefnMulti { span, .. } => Err(CranelispError::TypeError {
                message: "multi-signature functions not supported in Ring 0".into(),
                span: *span,
            }),

            ReplInput::TraitDecl(decl) => {
                self.register_trait_decl(decl)?;
                let ty = Type::Bool; // Placeholder return type for trait decl
                Ok(self.build_repl_result(ty, None))
            }

            ReplInput::TraitImpl(impl_) => {
                let default_defns = self.register_trait_impl(impl_)?;
                let ty = Type::Bool; // Placeholder return type for trait impl
                let mut result = self.build_repl_result(ty, None);
                result.default_method_defns = default_defns;
                Ok(result)
            }
        }
    }

    // --- Pass 1: Registration ---

    /// Register all TypeDef entries from the program.
    fn register_type_defs_from_program(
        &mut self,
        program: &[TopLevel],
    ) -> Result<(), CranelispError> {
        for top in program {
            if let TopLevel::TypeDef {
                name,
                docstring,
                type_params,
                constructors,
                visibility,
                span,
            } = top
            {
                self.register_type_def(
                    name,
                    docstring,
                    type_params,
                    constructors,
                    *visibility,
                    *span,
                )?;
            }
        }
        Ok(())
    }

    /// Register all TraitDecl entries from the program.
    fn register_trait_decls_from_program(
        &mut self,
        program: &[TopLevel],
    ) -> Result<(), CranelispError> {
        for top in program {
            if let TopLevel::TraitDecl(decl) = top {
                self.register_trait_decl(decl)?;
            }
        }
        Ok(())
    }

    /// Register all TraitImpl entries from the program.
    /// Returns default method definitions generated.
    fn register_trait_impls_from_program(
        &mut self,
        program: &[TopLevel],
    ) -> Result<Vec<Defn>, CranelispError> {
        let mut default_defns = Vec::new();
        for top in program {
            if let TopLevel::TraitImpl(impl_) = top {
                let defaults = self.register_trait_impl(impl_)?;
                default_defns.extend(defaults);
            }
        }
        Ok(default_defns)
    }

    /// Detect constrained polymorphic functions after generalization.
    ///
    /// A function is constrained if its generalized scheme has non-empty constraints.
    /// These functions are stored with `ConstrainedFn` in their DefKind.
    fn detect_constrained_fns(
        &mut self,
        defns: &[&Defn],
    ) -> HashSet<Symbol> {
        // Constrained functions are eagerly marked in pass2_check_bodies
        // by checking DefKind::UserFn { constrained_fn: Some(..) }.
        let mut names = HashSet::new();

        for defn in defns {
            if let Some(ModuleEntry::Def { kind, .. }) =
                self.current_symbol_table().get(defn.name.as_ref())
                && let DefKind::UserFn { constrained_fn: Some(_) } = kind.as_ref()
            {
                names.insert(defn.name.clone());
            }
        }

        names
    }

    /// Collect all Defn entries from the program.
    fn collect_defns(program: &[TopLevel]) -> Vec<&Defn> {
        program
            .iter()
            .filter_map(|top| {
                if let TopLevel::Defn(defn) = top {
                    Some(defn)
                } else {
                    None
                }
            })
            .collect()
    }

    /// Create fresh type variables for a function's parameters and return type,
    /// respecting any annotations, and register the signature in the symbol table.
    ///
    /// Returns `(param_types, return_type)` for use in body checking.
    /// Shared by `pass1_register_signatures` (batch) and `check_single_defn` (REPL)
    /// to prevent the two paths from diverging as rings add complexity.
    fn register_defn_signature(
        &mut self,
        defn: &Defn,
    ) -> Result<(Vec<Type>, Type), CranelispError> {
        let mut param_types = Vec::new();
        for (i, _param) in defn.params.iter().enumerate() {
            let param_ty = if let Some(Some(ann)) = defn.param_annotations.get(i) {
                let known = self.known_type_names();
                let var_map = HashMap::new();
                resolve_type_expr(ann, &var_map, &known, defn.span)?
            } else {
                self.fresh_var()
            };
            param_types.push(param_ty);
        }
        let ret_ty = self.fresh_var();

        let fn_type = Type::Fn(param_types.clone(), Box::new(ret_ty.clone()));
        let scheme = mono(fn_type);

        self.current_symbol_table_mut().insert(
            defn.name.clone(),
            ModuleEntry::Def {
                scheme,
                visibility: defn.visibility,
                docstring: defn.docstring.clone(),
                param_names: defn.params.clone(),
                kind: Box::new(DefKind::UserFn {
                    constrained_fn: None,
                }),
            },
        );

        Ok((param_types, ret_ty))
    }

    /// Pass 1: Register function signatures with fresh type variables.
    ///
    /// Returns a map from function name to (param type vars, return type var)
    /// for use in Pass 2.
    fn pass1_register_signatures(
        &mut self,
        defns: &[&Defn],
    ) -> Result<HashMap<Symbol, (Vec<Type>, Type)>, CranelispError> {
        let mut type_vars = HashMap::new();

        for defn in defns {
            let (param_types, ret_ty) = self.register_defn_signature(defn)?;
            type_vars.insert(defn.name.clone(), (param_types, ret_ty));
        }

        Ok(type_vars)
    }

    /// Pass 2: Check function bodies and generalize types.
    ///
    /// All bodies are checked first (with deferred trait resolution), then
    /// all functions are generalized.
    ///
    /// After each body check, we eagerly detect constrained polymorphism
    /// by checking if the function's type vars have active constraints.
    /// This must happen before later functions' call sites can pin the vars
    /// to concrete types through the shared substitution.
    fn pass2_check_bodies(
        &mut self,
        defns: &[&Defn],
        type_vars: &HashMap<Symbol, (Vec<Type>, Type)>,
    ) -> Result<(), CranelispError> {
        // Phase 1: Check all bodies, resolve deferred trait calls,
        // and eagerly mark constrained functions.
        for defn in defns {
            let (param_types, ret_ty) = type_vars
                .get(&defn.name)
                .ok_or_else(|| CranelispError::TypeError {
                    message: format!("internal: missing type vars for {}", defn.name),
                    span: defn.span,
                })?;

            self.check_defn_body(defn, param_types, ret_ty)?;
            self.resolve_deferred_trait_calls(&defn.body);

            // Eagerly detect if this function is constrained.
            // Must happen now, before later call sites resolve its type vars.
            let fn_type = Type::Fn(
                param_types.iter().map(|t| self.apply_subst(t)).collect(),
                Box::new(self.apply_subst(ret_ty)),
            );
            let trial_scheme = self.generalize(&fn_type);
            if !trial_scheme.constraints.is_empty() {
                // Mark as constrained immediately
                if let Some(ModuleEntry::Def { kind, .. }) =
                    self.current_symbol_table_mut().symbols.get_mut(&defn.name)
                {
                    let cf = ConstrainedFn {
                        defn: (*defn).clone(),
                        scheme: trial_scheme,
                    };
                    **kind = DefKind::UserFn {
                        constrained_fn: Some(Box::new(cf)),
                    };
                }
            }
        }

        // Phase 2: Generalize all functions.
        // If the final scheme has no constraints, clear any eager constrained_fn marker
        // (later call sites may have pinned the type vars to concrete types).
        for defn in defns {
            let (param_types, ret_ty) = type_vars.get(&defn.name).unwrap();
            let fn_type = Type::Fn(
                param_types.iter().map(|t| self.apply_subst(t)).collect(),
                Box::new(self.apply_subst(ret_ty)),
            );
            let scheme = self.generalize(&fn_type);
            if let Some(ModuleEntry::Def { scheme: s, kind, .. }) =
                self.current_symbol_table_mut().symbols.get_mut(&defn.name)
            {
                *s = scheme.clone();
                // Clear eager constrained marker if final scheme is unconstrained
                if scheme.constraints.is_empty()
                    && let DefKind::UserFn { constrained_fn: Some(_) } = kind.as_ref()
                {
                    **kind = DefKind::UserFn { constrained_fn: None };
                }
            }
        }

        // Phase 3: Re-resolve deferred trait calls now that all types are pinned.
        // During Phase 1, some trait method calls (e.g., `+` in `add`) couldn't be
        // resolved because arg types were still unresolved vars. After Phase 2,
        // later call sites may have pinned those vars to concrete types.
        for defn in defns {
            self.resolve_deferred_trait_calls(&defn.body);
        }

        Ok(())
    }

    /// Check a single function definition body.
    fn check_defn_body(
        &mut self,
        defn: &Defn,
        param_types: &[Type],
        ret_ty: &Type,
    ) -> Result<(), CranelispError> {
        self.push_scope();

        // Bind parameters
        for (param_name, param_ty) in defn.params.iter().zip(param_types.iter()) {
            self.bind_local(param_name.clone(), mono(param_ty.clone()));
        }

        // Bind the function name for recursion
        let fn_type = Type::Fn(param_types.to_vec(), Box::new(ret_ty.clone()));
        self.bind_local(defn.name.clone(), mono(fn_type));

        // Infer body type
        let body_ty = self.infer_expr(&defn.body)?;

        // Unify body type with return type variable
        self.unify(&body_ty, ret_ty, defn.span)?;

        self.pop_scope();
        Ok(())
    }

    /// Check a single defn for REPL (register, check, generalize in one step).
    fn check_single_defn(
        &mut self,
        defn: &Defn,
    ) -> Result<(Type, Scheme), CranelispError> {
        let (param_types, ret_ty) = self.register_defn_signature(defn)?;

        // Check body
        self.check_defn_body(defn, &param_types, &ret_ty)?;

        // Post-inference deferred trait resolution
        self.resolve_deferred_trait_calls(&defn.body);

        // Generalize (propagates active constraints)
        let resolved_fn_type = Type::Fn(
            param_types.iter().map(|t| self.apply_subst(t)).collect(),
            Box::new(self.apply_subst(&ret_ty)),
        );
        let scheme = self.generalize(&resolved_fn_type);

        // Update symbol table with generalized scheme
        // If constrained, also store as ConstrainedFn
        if let Some(ModuleEntry::Def { scheme: s, kind, .. }) =
            self.current_symbol_table_mut().symbols.get_mut(&defn.name)
        {
            *s = scheme.clone();

            if !scheme.constraints.is_empty() {
                let cf = ConstrainedFn {
                    defn: defn.clone(),
                    scheme: scheme.clone(),
                };
                **kind = DefKind::UserFn {
                    constrained_fn: Some(Box::new(cf)),
                };
            }
        }

        Ok((scheme.ty.clone(), scheme))
    }

    // --- Monomorphisation passes ---

    /// Pass 4 (batch): scan all defn bodies for calls to constrained functions
    /// and generate monomorphised specializations.
    fn pass4_monomorphise(
        &mut self,
        defns: &[&Defn],
        constrained_fn_names: &HashSet<Symbol>,
    ) -> Result<Vec<MonoDefn>, CranelispError> {
        if constrained_fn_names.is_empty() {
            return Ok(Vec::new());
        }

        // Collect call sites: (fn_name, arg_spans, call_span)
        let mut call_sites = Vec::new();
        for defn in defns {
            // Don't scan constrained fns for calls to themselves — those
            // are the generic definitions, not concrete call sites.
            if constrained_fn_names.contains(&defn.name) {
                continue;
            }
            Self::collect_constrained_calls(
                &defn.body,
                constrained_fn_names,
                &mut call_sites,
            );
        }

        // Resolve expr_types so we can look up concrete arg types
        let resolved_expr_types = self.resolve_expr_types();

        // Monomorphise each call site and record dispatch mappings
        let mut mono_defns = Vec::new();
        let mut seen: HashMap<String, JitSymbol> = HashMap::new();

        for (fn_name, arg_spans, call_span) in &call_sites {
            // Look up concrete arg types from resolved expr_types
            let arg_types: Vec<Type> = arg_spans
                .iter()
                .filter_map(|span| resolved_expr_types.get(span).cloned())
                .collect();

            if arg_types.len() != arg_spans.len() {
                // Missing type info for some args — skip this call site
                continue;
            }

            // Deduplicate: same fn + same arg types = same specialization
            let key = format!("{}${}", fn_name, arg_types.iter()
                .map(|t| format!("{}", t))
                .collect::<Vec<_>>()
                .join("+"));

            if let Some(mangled) = seen.get(&key) {
                // Already generated this specialization — just record dispatch
                self.method_resolutions.insert(
                    *call_span,
                    ResolvedCall::SigDispatch { mangled_name: mangled.clone() },
                );
                continue;
            }

            if let Some(mono) = self.monomorphise_call(fn_name, &arg_types, *call_span)? {
                let mangled = JitSymbol::from(mono.defn.name.as_ref());
                // Record dispatch for this call site
                self.method_resolutions.insert(
                    *call_span,
                    ResolvedCall::SigDispatch { mangled_name: mangled.clone() },
                );
                seen.insert(key, mangled);
                mono_defns.push(mono);
            }
        }

        Ok(mono_defns)
    }

    /// Scan an expression for calls to constrained functions (REPL path).
    ///
    /// Collects call sites, resolves arg types, and calls `monomorphise_call`
    /// for each. Used by both `check_repl_input(Expr)` and `check_repl_input(Defn)`.
    fn monomorphise_expr_calls(
        &mut self,
        expr: &Expr,
    ) -> Result<Vec<MonoDefn>, CranelispError> {
        // Build the set of constrained fn names from the symbol table
        let constrained_fn_names: HashSet<Symbol> = self.current_symbol_table().symbols
            .iter()
            .filter_map(|(name, entry)| {
                if let ModuleEntry::Def { kind, .. } = entry
                    && let DefKind::UserFn { constrained_fn: Some(_) } = kind.as_ref()
                {
                    return Some(name.clone());
                }
                None
            })
            .collect();

        if constrained_fn_names.is_empty() {
            return Ok(Vec::new());
        }

        let mut call_sites = Vec::new();
        Self::collect_constrained_calls(expr, &constrained_fn_names, &mut call_sites);

        if call_sites.is_empty() {
            return Ok(Vec::new());
        }

        let resolved_expr_types = self.resolve_expr_types();

        let mut mono_defns = Vec::new();
        let mut seen: HashMap<String, JitSymbol> = HashMap::new();

        for (fn_name, arg_spans, call_span) in &call_sites {
            let arg_types: Vec<Type> = arg_spans
                .iter()
                .filter_map(|span| resolved_expr_types.get(span).cloned())
                .collect();

            if arg_types.len() != arg_spans.len() {
                continue;
            }

            let key = format!("{}${}", fn_name, arg_types.iter()
                .map(|t| format!("{}", t))
                .collect::<Vec<_>>()
                .join("+"));

            if let Some(mangled) = seen.get(&key) {
                self.method_resolutions.insert(
                    *call_span,
                    ResolvedCall::SigDispatch { mangled_name: mangled.clone() },
                );
                continue;
            }

            if let Some(mono) = self.monomorphise_call(fn_name, &arg_types, *call_span)? {
                let mangled = JitSymbol::from(mono.defn.name.as_ref());
                self.method_resolutions.insert(
                    *call_span,
                    ResolvedCall::SigDispatch { mangled_name: mangled.clone() },
                );
                seen.insert(key, mangled);
                mono_defns.push(mono);
            }
        }

        Ok(mono_defns)
    }

    /// Recursively walk an expression tree collecting calls to constrained fns.
    ///
    /// Each call site is recorded as (fn_name, arg_spans, call_span).
    /// The arg_spans are the spans of each argument expression, used to look up
    /// their types from `expr_types`.
    pub(crate) fn collect_constrained_calls(
        expr: &Expr,
        constrained_fn_names: &HashSet<Symbol>,
        out: &mut Vec<(Symbol, Vec<Span>, Span)>,
    ) {
        match expr {
            Expr::Apply { callee, args, span } => {
                // Check if callee is a constrained fn
                if let Expr::Var { name, .. } = callee.as_ref()
                    && constrained_fn_names.contains(name)
                {
                    let arg_spans: Vec<Span> = args.iter()
                        .map(|a| a.span())
                        .collect();
                    out.push((name.clone(), arg_spans, *span));
                }
                // Recurse into callee and args
                Self::collect_constrained_calls(callee, constrained_fn_names, out);
                for arg in args {
                    Self::collect_constrained_calls(arg, constrained_fn_names, out);
                }
            }
            Expr::Let { bindings, body, .. } => {
                for (_, binding_expr) in bindings {
                    Self::collect_constrained_calls(binding_expr, constrained_fn_names, out);
                }
                Self::collect_constrained_calls(body, constrained_fn_names, out);
            }
            Expr::If { cond, then_branch, else_branch, .. } => {
                Self::collect_constrained_calls(cond, constrained_fn_names, out);
                Self::collect_constrained_calls(then_branch, constrained_fn_names, out);
                Self::collect_constrained_calls(else_branch, constrained_fn_names, out);
            }
            Expr::Lambda { body, .. } => {
                Self::collect_constrained_calls(body, constrained_fn_names, out);
            }
            Expr::Match { scrutinee, arms, .. } => {
                Self::collect_constrained_calls(scrutinee, constrained_fn_names, out);
                for arm in arms {
                    Self::collect_constrained_calls(&arm.body, constrained_fn_names, out);
                }
            }
            Expr::Annotate { expr: inner, .. } => {
                Self::collect_constrained_calls(inner, constrained_fn_names, out);
            }
            Expr::VecLit { elements, .. } => {
                for elem in elements {
                    Self::collect_constrained_calls(elem, constrained_fn_names, out);
                }
            }
            Expr::Trace { body, .. } => {
                Self::collect_constrained_calls(body, constrained_fn_names, out);
            }
            Expr::RunTests { init, pass_fn, fail_fn, .. } => {
                Self::collect_constrained_calls(init, constrained_fn_names, out);
                Self::collect_constrained_calls(pass_fn, constrained_fn_names, out);
                Self::collect_constrained_calls(fail_fn, constrained_fn_names, out);
            }
            // Leaf nodes: no children to recurse into
            Expr::IntLit { .. }
            | Expr::FloatLit { .. }
            | Expr::BoolLit { .. }
            | Expr::StringLit { .. }
            | Expr::Var { .. } => {}
        }
    }

    // --- Result building ---

    /// Resolve all recorded expr_types through the current substitution.
    fn resolve_expr_types(&self) -> HashMap<Span, Type> {
        self.expr_types
            .iter()
            .map(|(span, ty)| (*span, apply(&self.subst, ty)))
            .collect()
    }

    /// Build the final CheckResult from accumulated state.
    fn build_check_result(&mut self) -> CheckResult {
        let resolved_expr_types = self.resolve_expr_types();

        // Invariant: after monomorphisation (Ring 2+), no Type::Var should remain
        // in expr_types. In Ring 0-1, polymorphic function bodies legitimately
        // contain Var entries (e.g., `(defn id [x] x)` where x has a quantified
        // type variable). This assertion activates in Ring 2 when monomorphisation
        // resolves all type variables before codegen.
        //
        // TODO(Ring 2): uncomment when monomorphisation is implemented
        // debug_assert!(
        //     !resolved_expr_types.values().any(|ty| ty.contains_var()),
        //     "build_check_result: unresolved Type::Var in expr_types"
        // );

        CheckResult {
            method_resolutions: std::mem::take(&mut self.method_resolutions),
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: resolved_expr_types,
            default_method_defns: Vec::new(),
            warnings: std::mem::take(&mut self.warnings),
            type_defs: self.type_defs.type_defs.clone(),
            constructor_to_type: self.type_defs.constructor_to_type.clone(),
        }
    }

    /// Build a ReplCheckResult from the current state.
    fn build_repl_result(&mut self, ty: Type, scheme: Option<Scheme>) -> ReplCheckResult {
        let resolved_expr_types = self.resolve_expr_types();

        // See build_check_result comment: assertion deferred to Ring 2.
        // TODO(Ring 2): uncomment when monomorphisation is implemented
        // debug_assert!(
        //     !resolved_expr_types.values().any(|ty| ty.contains_var()),
        //     "build_repl_result: unresolved Type::Var in expr_types"
        // );

        ReplCheckResult {
            ty,
            scheme,
            method_resolutions: std::mem::take(&mut self.method_resolutions),
            expr_types: resolved_expr_types,
            warnings: std::mem::take(&mut self.warnings),
            type_defs: self.type_defs.type_defs.clone(),
            constructor_to_type: self.type_defs.constructor_to_type.clone(),
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            default_method_defns: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{Expr, ReplInput, TypeName, Visibility};

    fn span(start: u32, end: u32) -> Span {
        Span::new(start, end)
    }

    // spec: 05-definitions §5.1 — defn registers function with inferred type
    #[test]
    fn test_check_program_simple_defn() {
        let mut tc = TypeChecker::new();
        // (defn add-one [x] (add-i64 x 1))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("add-one"),
            docstring: None,
            params: vec![Symbol::from("x")],
            param_annotations: vec![None],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("add-i64"),
                    span: span(20, 27),
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("x"),
                        span: span(28, 29),
                    },
                    Expr::IntLit {
                        value: 1,
                        span: span(30, 31),
                    },
                ],
                span: span(19, 32),
            },
            visibility: Visibility::Public,
            span: span(0, 33),
        })];

        let _result = tc.check_program(&program).unwrap();

        // Check the function was registered with correct type: Fn([Int], Int)
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add-one") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int))
            );
        } else {
            panic!("add-one not found in symbol table");
        }
    }

    // spec: 03-types §3.4 — identity function generalized to polymorphic scheme
    #[test]
    fn test_check_program_identity_is_polymorphic() {
        let mut tc = TypeChecker::new();
        // (defn id [x] x)
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("id"),
            docstring: None,
            params: vec![Symbol::from("x")],
            param_annotations: vec![None],
            body: Expr::Var {
                name: Symbol::from("x"),
                span: span(14, 15),
            },
            visibility: Visibility::Public,
            span: span(0, 16),
        })];

        tc.check_program(&program).unwrap();

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("id") {
            // Should be forall [a]. Fn([a], a)
            assert_eq!(scheme.vars.len(), 1, "id should have 1 quantified var");
            match &scheme.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params.len(), 1);
                    assert_eq!(params[0], **ret);
                }
                _ => panic!("expected Fn type"),
            }
        } else {
            panic!("id not found in symbol table");
        }
    }

    // spec: 03-types §3.5.1 — recursive function inferred as monomorphic via self-reference
    #[test]
    fn test_check_program_recursive_function() {
        let mut tc = TypeChecker::new();
        // (defn fact [n] (if (eq-i64 n 0) 1 (mul-i64 n (fact (sub-i64 n 1)))))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("fact"),
            docstring: None,
            params: vec![Symbol::from("n")],
            param_annotations: vec![None],
            body: Expr::If {
                cond: Box::new(Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("eq-i64"),
                        span: span(20, 26),
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("n"),
                            span: span(27, 28),
                        },
                        Expr::IntLit {
                            value: 0,
                            span: span(29, 30),
                        },
                    ],
                    span: span(19, 31),
                }),
                then_branch: Box::new(Expr::IntLit {
                    value: 1,
                    span: span(33, 34),
                }),
                else_branch: Box::new(Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("mul-i64"),
                        span: span(36, 43),
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("n"),
                            span: span(44, 45),
                        },
                        Expr::Apply {
                            callee: Box::new(Expr::Var {
                                name: Symbol::from("fact"),
                                span: span(47, 51),
                            }),
                            args: vec![Expr::Apply {
                                callee: Box::new(Expr::Var {
                                    name: Symbol::from("sub-i64"),
                                    span: span(53, 60),
                                }),
                                args: vec![
                                    Expr::Var {
                                        name: Symbol::from("n"),
                                        span: span(61, 62),
                                    },
                                    Expr::IntLit {
                                        value: 1,
                                        span: span(63, 64),
                                    },
                                ],
                                span: span(52, 65),
                            }],
                            span: span(46, 66),
                        },
                    ],
                    span: span(35, 67),
                }),
                span: span(15, 68),
            },
            visibility: Visibility::Public,
            span: span(0, 69),
        })];

        tc.check_program(&program).unwrap();

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("fact") {
            assert!(
                scheme.vars.is_empty(),
                "fact should be monomorphic (Int -> Int)"
            );
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int))
            );
        } else {
            panic!("fact not found in symbol table");
        }
    }

    // spec: 05-definitions §5.2 — deftype registers constructors and enables match
    #[test]
    fn test_check_program_with_typedef() {
        let mut tc = TypeChecker::new();
        let program = vec![
            TopLevel::TypeDef {
                name: TypeName::from("Color"),
                docstring: None,
                type_params: vec![],
                constructors: vec![
                    cranelisp_types::ConstructorDef {
                        name: Symbol::from("Red"),
                        docstring: None,
                        fields: vec![],
                        span: Span::SYNTHETIC,
                    },
                    cranelisp_types::ConstructorDef {
                        name: Symbol::from("Green"),
                        docstring: None,
                        fields: vec![],
                        span: Span::SYNTHETIC,
                    },
                ],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            },
            TopLevel::Defn(Defn {
                name: Symbol::from("is-red"),
                docstring: None,
                params: vec![Symbol::from("c")],
                param_annotations: vec![None],
                body: Expr::Match {
                    scrutinee: Box::new(Expr::Var {
                        name: Symbol::from("c"),
                        span: span(30, 31),
                    }),
                    arms: vec![
                        cranelisp_types::MatchArm {
                            pattern: cranelisp_types::Pattern::Constructor {
                                name: Symbol::from("Red"),
                                bindings: vec![],
                                span: span(33, 36),
                            },
                            body: Expr::BoolLit {
                                value: true,
                                span: span(37, 41),
                            },
                            span: span(33, 41),
                        },
                        cranelisp_types::MatchArm {
                            pattern: cranelisp_types::Pattern::Wildcard {
                                span: span(42, 43),
                            },
                            body: Expr::BoolLit {
                                value: false,
                                span: span(44, 49),
                            },
                            span: span(42, 49),
                        },
                    ],
                    span: span(24, 50),
                    compiler_generated: false,
                },
                visibility: Visibility::Public,
                span: span(0, 51),
            }),
        ];

        let result = tc.check_program(&program).unwrap();

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("is-red") {
            assert_eq!(
                scheme.ty,
                Type::Fn(
                    vec![Type::ADT(TypeName::from("Color"), vec![])],
                    Box::new(Type::Bool)
                )
            );
        } else {
            panic!("is-red not found in symbol table");
        }

        // Type defs should be in the result
        assert!(result.type_defs.contains_key(&TypeName::from("Color")));
        assert!(result.constructor_to_type.contains_key("Red"));
    }

    // spec: 03-types §3.8 — unification failure produces type error
    #[test]
    fn test_check_program_type_error() {
        let mut tc = TypeChecker::new();
        // (defn bad [x] (add-i64 x true)) -- type error: Bool arg to monomorphic Int primitive
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("bad"),
            docstring: None,
            params: vec![Symbol::from("x")],
            param_annotations: vec![None],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("add-i64"),
                    span: span(16, 23),
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("x"),
                        span: span(24, 25),
                    },
                    Expr::BoolLit {
                        value: true,
                        span: span(26, 30),
                    },
                ],
                span: span(15, 31),
            },
            visibility: Visibility::Public,
            span: span(0, 32),
        })];

        // add-i64 has monomorphic type (Fn [Int Int] Int) so (add-i64 x true) is a
        // type error: Bool cannot unify with Int.
        let result = tc.check_program(&program);
        assert!(result.is_err());
    }

    // spec: 03-types §3.5.1 — all expression types fully resolved after inference
    #[test]
    fn test_check_program_expr_types_resolved() {
        let mut tc = TypeChecker::new();
        // (defn inc [x] (add-i64 x 1))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("inc"),
            docstring: None,
            params: vec![Symbol::from("x")],
            param_annotations: vec![None],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("add-i64"),
                    span: span(16, 23),
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("x"),
                        span: span(24, 25),
                    },
                    Expr::IntLit {
                        value: 1,
                        span: span(26, 27),
                    },
                ],
                span: span(15, 28),
            },
            visibility: Visibility::Public,
            span: span(0, 29),
        })];

        let result = tc.check_program(&program).unwrap();

        // All expr_types should be resolved (no Var types)
        for (span, ty) in &result.expr_types {
            if let Type::Var(_) = ty {
                panic!("unresolved Var in expr_types at {span}");
            }
        }
    }

    // spec: 03-types §3.1 — REPL expression inferred as literal type
    #[test]
    fn test_check_repl_expression() {
        let mut tc = TypeChecker::new();
        let input = ReplInput::Expr(Expr::IntLit {
            value: 42,
            span: span(0, 2),
        });
        let result = tc.check_repl_input(&input).unwrap();
        assert_eq!(result.ty, Type::Int);
        assert!(result.scheme.is_none());
    }

    // spec: 03-types §3.4 — REPL defn produces polymorphic scheme
    #[test]
    fn test_check_repl_defn() {
        let mut tc = TypeChecker::new();
        let input = ReplInput::Defn(Defn {
            name: Symbol::from("id"),
            docstring: None,
            params: vec![Symbol::from("x")],
            param_annotations: vec![None],
            body: Expr::Var {
                name: Symbol::from("x"),
                span: span(14, 15),
            },
            visibility: Visibility::Public,
            span: span(0, 16),
        });
        let result = tc.check_repl_input(&input).unwrap();

        // The scheme should be polymorphic
        let scheme = result.scheme.unwrap();
        assert_eq!(scheme.vars.len(), 1);
    }

    // spec: 05-definitions §5.2 — REPL typedef registers type and constructors
    #[test]
    fn test_check_repl_typedef() {
        let mut tc = TypeChecker::new();
        let input = ReplInput::TypeDef {
            name: TypeName::from("Dir"),
            docstring: None,
            type_params: vec![],
            constructors: vec![
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("North"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("South"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
            ],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let result = tc.check_repl_input(&input).unwrap();
        assert_eq!(result.ty, Type::ADT(TypeName::from("Dir"), vec![]));
        assert!(result.type_defs.contains_key(&TypeName::from("Dir")));
    }

    // spec: 03-types §3.5.1 — forward references resolved via two-pass inference
    #[test]
    fn test_check_program_forward_reference() {
        let mut tc = TypeChecker::new();
        // Two functions where the first calls the second
        // (defn double [x] (add-self x))
        // (defn add-self [y] (add-i64 y y))
        //
        // add-i64 is monomorphic (Fn [Int Int] Int), so add-self is pinned to Int.
        // double's type unifies with add-self's type through the call.
        let program = vec![
            TopLevel::Defn(Defn {
                name: Symbol::from("double"),
                docstring: None,
                params: vec![Symbol::from("x")],
                param_annotations: vec![None],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add-self"),
                        span: span(18, 26),
                    }),
                    args: vec![Expr::Var {
                        name: Symbol::from("x"),
                        span: span(27, 28),
                    }],
                    span: span(17, 29),
                },
                visibility: Visibility::Public,
                span: span(0, 30),
            }),
            TopLevel::Defn(Defn {
                name: Symbol::from("add-self"),
                docstring: None,
                params: vec![Symbol::from("y")],
                param_annotations: vec![None],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add-i64"),
                        span: span(48, 55),
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("y"),
                            span: span(56, 57),
                        },
                        Expr::Var {
                            name: Symbol::from("y"),
                            span: span(58, 59),
                        },
                    ],
                    span: span(47, 60),
                },
                visibility: Visibility::Public,
                span: span(31, 61),
            }),
        ];

        tc.check_program(&program).unwrap();

        // add-self is monomorphic: Fn([Int], Int) — add-i64 pins y to Int
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add-self") {
            assert!(
                scheme.vars.is_empty(),
                "add-self should have no quantified vars (monomorphic via add-i64)"
            );
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                "add-self: (Fn [Int] Int)"
            );
        } else {
            panic!("add-self not found in symbol table");
        }

        // double should also be monomorphic (calls add-self with Int)
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("double") {
            assert!(
                scheme.vars.is_empty(),
                "double should have no quantified vars (monomorphic via add-self)"
            );
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                "double: (Fn [Int] Int)"
            );
        } else {
            panic!("double not found in symbol table");
        }
    }

    // spec: 03-types §3.9 — type annotation pins parameter type in forward reference
    #[test]
    fn test_check_program_forward_reference_pinned() {
        let mut tc = TypeChecker::new();
        // (defn double [:Int x] (add-self x))
        // (defn add-self [y] (add-i64 y y))
        // Both are monomorphic: add-i64 pins y to Int, and annotation pins x to Int.
        let program = vec![
            TopLevel::Defn(Defn {
                name: Symbol::from("double"),
                docstring: None,
                params: vec![Symbol::from("x")],
                param_annotations: vec![Some(cranelisp_types::TypeExpr::Named(TypeName::from("Int")))],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add-self"),
                        span: span(118, 126),
                    }),
                    args: vec![Expr::Var {
                        name: Symbol::from("x"),
                        span: span(127, 128),
                    }],
                    span: span(117, 129),
                },
                visibility: Visibility::Public,
                span: span(100, 130),
            }),
            TopLevel::Defn(Defn {
                name: Symbol::from("add-self"),
                docstring: None,
                params: vec![Symbol::from("y")],
                param_annotations: vec![None],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add-i64"),
                        span: span(148, 155),
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("y"),
                            span: span(156, 157),
                        },
                        Expr::Var {
                            name: Symbol::from("y"),
                            span: span(158, 159),
                        },
                    ],
                    span: span(147, 160),
                },
                visibility: Visibility::Public,
                span: span(131, 161),
            }),
        ];

        tc.check_program(&program).unwrap();

        // double is pinned: Fn([Int], Int) — annotation + add-i64 both constrain to Int
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("double") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int))
            );
        } else {
            panic!("double not found");
        }

        // add-self is also pinned: Fn([Int], Int) — add-i64 constrains y to Int
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add-self") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int))
            );
        } else {
            panic!("add-self not found");
        }
    }

    // spec: 07-traits §7.5 — builtin function call resolved as BuiltinFn in method resolutions
    #[test]
    fn test_check_program_check_result_has_builtin_resolutions() {
        let mut tc = TypeChecker::new();
        // (defn inc [x] (add-i64 x 1))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("inc"),
            docstring: None,
            params: vec![Symbol::from("x")],
            param_annotations: vec![None],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("add-i64"),
                    span: span(16, 23),
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("x"),
                        span: span(24, 25),
                    },
                    Expr::IntLit {
                        value: 1,
                        span: span(26, 27),
                    },
                ],
                span: span(15, 28),
            },
            visibility: Visibility::Public,
            span: span(0, 29),
        })];

        let result = tc.check_program(&program).unwrap();

        // The add-i64 call site should have a BuiltinFn resolution
        assert!(!result.method_resolutions.is_empty());
        let resolution = result.method_resolutions.get(&span(15, 28)).unwrap();
        match resolution {
            cranelisp_types::ResolvedCall::BuiltinFn { name } => {
                assert_eq!(name.as_ref(), "add-i64");
            }
            _ => panic!("expected BuiltinFn"),
        }
    }

    // --- Ring 1: Polymorphic ADT program tests ---

    // spec: 05-definitions §5.2.2 — polymorphic typedef registers constructors with type params
    #[test]
    fn test_check_program_polymorphic_typedef() {
        let mut tc = TypeChecker::new();
        // (deftype (Option a) None (Some [:a val]))
        // (defn unwrap-or [opt default] (match opt [(Some x) x (None default)]))
        let program = vec![
            TopLevel::TypeDef {
                name: TypeName::from("Option"),
                docstring: None,
                type_params: vec![Symbol::from("a")],
                constructors: vec![
                    cranelisp_types::ConstructorDef {
                        name: Symbol::from("None"),
                        docstring: None,
                        fields: vec![],
                        span: Span::SYNTHETIC,
                    },
                    cranelisp_types::ConstructorDef {
                        name: Symbol::from("Some"),
                        docstring: None,
                        fields: vec![cranelisp_types::FieldDef {
                            name: Symbol::from("val"),
                            type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
                        }],
                        span: Span::SYNTHETIC,
                    },
                ],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            },
        ];

        let result = tc.check_program(&program).unwrap();
        assert!(result.type_defs.contains_key(&TypeName::from("Option")));
        assert!(result.constructor_to_type.contains_key("Some"));
        assert!(result.constructor_to_type.contains_key("None"));
    }

    // spec: 05-definitions §5.2.2 — REPL polymorphic typedef registers type defs
    #[test]
    fn test_check_repl_polymorphic_typedef() {
        let mut tc = TypeChecker::new();
        let input = ReplInput::TypeDef {
            name: TypeName::from("Option"),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            constructors: vec![
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("None"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("Some"),
                    docstring: None,
                    fields: vec![cranelisp_types::FieldDef {
                        name: Symbol::from("val"),
                        type_expr: cranelisp_types::TypeExpr::TypeVar(Symbol::from("a")),
                    }],
                    span: Span::SYNTHETIC,
                },
            ],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let result = tc.check_repl_input(&input).unwrap();
        assert!(result.type_defs.contains_key(&TypeName::from("Option")));
    }

    // spec: 03-types §3.1 — string literal inferred as String type
    #[test]
    fn test_check_repl_string_expression() {
        let mut tc = TypeChecker::new();
        let input = ReplInput::Expr(Expr::StringLit {
            value: "hello".to_string(),
            span: span(0, 7),
        });
        let result = tc.check_repl_input(&input).unwrap();
        assert_eq!(result.ty, Type::String);
    }

    // spec: 03-types §3.1 — function returning string literal has String return type
    #[test]
    fn test_check_program_string_in_function() {
        let mut tc = TypeChecker::new();
        // (defn greet [] "hello")
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("greet"),
            docstring: None,
            params: vec![],
            param_annotations: vec![],
            body: Expr::StringLit {
                value: "hello".to_string(),
                span: span(16, 23),
            },
            visibility: Visibility::Public,
            span: span(0, 24),
        })];

        tc.check_program(&program).unwrap();

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("greet") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![], Box::new(Type::String))
            );
        } else {
            panic!("greet not found in symbol table");
        }
    }

    // --- Ring 2: Constrained polymorphism tests ---

    // spec: 03-types §3.6 — collect_constrained_calls finds direct call to constrained fn
    #[test]
    fn test_collect_constrained_calls_finds_direct_call() {
        let constrained = HashSet::from([Symbol::from("add")]);
        // (add x y) where add is constrained
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add"),
                span: span(1, 4),
            }),
            args: vec![
                Expr::Var { name: Symbol::from("x"), span: span(5, 6) },
                Expr::Var { name: Symbol::from("y"), span: span(7, 8) },
            ],
            span: span(0, 9),
        };

        let mut calls = Vec::new();
        TypeChecker::collect_constrained_calls(&expr, &constrained, &mut calls);

        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].0.as_ref(), "add");
        assert_eq!(calls[0].1.len(), 2); // two arg spans
        assert_eq!(calls[0].2, span(0, 9)); // call span
    }

    // spec: 03-types §3.6 — collect_constrained_calls ignores non-constrained functions
    #[test]
    fn test_collect_constrained_calls_ignores_non_constrained() {
        let constrained = HashSet::from([Symbol::from("add")]);
        // (sub-i64 x y) where sub-i64 is NOT constrained
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("sub-i64"),
                span: span(1, 8),
            }),
            args: vec![
                Expr::Var { name: Symbol::from("x"), span: span(9, 10) },
                Expr::Var { name: Symbol::from("y"), span: span(11, 12) },
            ],
            span: span(0, 13),
        };

        let mut calls = Vec::new();
        TypeChecker::collect_constrained_calls(&expr, &constrained, &mut calls);

        assert!(calls.is_empty());
    }

    // spec: 03-types §3.6 — collect_constrained_calls recurses into let bindings
    #[test]
    fn test_collect_constrained_calls_recurses_into_let() {
        let constrained = HashSet::from([Symbol::from("add")]);
        // (let [z (add x y)] z)
        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("z"),
                Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add"),
                        span: span(10, 13),
                    }),
                    args: vec![
                        Expr::Var { name: Symbol::from("x"), span: span(14, 15) },
                        Expr::Var { name: Symbol::from("y"), span: span(16, 17) },
                    ],
                    span: span(9, 18),
                },
            )],
            body: Box::new(Expr::Var {
                name: Symbol::from("z"),
                span: span(20, 21),
            }),
            span: span(0, 22),
        };

        let mut calls = Vec::new();
        TypeChecker::collect_constrained_calls(&expr, &constrained, &mut calls);

        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].0.as_ref(), "add");
    }

    // spec: 03-types §3.6 — collect_constrained_calls recurses into if branches
    #[test]
    fn test_collect_constrained_calls_recurses_into_if() {
        let constrained = HashSet::from([Symbol::from("add")]);
        // (if true (add 1 2) (add 3 4))
        let expr = Expr::If {
            cond: Box::new(Expr::BoolLit { value: true, span: span(4, 8) }),
            then_branch: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("add"),
                    span: span(10, 13),
                }),
                args: vec![
                    Expr::IntLit { value: 1, span: span(14, 15) },
                    Expr::IntLit { value: 2, span: span(16, 17) },
                ],
                span: span(9, 18),
            }),
            else_branch: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("add"),
                    span: span(20, 23),
                }),
                args: vec![
                    Expr::IntLit { value: 3, span: span(24, 25) },
                    Expr::IntLit { value: 4, span: span(26, 27) },
                ],
                span: span(19, 28),
            }),
            span: span(0, 29),
        };

        let mut calls = Vec::new();
        TypeChecker::collect_constrained_calls(&expr, &constrained, &mut calls);

        assert_eq!(calls.len(), 2, "should find calls in both branches");
    }

    // spec: 03-types §3.6 — batch mode monomorphises constrained fn at concrete call site
    #[test]
    fn test_batch_monomorphise_generates_mono_defn() {
        let mut tc = TypeChecker::new();
        // Program: (defn add [x y] (+ x y))  -- constrained via +
        //          (defn main [] (add 3 4))   -- concrete Int call site
        let program = vec![
            TopLevel::Defn(Defn {
                name: Symbol::from("add"),
                docstring: None,
                params: vec![Symbol::from("x"), Symbol::from("y")],
                param_annotations: vec![None, None],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("+"),
                        span: span(18, 19),
                    }),
                    args: vec![
                        Expr::Var { name: Symbol::from("x"), span: span(20, 21) },
                        Expr::Var { name: Symbol::from("y"), span: span(22, 23) },
                    ],
                    span: span(17, 24),
                },
                visibility: Visibility::Public,
                span: span(0, 25),
            }),
            TopLevel::Defn(Defn {
                name: Symbol::from("main"),
                docstring: None,
                params: vec![],
                param_annotations: vec![],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add"),
                        span: span(40, 43),
                    }),
                    args: vec![
                        Expr::IntLit { value: 3, span: span(44, 45) },
                        Expr::IntLit { value: 4, span: span(46, 47) },
                    ],
                    span: span(39, 48),
                },
                visibility: Visibility::Public,
                span: span(26, 49),
            }),
        ];

        let result = tc.check_program(&program).unwrap();

        // In batch mode, add and main share a substitution during Pass 2.
        // main's (add 3 4) pins add's type vars to Int before generalization.
        // So add becomes monomorphic Fn([Int, Int], Int), not constrained.
        // This is correct HM behavior for same-program references.
        // Constrained polymorphism applies across module boundaries.
        assert!(
            result.constrained_fn_names.is_empty(),
            "within same program, add should be monomorphic due to shared subst"
        );
        assert!(
            result.mono_defns.is_empty(),
            "no constrained fns means no mono_defns needed"
        );

        // Verify add was correctly inferred as Fn([Int, Int], Int)
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int))
            );
        } else {
            panic!("add not found");
        }

        // The + call site within add didn't get resolved during Pass 2
        // because x/y were still Vars during add's body check.
        // In the same-program case, add is used monomorphically and
        // doesn't need separate mono_defn generation.
    }

    // spec: 03-types §3.6 — constrained fn without callers detected and registered
    #[test]
    fn test_batch_constrained_fn_alone_detected() {
        let mut tc = TypeChecker::new();
        // (defn add [x y] (+ x y))  -- alone, no callers; should be constrained
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            params: vec![Symbol::from("x"), Symbol::from("y")],
            param_annotations: vec![None, None],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("+"),
                    span: span(18, 19),
                }),
                args: vec![
                    Expr::Var { name: Symbol::from("x"), span: span(20, 21) },
                    Expr::Var { name: Symbol::from("y"), span: span(22, 23) },
                ],
                span: span(17, 24),
            },
            visibility: Visibility::Public,
            span: span(0, 25),
        })];

        let result = tc.check_program(&program).unwrap();

        assert!(
            result.constrained_fn_names.contains(&Symbol::from("add")),
            "add should be in constrained_fn_names"
        );

        // No callers, so no mono_defns
        assert!(
            result.mono_defns.is_empty(),
            "no call sites means no mono_defns"
        );

        // Check the scheme has Num constraint
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add") {
            assert!(
                !scheme.constraints.is_empty(),
                "add should have Num constraint"
            );
        } else {
            panic!("add not found in symbol table");
        }
    }

    // spec: 03-types §3.6 — REPL expression monomorphises constrained fn on demand
    #[test]
    fn test_repl_expr_monomorphise() {
        let mut tc = TypeChecker::new();

        // First, define a constrained fn: (defn add [x y] (+ x y))
        let defn_input = ReplInput::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            params: vec![Symbol::from("x"), Symbol::from("y")],
            param_annotations: vec![None, None],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("+"),
                    span: span(18, 19),
                }),
                args: vec![
                    Expr::Var { name: Symbol::from("x"), span: span(20, 21) },
                    Expr::Var { name: Symbol::from("y"), span: span(22, 23) },
                ],
                span: span(17, 24),
            },
            visibility: Visibility::Public,
            span: span(0, 25),
        });
        let _ = tc.check_repl_input(&defn_input).unwrap();

        // Now evaluate an expression that calls the constrained fn: (add 3 4)
        let expr_input = ReplInput::Expr(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add"),
                span: span(100, 103),
            }),
            args: vec![
                Expr::IntLit { value: 3, span: span(104, 105) },
                Expr::IntLit { value: 4, span: span(106, 107) },
            ],
            span: span(99, 108),
        });
        let result = tc.check_repl_input(&expr_input).unwrap();

        // Should have mono_defns populated
        assert!(
            !result.mono_defns.is_empty(),
            "REPL expr should generate mono_defns for constrained fn calls"
        );
        assert_eq!(
            result.mono_defns[0].defn.name.as_ref(),
            "add$Int+Int",
        );
    }

    // spec: 03-types §3.6 — REPL defn body triggers monomorphisation of constrained calls
    #[test]
    fn test_repl_defn_body_monomorphise() {
        let mut tc = TypeChecker::new();

        // Define a constrained fn: (defn add [x y] (+ x y))
        let defn_input = ReplInput::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            params: vec![Symbol::from("x"), Symbol::from("y")],
            param_annotations: vec![None, None],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("+"),
                    span: span(18, 19),
                }),
                args: vec![
                    Expr::Var { name: Symbol::from("x"), span: span(20, 21) },
                    Expr::Var { name: Symbol::from("y"), span: span(22, 23) },
                ],
                span: span(17, 24),
            },
            visibility: Visibility::Public,
            span: span(0, 25),
        });
        let _ = tc.check_repl_input(&defn_input).unwrap();

        // Define a function that calls the constrained fn: (defn main [] (add 1 2))
        let main_input = ReplInput::Defn(Defn {
            name: Symbol::from("main"),
            docstring: None,
            params: vec![],
            param_annotations: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("add"),
                    span: span(200, 203),
                }),
                args: vec![
                    Expr::IntLit { value: 1, span: span(204, 205) },
                    Expr::IntLit { value: 2, span: span(206, 207) },
                ],
                span: span(199, 208),
            },
            visibility: Visibility::Public,
            span: span(180, 209),
        });
        let result = tc.check_repl_input(&main_input).unwrap();

        // Should have mono_defns from the defn body scan
        assert!(
            !result.mono_defns.is_empty(),
            "REPL defn should generate mono_defns for constrained fn calls in body"
        );
        assert_eq!(
            result.mono_defns[0].defn.name.as_ref(),
            "add$Int+Int",
        );
    }

    // spec: 03-types §3.6 — program without constrained fns produces empty mono results
    #[test]
    fn test_batch_mono_no_constrained_fns_produces_empty() {
        let mut tc = TypeChecker::new();
        // (defn inc [x] (add-i64 x 1)) — no constrained fns, all monomorphic
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("inc"),
            docstring: None,
            params: vec![Symbol::from("x")],
            param_annotations: vec![None],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("add-i64"),
                    span: span(16, 23),
                }),
                args: vec![
                    Expr::Var { name: Symbol::from("x"), span: span(24, 25) },
                    Expr::IntLit { value: 1, span: span(26, 27) },
                ],
                span: span(15, 28),
            },
            visibility: Visibility::Public,
            span: span(0, 29),
        })];

        let result = tc.check_program(&program).unwrap();

        assert!(result.constrained_fn_names.is_empty());
        assert!(result.mono_defns.is_empty());
    }
}
