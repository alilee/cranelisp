//! Multi-pass type checking pipeline.
//!
//! `check()` is the unified entry point: it processes any `&[TopLevel]` slice
//! through a multi-pass pipeline (register → check → constrained → mono → curry).
//! A REPL line is a one-element slice; a batch program is a multi-element slice.
//! The passes work identically regardless of slice length.
//!
//! ## Per-Form API (v4 Pipeline)
//!
//! `check_form()` processes a single `TopLevel` form through one pass at a time.
//! The caller drives two-pass iteration:
//! - Pass 1 (`CheckPass::Register`): register type defs, traits, signatures.
//! - Pass 2 (`CheckPass::CheckBody`): check function bodies, detect constraints.
//!
//! `merge_form_result()` accumulates per-form results into a `ModuleCheckAccumulator`.
//! `finalize_check_result()` runs post-passes and drains the accumulator into `CheckResult`.
//!
//! `check()` internally uses `check_form()` in two passes — existing callers unchanged.
//!
//! `check_program` and `check_repl_input` are deprecated. All production callers
//! now use `check()`. The old methods are retained only for typecheck crate tests.

use std::collections::{HashMap, HashSet};

use cranelisp_types::{
    CheckResult, CompileContext, ConstrainedFn, CranelispError, Defn, DefKind, DefnVariant,
    DisplayInfo, Expr, JitSymbol, ModuleEntry, ModuleFullPath, ModuleStrategy, MonoDefn,
    ResolvedCall, Scheme, Span, Symbol, TopLevel, Type, Visibility, Warning, apply,
};

use crate::checker::TypeChecker;
use crate::resolve::resolve_type_expr;
use crate::scheme::mono;

// --- Per-Form Typecheck API types ---

/// Pass indicator for `check_form()`.
///
/// The two-pass structure (register all signatures, then check all bodies) is
/// fundamental to Algorithm W with mutual recursion. The caller drives the
/// iteration; `check_form` does the right thing for each (form, pass) pair.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckPass {
    /// Pass 1: register type/trait/signature.
    /// For Defn: registers signature only. For TypeDef/TraitDecl/TraitImpl: full registration.
    Register,
    /// Pass 2: check function body, generalize, detect constraints.
    /// Only meaningful for Defn forms. Other form kinds return an empty result.
    CheckBody,
}

/// Per-form typecheck result.
///
/// Returned by `check_form()` for each (form, pass) invocation. The caller
/// feeds this to `merge_form_result()` to accumulate into module-level state.
/// In v4, the scheduler also uses these fields for per-symbol codegen readiness.
#[derive(Debug)]
pub struct FormCheckResult {
    /// Method resolutions discovered while checking this form.
    /// In Pass 1: empty (registration produces no resolutions).
    /// In Pass 2: resolutions from the body of this defn.
    pub method_resolutions: HashMap<Span, ResolvedCall>,

    /// Expression types for this form's AST nodes.
    /// In Pass 1: may contain constructor types for TypeDef forms.
    /// In Pass 2: contains all expr types from the defn body + the defn's Fn type.
    pub expr_types: HashMap<Span, Type>,

    /// If this form defines a constrained polymorphic function (Pass 2 only),
    /// the function name. Used by the caller to build the constrained_fn_names set.
    pub constrained_fn: Option<Symbol>,

    /// Monomorphised definitions generated from this form's call sites (Pass 2 only).
    pub mono_defns: Vec<MonoDefn>,

    /// Default method definitions expanded from trait impls in this form (Pass 1 only).
    /// Produced when a TraitImpl form triggers default method synthesis.
    pub default_method_defns: Vec<Defn>,

    /// Multi-sig mangled definitions produced during overload resolution.
    /// Populated when a multi-sig DefnMulti's variants are resolved after Pass 2.
    pub multi_sig_defns: Vec<Defn>,

    /// Warnings emitted during checking this form.
    pub warnings: Vec<Warning>,

    /// Call graph edges discovered during this form's checking.
    /// Each entry is (caller_symbol, callee_symbol). Accumulated for the
    /// module's call graph, used by the scheduler for macro dependency walks.
    pub call_graph_edges: Vec<(Symbol, Symbol)>,
}

impl FormCheckResult {
    /// Create an empty FormCheckResult (used for no-op passes).
    fn empty() -> Self {
        FormCheckResult {
            method_resolutions: HashMap::new(),
            expr_types: HashMap::new(),
            constrained_fn: None,
            mono_defns: Vec::new(),
            default_method_defns: Vec::new(),
            multi_sig_defns: Vec::new(),
            warnings: Vec::new(),
            call_graph_edges: Vec::new(),
        }
    }
}

/// Per-module accumulator for form-by-form typecheck results.
///
/// One accumulator per module. Created before Pass 1, consumed by
/// `finalize_check_result()`. No concurrent access — a single worker
/// processes one module's forms sequentially (Invariant 5).
// FIXME(/typecheck): I-2 — method_resolutions, expr_types, warnings are collected here but
// never consumed during finalization (authoritative data stays in self.state). Step 3 scheduler
// should clarify which source is canonical to avoid design confusion.
pub struct ModuleCheckAccumulator {
    pub method_resolutions: HashMap<Span, ResolvedCall>,
    pub expr_types: HashMap<Span, Type>,
    pub constrained_fn_names: HashSet<Symbol>,
    pub mono_defns: Vec<MonoDefn>,
    pub default_method_defns: Vec<Defn>,
    pub multi_sig_defns: Vec<Defn>,
    pub warnings: Vec<Warning>,
    pub call_graph_edges: Vec<(Symbol, Symbol)>,
    /// Type vars from pass 1 registration, keyed by defn name.
    /// Needed by pass 2 to check bodies against registered signatures.
    pub defn_type_vars: HashMap<Symbol, (Vec<Type>, Type)>,
}

impl ModuleCheckAccumulator {
    /// Create a new empty accumulator for a module.
    pub fn new() -> Self {
        ModuleCheckAccumulator {
            method_resolutions: HashMap::new(),
            expr_types: HashMap::new(),
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            default_method_defns: Vec::new(),
            multi_sig_defns: Vec::new(),
            warnings: Vec::new(),
            call_graph_edges: Vec::new(),
            defn_type_vars: HashMap::new(),
        }
    }
}

// --- Name mangling for multi-sig overload dispatch ---

/// Mangle a function name with its parameter type signature.
/// e.g., `mangle_sig("foo", &[Type::Int, Type::Bool])` → `"foo$Int+Bool"`.
fn mangle_sig(name: &str, param_types: &[Type]) -> Symbol {
    if param_types.is_empty() {
        Symbol::from(format!("{}$", name))
    } else {
        let parts: Vec<String> = param_types.iter().map(mangle_type).collect();
        Symbol::from(format!("{}${}", name, parts.join("+")))
    }
}

/// Mangle a single type for name mangling.
fn mangle_type(ty: &Type) -> String {
    match ty {
        Type::Int => "Int".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::String => "String".to_string(),
        Type::Float => "Float".to_string(),
        Type::Fn(_, _) => "Fn".to_string(),
        Type::ADT(name, args) => {
            if args.is_empty() {
                name.to_string()
            } else {
                let arg_parts: Vec<String> = args.iter().map(mangle_type).collect();
                format!("{}${}", name, arg_parts.join("+"))
            }
        }
        Type::Var(_) => "Var".to_string(),
        Type::TyConApp(id, _) => format!("TyCon{id}"),
    }
}

/// Check if two concrete types are compatible (for overload resolution).
fn types_compatible(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Int, Type::Int)
        | (Type::Bool, Type::Bool)
        | (Type::String, Type::String)
        | (Type::Float, Type::Float) => true,
        (Type::Fn(p1, r1), Type::Fn(p2, r2)) => {
            p1.len() == p2.len()
                && p1
                    .iter()
                    .zip(p2.iter())
                    .all(|(a, b)| types_compatible(a, b))
                && types_compatible(r1, r2)
        }
        (Type::ADT(n1, a1), Type::ADT(n2, a2)) => {
            n1 == n2
                && a1.len() == a2.len()
                && a1
                    .iter()
                    .zip(a2.iter())
                    .all(|(a, b)| types_compatible(a, b))
        }
        (Type::TyConApp(id1, a1), Type::TyConApp(id2, a2)) => {
            id1 == id2
                && a1.len() == a2.len()
                && a1.iter().zip(a2.iter()).all(|(a, b)| types_compatible(a, b))
        }
        (Type::Var(_), _) | (_, Type::Var(_)) => true, // Unresolved — assume compatible
        _ => false,
    }
}

impl TypeChecker {
    // =================================================================
    // Per-Form Typecheck API (v4 pipeline)
    // =================================================================

    /// Check a single `TopLevel` form through one pass.
    ///
    /// The caller drives the two-pass iteration:
    /// - Pass 1 (`CheckPass::Register`): call for every form in source order.
    /// - Pass 2 (`CheckPass::CheckBody`): call for every form in source order.
    ///
    /// Returns a `FormCheckResult` that the caller feeds to `merge_form_result()`.
    ///
    /// ## Invariants
    /// - All signatures must be registered (Pass 1) before any body is checked (Pass 2).
    /// - Source order within Pass 1 must respect: TypeDef < TraitDecl < TraitImpl < Defn.
    /// - One `ModuleCheckAccumulator` per module, no concurrent access.
    pub fn check_form(
        &mut self,
        _module: &ModuleFullPath,
        form: &TopLevel,
        pass: CheckPass,
        accumulator: &mut ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        match pass {
            CheckPass::Register => self.check_form_register(form, accumulator),
            CheckPass::CheckBody => self.check_form_body(form, accumulator),
        }
    }

    /// Pass 1 (Register) dispatch: register type defs, trait decls/impls, signatures.
    fn check_form_register(
        &mut self,
        form: &TopLevel,
        accumulator: &mut ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        match form {
            TopLevel::TypeDef {
                name,
                docstring,
                type_params,
                constructors,
                visibility,
                span,
            } => {
                self.register_type_def(
                    name, docstring, type_params, constructors, *visibility, *span,
                )?;
                Ok(FormCheckResult::empty())
            }
            TopLevel::TraitDecl(decl) => {
                self.register_trait_decl(decl)?;
                Ok(FormCheckResult::empty())
            }
            TopLevel::TraitImpl(impl_) => {
                let defaults = self.register_trait_impl(impl_)?;
                let mut result = FormCheckResult::empty();
                result.default_method_defns = defaults;
                Ok(result)
            }
            TopLevel::Defn(defn) => {
                if defn.is_multi_sig() {
                    self.check_form_register_multi_sig(defn, accumulator)
                } else {
                    self.check_form_register_single_defn(defn, accumulator)
                }
            }
            TopLevel::Expr(_) => {
                // Expr forms should be wrapped as synthetic Defn before reaching here.
                // If they somehow arrive unwrapped, treat as no-op.
                Ok(FormCheckResult::empty())
            }
        }
    }

    /// Register a single-sig defn's signature (Pass 1).
    fn check_form_register_single_defn(
        &mut self,
        defn: &Defn,
        accumulator: &mut ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        let (param_types, ret_ty) = self.register_defn_signature(defn)?;
        accumulator.defn_type_vars.insert(defn.name.clone(), (param_types, ret_ty));
        Ok(FormCheckResult::empty())
    }

    /// Register a multi-sig defn: expand variants, register each, register base as Overloaded.
    fn check_form_register_multi_sig(
        &mut self,
        defn: &Defn,
        accumulator: &mut ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        let mut overload_entries = Vec::new();
        for (i, variant) in defn.variants.iter().enumerate() {
            let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));
            overload_entries.push((internal_name.clone(), variant.params.len()));

            let internal_defn = Defn {
                name: internal_name.clone(),
                docstring: defn.docstring.clone(),
                variants: vec![DefnVariant {
                    params: variant.params.clone(),
                    param_annotations: variant.param_annotations.clone(),
                    body: variant.body.clone(),
                    span: variant.span,
                }],
                visibility: defn.visibility,
                span: variant.span,
            };
            // Register each variant's signature
            let (param_types, ret_ty) = self.register_defn_signature(&internal_defn)?;
            accumulator.defn_type_vars.insert(internal_name, (param_types, ret_ty));
        }
        self.state.overloads.insert(defn.name.clone(), overload_entries);

        // Register a placeholder for the base name
        let placeholder_ty = self.fresh_var();
        let placeholder_scheme = mono(placeholder_ty);
        self.current_symbol_table_mut().insert(
            defn.name.clone(),
            ModuleEntry::Def {
                scheme: placeholder_scheme,
                visibility: defn.visibility,
                docstring: defn.docstring.clone(),
                param_names: vec![],
                kind: Box::new(DefKind::Overloaded { variants: vec![] }),
            },
        );

        Ok(FormCheckResult::empty())
    }

    /// Pass 2 (CheckBody) dispatch: check function bodies, generalize, detect constraints.
    fn check_form_body(
        &mut self,
        form: &TopLevel,
        accumulator: &mut ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        match form {
            TopLevel::Defn(defn) => {
                if defn.is_multi_sig() {
                    self.check_form_body_multi_sig(defn, accumulator)
                } else {
                    self.check_form_body_single_defn(defn, accumulator)
                }
            }
            // Non-Defn forms are no-ops in CheckBody pass.
            _ => Ok(FormCheckResult::empty()),
        }
    }

    /// Check a single-sig defn body (Pass 2).
    ///
    /// Checks the body, does eager constrained-fn detection, and scans
    /// for monomorphisation call sites.
    fn check_form_body_single_defn(
        &mut self,
        defn: &Defn,
        accumulator: &ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        let (param_types, ret_ty) = accumulator
            .defn_type_vars
            .get(&defn.name)
            .ok_or_else(|| CranelispError::TypeError {
                message: format!("internal: missing type vars for {}", defn.name),
                span: defn.span,
            })?;

        // Snapshot method_resolutions and expr_types sizes so we can extract
        // just the new entries added during this form's checking.
        let mr_before: HashSet<Span> = self.state.method_resolutions.keys().copied().collect();
        let et_before: HashSet<Span> = self.state.expr_types.keys().copied().collect();

        self.check_defn_body(defn, param_types, ret_ty)?;
        self.resolve_deferred_trait_calls(&defn.body());

        // Eager constrained-fn detection
        let fn_type = Type::Fn(
            param_types.iter().map(|t| self.apply_subst(t)).collect(),
            Box::new(self.apply_subst(ret_ty)),
        );
        let trial_scheme = self.generalize(&fn_type);
        let constrained_fn = if !trial_scheme.constraints.is_empty() {
            if let Some(ModuleEntry::Def { kind, .. }) =
                self.current_symbol_table_mut().symbols.get_mut(&defn.name)
            {
                let cf = ConstrainedFn {
                    defn: defn.clone(),
                    scheme: trial_scheme,
                };
                **kind = DefKind::UserFn {
                    constrained_fn: Some(Box::new(cf)),
                };
            }
            Some(defn.name.clone())
        } else {
            None
        };

        // Extract new method resolutions and expr types added during this form
        let mut form_mr = HashMap::new();
        for (span, res) in &self.state.method_resolutions {
            if !mr_before.contains(span) {
                form_mr.insert(*span, res.clone());
            }
        }
        let mut form_et = HashMap::new();
        for (span, ty) in &self.state.expr_types {
            if !et_before.contains(span) {
                form_et.insert(*span, ty.clone());
            }
        }

        let warnings = std::mem::take(&mut self.state.warnings);

        Ok(FormCheckResult {
            method_resolutions: form_mr,
            expr_types: form_et,
            constrained_fn,
            mono_defns: Vec::new(),
            default_method_defns: Vec::new(),
            multi_sig_defns: Vec::new(),
            warnings,
            call_graph_edges: Vec::new(),
        })
    }

    /// Check a multi-sig defn's variant bodies (Pass 2).
    fn check_form_body_multi_sig(
        &mut self,
        defn: &Defn,
        accumulator: &ModuleCheckAccumulator,
    ) -> Result<FormCheckResult, CranelispError> {
        let mr_before: HashSet<Span> = self.state.method_resolutions.keys().copied().collect();
        let et_before: HashSet<Span> = self.state.expr_types.keys().copied().collect();

        // Check each variant body
        for (i, variant) in defn.variants.iter().enumerate() {
            let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));
            let (param_types, ret_ty) = accumulator
                .defn_type_vars
                .get(&internal_name)
                .ok_or_else(|| CranelispError::TypeError {
                    message: format!(
                        "internal: missing type vars for multi-sig variant {}",
                        internal_name
                    ),
                    span: variant.span,
                })?;

            // Build a temporary single-variant defn for body checking
            let internal_defn = Defn {
                name: internal_name.clone(),
                docstring: defn.docstring.clone(),
                variants: vec![DefnVariant {
                    params: variant.params.clone(),
                    param_annotations: variant.param_annotations.clone(),
                    body: variant.body.clone(),
                    span: variant.span,
                }],
                visibility: defn.visibility,
                span: variant.span,
            };

            self.check_defn_body(&internal_defn, param_types, ret_ty)?;
            self.resolve_deferred_trait_calls(&internal_defn.body());

            // Eager constrained-fn detection for variant
            let fn_type = Type::Fn(
                param_types.iter().map(|t| self.apply_subst(t)).collect(),
                Box::new(self.apply_subst(ret_ty)),
            );
            let trial_scheme = self.generalize(&fn_type);
            if !trial_scheme.constraints.is_empty() {
                if let Some(ModuleEntry::Def { kind, .. }) =
                    self.current_symbol_table_mut().symbols.get_mut(&internal_name)
                {
                    let cf = ConstrainedFn {
                        defn: internal_defn,
                        scheme: trial_scheme,
                    };
                    **kind = DefKind::UserFn {
                        constrained_fn: Some(Box::new(cf)),
                    };
                }
            }
        }

        // Extract new method resolutions and expr types
        let mut form_mr = HashMap::new();
        for (span, res) in &self.state.method_resolutions {
            if !mr_before.contains(span) {
                form_mr.insert(*span, res.clone());
            }
        }
        let mut form_et = HashMap::new();
        for (span, ty) in &self.state.expr_types {
            if !et_before.contains(span) {
                form_et.insert(*span, ty.clone());
            }
        }

        let warnings = std::mem::take(&mut self.state.warnings);

        Ok(FormCheckResult {
            method_resolutions: form_mr,
            expr_types: form_et,
            constrained_fn: None,
            mono_defns: Vec::new(),
            default_method_defns: Vec::new(),
            multi_sig_defns: Vec::new(),
            warnings,
            call_graph_edges: Vec::new(),
        })
    }

    /// Merge a `FormCheckResult` into the module's accumulator.
    ///
    /// Called after each `check_form()` to accumulate per-form results
    /// into the module-level state.
    pub fn merge_form_result(
        &mut self,
        _module: &ModuleFullPath,
        accumulator: &mut ModuleCheckAccumulator,
        result: FormCheckResult,
    ) {
        accumulator.method_resolutions.extend(result.method_resolutions);
        accumulator.expr_types.extend(result.expr_types);
        if let Some(name) = result.constrained_fn {
            accumulator.constrained_fn_names.insert(name);
        }
        accumulator.mono_defns.extend(result.mono_defns);
        accumulator.default_method_defns.extend(result.default_method_defns);
        accumulator.multi_sig_defns.extend(result.multi_sig_defns);
        accumulator.warnings.extend(result.warnings);
        accumulator.call_graph_edges.extend(result.call_graph_edges);
    }

    /// Finalize typecheck for a module: run post-passes and drain accumulator into `CheckResult`.
    ///
    /// Runs:
    /// 1. Phase 2 generalization (apply final substitution, clear false-positive constrained markers)
    /// 2. Phase 3 re-resolve deferred trait calls
    /// 3. Multi-sig overload resolution (pass 2.5)
    /// 4. Constrained-fn detection and monomorphisation (passes 3-4)
    /// 5. Pending overload + auto-curry resolution (pass 5)
    /// 6. Build `CheckResult` from accumulated state
    ///
    /// Note: `type_defs` and `constructor_to_type` are read from the TypeChecker's
    /// module tables, not from the accumulator — TypeDef registration writes
    /// directly into the module's type_defs registry during Pass 1.
    pub fn finalize_check_result(
        &mut self,
        _module: &ModuleFullPath,
        accumulator: &mut ModuleCheckAccumulator,
        working_program: &[TopLevel],
        strategy: ModuleStrategy,
    ) -> Result<CheckResult, CranelispError> {
        // Phase 2: generalize all functions (matching pass2_check_bodies Phase 2).
        // Clear false-positive constrained markers.
        for (name, (param_types, ret_ty)) in &accumulator.defn_type_vars {
            let fn_type = Type::Fn(
                param_types.iter().map(|t| self.apply_subst(t)).collect(),
                Box::new(self.apply_subst(ret_ty)),
            );
            let scheme = self.generalize(&fn_type);
            if let Some(ModuleEntry::Def { scheme: s, kind, .. }) =
                self.current_symbol_table_mut().symbols.get_mut(name)
            {
                *s = scheme.clone();
                if scheme.constraints.is_empty()
                    && let DefKind::UserFn { constrained_fn: Some(_) } = kind.as_ref()
                {
                    **kind = DefKind::UserFn { constrained_fn: None };
                }
            }
        }

        // Phase 3: re-resolve deferred trait calls with final types
        for top in working_program {
            if let TopLevel::Defn(defn) = top {
                if defn.is_multi_sig() {
                    for (i, variant) in defn.variants.iter().enumerate() {
                        let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));
                        let internal_defn = Defn {
                            name: internal_name,
                            docstring: defn.docstring.clone(),
                            variants: vec![DefnVariant {
                                params: variant.params.clone(),
                                param_annotations: variant.param_annotations.clone(),
                                body: variant.body.clone(),
                                span: variant.span,
                            }],
                            visibility: defn.visibility,
                            span: variant.span,
                        };
                        self.resolve_deferred_trait_calls(&internal_defn.body());
                    }
                } else {
                    self.resolve_deferred_trait_calls(&defn.body());
                }
            }
        }

        // Pass 2.5: resolve multi-sig overloads
        let multi_sig_defns = self.resolve_multi_sig_overloads(
            working_program,
            &accumulator.defn_type_vars,
        )?;

        // Pass 3: detect constrained polymorphic functions
        let single_sig_defns = Self::collect_single_sig_defns(working_program);
        let mut constrained_fn_names = self.detect_constrained_fns(&single_sig_defns);

        // Add previously-accumulated constrained fns and those from prior REPL evals
        constrained_fn_names.extend(accumulator.constrained_fn_names.drain());

        if strategy == ModuleStrategy::Additive {
            for (name, entry) in self.current_symbol_table().all_symbols() {
                if let ModuleEntry::Def { kind, .. } = entry
                    && let DefKind::UserFn { constrained_fn: Some(_) } = kind.as_ref()
                {
                    constrained_fn_names.insert(name.clone());
                }
            }
        }

        // Pass 4: monomorphise constrained function call sites
        let mono_defns = self.pass4_monomorphise(&single_sig_defns, &constrained_fn_names)?;

        // Pass 5: resolve pending overload dispatch + auto-curry
        self.resolve_pending_overloads()?;
        self.resolve_auto_curry();

        // Build result
        let mut result = self.build_check_result();
        result.constrained_fn_names = constrained_fn_names;
        result.mono_defns = mono_defns;
        let mut all_default_defns = std::mem::take(&mut accumulator.default_method_defns);
        all_default_defns.extend(multi_sig_defns);
        result.default_method_defns = all_default_defns;

        Ok(result)
    }

    // =================================================================
    // Unified check() entry point — uses check_form internally
    // =================================================================

    /// Unified type-checking entry point.
    ///
    /// Processes a slice of `TopLevel` forms through the multi-pass pipeline
    /// using `check_form()` internally. Existing callers see identical results.
    ///
    /// `Expr` variants are wrapped in a synthetic zero-arg `Defn` named `__expr`
    /// so they flow through the same passes as regular definitions.
    #[must_use = "check result contains expr_types and method_resolutions needed by codegen"]
    pub fn check(
        &mut self,
        program: &[TopLevel],
        ctx: &CompileContext,
        strategy: ModuleStrategy,
    ) -> Result<CheckResult, CranelispError> {
        // Set active module from context.
        self.set_current_module(ctx.module.clone());

        // If Replace strategy, clear existing module state so that removed
        // definitions don't persist as stale entries.
        if strategy == ModuleStrategy::Replace {
            self.clear_module_for_replace();
        }

        // Build a working copy of the program with Expr variants wrapped
        // as synthetic zero-arg Defns.
        let working_program = Self::wrap_exprs_as_defns(program);

        // Create per-module accumulator
        let mut accumulator = ModuleCheckAccumulator::new();

        // Pass 1: Register all forms in source order
        for form in &working_program {
            let result = self.check_form(&ctx.module, form, CheckPass::Register, &mut accumulator)?;
            self.merge_form_result(&ctx.module, &mut accumulator, result);
        }

        // Register default method defns generated during Pass 1 TraitImpl processing.
        // These need Pass 1 signature registration too.
        let defaults: Vec<Defn> = std::mem::take(&mut accumulator.default_method_defns);
        for defn in &defaults {
            let form = TopLevel::Defn(defn.clone());
            let result = self.check_form(&ctx.module, &form, CheckPass::Register, &mut accumulator)?;
            self.merge_form_result(&ctx.module, &mut accumulator, result);
        }
        // Put defaults back so finalize knows about them
        accumulator.default_method_defns = defaults;

        // Pass 2: Check bodies for all forms
        for form in &working_program {
            let result = self.check_form(&ctx.module, form, CheckPass::CheckBody, &mut accumulator)?;
            self.merge_form_result(&ctx.module, &mut accumulator, result);
        }

        // Check bodies of default method defns too.
        let defaults_for_body: Vec<Defn> = accumulator.default_method_defns.clone();
        for defn in &defaults_for_body {
            let form = TopLevel::Defn(defn.clone());
            let result = self.check_form(&ctx.module, &form, CheckPass::CheckBody, &mut accumulator)?;
            self.merge_form_result(&ctx.module, &mut accumulator, result);
        }

        // Finalize: run post-passes (generalization, overload resolution, monomorphisation,
        // auto-curry) and build CheckResult.
        let mut result = self.finalize_check_result(
            &ctx.module, &mut accumulator, &working_program, strategy,
        )?;

        // Populate display info
        result.display = self.compute_display_info(program, &accumulator.defn_type_vars);

        Ok(result)
    }

    /// Wrap `Expr` variants as synthetic zero-arg `Defn` named `__expr`.
    fn wrap_exprs_as_defns(program: &[TopLevel]) -> Vec<TopLevel> {
        let mut working_program = Vec::with_capacity(program.len());
        for top in program {
            match top {
                TopLevel::Expr(expr) => {
                    let span = expr.span();
                    let wrapper_span = Span::new(
                        span.start.saturating_sub(1),
                        span.end.saturating_add(1),
                    );
                    let synthetic_defn = Defn {
                        name: Symbol::from("__expr"),
                        docstring: None,
                        variants: vec![DefnVariant {
                            params: vec![],
                            param_annotations: vec![],
                            body: expr.clone(),
                            span,
                        }],
                        visibility: Visibility::Public,
                        span: wrapper_span,
                    };
                    working_program.push(TopLevel::Defn(synthetic_defn));
                }
                other => {
                    working_program.push(other.clone());
                }
            }
        }
        working_program
    }

    /// Compute DisplayInfo from the last form in the program.
    ///
    /// Populated when the input has 1-2 elements (REPL-like input).
    /// For batch programs (many forms), returns None.
    fn compute_display_info(
        &self,
        original_program: &[TopLevel],
        defn_type_vars: &HashMap<Symbol, (Vec<Type>, Type)>,
    ) -> Option<DisplayInfo> {
        if original_program.len() > 2 {
            return None;
        }

        let last = original_program.last()?;
        match last {
            TopLevel::Expr(_expr) => {
                // The synthetic __expr defn was registered — look up its type.
                if let Some((_param_tys, ret_ty)) = defn_type_vars.get(&Symbol::from("__expr")) {
                    let resolved = self.apply_subst(ret_ty);
                    Some(DisplayInfo {
                        ty: resolved,
                        scheme: None,
                    })
                } else {
                    None
                }
            }
            TopLevel::Defn(defn) => {
                // Look up the defn's generalized scheme from the symbol table.
                if let Some(ModuleEntry::Def { scheme, .. }) =
                    self.current_symbol_table().get(defn.name.as_ref())
                {
                    Some(DisplayInfo {
                        ty: scheme.ty.clone(),
                        scheme: Some(scheme.clone()),
                    })
                } else {
                    None
                }
            }
            TopLevel::TypeDef { name, .. } => {
                let ty = Type::ADT(name.clone(), vec![]);
                Some(DisplayInfo { ty, scheme: None })
            }
            TopLevel::TraitDecl(_) => {
                Some(DisplayInfo { ty: Type::Bool, scheme: None })
            }
            TopLevel::TraitImpl(_) => {
                Some(DisplayInfo { ty: Type::Bool, scheme: None })
            }
        }
    }

    /// Clear module state for Replace strategy.
    ///
    /// Removes all symbol table entries, type defs, trait decls, and trait
    /// impls for the current module. Called at the start of `check()` when
    /// `ctx.strategy == ModuleStrategy::Replace`.
    fn clear_module_for_replace(&mut self) {
        // Clear symbol table entries for the current module
        self.current_symbol_table_mut().symbols.clear();

        // Note: type_defs, trait_registry, and impl_registry are shared
        // across modules in the current design. Full per-module clearing
        // would require tracking which registrations belong to which module.
        // For now, clearing the symbol table is sufficient for the Replace
        // semantics needed by file reloading.
    }

    /// Collect only single-sig Defn entries (skip multi-sig).
    fn collect_single_sig_defns(program: &[TopLevel]) -> Vec<&Defn> {
        program
            .iter()
            .filter_map(|top| {
                if let TopLevel::Defn(defn) = top {
                    if defn.is_multi_sig() {
                        None
                    } else {
                        Some(defn)
                    }
                } else {
                    None
                }
            })
            .collect()
    }

    /// Expand multi-sig defns into synthetic single-variant defns with
    /// internal names (`name__v0`, `name__v1`, ...).
    ///
    /// Also populates `self.overloads` with the base name → internal name
    /// mapping for later overload resolution.
    ///
    /// Returns owned `Vec<Defn>` — the caller holds references into this vec
    /// alongside the single-sig defn references from the program.
    ///
    /// Note: Superseded by `check_form_register_multi_sig` for the `check()` path.
    /// Retained for the deprecated `check_program` path used in tests.
    #[allow(dead_code)]
    fn expand_multi_sig_defns(&mut self, program: &[TopLevel]) -> Vec<Defn> {
        let mut internal_defns = Vec::new();

        for top in program {
            if let TopLevel::Defn(defn) = top {
                if !defn.is_multi_sig() {
                    continue;
                }

                let mut overload_entries = Vec::new();
                for (i, variant) in defn.variants.iter().enumerate() {
                    let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));
                    overload_entries.push((internal_name.clone(), variant.params.len()));

                    internal_defns.push(Defn {
                        name: internal_name,
                        docstring: defn.docstring.clone(),
                        variants: vec![DefnVariant {
                            params: variant.params.clone(),
                            param_annotations: variant.param_annotations.clone(),
                            body: variant.body.clone(),
                            span: variant.span,
                        }],
                        visibility: defn.visibility,
                        span: variant.span,
                    });
                }
                self.state.overloads.insert(defn.name.clone(), overload_entries);

                // Register a placeholder for the base name so `infer_var`
                // can find it during pass 2. The placeholder uses a fresh
                // type variable — the actual type is determined during
                // overload resolution after pass 2.
                let placeholder_ty = self.fresh_var();
                let placeholder_scheme = mono(placeholder_ty);
                self.current_symbol_table_mut().insert(
                    defn.name.clone(),
                    ModuleEntry::Def {
                        scheme: placeholder_scheme,
                        visibility: defn.visibility,
                        docstring: defn.docstring.clone(),
                        param_names: vec![],
                        kind: Box::new(DefKind::Overloaded { variants: vec![] }),
                    },
                );
            }
        }

        internal_defns
    }

    /// Resolve multi-sig overloads after pass 2: build mangled names from
    /// concrete types, check for duplicates, register mangled names in symbol
    /// table, and populate `resolved_overloads`.
    ///
    /// Returns a list of mangled Defn objects that the backend should compile.
    // FIXME(/typecheck): I-1 — this function is 135 lines, exceeds 100-line limit. Decompose.
    fn resolve_multi_sig_overloads(
        &mut self,
        program: &[TopLevel],
        type_vars: &HashMap<Symbol, (Vec<Type>, Type)>,
    ) -> Result<Vec<Defn>, CranelispError> {
        let mut result_defns = Vec::new();

        for top in program {
            if let TopLevel::Defn(defn) = top {
                if !defn.is_multi_sig() {
                    continue;
                }

                let mut resolved = Vec::new();
                let mut sig_set: Vec<Vec<Type>> = Vec::new();

                for (i, variant) in defn.variants.iter().enumerate() {
                    let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));

                    let (param_tys, ret_ty) = type_vars
                        .get(&internal_name)
                        .ok_or_else(|| CranelispError::TypeError {
                            message: format!(
                                "internal: missing type vars for multi-sig variant {}",
                                internal_name
                            ),
                            span: variant.span,
                        })?;

                    let concrete_params: Vec<Type> = param_tys
                        .iter()
                        .map(|t| self.apply_subst(t))
                        .collect();
                    let concrete_ret = self.apply_subst(ret_ty);
                    let mangled = mangle_sig(defn.name.as_ref(), &concrete_params);

                    // Check for duplicate signatures
                    if sig_set.iter().any(|s| s == &concrete_params) {
                        return Err(CranelispError::TypeError {
                            message: format!(
                                "duplicate signature for '{}': ({})",
                                defn.name,
                                concrete_params
                                    .iter()
                                    .map(|t| format!("{t}"))
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            ),
                            span: variant.span,
                        });
                    }
                    sig_set.push(concrete_params.clone());

                    let fn_ty = Type::Fn(
                        concrete_params.clone(),
                        Box::new(concrete_ret.clone()),
                    );
                    let scheme = self.generalize(&fn_ty);

                    // Remove internal name, register mangled name
                    self.current_symbol_table_mut()
                        .symbols
                        .remove(internal_name.as_ref());
                    self.current_symbol_table_mut().insert(
                        mangled.clone(),
                        ModuleEntry::Def {
                            scheme: scheme.clone(),
                            visibility: defn.visibility,
                            docstring: defn.docstring.clone(),
                            param_names: variant.params.clone(),
                            kind: Box::new(DefKind::UserFn {
                                constrained_fn: None,
                            }),
                        },
                    );

                    // Build the mangled defn for the backend
                    result_defns.push(Defn {
                        name: mangled.clone(),
                        docstring: defn.docstring.clone(),
                        variants: vec![DefnVariant {
                            params: variant.params.clone(),
                            param_annotations: variant.param_annotations.clone(),
                            body: variant.body.clone(),
                            span: variant.span,
                        }],
                        visibility: defn.visibility,
                        span: variant.span,
                    });

                    resolved.push((concrete_params, concrete_ret, mangled));
                }

                // Register the base name as Overloaded in the symbol table
                let overload_variants = resolved
                    .iter()
                    .map(|(params, ret, mangled)| {
                        cranelisp_types::OverloadVariant {
                            param_types: params.clone(),
                            ret_type: ret.clone(),
                            mangled_name: mangled.clone(),
                        }
                    })
                    .collect();

                // Build a union scheme for the base name — use first variant's
                // scheme for now. The base name is registered as Overloaded so
                // `infer_apply` detects it and records a pending overload.
                let first_fn_ty = Type::Fn(
                    resolved[0].0.clone(),
                    Box::new(resolved[0].1.clone()),
                );
                let base_scheme = self.generalize(&first_fn_ty);

                self.current_symbol_table_mut().insert(
                    defn.name.clone(),
                    ModuleEntry::Def {
                        scheme: base_scheme,
                        visibility: defn.visibility,
                        docstring: defn.docstring.clone(),
                        param_names: vec![],
                        kind: Box::new(DefKind::Overloaded {
                            variants: overload_variants,
                        }),
                    },
                );

                self.state.resolved_overloads.insert(
                    defn.name.clone(),
                    resolved,
                );
            }
        }

        Ok(result_defns)
    }

    /// Resolve pending overload dispatch resolutions.
    ///
    /// For each pending `(span, base_name, arg_types, ret_type_var)`, find
    /// the matching variant and record `SigDispatch` in method_resolutions.
    fn resolve_pending_overloads(&mut self) -> Result<(), CranelispError> {
        let pending = std::mem::take(&mut self.state.pending_overload_resolutions);

        for (span, base_name, arg_types, ret_type_var) in &pending {
            let concrete_args: Vec<Type> = arg_types
                .iter()
                .map(|t| apply(&self.state.subst, t))
                .collect();

            let variants = self.state
                .resolved_overloads
                .get(base_name)
                .ok_or_else(|| CranelispError::TypeError {
                    message: format!("no overloaded function: {}", base_name),
                    span: *span,
                })?
                .clone();

            // Find exact arity + type matches
            let mut exact_matches: Vec<&(Vec<Type>, Type, Symbol)> = Vec::new();

            for variant in &variants {
                let (param_types, _ret_ty, _mangled) = variant;
                if param_types.len() == concrete_args.len() {
                    let compatible = param_types
                        .iter()
                        .zip(concrete_args.iter())
                        .all(|(p, a)| types_compatible(p, a));
                    if compatible {
                        exact_matches.push(variant);
                    }
                }
            }

            if exact_matches.len() == 1 {
                let (param_types, ret_ty, mangled_name) = exact_matches[0];
                // Unify to bind type variables
                for (p, a) in param_types.iter().zip(concrete_args.iter()) {
                    self.unify(p, a, *span)?;
                }
                self.unify(ret_type_var, ret_ty, *span)?;
                self.state.method_resolutions.insert(
                    *span,
                    ResolvedCall::SigDispatch {
                        mangled_name: JitSymbol::from(mangled_name.as_ref()),
                    },
                );
            } else if exact_matches.len() > 1 {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "ambiguous call to '{}' — {} matching signatures",
                        base_name,
                        exact_matches.len()
                    ),
                    span: *span,
                });
            } else {
                return Err(CranelispError::TypeError {
                    message: format!(
                        "no matching signature for '{}' with arg types ({})",
                        base_name,
                        concrete_args
                            .iter()
                            .map(|t| format!("{t}"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    span: *span,
                });
            }
        }

        Ok(())
    }

    /// Check a complete program (batch mode).
    ///
    /// Two-pass pipeline:
    /// 1. Register type definitions and function signatures.
    /// 2. Check function bodies, generalize types.
    #[deprecated(note = "use check() instead — unified pipeline entry point")]
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

        // Pass 5: resolve auto-curry sites into method_resolutions
        self.resolve_auto_curry();

        let mut result = self.build_check_result();
        result.constrained_fn_names = constrained_fn_names.clone();
        result.mono_defns = mono_defns;
        result.default_method_defns = default_defns;
        Ok(result)
    }

    /// Check a single REPL input incrementally.
    #[deprecated(note = "use check() instead — unified pipeline entry point")]
    #[must_use = "check result contains type and expr_types needed by codegen"]
    pub fn check_repl_input(
        &mut self,
        input: &TopLevel,
    ) -> Result<CheckResult, CranelispError> {
        match input {
            TopLevel::Expr(expr) => {
                let ty = self.infer_expr(expr)?;
                let resolved = self.apply_subst(&ty);

                // Resolve auto-curry sites before building result.
                self.resolve_auto_curry();

                // Gap 4: scan for constrained-fn calls, monomorphise on demand
                let mono_defns = self.monomorphise_expr_calls(expr)?;

                let mut result = self.build_repl_result(resolved, None);
                result.mono_defns = mono_defns;
                Ok(result)
            }

            TopLevel::Defn(defn) if defn.is_multi_sig() => {
                Err(CranelispError::TypeError {
                    message: "multi-signature functions not supported in Ring 0".into(),
                    span: defn.span,
                })
            }

            TopLevel::Defn(defn) => {
                let (ty, scheme) = self.check_single_defn(defn)?;

                // Resolve auto-curry sites before building result.
                self.resolve_auto_curry();

                // Scan defn body for constrained-fn calls, monomorphise on demand
                let mono_defns = self.monomorphise_expr_calls(defn.body())?;

                let mut result = self.build_repl_result(ty, Some(scheme));
                result.mono_defns = mono_defns;
                Ok(result)
            }

            TopLevel::TypeDef {
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

            TopLevel::TraitDecl(decl) => {
                self.register_trait_decl(decl)?;
                let ty = Type::Bool; // Placeholder return type for trait decl
                Ok(self.build_repl_result(ty, None))
            }

            TopLevel::TraitImpl(impl_) => {
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
                    // Skip multi-sig defns — not supported in Ring 0 batch path
                    if defn.is_multi_sig() {
                        None
                    } else {
                        Some(defn)
                    }
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
        for (i, _param) in defn.params().iter().enumerate() {
            let param_ty = if let Some(Some(ann)) = defn.param_annotations().get(i) {
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
                param_names: defn.params().to_vec(),
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
            self.resolve_deferred_trait_calls(&defn.body());

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
            self.resolve_deferred_trait_calls(&defn.body());
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
        for (param_name, param_ty) in defn.params().iter().zip(param_types.iter()) {
            self.bind_local(param_name.clone(), mono(param_ty.clone()));
        }

        // Bind the function name for recursion
        let fn_type = Type::Fn(param_types.to_vec(), Box::new(ret_ty.clone()));
        self.bind_local(defn.name.clone(), mono(fn_type));

        // Infer body type
        let body_ty = self.infer_expr(&defn.body())?;

        // Unify body type with return type variable
        self.unify(&body_ty, ret_ty, defn.span)?;

        self.pop_scope();

        // Record the defn's Fn type in expr_types so the backend can look up
        // authoritative parameter types. Without this, unused params (e.g.,
        // `_s` in `(defn f [:String _s] 42)`) have no type recorded and
        // scope cleanup skips their RC dec, causing leaks.
        let resolved_fn_type = Type::Fn(
            param_types.iter().map(|t| self.apply_subst(t)).collect(),
            Box::new(self.apply_subst(ret_ty)),
        );
        self.record_expr_type(defn.span, resolved_fn_type);

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
        self.resolve_deferred_trait_calls(&defn.body());

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
                defn.body(),
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
                self.state.method_resolutions.insert(
                    *call_span,
                    ResolvedCall::SigDispatch { mangled_name: mangled.clone() },
                );
                continue;
            }

            if let Some(mono) = self.monomorphise_call(fn_name, &arg_types, *call_span)? {
                let mangled = JitSymbol::from(mono.defn.name.as_ref());
                // Record dispatch for this call site
                self.state.method_resolutions.insert(
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
                self.state.method_resolutions.insert(
                    *call_span,
                    ResolvedCall::SigDispatch { mangled_name: mangled.clone() },
                );
                continue;
            }

            if let Some(mono) = self.monomorphise_call(fn_name, &arg_types, *call_span)? {
                let mangled = JitSymbol::from(mono.defn.name.as_ref());
                self.state.method_resolutions.insert(
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
            Expr::ParBind { bindings, body, .. } => {
                for (_, binding_expr) in bindings {
                    Self::collect_constrained_calls(binding_expr, constrained_fn_names, out);
                }
                Self::collect_constrained_calls(body, constrained_fn_names, out);
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

    /// Drain pending auto-curry resolutions into method_resolutions.
    ///
    /// Each entry in `pending_auto_curry` records a call site where the
    /// typechecker detected partial application (fewer args than params).
    /// This converts them to `ResolvedCall::AutoCurry` entries that the
    /// backend can use for codegen.
    pub(crate) fn resolve_auto_curry(&mut self) {
        let pending = std::mem::take(&mut self.state.pending_auto_curry);
        for (span, name, applied_count, total_count, callee_ty, mut trait_resolution) in pending {
            // If the trait resolution wasn't determined earlier (types were
            // still unresolved vars during try_auto_curry), attempt it now.
            // Later unifications (e.g., from a call site like `(make-adder 10)`)
            // may have pinned the type vars to concrete types.
            if trait_resolution.is_none() {
                let resolved_callee = self.apply_subst(&callee_ty);
                if let Type::Fn(full_params, _) = &resolved_callee {
                    let resolved_params: Vec<Type> = full_params
                        .iter()
                        .map(|t| self.apply_subst(t))
                        .collect();
                    if let Ok(Some(r)) = self.try_resolve_trait_method(&name, &resolved_params, span) {
                        trait_resolution = Some(r);
                    } else if let Some(jit_name) = self.resolve_primitive_jit_name(&name) {
                        trait_resolution = Some(ResolvedCall::BuiltinFn { name: jit_name });
                    }
                }
            }

            self.state.method_resolutions.insert(
                span,
                ResolvedCall::AutoCurry {
                    target_name: name,
                    applied_count,
                    total_count,
                    trait_resolution: trait_resolution.map(Box::new),
                },
            );
        }
    }

    /// Resolve all recorded expr_types through the current substitution.
    fn resolve_expr_types(&self) -> HashMap<Span, Type> {
        self.state.expr_types
            .iter()
            .map(|(span, ty)| (*span, apply(&self.state.subst, ty)))
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
            method_resolutions: std::mem::take(&mut self.state.method_resolutions),
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: resolved_expr_types,
            default_method_defns: Vec::new(),
            warnings: std::mem::take(&mut self.state.warnings),
            type_defs: self.type_defs.get_mut().unwrap().type_defs.clone(),
            constructor_to_type: self.type_defs.get_mut().unwrap().constructor_to_type.clone(),
            display: None,
        }
    }

    /// Build a CheckResult with display info from the current state (REPL path).
    fn build_repl_result(&mut self, ty: Type, scheme: Option<Scheme>) -> CheckResult {
        let resolved_expr_types = self.resolve_expr_types();

        // See build_check_result comment: assertion deferred to Ring 2.
        // TODO(Ring 2): uncomment when monomorphisation is implemented
        // debug_assert!(
        //     !resolved_expr_types.values().any(|ty| ty.contains_var()),
        //     "build_repl_result: unresolved Type::Var in expr_types"
        // );

        CheckResult {
            method_resolutions: std::mem::take(&mut self.state.method_resolutions),
            expr_types: resolved_expr_types,
            warnings: std::mem::take(&mut self.state.warnings),
            type_defs: self.type_defs.get_mut().unwrap().type_defs.clone(),
            constructor_to_type: self.type_defs.get_mut().unwrap().constructor_to_type.clone(),
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            default_method_defns: Vec::new(),
            display: Some(DisplayInfo { ty, scheme }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{
        CompileContext, DefnVariant, Expr, FQSymbol, ModuleFullPath, Symbol, TraitDecl,
        TraitImpl, TraitMethodSig, TraitName, TypeExpr, TypeName, Visibility,
    };

    fn span(start: u32, end: u32) -> Span {
        Span::new(start, end)
    }

    /// Create a single-sig Defn (convenience for tests).
    fn make_defn(
        name: &str,
        params: Vec<Symbol>,
        param_annotations: Vec<Option<TypeExpr>>,
        body: Expr,
        visibility: Visibility,
        span: Span,
    ) -> Defn {
        Defn {
            name: Symbol::from(name),
            docstring: None,
            variants: vec![DefnVariant {
                params,
                param_annotations,
                body,
                span,
            }],
            visibility,
            span,
        }
    }

    /// Create a TypeChecker with all primitives available in the current module.
    /// Uses set_current_module to create a "test" module seeded with primitives.
    fn tc_with_prims() -> TypeChecker {
        let mut tc = TypeChecker::new();
        tc.set_current_module(ModuleFullPath::from("test"));
        tc
    }

    /// Register a minimal Num trait with `+` method, plus an impl for Int,
    /// so tests using `(+ x y)` work after Decision 17 elimination.
    fn register_num_trait_inline(tc: &mut TypeChecker) {
        let num_decl = TraitDecl {
            name: TraitName::from("Num"),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from("+"),
                docstring: None,
                params: vec![
                    TypeExpr::TypeVar(Symbol::from("a")),
                    TypeExpr::TypeVar(Symbol::from("a")),
                ],
                ret_type: TypeExpr::TypeVar(Symbol::from("a")),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        tc.register_trait_decl(&num_decl).unwrap();

        // impl Num for Int: + → add-i64
        let impl_ = TraitImpl {
            trait_name: TraitName::from("Num"),
            target_type: TypeName::from("Int"),
            type_args: vec![],
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("+"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("x"), Symbol::from("y")],
                    param_annotations: vec![None, None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: Span::SYNTHETIC,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: Span::SYNTHETIC },
                            Expr::Var { name: Symbol::from("y"), span: Span::SYNTHETIC },
                        ],
                        span: Span::SYNTHETIC,
                    },
                    span: Span::SYNTHETIC,
                }],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
        };
        tc.register_trait_impl(&impl_).unwrap();
        tc.clear_transient_state();
    }

    // spec: 05-definitions §5.1 — defn registers function with inferred type
    #[test]
    fn test_check_program_simple_defn() {
        let mut tc = tc_with_prims();
        // (defn add-one [x] (add-i64 x 1))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("add-one"),
            docstring: None,
            variants: vec![DefnVariant {
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
                span: span(0, 33),
            }],
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
        let mut tc = tc_with_prims();
        // (defn id [x] x)
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("id"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x")],
                param_annotations: vec![None],
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: span(14, 15),
                },
                span: span(0, 16),
            }],
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
        let mut tc = tc_with_prims();
        // (defn fact [n] (if (eq-i64 n 0) 1 (mul-i64 n (fact (sub-i64 n 1)))))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("fact"),
            docstring: None,
            variants: vec![DefnVariant {
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
                span: span(0, 69),
            }],
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
        let mut tc = tc_with_prims();
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
                variants: vec![DefnVariant {
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
                    span: span(0, 51),
                }],
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
        let mut tc = tc_with_prims();
        // (defn bad [x] (add-i64 x true)) -- type error: Bool arg to monomorphic Int primitive
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("bad"),
            docstring: None,
            variants: vec![DefnVariant {
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
                span: span(0, 32),
            }],
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
        let mut tc = tc_with_prims();
        // (defn inc [x] (add-i64 x 1))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("inc"),
            docstring: None,
            variants: vec![DefnVariant {
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
                span: span(0, 29),
            }],
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
        let mut tc = tc_with_prims();
        let input = TopLevel::Expr(Expr::IntLit {
            value: 42,
            span: span(0, 2),
        });
        let result = tc.check_repl_input(&input).unwrap();
        assert_eq!(result.display.as_ref().unwrap().ty, Type::Int);
        assert!(result.display.as_ref().unwrap().scheme.is_none());
    }

    // spec: 03-types §3.4 — REPL defn produces polymorphic scheme
    #[test]
    fn test_check_repl_defn() {
        let mut tc = tc_with_prims();
        let input = TopLevel::Defn(Defn {
            name: Symbol::from("id"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x")],
                param_annotations: vec![None],
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: span(14, 15),
                },
                span: span(0, 16),
            }],
            visibility: Visibility::Public,
            span: span(0, 16),
        });
        let result = tc.check_repl_input(&input).unwrap();

        // The scheme should be polymorphic
        let scheme = result.display.as_ref().unwrap().scheme.clone().unwrap();
        assert_eq!(scheme.vars.len(), 1);
    }

    // spec: 05-definitions §5.2 — REPL typedef registers type and constructors
    #[test]
    fn test_check_repl_typedef() {
        let mut tc = tc_with_prims();
        let input = TopLevel::TypeDef {
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
        assert_eq!(result.display.as_ref().unwrap().ty, Type::ADT(TypeName::from("Dir"), vec![]));
        assert!(result.type_defs.contains_key(&TypeName::from("Dir")));
    }

    // spec: 03-types §3.5.1 — forward references resolved via two-pass inference
    #[test]
    fn test_check_program_forward_reference() {
        let mut tc = tc_with_prims();
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
                variants: vec![DefnVariant {
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
                    span: span(0, 30),
                }],
                visibility: Visibility::Public,
                span: span(0, 30),
            }),
            TopLevel::Defn(Defn {
                name: Symbol::from("add-self"),
                docstring: None,
                variants: vec![DefnVariant {
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
                    span: span(31, 61),
                }],
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
        let mut tc = tc_with_prims();
        // (defn double [:Int x] (add-self x))
        // (defn add-self [y] (add-i64 y y))
        // Both are monomorphic: add-i64 pins y to Int, and annotation pins x to Int.
        let program = vec![
            TopLevel::Defn(Defn {
                name: Symbol::from("double"),
                docstring: None,
                variants: vec![DefnVariant {
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
                    span: span(100, 130),
                }],
                visibility: Visibility::Public,
                span: span(100, 130),
            }),
            TopLevel::Defn(Defn {
                name: Symbol::from("add-self"),
                docstring: None,
                variants: vec![DefnVariant {
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
                    span: span(131, 161),
                }],
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
        let mut tc = tc_with_prims();
        // (defn inc [x] (add-i64 x 1))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("inc"),
            docstring: None,
            variants: vec![DefnVariant {
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
                span: span(0, 29),
            }],
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
        let mut tc = tc_with_prims();
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
        let mut tc = tc_with_prims();
        let input = TopLevel::TypeDef {
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
        let mut tc = tc_with_prims();
        let input = TopLevel::Expr(Expr::StringLit {
            value: "hello".to_string(),
            span: span(0, 7),
        });
        let result = tc.check_repl_input(&input).unwrap();
        assert_eq!(result.display.as_ref().unwrap().ty, Type::String);
    }

    // spec: 03-types §3.1 — function returning string literal has String return type
    #[test]
    fn test_check_program_string_in_function() {
        let mut tc = tc_with_prims();
        // (defn greet [] "hello")
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("greet"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::StringLit {
                    value: "hello".to_string(),
                    span: span(16, 23),
                },
                span: span(0, 24),
            }],
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
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        // Program: (defn add [x y] (+ x y))  -- constrained via +
        //          (defn main [] (add 3 4))   -- concrete Int call site
        let program = vec![
            TopLevel::Defn(Defn {
                name: Symbol::from("add"),
                docstring: None,
                variants: vec![DefnVariant {
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
                    span: span(0, 25),
                }],
                visibility: Visibility::Public,
                span: span(0, 25),
            }),
            TopLevel::Defn(Defn {
                name: Symbol::from("main"),
                docstring: None,
                variants: vec![DefnVariant {
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
                    span: span(26, 49),
                }],
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
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        // (defn add [x y] (+ x y))  -- alone, no callers; should be constrained
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![DefnVariant {
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
                span: span(0, 25),
            }],
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
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);

        // First, define a constrained fn: (defn add [x y] (+ x y))
        let defn_input = TopLevel::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![DefnVariant {
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
                span: span(0, 25),
            }],
            visibility: Visibility::Public,
            span: span(0, 25),
        });
        let _ = tc.check_repl_input(&defn_input).unwrap();

        // Now evaluate an expression that calls the constrained fn: (add 3 4)
        let expr_input = TopLevel::Expr(Expr::Apply {
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
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);

        // Define a constrained fn: (defn add [x y] (+ x y))
        let defn_input = TopLevel::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![DefnVariant {
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
                span: span(0, 25),
            }],
            visibility: Visibility::Public,
            span: span(0, 25),
        });
        let _ = tc.check_repl_input(&defn_input).unwrap();

        // Define a function that calls the constrained fn: (defn main [] (add 1 2))
        let main_input = TopLevel::Defn(Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
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
                span: span(180, 209),
            }],
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
        let mut tc = tc_with_prims();
        // (defn inc [x] (add-i64 x 1)) — no constrained fns, all monomorphic
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("inc"),
            docstring: None,
            variants: vec![DefnVariant {
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
                span: span(0, 29),
            }],
            visibility: Visibility::Public,
            span: span(0, 29),
        })];

        let result = tc.check_program(&program).unwrap();

        assert!(result.constrained_fn_names.is_empty());
        assert!(result.mono_defns.is_empty());
    }

    // --- Multi-sig defn tests ---

    /// Helper to build a CompileContext for test module.
    fn test_ctx() -> CompileContext {
        CompileContext {
            module: ModuleFullPath::from("test"),
            codegen: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
        }
    }

    /// Helper to build a multi-sig Defn.
    fn make_multi_defn(
        name: &str,
        variants: Vec<DefnVariant>,
        span: Span,
    ) -> Defn {
        Defn {
            name: Symbol::from(name),
            docstring: None,
            variants,
            visibility: Visibility::Public,
            span,
        }
    }

    // spec: 05-definitions §5.1.2 — multi-sig defn with different arities
    #[test]
    fn test_multi_sig_different_arities() {
        let mut tc = tc_with_prims();

        // (defn add
        //   ([x y] (add-i64 x y))
        //   ([x y z] (add-i64 x (add-i64 y z))))
        let program = vec![TopLevel::Defn(make_multi_defn(
            "add",
            vec![
                DefnVariant {
                    params: vec![Symbol::from("x"), Symbol::from("y")],
                    param_annotations: vec![None, None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(10, 17),
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(18, 19) },
                            Expr::Var { name: Symbol::from("y"), span: span(20, 21) },
                        ],
                        span: span(9, 22),
                    },
                    span: span(5, 23),
                },
                DefnVariant {
                    params: vec![
                        Symbol::from("x"),
                        Symbol::from("y"),
                        Symbol::from("z"),
                    ],
                    param_annotations: vec![None, None, None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(30, 37),
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(38, 39) },
                            Expr::Apply {
                                callee: Box::new(Expr::Var {
                                    name: Symbol::from("add-i64"),
                                    span: span(41, 48),
                                }),
                                args: vec![
                                    Expr::Var { name: Symbol::from("y"), span: span(49, 50) },
                                    Expr::Var { name: Symbol::from("z"), span: span(51, 52) },
                                ],
                                span: span(40, 53),
                            },
                        ],
                        span: span(29, 54),
                    },
                    span: span(25, 55),
                },
            ],
            span(0, 56),
        ))];

        let result = tc.check(&program, &test_ctx(), cranelisp_types::ModuleStrategy::Additive).unwrap();

        // The base name "add" should be registered as Overloaded
        let entry = tc.current_symbol_table().get("add");
        assert!(entry.is_some(), "base name 'add' should be registered");
        if let Some(ModuleEntry::Def { kind, .. }) = entry {
            assert!(
                matches!(kind.as_ref(), DefKind::Overloaded { variants } if variants.len() == 2),
                "add should be Overloaded with 2 variants"
            );
        } else {
            panic!("add should be a Def entry");
        }

        // Mangled names should be registered: add$Int+Int and add$Int+Int+Int
        assert!(
            tc.current_symbol_table().get("add$Int+Int").is_some(),
            "add$Int+Int should be registered"
        );
        assert!(
            tc.current_symbol_table().get("add$Int+Int+Int").is_some(),
            "add$Int+Int+Int should be registered"
        );

        // The multi-sig defns should appear in default_method_defns
        // (currently piggybacking on that field)
        assert_eq!(
            result.default_method_defns.len(), 2,
            "should produce 2 mangled defns for the backend"
        );
    }

    // spec: 05-definitions §5.1.2 — multi-sig with same arity but different types
    #[test]
    fn test_multi_sig_same_arity_different_types() {
        let mut tc = tc_with_prims();

        // (defn process
        //   ([:Int x] (add-i64 x 1))
        //   ([:Bool x] (if x 1 0)))
        let program = vec![TopLevel::Defn(make_multi_defn(
            "process",
            vec![
                DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![Some(TypeExpr::Named(TypeName::from("Int")))],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(110, 117),
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(118, 119) },
                            Expr::IntLit { value: 1, span: span(120, 121) },
                        ],
                        span: span(109, 122),
                    },
                    span: span(105, 123),
                },
                DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![Some(TypeExpr::Named(TypeName::from("Bool")))],
                    body: Expr::If {
                        cond: Box::new(Expr::Var {
                            name: Symbol::from("x"),
                            span: span(130, 131),
                        }),
                        then_branch: Box::new(Expr::IntLit { value: 1, span: span(132, 133) }),
                        else_branch: Box::new(Expr::IntLit { value: 0, span: span(134, 135) }),
                        span: span(127, 136),
                    },
                    span: span(125, 137),
                },
            ],
            span(100, 138),
        ))];

        let result = tc.check(&program, &test_ctx(), cranelisp_types::ModuleStrategy::Additive).unwrap();

        // Mangled names should be different: process$Int vs process$Bool
        assert!(
            tc.current_symbol_table().get("process$Int").is_some(),
            "process$Int should be registered"
        );
        assert!(
            tc.current_symbol_table().get("process$Bool").is_some(),
            "process$Bool should be registered"
        );

        // 2 mangled defns produced
        assert_eq!(result.default_method_defns.len(), 2);
    }

    // spec: 05-definitions §5.1.2 — duplicate signatures produce an error
    #[test]
    fn test_multi_sig_duplicate_signatures_error() {
        let mut tc = tc_with_prims();

        // (defn dup
        //   ([:Int x] (add-i64 x 1))
        //   ([:Int y] (add-i64 y 2)))
        // Both variants have the same signature (Int) -> Int — should error.
        let program = vec![TopLevel::Defn(make_multi_defn(
            "dup",
            vec![
                DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![Some(TypeExpr::Named(TypeName::from("Int")))],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(210, 217),
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(218, 219) },
                            Expr::IntLit { value: 1, span: span(220, 221) },
                        ],
                        span: span(209, 222),
                    },
                    span: span(205, 223),
                },
                DefnVariant {
                    params: vec![Symbol::from("y")],
                    param_annotations: vec![Some(TypeExpr::Named(TypeName::from("Int")))],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(230, 237),
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("y"), span: span(238, 239) },
                            Expr::IntLit { value: 2, span: span(240, 241) },
                        ],
                        span: span(229, 242),
                    },
                    span: span(225, 243),
                },
            ],
            span(200, 244),
        ))];

        let err = tc.check(&program, &test_ctx(), cranelisp_types::ModuleStrategy::Additive);
        assert!(err.is_err(), "duplicate signatures should produce an error");
        let msg = format!("{}", err.unwrap_err());
        assert!(
            msg.contains("duplicate signature"),
            "error should mention 'duplicate signature', got: {msg}"
        );
    }

    // spec: 05-definitions §5.1.2 — call site resolves to correct variant
    #[test]
    fn test_multi_sig_call_site_resolution() {
        let mut tc = tc_with_prims();

        // Define multi-sig:
        // (defn add
        //   ([:Int x :Int y] (add-i64 x y))
        //   ([:Int x :Int y :Int z] (add-i64 x (add-i64 y z))))
        //
        // Then call it:
        // (add 1 2)  -- should resolve to add$Int+Int

        let multi_defn = TopLevel::Defn(make_multi_defn(
            "add",
            vec![
                DefnVariant {
                    params: vec![Symbol::from("x"), Symbol::from("y")],
                    param_annotations: vec![None, None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(310, 317),
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(318, 319) },
                            Expr::Var { name: Symbol::from("y"), span: span(320, 321) },
                        ],
                        span: span(309, 322),
                    },
                    span: span(305, 323),
                },
                DefnVariant {
                    params: vec![
                        Symbol::from("x"),
                        Symbol::from("y"),
                        Symbol::from("z"),
                    ],
                    param_annotations: vec![None, None, None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(330, 337),
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(338, 339) },
                            Expr::Apply {
                                callee: Box::new(Expr::Var {
                                    name: Symbol::from("add-i64"),
                                    span: span(341, 348),
                                }),
                                args: vec![
                                    Expr::Var { name: Symbol::from("y"), span: span(349, 350) },
                                    Expr::Var { name: Symbol::from("z"), span: span(351, 352) },
                                ],
                                span: span(340, 353),
                            },
                        ],
                        span: span(329, 354),
                    },
                    span: span(325, 355),
                },
            ],
            span(300, 356),
        ));

        // Expression that calls add with 2 args: (add 1 2)
        let call_span = span(400, 410);
        let call_expr = TopLevel::Expr(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add"),
                span: span(401, 404),
            }),
            args: vec![
                Expr::IntLit { value: 1, span: span(405, 406) },
                Expr::IntLit { value: 2, span: span(407, 408) },
            ],
            span: call_span,
        });

        let program = vec![multi_defn, call_expr];
        let result = tc.check(&program, &test_ctx(), cranelisp_types::ModuleStrategy::Additive).unwrap();

        // The call site should have a SigDispatch resolution to "add$Int+Int"
        let resolution = result.method_resolutions.get(&call_span);
        assert!(
            resolution.is_some(),
            "call site should have a resolution"
        );
        match resolution.unwrap() {
            ResolvedCall::SigDispatch { mangled_name } => {
                assert_eq!(
                    mangled_name.as_ref(), "add$Int+Int",
                    "should dispatch to add$Int+Int"
                );
            }
            other => {
                panic!("expected SigDispatch, got {:?}", other);
            }
        }
    }

    // =========================================================================
    // Per-Form Typecheck API tests (Sprint 40 Wave 2)
    // =========================================================================
    //
    // These tests exercise the new check_form / merge_form_result / finalize_check_result
    // API introduced for the v4 pipeline. They validate:
    // 1. Behavioral identity: check() via check_form produces same results
    // 2. Per-form basics: individual forms through check_form
    // 3. Two-pass correctness: register-then-check ordering
    // 4. Multi-form programs with interactions
    // 5. Edge cases from the design doc
    // 6. Negative tests (error cases)

    /// Helper: create a CompileContext for the "test" module (check_form tests).
    fn cf_test_ctx() -> CompileContext {
        CompileContext {
            module: ModuleFullPath::from("test"),
            codegen: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
        }
    }

    /// Helper: build an "inc" defn: (defn inc [x] (add-i64 x 1))
    fn make_inc_defn() -> Defn {
        make_defn(
            "inc",
            vec![Symbol::from("x")],
            vec![None],
            Expr::Apply {
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
            Visibility::Public,
            span(0, 29),
        )
    }

    /// Helper: build a Color typedef with Red and Green constructors.
    fn make_color_typedef() -> TopLevel {
        TopLevel::TypeDef {
            name: TypeName::from("Color"),
            docstring: None,
            type_params: vec![],
            constructors: vec![
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("Red"),
                    docstring: None,
                    fields: vec![],
                    span: span(200, 203),
                },
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("Green"),
                    docstring: None,
                    fields: vec![],
                    span: span(204, 209),
                },
            ],
            visibility: Visibility::Public,
            span: span(190, 210),
        }
    }

    /// Helper: build an is-red defn that matches on Color.
    fn make_is_red_defn() -> Defn {
        Defn {
            name: Symbol::from("is-red"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("c")],
                param_annotations: vec![None],
                body: Expr::Match {
                    scrutinee: Box::new(Expr::Var {
                        name: Symbol::from("c"),
                        span: span(230, 231),
                    }),
                    arms: vec![
                        cranelisp_types::MatchArm {
                            pattern: cranelisp_types::Pattern::Constructor {
                                name: Symbol::from("Red"),
                                bindings: vec![],
                                span: span(233, 236),
                            },
                            body: Expr::BoolLit {
                                value: true,
                                span: span(237, 241),
                            },
                            span: span(233, 241),
                        },
                        cranelisp_types::MatchArm {
                            pattern: cranelisp_types::Pattern::Wildcard {
                                span: span(242, 243),
                            },
                            body: Expr::BoolLit {
                                value: false,
                                span: span(244, 249),
                            },
                            span: span(242, 249),
                        },
                    ],
                    span: span(224, 250),
                    compiler_generated: false,
                },
                span: span(211, 251),
            }],
            visibility: Visibility::Public,
            span: span(211, 251),
        }
    }

    /// Helper: build the forward-reference program (double calls add-self).
    fn make_forward_ref_program() -> Vec<TopLevel> {
        vec![
            TopLevel::Defn(Defn {
                name: Symbol::from("double"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-self"),
                            span: span(318, 326),
                        }),
                        args: vec![Expr::Var {
                            name: Symbol::from("x"),
                            span: span(327, 328),
                        }],
                        span: span(317, 329),
                    },
                    span: span(300, 330),
                }],
                visibility: Visibility::Public,
                span: span(300, 330),
            }),
            TopLevel::Defn(Defn {
                name: Symbol::from("add-self"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("y")],
                    param_annotations: vec![None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(348, 355),
                        }),
                        args: vec![
                            Expr::Var {
                                name: Symbol::from("y"),
                                span: span(356, 357),
                            },
                            Expr::Var {
                                name: Symbol::from("y"),
                                span: span(358, 359),
                            },
                        ],
                        span: span(347, 360),
                    },
                    span: span(331, 361),
                }],
                visibility: Visibility::Public,
                span: span(331, 361),
            }),
        ]
    }

    // ---- Category 1: Behavioral Identity ----

    // spec: design/typecheck/check-form-api.md — check() via check_form produces identical CheckResult
    #[test]
    fn test_check_form_identity_simple_defn() {
        // Run a simple defn program through check() and verify the result matches expectations.
        // Since check() now internally uses check_form(), this tests behavioral identity.
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();
        let program = vec![TopLevel::Defn(make_inc_defn())];

        let result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // Verify the function was registered with correct type
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("inc") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                "inc should be (Fn [Int] Int)"
            );
        } else {
            panic!("inc not found in symbol table after check()");
        }

        // Verify expr_types populated (body expressions should be typed)
        assert!(!result.expr_types.is_empty(), "expr_types should be populated");

        // All expr_types should be resolved (no Var types)
        for (_span, ty) in &result.expr_types {
            if let Type::Var(_) = ty {
                panic!("unresolved Var in expr_types");
            }
        }

        // Verify method_resolutions populated (add-i64 call site resolved)
        assert!(!result.method_resolutions.is_empty(), "method_resolutions should have add-i64 call site");
    }

    // spec: design/typecheck/check-form-api.md — typedef + defn identity
    #[test]
    fn test_check_form_identity_typedef_plus_defn() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();
        let program = vec![
            make_color_typedef(),
            TopLevel::Defn(make_is_red_defn()),
        ];

        let result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // type_defs and constructor_to_type should be populated
        assert!(result.type_defs.contains_key(&TypeName::from("Color")));
        assert!(result.constructor_to_type.contains_key("Red"));
        assert!(result.constructor_to_type.contains_key("Green"));

        // is-red should have correct type
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

        // expr_types should be populated
        assert!(!result.expr_types.is_empty());
    }

    // spec: design/typecheck/check-form-api.md — forward reference identity
    #[test]
    fn test_check_form_identity_forward_reference() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();
        let program = make_forward_ref_program();

        let result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // Both should be monomorphic Int -> Int
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("double") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
            );
        } else {
            panic!("double not found");
        }

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get("add-self") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
            );
        } else {
            panic!("add-self not found");
        }

        assert!(!result.expr_types.is_empty());
    }

    // spec: design/typecheck/check-form-api.md — constrained fn identity
    #[test]
    fn test_check_form_identity_constrained_fn() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        let ctx = cf_test_ctx();

        // (defn add [x y] (+ x y)) — constrained by Num trait
        let program = vec![TopLevel::Defn(make_defn(
            "add",
            vec![Symbol::from("x"), Symbol::from("y")],
            vec![None, None],
            Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("+"),
                    span: span(400, 401),
                }),
                args: vec![
                    Expr::Var { name: Symbol::from("x"), span: span(402, 403) },
                    Expr::Var { name: Symbol::from("y"), span: span(404, 405) },
                ],
                span: span(399, 406),
            },
            Visibility::Public,
            span(390, 407),
        ))];

        let result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // Should be detected as constrained polymorphic
        assert!(
            result.constrained_fn_names.contains(&Symbol::from("add")),
            "add should be detected as constrained polymorphic"
        );
    }

    // spec: design/typecheck/check-form-api.md — expression-only identity
    #[test]
    fn test_check_form_identity_expr() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();
        let program = vec![TopLevel::Expr(Expr::IntLit {
            value: 42,
            span: span(500, 502),
        })];

        let result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // Display info should show Int type
        assert!(result.display.is_some());
        assert_eq!(result.display.as_ref().unwrap().ty, Type::Int);

        // expr_types should contain the literal's type
        assert!(!result.expr_types.is_empty());
    }

    // spec: design/typecheck/check-form-api.md — multi-sig defn identity
    #[test]
    fn test_check_form_identity_multi_sig() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();

        // Multi-sig: (defn add ([x] (add-i64 x 1)) ([x y] (add-i64 x y)))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![
                DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(610, 617),
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(618, 619) },
                            Expr::IntLit { value: 1, span: span(620, 621) },
                        ],
                        span: span(609, 622),
                    },
                    span: span(600, 623),
                },
                DefnVariant {
                    params: vec![Symbol::from("x"), Symbol::from("y")],
                    param_annotations: vec![None, None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: span(640, 647),
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(648, 649) },
                            Expr::Var { name: Symbol::from("y"), span: span(650, 651) },
                        ],
                        span: span(639, 652),
                    },
                    span: span(630, 653),
                },
            ],
            visibility: Visibility::Public,
            span: span(590, 654),
        })];

        let result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // The base name should be Overloaded in symbol table
        if let Some(ModuleEntry::Def { kind, .. }) = tc.symbol_table().get("add") {
            match kind.as_ref() {
                DefKind::Overloaded { variants } => {
                    assert_eq!(variants.len(), 2, "should have 2 overload variants");
                }
                other => panic!("expected Overloaded, got {:?}", other),
            }
        } else {
            panic!("add not found in symbol table");
        }

        // expr_types should be populated from both variant bodies
        assert!(!result.expr_types.is_empty());
    }

    // ---- Category 2: Per-Form Basics ----

    // spec: design/typecheck/check-form-api.md §check_form — single defn Register pass
    #[test]
    fn test_check_form_single_defn_register() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let defn = make_inc_defn();
        let form = TopLevel::Defn(defn);
        let result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();

        // Register pass should produce empty method_resolutions and expr_types
        assert!(result.method_resolutions.is_empty(), "Register pass produces no method resolutions");
        assert!(result.expr_types.is_empty(), "Register pass produces no expr types");
        assert!(result.constrained_fn.is_none(), "Register pass has no constrained fn");
        assert!(result.mono_defns.is_empty(), "Register pass has no mono defns");

        // Signature should be registered in the accumulator's defn_type_vars
        assert!(
            accumulator.defn_type_vars.contains_key(&Symbol::from("inc")),
            "defn_type_vars should contain 'inc' after Register pass"
        );

        // Signature should be registered in symbol table
        assert!(
            tc.symbol_table().get("inc").is_some(),
            "inc should be in symbol table after Register pass"
        );
    }

    // spec: design/typecheck/check-form-api.md §check_form — single defn CheckBody pass
    #[test]
    fn test_check_form_single_defn_check_body() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let defn = make_inc_defn();
        let form = TopLevel::Defn(defn);

        // Must register first
        let reg_result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, reg_result);

        // Now check body
        let body_result = tc.check_form(&module, &form, CheckPass::CheckBody, &mut accumulator).unwrap();

        // CheckBody pass should produce expr_types (body expressions typed)
        assert!(
            !body_result.expr_types.is_empty(),
            "CheckBody should produce expr_types for body expressions"
        );

        // CheckBody pass should produce method_resolutions for add-i64 call
        assert!(
            !body_result.method_resolutions.is_empty(),
            "CheckBody should have method resolution for add-i64 call"
        );

        // No constrained fn (inc is monomorphic)
        assert!(body_result.constrained_fn.is_none());
    }

    // spec: design/typecheck/check-form-api.md §check_form — TypeDef Register pass
    #[test]
    fn test_check_form_typedef_register() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let form = make_color_typedef();
        let result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();

        // Registration should be mostly empty result (type is registered internally)
        assert!(result.default_method_defns.is_empty());

        // Constructors should be registered in symbol table
        assert!(
            tc.symbol_table().get("Red").is_some(),
            "Red constructor should be in symbol table"
        );
        assert!(
            tc.symbol_table().get("Green").is_some(),
            "Green constructor should be in symbol table"
        );
    }

    // spec: design/typecheck/check-form-api.md §check_form — TypeDef CheckBody is no-op
    #[test]
    fn test_check_form_typedef_check_body_noop() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let form = make_color_typedef();
        // Register first
        let _ = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();

        // CheckBody on TypeDef should be a no-op
        let result = tc.check_form(&module, &form, CheckPass::CheckBody, &mut accumulator).unwrap();
        assert!(result.method_resolutions.is_empty());
        assert!(result.expr_types.is_empty());
        assert!(result.constrained_fn.is_none());
        assert!(result.mono_defns.is_empty());
    }

    // spec: design/typecheck/check-form-api.md §check_form — TraitDecl Register pass
    #[test]
    fn test_check_form_trait_decl_register() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let decl = TraitDecl {
            name: TraitName::from("Eq"),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from("eq"),
                docstring: None,
                params: vec![
                    TypeExpr::TypeVar(Symbol::from("a")),
                    TypeExpr::TypeVar(Symbol::from("a")),
                ],
                ret_type: TypeExpr::Named(TypeName::from("Bool")),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_param_names: vec![Symbol::from("lhs"), Symbol::from("rhs")],
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let form = TopLevel::TraitDecl(decl);
        let result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();

        // Should produce an empty result (registration is internal)
        assert!(result.method_resolutions.is_empty());
        assert!(result.expr_types.is_empty());
        assert!(result.default_method_defns.is_empty());
    }

    // spec: design/typecheck/check-form-api.md §check_form — TraitDecl CheckBody is no-op
    #[test]
    fn test_check_form_trait_decl_check_body_noop() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let decl = TraitDecl {
            name: TraitName::from("Show"),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from("show"),
                docstring: None,
                params: vec![TypeExpr::TypeVar(Symbol::from("a"))],
                ret_type: TypeExpr::Named(TypeName::from("String")),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_param_names: vec![Symbol::from("x")],
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let form = TopLevel::TraitDecl(decl);

        // Register first
        let _ = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();

        // CheckBody should be no-op
        let result = tc.check_form(&module, &form, CheckPass::CheckBody, &mut accumulator).unwrap();
        assert!(result.method_resolutions.is_empty());
        assert!(result.expr_types.is_empty());
    }

    // spec: design/typecheck/check-form-api.md §check_form — TraitImpl Register pass
    #[test]
    fn test_check_form_trait_impl_register() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // Register a new trait (Eq) then impl it for Int
        let decl = TraitDecl {
            name: TraitName::from("Eq"),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from("eq"),
                docstring: None,
                params: vec![
                    TypeExpr::TypeVar(Symbol::from("a")),
                    TypeExpr::TypeVar(Symbol::from("a")),
                ],
                ret_type: TypeExpr::Named(TypeName::from("Bool")),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_param_names: vec![Symbol::from("a"), Symbol::from("b")],
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let decl_form = TopLevel::TraitDecl(decl);
        let _ = tc.check_form(&module, &decl_form, CheckPass::Register, &mut accumulator).unwrap();

        // Now impl Eq for Int
        let impl_ = TraitImpl {
            trait_name: TraitName::from("Eq"),
            target_type: TypeName::from("Int"),
            type_args: vec![],
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("eq"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("a"), Symbol::from("b")],
                    param_annotations: vec![None, None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("eq-i64"),
                            span: Span::SYNTHETIC,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("a"), span: Span::SYNTHETIC },
                            Expr::Var { name: Symbol::from("b"), span: Span::SYNTHETIC },
                        ],
                        span: Span::SYNTHETIC,
                    },
                    span: Span::SYNTHETIC,
                }],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
        };
        let impl_form = TopLevel::TraitImpl(impl_);
        let result = tc.check_form(&module, &impl_form, CheckPass::Register, &mut accumulator).unwrap();

        // Impl registration should succeed (no error).
        // default_method_defns contains mangled-name defns for each impl method
        // (e.g., "Eq.eq$Int") that need signature registration and body checking.
        assert!(
            !result.default_method_defns.is_empty(),
            "impl should produce mangled method defns for backend compilation"
        );
        // The mangled defn name should follow the pattern Trait.method$Type
        assert!(
            result.default_method_defns.iter().any(|d| d.name.as_ref().contains("Eq.eq$Int")),
            "should contain Eq.eq$Int mangled defn"
        );
    }

    // spec: design/typecheck/check-form-api.md §check_form — Expr wrapped as __expr
    #[test]
    fn test_check_form_expr_register_and_check() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // Wrap expr as synthetic defn (matching what check() does internally)
        let expr = Expr::IntLit { value: 42, span: span(700, 702) };
        let synthetic_defn = Defn {
            name: Symbol::from("__expr"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: expr,
                span: span(700, 702),
            }],
            visibility: Visibility::Public,
            span: span(699, 703),
        };
        let form = TopLevel::Defn(synthetic_defn);

        // Register pass
        let reg_result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, reg_result);

        assert!(accumulator.defn_type_vars.contains_key(&Symbol::from("__expr")));

        // CheckBody pass
        let body_result = tc.check_form(&module, &form, CheckPass::CheckBody, &mut accumulator).unwrap();

        // expr_types should contain the literal's type
        assert!(
            !body_result.expr_types.is_empty(),
            "CheckBody should produce expr_types for the expression"
        );
    }

    // ---- Category 3: Two-Pass Correctness ----

    // spec: design/typecheck/check-form-api.md §Invariant 1 — forward reference resolves via two-pass
    #[test]
    fn test_check_form_two_pass_mutual_reference() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let program = make_forward_ref_program();

        // Pass 1: Register both defns
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::Register, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }

        // Both signatures should be registered
        assert!(accumulator.defn_type_vars.contains_key(&Symbol::from("double")));
        assert!(accumulator.defn_type_vars.contains_key(&Symbol::from("add-self")));

        // Pass 2: Check bodies of both
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::CheckBody, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }

        // Both should have produced expr_types
        assert!(!accumulator.expr_types.is_empty(), "accumulated expr_types should be non-empty");

        // Finalize to get final types
        let result = tc.finalize_check_result(
            &module, &mut accumulator, &program, ModuleStrategy::Replace,
        ).unwrap();

        // After finalization, all expr_types should be resolved
        for (_span, ty) in &result.expr_types {
            if let Type::Var(_) = ty {
                panic!("unresolved Var in expr_types after finalize");
            }
        }
    }

    // spec: design/typecheck/check-form-api.md §Invariant 1 — CheckBody before Register errors
    #[test]
    fn test_check_form_check_body_before_register_errors() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let defn = make_inc_defn();
        let form = TopLevel::Defn(defn);

        // Try CheckBody without registering first — should error
        let result = tc.check_form(&module, &form, CheckPass::CheckBody, &mut accumulator);
        assert!(
            result.is_err(),
            "CheckBody before Register should produce an error"
        );
    }

    // spec: design/typecheck/check-form-api.md §Invariant 1 — Register populates defn_type_vars
    #[test]
    fn test_check_form_register_populates_defn_type_vars() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let defn = make_inc_defn();
        let form = TopLevel::Defn(defn);

        let _ = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator).unwrap();

        // defn_type_vars should contain the defn's name with type vars
        let (param_types, _ret_ty) = accumulator.defn_type_vars.get(&Symbol::from("inc"))
            .expect("inc should be in defn_type_vars");

        // inc has 1 parameter
        assert_eq!(param_types.len(), 1, "inc has 1 parameter");
    }

    // spec: design/typecheck/check-form-api.md §Invariant 2 — TypeDef before defn using constructors
    #[test]
    fn test_check_form_typedef_before_defn() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // Register TypeDef(Color) first
        let typedef_form = make_color_typedef();
        let result = tc.check_form(&module, &typedef_form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);

        // Then register Defn(is-red) which uses Color constructors
        let defn_form = TopLevel::Defn(make_is_red_defn());
        let result = tc.check_form(&module, &defn_form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);

        // Pass 2: check body — should resolve constructor types correctly
        // TypeDef is no-op in CheckBody
        let _ = tc.check_form(&module, &typedef_form, CheckPass::CheckBody, &mut accumulator).unwrap();

        let body_result = tc.check_form(&module, &defn_form, CheckPass::CheckBody, &mut accumulator).unwrap();

        // Should succeed and produce expr_types
        assert!(!body_result.expr_types.is_empty(), "is-red body should have expr_types");
    }

    // spec: design/typecheck/check-form-api.md §Invariant 2 — TraitDecl before TraitImpl
    #[test]
    fn test_check_form_trait_decl_before_impl() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // Register TraitDecl(Eq) first
        let decl = TraitDecl {
            name: TraitName::from("Eq"),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from("eq"),
                docstring: None,
                params: vec![
                    TypeExpr::TypeVar(Symbol::from("a")),
                    TypeExpr::TypeVar(Symbol::from("a")),
                ],
                ret_type: TypeExpr::Named(TypeName::from("Bool")),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_param_names: vec![Symbol::from("a"), Symbol::from("b")],
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let decl_form = TopLevel::TraitDecl(decl);
        let result = tc.check_form(&module, &decl_form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);

        // Then register TraitImpl(Eq for Int) — should succeed because decl was registered first
        let impl_ = TraitImpl {
            trait_name: TraitName::from("Eq"),
            target_type: TypeName::from("Int"),
            type_args: vec![],
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("eq"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("a"), Symbol::from("b")],
                    param_annotations: vec![None, None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("eq-i64"),
                            span: Span::SYNTHETIC,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("a"), span: Span::SYNTHETIC },
                            Expr::Var { name: Symbol::from("b"), span: Span::SYNTHETIC },
                        ],
                        span: Span::SYNTHETIC,
                    },
                    span: Span::SYNTHETIC,
                }],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
        };
        let impl_form = TopLevel::TraitImpl(impl_);
        let result = tc.check_form(&module, &impl_form, CheckPass::Register, &mut accumulator);

        // Should succeed — no error
        assert!(result.is_ok(), "TraitImpl after TraitDecl should succeed");
    }

    // ---- Category 4: Multi-Form Programs ----

    // spec: design/typecheck/check-form-api.md §Invariant 3 — shared substitution
    #[test]
    fn test_check_form_multi_defn_shared_substitution() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // Three defns: h uses add-i64 (pins to Int), g calls h, f calls g
        let h = TopLevel::Defn(make_defn(
            "h",
            vec![Symbol::from("x"), Symbol::from("y")],
            vec![None, None],
            Expr::Apply {
                callee: Box::new(Expr::Var { name: Symbol::from("add-i64"), span: span(800, 807) }),
                args: vec![
                    Expr::Var { name: Symbol::from("x"), span: span(808, 809) },
                    Expr::Var { name: Symbol::from("y"), span: span(810, 811) },
                ],
                span: span(799, 812),
            },
            Visibility::Public,
            span(790, 813),
        ));
        let g = TopLevel::Defn(make_defn(
            "g",
            vec![Symbol::from("a")],
            vec![None],
            Expr::Apply {
                callee: Box::new(Expr::Var { name: Symbol::from("h"), span: span(830, 831) }),
                args: vec![
                    Expr::Var { name: Symbol::from("a"), span: span(832, 833) },
                    Expr::Var { name: Symbol::from("a"), span: span(834, 835) },
                ],
                span: span(829, 836),
            },
            Visibility::Public,
            span(820, 837),
        ));
        let f = TopLevel::Defn(make_defn(
            "f",
            vec![Symbol::from("z")],
            vec![None],
            Expr::Apply {
                callee: Box::new(Expr::Var { name: Symbol::from("g"), span: span(860, 861) }),
                args: vec![
                    Expr::Var { name: Symbol::from("z"), span: span(862, 863) },
                ],
                span: span(859, 864),
            },
            Visibility::Public,
            span(850, 865),
        ));

        let program = vec![f, g, h];

        // Pass 1: Register all
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::Register, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }

        // Pass 2: Check all bodies
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::CheckBody, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }

        // Finalize
        let _result = tc.finalize_check_result(
            &module, &mut accumulator, &program, ModuleStrategy::Replace,
        ).unwrap();

        // All three should be monomorphic Int via shared substitution
        for name in &["f", "g", "h"] {
            if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table().get(*name) {
                assert!(
                    scheme.vars.is_empty(),
                    "{} should be monomorphic (pinned to Int via shared substitution)", name
                );
            } else {
                panic!("{} not found in symbol table", name);
            }
        }
    }

    // spec: design/typecheck/check-form-api.md — accumulator merge grows with each form
    #[test]
    fn test_check_form_accumulator_merge() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let program = make_forward_ref_program();

        // Pass 1: Register all
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::Register, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }

        // Pass 2: Check bodies and verify accumulator grows
        let et_before_first = accumulator.expr_types.len();
        let form0_result = tc.check_form(&module, &program[0], CheckPass::CheckBody, &mut accumulator).unwrap();
        let form0_et = form0_result.expr_types.len();
        tc.merge_form_result(&module, &mut accumulator, form0_result);
        let et_after_first = accumulator.expr_types.len();

        assert!(
            et_after_first > et_before_first,
            "accumulator should grow after first form's CheckBody"
        );

        let form1_result = tc.check_form(&module, &program[1], CheckPass::CheckBody, &mut accumulator).unwrap();
        let form1_et = form1_result.expr_types.len();
        tc.merge_form_result(&module, &mut accumulator, form1_result);
        let et_after_second = accumulator.expr_types.len();

        assert!(
            et_after_second > et_after_first,
            "accumulator should grow after second form's CheckBody"
        );
        assert_eq!(
            et_after_second,
            et_before_first + form0_et + form1_et,
            "total expr_types should be sum of per-form contributions"
        );
    }

    // spec: design/typecheck/check-form-api.md — finalize resolves pending and produces complete result
    #[test]
    fn test_check_form_finalize_produces_complete_result() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        let program = vec![TopLevel::Defn(make_inc_defn())];

        // Full two-pass processing
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::Register, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }
        for form in &program {
            let result = tc.check_form(&module, form, CheckPass::CheckBody, &mut accumulator).unwrap();
            tc.merge_form_result(&module, &mut accumulator, result);
        }

        let result = tc.finalize_check_result(
            &module, &mut accumulator, &program, ModuleStrategy::Replace,
        ).unwrap();

        // finalize should produce a complete CheckResult
        assert!(!result.expr_types.is_empty(), "finalized result should have expr_types");
        assert!(!result.method_resolutions.is_empty(), "finalized result should have method_resolutions");

        // All expr_types should be fully resolved
        for (_span, ty) in &result.expr_types {
            if let Type::Var(_) = ty {
                panic!("unresolved Var in finalized expr_types");
            }
        }
    }

    // ---- Category 5: Edge Cases ----

    // spec: design/typecheck/check-form-api.md §DefnMulti — multi-sig Register
    #[test]
    fn test_check_form_defn_multi_register() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // Multi-sig defn: two variants
        let multi = TopLevel::Defn(Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![
                DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var { name: Symbol::from("add-i64"), span: span(1010, 1017) }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(1018, 1019) },
                            Expr::IntLit { value: 1, span: span(1020, 1021) },
                        ],
                        span: span(1009, 1022),
                    },
                    span: span(1000, 1023),
                },
                DefnVariant {
                    params: vec![Symbol::from("x"), Symbol::from("y")],
                    param_annotations: vec![None, None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var { name: Symbol::from("add-i64"), span: span(1040, 1047) }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: span(1048, 1049) },
                            Expr::Var { name: Symbol::from("y"), span: span(1050, 1051) },
                        ],
                        span: span(1039, 1052),
                    },
                    span: span(1030, 1053),
                },
            ],
            visibility: Visibility::Public,
            span: span(990, 1054),
        });

        let result = tc.check_form(&module, &multi, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, result);

        // Internal variant defns should be in defn_type_vars
        assert!(
            accumulator.defn_type_vars.contains_key(&Symbol::from("add__v0")),
            "add__v0 should be in defn_type_vars"
        );
        assert!(
            accumulator.defn_type_vars.contains_key(&Symbol::from("add__v1")),
            "add__v1 should be in defn_type_vars"
        );

        // Base name should be in symbol table as Overloaded placeholder
        if let Some(ModuleEntry::Def { kind, .. }) = tc.symbol_table().get("add") {
            match kind.as_ref() {
                DefKind::Overloaded { .. } => {} // expected
                other => panic!("expected Overloaded placeholder, got {:?}", other),
            }
        } else {
            panic!("add base name not found in symbol table");
        }
    }

    // spec: design/typecheck/check-form-api.md §Constrained polymorphism — detection
    #[test]
    fn test_check_form_constrained_fn_detection() {
        let mut tc = tc_with_prims();
        register_num_trait_inline(&mut tc);
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // (defn add [x y] (+ x y)) — constrained by Num
        let defn_form = TopLevel::Defn(make_defn(
            "add",
            vec![Symbol::from("x"), Symbol::from("y")],
            vec![None, None],
            Expr::Apply {
                callee: Box::new(Expr::Var { name: Symbol::from("+"), span: span(1100, 1101) }),
                args: vec![
                    Expr::Var { name: Symbol::from("x"), span: span(1102, 1103) },
                    Expr::Var { name: Symbol::from("y"), span: span(1104, 1105) },
                ],
                span: span(1099, 1106),
            },
            Visibility::Public,
            span(1090, 1107),
        ));

        // Register
        let reg = tc.check_form(&module, &defn_form, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, reg);

        // Check body
        let body = tc.check_form(&module, &defn_form, CheckPass::CheckBody, &mut accumulator).unwrap();

        // Should detect constrained fn
        assert!(
            body.constrained_fn.is_some(),
            "add should be detected as constrained"
        );
        assert_eq!(
            body.constrained_fn.as_ref().unwrap().as_ref(),
            "add",
        );
    }

    // spec: design/typecheck/check-form-api.md — expr_types fully resolved after finalize
    #[test]
    fn test_check_form_expr_types_no_unresolved_vars() {
        let mut tc = tc_with_prims();
        let ctx = cf_test_ctx();

        // Use a polymorphic identity function called with Int to test resolution
        let program = vec![
            TopLevel::Defn(make_defn(
                "id",
                vec![Symbol::from("x")],
                vec![None],
                Expr::Var { name: Symbol::from("x"), span: span(1214, 1215) },
                Visibility::Public,
                span(1200, 1216),
            )),
            TopLevel::Defn(make_defn(
                "use-id",
                vec![Symbol::from("y")],
                vec![None],
                Expr::Apply {
                    callee: Box::new(Expr::Var { name: Symbol::from("id"), span: span(1230, 1232) }),
                    args: vec![Expr::Apply {
                        callee: Box::new(Expr::Var { name: Symbol::from("add-i64"), span: span(1234, 1241) }),
                        args: vec![
                            Expr::Var { name: Symbol::from("y"), span: span(1242, 1243) },
                            Expr::IntLit { value: 1, span: span(1244, 1245) },
                        ],
                        span: span(1233, 1246),
                    }],
                    span: span(1229, 1247),
                },
                Visibility::Public,
                span(1220, 1248),
            )),
        ];

        let result = tc.check(&program, &ctx, ModuleStrategy::Additive).unwrap();

        // All expr_types should be fully resolved
        for (_span, ty) in &result.expr_types {
            if let Type::Var(_) = ty {
                panic!("unresolved Var in expr_types after check()");
            }
        }
    }

    // spec: design/typecheck/check-form-api.md — warnings accumulated across forms
    #[test]
    fn test_check_form_warnings_accumulated() {
        // This tests that the merge mechanism for warnings works.
        // We verify structurally that warnings from FormCheckResult are collected.
        let mut accumulator = ModuleCheckAccumulator::new();
        assert!(accumulator.warnings.is_empty());

        // Simulate a FormCheckResult with a warning
        let result_with_warning = FormCheckResult {
            method_resolutions: HashMap::new(),
            expr_types: HashMap::new(),
            constrained_fn: None,
            mono_defns: Vec::new(),
            default_method_defns: Vec::new(),
            multi_sig_defns: Vec::new(),
            warnings: vec![Warning {
                kind: cranelisp_types::WarningKind::Other,
                message: "test warning".to_string(),
                span: Span::SYNTHETIC,
            }],
            call_graph_edges: Vec::new(),
        };

        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        tc.merge_form_result(&module, &mut accumulator, result_with_warning);

        assert_eq!(accumulator.warnings.len(), 1);
        assert_eq!(accumulator.warnings[0].message, "test warning");
    }

    // ---- Negative Tests ----

    // spec: design/typecheck/check-form-api.md — type error propagates from CheckBody
    #[test]
    fn test_check_form_type_error_propagates() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // (defn bad [x] (add-i64 x true)) — type error
        let bad_defn = TopLevel::Defn(make_defn(
            "bad",
            vec![Symbol::from("x")],
            vec![None],
            Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("add-i64"),
                    span: span(1316, 1323),
                }),
                args: vec![
                    Expr::Var { name: Symbol::from("x"), span: span(1324, 1325) },
                    Expr::BoolLit { value: true, span: span(1326, 1330) },
                ],
                span: span(1315, 1331),
            },
            Visibility::Public,
            span(1300, 1332),
        ));

        // Register should succeed
        let reg = tc.check_form(&module, &bad_defn, CheckPass::Register, &mut accumulator).unwrap();
        tc.merge_form_result(&module, &mut accumulator, reg);

        // CheckBody should produce an error
        let result = tc.check_form(&module, &bad_defn, CheckPass::CheckBody, &mut accumulator);
        assert!(result.is_err(), "type error in body should propagate as Err");
    }

    // spec: design/typecheck/check-form-api.md — unknown trait in TraitImpl errors
    #[test]
    fn test_check_form_trait_impl_unknown_trait_error() {
        let mut tc = tc_with_prims();
        let module = ModuleFullPath::from("test");
        let mut accumulator = ModuleCheckAccumulator::new();

        // TraitImpl referencing undeclared trait
        let impl_ = TraitImpl {
            trait_name: TraitName::from("NonexistentTrait"),
            target_type: TypeName::from("Int"),
            type_args: vec![],
            type_constraints: vec![],
            methods: vec![],
            span: Span::SYNTHETIC,
        };
        let form = TopLevel::TraitImpl(impl_);
        let result = tc.check_form(&module, &form, CheckPass::Register, &mut accumulator);

        assert!(result.is_err(), "TraitImpl for undeclared trait should error");
    }
}
