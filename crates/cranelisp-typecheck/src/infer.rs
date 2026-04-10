//! Expression type inference: one method per Expr variant.
//!
//! `infer_expr` dispatches to per-variant helpers. Each helper is typically
//! 10-40 lines, independently testable. Addresses audit HIGH-1 (monolithic infer_expr).

use std::collections::HashMap;

use cranelisp_types::{
    CranelispError, Expr, MatchArm, ModuleEntry, Pattern, ResolvedCall, Scheme, Span, Symbol,
    Type, TypeExpr,
};

use crate::checker::{CheckState, TypeChecker};
use crate::resolve::resolve_type_expr;
use crate::scheme::mono;

impl TypeChecker {

    /// Convenience wrapper for tests — creates a temporary CheckState from self.state.
    /// Used by test code that doesn't want to manage state explicitly.
    #[cfg(test)]
    pub(crate) fn infer_expr_for_test(&mut self, expr: &Expr) -> Result<Type, CranelispError> {
        let mut state = std::mem::replace(&mut self.state, CheckState::new(cranelisp_types::ModuleFullPath::from("")));
        let result = self.infer_expr(&mut state, expr);
        self.state = state;
        result
    }

    /// Infer the type of an expression. Main dispatch method.
    pub(crate) fn infer_expr(&self, state: &mut CheckState, expr: &Expr) -> Result<Type, CranelispError> {
        match expr {
            Expr::IntLit { span, .. } => self.infer_int_lit(state, *span),
            Expr::FloatLit { span, .. } => self.infer_float_lit(state, *span),
            Expr::BoolLit { span, .. } => self.infer_bool_lit(state, *span),
            Expr::Var { name, span } => self.infer_var(state, name, *span),
            Expr::Let {
                bindings,
                body,
                span,
            } => self.infer_let(state, bindings, body, *span),
            Expr::If {
                cond,
                then_branch,
                else_branch,
                span,
            } => self.infer_if(state, cond, then_branch, else_branch, *span),
            Expr::Lambda {
                params,
                param_annotations,
                body,
                span,
            } => self.infer_lambda(state, params, param_annotations, body, *span),
            Expr::Apply {
                callee,
                args,
                span,
            } => {
                // `trace` is not a parser keyword — it arrives as Apply.
                // Intercept when callee is the `trace` special form from primitives.
                if let Expr::Var { name, .. } = callee.as_ref()
                    && &**name == "trace" && self.is_trace_in_scope(state)
                {
                    if args.len() != 1 {
                        return Err(CranelispError::TypeError {
                            message: "trace requires exactly one expression".into(),
                            span: *span,
                        });
                    }
                    return self.infer_trace(state, &args[0], *span);
                }
                self.infer_apply(state, callee, args, *span)
            }
            Expr::Match {
                scrutinee,
                arms,
                span,
                ..
            } => self.infer_match(state, scrutinee, arms, *span),
            Expr::Annotate {
                annotation,
                expr,
                span,
            } => self.infer_annotate(state, annotation, expr, *span),

            Expr::StringLit { span, .. } => self.infer_string_lit(state, *span),
            Expr::VecLit { elements, span } => self.infer_vec_lit(state, elements, *span),
            Expr::Trace { body, span, .. } => self.infer_trace(state, body, *span),
            Expr::RunTests { init, pass_fn, fail_fn, span, .. } => {
                self.infer_run_tests(state, init, pass_fn, fail_fn, *span)
            }
            // ParBind is semantically identical to Let for type-checking;
            // parallel execution is a codegen concern.
            Expr::ParBind {
                bindings,
                body,
                span,
            } => self.infer_let(state, bindings, body, *span),
        }
    }

    // --- Per-variant inference methods ---

    fn infer_int_lit(&self, state: &mut CheckState, span: Span) -> Result<Type, CranelispError> {
        self.record_expr_type(state, span, Type::Int);
        Ok(Type::Int)
    }

    fn infer_string_lit(&self, state: &mut CheckState, span: Span) -> Result<Type, CranelispError> {
        self.record_expr_type(state, span, Type::String);
        Ok(Type::String)
    }

    fn infer_float_lit(&self, state: &mut CheckState, span: Span) -> Result<Type, CranelispError> {
        self.record_expr_type(state, span, Type::Float);
        Ok(Type::Float)
    }

    fn infer_bool_lit(&self, state: &mut CheckState, span: Span) -> Result<Type, CranelispError> {
        self.record_expr_type(state, span, Type::Bool);
        Ok(Type::Bool)
    }

    fn infer_var(&self, state: &mut CheckState, name: &Symbol, span: Span) -> Result<Type, CranelispError> {
        let scheme = self.lookup(state, name).ok_or_else(|| CranelispError::TypeError {
            message: format!("undefined variable: {name}"),
            span,
        })?;

        // Don't instantiate special forms -- they are not callable as values
        if let Some(ModuleEntry::Def { kind, .. }) = self.current_symbol_table_with_state(state).get(name)
            && matches!(kind.as_ref(), cranelisp_types::DefKind::SpecialForm { .. })
        {
            return Err(CranelispError::TypeError {
                message: format!("{name} is a special form, not a value"),
                span,
            });
        }

        // Reject internal constructors (e.g. Bind) — they cannot be
        // constructed by user code, only by compiler-generated primitives.
        if self.is_internal_constructor(name) {
            return Err(CranelispError::TypeError {
                message: format!(
                    "cannot construct internal type constructor '{name}'"
                ),
                span,
            });
        }

        // Constrained polymorphic functions cannot be used as bare values
        // (spec §3.6.6). They must be called with arguments so concrete
        // types can be determined for monomorphisation.
        if !state.in_call_position
            && let Some(entry) = self.resolve_entry_in_current_module(state, name)
            && let ModuleEntry::Def { kind, .. } = entry
            && matches!(
                kind.as_ref(),
                cranelisp_types::DefKind::UserFn { constrained_fn: Some(_) }
            )
        {
            return Err(CranelispError::TypeError {
                message: format!(
                    "constrained function '{name}' cannot be used as a value \
                     — it must be called with arguments"
                ),
                span,
            });
        }

        let ty = self.instantiate(state, &scheme);
        let resolved = self.apply_subst(state, &ty);
        self.record_expr_type(state, span, resolved.clone());
        Ok(resolved)
    }

    // Note: creates a new scope for let bindings, preventing variable leakage
    // into enclosing scope. This deviates from plan section 2.3 but is strictly
    // better behavior.
    fn infer_let(
        &self, state: &mut CheckState,
        bindings: &[(Symbol, Expr)],
        body: &Expr,
        span: Span,
    ) -> Result<Type, CranelispError> {
        self.push_scope(state);

        for (name, binding_expr) in bindings {
            let binding_ty = self.infer_expr(state, binding_expr)?;
            // Let bindings are monomorphic (spec 3.5.3)
            self.bind_local(state, name.clone(), mono(binding_ty));
        }

        let body_ty = self.infer_expr(state, body)?;
        self.pop_scope(state);

        let resolved = self.apply_subst(state, &body_ty);
        self.record_expr_type(state, span, resolved.clone());
        Ok(resolved)
    }

    fn infer_if(
        &self, state: &mut CheckState,
        cond: &Expr,
        then_branch: &Expr,
        else_branch: &Expr,
        span: Span,
    ) -> Result<Type, CranelispError> {
        let cond_ty = self.infer_expr(state, cond)?;
        self.unify(state, &cond_ty, &Type::Bool, cond.span())?;

        let then_ty = self.infer_expr(state, then_branch)?;
        let else_ty = self.infer_expr(state, else_branch)?;
        self.unify(state, &then_ty, &else_ty, span)?;

        let resolved = self.apply_subst(state, &then_ty);
        self.record_expr_type(state, span, resolved.clone());
        Ok(resolved)
    }

    fn infer_lambda(
        &self, state: &mut CheckState,
        params: &[Symbol],
        param_annotations: &[Option<TypeExpr>],
        body: &Expr,
        span: Span,
    ) -> Result<Type, CranelispError> {
        self.push_scope(state);

        let mut param_types = Vec::new();
        for (i, param_name) in params.iter().enumerate() {
            let param_ty = if let Some(Some(annotation)) = param_annotations.get(i) {
                let known = self.known_type_names();
                let var_map = HashMap::new();
                resolve_type_expr(annotation, &var_map, &known, span)?
            } else {
                self.fresh_var()
            };
            param_types.push(param_ty.clone());
            self.bind_local(state, param_name.clone(), mono(param_ty));
        }

        let body_ty = self.infer_expr(state, body)?;
        self.pop_scope(state);

        let fn_type = Type::Fn(
            param_types
                .iter()
                .map(|t| self.apply_subst(state, t))
                .collect(),
            Box::new(self.apply_subst(state, &body_ty)),
        );
        self.record_expr_type(state, span, fn_type.clone());
        Ok(fn_type)
    }

    fn infer_apply(
        &self, state: &mut CheckState,
        callee: &Expr,
        args: &[Expr],
        span: Span,
    ) -> Result<Type, CranelispError> {
        // Mark callee as in call position so constrained fn references are allowed.
        // Save/restore is stack-based: each nesting level preserves the outer value.
        let prev_call_position = state.in_call_position;
        state.in_call_position = true;
        let callee_ty = self.infer_expr(state, callee);
        state.in_call_position = prev_call_position;
        let callee_ty = callee_ty?;

        // Arguments are NOT in call position — a constrained fn passed as an
        // argument (e.g., `(f add)`) must be rejected. Explicitly clear the flag
        // to handle nested applications like `((f x) add)` where the outer
        // save/restore leaves `in_call_position` true during inner arg inference.
        let prev_for_args = state.in_call_position;
        state.in_call_position = false;
        let mut arg_types = Vec::new();
        for arg in args {
            arg_types.push(self.infer_expr(state, arg)?);
        }
        state.in_call_position = prev_for_args;

        let ret_ty = self.fresh_var();

        // Multi-sig overload dispatch: if the callee is a Var whose name is
        // in the overloads table, defer resolution to the overload pass.
        // We don't unify here because the base name's scheme may not match
        // the actual call site arity/types.
        if let Expr::Var { name, .. } = callee
            && state.overloads.contains_key(name)
        {
            state.pending_overload_resolutions.push((
                span,
                name.clone(),
                arg_types.clone(),
                ret_ty.clone(),
            ));
            // Record arg types in expr_types for each arg
            for (arg, arg_ty) in args.iter().zip(arg_types.iter()) {
                self.record_expr_type(state, arg.span(), self.apply_subst(state, arg_ty));
            }
            self.record_expr_type(state, span, ret_ty.clone());
            return Ok(ret_ty);
        }

        // Unify callee with Fn(arg_types, ret_ty).
        // On failure, try auto-curry: callee may have more params than provided args.
        let expected_fn = Type::Fn(arg_types.clone(), Box::new(ret_ty.clone()));
        let unify_result = self.unify(state, &callee_ty, &expected_fn, span);

        if let Err(ref _e) = unify_result {
            if let Some(ty) = self.try_auto_curry(state, callee, &callee_ty, &arg_types, span)? {
                // Auto-curry succeeded. If the callee is a trait method or builtin,
                // resolve it now so the wrapper function can call the concrete
                // implementation (e.g., "+" → "add-i64" for Int).
                if let Expr::Var { name, .. } = callee {
                    // Use the FULL param types from the callee's resolved type
                    // (not just the applied args) for trait resolution.
                    let resolved_callee = self.apply_subst(state, &callee_ty);
                    if let Type::Fn(full_params, _) = &resolved_callee {
                        let resolved_params: Vec<Type> = full_params
                            .iter()
                            .map(|t| self.apply_subst(state, t))
                            .collect();
                        let resolution = match
                            self.try_resolve_trait_method(state, name, &resolved_params, span)
                        {
                            Ok(Some(r)) => Some(r),
                            Ok(None) => self.resolve_primitive_jit_name(state, name)
                                .map(|jit_name| ResolvedCall::BuiltinFn { name: jit_name }),
                            Err(e) => return Err(e),
                        };
                        if resolution.is_some() {
                            // Attach to the last pending_auto_curry entry (the one
                            // just pushed by try_auto_curry).
                            if let Some(entry) = state.pending_auto_curry.last_mut() {
                                entry.5 = resolution;
                            }
                        }
                    }
                }
                return Ok(ty);
            }
            // Not auto-curryable — propagate original error.
            unify_result?;
        }

        // Resolve the call: trait method, builtin primitive, or user function.
        if let Expr::Var { name, .. } = callee {
            let resolved_args: Vec<Type> = arg_types
                .iter()
                .map(|t| self.apply_subst(state, t))
                .collect();

            if let Some(resolution) =
                self.try_resolve_trait_method(state, name, &resolved_args, span)?
            {
                // Trait method resolution (Ring 2): operators like +, -, =, <
                state.method_resolutions.insert(span, resolution);
            } else if let Some(jit_name) = self.resolve_primitive_jit_name(state, name) {
                // Named primitive resolution (Ring 0-3): add-i64, str-concat,
                // macros/sconcat, quote-sexp, etc.
                state.method_resolutions
                    .insert(span, ResolvedCall::BuiltinFn { name: jit_name });
            }
        }

        let resolved = self.apply_subst(state, &ret_ty);
        self.record_expr_type(state, span, resolved.clone());
        Ok(resolved)
    }

    /// Try auto-curry: if the callee has more params than supplied args,
    /// unify applied args with the first N params and return the curried
    /// return type `(Fn [remaining_params...] ret)`.
    ///
    /// Returns `Some(curry_type)` on success, `None` if not applicable.
    /// The caller should propagate the original unification error when None.
    fn try_auto_curry(
        &self, state: &mut CheckState,
        callee: &Expr,
        callee_ty: &Type,
        arg_types: &[Type],
        span: Span,
    ) -> Result<Option<Type>, CranelispError> {
        // Auto-curry requires at least one applied arg (zero args = bare ref, not curry).
        if arg_types.is_empty() {
            return Ok(None);
        }

        // Resolve the callee type through substitution to get concrete Fn type.
        let resolved_callee = self.apply_subst(state, callee_ty);
        let (params, ret) = match &resolved_callee {
            Type::Fn(params, ret) if arg_types.len() < params.len() => (params, ret),
            _ => return Ok(None),
        };

        // Auto-curry requires a named callee (Expr::Var) so the backend can
        // emit the AutoCurry resolution. Non-Var callees (lambdas, complex
        // expressions) would silently produce no resolution, causing miscompilation.
        // Reject them with a clear error — the user can bind to a variable first.
        let callee_name = match callee {
            Expr::Var { name, .. } => name.clone(),
            _ => {
                return Err(CranelispError::TypeError {
                    message: "auto-curry requires a named function; bind this expression to a variable first".to_string(),
                    span,
                });
            }
        };

        // Unify each applied arg with the corresponding parameter.
        for (arg_ty, param_ty) in arg_types.iter().zip(params.iter()) {
            self.unify(state, arg_ty, param_ty, span)?;
        }

        // Build curry return type from remaining params.
        let remaining: Vec<Type> = params[arg_types.len()..]
            .iter()
            .map(|t| self.apply_subst(state, t))
            .collect();
        let curry_ret = Type::Fn(remaining, ret.clone());

        // Record auto-curry resolution for the backend.
        // The trait_resolution (6th element) starts as None; it is filled in
        // by infer_apply after try_auto_curry returns (if types are concrete),
        // or by resolve_auto_curry when draining (if types get pinned later).
        state.pending_auto_curry.push((
            span,
            callee_name,
            arg_types.len(),
            params.len(),
            callee_ty.clone(),
            None,
        ));

        let ty = self.apply_subst(state, &curry_ret);
        self.record_expr_type(state, span, ty.clone());
        Ok(Some(ty))
    }

    /// Resolve a name to its JIT-level primitive name, if it is a primitive.
    ///
    /// Handles both unqualified names (looked up in current module) and
    /// qualified names like `macros/sconcat` (split on `/`, looked up in
    /// the target module directly). Returns the bare JIT name (not qualified)
    /// for `ResolvedCall::BuiltinFn`.
    ///
    /// This is needed because the quasiquote expander emits `macros/sconcat`
    /// calls with the module prefix.
    pub(crate) fn resolve_primitive_jit_name(&self, state: &CheckState, name: &str) -> Option<Symbol> {
        use cranelisp_types::{DefKind, ModuleFullPath};

        // Try qualified name: "module/name" -> look up in target module
        if let Some(slash_pos) = name.find('/') {
            let module_part = &name[..slash_pos];
            let name_part = &name[slash_pos + 1..];
            if !module_part.is_empty() && !name_part.is_empty() {
                let module_path = ModuleFullPath::from(module_part);
                // Clone-and-drop: get entry from guard, drop guard, then follow chain
                let entry = {
                    let guard = self.modules.get(&module_path);
                    guard.as_ref().and_then(|g| g.get(name_part).cloned())
                };
                if let Some(entry) = entry {
                    let terminal = self.resolve_to_terminal_entry_owned(&entry, 0)?;
                    if let ModuleEntry::Def { kind, .. } = &terminal {
                        // Return the JIT symbol name if specified (platform effects),
                        // otherwise return the bare name.
                        if let DefKind::Primitive { jit_name: Some(jit), .. } = kind.as_ref() {
                            return Some(Symbol::from(jit.as_ref()));
                        }
                        if matches!(kind.as_ref(), DefKind::Primitive { .. }) {
                            return Some(Symbol::from(name_part));
                        }
                    }
                }
            }
            return None;
        }

        // Unqualified name: resolve in current module (returns owned entry)
        let entry = self.resolve_entry_in_current_module(state, name)?;
        if let ModuleEntry::Def { kind, .. } = &entry {
            // Return the JIT symbol name if specified (platform effects),
            // otherwise return the bare name.
            if let DefKind::Primitive { jit_name: Some(jit), .. } = kind.as_ref() {
                return Some(Symbol::from(jit.as_ref()));
            }
            if matches!(kind.as_ref(), DefKind::Primitive { .. }) {
                return Some(Symbol::from(name));
            }
        }
        None
    }

    /// Post-inference pass: resolve trait method calls that couldn't be resolved
    /// during inference because argument types were still unresolved type variables.
    ///
    /// Called after a function body is fully checked and all substitutions are
    /// established. Walks the expression tree, finds Apply nodes whose callee is
    /// a known trait method but has no entry in method_resolutions, and resolves them.
    pub(crate) fn resolve_deferred_trait_calls(&self, state: &mut CheckState, expr: &Expr) {
        match expr {
            Expr::Apply { callee, args, span } => {
                // Try to resolve this Apply if it's not already resolved
                if !state.method_resolutions.contains_key(span)
                    && let Expr::Var { name, .. } = callee.as_ref()
                    && self.is_trait_method(name)
                {
                    let resolved_args: Vec<Type> = args
                        .iter()
                        .map(|a| {
                            state.expr_types
                                .get(&a.span())
                                .map(|t| self.apply_subst(state, t))
                                .unwrap_or_else(|| Type::Var(0))
                        })
                        .collect();
                    if let Ok(Some(resolution)) =
                        self.try_resolve_trait_method(state, name, &resolved_args, *span)
                    {
                        state.method_resolutions.insert(*span, resolution);
                    }
                }
                // Recurse
                self.resolve_deferred_trait_calls(state, callee);
                for arg in args {
                    self.resolve_deferred_trait_calls(state, arg);
                }
            }
            Expr::Let { bindings, body, .. } => {
                for (_, binding_expr) in bindings {
                    self.resolve_deferred_trait_calls(state, binding_expr);
                }
                self.resolve_deferred_trait_calls(state, body);
            }
            Expr::If { cond, then_branch, else_branch, .. } => {
                self.resolve_deferred_trait_calls(state, cond);
                self.resolve_deferred_trait_calls(state, then_branch);
                self.resolve_deferred_trait_calls(state, else_branch);
            }
            Expr::Lambda { body, .. } => {
                self.resolve_deferred_trait_calls(state, body);
            }
            Expr::Match { scrutinee, arms, .. } => {
                self.resolve_deferred_trait_calls(state, scrutinee);
                for arm in arms {
                    self.resolve_deferred_trait_calls(state, &arm.body);
                }
            }
            Expr::Annotate { expr: inner, .. } => {
                self.resolve_deferred_trait_calls(state, inner);
            }
            Expr::VecLit { elements, .. } => {
                for elem in elements {
                    self.resolve_deferred_trait_calls(state, elem);
                }
            }
            Expr::Trace { body, .. } => {
                self.resolve_deferred_trait_calls(state, body);
            }
            Expr::ParBind { bindings, body, .. } => {
                for (_, binding_expr) in bindings {
                    self.resolve_deferred_trait_calls(state, binding_expr);
                }
                self.resolve_deferred_trait_calls(state, body);
            }
            _ => {}
        }
    }

    fn infer_match(
        &self, state: &mut CheckState,
        scrutinee: &Expr,
        arms: &[MatchArm],
        span: Span,
    ) -> Result<Type, CranelispError> {
        if arms.is_empty() {
            return Err(CranelispError::TypeError {
                message: "match expression must have at least one arm".into(),
                span,
            });
        }

        let scrutinee_ty = self.infer_expr(state, scrutinee)?;
        let result_ty = self.fresh_var();

        let mut covered_ctors: Vec<Symbol> = Vec::new();
        let mut has_wildcard = false;

        for arm in arms {
            self.push_scope(state);

            match &arm.pattern {
                Pattern::Constructor {
                    name,
                    bindings,
                    span: pat_span,
                } => {
                    self.check_constructor_pattern(state, 
                        name,
                        bindings,
                        &scrutinee_ty,
                        *pat_span,
                    )?;
                    covered_ctors.push(name.clone());
                }
                Pattern::Wildcard { .. } => {
                    has_wildcard = true;
                }
                Pattern::Var {
                    name,
                    ..
                } => {
                    has_wildcard = true;
                    self.bind_local(state, name.clone(), mono(self.apply_subst(state, &scrutinee_ty)));
                }
            }

            let arm_ty = self.infer_expr(state, &arm.body)?;
            self.unify(state, &arm_ty, &result_ty, arm.span)?;

            self.pop_scope(state);
        }

        // Check exhaustiveness for concrete ADT scrutinees
        let resolved_scrutinee = self.apply_subst(state, &scrutinee_ty);
        if let Type::ADT(type_name, _) = &resolved_scrutinee {
            self.check_exhaustiveness(type_name, &covered_ctors, has_wildcard, span)?;
        }

        let resolved = self.apply_subst(state, &result_ty);
        self.record_expr_type(state, span, resolved.clone());
        Ok(resolved)
    }

    /// Check a constructor pattern against the scrutinee type.
    ///
    /// For nullary constructors, validates no bindings and unifies with ADT type.
    /// For data constructors, instantiates the polymorphic constructor scheme,
    /// unifies the result type with the scrutinee, and binds pattern variables
    /// to the instantiated field types.
    fn check_constructor_pattern(
        &self, state: &mut CheckState,
        name: &Symbol,
        bindings: &[Symbol],
        scrutinee_ty: &Type,
        span: Span,
    ) -> Result<(), CranelispError> {
        // Reject internal constructors (e.g. Bind) in pattern matching.
        // Internal constructors are implementation details not meant for user code.
        if self.is_internal_constructor(name) {
            return Err(CranelispError::TypeError {
                message: format!(
                    "cannot match on internal type constructor '{name}'"
                ),
                span,
            });
        }

        // Look up the constructor's scheme from the symbol table
        let ctor_scheme = self.lookup_constructor_scheme(state, name, span)?;

        // Instantiate the scheme with fresh type variables
        let instantiated = self.instantiate(state, &ctor_scheme);

        // Unify and bind depending on whether the constructor has fields
        self.unify_pattern_with_scrutinee(state, 
            name, bindings, &instantiated, scrutinee_ty, span,
        )
    }

    /// Look up a constructor's type scheme from the symbol table.
    ///
    /// Supports module-qualified names (e.g. `macros/SCons`): strips the module
    /// prefix for the `constructor_to_type` registry lookup, then uses the full
    /// qualified name for scheme resolution (which already handles `/`).
    fn lookup_constructor_scheme(
        &self, state: &CheckState,
        name: &Symbol,
        span: Span,
    ) -> Result<Scheme, CranelispError> {
        // For qualified names like "macros/SCons", use the bare name for
        // the constructor_to_type lookup (which stores unqualified names).
        let bare_name: &str = if let Some(slash_pos) = name.as_ref().find('/') {
            &name.as_ref()[slash_pos + 1..]
        } else {
            name.as_ref()
        };

        // Verify the constructor exists in the type registry
        if self.type_defs.read().unwrap()
            .constructor_type(bare_name)
            .is_none()
        {
            return Err(CranelispError::TypeError {
                message: format!("unknown constructor in pattern: {name}"),
                span,
            });
        }

        // Get the scheme from the symbol table (handles qualified names via lookup)
        self.lookup(state, name).ok_or_else(|| CranelispError::TypeError {
            message: format!("constructor {name} has no type scheme"),
            span,
        })
    }

    /// Unify an instantiated constructor type with the scrutinee and bind variables.
    fn unify_pattern_with_scrutinee(
        &self, state: &mut CheckState,
        name: &Symbol,
        bindings: &[Symbol],
        instantiated: &Type,
        scrutinee_ty: &Type,
        span: Span,
    ) -> Result<(), CranelispError> {
        match instantiated {
            // Nullary constructor: type is just the ADT type
            Type::ADT(..) => {
                if !bindings.is_empty() {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "constructor {name} takes no arguments, got {}",
                            bindings.len()
                        ),
                        span,
                    });
                }
                self.unify(state, scrutinee_ty, instantiated, span)
            }

            // Data constructor: type is Fn([field_types], adt_type)
            Type::Fn(field_types, ret_type) => {
                self.bind_data_ctor_pattern(state, 
                    name, bindings, field_types, ret_type, scrutinee_ty, span,
                )
            }

            _ => Err(CranelispError::TypeError {
                message: format!(
                    "constructor {name} has unexpected type: {instantiated}"
                ),
                span,
            }),
        }
    }

    /// Bind pattern variables for a data constructor with fields.
    fn bind_data_ctor_pattern(
        &self, state: &mut CheckState,
        name: &Symbol,
        bindings: &[Symbol],
        field_types: &[Type],
        ret_type: &Type,
        scrutinee_ty: &Type,
        span: Span,
    ) -> Result<(), CranelispError> {
        if bindings.len() != field_types.len() {
            return Err(CranelispError::TypeError {
                message: format!(
                    "constructor {name} expects {} field(s), got {} binding(s)",
                    field_types.len(),
                    bindings.len()
                ),
                span,
            });
        }

        // Unify the constructor's result type with the scrutinee
        self.unify(state, scrutinee_ty, ret_type, span)?;

        // Bind each pattern variable to the resolved field type
        for (binding_name, field_ty) in bindings.iter().zip(field_types.iter()) {
            let resolved = self.apply_subst(state, field_ty);
            self.bind_local(state, binding_name.clone(), mono(resolved));
        }

        Ok(())
    }

    fn infer_vec_lit(
        &self, state: &mut CheckState,
        elements: &[Expr],
        span: Span,
    ) -> Result<Type, CranelispError> {
        let elem_type = if elements.is_empty() {
            // Empty vec: polymorphic (Vec fresh_var)
            self.fresh_var()
        } else {
            // Non-empty vec: infer first element, unify all others with it
            let first_ty = self.infer_expr(state, &elements[0])?;
            for elem in &elements[1..] {
                let elem_ty = self.infer_expr(state, elem)?;
                self.unify(state, &first_ty, &elem_ty, elem.span())?;
            }
            self.apply_subst(state, &first_ty)
        };

        let vec_type = Type::ADT("Vec".into(), vec![elem_type]);
        self.record_expr_type(state, span, vec_type.clone());
        Ok(vec_type)
    }

    /// Infer the type of `(trace expr)`.
    ///
    /// Check whether `trace` is in scope — i.e., imported from `primitives`.
    /// `trace` is a module-scoped special form, not a parser keyword.
    fn is_trace_in_scope(&self, state: &CheckState) -> bool {
        // Check if `trace` resolves in the current module to the primitives entry.
        // It could be imported via (import [primitives [trace]]) or qualified primitives/trace.
        self.lookup(state, &Symbol::from("trace")).is_some()
    }

    /// The body expression is inferred normally (for side effects on the type
    /// environment, e.g. unification constraints), but the result type is
    /// always `Trace` regardless of the body's type.
    ///
    /// See spec §3.2.4 (Trace typing rule) and §4.12.1.
    fn infer_trace(
        &self, state: &mut CheckState,
        body: &Expr,
        span: Span,
    ) -> Result<Type, CranelispError> {
        // Infer the body — we don't use its type, but inference must run
        // to propagate constraints and detect errors within the body.
        let _body_ty = self.infer_expr(state, body)?;

        let trace_type = Type::ADT("Trace".into(), vec![]);
        self.record_expr_type(state, span, trace_type.clone());
        Ok(trace_type)
    }

    /// Infer the type of `(run-tests init pass-fn fail-fn)`.
    ///
    /// - `init` determines the accumulator type `:a`
    /// - `pass_fn :: (Fn [:a String Int] :a)`
    /// - `fail_fn :: (Fn [:a String Int String Trace] :a)`
    /// - Result type is `:a` (the accumulator type)
    fn infer_run_tests(
        &self, state: &mut CheckState,
        init: &Expr,
        pass_fn: &Expr,
        fail_fn: &Expr,
        span: Span,
    ) -> Result<Type, CranelispError> {
        // Infer accumulator type from init
        let acc_ty = self.infer_expr(state, init)?;
        let acc_ty = self.apply_subst(state, &acc_ty);

        // pass_fn :: (Fn [acc_ty String Int] acc_ty)
        let expected_pass = Type::Fn(
            vec![acc_ty.clone(), Type::String, Type::Int],
            Box::new(acc_ty.clone()),
        );
        let pass_ty = self.infer_expr(state, pass_fn)?;
        self.unify(state, &pass_ty, &expected_pass, span)?;

        // fail_fn :: (Fn [acc_ty String Int String Trace] acc_ty)
        let trace_ty = Type::ADT("Trace".into(), vec![]);
        let expected_fail = Type::Fn(
            vec![acc_ty.clone(), Type::String, Type::Int, Type::String, trace_ty],
            Box::new(acc_ty.clone()),
        );
        let fail_ty = self.infer_expr(state, fail_fn)?;
        self.unify(state, &fail_ty, &expected_fail, span)?;

        // Result type: acc_ty
        let result_ty = self.apply_subst(state, &acc_ty);
        self.record_expr_type(state, span, result_ty.clone());
        Ok(result_ty)
    }

    fn infer_annotate(
        &self, state: &mut CheckState,
        annotation: &TypeExpr,
        expr: &Expr,
        span: Span,
    ) -> Result<Type, CranelispError> {
        let known = self.known_type_names();
        let var_map = HashMap::new();
        let ann_type = resolve_type_expr(annotation, &var_map, &known, span)?;

        let expr_ty = self.infer_expr(state, expr)?;
        self.unify(state, &expr_ty, &ann_type, span)?;

        let resolved = self.apply_subst(state, &ann_type);
        self.record_expr_type(state, span, resolved.clone());
        Ok(resolved)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{ConstructorDef, ImportNames, ImportSpec, ModuleEntry, ModuleFullPath, Span, Symbol, TypeName, Visibility};

    fn span(start: u32, end: u32) -> Span {
        Span::new(start, end)
    }

    /// Create a TypeChecker with builtins for testing.
    /// Uses set_current_module to create a "test" module seeded with primitives.
    fn tc() -> TypeChecker {
        let mut tc = TypeChecker::new();
        tc.set_current_module(ModuleFullPath::from("test"));
        // Import primitives so bare names (add-i64 etc.) resolve.
        let import_spec = ImportSpec {
            module_path: ModuleFullPath::from("primitives"),
            alias: None,
            names: ImportNames::Glob,
            span: Span::new(0, 0),
        };
        tc.register_imports(&[import_spec]).unwrap();
        tc
    }

    /// Register a simple enum type for testing.
    fn register_color(tc: &mut TypeChecker) {
        tc.register_type_def_self(
            &TypeName::from("Color"),
            &None,
            &[],
            &[
                ConstructorDef {
                    name: Symbol::from("Red"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
                ConstructorDef {
                    name: Symbol::from("Green"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
                ConstructorDef {
                    name: Symbol::from("Blue"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
            ],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();
    }

    // --- Literal tests ---

    // spec: 03-types §3.5.3 — integer literal infers to Int
    #[test]
    fn test_infer_int_lit() {
        let mut tc = tc();
        let expr = Expr::IntLit {
            value: 42,
            span: span(0, 2),
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.5.3 — float literal infers to Float
    #[test]
    fn test_infer_float_lit() {
        let mut tc = tc();
        let expr = Expr::FloatLit {
            value: 2.72,
            span: span(0, 4),
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::Float);
    }

    // spec: 03-types §3.5.3 — boolean literal infers to Bool
    #[test]
    fn test_infer_bool_lit() {
        let mut tc = tc();
        let expr = Expr::BoolLit {
            value: true,
            span: span(0, 4),
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::Bool);
    }

    // --- Var tests ---

    // spec: 03-types §3.5.3 — variable reference looks up and instantiates scheme
    #[test]
    fn test_infer_var_defined() {
        let mut tc = tc();
        tc.bind_local_self(Symbol::from("x"), mono(Type::Int));
        let expr = Expr::Var {
            name: Symbol::from("x"),
            span: span(0, 1),
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.5.3 — undefined variable reference is a type error
    #[test]
    fn test_infer_var_undefined() {
        let mut tc = tc();
        let expr = Expr::Var {
            name: Symbol::from("x"),
            span: span(0, 1),
        };
        assert!(tc.infer_expr_for_test(&expr).is_err());
    }

    // --- Let tests ---

    // spec: 03-types §3.5.3 — let binding infers value type and propagates to body
    #[test]
    fn test_infer_let_simple() {
        let mut tc = tc();
        // (let [x 42] x)
        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("x"),
                Expr::IntLit {
                    value: 42,
                    span: span(6, 8),
                },
            )],
            body: Box::new(Expr::Var {
                name: Symbol::from("x"),
                span: span(10, 11),
            }),
            span: span(0, 12),
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.5.3 — let sequential bindings: later bindings see earlier ones
    #[test]
    fn test_infer_let_sequential_bindings() {
        let mut tc = tc();
        // (let [x 42 y x] y)
        let expr = Expr::Let {
            bindings: vec![
                (
                    Symbol::from("x"),
                    Expr::IntLit {
                        value: 42,
                        span: span(6, 8),
                    },
                ),
                (
                    Symbol::from("y"),
                    Expr::Var {
                        name: Symbol::from("x"),
                        span: span(11, 12),
                    },
                ),
            ],
            body: Box::new(Expr::Var {
                name: Symbol::from("y"),
                span: span(14, 15),
            }),
            span: span(0, 16),
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::Int);
    }

    // --- If tests ---

    // spec: 03-types §3.5.3 — if expression: branches unify, result is branch type
    #[test]
    fn test_infer_if_ok() {
        let mut tc = tc();
        // (if true 1 2)
        let expr = Expr::If {
            cond: Box::new(Expr::BoolLit {
                value: true,
                span: span(4, 8),
            }),
            then_branch: Box::new(Expr::IntLit {
                value: 1,
                span: span(9, 10),
            }),
            else_branch: Box::new(Expr::IntLit {
                value: 2,
                span: span(11, 12),
            }),
            span: span(0, 13),
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.5.3 — if condition must unify with Bool
    #[test]
    fn test_infer_if_non_bool_condition() {
        let mut tc = tc();
        // (if 42 1 2) -- condition must be Bool
        let expr = Expr::If {
            cond: Box::new(Expr::IntLit {
                value: 42,
                span: span(4, 6),
            }),
            then_branch: Box::new(Expr::IntLit {
                value: 1,
                span: span(7, 8),
            }),
            else_branch: Box::new(Expr::IntLit {
                value: 2,
                span: span(9, 10),
            }),
            span: span(0, 11),
        };
        let err = tc.infer_expr_for_test(&expr).unwrap_err();
        assert!(err.message().contains("type mismatch"));
    }

    // spec: 03-types §3.5.3 — if branches must unify with each other
    #[test]
    fn test_infer_if_branch_mismatch() {
        let mut tc = tc();
        // (if true 1 true) -- branches must agree
        let expr = Expr::If {
            cond: Box::new(Expr::BoolLit {
                value: true,
                span: span(4, 8),
            }),
            then_branch: Box::new(Expr::IntLit {
                value: 1,
                span: span(9, 10),
            }),
            else_branch: Box::new(Expr::BoolLit {
                value: true,
                span: span(11, 15),
            }),
            span: span(0, 16),
        };
        assert!(tc.infer_expr_for_test(&expr).is_err());
    }

    // --- Lambda tests ---

    // spec: 03-types §3.5.3 — lambda: params get fresh vars, result is Fn type
    #[test]
    fn test_infer_lambda_identity() {
        let mut tc = tc();
        // (fn [x] x)
        let expr = Expr::Lambda {
            params: vec![Symbol::from("x")],
            param_annotations: vec![None],
            body: Box::new(Expr::Var {
                name: Symbol::from("x"),
                span: span(8, 9),
            }),
            span: span(0, 10),
        };
        let ty = tc.infer_expr_for_test(&expr).unwrap();
        // Should be Fn([tN], tN) for some N
        match ty {
            Type::Fn(params, ret) => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0], *ret);
            }
            _ => panic!("expected Fn type, got {ty:?}"),
        }
    }

    // spec: 03-types §3.9.1 — concrete type annotation constrains param type
    #[test]
    fn test_infer_lambda_annotated() {
        let mut tc = tc();
        // (fn [:Int x] x)
        let expr = Expr::Lambda {
            params: vec![Symbol::from("x")],
            param_annotations: vec![Some(TypeExpr::Named(TypeName::from("Int")))],
            body: Box::new(Expr::Var {
                name: Symbol::from("x"),
                span: span(13, 14),
            }),
            span: span(0, 15),
        };
        let ty = tc.infer_expr_for_test(&expr).unwrap();
        assert_eq!(ty, Type::Fn(vec![Type::Int], Box::new(Type::Int)));
    }

    // --- Apply tests ---

    // spec: 03-types §3.5.3 — function application unifies callee with arg types
    #[test]
    fn test_infer_apply_lambda() {
        let mut tc = tc();
        // ((fn [x] x) 42)
        let expr = Expr::Apply {
            callee: Box::new(Expr::Lambda {
                params: vec![Symbol::from("x")],
                param_annotations: vec![None],
                body: Box::new(Expr::Var {
                    name: Symbol::from("x"),
                    span: span(8, 9),
                }),
                span: span(1, 10),
            }),
            args: vec![Expr::IntLit {
                value: 42,
                span: span(11, 13),
            }],
            span: span(0, 14),
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.5.3 — apply primitive add-i64 records BuiltinFn resolution
    #[test]
    fn test_infer_apply_int_add() {
        let mut tc = tc();
        // (add-i64 1 2) -> Int
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(1, 8),
            }),
            args: vec![
                Expr::IntLit {
                    value: 1,
                    span: span(9, 10),
                },
                Expr::IntLit {
                    value: 2,
                    span: span(11, 12),
                },
            ],
            span: span(0, 13),
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::Int);

        // Check that a BuiltinFn resolution was recorded
        let resolution = tc.state.method_resolutions.get(&span(0, 13)).unwrap();
        match resolution {
            ResolvedCall::BuiltinFn { name } => {
                assert_eq!(name.as_ref(), "add-i64");
            }
            _ => panic!("expected BuiltinFn resolution"),
        }
    }

    // spec: 03-types §3.5.3 — apply primitive add-f64 infers Float return
    #[test]
    fn test_infer_apply_float_add() {
        let mut tc = tc();
        // (add-f64 1.0 2.0) -> Float
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-f64"),
                span: span(1, 8),
            }),
            args: vec![
                Expr::FloatLit {
                    value: 1.0,
                    span: span(9, 12),
                },
                Expr::FloatLit {
                    value: 2.0,
                    span: span(13, 16),
                },
            ],
            span: span(0, 17),
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::Float);

        let resolution = tc.state.method_resolutions.get(&span(0, 17)).unwrap();
        match resolution {
            ResolvedCall::BuiltinFn { name } => {
                assert_eq!(name.as_ref(), "add-f64");
            }
            _ => panic!("expected BuiltinFn resolution"),
        }
    }

    // spec: 03-types §3.5.3 — apply comparison primitive returns Bool
    #[test]
    fn test_infer_apply_int_eq() {
        let mut tc = tc();
        // (eq-i64 1 2) -> Bool
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("eq-i64"),
                span: span(1, 7),
            }),
            args: vec![
                Expr::IntLit {
                    value: 1,
                    span: span(8, 9),
                },
                Expr::IntLit {
                    value: 2,
                    span: span(10, 11),
                },
            ],
            span: span(0, 12),
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::Bool);
    }

    // spec: appendix-a-builtins §A.3 — not primitive: Bool -> Bool
    #[test]
    fn test_infer_apply_not() {
        let mut tc = tc();
        // (not true) -> Bool
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("not"),
                span: span(1, 4),
            }),
            args: vec![Expr::BoolLit {
                value: true,
                span: span(5, 9),
            }],
            span: span(0, 10),
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::Bool);

        let resolution = tc.state.method_resolutions.get(&span(0, 10)).unwrap();
        match resolution {
            ResolvedCall::BuiltinFn { name } => {
                assert_eq!(name.as_ref(), "not");
            }
            _ => panic!("expected BuiltinFn resolution"),
        }
    }

    // spec: 03-types §3.8.6 — type mismatch: float args to int primitive fails
    #[test]
    fn test_infer_apply_type_mismatch_int_add_float() {
        let mut tc = tc();
        // (add-i64 1.0 2.0) -- type error: float args to int primitive
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(1, 8),
            }),
            args: vec![
                Expr::FloatLit {
                    value: 1.0,
                    span: span(9, 12),
                },
                Expr::FloatLit {
                    value: 2.0,
                    span: span(13, 16),
                },
            ],
            span: span(0, 17),
        };
        assert!(tc.infer_expr_for_test(&expr).is_err(), "add-i64 with float args should fail");
    }

    // spec: 04-expressions §4.6.3 — too few args triggers auto-curry
    #[test]
    fn test_infer_apply_auto_curry() {
        let mut tc = tc();
        // (add-i64 1) -- too few args, auto-curry returns Fn([Int], Int)
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(1, 8),
            }),
            args: vec![Expr::IntLit {
                value: 1,
                span: span(9, 10),
            }],
            span: span(0, 11),
        };
        let ty = tc.infer_expr_for_test(&expr).expect("auto-curry should succeed");
        let resolved = tc.apply_subst_self(&ty);
        match resolved {
            Type::Fn(params, ret) => {
                assert_eq!(params.len(), 1, "curried fn should take 1 remaining arg");
                assert_eq!(params[0], Type::Int);
                assert_eq!(*ret, Type::Int);
            }
            other => panic!("expected Fn type, got {:?}", other),
        }
    }

    // spec: 03-types §3.8.3 — too many args is still an arity error
    #[test]
    fn test_infer_apply_too_many_args() {
        let mut tc = tc();
        // (add-i64 1 2 3) -- too many args
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(1, 8),
            }),
            args: vec![
                Expr::IntLit { value: 1, span: span(9, 10) },
                Expr::IntLit { value: 2, span: span(11, 12) },
                Expr::IntLit { value: 3, span: span(13, 14) },
            ],
            span: span(0, 15),
        };
        assert!(tc.infer_expr_for_test(&expr).is_err());
    }

    // --- Match tests ---

    // spec: 06-pattern-matching §6.1 — match enum with all constructors covered
    #[test]
    fn test_infer_match_enum() {
        let mut tc = tc();
        register_color(&mut tc);

        // (match Red [Red 1 Green 2 Blue 3])
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Var {
                name: Symbol::from("Red"),
                span: span(7, 10),
            }),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: Symbol::from("Red"),
                        bindings: vec![],
                        span: span(12, 15),
                    },
                    body: Expr::IntLit {
                        value: 1,
                        span: span(16, 17),
                    },
                    span: span(12, 17),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: Symbol::from("Green"),
                        bindings: vec![],
                        span: span(18, 23),
                    },
                    body: Expr::IntLit {
                        value: 2,
                        span: span(24, 25),
                    },
                    span: span(18, 25),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: Symbol::from("Blue"),
                        bindings: vec![],
                        span: span(26, 30),
                    },
                    body: Expr::IntLit {
                        value: 3,
                        span: span(31, 32),
                    },
                    span: span(26, 32),
                },
            ],
            span: span(0, 33),
            compiler_generated: false,
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::Int);
    }

    // spec: 06-pattern-matching §6.5.1 — non-exhaustive match on ADT is compile error
    #[test]
    fn test_infer_match_non_exhaustive() {
        let mut tc = tc();
        register_color(&mut tc);

        // Match with only Red -- missing Green, Blue
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Var {
                name: Symbol::from("Red"),
                span: span(7, 10),
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: Symbol::from("Red"),
                    bindings: vec![],
                    span: span(12, 15),
                },
                body: Expr::IntLit {
                    value: 1,
                    span: span(16, 17),
                },
                span: span(12, 17),
            }],
            span: span(0, 18),
            compiler_generated: false,
        };
        let err = tc.infer_expr_for_test(&expr).unwrap_err();
        assert!(err.message().contains("non-exhaustive"));
    }

    // spec: 06-pattern-matching §6.2.3 — wildcard pattern covers remaining cases
    #[test]
    fn test_infer_match_wildcard() {
        let mut tc = tc();
        register_color(&mut tc);

        // (match Red [Red 1 _ 0])
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Var {
                name: Symbol::from("Red"),
                span: span(7, 10),
            }),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: Symbol::from("Red"),
                        bindings: vec![],
                        span: span(12, 15),
                    },
                    body: Expr::IntLit {
                        value: 1,
                        span: span(16, 17),
                    },
                    span: span(12, 17),
                },
                MatchArm {
                    pattern: Pattern::Wildcard {
                        span: span(18, 19),
                    },
                    body: Expr::IntLit {
                        value: 0,
                        span: span(20, 21),
                    },
                    span: span(18, 21),
                },
            ],
            span: span(0, 22),
            compiler_generated: false,
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::Int);
    }

    // spec: 06-pattern-matching §6.2.4 — variable pattern binds scrutinee value
    #[test]
    fn test_infer_match_var_pattern() {
        let mut tc = tc();
        register_color(&mut tc);

        // (match Red [x 1]) -- var pattern binds scrutinee
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Var {
                name: Symbol::from("Red"),
                span: span(7, 10),
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Var {
                    name: Symbol::from("x"),
                    span: span(12, 13),
                },
                body: Expr::IntLit {
                    value: 1,
                    span: span(14, 15),
                },
                span: span(12, 15),
            }],
            span: span(0, 16),
            compiler_generated: false,
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::Int);
    }

    // --- Annotate tests ---

    // spec: 03-types §3.9.1 — annotation matching inferred type succeeds
    #[test]
    fn test_infer_annotate_matching() {
        let mut tc = tc();
        // (:Int 42) -- annotation matches
        let expr = Expr::Annotate {
            annotation: TypeExpr::Named(TypeName::from("Int")),
            expr: Box::new(Expr::IntLit {
                value: 42,
                span: span(5, 7),
            }),
            span: span(0, 8),
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.9.1 — annotation mismatching inferred type fails
    #[test]
    fn test_infer_annotate_mismatch() {
        let mut tc = tc();
        // (:Bool 42) -- annotation doesn't match
        let expr = Expr::Annotate {
            annotation: TypeExpr::Named(TypeName::from("Bool")),
            expr: Box::new(Expr::IntLit {
                value: 42,
                span: span(6, 8),
            }),
            span: span(0, 9),
        };
        assert!(tc.infer_expr_for_test(&expr).is_err());
    }

    // --- expr_types recording tests ---

    // spec: 03-types §3.5.1 — expr_types map records inferred type per span
    #[test]
    fn test_expr_types_recorded() {
        let mut tc = tc();
        let s = span(0, 2);
        let expr = Expr::IntLit { value: 42, span: s };
        tc.infer_expr_for_test(&expr).unwrap();
        assert_eq!(tc.state.expr_types.get(&s), Some(&Type::Int));
    }

    // --- Nested expression tests ---

    // spec: 03-types §3.5.3 — nested function application infers correctly
    #[test]
    fn test_infer_nested_arithmetic() {
        let mut tc = tc();
        // (add-i64 (add-i64 1 2) 3)
        let inner = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(9, 16),
            }),
            args: vec![
                Expr::IntLit {
                    value: 1,
                    span: span(17, 18),
                },
                Expr::IntLit {
                    value: 2,
                    span: span(19, 20),
                },
            ],
            span: span(8, 21),
        };
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(1, 8),
            }),
            args: vec![
                inner,
                Expr::IntLit {
                    value: 3,
                    span: span(23, 24),
                },
            ],
            span: span(0, 25),
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::Int);
    }

    // --- String literal tests (Ring 1) ---

    // spec: 03-types §3.5.3 — string literal infers to String
    #[test]
    fn test_infer_string_lit() {
        let mut tc = tc();
        let expr = Expr::StringLit {
            value: "hello".to_string(),
            span: span(0, 7),
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::String);
    }

    // spec: 03-types §3.5.1 — string literal records String in expr_types
    #[test]
    fn test_string_lit_expr_types_recorded() {
        let mut tc = tc();
        let s = span(0, 7);
        let expr = Expr::StringLit {
            value: "hello".to_string(),
            span: s,
        };
        tc.infer_expr_for_test(&expr).unwrap();
        assert_eq!(tc.state.expr_types.get(&s), Some(&Type::String));
    }

    // --- Data constructor pattern tests (Ring 1) ---

    /// Register (Option a) with None and Some[:a val].
    fn register_option(tc: &mut TypeChecker) {
        tc.register_type_def_self(
            &TypeName::from("Option"),
            &None,
            &[Symbol::from("a")],
            &[
                ConstructorDef {
                    name: Symbol::from("None"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
                ConstructorDef {
                    name: Symbol::from("Some"),
                    docstring: None,
                    fields: vec![cranelisp_types::FieldDef {
                        name: Symbol::from("val"),
                        type_expr: TypeExpr::TypeVar(Symbol::from("a")),
                    }],
                    span: Span::SYNTHETIC,
                },
            ],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();
    }

    // spec: 06-pattern-matching §6.4.1 — data constructor pattern binds field types
    #[test]
    fn test_infer_match_data_constructor_pattern() {
        let mut tc = tc();
        register_option(&mut tc);

        // (match (Some 42) [(Some x) x (None 0)])
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: span(8, 12),
                }),
                args: vec![Expr::IntLit {
                    value: 42,
                    span: span(13, 15),
                }],
                span: span(7, 16),
            }),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: Symbol::from("Some"),
                        bindings: vec![Symbol::from("x")],
                        span: span(18, 24),
                    },
                    body: Expr::Var {
                        name: Symbol::from("x"),
                        span: span(26, 27),
                    },
                    span: span(18, 27),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: Symbol::from("None"),
                        bindings: vec![],
                        span: span(29, 33),
                    },
                    body: Expr::IntLit {
                        value: 0,
                        span: span(34, 35),
                    },
                    span: span(29, 35),
                },
            ],
            span: span(0, 36),
            compiler_generated: false,
        };

        // Should infer result type Int (x : Int from Some pattern, 0 : Int)
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::Int);
    }

    // spec: 06-pattern-matching §6.2.1 — wrong binding count in constructor pattern is error
    #[test]
    fn test_infer_match_data_constructor_wrong_binding_count() {
        let mut tc = tc();
        register_option(&mut tc);

        // (match (Some 42) [(Some x y) x]) -- too many bindings
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: span(108, 112),
                }),
                args: vec![Expr::IntLit {
                    value: 42,
                    span: span(113, 115),
                }],
                span: span(107, 116),
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: Symbol::from("Some"),
                    bindings: vec![Symbol::from("x"), Symbol::from("y")],
                    span: span(118, 128),
                },
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: span(130, 131),
                },
                span: span(118, 131),
            }],
            span: span(100, 132),
            compiler_generated: false,
        };

        let err = tc.infer_expr_for_test(&expr).unwrap_err();
        assert!(err.message().contains("expects 1 field"));
    }

    // spec: 06-pattern-matching §6.2.2 — nullary constructor with bindings is error
    #[test]
    fn test_infer_match_nullary_with_bindings_errors() {
        let mut tc = tc();
        register_option(&mut tc);

        // (match (Some 1) [(None x) x]) -- None is nullary, no bindings allowed
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: span(208, 212),
                }),
                args: vec![Expr::IntLit {
                    value: 1,
                    span: span(213, 214),
                }],
                span: span(207, 215),
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: Symbol::from("None"),
                    bindings: vec![Symbol::from("x")],
                    span: span(217, 224),
                },
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: span(226, 227),
                },
                span: span(217, 227),
            }],
            span: span(200, 228),
            compiler_generated: false,
        };

        let err = tc.infer_expr_for_test(&expr).unwrap_err();
        assert!(err.message().contains("takes no arguments"));
    }

    // spec: 06-pattern-matching §6.5.1 — non-exhaustive match on Option (missing None)
    #[test]
    fn test_infer_match_option_non_exhaustive() {
        let mut tc = tc();
        register_option(&mut tc);

        // Match only Some, missing None
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: span(308, 312),
                }),
                args: vec![Expr::IntLit {
                    value: 1,
                    span: span(313, 314),
                }],
                span: span(307, 315),
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: Symbol::from("Some"),
                    bindings: vec![Symbol::from("x")],
                    span: span(317, 324),
                },
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: span(326, 327),
                },
                span: span(317, 327),
            }],
            span: span(300, 328),
            compiler_generated: false,
        };

        let err = tc.infer_expr_for_test(&expr).unwrap_err();
        assert!(err.message().contains("None"));
    }

    // --- Lambda expr_types completeness (Ring 1 validation) ---

    // spec: 03-types §3.5.3 — lambda records Fn type in expr_types
    #[test]
    fn test_lambda_expr_types_recorded() {
        let mut tc = tc();
        let s = span(0, 10);
        let expr = Expr::Lambda {
            params: vec![Symbol::from("x")],
            param_annotations: vec![Some(TypeExpr::Named(TypeName::from("Int")))],
            body: Box::new(Expr::Var {
                name: Symbol::from("x"),
                span: span(13, 14),
            }),
            span: s,
        };
        tc.infer_expr_for_test(&expr).unwrap();

        // Lambda should record a Fn type in expr_types
        let recorded = tc.state.expr_types.get(&s).unwrap();
        assert!(matches!(recorded, Type::Fn(_, _)));
    }

    // --- Annotate with Applied type (Ring 1) ---

    // spec: 03-types §3.9.1 — annotate with applied type :(Option Int)
    #[test]
    fn test_annotate_with_applied_type() {
        let mut tc = tc();
        register_option(&mut tc);

        // :(Option Int) (Some 42) -- annotate with applied type
        let annotate_expr = Expr::Annotate {
            annotation: TypeExpr::Applied(
                TypeName::from("Option"),
                vec![TypeExpr::Named(TypeName::from("Int"))],
            ),
            expr: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: span(418, 422),
                }),
                args: vec![Expr::IntLit {
                    value: 42,
                    span: span(423, 425),
                }],
                span: span(417, 426),
            }),
            span: span(400, 427),
        };

        let ty = tc.infer_expr_for_test(&annotate_expr).unwrap();
        assert_eq!(
            ty,
            Type::ADT(TypeName::from("Option"), vec![Type::Int])
        );
    }

    // --- Product type match tests ---

    // spec: 06-pattern-matching §6.4.1 — product type destructuring in match
    #[test]
    fn test_infer_match_product_type() {
        let mut tc = tc();
        // (deftype Point [:Int x :Int y])
        tc.register_type_def_self(
            &TypeName::from("Point"),
            &None,
            &[],
            &[ConstructorDef {
                name: Symbol::from("Point"),
                docstring: None,
                fields: vec![
                    cranelisp_types::FieldDef {
                        name: Symbol::from("x"),
                        type_expr: TypeExpr::Named(TypeName::from("Int")),
                    },
                    cranelisp_types::FieldDef {
                        name: Symbol::from("y"),
                        type_expr: TypeExpr::Named(TypeName::from("Int")),
                    },
                ],
                span: Span::SYNTHETIC,
            }],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // (match (Point 1 2) [(Point a b) (add-i64 a b)])
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Point"),
                    span: span(508, 513),
                }),
                args: vec![
                    Expr::IntLit {
                        value: 1,
                        span: span(514, 515),
                    },
                    Expr::IntLit {
                        value: 2,
                        span: span(516, 517),
                    },
                ],
                span: span(507, 518),
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: Symbol::from("Point"),
                    bindings: vec![Symbol::from("a"), Symbol::from("b")],
                    span: span(520, 530),
                },
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add-i64"),
                        span: span(532, 539),
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("a"),
                            span: span(540, 541),
                        },
                        Expr::Var {
                            name: Symbol::from("b"),
                            span: span(542, 543),
                        },
                    ],
                    span: span(531, 544),
                },
                span: span(520, 544),
            }],
            span: span(500, 545),
            compiler_generated: false,
        };

        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::Int);
    }

    // spec: 05-definitions §5.2.7 — data constructor applied as function
    #[test]
    fn test_infer_constructor_as_function() {
        let mut tc = tc();
        register_option(&mut tc);

        // (Some 42) -- constructor applied to argument
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("Some"),
                span: span(601, 605),
            }),
            args: vec![Expr::IntLit {
                value: 42,
                span: span(606, 608),
            }],
            span: span(600, 609),
        };

        let ty = tc.infer_expr_for_test(&expr).unwrap();
        assert_eq!(
            ty,
            Type::ADT(TypeName::from("Option"), vec![Type::Int])
        );
    }

    // spec: 05-definitions §5.2.7 — nullary constructor is polymorphic value
    #[test]
    fn test_infer_none_has_polymorphic_type() {
        let mut tc = tc();
        register_option(&mut tc);

        // None on its own should be (Option tN) for some N
        let expr = Expr::Var {
            name: Symbol::from("None"),
            span: span(700, 704),
        };

        let ty = tc.infer_expr_for_test(&expr).unwrap();
        match &ty {
            Type::ADT(name, args) => {
                assert_eq!(name.as_ref(), "Option");
                assert_eq!(args.len(), 1);
                // The arg should be a fresh var
                assert!(matches!(args[0], Type::Var(_)));
            }
            _ => panic!("None should have ADT type, got {ty:?}"),
        }
    }

    // spec: 03-types §3.5.3 — if branches with String type unify
    #[test]
    fn test_infer_string_in_if_branches() {
        let mut tc = tc();
        // (if true "hello" "world")
        let expr = Expr::If {
            cond: Box::new(Expr::BoolLit {
                value: true,
                span: span(804, 808),
            }),
            then_branch: Box::new(Expr::StringLit {
                value: "hello".to_string(),
                span: span(809, 816),
            }),
            else_branch: Box::new(Expr::StringLit {
                value: "world".to_string(),
                span: span(817, 824),
            }),
            span: span(800, 825),
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::String);
    }

    // spec: 03-types §3.5.3 — let binding with String value
    #[test]
    fn test_infer_string_in_let() {
        let mut tc = tc();
        // (let [s "hello"] s)
        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("s"),
                Expr::StringLit {
                    value: "hello".to_string(),
                    span: span(906, 913),
                },
            )],
            body: Box::new(Expr::Var {
                name: Symbol::from("s"),
                span: span(915, 916),
            }),
            span: span(900, 917),
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::String);
    }

    // --- Vec literal tests (Sprint 3) ---

    // spec: 03-types §3.5.3 — Vec literal with Int elements infers (Vec Int)
    #[test]
    fn test_infer_vec_lit_ints() {
        let mut tc = tc();
        // [1 2 3]
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 1, span: span(1001, 1002) },
                Expr::IntLit { value: 2, span: span(1003, 1004) },
                Expr::IntLit { value: 3, span: span(1005, 1006) },
            ],
            span: span(1000, 1007),
        };
        assert_eq!(
            tc.infer_expr_for_test(&expr).unwrap(),
            Type::ADT(TypeName::from("Vec"), vec![Type::Int])
        );
    }

    // spec: 03-types §3.5.3 — Vec literal with String elements infers (Vec String)
    #[test]
    fn test_infer_vec_lit_strings() {
        let mut tc = tc();
        // ["a" "b"]
        let expr = Expr::VecLit {
            elements: vec![
                Expr::StringLit { value: "a".into(), span: span(1101, 1104) },
                Expr::StringLit { value: "b".into(), span: span(1105, 1108) },
            ],
            span: span(1100, 1109),
        };
        assert_eq!(
            tc.infer_expr_for_test(&expr).unwrap(),
            Type::ADT(TypeName::from("Vec"), vec![Type::String])
        );
    }

    // spec: 03-types §3.5.3 — empty Vec literal is polymorphic (Vec a)
    #[test]
    fn test_infer_vec_lit_empty_is_polymorphic() {
        let mut tc = tc();
        // []
        let expr = Expr::VecLit {
            elements: vec![],
            span: span(1200, 1202),
        };
        let ty = tc.infer_expr_for_test(&expr).unwrap();
        match &ty {
            Type::ADT(name, args) => {
                assert_eq!(name.as_ref(), "Vec");
                assert_eq!(args.len(), 1);
                // Element type should be a fresh type variable
                assert!(matches!(args[0], Type::Var(_)));
            }
            _ => panic!("empty vec should be ADT(Vec, [Var]), got {ty:?}"),
        }
    }

    // spec: 03-types §3.5.3 — Vec literal elements must have same type
    #[test]
    fn test_infer_vec_lit_type_mismatch() {
        let mut tc = tc();
        // [1 "hello"] -- Int vs String
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 1, span: span(1301, 1302) },
                Expr::StringLit { value: "hello".into(), span: span(1303, 1310) },
            ],
            span: span(1300, 1311),
        };
        let err = tc.infer_expr_for_test(&expr).unwrap_err();
        assert!(err.message().contains("mismatch"), "expected type mismatch error, got: {}", err.message());
    }

    // spec: 03-types §3.5.3 — Vec literal with Bool elements infers (Vec Bool)
    #[test]
    fn test_infer_vec_lit_booleans() {
        let mut tc = tc();
        // [true false]
        let expr = Expr::VecLit {
            elements: vec![
                Expr::BoolLit { value: true, span: span(1401, 1405) },
                Expr::BoolLit { value: false, span: span(1406, 1411) },
            ],
            span: span(1400, 1412),
        };
        assert_eq!(
            tc.infer_expr_for_test(&expr).unwrap(),
            Type::ADT(TypeName::from("Vec"), vec![Type::Bool])
        );
    }

    // spec: 03-types §3.5.3 — Vec literal in let binding propagates element type
    #[test]
    fn test_infer_vec_lit_in_let_binding() {
        let mut tc = tc();
        // (let [xs [1 2 3]] xs)
        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("xs"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: span(1508, 1509) },
                        Expr::IntLit { value: 2, span: span(1510, 1511) },
                        Expr::IntLit { value: 3, span: span(1512, 1513) },
                    ],
                    span: span(1507, 1514),
                },
            )],
            body: Box::new(Expr::Var {
                name: Symbol::from("xs"),
                span: span(1516, 1518),
            }),
            span: span(1500, 1519),
        };
        assert_eq!(
            tc.infer_expr_for_test(&expr).unwrap(),
            Type::ADT(TypeName::from("Vec"), vec![Type::Int])
        );
    }

    // spec: 03-types §3.5.3 — Vec literal as function argument unifies element type
    #[test]
    fn test_infer_vec_lit_as_function_arg() {
        let mut tc = tc();
        // Define a function that takes (Vec Int) -> Int
        tc.bind_local_self(
            Symbol::from("vec-len"),
            mono(Type::Fn(
                vec![Type::ADT(TypeName::from("Vec"), vec![Type::Int])],
                Box::new(Type::Int),
            )),
        );
        // (vec-len [1 2 3])
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: span(1601, 1608),
            }),
            args: vec![Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 1, span: span(1610, 1611) },
                    Expr::IntLit { value: 2, span: span(1612, 1613) },
                    Expr::IntLit { value: 3, span: span(1614, 1615) },
                ],
                span: span(1609, 1616),
            }],
            span: span(1600, 1617),
        };
        assert_eq!(tc.infer_expr_for_test(&expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.5.3 — lambda returning Vec infers (Fn [Int] (Vec Int))
    #[test]
    fn test_infer_vec_lit_as_function_return() {
        let mut tc = tc();
        // (fn [x] [x]) -- returns Vec of the param type
        let expr = Expr::Lambda {
            params: vec![Symbol::from("x")],
            param_annotations: vec![Some(TypeExpr::Named(TypeName::from("Int")))],
            body: Box::new(Expr::VecLit {
                elements: vec![Expr::Var {
                    name: Symbol::from("x"),
                    span: span(1710, 1711),
                }],
                span: span(1709, 1712),
            }),
            span: span(1700, 1713),
        };
        let ty = tc.infer_expr_for_test(&expr).unwrap();
        assert_eq!(
            ty,
            Type::Fn(
                vec![Type::Int],
                Box::new(Type::ADT(TypeName::from("Vec"), vec![Type::Int]))
            )
        );
    }

    // spec: 03-types §3.5.3 — single-element Vec literal infers element type
    #[test]
    fn test_infer_vec_lit_single_element() {
        let mut tc = tc();
        // [42]
        let expr = Expr::VecLit {
            elements: vec![Expr::IntLit { value: 42, span: span(1801, 1803) }],
            span: span(1800, 1804),
        };
        assert_eq!(
            tc.infer_expr_for_test(&expr).unwrap(),
            Type::ADT(TypeName::from("Vec"), vec![Type::Int])
        );
    }

    // spec: 03-types §3.5.1 — Vec literal records type in expr_types map
    #[test]
    fn test_infer_vec_lit_expr_type_recorded() {
        let mut tc = tc();
        let s = span(1900, 1907);
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 1, span: span(1901, 1902) },
                Expr::IntLit { value: 2, span: span(1903, 1904) },
            ],
            span: s,
        };
        tc.infer_expr_for_test(&expr).unwrap();
        assert_eq!(
            tc.state.expr_types.get(&s),
            Some(&Type::ADT(TypeName::from("Vec"), vec![Type::Int]))
        );
    }

    // spec: 03-types §3.5.3 — Vec literal with Float elements infers (Vec Float)
    #[test]
    fn test_infer_vec_lit_floats() {
        let mut tc = tc();
        // [1.0 2.0 3.0]
        let expr = Expr::VecLit {
            elements: vec![
                Expr::FloatLit { value: 1.0, span: span(2001, 2004) },
                Expr::FloatLit { value: 2.0, span: span(2005, 2008) },
                Expr::FloatLit { value: 3.0, span: span(2009, 2012) },
            ],
            span: span(2000, 2013),
        };
        assert_eq!(
            tc.infer_expr_for_test(&expr).unwrap(),
            Type::ADT(TypeName::from("Vec"), vec![Type::Float])
        );
    }

    // -----------------------------------------------------------------------
    // resolve_primitive_jit_name tests (pipeline-orchestration §3)
    // -----------------------------------------------------------------------

    // spec: pipeline-orchestration §3 — unqualified primitive resolves to bare name
    #[test]
    fn test_resolve_primitive_unqualified() {
        let tc = tc();
        let result = tc.resolve_primitive_jit_name_self("add-i64");
        assert_eq!(result.as_deref(), Some("add-i64"));
    }

    // spec: pipeline-orchestration §3 — non-primitive returns None
    #[test]
    fn test_resolve_primitive_non_primitive() {
        let tc = tc();
        let result = tc.resolve_primitive_jit_name_self("if");
        // "if" is a SpecialForm, not a Primitive
        assert!(result.is_none(), "special forms should not resolve as primitives");
    }

    // spec: pipeline-orchestration §3 — unknown name returns None
    #[test]
    fn test_resolve_primitive_unknown() {
        let tc = tc();
        let result = tc.resolve_primitive_jit_name_self("nonexistent");
        assert!(result.is_none());
    }

    // spec: pipeline-orchestration §3 — qualified macros/sconcat resolves to bare "sconcat"
    #[test]
    fn test_resolve_primitive_qualified_sconcat() {
        let tc = tc();
        let result = tc.resolve_primitive_jit_name_self("macros/sconcat");
        assert_eq!(
            result.as_deref(),
            Some("sconcat"),
            "macros/sconcat should resolve to bare name 'sconcat'"
        );
    }

    // spec: pipeline-orchestration §3 — qualified name for non-primitive returns None
    #[test]
    fn test_resolve_primitive_qualified_non_primitive() {
        let tc = tc();
        // macros/SNil is a Constructor, not a Primitive
        let result = tc.resolve_primitive_jit_name_self("macros/SNil");
        assert!(result.is_none(), "constructors should not resolve as primitives");
    }

    // spec: pipeline-orchestration §3 — qualified name in unknown module returns None
    #[test]
    fn test_resolve_primitive_qualified_unknown_module() {
        let tc = tc();
        let result = tc.resolve_primitive_jit_name_self("unknown/foo");
        assert!(result.is_none());
    }

    // spec: pipeline-orchestration §3 — extern primitives resolve (str-concat)
    #[test]
    fn test_resolve_primitive_extern() {
        let tc = tc();
        let result = tc.resolve_primitive_jit_name_self("str-concat");
        assert_eq!(result.as_deref(), Some("str-concat"));
    }

    // spec: pipeline-orchestration §3 — quote-sexp resolves as primitive
    #[test]
    fn test_resolve_primitive_quote_sexp() {
        let tc = tc();
        let result = tc.resolve_primitive_jit_name_self("quote-sexp");
        assert_eq!(result.as_deref(), Some("quote-sexp"));
    }

    // -----------------------------------------------------------------------
    // B2: in_call_position scoping — args must NOT be in call position
    // -----------------------------------------------------------------------

    /// Register a constrained function "cfn" in the current module for testing.
    fn register_constrained_fn(tc: &mut TypeChecker) {
        use cranelisp_types::{ConstrainedFn, Defn, DefnVariant};

        let a_var = tc.fresh_var();
        let a_id = match &a_var { Type::Var(id) => *id, _ => unreachable!() };
        let fn_ty = Type::Fn(vec![a_var.clone(), a_var.clone()], Box::new(a_var));
        let scheme = Scheme {
            vars: vec![a_id],
            constraints: {
                let mut c = HashMap::new();
                c.insert(a_id, vec![cranelisp_types::TraitName::from("Num")]);
                c
            },
            ty: fn_ty,
        };

        // Bind in scope so infer_var finds it
        tc.bind_local_self(Symbol::from("cfn"), scheme.clone());

        // Register in module so the constrained_fn check finds it
        tc.current_symbol_table_mut().insert(
            Symbol::from("cfn"),
            ModuleEntry::Def {
                scheme: scheme.clone(),
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![Symbol::from("x"), Symbol::from("y")],
                kind: Box::new(cranelisp_types::DefKind::UserFn {
                    constrained_fn: Some(Box::new(ConstrainedFn {
                        defn: Defn {
                            name: Symbol::from("cfn"),
                            docstring: None,
                            variants: vec![DefnVariant {
                                params: vec![Symbol::from("x"), Symbol::from("y")],
                                param_annotations: vec![None, None],
                                body: Expr::IntLit { value: 0, span: Span::SYNTHETIC },
                                span: Span::SYNTHETIC,
                            }],
                            visibility: Visibility::Public,
                            span: Span::SYNTHETIC,
                        },
                        scheme: scheme.clone(),
                    })),
                }),
                callees: Vec::new(),
                got_slot: None,
            },
        );
    }

    // spec: 03-types §3.6.6 — constrained fn as argument in nested apply is rejected
    #[test]
    fn test_constrained_fn_rejected_as_arg_in_nested_apply() {
        let mut tc = tc();
        register_constrained_fn(&mut tc);

        // Set up: (fn [f] f) as an identity function
        tc.bind_local_self(
            Symbol::from("id"),
            Scheme {
                vars: vec![],
                ty: Type::Fn(
                    vec![Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int))],
                    Box::new(Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int))),
                ),
                constraints: HashMap::new(),
            },
        );

        // (id cfn) — cfn is an argument, NOT in call position → should error
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("id"),
                span: span(3000, 3002),
            }),
            args: vec![Expr::Var {
                name: Symbol::from("cfn"),
                span: span(3003, 3006),
            }],
            span: span(2999, 3007),
        };

        let err = tc.infer_expr_for_test(&expr).unwrap_err();
        assert!(
            err.message().contains("constrained function"),
            "should reject constrained fn as argument, got: {}",
            err.message()
        );
    }

    // spec: 03-types §3.6.6 — constrained fn in call position of nested apply is allowed
    #[test]
    fn test_constrained_fn_allowed_in_call_position() {
        let mut tc = tc();
        register_constrained_fn(&mut tc);

        // (cfn 1 2) — cfn is in call position → should succeed
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("cfn"),
                span: span(3100, 3103),
            }),
            args: vec![
                Expr::IntLit { value: 1, span: span(3104, 3105) },
                Expr::IntLit { value: 2, span: span(3106, 3107) },
            ],
            span: span(3099, 3108),
        };

        // Should succeed (constrained fn in call position is allowed)
        assert!(tc.infer_expr_for_test(&expr).is_ok());
    }

    // -----------------------------------------------------------------------
    // Trait constraint eagerness: trait methods with wrong types error at call site
    // -----------------------------------------------------------------------

    /// Set up Num trait with + method (impl for Int, Float only)
    /// and Ord trait with < method (impl for Int, Float only).
    fn register_num_and_ord_traits(tc: &mut TypeChecker) {
        use cranelisp_types::{DefnVariant, TraitDecl, TraitImpl, TraitMethodSig, TraitName, TypeExpr, Defn};

        // Num trait: + :: (Fn [a a] a)
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
        tc.register_trait_decl_self(&num_decl).unwrap();

        // impl Num for Int
        let int_impl = TraitImpl {
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
        tc.register_trait_impl_self(&int_impl).unwrap();

        // impl Num for Float
        let float_impl = TraitImpl {
            trait_name: TraitName::from("Num"),
            target_type: TypeName::from("Float"),
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
                            name: Symbol::from("add-f64"),
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
        tc.register_trait_impl_self(&float_impl).unwrap();

        // Ord trait: < :: (Fn [a a] Bool)
        let ord_decl = TraitDecl {
            name: TraitName::from("Ord"),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from("<"),
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
        tc.register_trait_decl_self(&ord_decl).unwrap();

        // impl Ord for Int
        let int_ord_impl = TraitImpl {
            trait_name: TraitName::from("Ord"),
            target_type: TypeName::from("Int"),
            type_args: vec![],
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("<"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![Symbol::from("x"), Symbol::from("y")],
                    param_annotations: vec![None, None],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("lt-i64"),
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
        tc.register_trait_impl_self(&int_ord_impl).unwrap();

        tc.clear_transient_state();
    }

    // spec: 07-traits §7.4.3 — (+ true true) errors: Bool has no Num impl
    #[test]
    fn test_trait_method_plus_bool_error() {
        let mut tc = tc();
        register_num_and_ord_traits(&mut tc);

        // (+ true true)
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("+"),
                span: span(4001, 4002),
            }),
            args: vec![
                Expr::BoolLit { value: true, span: span(4003, 4007) },
                Expr::BoolLit { value: true, span: span(4008, 4012) },
            ],
            span: span(4000, 4013),
        };

        let err = tc.infer_expr_for_test(&expr).unwrap_err();
        assert!(
            err.message().contains("no impl of trait Num for type Bool"),
            "expected Num/Bool error, got: {}",
            err.message()
        );
    }

    // spec: 07-traits §7.4.3 — (+ "a" "b") errors: String has no Num impl
    #[test]
    fn test_trait_method_plus_string_error() {
        let mut tc = tc();
        register_num_and_ord_traits(&mut tc);

        // (+ "a" "b")
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("+"),
                span: span(4101, 4102),
            }),
            args: vec![
                Expr::StringLit { value: "a".to_string(), span: span(4103, 4106) },
                Expr::StringLit { value: "b".to_string(), span: span(4107, 4110) },
            ],
            span: span(4100, 4111),
        };

        let err = tc.infer_expr_for_test(&expr).unwrap_err();
        assert!(
            err.message().contains("no impl of trait Num for type String"),
            "expected Num/String error, got: {}",
            err.message()
        );
    }

    // spec: 07-traits §7.4.3 — (< true false) errors: Bool has no Ord impl
    #[test]
    fn test_trait_method_lt_bool_error() {
        let mut tc = tc();
        register_num_and_ord_traits(&mut tc);

        // (< true false)
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("<"),
                span: span(4201, 4202),
            }),
            args: vec![
                Expr::BoolLit { value: true, span: span(4203, 4207) },
                Expr::BoolLit { value: false, span: span(4208, 4213) },
            ],
            span: span(4200, 4214),
        };

        let err = tc.infer_expr_for_test(&expr).unwrap_err();
        assert!(
            err.message().contains("no impl of trait Ord for type Bool"),
            "expected Ord/Bool error, got: {}",
            err.message()
        );
    }

    // spec: 07-traits §7.4.3 — (< "a" "b") errors: String has no Ord impl
    #[test]
    fn test_trait_method_lt_string_error() {
        let mut tc = tc();
        register_num_and_ord_traits(&mut tc);

        // (< "a" "b")
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("<"),
                span: span(4301, 4302),
            }),
            args: vec![
                Expr::StringLit { value: "a".to_string(), span: span(4303, 4306) },
                Expr::StringLit { value: "b".to_string(), span: span(4307, 4310) },
            ],
            span: span(4300, 4311),
        };

        let err = tc.infer_expr_for_test(&expr).unwrap_err();
        assert!(
            err.message().contains("no impl of trait Ord for type String"),
            "expected Ord/String error, got: {}",
            err.message()
        );
    }

    // spec: 07-traits §7.4.3 — (+ 1 true) errors: type mismatch (Int vs Bool)
    #[test]
    fn test_trait_method_mixed_types_error() {
        let mut tc = tc();
        register_num_and_ord_traits(&mut tc);

        // (+ 1 true) — first arg is Int, second is Bool → unification error
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("+"),
                span: span(4401, 4402),
            }),
            args: vec![
                Expr::IntLit { value: 1, span: span(4403, 4404) },
                Expr::BoolLit { value: true, span: span(4405, 4409) },
            ],
            span: span(4400, 4410),
        };

        // Should error: either unification fails (Int vs Bool) or constraint fails
        assert!(tc.infer_expr_for_test(&expr).is_err());
    }

    // spec: 07-traits §7.4.1 — (+ 1 2) succeeds: Int has Num impl
    #[test]
    fn test_trait_method_plus_int_succeeds() {
        let mut tc = tc();
        register_num_and_ord_traits(&mut tc);

        // (+ 1 2) -> Int
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("+"),
                span: span(4501, 4502),
            }),
            args: vec![
                Expr::IntLit { value: 1, span: span(4503, 4504) },
                Expr::IntLit { value: 2, span: span(4505, 4506) },
            ],
            span: span(4500, 4507),
        };

        let ty = tc.infer_expr_for_test(&expr).unwrap();
        assert_eq!(ty, Type::Int);

        // Check TraitMethod resolution was recorded
        let resolution = tc.state.method_resolutions.get(&span(4500, 4507)).unwrap();
        match resolution {
            ResolvedCall::TraitMethod { mangled_name, .. } => {
                assert_eq!(mangled_name.as_ref(), "Num.+$Int");
            }
            _ => panic!("expected TraitMethod resolution, got {resolution:?}"),
        }
    }

    // spec: 07-traits §7.4.1 — (+ 1.0 2.0) succeeds: Float has Num impl
    #[test]
    fn test_trait_method_plus_float_succeeds() {
        let mut tc = tc();
        register_num_and_ord_traits(&mut tc);

        // (+ 1.0 2.0) -> Float
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("+"),
                span: span(4601, 4602),
            }),
            args: vec![
                Expr::FloatLit { value: 1.0, span: span(4603, 4606) },
                Expr::FloatLit { value: 2.0, span: span(4607, 4610) },
            ],
            span: span(4600, 4611),
        };

        let ty = tc.infer_expr_for_test(&expr).unwrap();
        assert_eq!(ty, Type::Float);
    }
}
