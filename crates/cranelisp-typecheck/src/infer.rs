//! Expression type inference: one method per Expr variant.
//!
//! `infer_expr` dispatches to per-variant helpers. Each helper is typically
//! 10-40 lines, independently testable. Addresses audit HIGH-1 (monolithic infer_expr).

use std::collections::HashMap;

use cranelisp_types::{ErrorLocation, 
    CranelispError, Expr, MatchArm, ModuleEntry, Pattern, ResolvedCall, Scheme, Span, Symbol,
    Type, TypeExpr,
};

use crate::checker::{CheckState, TypeCheckEnv};
use crate::scheme::mono;

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Infer the type of an expression. Main dispatch method.
    pub(crate) fn infer_expr(&self, state: &mut CheckState, expr: &Expr) -> Result<Type, CranelispError> {
        match expr {
            Expr::IntLit { span, .. } => self.infer_int_lit(state, *span),
            Expr::FloatLit { span, .. } => self.infer_float_lit(state, *span),
            Expr::BoolLit { span, .. } => self.infer_bool_lit(state, *span),
            Expr::Var { name, span, .. } => self.infer_var(state, name, *span),
            Expr::Let {
                bindings,
                body,
                span,
                ..
            } => self.infer_let(state, bindings, body, *span),
            Expr::If {
                cond,
                then_branch,
                else_branch,
                span,
                ..
            } => self.infer_if(state, cond, then_branch, else_branch, *span),
            Expr::Lambda {
                params,
                body,
                span,
                ..
            } => self.infer_lambda(state, params, body, *span),
            Expr::Apply {
                callee,
                args,
                span,
                ..
            } => self.infer_apply(state, callee, args, *span),
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
                ..
            } => self.infer_annotate(state, annotation, expr, *span),

            Expr::StringLit { span, .. } => self.infer_string_lit(state, *span),
            Expr::VecLit { elements, span, .. } => self.infer_vec_lit(state, elements, *span),
            Expr::Trace { body, span, .. } => self.infer_trace(state, body, *span),
            // ParBind is semantically identical to Let for type-checking;
            // parallel execution is a codegen concern.
            Expr::ParBind {
                bindings,
                body,
                span,
                ..
            } => self.infer_let(state, bindings, body, *span),
            // Trigger 2 (S70 shared `instantiate_ctor` helper): the typing rule
            // for synthesised `Expr::ConstrADT` nodes inside constructor Def
            // bodies. Resolves the (type_name, tag) identity to the ctor's
            // instantiated scheme, unifies fields, and returns the ADT result.
            Expr::ConstrADT { type_name, tag, fields, span, .. } => {
                self.infer_constradt(state, type_name, *tag, fields, *span)
            }
        }
    }

    /// Typing rule for `Expr::ConstrADT { type_name, tag, fields, span }`.
    /// Per S70 Trigger 2 — shares the `instantiate_ctor` resolution helper
    /// with `check_constructor_pattern`. Pattern matching consumes the
    /// instantiated type as the scrutinee target; constructor-call typing
    /// consumes it as the result, with field types unified against it.
    fn infer_constradt(
        &self,
        state: &mut CheckState,
        type_name: &cranelisp_types::FQTypeName,
        tag: usize,
        fields: &[Expr],
        span: Span,
    ) -> Result<Type, CranelispError> {
        let (_fq_sym, instantiated) = self.instantiate_ctor(state, type_name, tag, span)?;
        match instantiated {
            Type::ADT(..) if fields.is_empty() => {
                self.record_expr_type(state, span, instantiated.clone());
                Ok(instantiated)
            }
            Type::Fn(field_tys, adt_ty) => {
                if fields.len() != field_tys.len() {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "constructor expects {} fields, got {}",
                            field_tys.len(),
                            fields.len()
                        ),
                        location: ErrorLocation::from_span(span),
                    });
                }
                for (f_expr, expected) in fields.iter().zip(field_tys.iter()) {
                    let f_ty = self.infer_expr(state, f_expr)?;
                    self.unify(state, &f_ty, expected, f_expr.span())?;
                }
                let result = *adt_ty;
                self.record_expr_type(state, span, result.clone());
                Ok(result)
            }
            other => Err(CranelispError::TypeError {
                message: format!("unexpected constructor type for {}#{}: {:?}", type_name.name, tag, other),
                location: ErrorLocation::from_span(span),
            }),
        }
    }

    /// Trigger 2 shared helper: resolve a constructor identity to its FQ
    /// symbol + instantiated type. Used by both pattern matching and
    /// constructor-call typing. The returned `Type` is `Type::ADT(..)` for
    /// nullary constructors, `Type::Fn(field_tys, adt_ty)` for data
    /// constructors.
    pub(crate) fn instantiate_ctor(
        &self,
        state: &mut CheckState,
        type_name: &cranelisp_types::FQTypeName,
        tag: usize,
        span: Span,
    ) -> Result<(cranelisp_types::FQSymbol, Type), CranelispError> {
        // Look up the type's TypeDefInfo in its defining module.
        let info = self.lookup_type_def_in_module(&type_name.module, &type_name.name)
            .ok_or_else(|| CranelispError::TypeError {
                message: format!("unknown type in constructor: {type_name}"),
                location: ErrorLocation::from_span(span),
            })?;
        if tag >= info.constructors.len() {
            return Err(CranelispError::TypeError {
                message: format!("constructor tag {tag} out of range for {type_name}"),
                location: ErrorLocation::from_span(span),
            });
        }
        let ctor_sym = info.constructors[tag].clone();
        let fq_ctor = cranelisp_types::FQSymbol {
            module: type_name.module.clone(),
            symbol: ctor_sym.clone(),
        };
        // Look up the ctor's scheme via its Def in the type's defining module.
        let scheme = self
            .probe_module_entry_owned(&type_name.module, ctor_sym.as_ref())
            .and_then(|e| match e {
                cranelisp_types::ModuleEntry::Def { scheme, .. } => Some(scheme.clone()),
                _ => None,
            })
            .ok_or_else(|| CranelispError::TypeError {
                message: format!("constructor {fq_ctor} has no scheme"),
                location: ErrorLocation::from_span(span),
            })?;
        Ok((fq_ctor, self.instantiate(state, &scheme)))
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
            location: ErrorLocation::from_span(span),
        })?;

        // Don't instantiate special forms -- they are not callable as values.
        // Per S69 Submission 36: special forms live on `ModuleEntry::SpecialForm`,
        // not as a `DefKind` discriminator.
        {
            let r = self.current_symbol_table(state);
            let v = r.view();
            if let Some(ModuleEntry::SpecialForm { .. }) = v.lookup(name) {
                return Err(CranelispError::TypeError {
                    message: format!("{name} is a special form, not a value"),
                    location: ErrorLocation::from_span(span),
                });
            }
        }

        // Reject internal constructors (e.g. Bind) — they cannot be
        // constructed by user code, only by compiler-generated primitives.
        if self.is_internal_constructor(state, name) {
            return Err(CranelispError::TypeError {
                message: format!(
                    "cannot construct internal type constructor '{name}'"
                ),
                location: ErrorLocation::from_span(span),
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
                location: ErrorLocation::from_span(span),
            });
        }

        // Multi-sig (overloaded) functions cannot be used as bare values.
        // They must be called so the dispatch can select the correct variant.
        if !state.in_call_position
            && let Some(entry) = self.resolve_entry_in_current_module(state, name)
            && let ModuleEntry::Def { kind, .. } = entry
            && matches!(kind.as_ref(), cranelisp_types::DefKind::Overloaded { .. })
        {
            return Err(CranelispError::TypeError {
                message: format!(
                    "multi-sig function '{name}' cannot be used as a value \
                     — it must be called with arguments"
                ),
                location: ErrorLocation::from_span(span),
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
        params: &[(Symbol, Option<TypeExpr>)],
        body: &Expr,
        span: Span,
    ) -> Result<Type, CranelispError> {
        self.push_scope(state);

        let mut param_types = Vec::new();
        for (param_name, annotation) in params.iter() {
            let param_ty = if let Some(annotation) = annotation {
                let var_map = HashMap::new();
                self.resolve_type_expr_in_module(
                    annotation, &var_map, &state.current_module, span,
                )?
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
                state.method_resolutions.resolved_calls.insert(span, resolution);
            } else if let Some(jit_name) = self.resolve_primitive_jit_name(state, name) {
                // Named primitive resolution (Ring 0-3): add-i64, str-concat,
                // macros/sconcat, quote-sexp, etc.
                state.method_resolutions
                    .resolved_calls
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
                    location: ErrorLocation::from_span(span),
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
                        // Per Decision 48: the symbol-table key IS the JIT linker
                        // name for primitives. Return the bare entry name.
                        if matches!(kind.as_ref(), DefKind::Primitive) {
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
            // Per Decision 48: the symbol-table key IS the JIT linker name for
            // primitives. Return the bare entry name.
            if matches!(kind.as_ref(), DefKind::Primitive) {
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
            Expr::Apply { callee, args, span, .. } => {
                // Try to resolve this Apply if it's not already resolved
                if !state.method_resolutions.resolved_calls.contains_key(span)
                    && let Expr::Var { name, .. } = callee.as_ref()
                    && self.is_trait_method_with_state(state, name)
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
                        state.method_resolutions.resolved_calls.insert(*span, resolution);
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
                location: ErrorLocation::from_span(span),
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
                    // SymbolRef carries as-written qualification; for now
                    // pass the inner Symbol (qualified module prefix folds
                    // into the name string for string-based lookups below).
                    let ctor_sym = if let Some(module) = &name.module {
                        Symbol::from(format!("{}/{}", module, name.name).as_str())
                    } else {
                        name.name.clone()
                    };
                    self.check_constructor_pattern(state,
                        &ctor_sym,
                        bindings,
                        &scrutinee_ty,
                        *pat_span,
                    )?;
                    covered_ctors.push(ctor_sym);
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

        // Check exhaustiveness for concrete ADT scrutinees.
        // The type is defined in `fqtn.module` (its home module), not the
        // current module — under Principle 17 short-name resolution, looking
        // up the type via `state.current_module` would fail for ADTs imported
        // from other modules (e.g. `macros/SList` matched in `fn.threading`).
        let resolved_scrutinee = self.apply_subst(state, &scrutinee_ty);
        if let Type::ADT(fqtn, _) = &resolved_scrutinee {
            self.check_exhaustiveness_in_module(
                fqtn,
                &covered_ctors,
                has_wildcard,
                span,
            )?;
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
        if self.is_internal_constructor(state, name) {
            return Err(CranelispError::TypeError {
                message: format!(
                    "cannot match on internal type constructor '{name}'"
                ),
                location: ErrorLocation::from_span(span),
            });
        }

        // Trigger 3 (S70): populate `MethodResolutions.pattern_ctors` keyed
        // by `pat_span`. The bare `Symbol` slipping into backend codegen for
        // pattern dispatch is the D47-violation flagged by the
        // cranelisp-types solidness sweep (finding #4); the FQ-typed sidecar
        // is the resolved-stage replacement.
        //
        // Look up the ctor's owning Def to recover (type_name, tag) — these
        // live on `DefKind::Constructor` post-S70 (the prior
        // `ModuleEntry::Constructor` variant was retired). The lookup
        // returns the terminal entry, following Import chains.
        if let Some(entry) = self.resolve_entry_in_current_module(state, name.as_ref()) {
            if let cranelisp_types::ModuleEntry::Def { kind, .. } = &entry {
                if let cranelisp_types::DefKind::Constructor { type_name, tag, .. } = kind.as_ref() {
                    // Use the shared `instantiate_ctor` helper for the
                    // resolution+instantiation core (Trigger 2 sharing).
                    let (fq_sym, instantiated) = self.instantiate_ctor(
                        state, type_name, *tag, span,
                    )?;
                    state.method_resolutions.pattern_ctors.insert(span, fq_sym);
                    return self.unify_pattern_with_scrutinee(
                        state, name, bindings, &instantiated, scrutinee_ty, span,
                    );
                }
            }
        }

        // Fallback: the ctor's name doesn't resolve to a Def with
        // DefKind::Constructor (e.g., product-type single-ctor cases that
        // route through `constructor_scheme` on TypeDef). Use the legacy
        // scheme lookup until the type-def-product path is migrated.
        let ctor_scheme = self.lookup_constructor_scheme(state, name, span)?;
        let instantiated = self.instantiate(state, &ctor_scheme);
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
        // Constructor name can be bare (`SCons`, looked up in current module
        // via Principle 17 import-scoped resolution) or fully qualified
        // (`macros/SCons`, looked up in the named module directly — FQ refs
        // bypass the import system per the module-locality model).
        let exists = if let Some(slash_pos) = name.as_ref().find('/') {
            let module_str = &name.as_ref()[..slash_pos];
            let bare_name = &name.as_ref()[slash_pos + 1..];
            let module_path = cranelisp_types::ModuleFullPath::from(module_str);
            self.lookup_constructor_type_in_module(&module_path, bare_name)
                .is_some()
        } else {
            self.lookup_constructor_type_with_state(state, name.as_ref())
                .is_some()
        };
        if !exists {
            return Err(CranelispError::TypeError {
                message: format!("unknown constructor in pattern: {name}"),
                location: ErrorLocation::from_span(span),
            });
        }

        // Get the scheme from the symbol table (handles qualified names via lookup)
        self.lookup(state, name).ok_or_else(|| CranelispError::TypeError {
            message: format!("constructor {name} has no type scheme"),
            location: ErrorLocation::from_span(span),
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
                        location: ErrorLocation::from_span(span),
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
                location: ErrorLocation::from_span(span),
            }),
        }
    }

    /// Bind pattern variables for a data constructor with fields.
    #[allow(clippy::too_many_arguments)]
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
                location: ErrorLocation::from_span(span),
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

        let vec_type = Type::ADT(
            cranelisp_types::FQTypeName::new(
                cranelisp_types::ModuleFullPath::from("primitives"),
                cranelisp_types::TypeName::from("Vec"),
            ),
            vec![elem_type],
        );
        self.record_expr_type(state, span, vec_type.clone());
        Ok(vec_type)
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

        let trace_type = Type::ADT(
            cranelisp_types::FQTypeName::new(
                cranelisp_types::ModuleFullPath::from("primitives"),
                cranelisp_types::TypeName::from("Trace"),
            ),
            vec![],
        );
        self.record_expr_type(state, span, trace_type.clone());
        Ok(trace_type)
    }

    /// Infer the type of an annotated expression `(:T e)` per spec §3.5.
    /// Resolves the type expression `T`, infers the body's type, unifies the two,
    /// and records the resolved type at `span`.
    fn infer_annotate(
        &self, state: &mut CheckState,
        annotation: &TypeExpr,
        expr: &Expr,
        span: Span,
    ) -> Result<Type, CranelispError> {
        let var_map = HashMap::new();
        let ann_type = self.resolve_type_expr_in_module(
            annotation, &var_map, &state.current_module, span,
        )?;

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
    use crate::checker::TestFixture;
    use cranelisp_types::{ConstructorDef, FQTypeName, ImportNames, ImportSpec, ModuleEntry, ModuleFullPath, Span, Symbol, TypeName, Visibility};

    /// Test helper: create an FQTypeName in the "test" module (used for types registered via
    /// register_type_def_self in tc() which has current_module = "test").
    fn test_fqtn(name: &str) -> FQTypeName {
        FQTypeName::new(ModuleFullPath::from("test"), TypeName::from(name))
    }

    /// Test helper: create an FQTypeName in the "primitives" module.
    fn prims_fqtn(name: &str) -> FQTypeName {
        FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from(name))
    }

    fn span(start: u32, end: u32) -> Span {
        Span::new(start, end)
    }

    /// Create a TypeChecker with builtins for testing.
    /// Uses set_current_module to create a "test" module seeded with primitives.
    fn tc() -> TestFixture {
        let mut tc = TestFixture::new();
        tc.set_current_module(ModuleFullPath::from("test"));
        // Import primitives so bare names (add-i64 etc.) resolve.
        let import_spec = ImportSpec {
            module_path: ModuleFullPath::from("primitives"),
            alias: None,
            names: ImportNames::Glob,
            span: Span::new(0, 0),
        };
        tc.register_imports_self(&[import_spec]).unwrap();
        tc
    }

    /// Register a simple enum type for testing.
    fn register_color(tc: &mut TestFixture) {
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
        let mut expr = Expr::IntLit {
            value: 42,
            span: span(0, 2),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.5.3 — float literal infers to Float
    #[test]
    fn test_infer_float_lit() {
        let mut tc = tc();
        let mut expr = Expr::FloatLit {
            value: 2.72,
            span: span(0, 4),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Float);
    }

    // spec: 03-types §3.5.3 — boolean literal infers to Bool
    #[test]
    fn test_infer_bool_lit() {
        let mut tc = tc();
        let mut expr = Expr::BoolLit {
            value: true,
            span: span(0, 4),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Bool);
    }

    // --- Var tests ---

    // spec: 03-types §3.5.3 — variable reference looks up and instantiates scheme
    #[test]
    fn test_infer_var_defined() {
        let mut tc = tc();
        tc.bind_local_self(Symbol::from("x"), mono(Type::Int));
        let mut expr = Expr::Var {
            name: Symbol::from("x"),
            span: span(0, 1),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.5.3 — undefined variable reference is a type error
    #[test]
    fn test_infer_var_undefined() {
        let mut tc = tc();
        let mut expr = Expr::Var {
            name: Symbol::from("x"),
            span: span(0, 1),
            inferred_type: None,
        };
        assert!(tc.infer_expr_for_test(&mut expr).is_err());
    }

    // --- Let tests ---

    // spec: 03-types §3.5.3 — let binding infers value type and propagates to body
    #[test]
    fn test_infer_let_simple() {
        let mut tc = tc();
        // (let [x 42] x)
        let mut expr = Expr::Let {
            bindings: vec![(
                Symbol::from("x"),
                Expr::IntLit {
                    value: 42,
                    span: span(6, 8),
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Var {
                name: Symbol::from("x"),
                span: span(10, 11),
                inferred_type: None,
            }),
            span: span(0, 12),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.5.3 — let sequential bindings: later bindings see earlier ones
    #[test]
    fn test_infer_let_sequential_bindings() {
        let mut tc = tc();
        // (let [x 42 y x] y)
        let mut expr = Expr::Let {
            bindings: vec![
                (
                    Symbol::from("x"),
                    Expr::IntLit {
                        value: 42,
                        span: span(6, 8),
                        inferred_type: None,
                    },
                ),
                (
                    Symbol::from("y"),
                    Expr::Var {
                        name: Symbol::from("x"),
                        span: span(11, 12),
                        inferred_type: None,
                    },
                ),
            ],
            body: Box::new(Expr::Var {
                name: Symbol::from("y"),
                span: span(14, 15),
                inferred_type: None,
            }),
            span: span(0, 16),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // --- If tests ---

    // spec: 03-types §3.5.3 — if expression: branches unify, result is branch type
    #[test]
    fn test_infer_if_ok() {
        let mut tc = tc();
        // (if true 1 2)
        let mut expr = Expr::If {
            cond: Box::new(Expr::BoolLit {
                value: true,
                span: span(4, 8),
                inferred_type: None,
            }),
            then_branch: Box::new(Expr::IntLit {
                value: 1,
                span: span(9, 10),
                inferred_type: None,
            }),
            else_branch: Box::new(Expr::IntLit {
                value: 2,
                span: span(11, 12),
                inferred_type: None,
            }),
            span: span(0, 13),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.5.3 — if condition must unify with Bool
    #[test]
    fn test_infer_if_non_bool_condition() {
        let mut tc = tc();
        // (if 42 1 2) -- condition must be Bool
        let mut expr = Expr::If {
            cond: Box::new(Expr::IntLit {
                value: 42,
                span: span(4, 6),
                inferred_type: None,
            }),
            then_branch: Box::new(Expr::IntLit {
                value: 1,
                span: span(7, 8),
                inferred_type: None,
            }),
            else_branch: Box::new(Expr::IntLit {
                value: 2,
                span: span(9, 10),
                inferred_type: None,
            }),
            span: span(0, 11),
            inferred_type: None,
        };
        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
        assert!(err.message().contains("type mismatch"));
    }

    // spec: 03-types §3.5.3 — if branches must unify with each other
    #[test]
    fn test_infer_if_branch_mismatch() {
        let mut tc = tc();
        // (if true 1 true) -- branches must agree
        let mut expr = Expr::If {
            cond: Box::new(Expr::BoolLit {
                value: true,
                span: span(4, 8),
                inferred_type: None,
            }),
            then_branch: Box::new(Expr::IntLit {
                value: 1,
                span: span(9, 10),
                inferred_type: None,
            }),
            else_branch: Box::new(Expr::BoolLit {
                value: true,
                span: span(11, 15),
                inferred_type: None,
            }),
            span: span(0, 16),
            inferred_type: None,
        };
        assert!(tc.infer_expr_for_test(&mut expr).is_err());
    }

    // --- Lambda tests ---

    // spec: 03-types §3.5.3 — lambda: params get fresh vars, result is Fn type
    #[test]
    fn test_infer_lambda_identity() {
        let mut tc = tc();
        // (fn [x] x)
        let mut expr = Expr::Lambda {
            params: vec![(Symbol::from("x"), None)],
            body: Box::new(Expr::Var {
                name: Symbol::from("x"),
                span: span(8, 9),
                inferred_type: None,
            }),
            span: span(0, 10),
            inferred_type: None,
        };
        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
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
        let mut expr = Expr::Lambda {
            params: vec![(Symbol::from("x"), Some(TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int")))))],
            body: Box::new(Expr::Var {
                name: Symbol::from("x"),
                span: span(13, 14),
                inferred_type: None,
            }),
            span: span(0, 15),
            inferred_type: None,
        };
        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(ty, Type::Fn(vec![Type::Int], Box::new(Type::Int)));
    }

    // --- Apply tests ---

    // spec: 03-types §3.5.3 — function application unifies callee with arg types
    #[test]
    fn test_infer_apply_lambda() {
        let mut tc = tc();
        // ((fn [x] x) 42)
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Lambda {
                params: vec![(Symbol::from("x"), None)],
                body: Box::new(Expr::Var {
                    name: Symbol::from("x"),
                    span: span(8, 9),
                    inferred_type: None,
                }),
                span: span(1, 10),
                inferred_type: None,
            }),
            args: vec![Expr::IntLit {
                value: 42,
                span: span(11, 13),
                inferred_type: None,
            }],
            span: span(0, 14),
            resolved_call: None,
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.5.3 — apply primitive add-i64 records BuiltinFn resolution
    #[test]
    fn test_infer_apply_int_add() {
        let mut tc = tc();
        // (add-i64 1 2) -> Int
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(1, 8),
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit {
                    value: 1,
                    span: span(9, 10),
                    inferred_type: None,
                },
                Expr::IntLit {
                    value: 2,
                    span: span(11, 12),
                    inferred_type: None,
                },
            ],
            span: span(0, 13),
            resolved_call: None,
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);

        // Check that a BuiltinFn resolution was recorded
        let resolution = tc.state.method_resolutions.resolved_calls.get(&span(0, 13)).unwrap();
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
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-f64"),
                span: span(1, 8),
                inferred_type: None,
            }),
            args: vec![
                Expr::FloatLit {
                    value: 1.0,
                    span: span(9, 12),
                    inferred_type: None,
                },
                Expr::FloatLit {
                    value: 2.0,
                    span: span(13, 16),
                    inferred_type: None,
                },
            ],
            span: span(0, 17),
            resolved_call: None,
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Float);

        let resolution = tc.state.method_resolutions.resolved_calls.get(&span(0, 17)).unwrap();
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
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("eq-i64"),
                span: span(1, 7),
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit {
                    value: 1,
                    span: span(8, 9),
                    inferred_type: None,
                },
                Expr::IntLit {
                    value: 2,
                    span: span(10, 11),
                    inferred_type: None,
                },
            ],
            span: span(0, 12),
            resolved_call: None,
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Bool);
    }

    // spec: appendix-a-builtins §A.3 — not primitive: Bool -> Bool
    #[test]
    fn test_infer_apply_not() {
        let mut tc = tc();
        // (not true) -> Bool
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("not"),
                span: span(1, 4),
                inferred_type: None,
            }),
            args: vec![Expr::BoolLit {
                value: true,
                span: span(5, 9),
                inferred_type: None,
            }],
            span: span(0, 10),
            resolved_call: None,
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Bool);

        let resolution = tc.state.method_resolutions.resolved_calls.get(&span(0, 10)).unwrap();
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
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(1, 8),
                inferred_type: None,
            }),
            args: vec![
                Expr::FloatLit {
                    value: 1.0,
                    span: span(9, 12),
                    inferred_type: None,
                },
                Expr::FloatLit {
                    value: 2.0,
                    span: span(13, 16),
                    inferred_type: None,
                },
            ],
            span: span(0, 17),
            resolved_call: None,
            inferred_type: None,
        };
        assert!(tc.infer_expr_for_test(&mut expr).is_err(), "add-i64 with float args should fail");
    }

    // spec: 04-expressions §4.6.3 — too few args triggers auto-curry
    #[test]
    fn test_infer_apply_auto_curry() {
        let mut tc = tc();
        // (add-i64 1) -- too few args, auto-curry returns Fn([Int], Int)
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(1, 8),
                inferred_type: None,
            }),
            args: vec![Expr::IntLit {
                value: 1,
                span: span(9, 10),
                inferred_type: None,
            }],
            span: span(0, 11),
            resolved_call: None,
            inferred_type: None,
        };
        let ty = tc.infer_expr_for_test(&mut expr).expect("auto-curry should succeed");
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
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(1, 8),
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit { value: 1, span: span(9, 10), inferred_type: None, },
                Expr::IntLit { value: 2, span: span(11, 12), inferred_type: None, },
                Expr::IntLit { value: 3, span: span(13, 14), inferred_type: None, },
            ],
            span: span(0, 15),
            resolved_call: None,
            inferred_type: None,
        };
        assert!(tc.infer_expr_for_test(&mut expr).is_err());
    }

    // --- Match tests ---

    // spec: 06-pattern-matching §6.1 — match enum with all constructors covered
    #[test]
    fn test_infer_match_enum() {
        let mut tc = tc();
        register_color(&mut tc);

        // (match Red [Red 1 Green 2 Blue 3])
        let mut expr = Expr::Match {
            scrutinee: Box::new(Expr::Var {
                name: Symbol::from("Red"),
                span: span(7, 10),
                inferred_type: None,
            }),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: cranelisp_types::SymbolRef::new(None, Symbol::from("Red")),
                        bindings: vec![],
                        span: span(12, 15),
                    },
                    body: Expr::IntLit {
                        value: 1,
                        span: span(16, 17),
                        inferred_type: None,
                    },
                    span: span(12, 17),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: cranelisp_types::SymbolRef::new(None, Symbol::from("Green")),
                        bindings: vec![],
                        span: span(18, 23),
                    },
                    body: Expr::IntLit {
                        value: 2,
                        span: span(24, 25),
                        inferred_type: None,
                    },
                    span: span(18, 25),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: cranelisp_types::SymbolRef::new(None, Symbol::from("Blue")),
                        bindings: vec![],
                        span: span(26, 30),
                    },
                    body: Expr::IntLit {
                        value: 3,
                        span: span(31, 32),
                        inferred_type: None,
                    },
                    span: span(26, 32),
                },
            ],
            span: span(0, 33),
            compiler_generated: false,
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 06-pattern-matching §6.5.1 — non-exhaustive match on ADT is compile error
    #[test]
    fn test_infer_match_non_exhaustive() {
        let mut tc = tc();
        register_color(&mut tc);

        // Match with only Red -- missing Green, Blue
        let mut expr = Expr::Match {
            scrutinee: Box::new(Expr::Var {
                name: Symbol::from("Red"),
                span: span(7, 10),
                inferred_type: None,
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: cranelisp_types::SymbolRef::new(None, Symbol::from("Red")),
                    bindings: vec![],
                    span: span(12, 15),
                },
                body: Expr::IntLit {
                    value: 1,
                    span: span(16, 17),
                    inferred_type: None,
                },
                span: span(12, 17),
            }],
            span: span(0, 18),
            compiler_generated: false,
            inferred_type: None,
        };
        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
        assert!(err.message().contains("non-exhaustive"));
    }

    // spec: 06-pattern-matching §6.2.3 — wildcard pattern covers remaining cases
    #[test]
    fn test_infer_match_wildcard() {
        let mut tc = tc();
        register_color(&mut tc);

        // (match Red [Red 1 _ 0])
        let mut expr = Expr::Match {
            scrutinee: Box::new(Expr::Var {
                name: Symbol::from("Red"),
                span: span(7, 10),
                inferred_type: None,
            }),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: cranelisp_types::SymbolRef::new(None, Symbol::from("Red")),
                        bindings: vec![],
                        span: span(12, 15),
                    },
                    body: Expr::IntLit {
                        value: 1,
                        span: span(16, 17),
                        inferred_type: None,
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
                        inferred_type: None,
                    },
                    span: span(18, 21),
                },
            ],
            span: span(0, 22),
            compiler_generated: false,
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 06-pattern-matching §6.2.4 — variable pattern binds scrutinee value
    #[test]
    fn test_infer_match_var_pattern() {
        let mut tc = tc();
        register_color(&mut tc);

        // (match Red [x 1]) -- var pattern binds scrutinee
        let mut expr = Expr::Match {
            scrutinee: Box::new(Expr::Var {
                name: Symbol::from("Red"),
                span: span(7, 10),
                inferred_type: None,
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Var {
                    name: Symbol::from("x"),
                    span: span(12, 13),
                },
                body: Expr::IntLit {
                    value: 1,
                    span: span(14, 15),
                    inferred_type: None,
                },
                span: span(12, 15),
            }],
            span: span(0, 16),
            compiler_generated: false,
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // --- Annotate tests ---

    // spec: 03-types §3.9.1 — annotation matching inferred type succeeds
    #[test]
    fn test_infer_annotate_matching() {
        let mut tc = tc();
        // (:Int 42) -- annotation matches
        let mut expr = Expr::Annotate {
            annotation: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
            expr: Box::new(Expr::IntLit {
                value: 42,
                span: span(5, 7),
                inferred_type: None,
            }),
            span: span(0, 8),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.9.1 — annotation mismatching inferred type fails
    #[test]
    fn test_infer_annotate_mismatch() {
        let mut tc = tc();
        // (:Bool 42) -- annotation doesn't match
        let mut expr = Expr::Annotate {
            annotation: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Bool"))),
            expr: Box::new(Expr::IntLit {
                value: 42,
                span: span(6, 8),
                inferred_type: None,
            }),
            span: span(0, 9),
            inferred_type: None,
        };
        assert!(tc.infer_expr_for_test(&mut expr).is_err());
    }

    // --- expr_types recording tests ---

    // spec: 03-types §3.5.1 — expr_types map records inferred type per span
    #[test]
    fn test_expr_types_recorded() {
        let mut tc = tc();
        let s = span(0, 2);
        let mut expr = Expr::IntLit { value: 42, span: s, inferred_type: None, };
        tc.infer_expr_for_test(&mut expr).unwrap();
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
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit {
                    value: 1,
                    span: span(17, 18),
                    inferred_type: None,
                },
                Expr::IntLit {
                    value: 2,
                    span: span(19, 20),
                    inferred_type: None,
                },
            ],
            span: span(8, 21),
            resolved_call: None,
            inferred_type: None,
        };
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(1, 8),
                inferred_type: None,
            }),
            args: vec![
                inner,
                Expr::IntLit {
                    value: 3,
                    span: span(23, 24),
                    inferred_type: None,
                },
            ],
            span: span(0, 25),
            resolved_call: None,
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // --- String literal tests (Ring 1) ---

    // spec: 03-types §3.5.3 — string literal infers to String
    #[test]
    fn test_infer_string_lit() {
        let mut tc = tc();
        let mut expr = Expr::StringLit {
            value: "hello".to_string(),
            span: span(0, 7),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::String);
    }

    // spec: 03-types §3.5.1 — string literal records String in expr_types
    #[test]
    fn test_string_lit_expr_types_recorded() {
        let mut tc = tc();
        let s = span(0, 7);
        let mut expr = Expr::StringLit {
            value: "hello".to_string(),
            span: s,
            inferred_type: None,
        };
        tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(tc.state.expr_types.get(&s), Some(&Type::String));
    }

    // --- Data constructor pattern tests (Ring 1) ---

    /// Register (Option a) with None and Some[:a val].
    fn register_option(tc: &mut TestFixture) {
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
                        span: Span::SYNTHETIC,
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
        let mut expr = Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: span(8, 12),
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit {
                    value: 42,
                    span: span(13, 15),
                    inferred_type: None,
                }],
                span: span(7, 16),
                resolved_call: None,
                inferred_type: None,
            }),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: cranelisp_types::SymbolRef::new(None, Symbol::from("Some")),
                        bindings: vec![Symbol::from("x")],
                        span: span(18, 24),
                    },
                    body: Expr::Var {
                        name: Symbol::from("x"),
                        span: span(26, 27),
                        inferred_type: None,
                    },
                    span: span(18, 27),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: cranelisp_types::SymbolRef::new(None, Symbol::from("None")),
                        bindings: vec![],
                        span: span(29, 33),
                    },
                    body: Expr::IntLit {
                        value: 0,
                        span: span(34, 35),
                        inferred_type: None,
                    },
                    span: span(29, 35),
                },
            ],
            span: span(0, 36),
            compiler_generated: false,
            inferred_type: None,
        };

        // Should infer result type Int (x : Int from Some pattern, 0 : Int)
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 06-pattern-matching §6.2.1 — wrong binding count in constructor pattern is error
    #[test]
    fn test_infer_match_data_constructor_wrong_binding_count() {
        let mut tc = tc();
        register_option(&mut tc);

        // (match (Some 42) [(Some x y) x]) -- too many bindings
        let mut expr = Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: span(108, 112),
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit {
                    value: 42,
                    span: span(113, 115),
                    inferred_type: None,
                }],
                span: span(107, 116),
                resolved_call: None,
                inferred_type: None,
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: cranelisp_types::SymbolRef::new(None, Symbol::from("Some")),
                    bindings: vec![Symbol::from("x"), Symbol::from("y")],
                    span: span(118, 128),
                },
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: span(130, 131),
                    inferred_type: None,
                },
                span: span(118, 131),
            }],
            span: span(100, 132),
            compiler_generated: false,
            inferred_type: None,
        };

        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
        assert!(err.message().contains("expects 1 field"));
    }

    // spec: 06-pattern-matching §6.2.2 — nullary constructor with bindings is error
    #[test]
    fn test_infer_match_nullary_with_bindings_errors() {
        let mut tc = tc();
        register_option(&mut tc);

        // (match (Some 1) [(None x) x]) -- None is nullary, no bindings allowed
        let mut expr = Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: span(208, 212),
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit {
                    value: 1,
                    span: span(213, 214),
                    inferred_type: None,
                }],
                span: span(207, 215),
                resolved_call: None,
                inferred_type: None,
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: cranelisp_types::SymbolRef::new(None, Symbol::from("None")),
                    bindings: vec![Symbol::from("x")],
                    span: span(217, 224),
                },
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: span(226, 227),
                    inferred_type: None,
                },
                span: span(217, 227),
            }],
            span: span(200, 228),
            compiler_generated: false,
            inferred_type: None,
        };

        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
        assert!(err.message().contains("takes no arguments"));
    }

    // spec: 06-pattern-matching §6.5.1 — non-exhaustive match on Option (missing None)
    #[test]
    fn test_infer_match_option_non_exhaustive() {
        let mut tc = tc();
        register_option(&mut tc);

        // Match only Some, missing None
        let mut expr = Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: span(308, 312),
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit {
                    value: 1,
                    span: span(313, 314),
                    inferred_type: None,
                }],
                span: span(307, 315),
                resolved_call: None,
                inferred_type: None,
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: cranelisp_types::SymbolRef::new(None, Symbol::from("Some")),
                    bindings: vec![Symbol::from("x")],
                    span: span(317, 324),
                },
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: span(326, 327),
                    inferred_type: None,
                },
                span: span(317, 327),
            }],
            span: span(300, 328),
            compiler_generated: false,
            inferred_type: None,
        };

        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
        assert!(err.message().contains("None"));
    }

    // --- Lambda expr_types completeness (Ring 1 validation) ---

    // spec: 03-types §3.5.3 — lambda records Fn type in expr_types
    #[test]
    fn test_lambda_expr_types_recorded() {
        let mut tc = tc();
        let s = span(0, 10);
        let mut expr = Expr::Lambda {
            params: vec![(Symbol::from("x"), Some(TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int")))))],
            body: Box::new(Expr::Var {
                name: Symbol::from("x"),
                span: span(13, 14),
                inferred_type: None,
            }),
            span: s,
            inferred_type: None,
        };
        tc.infer_expr_for_test(&mut expr).unwrap();

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
        let mut annotate_expr = Expr::Annotate {
            annotation: TypeExpr::Applied(cranelisp_types::TypeRef::new(None, TypeName::from("Option")),
                vec![TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int")))],
            ),
            expr: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: span(418, 422),
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit {
                    value: 42,
                    span: span(423, 425),
                    inferred_type: None,
                }],
                span: span(417, 426),
                resolved_call: None,
                inferred_type: None,
            }),
            span: span(400, 427),
            inferred_type: None,
        };

        let ty = tc.infer_expr_for_test(&mut annotate_expr).unwrap();
        assert_eq!(
            ty,
            Type::ADT(test_fqtn("Option"), vec![Type::Int])
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
                        type_expr: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
                        span: Span::SYNTHETIC,
                    },
                    cranelisp_types::FieldDef {
                        name: Symbol::from("y"),
                        type_expr: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int"))),
                        span: Span::SYNTHETIC,
                    },
                ],
                span: Span::SYNTHETIC,
            }],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // (match (Point 1 2) [(Point a b) (add-i64 a b)])
        let mut expr = Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Point"),
                    span: span(508, 513),
                    inferred_type: None,
                }),
                args: vec![
                    Expr::IntLit {
                        value: 1,
                        span: span(514, 515),
                        inferred_type: None,
                    },
                    Expr::IntLit {
                        value: 2,
                        span: span(516, 517),
                        inferred_type: None,
                    },
                ],
                span: span(507, 518),
                resolved_call: None,
                inferred_type: None,
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: cranelisp_types::SymbolRef::new(None, Symbol::from("Point")),
                    bindings: vec![Symbol::from("a"), Symbol::from("b")],
                    span: span(520, 530),
                },
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add-i64"),
                        span: span(532, 539),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("a"),
                            span: span(540, 541),
                            inferred_type: None,
                        },
                        Expr::Var {
                            name: Symbol::from("b"),
                            span: span(542, 543),
                            inferred_type: None,
                        },
                    ],
                    span: span(531, 544),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: span(520, 544),
            }],
            span: span(500, 545),
            compiler_generated: false,
            inferred_type: None,
        };

        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 05-definitions §5.2.7 — data constructor applied as function
    #[test]
    fn test_infer_constructor_as_function() {
        let mut tc = tc();
        register_option(&mut tc);

        // (Some 42) -- constructor applied to argument
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("Some"),
                span: span(601, 605),
                inferred_type: None,
            }),
            args: vec![Expr::IntLit {
                value: 42,
                span: span(606, 608),
                inferred_type: None,
            }],
            span: span(600, 609),
            resolved_call: None,
            inferred_type: None,
        };

        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(
            ty,
            Type::ADT(test_fqtn("Option"), vec![Type::Int])
        );
    }

    // spec: 05-definitions §5.2.7 — nullary constructor is polymorphic value
    #[test]
    fn test_infer_none_has_polymorphic_type() {
        let mut tc = tc();
        register_option(&mut tc);

        // None on its own should be (Option tN) for some N
        let mut expr = Expr::Var {
            name: Symbol::from("None"),
            span: span(700, 704),
            inferred_type: None,
        };

        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        match &ty {
            Type::ADT(name, args) => {
                assert_eq!(name.name.as_ref(), "Option");
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
        let mut expr = Expr::If {
            cond: Box::new(Expr::BoolLit {
                value: true,
                span: span(804, 808),
                inferred_type: None,
            }),
            then_branch: Box::new(Expr::StringLit {
                value: "hello".to_string(),
                span: span(809, 816),
                inferred_type: None,
            }),
            else_branch: Box::new(Expr::StringLit {
                value: "world".to_string(),
                span: span(817, 824),
                inferred_type: None,
            }),
            span: span(800, 825),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::String);
    }

    // spec: 03-types §3.5.3 — let binding with String value
    #[test]
    fn test_infer_string_in_let() {
        let mut tc = tc();
        // (let [s "hello"] s)
        let mut expr = Expr::Let {
            bindings: vec![(
                Symbol::from("s"),
                Expr::StringLit {
                    value: "hello".to_string(),
                    span: span(906, 913),
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Var {
                name: Symbol::from("s"),
                span: span(915, 916),
                inferred_type: None,
            }),
            span: span(900, 917),
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::String);
    }

    // --- Vec literal tests (Sprint 3) ---

    // spec: 03-types §3.5.3 — Vec literal with Int elements infers (Vec Int)
    #[test]
    fn test_infer_vec_lit_ints() {
        let mut tc = tc();
        // [1 2 3]
        let mut expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 1, span: span(1001, 1002), inferred_type: None, },
                Expr::IntLit { value: 2, span: span(1003, 1004), inferred_type: None, },
                Expr::IntLit { value: 3, span: span(1005, 1006), inferred_type: None, },
            ],
            span: span(1000, 1007),
            inferred_type: None,
        };
        assert_eq!(
            tc.infer_expr_for_test(&mut expr).unwrap(),
            Type::ADT(prims_fqtn("Vec"), vec![Type::Int])
        );
    }

    // spec: 03-types §3.5.3 — Vec literal with String elements infers (Vec String)
    #[test]
    fn test_infer_vec_lit_strings() {
        let mut tc = tc();
        // ["a" "b"]
        let mut expr = Expr::VecLit {
            elements: vec![
                Expr::StringLit { value: "a".into(), span: span(1101, 1104), inferred_type: None, },
                Expr::StringLit { value: "b".into(), span: span(1105, 1108), inferred_type: None, },
            ],
            span: span(1100, 1109),
            inferred_type: None,
        };
        assert_eq!(
            tc.infer_expr_for_test(&mut expr).unwrap(),
            Type::ADT(prims_fqtn("Vec"), vec![Type::String])
        );
    }

    // spec: 03-types §3.5.3 — empty Vec literal is polymorphic (Vec a)
    #[test]
    fn test_infer_vec_lit_empty_is_polymorphic() {
        let mut tc = tc();
        // []
        let mut expr = Expr::VecLit {
            elements: vec![],
            span: span(1200, 1202),
            inferred_type: None,
        };
        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        match &ty {
            Type::ADT(name, args) => {
                assert_eq!(name.name.as_ref(), "Vec");
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
        let mut expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 1, span: span(1301, 1302), inferred_type: None, },
                Expr::StringLit { value: "hello".into(), span: span(1303, 1310), inferred_type: None, },
            ],
            span: span(1300, 1311),
            inferred_type: None,
        };
        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
        assert!(err.message().contains("mismatch"), "expected type mismatch error, got: {}", err.message());
    }

    // spec: 03-types §3.5.3 — Vec literal with Bool elements infers (Vec Bool)
    #[test]
    fn test_infer_vec_lit_booleans() {
        let mut tc = tc();
        // [true false]
        let mut expr = Expr::VecLit {
            elements: vec![
                Expr::BoolLit { value: true, span: span(1401, 1405), inferred_type: None, },
                Expr::BoolLit { value: false, span: span(1406, 1411), inferred_type: None, },
            ],
            span: span(1400, 1412),
            inferred_type: None,
        };
        assert_eq!(
            tc.infer_expr_for_test(&mut expr).unwrap(),
            Type::ADT(prims_fqtn("Vec"), vec![Type::Bool])
        );
    }

    // spec: 03-types §3.5.3 — Vec literal in let binding propagates element type
    #[test]
    fn test_infer_vec_lit_in_let_binding() {
        let mut tc = tc();
        // (let [xs [1 2 3]] xs)
        let mut expr = Expr::Let {
            bindings: vec![(
                Symbol::from("xs"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: span(1508, 1509), inferred_type: None, },
                        Expr::IntLit { value: 2, span: span(1510, 1511), inferred_type: None, },
                        Expr::IntLit { value: 3, span: span(1512, 1513), inferred_type: None, },
                    ],
                    span: span(1507, 1514),
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Var {
                name: Symbol::from("xs"),
                span: span(1516, 1518),
                inferred_type: None,
            }),
            span: span(1500, 1519),
            inferred_type: None,
        };
        assert_eq!(
            tc.infer_expr_for_test(&mut expr).unwrap(),
            Type::ADT(prims_fqtn("Vec"), vec![Type::Int])
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
                vec![Type::ADT(prims_fqtn("Vec"), vec![Type::Int])],
                Box::new(Type::Int),
            )),
        );
        // (vec-len [1 2 3])
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: span(1601, 1608),
                inferred_type: None,
            }),
            args: vec![Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 1, span: span(1610, 1611), inferred_type: None, },
                    Expr::IntLit { value: 2, span: span(1612, 1613), inferred_type: None, },
                    Expr::IntLit { value: 3, span: span(1614, 1615), inferred_type: None, },
                ],
                span: span(1609, 1616),
                inferred_type: None,
            }],
            span: span(1600, 1617),
            resolved_call: None,
            inferred_type: None,
        };
        assert_eq!(tc.infer_expr_for_test(&mut expr).unwrap(), Type::Int);
    }

    // spec: 03-types §3.5.3 — lambda returning Vec infers (Fn [Int] (Vec Int))
    #[test]
    fn test_infer_vec_lit_as_function_return() {
        let mut tc = tc();
        // (fn [x] [x]) -- returns Vec of the param type
        let mut expr = Expr::Lambda {
            params: vec![(Symbol::from("x"), Some(TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Int")))))],
            body: Box::new(Expr::VecLit {
                elements: vec![Expr::Var {
                    name: Symbol::from("x"),
                    span: span(1710, 1711),
                    inferred_type: None,
                }],
                span: span(1709, 1712),
                inferred_type: None,
            }),
            span: span(1700, 1713),
            inferred_type: None,
        };
        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(
            ty,
            Type::Fn(
                vec![Type::Int],
                Box::new(Type::ADT(prims_fqtn("Vec"), vec![Type::Int]))
            )
        );
    }

    // spec: 03-types §3.5.3 — single-element Vec literal infers element type
    #[test]
    fn test_infer_vec_lit_single_element() {
        let mut tc = tc();
        // [42]
        let mut expr = Expr::VecLit {
            elements: vec![Expr::IntLit { value: 42, span: span(1801, 1803), inferred_type: None, }],
            span: span(1800, 1804),
            inferred_type: None,
        };
        assert_eq!(
            tc.infer_expr_for_test(&mut expr).unwrap(),
            Type::ADT(prims_fqtn("Vec"), vec![Type::Int])
        );
    }

    // spec: 03-types §3.5.1 — Vec literal records type in expr_types map
    #[test]
    fn test_infer_vec_lit_expr_type_recorded() {
        let mut tc = tc();
        let s = span(1900, 1907);
        let mut expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 1, span: span(1901, 1902), inferred_type: None, },
                Expr::IntLit { value: 2, span: span(1903, 1904), inferred_type: None, },
            ],
            span: s,
            inferred_type: None,
        };
        tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(
            tc.state.expr_types.get(&s),
            Some(&Type::ADT(prims_fqtn("Vec"), vec![Type::Int]))
        );
    }

    // spec: 03-types §3.5.3 — Vec literal with Float elements infers (Vec Float)
    #[test]
    fn test_infer_vec_lit_floats() {
        let mut tc = tc();
        // [1.0 2.0 3.0]
        let mut expr = Expr::VecLit {
            elements: vec![
                Expr::FloatLit { value: 1.0, span: span(2001, 2004), inferred_type: None, },
                Expr::FloatLit { value: 2.0, span: span(2005, 2008), inferred_type: None, },
                Expr::FloatLit { value: 3.0, span: span(2009, 2012), inferred_type: None, },
            ],
            span: span(2000, 2013),
            inferred_type: None,
        };
        assert_eq!(
            tc.infer_expr_for_test(&mut expr).unwrap(),
            Type::ADT(prims_fqtn("Vec"), vec![Type::Float])
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
    fn register_constrained_fn(tc: &mut TestFixture) {
        use cranelisp_types::{ConstrainedFn, DefnVariant};

        let a_var = tc.fresh_var();
        let a_id = match &a_var { Type::Var(id) => *id, _ => unreachable!() };
        let fn_ty = Type::Fn(vec![a_var.clone(), a_var.clone()], Box::new(a_var));
        let scheme = Scheme {
            type_vars: vec![a_id],
            constraints: {
                let mut c = HashMap::new();
                c.insert(a_id, vec![cranelisp_types::FQTraitName::new(
                    cranelisp_types::ModuleFullPath::from("test"),
                    cranelisp_types::TraitName::from("Num"),
                )]);
                c
            },
            ty: fn_ty,
        };

        // Bind in scope so infer_var finds it
        tc.bind_local_self(Symbol::from("cfn"), scheme.clone());

        // Register in module so the constrained_fn check finds it
        tc.symbol_table_mut().insert(
            Symbol::from("cfn"),
            ModuleEntry::def(
                scheme.clone(),
                cranelisp_types::DefKind::UserFn {
                    constrained_fn: Some(Box::new(ConstrainedFn {
                        variant: DefnVariant {
                            params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                            body: Expr::IntLit { value: 0, span: Span::SYNTHETIC, inferred_type: None, },
                            span: Span::SYNTHETIC,
                        },
                        scheme: scheme.clone(),
                    })),
                },
            )
            .param_names(vec![Symbol::from("x"), Symbol::from("y")])
            .build(),
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
                type_vars: vec![],
                ty: Type::Fn(
                    vec![Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int))],
                    Box::new(Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int))),
                ),
                constraints: HashMap::new(),
            },
        );

        // (id cfn) — cfn is an argument, NOT in call position → should error
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("id"),
                span: span(3000, 3002),
                inferred_type: None,
            }),
            args: vec![Expr::Var {
                name: Symbol::from("cfn"),
                span: span(3003, 3006),
                inferred_type: None,
            }],
            span: span(2999, 3007),
            resolved_call: None,
            inferred_type: None,
        };

        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
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
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("cfn"),
                span: span(3100, 3103),
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit { value: 1, span: span(3104, 3105), inferred_type: None, },
                Expr::IntLit { value: 2, span: span(3106, 3107), inferred_type: None, },
            ],
            span: span(3099, 3108),
            resolved_call: None,
            inferred_type: None,
        };

        // Should succeed (constrained fn in call position is allowed)
        assert!(tc.infer_expr_for_test(&mut expr).is_ok());
    }

    // -----------------------------------------------------------------------
    // Trait constraint eagerness: trait methods with wrong types error at call site
    // -----------------------------------------------------------------------

    /// Set up Num trait with + method (impl for Int, Float only)
    /// and Ord trait with < method (impl for Int, Float only).
    fn register_num_and_ord_traits(tc: &mut TestFixture) {
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
                    (Symbol::from("lhs"), TypeExpr::TypeVar(Symbol::from("a"))),
                    (Symbol::from("rhs"), TypeExpr::TypeVar(Symbol::from("a"))),
                ],
                ret_type: TypeExpr::TypeVar(Symbol::from("a")),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        tc.register_trait_decl_self(&num_decl).unwrap();

        // impl Num for Int
        let int_impl = TraitImpl {
            trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Num")),
            target: cranelisp_types::TypeExpr::Named(
                cranelisp_types::TypeRef::new(None, TypeName::from("Int")),
            ),
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("+"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: Span::SYNTHETIC,
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: Span::SYNTHETIC, inferred_type: None, },
                            Expr::Var { name: Symbol::from("y"), span: Span::SYNTHETIC, inferred_type: None, },
                        ],
                        span: Span::SYNTHETIC,
                        resolved_call: None,
                        inferred_type: None,
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
            trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Num")),
            target: cranelisp_types::TypeExpr::Named(
                cranelisp_types::TypeRef::new(None, TypeName::from("Float")),
            ),
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("+"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-f64"),
                            span: Span::SYNTHETIC,
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: Span::SYNTHETIC, inferred_type: None, },
                            Expr::Var { name: Symbol::from("y"), span: Span::SYNTHETIC, inferred_type: None, },
                        ],
                        span: Span::SYNTHETIC,
                        resolved_call: None,
                        inferred_type: None,
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
                    (Symbol::from("lhs"), TypeExpr::TypeVar(Symbol::from("a"))),
                    (Symbol::from("rhs"), TypeExpr::TypeVar(Symbol::from("a"))),
                ],
                ret_type: TypeExpr::Named(cranelisp_types::TypeRef::new(None, TypeName::from("Bool"))),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        tc.register_trait_decl_self(&ord_decl).unwrap();

        // impl Ord for Int
        let int_ord_impl = TraitImpl {
            trait_name: cranelisp_types::TraitRef::new(None, TraitName::from("Ord")),
            target: cranelisp_types::TypeExpr::Named(
                cranelisp_types::TypeRef::new(None, TypeName::from("Int")),
            ),
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from("<"),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("lt-i64"),
                            span: Span::SYNTHETIC,
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var { name: Symbol::from("x"), span: Span::SYNTHETIC, inferred_type: None, },
                            Expr::Var { name: Symbol::from("y"), span: Span::SYNTHETIC, inferred_type: None, },
                        ],
                        span: Span::SYNTHETIC,
                        resolved_call: None,
                        inferred_type: None,
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
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("+"),
                span: span(4001, 4002),
                inferred_type: None,
            }),
            args: vec![
                Expr::BoolLit { value: true, span: span(4003, 4007), inferred_type: None, },
                Expr::BoolLit { value: true, span: span(4008, 4012), inferred_type: None, },
            ],
            span: span(4000, 4013),
            resolved_call: None,
            inferred_type: None,
        };

        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
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
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("+"),
                span: span(4101, 4102),
                inferred_type: None,
            }),
            args: vec![
                Expr::StringLit { value: "a".to_string(), span: span(4103, 4106), inferred_type: None, },
                Expr::StringLit { value: "b".to_string(), span: span(4107, 4110), inferred_type: None, },
            ],
            span: span(4100, 4111),
            resolved_call: None,
            inferred_type: None,
        };

        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
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
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("<"),
                span: span(4201, 4202),
                inferred_type: None,
            }),
            args: vec![
                Expr::BoolLit { value: true, span: span(4203, 4207), inferred_type: None, },
                Expr::BoolLit { value: false, span: span(4208, 4213), inferred_type: None, },
            ],
            span: span(4200, 4214),
            resolved_call: None,
            inferred_type: None,
        };

        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
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
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("<"),
                span: span(4301, 4302),
                inferred_type: None,
            }),
            args: vec![
                Expr::StringLit { value: "a".to_string(), span: span(4303, 4306), inferred_type: None, },
                Expr::StringLit { value: "b".to_string(), span: span(4307, 4310), inferred_type: None, },
            ],
            span: span(4300, 4311),
            resolved_call: None,
            inferred_type: None,
        };

        let err = tc.infer_expr_for_test(&mut expr).unwrap_err();
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
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("+"),
                span: span(4401, 4402),
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit { value: 1, span: span(4403, 4404), inferred_type: None, },
                Expr::BoolLit { value: true, span: span(4405, 4409), inferred_type: None, },
            ],
            span: span(4400, 4410),
            resolved_call: None,
            inferred_type: None,
        };

        // Should error: either unification fails (Int vs Bool) or constraint fails
        assert!(tc.infer_expr_for_test(&mut expr).is_err());
    }

    // spec: 07-traits §7.4.1 — (+ 1 2) succeeds: Int has Num impl
    #[test]
    fn test_trait_method_plus_int_succeeds() {
        let mut tc = tc();
        register_num_and_ord_traits(&mut tc);

        // (+ 1 2) -> Int
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("+"),
                span: span(4501, 4502),
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit { value: 1, span: span(4503, 4504), inferred_type: None, },
                Expr::IntLit { value: 2, span: span(4505, 4506), inferred_type: None, },
            ],
            span: span(4500, 4507),
            resolved_call: None,
            inferred_type: None,
        };

        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(ty, Type::Int);

        // Check resolution was recorded — FIXME 0185: primitive trait-method
        // resolution short-circuits to ResolvedCall::BuiltinFn instead of
        // TraitMethod, so backend can inline the primitive without paying the
        // impl-body call frame. (Num, +, Int) → add-i64.
        let resolution = tc.state.method_resolutions.resolved_calls.get(&span(4500, 4507)).unwrap();
        match resolution {
            ResolvedCall::BuiltinFn { name } => {
                assert_eq!(name.as_ref(), "add-i64");
            }
            _ => panic!("expected BuiltinFn resolution (primitive trait-method short-circuit per FIXME 0185), got {resolution:?}"),
        }
    }

    // spec: 07-traits §7.4.1 — (+ 1.0 2.0) succeeds: Float has Num impl
    #[test]
    fn test_trait_method_plus_float_succeeds() {
        let mut tc = tc();
        register_num_and_ord_traits(&mut tc);

        // (+ 1.0 2.0) -> Float
        let mut expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("+"),
                span: span(4601, 4602),
                inferred_type: None,
            }),
            args: vec![
                Expr::FloatLit { value: 1.0, span: span(4603, 4606), inferred_type: None, },
                Expr::FloatLit { value: 2.0, span: span(4607, 4610), inferred_type: None, },
            ],
            span: span(4600, 4611),
            resolved_call: None,
            inferred_type: None,
        };

        let ty = tc.infer_expr_for_test(&mut expr).unwrap();
        assert_eq!(ty, Type::Float);
    }
}
