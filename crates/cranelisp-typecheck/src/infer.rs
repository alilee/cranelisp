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
        let (scheme, gap) = self.lookup(state, name);
        // Record the in-band gap (if any) so a failed qualified-name resolution
        // surfaces as `CheckError::Gap` once the per-form dispatcher reports its
        // not-found error. Always write (Some or None) to match the prior
        // clear-on-attempt / set-on-miss side-slot semantics.
        state.pending_gap = gap;
        let scheme = scheme.ok_or_else(|| CranelispError::TypeError {
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
                // Chain-follow the qualified name to its terminal entry
                // (staging-aware, Principle 17), discarding the home module.
                if let Some((ModuleEntry::Def { kind, .. }, _home)) =
                    self.resolve_terminal_entry_and_home(&module_path, name_part)
                    // Per Decision 48: the symbol-table key IS the JIT linker
                    // name for primitives. Return the bare entry name.
                    && matches!(kind.as_ref(), DefKind::Primitive)
                {
                    return Some(Symbol::from(name_part));
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
        // Per-node action: try to resolve an as-yet-unresolved trait-method Apply.
        if let Expr::Apply { callee, args, span, .. } = expr
            && !state.method_resolutions.resolved_calls.contains_key(span)
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
        // Recurse into children via the shared enumeration helper.
        crate::program::for_each_child_expr(expr, |child| {
            self.resolve_deferred_trait_calls(state, child)
        });
    }

    /// Post-inference pass: resolve trait methods used in **value position**
    /// (spec §7.6 — trait methods are ordinary first-class values).
    ///
    /// Sibling of [`Self::resolve_deferred_trait_calls`], which handles the
    /// *call* position (a trait method as the callee of an `Apply`). This pass
    /// handles the complementary case: a trait method name appearing as a bare
    /// `Expr::Var` that is NOT the callee of an enclosing `Apply` — e.g. the
    /// binding in `(let [f =] (f "hi" "hi"))`, or a method passed to a HOF
    /// (`(apply2 + 1 2)`). In those positions the method escapes as a value;
    /// the backend must emit a zero-capture dispatch-wrapper closure, and
    /// (Decision 43) backend has no trait knowledge, so typecheck must record
    /// the concrete impl selection here.
    ///
    /// For each value-position `Var` whose resolved name is a trait method and
    /// whose final `inferred_type` is a function type, the method is resolved
    /// via [`Self::try_resolve_trait_method`] over the concrete parameter types
    /// read from that function type. The resulting `ResolvedCall`
    /// (`BuiltinFn { name }` for primitive-implemented methods, e.g. `eq-f64`/
    /// `str-eq`, or `TraitMethod { mangled_name }` otherwise) is recorded on the
    /// Var's span in the same `method_resolutions.resolved_calls` map the call
    /// path uses; `annotate_expr_from_maps` then overlays it onto
    /// `Expr::Var.resolved_call`.
    ///
    /// Ordinary fn / local Vars are left untouched (`is_trait_method_with_state`
    /// gates the predicate; a `let`-bound local or user fn is not a trait method
    /// declaration, so it never matches and keeps `resolved_call: None`).
    ///
    /// `in_callee_position` is `true` only for the `callee` child of an `Apply`
    /// — that child is the call path's responsibility and must be skipped here.
    pub(crate) fn resolve_value_position_trait_methods(
        &self,
        state: &mut CheckState,
        expr: &Expr,
        in_callee_position: bool,
    ) {
        // A bare Var in value position: try to resolve it as a trait method
        // used as a first-class value.
        if let Expr::Var { name, span, .. } = expr
            && !in_callee_position
            && !state.method_resolutions.resolved_calls.contains_key(span)
            && self.is_trait_method_with_state(state, name)
        {
            // The Var's final type must be a function type for it to be used
            // as a callable value. Read it from the side map and substitute.
            let var_ty = state
                .expr_types
                .get(span)
                .map(|t| self.apply_subst(state, t));
            if let Some(Type::Fn(params, _)) = var_ty {
                let resolved_params: Vec<Type> =
                    params.iter().map(|t| self.apply_subst(state, t)).collect();
                // Mirror the call-path resolution: trait-method impl selection
                // first, then a primitive-name fallback (the latter only fires
                // for genuinely primitive-named methods, which trait resolution
                // already covers — kept for symmetry with infer_apply).
                if let Ok(Some(resolution)) =
                    self.try_resolve_trait_method(state, name, &resolved_params, *span)
                {
                    state.method_resolutions.resolved_calls.insert(*span, resolution);
                }
            }
        }

        // Recurse. The `callee` child of an `Apply` is the call path's domain
        // (resolve_deferred_trait_calls / infer_apply) — flag it so this pass
        // does not also try to resolve it as a value.
        match expr {
            Expr::Apply { callee, args, .. } => {
                self.resolve_value_position_trait_methods(state, callee, true);
                for arg in args {
                    self.resolve_value_position_trait_methods(state, arg, false);
                }
            }
            other => crate::program::for_each_child_expr(other, |child| {
                self.resolve_value_position_trait_methods(state, child, false)
            }),
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
        &self, state: &mut CheckState,
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
        let (scheme, gap) = self.lookup(state, name);
        state.pending_gap = gap;
        scheme.ok_or_else(|| CranelispError::TypeError {
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
mod tests;
