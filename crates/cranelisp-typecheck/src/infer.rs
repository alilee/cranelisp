//! Expression type inference: one method per Expr variant.
//!
//! `infer_expr` dispatches to per-variant helpers. Each helper is typically
//! 10-40 lines, independently testable. Addresses audit HIGH-1 (monolithic infer_expr).

use cranelisp_types::{ErrorLocation,
    ApplyRef, CranelispError, Expr, JitSymbol, MatchArm, ModuleEntry, Pattern, ResolvedCall, Span,
    Symbol, Type, TypeExpr, VarRef,
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
            } => {
                let ty = self.infer_apply(state, callee, args, *span)?;
                // Apply-side totality (S114 carrier flip, design §2.2): EVERY
                // checked `Apply` records a typed dispatch verdict. A dispatch
                // seam inside `infer_apply` (trait-method / sig-dispatch /
                // builtin / auto-curry) already recorded `ApplyRef::Dispatch`;
                // stamp the POSITIVE `ApplyRef::ViaCallee` for every OTHER
                // checked Apply (the identity rides the callee expression).
                // `or_insert` never clobbers a Dispatch; a later-pass dispatch
                // selection (`record_dispatch_target` in mono_collect /
                // monomorphise / register) `insert`s and overwrites this
                // ViaCallee, so the final verdict is correct regardless of the
                // pass that resolves the dispatch.
                state
                    .method_resolutions
                    .apply_refs
                    .entry(*span)
                    .or_insert(ApplyRef::ViaCallee);
                Ok(ty)
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
                ..
            } => self.infer_annotate(state, annotation, expr, *span),

            Expr::StringLit { span, .. } => self.infer_string_lit(state, *span),
            Expr::VecLit { elements, span, .. } => self.infer_vec_lit(state, elements, *span),
            Expr::Trace { body, span, .. } => self.infer_trace(state, body, *span),
            Expr::ParBind {
                bindings,
                body,
                span,
                ..
            } => self.infer_par_bind(state, bindings, body, *span),
            Expr::LaunchContinue {
                launched,
                continuation,
                span,
                ..
            } => self.infer_launch_continue(state, launched, continuation, *span),
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
        // Look up the ctor's scheme via its `Def` in the type's defining module,
        // recording the STORAGE key that HIT as the sidecar identity (§10.1).
        // **S109 dotted-ctor keying.** `TypeDefInfo.constructors` carries the bare
        // display name, but a sum ctor's real got-slotted `Def` now lives under
        // the canonical `member_key(Type, Ctor)` key (`Maybe.Some`) — the bare key
        // is a poison-able `Import` alias (or `Ambiguous` under contest). Probe the
        // canonical key first, falling back to the bare key for the product
        // dual-facet (kept at the type-name key) and for hand-seeded internal ctors
        // (`Bind`) that retain their bare storage key. The returned `FQSymbol.symbol`
        // is whichever key resolved — the backend reads its `Def` by DIRECT keyed
        // lookup, never re-resolving the bare name context-free (§10.3, DC-11 cure).
        let canonical = cranelisp_types::member_key(&type_name.name, ctor_sym.as_ref());
        let (storage_key, scheme) = self
            .probe_module_entry_owned(&type_name.module, canonical.as_ref())
            .and_then(|e| match e {
                cranelisp_types::ModuleEntry::Def { scheme, .. } => {
                    Some((canonical.clone(), scheme.clone()))
                }
                _ => None,
            })
            .or_else(|| {
                self.probe_module_entry_owned(&type_name.module, ctor_sym.as_ref())
                    .and_then(|e| match e {
                        cranelisp_types::ModuleEntry::Def { scheme, .. } => {
                            Some((ctor_sym.clone(), scheme.clone()))
                        }
                        _ => None,
                    })
            })
            .ok_or_else(|| CranelispError::TypeError {
                message: format!(
                    "constructor {}.{ctor_sym} has no scheme",
                    type_name.name
                ),
                location: ErrorLocation::from_span(span),
            })?;
        let fq_ctor = cranelisp_types::FQSymbol {
            module: type_name.module.clone(),
            symbol: storage_key,
        };
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
        // S113 0655 (user ruling (a)) — spelling normalization at the ONE Var
        // entry: a reference qualified with the CURRENT module (after §8.6.6
        // alias substitution) IS the bare local. Normalize BEFORE the env
        // consult so every read below (scheme lookup, the value/undefined
        // diagnostics, the dotted/carrier recorders, and — via
        // `record_reference_target`'s env consult — the §4.6 shadow + §11.8.7
        // recursion-self carve-out) observes the bare shape. See
        // `TypeCheckEnv::normalize_self_qualified`.
        let name: &str = self.normalize_self_qualified(state, name.as_ref());
        let (scheme, gap) = self.lookup(state, name);
        // Record the in-band gap (if any) so a failed qualified-name resolution
        // surfaces as `CheckError::Gap` once the per-form dispatcher reports its
        // not-found error. Always write (Some or None) to match the prior
        // clear-on-attempt / set-on-miss side-slot semantics.
        state.pending_gap = gap;
        // A bare name that resolves to a poisoned (ambiguous) symbol-table entry
        // is a compile-time error listing the qualified alternatives (spec
        // §8.6.5; for field accessors §5.2.6). The `Ambiguous` sentinel yields
        // no scheme, so without this check it would mis-report as "undefined
        // variable". Cross-type duplicate field-name accessors record their
        // owning types in `accessor_owning_types`; surface them as `Type.member`
        // alternatives.
        if scheme.is_none()
            && matches!(
                self.resolve_entry_scoped(state, name),
                Some(ModuleEntry::Ambiguous { .. })
            )
        {
            // Same-cluster (`--run`): the owners were recorded on `CheckState`
            // as each accessor was synthesised in this `check_forms` call.
            // Cross-cluster (the REPL drives each form as its own cluster with a
            // FRESH `CheckState`), the map is empty by the time the bare use is
            // checked — the poisoning `deftype`s ran in now-discarded prior
            // clusters. Re-derive the owners structurally from the durable symbol
            // table so BOTH paths list the canonical alternatives (§5.2.6 gives
            // the REPL no exemption).
            let owners: Vec<cranelisp_types::FQTypeName> = match state.accessor_owning_types.get(name)
            {
                Some(tys) if !tys.is_empty() => tys.clone(),
                _ => self.reconstruct_accessor_alternatives(state, name),
            };
            let hint = if owners.is_empty() {
                String::new()
            } else {
                let alts: Vec<String> = owners
                    .iter()
                    .map(|t| cranelisp_types::member_key(&t.name, name).as_ref().to_string())
                    .collect();
                format!(" — use a qualified member ({})", alts.join(" or "))
            };
            return Err(CranelispError::TypeError {
                message: format!("ambiguous bare name '{name}'{hint}"),
                location: ErrorLocation::from_span(span),
            });
        }
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
            if let Some(ModuleEntry::SpecialForm { .. }) = v.lookup(&Symbol::from(name)) {
                return Err(CranelispError::TypeError {
                    message: format!("{name} is a special form, not a value"),
                    location: ErrorLocation::from_span(span),
                });
            }
        }

        // Reject internal constructors (e.g. Bind) — they cannot be
        // constructed by user code, only by compiler-generated primitives.
        if self.is_internal_constructor(state, &Symbol::from(name)) {
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
        //
        // PS-SH1 / §11.8.7 Ruling 5 (value-position mirror) — LOCAL-SCOPE-FIRST.
        // A `let`/`fn`/param binding that lexically shadows a constrained/overload
        // base is a §4.6 LOCAL — resolving it here to the module base and rejecting
        // it as "cannot be used as a value" wrong-rejects the local (a plain closure
        // value). Consult local scope BEFORE the base reject: enter the reject only
        // when `name` is NOT locally bound at all, OR it is the genuine recursion
        // self-reference (whose recursion binding IS a local at `current_defn_frame`
        // but genuinely refers to the multi-sig/constrained base — still not a value).
        // This mirrors the call-gate discriminator (`infer_apply`, Ruling 5) to the
        // value-position gates. A shadowed name falls through to ordinary local
        // inference (the closure's own scheme — indirect value, no carrier).
        if !state.in_call_position
            && state.resolves_to_carrier_identity(name)
            && let Some(entry) = self.resolve_entry_scoped(state, name)
            && let ModuleEntry::Def { kind, .. } = entry
            && matches!(
                kind.as_ref(),
                cranelisp_types::DefKind::UserFn {
                    fn_state: cranelisp_types::UserFnState::Constrained(_)
                }
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
        //
        // PS-SH1 / §11.8.7 Ruling 5 (value-position mirror) — LOCAL-SCOPE-FIRST
        // (see the constrained-value gate above). A `let`-shadowed multi-sig base
        // (`(defn g [] (let [h (fn [y] 100)] (use-hof h)))`, `h` a base) used in
        // value position (HOF arg / returned / container-stored) MUST resolve to the
        // LOCAL closure, never wrong-reject as "multi-sig cannot be used as a value".
        if !state.in_call_position
            && state.resolves_to_carrier_identity(name)
            && let Some(entry) = self.resolve_entry_scoped(state, name)
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

        // Reference-recording feeds, placed after every rejection gate above so
        // only a successfully-typed reference records. ONE resolution serves
        // both (Principle 24 — the "Resolve once" consolidation, FIXME 0616):
        //  - S110 0583 → S114 `var_refs` (was `resolved_targets`) — the total,
        //    typed backend keyed-consumer carrier: `VarRef::Global(storage_fq)`
        //    for a table reference, `VarRef::Local` for a §4.6 local (absence is
        //    now unrepresentable — the totality flip);
        //  - S101 `Def.callees` — a `UserFn`-filtered projection of the same
        //    resolution.
        // A dotted `Type.member` form (`Maybe.Some`) resolved through the dotted
        // core, not `scope_resolve`, so record its canonical member FQ directly
        // (leg 3, carrier only — dotted refs are `callees` residue); every other
        // name goes through the shared bare/qualified recorder (which also owns
        // the local-shadow gate + the self-recursion carve-out, leg 2).
        if let Some(fq) = self.resolve_dotted_member_fq(state, name) {
            // A dotted `Type.member` reference is a table reference — its typed
            // verdict is `VarRef::Global` with the canonical member storage FQ.
            state
                .method_resolutions
                .var_refs
                .insert(span, VarRef::Global(fq));
        } else {
            self.record_reference_target(state, name, span);
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
        // Binder provenance: the `let` node span is the binding-form span every
        // `let`-bound name shares (S114 `VarRef::Local`).
        self.push_scope(state, span);

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

    /// Typing rule for `Expr::ParBind` (spec/10-io.md §10.12 transparency).
    ///
    /// A `ParBind` is produced by auto-IO scheduling (FIXME 0367) from a monadic
    /// `bind` chain over data-independent, non-`Sequential` effects. It is NOT a
    /// plain `Let`: each binding value `vᵢ` is an `IO aᵢ` action, and the bound
    /// name must be `aᵢ` (the UNWRAPPED inner type) — exactly as the sequential
    /// `(bind (IO a) (fn [name] ...))` form binds `name : a` through `bind`'s
    /// `(IO a) -> (a -> IO b) -> IO b` scheme. The body is itself an `IO U`
    /// action and the whole `ParBind` types as `IO U`. Routing through
    /// `infer_let` (which would bind `name : IO a`) is wrong — see FIXME 0400.
    ///
    /// Because this mirrors the sequential bind chain's typing exactly, the
    /// §10.12 transparency invariant holds: a chain types identically whether or
    /// not auto-scheduling grouped it into a `ParBind`.
    fn infer_par_bind(
        &self, state: &mut CheckState,
        bindings: &[(Symbol, Expr)],
        body: &Expr,
        span: Span,
    ) -> Result<Type, CranelispError> {
        // Binder provenance: the `ParBind` node span (S114 `VarRef::Local`).
        self.push_scope(state, span);

        for (name, binding_expr) in bindings {
            // Each binding value is an `IO aᵢ` action. Unify against `IO ?aᵢ`
            // to unwrap the `IO` constructor — the same unification the
            // sequential `bind` primitive performs via its scheme — and bind the
            // name to the inner type `aᵢ` (monomorphic, spec §3.5.3).
            let binding_ty = self.infer_expr(state, binding_expr)?;
            let inner_ty = self.fresh_var();
            let io_inner = Self::io_type(inner_ty.clone());
            self.unify(state, &binding_ty, &io_inner, binding_expr.span())?;
            let resolved_inner = self.apply_subst(state, &inner_ty);
            self.bind_local(state, name.clone(), mono(resolved_inner));
        }

        // The body is itself an `IO U` action; the ParBind result is that `IO U`.
        let body_ty = self.infer_expr(state, body)?;
        let result_inner = self.fresh_var();
        let io_result = Self::io_type(result_inner);
        self.unify(state, &body_ty, &io_result, body.span())?;
        self.pop_scope(state);

        let resolved = self.apply_subst(state, &io_result);
        self.record_expr_type(state, span, resolved.clone());
        Ok(resolved)
    }

    /// Typing rule for `Expr::LaunchContinue` (spec §10.12.7 — launch-and-continue).
    ///
    /// Semantically a sequential `Bind(launched, λ_. continuation)` for type
    /// purposes (`ast.rs` rustdoc): `launched` is an effect whose result is
    /// **discarded**, and `continuation` produces this node's value. So this
    /// types EXACTLY like a sequential bind step whose binder is unused —
    /// preserving the §10.12 transparency invariant (a chain types identically
    /// whether or not the analysis marked the step launch-eligible).
    ///
    /// - `launched` must be a real effect `IO a` (it still typechecks — it runs
    ///   as a detached strand). Its inner type `a` is discarded (no name binds
    ///   it; the continuation cannot reference it).
    /// - `continuation` is itself an `IO U` action; its type IS this node's type.
    fn infer_launch_continue(
        &self, state: &mut CheckState,
        launched: &Expr,
        continuation: &Expr,
        span: Span,
    ) -> Result<Type, CranelispError> {
        // The launched effect must be an `IO a` action; unify against `IO ?a` to
        // assert it (the same unwrap the sequential `bind` performs), then DISCARD
        // the inner type — no name binds it, the continuation cannot await it.
        let launched_ty = self.infer_expr(state, launched)?;
        let launched_inner = self.fresh_var();
        let io_launched = Self::io_type(launched_inner);
        self.unify(state, &launched_ty, &io_launched, launched.span())?;

        // The continuation is itself an `IO U` action; its type is this node's type.
        let cont_ty = self.infer_expr(state, continuation)?;
        let result_inner = self.fresh_var();
        let io_result = Self::io_type(result_inner);
        self.unify(state, &cont_ty, &io_result, continuation.span())?;

        let resolved = self.apply_subst(state, &io_result);
        self.record_expr_type(state, span, resolved.clone());
        Ok(resolved)
    }

    /// Construct the `primitives/IO` ADT applied to one inner type argument.
    fn io_type(inner: Type) -> Type {
        Type::ADT(
            cranelisp_types::FQTypeName::new(
                cranelisp_types::ModuleFullPath::from("primitives"),
                cranelisp_types::TypeName::from("IO"),
            ),
            vec![inner],
        )
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
        // Binder provenance: the lambda node span every param shares (S114
        // `VarRef::Local` — per-param spans do not exist on the AST).
        self.push_scope(state, span);

        // SHARE the enclosing definition's written-var scope (spec §3.3.1
        // co-reference [S109 W6.3]): a nested `fn`'s `:a` CO-REFERS to the
        // enclosing `a`, never a fresh shadow (the 0588 seam). A standalone
        // lambda (no enclosing scope) gets a fresh one via `unwrap_or_default`. A
        // lambda's OWN fresh param vars are FLEXIBLE — a lambda is NOT a
        // generalization boundary in rank-1; its written var is quantified at the
        // enclosing definition and instantiated at application, so leaving it
        // flexible is the faithful realization (`((fn [:a x] x) 3)` → 3). No
        // bare-path id is ever rigid: rigidity lives on the constraint path, so
        // the minted ids from THIS call are never added to `state.rigid_vars`.
        //
        // A nested `fn` that DEFINES a rank-1 polymorphic function value — whether
        // returned, let-stored, or applied in place — is a legitimate syntactic
        // value (spec §3.3.4 / §3.10, W6.3 ruling): `(defn mk [] (fn [:b y] y))`
        // and `(defn mkid [] (fn [y] y))` are the SAME thing (the written `:b` is
        // irrelevant). The genuine rank-2 / multi-type-use restrictions are enforced
        // ELSEWHERE (value restriction + unification), not by an eager escape check
        // here.
        let mut var_map = state.written_var_scope.take().unwrap_or_default();
        // Resolve the param annotations (extending the shared `var_map`) in a
        // fallible closure so the shared scope is re-installed and the pushed env
        // frame is popped on EVERY exit (Principle 18, FIXME 0595 item 2). The
        // pre-existing `?` exits (annotation-resolution / body-inference errors)
        // skipped `pop_scope` — leaking the frame — and left `written_var_scope`
        // as `None` on the annotation-error path. Benign today (a Pass-2 error
        // aborts the whole `check_forms` call and the enclosing `check_defn_body`
        // restores its own saved scope), but the asymmetry is a trap for any
        // future continue-after-form-error mode, so it is made structural here.
        let param_result = (|| -> Result<Vec<Type>, CranelispError> {
            let mut param_types = Vec::new();
            for (param_name, annotation) in params.iter() {
                let param_ty = if let Some(annotation) = annotation {
                    self.resolve_annotation_type_expr_in_module(
                        annotation, &mut var_map, &state.current_module, span,
                    )?
                } else {
                    self.fresh_var()
                };
                param_types.push(param_ty.clone());
                self.bind_local(state, param_name.clone(), mono(param_ty));
            }
            Ok(param_types)
        })();
        // Re-install the shared (param-extended) scope on EVERY path BEFORE the
        // body is inferred, so a nested annotation / lambda co-refers through the
        // same scope — and so it is never left `None` on the error path.
        state.written_var_scope = Some(var_map);

        let result = param_result.and_then(|param_types| {
            let body_ty = self.infer_expr(state, body)?;
            let fn_type = Type::Fn(
                param_types
                    .iter()
                    .map(|t| self.apply_subst(state, t))
                    .collect(),
                Box::new(self.apply_subst(state, &body_ty)),
            );
            self.record_expr_type(state, span, fn_type.clone());
            Ok(fn_type)
        });
        // Symmetric env-frame teardown — pop the frame pushed above on both the
        // Ok and Err paths (the 0595-item-2 hardening).
        self.pop_scope(state);
        result
    }

    /// MC-X2 — lazily register an IMPORTED multi-sig base into the overload
    /// machinery. The `overloads`/`resolved_overloads` tables are populated for
    /// LOCALLY-defined bases (Pass-1 registration + the `form.rs` rehydration of
    /// the current module's `Overloaded` entries); an imported base (`(import
    /// [mlib [h]])`) is a `ModuleEntry::Import` chain-following to an `Overloaded`
    /// entry in its HOME module, invisible to those tables. Chain-follow `name`;
    /// if it terminates at an `Overloaded` entry in a DIFFERENT module, mirror the
    /// local rehydration (`form.rs`) AND record the base's HOME in `overload_homes`
    /// so the drain keys the dispatch carrier by the base's storage identity
    /// (P24), not the caller's module. Idempotent (guards on `contains_key`).
    ///
    /// A base referenced BOTH bare (`h`, after import) and qualified (`mlib/h`)
    /// double-keys `overload_homes` under both names — harmless: each key maps to
    /// the same home, and Fix A mangles the concrete identity from the BARE base
    /// name, so both references dispatch to the same `mlib`-keyed `h$Int`.
    fn maybe_rehydrate_imported_overload_base(
        &self,
        state: &mut CheckState,
        name: &Symbol,
    ) {
        if state.overloads.contains_key(name) {
            return;
        }
        let Some((entry, home)) = self.resolve_terminal_entry_scoped(state, name.as_ref()) else {
            return;
        };
        if home == state.current_module {
            return; // local base — the ordinary registration path owns it
        }
        if let ModuleEntry::Def { kind, .. } = &entry
            && let cranelisp_types::DefKind::Overloaded { variants } = kind.as_ref()
            && !variants.is_empty()
        {
            let overload_keys: Vec<(Symbol, usize)> = variants
                .iter()
                .map(|v| (v.mangled_name.clone(), v.param_types.len()))
                .collect();
            let resolved: Vec<(Vec<Type>, Type, Symbol)> = variants
                .iter()
                .map(|v| (v.param_types.clone(), v.ret_type.clone(), v.mangled_name.clone()))
                .collect();
            state.overloads.insert(name.clone(), overload_keys);
            state.resolved_overloads.insert(name.clone(), resolved);
            state.overload_homes.insert(name.clone(), home);
        }
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

        // MC-X5 — SPELLING NORMALIZATION at the overload gate. The gate below keys
        // dispatch on the callee's RAW AST name, but a current-module-qualified
        // self-call (`(user/msig …)` inside module `user`) IS the bare local
        // (§8.6.6 / 0655 — the same normalization `infer_var` applies at its Var
        // entry). Without it, `state.overloads.contains_key("user/msig")` misses
        // (the table is keyed bare) so the qualified multi-sig self-call skips the
        // dispatch path and wrong-rejects. Normalize ONCE here so every downstream
        // read in the overload block (the `overloads`/`resolved_overloads` lookups,
        // the rehydration gate, the recursion-self discriminator, the deferred
        // pending's base key, the dispatch mangle) observes the bare identity. A
        // non-self qualifier (`mlib/h`) and a bare name are returned unchanged, so
        // the imported-base (MC-X2) and ordinary paths are untouched.
        let normalized_callee: Option<Symbol> = match callee {
            Expr::Var { name, .. } => {
                Some(Symbol::from(self.normalize_self_qualified(state, name.as_ref())))
            }
            _ => None,
        };

        // Multi-sig overload dispatch: if the callee is a Var whose name is
        // in the overloads table, defer resolution to the overload pass.
        // We don't unify here because the base name's scheme may not match
        // the actual call site arity/types.
        //
        // MC-X2 (W2-close) — an IMPORTED multi-sig base is NOT in `state.overloads`
        // (that table holds LOCALLY-defined bases). Lazily rehydrate it from its
        // chain-followed `Overloaded` home entry so the SAME overload machinery
        // (gate → drain → carrier) dispatches it, keyed by its HOME module (P24).
        // Only for a not-locally-shadowed Var callee that is not already an overload.
        if let Some(name) = normalized_callee.as_ref()
            && !state.overloads.contains_key(name)
            && state.env.lookup(name.as_ref()).is_none()
        {
            self.maybe_rehydrate_imported_overload_base(state, name);
        }

        // §11.8.7 ruling 5 — LOCAL-SCOPE-FIRST guard. A `let`/`fn`/param binding
        // that lexically shadows a multi-sig base (`(defn t1 [x] (let [m1 (fn [y]
        // y)] (m1 x)))`, `m1` a base) MUST resolve to the LOCAL binding (spec §4.6
        // / §5.1.2), never the global overload table. Enter the overload path
        // ONLY when `name` is NOT locally bound at all, OR it is the genuine
        // recursion self-reference (the §5.1.2 back-flow self-call, whose
        // recursion binding IS a local at `current_defn_frame`). This is the
        // composition contract with the R1 leg: during a mono recheck the
        // self-call's base is not locally bound (`recheck_body_for_mono` binds
        // only the instance mangle), so the guard admits R1's inline path
        // unchanged — the guard is a strict pre-filter that never fires on R1's or
        // a genuine self-call's inputs. A shadowed call falls through to ordinary
        // local inference (indirect call, no carrier — no schema bump).
        if let Some(name) = normalized_callee.as_ref()
            && state.overloads.contains_key(name)
            && state.resolves_to_carrier_identity(name.as_ref())
        {
            // I1 fix (§11.3.1 caveat (b)): during a multi-sig template clause's
            // mono recheck, an inner self-call to the overloaded base (`(g x)`
            // inside `g`'s genuinely-poly clause) is monomorphic recursion to THIS
            // instance. The textual `current_defn` tag classifies it as *external*
            // (current_defn is the template mangle `g$Var`, not `g`/`g__vN`), so
            // absent this it would defer a pending entry the sole drain has already
            // taken — never resolved, leaving a residual var that wrong-rejects with
            // the internal `g$Var$Int` mangle leaking into the diagnostic. When the
            // recheck ctx names this base and the call's args EQUAL the instance's
            // concrete params (same arity + same instantiation), resolve inline:
            // unify + dispatch to the instance mangle, exactly as the standalone
            // twin's self-call resolves. A call at DIFFERENT args (a distinct
            // instance / sibling clause) falls through to the ordinary defer.
            if state
                .mono_recheck_self
                .as_ref()
                .is_some_and(|(base, _, ip, _)| base == name && ip.len() == arg_types.len())
            {
                let (instance, inst_params, inst_ret) = {
                    let (_, instance, ip, ir) = state.mono_recheck_self.as_ref().unwrap();
                    (instance.clone(), ip.clone(), ir.clone())
                };
                let resolved_args: Vec<Type> =
                    arg_types.iter().map(|a| self.apply_subst(state, a)).collect();
                if inst_params.iter().zip(resolved_args.iter()).all(|(p, a)| p == a) {
                    for (p, a) in inst_params.iter().zip(arg_types.iter()) {
                        self.unify(state, p, a, span)?;
                    }
                    self.unify(state, &inst_ret, &ret_ty, span)?;
                    let resolution = ResolvedCall::SigDispatch { mangled_name: instance };
                    self.record_dispatch_target(state, span, &resolution);
                    state.method_resolutions.resolved_calls.insert(span, resolution);
                    for (arg, arg_ty) in args.iter().zip(arg_types.iter()) {
                        self.record_expr_type(state, arg.span(), self.apply_subst(state, arg_ty));
                    }
                    // The callee (the overloaded base `Var`) is typed to the
                    // instance's concrete signature — the mono codegen view
                    // (`from_expr`, hard-error) requires every node concrete, and an
                    // overloaded base otherwise carries the polymorphic union type.
                    self.record_expr_type(
                        state,
                        callee.span(),
                        Type::Fn(inst_params.clone(), Box::new(inst_ret.clone())),
                    );
                    self.record_expr_type(state, span, self.apply_subst(state, &ret_ty));
                    return Ok(ret_ty);
                }
            }

            // §11.8.3 leg R1 — a CROSS-ARITY (or distinct-args) sibling self-call
            // from a genuinely-poly template clause's mono recheck. The
            // same-instantiation gate above fires only for THIS instance's exact
            // arity+args; a sibling at a different arity (`(g2 1 2)` from the 1-arg
            // clause's recheck) skips it, and pre-R1 re-deferred a pending entry the
            // sole drain has already taken → orphan → wrong-reject with the internal
            // `$Var$Int` mangle leaking. Widen the inline match set from "this
            // instance" to "the base's SETTLED overload clauses" (§11.3.4 recorded
            // direction): select the sibling by arity+args from `resolved_overloads`
            // and dispatch to its concrete mangle — a concrete clause directly, a
            // `$Var` template clause via `monomorphise_call` at the concrete args —
            // exactly as the standalone twin's ordinary call would. The inline path
            // (not a post-body scan) is required so the callee node is retyped
            // concrete for `from_expr`.
            if let Some(base) = state.mono_recheck_self.as_ref().map(|(b, ..)| b.clone())
                && base == *name
            {
                let resolved_args: Vec<Type> =
                    arg_types.iter().map(|a| self.apply_subst(state, a)).collect();
                if resolved_args.iter().all(Type::is_concrete)
                    && let Some(variants) = state.resolved_overloads.get(name).cloned()
                    && let crate::program::OverloadSelection::Unique((cparams, cret, cmangled)) =
                        crate::program::select_unique_overload_variant(&variants, &resolved_args)
                {
                    let clause_params = cparams.clone();
                    let clause_mangled = cmangled.clone();
                    let clause_ret = cret.clone();
                    // Resolve the selected sibling clause to a CONCRETE dispatch
                    // target + its concrete signature.
                    let (dispatch_name, inst_params, inst_ret) =
                        if clause_params.iter().all(Type::is_concrete) {
                            // Concrete sibling clause — dispatch to its mangle.
                            (
                                JitSymbol::from(clause_mangled.as_ref()),
                                clause_params.clone(),
                                self.apply_subst(state, &clause_ret),
                            )
                        } else {
                            // `$Var` template sibling (constrained / genuinely-poly)
                            // — monomorphise at the concrete args and dispatch to the
                            // minted instance. `origin_base = Some(name)` so a nested
                            // self-call inside it resolves as monomorphic recursion.
                            let mono = self.monomorphise_call(
                                state, &clause_mangled, &resolved_args, span, None, Some(name),
                            )?;
                            let instance = match &mono {
                                Some(md) => md.defn.name.clone(),
                                None => clause_mangled.clone(),
                            };
                            let cm = state.current_module.clone();
                            let inst_ret = self
                                .probe_module_entry_owned(&cm, instance.as_ref())
                                .and_then(|e| match e {
                                    ModuleEntry::Def { scheme, .. } => match &scheme.ty {
                                        Type::Fn(_, r) => Some((**r).clone()),
                                        _ => None,
                                    },
                                    _ => None,
                                })
                                .unwrap_or_else(|| self.apply_subst(state, &clause_ret));
                            (JitSymbol::from(instance.as_ref()), resolved_args.clone(), inst_ret)
                        };
                    for (p, a) in inst_params.iter().zip(arg_types.iter()) {
                        self.unify(state, p, a, span)?;
                    }
                    self.unify(state, &inst_ret, &ret_ty, span)?;
                    let resolution = ResolvedCall::SigDispatch { mangled_name: dispatch_name };
                    self.record_dispatch_target(state, span, &resolution);
                    state.method_resolutions.resolved_calls.insert(span, resolution);
                    for (arg, arg_ty) in args.iter().zip(arg_types.iter()) {
                        self.record_expr_type(state, arg.span(), self.apply_subst(state, arg_ty));
                    }
                    // Retype the callee (the overloaded base `Var`) to the sibling
                    // clause's concrete signature — `from_expr` requires every node
                    // concrete, and the base otherwise carries the polymorphic union.
                    self.record_expr_type(
                        state,
                        callee.span(),
                        Type::Fn(inst_params.clone(), Box::new(inst_ret.clone())),
                    );
                    self.record_expr_type(state, span, self.apply_subst(state, &ret_ty));
                    return Ok(ret_ty);
                }
            }

            // §5.1.2 self-call tag: a call to overloaded base `name` from inside
            // one of `name`'s OWN clause bodies (the current defn is `name` or a
            // `name__vN` clause) is a monomorphic-recursion sibling self-call — the
            // drain unifies it (back-flow), not monomorphises it.
            let is_self_call = state
                .current_defn
                .as_ref()
                .map(|d| {
                    let d = d.as_ref();
                    d == name.as_ref() || d.starts_with(&format!("{}__v", name))
                })
                .unwrap_or(false);
            state.pending_overload_resolutions.push((
                span,
                name.clone(),
                arg_types.clone(),
                ret_ty.clone(),
                is_self_call,
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
                // §11.8.8 (Important-1) — the auto-curry filler is the untested
                // SIBLING of the post-unify resolver below: it too keyed the raw
                // AST name, so a shadowing local passed as a curried HOF value
                // (`(let [+ (fn [a b] 0)] (map + xs))`) would fill in the
                // trait/primitive carrier over the local closure. Gate on the same
                // Ruling-5 carrier discriminator + `normalized_callee` (Minor-1).
                if let Some(name) = normalized_callee.as_ref()
                    && state.resolves_to_carrier_identity(name.as_ref())
                {
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
                            Ok(None) => self.resolve_primitive_jit_name(state, name.as_ref())
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
        // §11.8.8 (W3-review Important-1) — key on the CARRIER identity, NOT the
        // raw AST name: a `let`/`fn`/param binding that SHADOWS a trait method or
        // primitive (`(let [+ (fn [a b] 0)] (+ 1 2))`) MUST call the local closure
        // (returns 0), never the global `Num.+` dispatch (mis-dispatch → 3, spec
        // §4.6 violation). `resolves_to_carrier_identity` is the shared Ruling-5
        // discriminator (checker.rs, the same gate the value-position + overload
        // paths consult); a shadowed name skips resolution and rides its own local
        // scheme (indirect call, no dispatch carrier). Minor-1: read
        // `normalized_callee` so a self-qualified spelling (`(user/+ …)` inside
        // module `user`) folds to the bare carrier identity like `infer_var`.
        if let Some(name) = normalized_callee.as_ref()
            && state.resolves_to_carrier_identity(name.as_ref())
        {
            let resolved_args: Vec<Type> = arg_types
                .iter()
                .map(|t| self.apply_subst(state, t))
                .collect();

            if let Some(resolution) =
                self.try_resolve_trait_method(state, name, &resolved_args, span)?
            {
                // Trait method resolution (Ring 2): operators like +, -, =, <
                // S110 0583 leg 1: record the dispatch-leg carrier at the Apply
                // span alongside the `resolved_calls` insert (FIXME 0616).
                self.record_dispatch_target(state, span, &resolution);
                state.method_resolutions.resolved_calls.insert(span, resolution);
            } else if let Some(jit_name) = self.resolve_primitive_jit_name(state, name.as_ref()) {
                // Named primitive resolution (Ring 0-3): add-i64, str-concat,
                // macros/sconcat, quote-sexp, etc.
                let resolution = ResolvedCall::BuiltinFn { name: jit_name };
                self.record_dispatch_target(state, span, &resolution);
                state.method_resolutions.resolved_calls.insert(span, resolution);
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
            Expr::Var { name, .. } => {
                // ADT constructors do NOT auto-curry: an under-applied
                // constructor is an arity error (spec §5.2.7). With the S79
                // product-ctor dual facet a single-ctor product is an ordinary
                // got-slotted ctor `Def` whose function-type scheme is curry-
                // shaped, so it would otherwise fall through to the generic
                // curry path here; reject it with a clear arity diagnostic.
                if let Some(cranelisp_types::ModuleEntry::Def { kind, .. }) =
                    self.resolve_constructor_entry(state, name.as_ref())
                    && let cranelisp_types::DefKind::Constructor { field_count, .. } =
                        kind.as_ref()
                {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "constructor {name} expects {field_count} argument{} but got {}",
                            if *field_count == 1 { "" } else { "s" },
                            arg_types.len(),
                        ),
                        location: ErrorLocation::from_span(span),
                    });
                }
                name.clone()
            }
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
        // Capture the callee `Var` span so the drain (`resolve_auto_curry`) can
        // transport its already-recorded storage carrier for a plain-fn curry
        // (S110 W0.1b, §1.1.1). `callee` is a `Var` here (the `callee_name`
        // match above errors on any non-`Var` callee).
        let callee_var_span = match callee {
            Expr::Var { span, .. } => Some(*span),
            _ => None,
        };
        state.pending_auto_curry.push((
            span,
            callee_name,
            arg_types.len(),
            params.len(),
            callee_ty.clone(),
            None,
            callee_var_span,
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
                    //
                    // FIXME 0360 (ruled S83 /arch, Path 1): `PrimitiveExtern`
                    // is the slot-less, by-name-dispatched (`Linkage::Import`)
                    // sibling of `Primitive` — `sconcat`, `quote-sexp`, `bind`,
                    // the trace field accessors. It must ALSO classify as
                    // `BuiltinFn`; the backend's builtin-dispatch funnel is
                    // slot-agnostic (handles both GOT-indirect and by-name).
                    // Omitting it silently drops these callees from lowering.
                    && matches!(
                        kind.as_ref(),
                        DefKind::Primitive { .. } | DefKind::PrimitiveExtern
                    )
                {
                    return Some(Symbol::from(name_part));
                }
            }
            return None;
        }

        // Unqualified name: resolve in current module (returns owned entry)
        let entry = self.resolve_entry_scoped(state, name)?;
        if let ModuleEntry::Def { kind, .. } = &entry {
            // Per Decision 48: the symbol-table key IS the JIT linker name for
            // primitives. Return the bare entry name.
            //
            // FIXME 0360 (ruled S83 /arch, Path 1): `PrimitiveExtern` callees
            // (slot-less, by-name `Linkage::Import` dispatch) must classify as
            // `BuiltinFn` too — see the qualified-arm comment above.
            if matches!(kind.as_ref(), DefKind::Primitive { .. } | DefKind::PrimitiveExtern) {
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
    ///
    /// **F-D2-10 (FIXME 0672) — the settlement re-attempt propagates the no-impl
    /// error (S114).** A NULLARY return-type-dispatched method (`(zed)` with
    /// `Self` in return position) defers at `infer_apply` because its return type
    /// is still a `Var` until a later annotation (`:Widget (zed)`) or call context
    /// pins it. By this pass the return type is SETTLED (P26 — derive from settled
    /// state), so `try_resolve_trait_method`'s nullary branch reaches
    /// `has_impl_in_home` with the concrete return type — and if there is NO impl,
    /// returns the located "no impl of trait X for type Y" error naming the owning
    /// trait. That `Err` is now PROPAGATED (the pre-S114 `if let Ok(Some(..))`
    /// SWALLOWED it, leaking the unresolved Apply to codegen as `undefined
    /// function` — the wrong phase; `design/typecheck/typed-resolution-carrier.md`
    /// §5). This makes the nullary case uniform with the unary sibling (F-D2-7),
    /// which already propagates from `infer_apply`. `Ok(None)` (genuinely still
    /// deferred — a non-concrete return type, dispatched elsewhere) stays a skip.
    pub(crate) fn resolve_deferred_trait_calls(
        &self,
        state: &mut CheckState,
        expr: &Expr,
    ) -> Result<(), CranelispError> {
        // Per-node action: try to resolve an as-yet-unresolved trait-method Apply.
        if let Expr::Apply { callee, args, span, .. } = expr
            && !state.method_resolutions.resolved_calls.contains_key(span)
            && let Expr::Var { name, span: callee_span, .. } = callee.as_ref()
            // §11.8.8 (W3-review Important-1) — "the carrier is the IDENTITY". This
            // post-inference pass runs AFTER the `let`/`fn` scope is popped, so
            // `env.lookup` can no longer see a shadowing local; consult the CARRIER
            // VERDICT `infer_var` already recorded for the callee `Var` instead. A
            // callee resolved to a §4.6 LOCAL binding (`(let [+ (fn [a b] 0)]
            // (+ 1 2))`, and its `((+ 1) 2)` auto-curry sibling) carries
            // `VarRef::Local` — the call is on the local closure, NOT the trait
            // method (mis-dispatch → 3, spec §4.6 violation). The recursion-self
            // carve-out records `VarRef::Global`, so a genuine self-call still
            // dispatches. This is the post-scope form of the same discriminator
            // `CheckState::resolves_to_carrier_identity` applies at the
            // inference-time seams (the infer_apply post-unify + auto-curry blocks)
            // — it READS the recorded verdict rather than recomputing it.
            && !matches!(
                state.method_resolutions.var_refs.get(callee_span),
                Some(cranelisp_types::VarRef::Local { .. })
            )
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
            // Propagate the located no-impl error (F-D2-10); skip on `Ok(None)`.
            if let Some(resolution) =
                self.try_resolve_trait_method(state, name, &resolved_args, *span)?
            {
                // S110 0583 leg 1 (deferred dispatch): carrier at the Apply span.
                self.record_dispatch_target(state, *span, &resolution);
                state.method_resolutions.resolved_calls.insert(*span, resolution);
            }
        }
        // Recurse into children via the shared enumeration helper, propagating the
        // first child error (the F-D2-10 no-impl reject).
        let mut first_err: Option<CranelispError> = None;
        crate::program::for_each_child_expr(expr, |child| {
            if first_err.is_none()
                && let Err(e) = self.resolve_deferred_trait_calls(state, child)
            {
                first_err = Some(e);
            }
        });
        match first_err {
            Some(e) => Err(e),
            None => Ok(()),
        }
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
    ) -> Result<(), CranelispError> {
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
                // F-D2-11 (§3.8 disposition; §7.11.2(c)) — PROPAGATE the located
                // no-impl `Err`. A trait method used as a first-class VALUE
                // (`(let [eq =] (eq (Widget 1) (Widget 2)))`) whose concrete types
                // have NO impl was previously SWALLOWED here (the `if let
                // Ok(Some(..))` — the W2-review Important-3 sibling of the F-D2-10
                // call-path swallow): the Var kept NO resolution and WRONG-ACCEPTED
                // via the downstream primitive-name fallback (`=` → primitive `eq`,
                // returns false). Widening this pass to `Result` (the same widening
                // the W2 fix gave the call path — this is why the swallow survived)
                // lets the located `no impl of trait Eq` error surface, uniform ×3
                // modes. `Ok(None)` (deferred/return-dispatch) records nothing, as
                // before; only `Ok(Some)` records a resolution.
                match self.try_resolve_trait_method(state, name, &resolved_params, *span) {
                    Ok(Some(resolution)) => {
                        // S110 0583 leg 1 (value-position trait method): the carrier
                        // rides the SAME Var span the resolved_call keys (this Var is
                        // a value, not an Apply callee — the backend's fn-as-value
                        // wrapper keys it here). FIXME 0616.
                        self.record_dispatch_target(state, *span, &resolution);
                        state.method_resolutions.resolved_calls.insert(*span, resolution);
                    }
                    Ok(None) => {}
                    Err(e) => return Err(e),
                }
            }
        }

        // Recurse. The `callee` child of an `Apply` is the call path's domain
        // (resolve_deferred_trait_calls / infer_apply) — flag it so this pass
        // does not also try to resolve it as a value.
        match expr {
            Expr::Apply { callee, args, .. } => {
                self.resolve_value_position_trait_methods(state, callee, true)?;
                for arg in args {
                    self.resolve_value_position_trait_methods(state, arg, false)?;
                }
            }
            other => {
                // `for_each_child_expr` takes a `FnMut(&Expr)` (no `?`), so capture
                // the first no-impl `Err` and surface it after the walk.
                let mut first_err: Option<CranelispError> = None;
                crate::program::for_each_child_expr(other, |child| {
                    if first_err.is_none()
                        && let Err(e) =
                            self.resolve_value_position_trait_methods(state, child, false)
                    {
                        first_err = Some(e);
                    }
                });
                if let Some(e) = first_err {
                    return Err(e);
                }
            }
        }
        Ok(())
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
            // Binder provenance: the match-arm node span every var-pattern
            // binder in this arm shares (S114 `VarRef::Local`).
            self.push_scope(state, arm.span);

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
        // by `pat_span` (FQ-typed sidecar; the bare `Symbol` must not slip into
        // backend codegen). The pattern ctor name may be **dotted** (`Maybe.Some`,
        // S109), **bare** (`SCons`, current-module + prelude fallback), or
        // **module-qualified** (`macros/SCons`, FQ, load-bearing for every
        // quasiquote macro). `resolve_constructor_entry` dispatches all three.
        if let Some(cranelisp_types::ModuleEntry::Def { kind, .. }) =
            self.resolve_constructor_entry(state, name.as_ref())
            && let cranelisp_types::DefKind::Constructor { type_name, tag, .. } = kind.as_ref()
        {
            let (fq_sym, instantiated) = self.instantiate_ctor(state, type_name, *tag, span)?;
            state.method_resolutions.pattern_ctors.insert(span, fq_sym);
            return self.unify_pattern_with_scrutinee(
                state, name, bindings, &instantiated, scrutinee_ty, span,
            );
        }

        // **Scrutinee-directed disambiguation (S109 W1, spec §6.2.1 / design §7 /
        // DC-11).** A BARE ctor name that did NOT resolve to a `Def` above is
        // either contested (`Ambiguous`) or absent-in-local-scope (an imported
        // type whose ctors were not brought in). Resolve it against the
        // scrutinee's type when that type is a DETERMINED ADT: probe the canonical
        // `member_key(scrutinee_type, bare)` in the scrutinee type's home module
        // and accept iff the terminal is a ctor of that exact type. The
        // determination depends only on the scrutinee's type at this point
        // (front-to-back, no arm-order sensitivity).
        if !name.as_ref().contains('.') && !name.as_ref().contains('/') {
            let scrut = self.apply_subst(state, scrutinee_ty);
            if let Type::ADT(fqtn, _) = &scrut
                // Only when the scrutinee's TYPE is itself IN SCOPE (resolvable by
                // name in the current module). A bare ctor of a type that is NOT
                // in scope stays unresolved — e.g. `Trace`'s `TraceCall` is not
                // auto-imported (spec §11.2), so `(match (trace ..) [(TraceCall ..)])`
                // without `(import [primitives [TraceCall]])` is an error. The
                // "resolvable ADT head" gate of design §7.
                && self
                    .scope_resolve(state, fqtn.name.as_ref(), span)
                    .ok()
                    .and_then(|r| {
                        crate::checker::type_def_view_of(&r.entry).map(|td| &td.name == fqtn)
                    })
                    .unwrap_or(false)
            {
                let key = cranelisp_types::member_key(&fqtn.name, name.as_ref());
                if let Some(cranelisp_types::ModuleEntry::Def { kind, .. }) =
                    self.probe_module_entry_owned(&fqtn.module, key.as_ref())
                    && let cranelisp_types::DefKind::Constructor { type_name, tag, .. } =
                        kind.as_ref()
                    && type_name == fqtn
                {
                    let (fq_sym, instantiated) =
                        self.instantiate_ctor(state, type_name, *tag, span)?;
                    state.method_resolutions.pattern_ctors.insert(span, fq_sym);
                    return self.unify_pattern_with_scrutinee(
                        state, name, bindings, &instantiated, scrutinee_ty, span,
                    );
                }
            }

            // The scrutinee did not disambiguate. A CONTESTED (`Ambiguous`) bare
            // name is then a compile-time error listing the canonical
            // alternatives (spec §6.2.1 "poison only when the scrutinee type
            // cannot disambiguate").
            if matches!(
                self.resolve_entry_scoped(state, name.as_ref()),
                Some(ModuleEntry::Ambiguous { .. })
            ) {
                let owners = self.reconstruct_accessor_alternatives(state, name.as_ref());
                let hint = if owners.is_empty() {
                    String::new()
                } else {
                    let alts: Vec<String> = owners
                        .iter()
                        .map(|t| {
                            cranelisp_types::member_key(&t.name, name.as_ref())
                                .as_ref()
                                .to_string()
                        })
                        .collect();
                    format!(" — use a qualified constructor ({})", alts.join(" or "))
                };
                return Err(CranelispError::TypeError {
                    message: format!("ambiguous constructor '{name}' in pattern{hint}"),
                    location: ErrorLocation::from_span(span),
                });
            }
        }

        // The name does not resolve to a constructor `Def`.
        Err(CranelispError::TypeError {
            message: format!("unknown constructor in pattern: {name}"),
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
        // A value annotation `:T form` (body/"return"/value position, §3.9/§4.9)
        // resolves against the definition's SHARED written-var scope (spec §3.3
        // co-reference): a body `:a` CO-REFERS to the param's `a` (FV-6), never a
        // fresh per-`Annotate` shadow. Three W6.3 cases (spec §3.3.1/§3.3.3):
        let mut var_map = state.written_var_scope.take().unwrap_or_default();
        match self.resolve_annotation_type_expr_in_module(
            annotation, &mut var_map, &state.current_module, span,
        ) {
            // (1) The annotation is a bare type VARIABLE or a concrete TYPE. It
            // is a FLEXIBLE annotation — the annotated value's type unifies with
            // `ann_type` (W6.3 removes the W6.2 rigid marking: a bare `:a` in
            // value position pins FREELY to the expr's type, §3.3.1 MUST (a) rows
            // 4/11; a concrete `:Int`/`:Float` resolves an otherwise-ambiguous
            // type incl. return-type dispatch, §3.3.3 MUST (d) rows 13–15). A
            // legitimately-polymorphic residual (`:(Vec a) []`) still flows into
            // the §3.11 ambiguity machinery.
            Ok(ann_type) => {
                state.written_var_scope = Some(var_map);
                let expr_ty = self.infer_expr(state, expr)?;
                self.unify(state, &expr_ty, &ann_type, span)?;
                let resolved = self.apply_subst(state, &ann_type);
                self.record_expr_type(state, span, resolved.clone());
                Ok(resolved)
            }
            // (2)/(3) No such TYPE. If the annotation is a single bare name that
            // resolves as a TRAIT, this is a value-position CONSTRAINT — a pure
            // SATISFACTION CHECK (spec §3.3.3 MUST (c)/(e)): it verifies the
            // expr's already-known type implements the trait and changes NOTHING
            // (no unification, no held-abstract). It does NOT disambiguate a
            // return-type-polymorphic form — only a concrete type does (row 17),
            // so a residual var is left for the §3.11 gate.
            Err(type_err) => {
                state.written_var_scope = Some(var_map);
                if let Some(tref) = crate::program::single_trait_bound_from_annotation(annotation) {
                    // Resolve the trait's HOME, honouring a qualified module ref
                    // (`:fmt/Display`) DIRECTLY — mirroring `resolve_bound_param`,
                    // so a value-position constraint and a parameter constraint
                    // (the two entrances to the same constraint shape) resolve
                    // identically (0597 secondary; the §L consistency lens). A
                    // bare ref resolves via current-module-or-prelude.
                    let trait_home = match &tref.module {
                        Some(m) => Some(m.clone()),
                        None => self.resolve_trait(state, tref.name.as_ref(), span).ok(),
                    };
                    if let Some(home) = trait_home {
                        let expr_ty = self.infer_expr(state, expr)?;
                        let resolved = self.apply_subst(state, &expr_ty);
                        let tn = cranelisp_types::TraitName::from(tref.name.as_ref());
                        // Satisfaction check (§3.3.3 MUST (c), "accepted IFF the
                        // expression's type implements the trait"). Three cases on
                        // the resolved expr type:
                        //
                        //  - NOMINAL concrete (`concrete_type_name` = Some): it
                        //    MUST implement the trait (row 12 pos accepts
                        //    `:Num2 5`; the neg rejects `:Num2 "s"`).
                        //  - CONCRETE but NON-NOMINAL (`Fn`, …): impls are keyed
                        //    by TYPE NAME, so a function type implements NOTHING —
                        //    it MUST be rejected, not silently accepted. `None`
                        //    from `concrete_type_name` on a concrete type was the
                        //    0596-sibling false accept (`(defn g1 [] :NumT
                        //    (fn [:Int y] y))`), FIXME 0597.
                        //  - still a `Type::Var` (unresolved return-type dispatch,
                        //    `:Zeroable (zed)`): the constraint does NOT resolve it
                        //    — leave the residual var for the §3.11 ambiguity gate
                        //    (row 17).
                        match crate::traits::concrete_type_name(&resolved) {
                            Some(impl_ty) => {
                                if !self.has_impl_in_home(&home, &tn, &impl_ty) {
                                    return Err(CranelispError::TypeError {
                                        message: format!(
                                            "type {impl_ty} does not implement trait {} \
                                             — a value-position constraint is a \
                                             satisfaction check (spec §3.3.3)",
                                            tref.name
                                        ),
                                        location: ErrorLocation::from_span(span),
                                    });
                                }
                            }
                            None if resolved.is_concrete() => {
                                return Err(CranelispError::TypeError {
                                    message: format!(
                                        "type {resolved} does not implement trait {} — a \
                                         value-position constraint is a satisfaction \
                                         check (spec §3.3.3); a function type implements \
                                         no trait",
                                        tref.name
                                    ),
                                    location: ErrorLocation::from_span(span),
                                });
                            }
                            None => {}
                        }
                        // The type is UNCHANGED (satisfaction check only).
                        self.record_expr_type(state, span, resolved.clone());
                        return Ok(resolved);
                    }
                }
                Err(type_err.into())
            }
        }
    }
}

#[cfg(test)]
mod tests;
