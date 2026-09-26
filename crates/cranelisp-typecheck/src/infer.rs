//! Expression type inference: one method per Expr variant.
//!
//! `infer_expr` dispatches to per-variant helpers. Each helper is typically
//! 10-40 lines, independently testable. Addresses audit HIGH-1 (monolithic infer_expr).

use cranelisp_types::{
    ApplyRef, Binding, CallableOrigin, CranelispError, Decl, ErrorLocation, Expr, FQSymbol, Life,
    MatchArm, Pattern, ResolvedCall, Span, Symbol, TemplateKind, Type, TypeExpr, VarRef,
};

use crate::checker::{CheckState, TypeCheckEnv};
use crate::scheme::mono;

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Infer the type of an expression. Main dispatch method.
    pub(crate) fn infer_expr(
        &self,
        state: &mut CheckState,
        expr: &Expr,
    ) -> Result<Type, CranelispError> {
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
                params, body, span, ..
            } => self.infer_lambda(state, params, body, *span),
            Expr::Apply {
                callee, args, span, ..
            } => {
                let ty = self.infer_apply(state, callee, args, *span)?;
                // Apply-side totality (S114 carrier flip, design/typecheck/ast-annotation.md §2.1): EVERY
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
                let candidate_pending = state.body_frame.pending_name_uses.iter().any(|site| {
                    site.applications
                        .iter()
                        .any(|application| application.call_span == *span)
                });
                if !candidate_pending {
                    state
                        .method_resolutions
                        .apply_refs
                        .entry(*span)
                        .or_insert(ApplyRef::ViaCallee);
                }
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
            Expr::ConstrADT {
                type_name,
                tag,
                fields,
                span,
                ..
            } => self.infer_constradt(state, type_name, *tag, fields, *span),
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
                message: format!(
                    "unexpected constructor type for {}#{}: {:?}",
                    type_name.name, tag, other
                ),
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
        let info = self
            .lookup_type_def_in_module(&type_name.module, &type_name.name)
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
        // Look up the ctor's scheme via its binding in the type's defining module,
        // recording the STORAGE key that hit as the sidecar identity
        // (`design/arch/dotted-ctor-canonical-keys.md` §10.1).
        // `TypeDefInfo.constructors` carries bare display names, but a sum ctor's
        // binding lives under the canonical `member_key(Type, Ctor)` key
        // (`Maybe.Some`); its bare spelling is only a candidate exposure. Probe the
        // canonical key first, then the bare key, which serves the product
        // dual-facet alone (arch §1). The backend reads the recorded key directly,
        // never re-resolving the bare name (arch §10.3).
        let canonical = cranelisp_types::member_key(&type_name.name, ctor_sym.as_ref());
        let (storage_key, scheme) = self
            .probe_module_entry_owned(&type_name.module, canonical.as_ref())
            .and_then(|e| {
                e.callable()
                    .map(|c| (canonical.clone(), c.arm.scheme.clone()))
            })
            .or_else(|| {
                self.probe_module_entry_owned(&type_name.module, ctor_sym.as_ref())
                    .and_then(|e| {
                        e.callable()
                            .map(|c| (ctor_sym.clone(), c.arm.scheme.clone()))
                    })
            })
            .ok_or_else(|| CranelispError::TypeError {
                message: format!("constructor {}.{ctor_sym} has no scheme", type_name.name),
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

    fn infer_var(
        &self,
        state: &mut CheckState,
        name: &Symbol,
        span: Span,
    ) -> Result<Type, CranelispError> {
        // S113 0655 (user ruling (a)) — spelling normalization at the ONE Var
        // entry: a reference qualified with the CURRENT module (after §8.6.6
        // alias substitution) IS the bare local. Normalize BEFORE the env
        // consult so every read below (scheme lookup, the value/undefined
        // diagnostics, the dotted/carrier recorders, and — via
        // `record_reference_target`'s env consult — the §4.6 shadow + §11.8.7
        // recursion-self carve-out) observes the bare shape. See
        // `TypeCheckEnv::normalize_self_qualified`.
        let name: &str = self.normalize_self_qualified(state, name.as_ref());

        // Lexical bindings shadow the entire module candidate set. Otherwise
        // retain every value-role terminal until ordinary HM constraints can
        // select one; raw candidate cardinality is not a resolution verdict.
        if state.env.lookup(name).is_none()
            && self.resolve_dotted_member_fq(state, name).is_none()
            && let Ok(candidates) = self.scope_resolve_candidates(state, name, span)
        {
            let contested = candidates.len() > 1;
            let value_candidates: Vec<_> = candidates
                .into_iter()
                .filter(|candidate| {
                    crate::candidate_selection::is_value_candidate(&candidate.entry)
                })
                .collect();
            // A contested spelling is decided only after the syntactic-role
            // filter. Zero, one, and many eligible terminals all enter the
            // same settlement lifecycle: zero becomes no-match, one replays
            // its canonical identity, and many await ordinary HM constraints.
            if contested {
                let survivors = value_candidates
                    .into_iter()
                    .map(|candidate| candidate.canonical)
                    .collect();
                return Ok(self.collect_pending_name_use(
                    state,
                    Symbol::from(name),
                    span,
                    survivors,
                ));
            }
        }
        let (scheme, gap) = self.lookup(state, name);
        // Record the in-band gap (if any) so a failed qualified-name resolution
        // surfaces as `CheckError::Gap` once the per-form dispatcher reports its
        // not-found error. Always write (Some or None) to match the prior
        // clear-on-attempt / set-on-miss side-slot semantics.
        state.pending_gap = gap;
        // A bare spelling that still has several candidates here yields no
        // scheme; report it as ambiguous, listing canonical `Type.member`
        // alternatives, rather than as "undefined variable" (spec §8.6.5; field
        // accessors §5.2.6).
        if scheme.is_none()
            && self
                .scope_resolve_candidates(state, name, span)
                .is_ok_and(|candidates| candidates.len() > 1)
        {
            // Same-cluster (`--run`): the owners were recorded on `CheckState`
            // as each accessor was synthesised in this `check_forms` call.
            // Cross-cluster (the REPL drives each form as its own cluster with a
            // FRESH `CheckState`), the map is empty by the time the bare use is
            // checked — the contributing `deftype`s ran in earlier clusters.
            // Re-derive the owners structurally from the durable symbol table so
            // both paths list the canonical alternatives (§5.2.6 gives the REPL
            // no exemption).
            let owners: Vec<cranelisp_types::FQTypeName> =
                match state.accessor_owning_types.get(name) {
                    Some(tys) if !tys.is_empty() => tys.clone(),
                    _ => self.reconstruct_accessor_alternatives(state, name),
                };
            let hint = if owners.is_empty() {
                String::new()
            } else {
                let alts: Vec<String> = owners
                    .iter()
                    .map(|t| {
                        cranelisp_types::member_key(&t.name, name)
                            .as_ref()
                            .to_string()
                    })
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
            if let Some(Binding {
                declaration: Decl::SpecialForm(_),
                ..
            }) = v.lookup(&Symbol::from(name))
            {
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
                message: format!("cannot construct internal type constructor '{name}'"),
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
            && entry.callable().is_some_and(|callable| {
                matches!(
                    callable.arm.life,
                    Life::Template {
                        kind: TemplateKind::Constrained(_),
                        ..
                    }
                )
            })
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
            && matches!(entry.declaration, Decl::Overloaded(_))
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
        &self,
        state: &mut CheckState,
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
        &self,
        state: &mut CheckState,
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
        &self,
        state: &mut CheckState,
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
        &self,
        state: &mut CheckState,
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
        &self,
        state: &mut CheckState,
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
        let mut var_map = state
            .body_frame
            .written_var_scope
            .take()
            .unwrap_or_default();
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
                        annotation,
                        &mut var_map,
                        &state.current_module,
                        span,
                    )
                    .map_err(|failure| failure.into_form_error(state))?
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
        state.body_frame.written_var_scope = Some(var_map);

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
    fn maybe_rehydrate_imported_overload_base(&self, state: &mut CheckState, name: &Symbol) {
        if state.overloads.contains_key(name) {
            return;
        }
        let Some((entry, home)) = self.resolve_terminal_entry_scoped(state, name.as_ref()) else {
            return;
        };
        if home == state.current_module {
            return; // local base — the ordinary registration path owns it
        }
        if let Decl::Overloaded(declaration) = &entry.declaration {
            self.rehydrate_overload_group(state, name, &home, declaration);
        }
    }

    fn rehydrate_overload_group(
        &self,
        state: &mut CheckState,
        name: &Symbol,
        home: &cranelisp_types::ModuleFullPath,
        declaration: &cranelisp_types::OverloadedCallable<C>,
    ) {
        if declaration.arms.is_empty() {
            return;
        }
        let overload_keys = declaration
            .arms
            .iter()
            .filter_map(|arm| {
                let Type::Fn(params, _) = &arm.callable.scheme.ty else {
                    return None;
                };
                Some((
                    Symbol::from(format!("{}__arm{}", name, arm.id.ordinal())),
                    params.len(),
                ))
            })
            .collect();
        let resolved = declaration
            .arms
            .iter()
            .filter_map(|arm| {
                let Type::Fn(params, ret) = &arm.callable.scheme.ty else {
                    return None;
                };
                Some((
                    params.clone(),
                    (**ret).clone(),
                    Symbol::from(format!("{}__arm{}", name, arm.id.ordinal())),
                ))
            })
            .collect();
        state.overloads.insert(name.clone(), overload_keys);
        state.resolved_overloads.insert(name.clone(), resolved);
        state.overload_homes.insert(name.clone(), home.clone());
    }

    /// Feed an already-selected overload declaration and its application into
    /// the existing overload queue without re-resolving the contested source
    /// spelling. Imported groups use their canonical qualified identity as the
    /// private queue key, so two selected same-named groups cannot overwrite
    /// one another's variant/home facts.
    pub(crate) fn enqueue_selected_overload_application(
        &self,
        state: &mut CheckState,
        selected: &cranelisp_types::FQSymbol,
        binding: &Binding<C>,
        application: &crate::candidate_selection::PendingApplication,
        callee_span: Span,
    ) {
        let queue_key = if selected.module == state.current_module {
            selected.symbol.clone()
        } else {
            Symbol::from(selected.to_string())
        };
        if let Decl::Overloaded(declaration) = &binding.declaration {
            self.rehydrate_overload_group(state, &queue_key, &selected.module, declaration);
        }
        let is_self_call = selected.module == state.current_module
            && state
                .body_frame
                .recursion
                .as_ref()
                .is_some_and(|recursion| {
                    recursion.name == selected.symbol
                        || recursion
                            .name
                            .as_ref()
                            .starts_with(&format!("{}__v", selected.symbol))
                });
        state.pending_overload_resolutions.push((
            application.call_span,
            queue_key,
            application.argument_types.clone(),
            application.result_type.clone(),
            is_self_call,
            callee_span,
        ));
    }

    fn infer_apply(
        &self,
        state: &mut CheckState,
        callee: &Expr,
        args: &[Expr],
        span: Span,
    ) -> Result<Type, CranelispError> {
        // An authored overload family has no stand-alone callable value in the
        // symbol table while its clauses are being checked. Recognize that
        // transient typecheck state before ordinary Var inference, otherwise
        // the removed `Group` placeholder turns every same-cluster call into an
        // `undefined variable` before the overload drain can select an arm.
        let normalized_callee: Option<Symbol> = match callee {
            Expr::Var { name, .. } => Some(Symbol::from(
                self.normalize_self_qualified(state, name.as_ref()),
            )),
            _ => None,
        };
        if let Some(name) = normalized_callee.as_ref()
            && !state.overloads.contains_key(name)
            && state.env.lookup(name.as_ref()).is_none()
        {
            self.maybe_rehydrate_imported_overload_base(state, name);
        }
        let overload_callee = normalized_callee.as_ref().is_some_and(|name| {
            state.overloads.contains_key(name) && state.resolves_to_carrier_identity(name.as_ref())
        });

        // Mark callee as in call position so constrained fn references are allowed.
        // Save/restore is stack-based: each nesting level preserves the outer value.
        let prev_call_position = state.in_call_position;
        state.in_call_position = true;
        let callee_ty = if overload_callee {
            let ty = Type::Fn(
                (0..args.len()).map(|_| self.fresh_var()).collect(),
                Box::new(self.fresh_var()),
            );
            let Some(written) = normalized_callee.as_ref() else {
                unreachable!("invariant: overload callee is a normalized Var")
            };
            let owner_module = state
                .overload_homes
                .get(written)
                .cloned()
                .unwrap_or_else(|| state.current_module.clone());
            let owner_symbol = Symbol::from(
                written
                    .as_ref()
                    .rsplit('/')
                    .next()
                    .unwrap_or(written.as_ref()),
            );
            state.method_resolutions.var_refs.insert(
                callee.span(),
                cranelisp_types::VarRef::Global(FQSymbol {
                    module: owner_module,
                    symbol: owner_symbol,
                }),
            );
            self.record_expr_type(state, callee.span(), ty.clone());
            Ok(ty)
        } else {
            self.infer_expr(state, callee)
        };
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

        if self.attach_pending_application(
            state,
            &callee_ty,
            span,
            arg_types.clone(),
            ret_ty.clone(),
        ) {
            self.settle_pending_name_uses(state, false)?;
            let still_pending = state.body_frame.pending_name_uses.iter().any(|site| {
                site.applications
                    .iter()
                    .any(|application| application.call_span == span)
            });
            let handed_to_overload = state
                .pending_overload_resolutions
                .iter()
                .any(|pending| pending.0 == span);
            if still_pending || handed_to_overload {
                for (arg, arg_ty) in args.iter().zip(arg_types.iter()) {
                    self.record_expr_type(state, arg.span(), self.apply_subst(state, arg_ty));
                }
                self.record_expr_type(state, span, self.apply_subst(state, &ret_ty));
                return Ok(ret_ty);
            }
        }

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
                .and_then(|context| context.recursion.as_ref())
                .is_some_and(|recursion| {
                    recursion.base == *name && recursion.params.len() == arg_types.len()
                })
            {
                let (instance, inst_params, inst_ret) = {
                    let recursion = state
                        .mono_recheck_self
                        .as_ref()
                        .and_then(|context| context.recursion.as_ref())
                        .unwrap();
                    (
                        recursion.instance.clone(),
                        recursion.params.clone(),
                        recursion.ret.clone(),
                    )
                };
                let resolved_args: Vec<Type> = arg_types
                    .iter()
                    .map(|a| self.apply_subst(state, a))
                    .collect();
                if inst_params
                    .iter()
                    .zip(resolved_args.iter())
                    .all(|(p, a)| p == a)
                {
                    for (p, a) in inst_params.iter().zip(arg_types.iter()) {
                        self.unify(state, p, a, span)?;
                    }
                    self.unify(state, &inst_ret, &ret_ty, span)?;
                    let resolution = ResolvedCall::SigDispatch {
                        target: cranelisp_types::CallableTarget::Binding(FQSymbol {
                            module: state.current_module.clone(),
                            symbol: Symbol::from(instance.as_ref()),
                        }),
                    };
                    self.record_dispatch_target(state, span, &resolution);
                    state
                        .method_resolutions
                        .resolved_calls
                        .insert(span, resolution);
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
            if let Some(base) = state
                .mono_recheck_self
                .as_ref()
                .and_then(|context| context.recursion.as_ref())
                .map(|recursion| recursion.base.clone())
                && base == *name
            {
                let resolved_args: Vec<Type> = arg_types
                    .iter()
                    .map(|a| self.apply_subst(state, a))
                    .collect();
                if resolved_args.iter().all(Type::is_concrete)
                    && let Some(variants) = state.resolved_overloads.get(name).cloned()
                    && let crate::program::OverloadSelection::Unique((cparams, cret, cmangled)) =
                        crate::program::select_unique_overload_variant(&variants, &resolved_args)
                {
                    let clause_params = cparams.clone();
                    let clause_mangled = cmangled.clone();
                    let clause_ret = cret.clone();
                    let clause_index = variants
                        .iter()
                        .position(|(_, _, label)| label == &clause_mangled)
                        .ok_or_else(|| CranelispError::CodegenError {
                            message: format!(
                                "internal: selected overload arm missing from `{name}`"
                            ),
                            location: ErrorLocation::from_span(span),
                        })?;
                    let selected_arm = cranelisp_types::CallableArmId::from_ordinal(clause_index)
                        .map_err(crate::result::lifecycle_error)?;
                    let selected_target = cranelisp_types::CallableTarget::OverloadArm {
                        owner: FQSymbol {
                            module: state.current_module.clone(),
                            symbol: name.clone(),
                        },
                        arm: selected_arm,
                    };
                    // Whether an arm needs an instance is a lifecycle fact, not
                    // a property of the selected call's substituted parameter
                    // vector.  A template arm naturally has concrete parameters
                    // here because overload selection just instantiated it.
                    let selected_template = state
                        .mono_recheck_self
                        .as_ref()
                        .and_then(|context| {
                            context
                                .local_templates
                                .get(&clause_mangled)
                                .cloned()
                                .map(|core| crate::traits::TemplateFn {
                                    core,
                                    local_templates: context.local_templates.clone(),
                                    template_target: Some(selected_target.clone()),
                                })
                        })
                        .or_else(|| self.owned_overload_template(&selected_target));
                    // Resolve the selected sibling clause to a CONCRETE dispatch
                    // target + its concrete signature.
                    let (dispatch_name, inst_params, inst_ret) = if let Some(template) =
                        selected_template
                    {
                        // Template sibling (constrained / genuinely-poly) —
                        // monomorphise at the concrete args and dispatch to
                        // the minted instance.
                        let use_type = Type::Fn(
                            resolved_args.clone(),
                            Box::new(self.apply_subst(state, &clause_ret)),
                        );
                        let demand = self.derive_mono_demand(
                            state,
                            selected_target.clone(),
                            &template.core.scheme,
                            &use_type,
                            span,
                        );
                        let mono = if let Some(demand) = demand {
                            self.monomorphise_call(
                                state,
                                &clause_mangled,
                                &demand,
                                None,
                                Some(name),
                                Some(template),
                            )?
                        } else {
                            None
                        };
                        let instance = match &mono {
                            Some(md) => md.defn.name.clone(),
                            None => clause_mangled.clone(),
                        };
                        let cm = state.current_module.clone();
                        let inst_ret = self
                            .probe_module_entry_owned(&cm, instance.as_ref())
                            .and_then(|e| {
                                e.callable()
                                    .and_then(|callable| match &callable.arm.scheme.ty {
                                        Type::Fn(_, r) => Some((**r).clone()),
                                        _ => None,
                                    })
                            })
                            .unwrap_or_else(|| self.apply_subst(state, &clause_ret));
                        (
                            cranelisp_types::CallableTarget::Binding(FQSymbol {
                                module: state.current_module.clone(),
                                symbol: instance,
                            }),
                            resolved_args.clone(),
                            inst_ret,
                        )
                    } else {
                        // Concrete sibling clause — dispatch to its owned arm.
                        (
                            selected_target,
                            clause_params.clone(),
                            self.apply_subst(state, &clause_ret),
                        )
                    };
                    for (p, a) in inst_params.iter().zip(arg_types.iter()) {
                        self.unify(state, p, a, span)?;
                    }
                    self.unify(state, &inst_ret, &ret_ty, span)?;
                    let resolution = ResolvedCall::SigDispatch {
                        target: dispatch_name,
                    };
                    self.record_dispatch_target(state, span, &resolution);
                    state
                        .method_resolutions
                        .resolved_calls
                        .insert(span, resolution);
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
                .body_frame
                .recursion
                .as_ref()
                .map(|d| {
                    let d = d.name.as_ref();
                    d == name.as_ref() || d.starts_with(&format!("{}__v", name))
                })
                .unwrap_or(false);
            state.pending_overload_resolutions.push((
                span,
                name.clone(),
                arg_types.clone(),
                ret_ty.clone(),
                is_self_call,
                // FIXME 0719 — carry the callee `Var`'s own span so the drain can
                // retype it to the SELECTED clause's signature, exactly as the
                // inline arm above does. Without it the node keeps the
                // pre-dispatch instantiation of the overloaded base and a
                // wrapper-indirected mono instance ships a residual `Var` into
                // `from_expr`.
                callee.span(),
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
                        let resolution = match self.try_resolve_trait_method(
                            state,
                            name,
                            &resolved_params,
                            span,
                        ) {
                            Ok(Some(r)) => Some(r),
                            Ok(None) => self
                                .resolve_builtin(state, name.as_ref(), span)
                                .map(crate::checker::PendingDispatch::Builtin),
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

            if let Some(dispatch) =
                self.try_resolve_trait_method(state, name, &resolved_args, span)?
            {
                let resolution = self.settle_dispatch(state, span, dispatch);
                // An unannotated default method has a fresh result variable on
                // the trait's generic carrier. Once dispatch selects a concrete
                // impl, refine that variable from the selected mangled method's
                // checked scheme. The impl method is the authoritative inferred
                // result; leaving the carrier's fresh var untouched reports
                // values such as `:a 7` even though the method body inferred Int.
                if let ResolvedCall::TraitMethod {
                    mangled_name,
                    impl_module,
                    ..
                } = &resolution
                    && let Some(entry) =
                        self.probe_module_entry_owned(impl_module, mangled_name.as_ref())
                    && let Some(callable) = entry.callable()
                    && let Type::Fn(_, selected_ret) = &callable.arm.scheme.ty
                {
                    self.unify(state, &ret_ty, selected_ret.as_ref(), span)?;
                }
                // Trait method resolution (Ring 2): operators like +, -, =, <
                // S110 0583 leg 1: record the dispatch-leg carrier at the Apply
                // span alongside the `resolved_calls` insert (FIXME 0616).
                state
                    .method_resolutions
                    .resolved_calls
                    .insert(span, resolution);
            } else if let Some(builtin) = self.resolve_builtin(state, name.as_ref(), span) {
                // Named primitive resolution (Ring 0-3): add-i64, str-concat,
                // macros/sconcat, quote-sexp, etc.
                let resolution = ResolvedCall::BuiltinFn {
                    name: builtin.jit_name,
                };
                state.method_resolutions.apply_refs.insert(
                    span,
                    cranelisp_types::ApplyRef::Dispatch(builtin.storage_fq),
                );
                state
                    .method_resolutions
                    .resolved_calls
                    .insert(span, resolution);
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
        &self,
        state: &mut CheckState,
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
                // A probe: its gap is dropped.
                if let (Some(entry), _) = self.resolve_constructor_entry(state, name.as_ref())
                    && let Some(callable) = entry.callable()
                    && let CallableOrigin::Ctor { field_count, .. } = &callable.origin
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
    pub(crate) fn resolve_builtin(
        &self,
        state: &CheckState,
        name: &str,
        span: Span,
    ) -> Option<crate::checker::ResolvedBuiltin> {
        let resolved = self.scope_resolve(state, name, span).ok()?;
        resolved
            .entry
            .callable()
            .is_some_and(|callable| matches!(callable.origin, CallableOrigin::RustPrimitive))
            .then(|| {
                let storage_fq = resolved.canonical;
                crate::checker::ResolvedBuiltin {
                    jit_name: storage_fq.symbol.clone(),
                    storage_fq,
                }
            })
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
    /// function` — the wrong phase; `design/typecheck/typecheck.md`
    /// §9.1). This makes the nullary case uniform with the unary sibling (F-D2-7),
    /// which already propagates from `infer_apply`. `Ok(None)` (genuinely still
    /// deferred — a non-concrete return type, dispatched elsewhere) stays a skip.
    pub(crate) fn resolve_deferred_trait_calls(
        &self,
        state: &mut CheckState,
        expr: &Expr,
    ) -> Result<(), CranelispError> {
        // Per-node action: try to resolve an as-yet-unresolved trait-method Apply.
        if let Expr::Apply {
            callee, args, span, ..
        } = expr
            && !state.method_resolutions.resolved_calls.contains_key(span)
            && let Expr::Var {
                name,
                span: callee_span,
                ..
            } = callee.as_ref()
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
        {
            let resolved_args: Vec<Type> = args
                .iter()
                .map(|a| {
                    state
                        .expr_types
                        .get(&a.span())
                        .map(|t| self.apply_subst(state, t))
                        .unwrap_or_else(|| Type::Var(0))
                })
                .collect();
            // Propagate the located no-impl error (F-D2-10); skip on `Ok(None)`.
            if let Some(dispatch) = self.try_resolve_trait_method_from_carrier(
                state,
                name,
                *callee_span,
                &resolved_args,
                *span,
            )? {
                let resolution = self.settle_dispatch(state, *span, dispatch);
                // S110 0583 leg 1 (deferred dispatch): carrier at the Apply span.
                state
                    .method_resolutions
                    .resolved_calls
                    .insert(*span, resolution);
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
                match self.try_resolve_trait_method_from_carrier(
                    state,
                    name,
                    *span,
                    &resolved_params,
                    *span,
                ) {
                    Ok(Some(dispatch)) => {
                        let resolution = self.settle_dispatch(state, *span, dispatch);
                        // S110 0583 leg 1 (value-position trait method): the carrier
                        // rides the SAME Var span the resolved_call keys (this Var is
                        // a value, not an Apply callee — the backend's fn-as-value
                        // wrapper keys it here). FIXME 0616.
                        state
                            .method_resolutions
                            .resolved_calls
                            .insert(*span, resolution);
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

    /// Resolve a trait method from the already-recorded Var carrier.
    ///
    /// Candidate selection may have replaced a contested written spelling with
    /// one canonical declaration after the expression was first inferred.  The
    /// post-inference settlement passes must therefore consume that canonical
    /// identity, rather than repeat lookup by the raw AST name and potentially
    /// select a different declaration.  Absence is retained only for legacy
    /// unit seams that invoke these passes without first inferring the Var.
    fn try_resolve_trait_method_from_carrier(
        &self,
        state: &mut CheckState,
        written_name: &Symbol,
        var_span: Span,
        argument_types: &[Type],
        call_span: Span,
    ) -> Result<Option<crate::checker::PendingDispatch>, CranelispError> {
        match state.method_resolutions.var_refs.get(&var_span).cloned() {
            Some(VarRef::Global(selected)) => {
                let is_trait_method = self
                    .probe_module_entry_owned(&selected.module, selected.symbol.as_ref())
                    .is_some_and(|binding| matches!(binding.declaration, Decl::TraitMethod(_)));
                if is_trait_method {
                    self.try_resolve_selected_trait_method(
                        state,
                        &selected,
                        argument_types,
                        call_span,
                    )
                } else {
                    Ok(None)
                }
            }
            Some(VarRef::Local { .. }) => Ok(None),
            None if self.is_trait_method_with_state(state, written_name) => {
                self.try_resolve_trait_method(state, written_name, argument_types, call_span)
            }
            None => Ok(None),
        }
    }

    fn infer_match(
        &self,
        state: &mut CheckState,
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

        let mut covered_ctor_spans: Vec<Span> = Vec::new();
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
                    self.check_constructor_pattern(
                        state,
                        &ctor_sym,
                        bindings,
                        &scrutinee_ty,
                        *pat_span,
                    )?;
                    covered_ctor_spans.push(*pat_span);
                }
                Pattern::Wildcard { .. } => {
                    has_wildcard = true;
                }
                Pattern::Var { name, .. } => {
                    has_wildcard = true;
                    self.bind_local(
                        state,
                        name.clone(),
                        mono(self.apply_subst(state, &scrutinee_ty)),
                    );
                }
            }

            let arm_ty = self.infer_expr(state, &arm.body)?;
            self.unify(state, &arm_ty, &result_ty, arm.span)?;

            self.pop_scope(state);
        }

        // Arm bodies have now constrained the provisional scrutinee/binder
        // anchors. Select and replay contested constructors before
        // exhaustiveness consumes their canonical identities.
        self.settle_pending_candidates(state, false, true)?;

        // Check exhaustiveness for concrete ADT scrutinees.
        // The type is defined in `fqtn.module` (its home module), not the
        // current module — under Principle 17 short-name resolution, looking
        // up the type via `state.current_module` would fail for ADTs imported
        // from other modules (e.g. `macros/SList` matched in `fn.threading`).
        let resolved_scrutinee = self.apply_subst(state, &scrutinee_ty);
        if let Type::ADT(fqtn, _) = &resolved_scrutinee {
            let covered_ctors = covered_ctor_spans
                .iter()
                .filter_map(|pattern_span| {
                    let selected = state.method_resolutions.pattern_ctors.get(pattern_span)?;
                    let binding =
                        self.probe_module_entry_owned(&selected.module, selected.symbol.as_ref())?;
                    let callable = binding.callable()?;
                    let CallableOrigin::Ctor { type_name, tag, .. } = &callable.origin else {
                        return None;
                    };
                    if type_name != fqtn {
                        return None;
                    }
                    self.lookup_type_def_in_module(&fqtn.module, &fqtn.name)
                        .and_then(|info| info.constructors.get(*tag).cloned())
                })
                .collect::<Vec<_>>();
            self.check_exhaustiveness_in_module(fqtn, &covered_ctors, has_wildcard, span)?;
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
        &self,
        state: &mut CheckState,
        name: &Symbol,
        bindings: &[Symbol],
        scrutinee_ty: &Type,
        span: Span,
    ) -> Result<(), CranelispError> {
        // Reject internal constructors (e.g. Bind) in pattern matching.
        // Internal constructors are implementation details not meant for user code.
        if self.is_internal_constructor(state, name) {
            return Err(CranelispError::TypeError {
                message: format!("cannot match on internal type constructor '{name}'"),
                location: ErrorLocation::from_span(span),
            });
        }

        // Trigger 3 (S70): populate `MethodResolutions.pattern_ctors` keyed
        // by `pat_span` (FQ-typed sidecar; the bare `Symbol` must not slip into
        // backend codegen). The pattern ctor name may be **dotted** (`Maybe.Some`,
        // S109), **bare** (`SCons`, current-module + prelude fallback), or
        // **module-qualified** (`macros/SCons`, FQ, load-bearing for every
        // quasiquote macro). `resolve_constructor_entry` dispatches all three.
        let (entry, qualified_gap) = self.resolve_constructor_entry(state, name.as_ref());
        if let Some(entry) = entry
            && let Some(callable) = entry.callable()
            && let CallableOrigin::Ctor { type_name, tag, .. } = &callable.origin
        {
            let (fq_sym, instantiated) = self.instantiate_ctor(state, type_name, *tag, span)?;
            state.method_resolutions.pattern_ctors.insert(span, fq_sym);
            return self.unify_pattern_with_scrutinee(
                state,
                name,
                bindings,
                &instantiated,
                scrutinee_ty,
                span,
            );
        }

        // **Scrutinee-directed disambiguation (spec §6.2.1; arch
        // `dotted-ctor-canonical-keys.md` §7).** A BARE ctor name that did NOT
        // resolve to a single constructor above either has several candidates or
        // is absent from local scope (an imported type whose ctors were not
        // brought in). Resolve it against the
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
                if let Some(entry) = self.probe_module_entry_owned(&fqtn.module, key.as_ref())
                    && let Some(callable) = entry.callable()
                    && let CallableOrigin::Ctor { type_name, tag, .. } = &callable.origin
                    && type_name == fqtn
                {
                    let (fq_sym, instantiated) =
                        self.instantiate_ctor(state, type_name, *tag, span)?;
                    state.method_resolutions.pattern_ctors.insert(span, fq_sym);
                    return self.unify_pattern_with_scrutinee(
                        state,
                        name,
                        bindings,
                        &instantiated,
                        scrutinee_ty,
                        span,
                    );
                }
            }

            let constructor_candidates = self
                .scope_resolve_candidates(state, name.as_ref(), span)
                .unwrap_or_default()
                .into_iter()
                .filter(|candidate| {
                    candidate.entry.callable().is_some_and(|callable| {
                        matches!(callable.origin, CallableOrigin::Ctor { .. })
                    })
                })
                .map(|candidate| candidate.canonical)
                .collect::<Vec<_>>();
            if !constructor_candidates.is_empty() {
                self.collect_pending_pattern_use(
                    state,
                    name.clone(),
                    span,
                    scrutinee_ty.clone(),
                    bindings,
                    constructor_candidates,
                );
                self.settle_pending_pattern_uses(state, false)?;
                return Ok(());
            }

            // The scrutinee did not disambiguate. A bare name that still has
            // several candidates is then a compile-time error listing the
            // canonical alternatives (spec §6.2.1). The approved target derives
            // this list from the surviving candidates
            // (`design/typecheck/use-site-candidate-selection.md` §9); this
            // branch still reconstructs it from the table
            // (`design/typecheck/dotted-ctor-registration.md` §8).
            if self
                .scope_resolve_candidates(state, name.as_ref(), span)
                .is_ok_and(|candidates| candidates.len() > 1)
            {
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

        // The name does not resolve to a constructor `Def`. A qualified miss
        // has no scrutinee-directed fallback, so it is the form's failure and
        // its walk's gap is recorded here, as `infer_var` records the value
        // twin's (`design/typecheck/typecheck.md` §3.5, §7.3.1).
        if name.as_ref().contains('/') {
            state.pending_gap = qualified_gap;
        }
        Err(CranelispError::TypeError {
            message: format!("unknown constructor in pattern: {name}"),
            location: ErrorLocation::from_span(span),
        })
    }

    /// Unify an instantiated constructor type with the scrutinee and bind variables.
    fn unify_pattern_with_scrutinee(
        &self,
        state: &mut CheckState,
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
            Type::Fn(field_types, ret_type) => self.bind_data_ctor_pattern(
                state,
                name,
                bindings,
                field_types,
                ret_type,
                scrutinee_ty,
                span,
            ),

            _ => Err(CranelispError::TypeError {
                message: format!("constructor {name} has unexpected type: {instantiated}"),
                location: ErrorLocation::from_span(span),
            }),
        }
    }

    /// Bind pattern variables for a data constructor with fields.
    #[allow(clippy::too_many_arguments)]
    fn bind_data_ctor_pattern(
        &self,
        state: &mut CheckState,
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
        &self,
        state: &mut CheckState,
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
        &self,
        state: &mut CheckState,
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
        &self,
        state: &mut CheckState,
        annotation: &TypeExpr,
        expr: &Expr,
        span: Span,
    ) -> Result<Type, CranelispError> {
        // A value annotation `:T form` (body/"return"/value position, §3.9/§4.9)
        // resolves against the definition's SHARED written-var scope (spec §3.3
        // co-reference): a body `:a` CO-REFERS to the param's `a` (FV-6), never a
        // fresh per-`Annotate` shadow. Three W6.3 cases (spec §3.3.1/§3.3.3):
        let mut var_map = state
            .body_frame
            .written_var_scope
            .take()
            .unwrap_or_default();
        match self.resolve_annotation_type_expr_in_module(
            annotation,
            &mut var_map,
            &state.current_module,
            span,
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
                state.body_frame.written_var_scope = Some(var_map);
                let expr_ty = self.infer_expr(state, expr)?;
                self.unify(state, &expr_ty, &ann_type, span)?;
                let resolved = self.apply_subst(state, &ann_type);
                self.record_expr_type(state, span, resolved.clone());
                Ok(resolved)
            }
            // (2)/(3) No such TYPE. If the annotation is a single name that
            // resolves as a TRAIT, this is a value-position CONSTRAINT — a pure
            // SATISFACTION CHECK (spec §3.3.3 MUST (c)/(e)): it verifies the
            // expr's already-known type implements the trait and changes NOTHING
            // (no unification, no held-abstract). It does NOT disambiguate a
            // return-type-polymorphic form — only a concrete type does (row 17),
            // so a residual var is left for the §3.11 gate. Otherwise the type
            // failure is the form's failure (typecheck.md §7.3.2 step F).
            Err(type_err) => {
                state.body_frame.written_var_scope = Some(var_map);
                // The parameter route reads the trait through the same step,
                // so the two entrances to this constraint shape resolve
                // identically.
                if let Some(fq_trait) = self.resolve_annotation_trait(state, annotation, span) {
                    let home = &fq_trait.module;
                    let tn = &fq_trait.name;
                    let expr_ty = self.infer_expr(state, expr)?;
                    let resolved = self.apply_subst(state, &expr_ty);
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
                            if !self.has_impl_in_home(home, tn, &impl_ty) {
                                return Err(CranelispError::TypeError {
                                    message: format!(
                                        "type {impl_ty} does not implement trait {} \
                                         — a value-position constraint is a \
                                         satisfaction check (spec §3.3.3)",
                                        tn
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
                                    tn
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
                Err(type_err.into_form_error(state))
            }
        }
    }
}

#[cfg(test)]
mod tests;
