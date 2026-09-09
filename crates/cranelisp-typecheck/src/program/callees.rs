use super::*;

// --- Per-Form Typecheck API types ---

/// Pass indicator for `check_form()`.
///
/// The two-pass structure (register all signatures, then check all bodies) is
/// fundamental to Algorithm W with mutual recursion. The caller drives the
/// iteration; `check_form` does the right thing for each (form, pass) pair.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CheckPass {
    /// Pass 1: register type/trait/signature.
    /// For Defn: registers signature only. For TypeDef/TraitDecl/TraitImpl: full registration.
    Register,
    /// Pass 2: check function body, generalize, detect constraints.
    /// Only meaningful for Defn forms. Other form kinds return an empty result.
    CheckBody,
}

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    // =================================================================
    // Per-Form Typecheck API (v4 pipeline)
    // =================================================================

    /// The ONE shared callee-edge harvest, applied at EVERY body-check seam
    /// (FIXME 0472 — the `codegen_view` precedent: one helper, all seams).
    ///
    /// Combines the two edge channels for the body just checked, attributed
    /// to `caller`:
    /// - `ResolvedCall`-derived edges from the caller-supplied
    ///   method-resolutions delta (trait methods, sig-dispatch, auto-curry);
    /// - the completed `BodyFrame` user references (every
    ///   statically-resolved call-/value-position user-fn reference,
    ///   FIXME 0470).
    ///
    /// Top-level bodies retain [`Self::harvest_callees`] directly in the body
    /// ledger. This caller-attributed projection remains for
    /// `finalize_impl_method_writeback`, whose impl/default/HKT body settles at
    /// its local seam. Deliberately NOT wired:
    /// `recheck_body_for_mono` — a mono instance's body duplicates its
    /// constrained TEMPLATE's body, whose edges are already complete via the
    /// template's own defn-form check, and the call-site recorder gives the
    /// caller→template edge; the reverse closure reaches the minting caller
    /// through the template chain, and mono instances are re-minted whenever
    /// that caller re-typechecks.
    pub(crate) fn harvest_callees(
        &self,
        state: &CheckState,
        method_resolutions_delta: &HashMap<Span, ResolvedCall>,
        user_fn_refs: &HashMap<Span, FQSymbol>,
    ) -> Vec<FQSymbol> {
        self.harvest_callees_in_module(
            method_resolutions_delta,
            user_fn_refs,
            &state.current_module,
        )
    }

    pub(crate) fn harvest_callees_in_module(
        &self,
        method_resolutions_delta: &HashMap<Span, ResolvedCall>,
        user_fn_refs: &HashMap<Span, FQSymbol>,
        body_module: &ModuleFullPath,
    ) -> Vec<FQSymbol> {
        let mut callees: Vec<FQSymbol> = method_resolutions_delta
            .values()
            .filter_map(|resolved| self.resolved_call_to_fqsymbol(resolved, body_module))
            .chain(user_fn_refs.values().cloned())
            .collect();
        callees.sort_by(|a, b| {
            a.module
                .as_ref()
                .cmp(b.module.as_ref())
                .then(a.symbol.as_ref().cmp(b.symbol.as_ref()))
        });
        callees.dedup();
        callees
    }

    /// Derive the callee `FQSymbol` from a `ResolvedCall`, if it represents
    /// a user-defined dependency (not a builtin).
    pub(super) fn resolved_call_to_fqsymbol(
        &self,
        resolved: &ResolvedCall,
        current_module: &ModuleFullPath,
    ) -> Option<FQSymbol> {
        match resolved {
            ResolvedCall::TraitMethod {
                mangled_name,
                impl_module,
                ..
            } => {
                // S110 W0.1b (§1.1.1): the mangled method `Def` is STORED in the
                // impl-WRITER's module, carried on the resolution as
                // `impl_module` (read off the `TraitImpl` shell in
                // `try_resolve_trait_method`). This is the callees.rs "Step 5"
                // resolution — never `current_module`, which is wrong for a
                // cross-module trait call. Also repairs the S101 reverse index.
                Some(FQSymbol {
                    module: impl_module.clone(),
                    symbol: Symbol::from(mangled_name.as_ref()),
                })
            }
            ResolvedCall::SigDispatch { target } => match target {
                cranelisp_types::CallableTarget::Binding(owner)
                | cranelisp_types::CallableTarget::OverloadArm { owner, .. }
                | cranelisp_types::CallableTarget::MacroClause { owner, .. } => Some(owner.clone()),
                _ => None,
            },
            ResolvedCall::AutoCurry {
                trait_resolution, ..
            } => {
                // If there's an inner trait resolution, derive the edge from it.
                if let Some(inner) = trait_resolution {
                    self.resolved_call_to_fqsymbol(inner, current_module)
                } else {
                    // Plain-fn curry — NO edge from this path (FIXME 0619 leg 3).
                    // The old `{current_module, target}` derivation was WRONG for
                    // an imported curry target (target lives in its home module,
                    // not the caller's) and spurious for a local target. The
                    // correct edge lands via the OTHER channel: `infer_var`
                    // records the callee `Var` into `user_fn_refs` with the
                    // terminal storage home (the same source the carrier's
                    // callee-span transport reads — `mono_collect::resolve_auto_curry`),
                    // so the plain-fn curry callee is covered there, in agreement
                    // with the carrier. Recording a wrong-module duplicate here
                    // only starved/mis-named the S101 reverse index.
                    None
                }
            }
            ResolvedCall::BuiltinFn { .. } => {
                // Builtins are always available — no codegen dependency.
                None
            }
            // `ResolvedCall` is `#[non_exhaustive]` per Decision 47 / S69
            // Submission 32. Future variants land here; they default to "no
            // call graph edge" until the call-graph maintainers wire them.
            _ => None,
        }
    }

    /// Derive the STORAGE FQ the backend keys its ONE fetch on for a
    /// dispatch-leg selection (S110 0583, `design/arch/backend-keyed-consumer.md`
    /// §1.1) — the Apply-span `apply_refs` `ApplyRef::Dispatch` carrier (S114
    /// carrier flip — was the `resolved_targets` carrier the W0 writer never
    /// produced, FIXME 0616 leg 1). Called alongside every `resolved_calls`
    /// insert at a dispatch-selection seam ("recording happens where resolution
    /// happens", Principle 24).
    ///
    /// Unlike [`Self::resolved_call_to_fqsymbol`] (the `callees` projection,
    /// which drops builtins as non-dependencies) this INCLUDES the `BuiltinFn`
    /// arm: the primitive/operator leg is the named W1 failure scenario
    /// (`(+ 1 2)` — operators are trait methods short-circuited to `add-i64`).
    /// The module derivation for TraitMethod / SigDispatch / AutoCurry is
    /// single-sourced on `resolved_call_to_fqsymbol` (Principle 7), so the
    /// carrier and the `callees` edge agree on the mangled entry's home.
    pub(crate) fn dispatch_target_fq(
        &self,
        state: &CheckState,
        resolved: &ResolvedCall,
    ) -> Option<FQSymbol> {
        match resolved {
            ResolvedCall::BuiltinFn { .. } => None,
            other => self.resolved_call_to_fqsymbol(other, &state.current_module),
        }
    }

    /// Record the dispatch-leg carrier for a just-inserted `ResolvedCall`
    /// (FIXME 0616 leg 1) — the ONE-line companion of a
    /// `state.method_resolutions.resolved_calls.insert(span, resolved)` at a
    /// seam that writes through `state`. Keyed at the same (Apply) span.
    ///
    /// **Carrier-identity precondition (§11.8.8, W3-review Important-1).** A
    /// dispatch is recorded ONLY where the callee resolves to its TABLE/carrier
    /// identity — trait method, overload, or primitive. A callee that is a §4.6
    /// LOCAL SHADOW (a `let`/`fn`/param binding masking a same-named
    /// trait/primitive, `(let [+ (fn [a b] 0)] (+ 1 2))`) is an INDIRECT call on
    /// the local closure's own scheme and records NO dispatch carrier here: its
    /// `infer_apply` resolution seams gate on
    /// [`CheckState::resolves_to_carrier_identity`] first, so a shadowed name
    /// never reaches this recorder (mis-dispatch → the trait method would be a
    /// spec §4.6 violation).
    pub(crate) fn record_dispatch_target(
        &self,
        state: &mut CheckState,
        span: Span,
        resolved: &ResolvedCall,
    ) {
        if let Some(fq) = self.dispatch_target_fq(state, resolved) {
            state
                .method_resolutions
                .apply_refs
                .insert(span, cranelisp_types::ApplyRef::Dispatch(fq));
        }
    }

    pub(crate) fn settle_dispatch(
        &self,
        state: &mut CheckState,
        span: Span,
        dispatch: crate::checker::PendingDispatch,
    ) -> ResolvedCall {
        match dispatch {
            crate::checker::PendingDispatch::Builtin(builtin) => {
                state.method_resolutions.apply_refs.insert(
                    span,
                    cranelisp_types::ApplyRef::Dispatch(builtin.storage_fq),
                );
                ResolvedCall::BuiltinFn {
                    name: builtin.jit_name,
                }
            }
            crate::checker::PendingDispatch::Resolved(resolution) => {
                self.record_dispatch_target(state, span, &resolution);
                resolution
            }
        }
    }
}

#[cfg(test)]
mod tests;
