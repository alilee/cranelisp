use super::*;

/// Extract the user-fn reference edges added to `state.user_fn_refs` during
/// one form's checking (FIXME 0470, S101), attributed to `caller`.
///
/// Sibling of the `form_mr` span-set delta for `method_resolutions`: `before`
/// is the key snapshot taken at the top of `check_form_body_*`; everything
/// newer belongs to the form under check (including references inside nested
/// lambdas, which are inferred within the enclosing defn's body — the L-R2
/// carrier attribution).
fn extract_user_fn_ref_edges(
    state: &CheckState,
    caller: &Symbol,
    before: &HashSet<Span>,
) -> Vec<(Symbol, FQSymbol)> {
    state
        .user_fn_refs
        .iter()
        .filter(|(span, _)| !before.contains(span))
        .map(|(_, fq)| (caller.clone(), fq.clone()))
        .collect()
}

/// Group call graph edges by caller, sort + deduplicate, and write to `ModuleEntry`.
///
/// Used by both `merge_form_result` (eager write so the scheduler can read callees
/// immediately) and `finalize_check_result` (canonical final write that includes
/// any edges from post-passes).
///
/// **Completeness contract (FIXME 0470 + 0472, S101).** The edge feed is the
/// union of `ResolvedCall`-derived edges (trait methods, sig-dispatch,
/// auto-curry) and the `CheckState.user_fn_refs` recording (every
/// statically-resolved call- OR value-position reference to a
/// `DefKind::UserFn` `Def`), harvested by the ONE shared
/// `harvest_callee_edges` helper at every body-check seam: the two Pass-2
/// per-form seams (through this sink) AND the Pass-1
/// `finalize_impl_method_writeback` seam (impl-provided, default, and HKT
/// trait-method bodies — written directly to the mangled entry). A checked
/// entry's `callees` therefore names EVERY statically-resolved user-fn
/// reference in its body, with one deliberate residue: mono-instance bodies
/// (`recheck_body_for_mono`) carry no own edges — their constrained
/// TEMPLATE's entry carries the complete set and the call-site recorder gives
/// the caller→template edge, so the reverse closure is preserved through the
/// template chain. The S101 dependent-recompilation transaction derives its
/// reverse index from this set (`design/int/session-transaction.md`
/// §3.2/§3.3); silently dropping edges starves the affected-set closure.
/// Guarded by the `program::tests::callees_*` completeness-contract tests
/// (`tests/plan/s101-coverage-postmortem.md` §2.1).
pub(crate) fn write_callees_to_module_entries<C, L>(
    sym_table: &mut SymbolTable<C, L>,
    edges: &[(Symbol, FQSymbol)],
) where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let mut by_caller: HashMap<Symbol, Vec<FQSymbol>> = HashMap::new();
    for (caller, callee) in edges {
        by_caller
            .entry(caller.clone())
            .or_default()
            .push(callee.clone());
    }
    for (caller, mut callees) in by_caller {
        callees.sort_by(|a, b| {
            a.module
                .as_ref()
                .cmp(b.module.as_ref())
                .then(a.symbol.as_ref().cmp(b.symbol.as_ref()))
        });
        callees.dedup();
        // Per Submission 22: `ModuleEntry::Macro` retired. Macros are now
        // `ModuleEntry::Def` entries with `kind: DefKind::Macro { clauses_meta }`,
        // so the prior OR-pattern collapses to the single Def arm.
        if let Some(ModuleEntry::Def { callees: c, .. }) = sym_table.symbols.get_mut(&caller) {
            *c = callees;
        }
    }
}

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

    /// Extract call graph edges from method resolutions for a given caller.
    ///
    /// For each `ResolvedCall` in the provided map, derives the callee as an
    /// `FQSymbol`. `BuiltinFn` resolutions are skipped (always available).
    /// The caller symbol is the defn whose body produced these resolutions.
    pub(super) fn extract_call_graph_edges(
        &self,
        state: &CheckState,
        caller: &Symbol,
        method_resolutions: &HashMap<Span, ResolvedCall>,
    ) -> Vec<(Symbol, FQSymbol)> {
        let current_module = state.current_module.clone();
        let mut edges = Vec::new();

        for resolved in method_resolutions.values() {
            if let Some(callee) = self.resolved_call_to_fqsymbol(resolved, &current_module) {
                edges.push((caller.clone(), callee));
            }
        }

        edges
    }

    /// The ONE shared callee-edge harvest, applied at EVERY body-check seam
    /// (FIXME 0472 — the `codegen_view` precedent: one helper, all seams).
    ///
    /// Combines the two edge channels for the body just checked, attributed
    /// to `caller`:
    /// - `ResolvedCall`-derived edges from the caller-supplied
    ///   method-resolutions delta (trait methods, sig-dispatch, auto-curry);
    /// - the `CheckState.user_fn_refs` delta since `ufr_before` (every
    ///   statically-resolved call-/value-position user-fn reference,
    ///   FIXME 0470).
    ///
    /// Seams wired: `check_form_body_single_defn` / `check_form_body_multi_sig`
    /// (edges ride `FormCheckResult.call_graph_edges` into the merge/finalize
    /// sinks) and `finalize_impl_method_writeback` (impl-provided, default,
    /// and HKT trait-method bodies — Pass-1 bodies outside the per-form
    /// channel; edges written directly to the mangled entry, mirroring its
    /// `ast`/`codegen_view` direct writes). Deliberately NOT wired:
    /// `recheck_body_for_mono` — a mono instance's body duplicates its
    /// constrained TEMPLATE's body, whose edges are already complete via the
    /// template's own defn-form check, and the call-site recorder gives the
    /// caller→template edge; the reverse closure reaches the minting caller
    /// through the template chain, and mono instances are re-minted whenever
    /// that caller re-typechecks.
    pub(crate) fn harvest_callee_edges(
        &self,
        state: &CheckState,
        caller: &Symbol,
        method_resolutions_delta: &HashMap<Span, ResolvedCall>,
        ufr_before: &HashSet<Span>,
    ) -> Vec<(Symbol, FQSymbol)> {
        let mut edges = self.extract_call_graph_edges(state, caller, method_resolutions_delta);
        edges.extend(extract_user_fn_ref_edges(state, caller, ufr_before));
        edges
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
            ResolvedCall::SigDispatch { mangled_name } => {
                // Multi-sig variants are always local to the current module.
                Some(FQSymbol {
                    module: current_module.clone(),
                    symbol: Symbol::from(mangled_name.as_ref()),
                })
            }
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
