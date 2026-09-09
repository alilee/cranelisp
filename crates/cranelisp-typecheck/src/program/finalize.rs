use super::*;
use cranelisp_types::Scheme;
mod ambiguity;
#[cfg(test)]
pub(super) use ambiguity::AmbiguousForm;

pub(crate) fn collect_expr_spans(expr: &Expr, spans: &mut HashSet<Span>) {
    spans.insert(expr.span());
    for_each_child_expr(expr, |child| collect_expr_spans(child, spans));
}

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Merge a `FormCheckResult` into the module's accumulator.
    ///
    /// Called after each `check_form()` to accumulate the remaining per-form
    /// products. Resolution, expression and callee facts have longer-lived
    /// owners and do not travel through this carrier.
    pub(crate) fn merge_form_result(
        &self,
        _module: &ModuleFullPath,
        state: &mut CheckState,
        accumulator: &mut ModuleCheckAccumulator,
        result: FormCheckResult,
    ) {
        self.merge_form_result_inner(state, accumulator, result);
    }

    pub(super) fn merge_form_result_inner(
        &self,
        _state: &mut CheckState,
        accumulator: &mut ModuleCheckAccumulator,
        result: FormCheckResult,
    ) {
        if let Some(name) = result.constrained_fn {
            accumulator.constrained_fn_names.insert(name);
        }
        accumulator.mono_defns.extend(result.mono_defns);
        accumulator
            .default_method_defns
            .extend(result.default_method_defns);
        accumulator.multi_sig_defns.extend(result.multi_sig_defns);
        accumulator.warnings.extend(result.warnings);
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
    /// Finalize: run post-passes and drain the accumulator into `CheckResult`.
    pub(crate) fn finalize_check_result(
        &self,
        _module: &ModuleFullPath,
        state: &mut CheckState,
        accumulator: &mut ModuleCheckAccumulator,
        working_program: &[TopLevel],
        strategy: ModuleStrategy,
    ) -> Result<CheckResult, CranelispError> {
        self.finalize_check_result_inner(state, accumulator, working_program, strategy)
    }

    /// Re-generalize every checked body's scheme from its registered source vars
    /// resolved through the current global substitution, and clear any
    /// false-positive constrained-fn markers whose schemes ended up
    /// constraint-free.
    ///
    /// Run once after body-checking (the original Phase-2 generalization) and
    /// AGAIN after monomorphisation (FIXME 0349): pass4's call-site result
    /// propagation can pin a caller's previously-loose result var (a
    /// forward-referenced callee left it polymorphic), and re-running this makes
    /// the caller's stored scheme reflect that pinning — turning a spuriously
    /// polymorphic caller (`main : (Fn [] (IO t))`) into its true monomorphic
    /// form (`main : (Fn [] (IO Int))`). Idempotent for defns whose source vars
    /// did not move between calls.
    pub(super) fn regeneralize_defn_schemes(
        &self,
        state: &mut CheckState,
        accumulator: &ModuleCheckAccumulator,
    ) -> Result<(), CranelispError> {
        for body in accumulator.bodies.checked_bodies() {
            let registration = &body.registration;
            let fn_type = Type::Fn(
                registration
                    .param_types
                    .iter()
                    .map(|t| self.apply_subst(state, t))
                    .collect(),
                Box::new(self.apply_subst(state, &registration.ret_ty)),
            );
            let scheme = self.generalize(state, &fn_type);
            self.current_symbol_table_mut(state)
                .update_declared_scheme(&registration.publication_name, scheme)
                .map_err(crate::result::lifecycle_error)?;
        }

        Ok(())
    }

    /// Re-generalize checked source bodies after the overload drain, which may
    /// have supplied their last return-type constraint. Every body remains
    /// `Life::Declared` at this point, so the exact ledger population is the
    /// scope. Test-root specialization runs afterward and therefore cannot be
    /// overwritten by this source-monotype refresh.
    pub(super) fn regeneralize_only_polymorphic(
        &self,
        state: &mut CheckState,
        accumulator: &ModuleCheckAccumulator,
    ) -> Result<(), CranelispError> {
        for body in accumulator.bodies.checked_bodies() {
            let registration = &body.registration;
            let fn_type = Type::Fn(
                registration
                    .param_types
                    .iter()
                    .map(|t| self.apply_subst(state, t))
                    .collect(),
                Box::new(self.apply_subst(state, &registration.ret_ty)),
            );
            let scheme = self.generalize(state, &fn_type);
            self.current_symbol_table_mut(state)
                .update_declared_scheme(&registration.publication_name, scheme)
                .map_err(crate::result::lifecycle_error)?;
        }

        Ok(())
    }

    /// Re-settle the stored schemes of already-determined **`Polymorphic`**
    /// cluster members from their registered body monotypes through the
    /// current global substitution — scheme-only, no re-slotting (FIXME 0488
    /// sig c).
    ///
    /// **The ordering bug this fixes.** A fn that FORWARD-references a
    /// same-cluster helper (`vreduce` calling the later-defined `vreduce-loop`)
    /// has its 0344 generalize-writeback run at the END of its OWN body check —
    /// BEFORE the helper's body ties the accumulator↔result vars. The writeback
    /// therefore freezes an UNDER-tied scheme (`vreduce : (Fn [f a (Vec b)] c)`,
    /// result untied). A LATER sibling (`vconcat = (vreduce vec-push va vb)`)
    /// then instantiates that stale scheme and inherits the under-tie into its
    /// OWN scheme (`(Fn [a (Vec b)] c)`), which fails pass-4's all-args-concrete
    /// guard at every composed consumer turn (`undefined function: <outer>`).
    /// `finalize`'s [`Self::regeneralize_defn_schemes`] re-ties the
    /// forward-referencing fn correctly — but only AFTER the sibling's body was
    /// already checked against the stale scheme.
    ///
    /// Running this once BEFORE each subsequent form's body check settles the
    /// forward-reference chain (`vreduce-loop`'s body has run → its ties are in
    /// `state.subst` → `vreduce` re-ties) so the sibling sees the tied scheme.
    /// It re-runs the SAME idempotent generalization `finalize` already
    /// performs, only earlier; it does not change HOW generalization computes.
    ///
    /// **Scoped by construction (does not touch the 0344 balance).** A sibling
    /// that USES a member instantiates a FRESH copy of the member's (now
    /// generalized) scheme, so re-generalizing the member later never disturbs
    /// the sibling's already-done inference — it only picks up ties from the
    /// member's OWN forward-referenced helpers. Restricted to already-determined
    /// `Polymorphic` templates (`NotDetermined` = not-yet-body-checked members
    /// are skipped so a forward reference still binds their shared Pass-1 vars,
    /// which 0349's mono-time result pinning relies on) and gated constraint-free
    /// (mirroring the 0344 body-check writeback) so a `Constrained` fn's mono
    /// Pass-1 entry is never disturbed. Concrete members carry no re-tieable vars
    /// and are skipped after a cheap lookup.
    pub(super) fn resettle_polymorphic_schemes(
        &self,
        state: &mut CheckState,
        accumulator: &ModuleCheckAccumulator,
    ) -> Result<(), CranelispError> {
        for body in accumulator.bodies.checked_bodies() {
            let registration = &body.registration;
            // This pre-sibling refresh is the former `Polymorphic`-only gate.
            // Checked bodies remain `Life::Declared` until final publication,
            // so lifecycle state can no longer distinguish a pure-parametric
            // body from an eagerly detected constrained body. The accumulator
            // owns that checked-body classification during this window.
            if accumulator
                .constrained_fn_names
                .contains(&registration.publication_name)
            {
                continue;
            }
            let fn_type = Type::Fn(
                registration
                    .param_types
                    .iter()
                    .map(|t| self.apply_subst(state, t))
                    .collect(),
                Box::new(self.apply_subst(state, &registration.ret_ty)),
            );
            let scheme = self.generalize(state, &fn_type);
            // Pure-parametric only (mirror the 0344 writeback gate). A scheme
            // that acquired constraints is left to the constrained-fn path.
            if !scheme.constraints.is_empty() {
                continue;
            }
            self.current_symbol_table_mut(state)
                .update_declared_scheme(&registration.publication_name, scheme)
                .map_err(crate::result::lifecycle_error)?;
        }
        Ok(())
    }

    /// Phase 3 (finalize): re-resolve deferred trait calls with the final
    /// substitution across every defn body (`program-decomposition.md` §2.1 P1).
    /// Per-defn resolution already ran in `check_form_body`, but cross-defn
    /// substitution refinement (e.g. constrained fns pinned by call sites) may
    /// enable additional resolutions. Updates the side maps for backward
    /// compatibility; AST annotation is already done per-defn. A multi-sig defn
    /// fans per `__v{i}` variant (the register-side internal-defn keys).
    pub(super) fn reresolve_deferred_calls(
        &self,
        state: &mut CheckState,
        working_program: &[TopLevel],
    ) -> Result<(), CranelispError> {
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
                                body: variant.body.clone(),
                                span: variant.span,
                            }],
                            visibility: defn.visibility,
                            span: variant.span,
                        };
                        self.resolve_deferred_trait_calls(state, internal_defn.body())?;
                        self.resolve_value_position_trait_methods(
                            state,
                            internal_defn.body(),
                            false,
                        )?;
                    }
                } else {
                    self.resolve_deferred_trait_calls(state, defn.body())?;
                    self.resolve_value_position_trait_methods(state, defn.body(), false)?;
                }
            }
        }
        Ok(())
    }

    /// Pass 3 (finalize): the complete set of constrained/parametric fn names to
    /// monomorphise (`program-decomposition.md` §2.1 P3) — the per-cluster
    /// `detect_constrained_fns` result, the accumulator carry (prior REPL evals),
    /// plus (Additive strategy only) a live-table scan for cross-call
    /// constrained / polymorphic-with-ast fns.
    pub(super) fn collect_all_constrained_names(
        &self,
        state: &mut CheckState,
        single_sig_defns: &[&Defn],
        accumulator: &mut ModuleCheckAccumulator,
        strategy: ModuleStrategy,
    ) -> HashSet<Symbol> {
        let mut constrained_fn_names = self.detect_constrained_fns(state, single_sig_defns);

        // Add previously-accumulated constrained fns and those from prior REPL evals
        constrained_fn_names.extend(accumulator.constrained_fn_names.drain());

        if strategy == ModuleStrategy::Additive {
            let r = self.current_symbol_table(state);
            for (name, entry) in r.view().iter() {
                if entry.callable().is_some_and(|callable| {
                    matches!(
                        callable.arm.life,
                        Life::Template {
                            body: TemplateBody::Ast(_),
                            ..
                        }
                    )
                }) {
                    constrained_fn_names.insert(name.clone());
                }
            }
        }

        constrained_fn_names
    }

    /// Sweep post-pass outputs from `state` into the accumulator. Post-passes
    /// (resolve_deferred_trait_calls, pass4_monomorphise, resolve_pending_overloads,
    /// resolve_auto_curry) write new method resolutions into
    /// `state.method_resolutions`; merge these into the accumulator so it becomes
    /// the single authoritative source.
    pub(super) fn sweep_post_pass_outputs(
        &self,
        state: &mut CheckState,
        accumulator: &mut ModuleCheckAccumulator,
    ) {
        accumulator.resolutions = std::mem::take(&mut state.method_resolutions);
        accumulator
            .expr_types
            .extend(std::mem::take(&mut state.expr_types));
        accumulator
            .warnings
            .extend(std::mem::take(&mut state.warnings));
    }

    pub(super) fn finalize_check_result_inner(
        &self,
        state: &mut CheckState,
        accumulator: &mut ModuleCheckAccumulator,
        working_program: &[TopLevel],
        strategy: ModuleStrategy,
    ) -> Result<CheckResult, CranelispError> {
        // Phase 2: generalize all functions (matching pass2_check_bodies Phase 2).
        // Clear false-positive constrained markers.
        self.regeneralize_defn_schemes(state, accumulator)?;

        // Phase 3: re-resolve deferred trait calls with final substitution.
        // Propagates the F-D2-10 no-impl reject (nullary return-dispatch to a
        // type with no impl) as a located typecheck error.
        self.reresolve_deferred_calls(state, working_program)?;

        // Pass 2.5: resolve multi-sig overloads.
        // Side effect: registers mangled variants on the symbol table.
        // The returned Vec<Defn> was carried on CheckResult.default_method_defns
        // pre-slim; no longer needed — mangled entries live on SymbolTable.
        // `multi_sig_mangled_names` (base → [mangled]) IS needed below: the
        // re-annotation block re-keys multi-sig variant entries by their mangled
        // names (the internal `{name}__v{i}` keys are gone post-registration).
        let mut multi_sig_mangled_names = MangledNamesByBase::new();
        let _multi_sig_defns = self.resolve_multi_sig_overloads(
            state,
            working_program,
            accumulator,
            &mut multi_sig_mangled_names,
        )?;

        // Pass 3: detect constrained polymorphic functions (cluster result +
        // accumulator carry + Additive live-table scan).
        let single_sig_defns = Self::collect_single_sig_defns(working_program);
        let constrained_fn_names =
            self.collect_all_constrained_names(state, &single_sig_defns, accumulator, strategy);

        // Instance demands are derived after overload back-flow and scheme
        // settlement below; nested rechecks must see that same settled scheme.

        // S84 Wave 1b (FIXME 0374/0378 issue 3): register discovered `test-*`
        // entry points as monomorphisation ROOTS — mint a concrete
        // `(Fn [] (Option String))` instance under the bare name for any
        // slot-less `Polymorphic` degenerate test fn (`(defn test-x [] None)`).
        // Run AFTER both `regeneralize_defn_schemes` passes so the regeneralize's
        // unconditional scheme-writeback cannot demote the minted concrete
        // scheme back to `(Option a)`. The discovery readers
        // (`discover_test_names` / `discover_eligible_tests`) read the concrete
        // instance's slot under the same name.
        // Pass 5: drain the deferred multi-sig/overload resolutions and
        // auto-curry. This is the TOP-LEVEL drain of `state.pending_overload_
        // resolutions`, which `infer.rs` fills whenever a call targets an
        // overloaded base (it mints a fresh return var and defers, NOT resolving
        // per-defn). It unifies each deferred call's return var with the selected
        // variant's concrete return and records the `SigDispatch` resolution at
        // the call span. (Corrects the former "already resolved per-defn" comment
        // — I1: nothing drains per-defn; this ordering is load-bearing for the
        // LEG-2 value scan below.) NOTE (§11.8.3 Important 1): `recheck_body_for_
        // mono` runs a SECOND, SCOPED invocation over the isolated pendings a mono
        // body defers, so its inner multi-sig dispatch carriers land in the mono
        // view — the outer pendings here are unaffected by that scoped drain.
        self.resolve_pending_overloads(state, Some(&accumulator.bodies))?;
        // S115 W4 — the SETTLED auto-curry window. Re-admit every entry a
        // pre-settlement body drain held back because its only carrier was a
        // trait-method-declaration FQ (`mono_collect::AutoCurryDrain`); by here
        // the call sites have pinned the operand types, so the operator
        // re-resolves to its real impl (`primitives/eq-i64`) and rides a slotted
        // carrier. This is the ONE drain of `deferred_auto_curry` — never inside
        // a mono/impl body recheck, whose resolution maps and module scope are
        // swapped.
        let deferred = std::mem::take(&mut state.deferred_auto_curry);
        state.pending_auto_curry.splice(0..0, deferred);
        self.resolve_auto_curry(state, AutoCurryDrain::Final);

        // S110 C-4 — re-settle any caller whose stored scheme was left spuriously
        // `Polymorphic` because the call in its body was an overloaded/multi-arity
        // dispatch DEFERRED past the FIXME-0349 re-generalize above. `(defn main []
        // (Pure (h 7)))` calling `(defn h ([:Int x] x) …)` defers `(h 7)` at
        // `infer.rs` (the `state.overloads` guard mints a fresh return var and
        // pushes a `pending_overload_resolution`); only `resolve_pending_overloads`
        // (just above) unifies that var with the selected variant's concrete `Int`
        // return. That runs AFTER the re-generalize that fixed `main`'s scheme, so
        // `main` was generalized while its return var was still free → quantified →
        // slot-less `Polymorphic`, which the backend correctly declines to codegen
        // (the "entry module has no `main` function" `--run`/`--link` misdirect; the
        // REPL face is the §3.11 ambiguity on `main$`).
        //
        // This SCOPED pass re-runs the idempotent generalize+reslot ONLY for entries
        // currently in the `Polymorphic` state (its `regeneralize_only_polymorphic`
        // gate SKIPS `Concrete` entries), so it collapses such a `main` to its true
        // `(Fn [] (IO Int))` `Concrete{slot}` WITHOUT touching the concrete schemes
        // minted by `register_test_fn_mono_roots` above — a BLANKET third
        // `regeneralize_defn_schemes` would overwrite a mono-root's minted concrete
        // scheme back to its polymorphic registered signature (the finalize ordering
        // hazard the mono-root comment guards; `test_fn_registered_as_mono_root_
        // gets_concrete_instance`). Genuinely polymorphic defns (`(defn empty []
        // [])`, scheme stays `(Fn [] (Vec a))`) are non-concrete after
        // re-generalize and stay `Polymorphic`.
        self.regeneralize_only_polymorphic(state, accumulator)?;

        // Test entry roots are the final scheme refinement for their checked
        // ledger records. Run after every source-monotype re-generalization so
        // the concrete `(Option String)` root cannot be overwritten before the
        // one publication window.
        self.register_test_fn_mono_roots(state, &mut accumulator.bodies)?;

        // §3.11.1 value-position scan for ALL top-level forms — single-clause
        // defns, `__expr`, AND multi-arity clauses (S112 leg a: the former
        // pre-drain `ClauseIndependence` leg is collapsed into this ONE post-drain
        // pass). It runs AFTER `resolve_pending_overloads` (so a clause pinned by a
        // sibling self-call — `rp4`'s `p`/`rot` — has acquired the concrete param
        // types the back-flow gives it: §5.1.2; and a deferred-overload return var
        // in a value position — `(let [r (h 7)] r)` — is unified to the variant's
        // concrete return: B1) AND AFTER `regeneralize_only_polymorphic` (so a
        // caller left spuriously `Polymorphic` at drain time is collapsed to
        // `Concrete`, its unpinned-`[]` body then SCANNED rather than poly-skipped:
        // B2). It stays BEFORE `sweep_post_pass_outputs` (below), which drains
        // `state.expr_types` that both this scan and `collect_unresolved_dispatch`
        // read by span.
        if let Some(amb) = self.find_ambiguous_top_level_form(state, accumulator, working_program) {
            return Err(CranelispError::TypeError {
                message: amb.message(),
                location: ErrorLocation::from_span(amb.span),
            });
        }

        // The unresolved-return-poly-dispatch signal (carrier (A), FIXME 0611
        // ratified; `design/typecheck/return-poly-dispatch-signal.md` §3.1). int
        // applies this at the entry/eval-result boundary it owns (Principle 19).
        // Computed HERE — POST-drain alongside the LEG-2 value scan, BEFORE
        // `sweep_post_pass_outputs` drains `state.expr_types` — so the
        // dispatch-outcome read (`method_return_dispatch_type`, which reads the
        // per-span recorded type) sees the settled types, NOT an emptied map. The
        // drain does not resolve trait-method dispatch (that is
        // `reresolve_deferred_calls`, above), so this signal is unchanged by the
        // move; it is co-located with LEG 2 to keep the two span-map readers
        // adjacent within the same pre-sweep window. EMPTY for every valid program.
        let unresolved_dispatch = self.collect_unresolved_dispatch(state, working_program);

        // Post-drain multi-sig variant finalisation (S112 leg a §11.3(B), extends
        // the S91 Wave-7 / FIXME 0432 Face A return-type refresh). Runs AFTER the
        // drain so the §5.1.2 back-flow has settled every clause's params: Phase A
        // promotes a back-flow-pinned clause (registered as a `$Var` `Polymorphic`
        // template pre-drain) to its `Concrete{slot}` sibling under the concrete
        // mangle — the exact name the drain's concrete branch recorded in each
        // caller's `SigDispatch`; Phase B refreshes persisted return types so a
        // later REPL cluster sees the concrete return (not a stale `:a`). It
        // mutates `multi_sig_mangled_names` to re-point at the concrete siblings so
        // the `finalize_annotations_and_publish` re-annotation below targets them.
        self.finalize_multi_sig_variant_types(
            state,
            working_program,
            accumulator,
            &mut multi_sig_mangled_names,
        )?;

        // §11.8.3 leg D3 — the SECOND mono-harvest settlement point. Now that
        // `finalize_multi_sig_variant_types` (Phase A) has settled every multi-sig
        // clause concrete, scan the MULTI-SIG clause bodies for inner mono call
        // sites (a poly hop like `(idpoly n)` inside `build`'s clause body). The
        // single-sig pass-4 above (line ~1015) filtered every multi-sig defn out
        // (`Defn::body()` panics on them), so a poly callee reached only from a
        // multi-sig clause body was never enqueued → codegen `undefined function`.
        // This is the SAME `pass4_monomorphise` harvest (arch W2a pin — one
        // parameterized fn at two settlement points, not a forked sibling),
        // invoked with the complementary `MultiSig` family. Runs BEFORE the sweep
        // below so the minted SigDispatch carriers reach the accumulator that
        // `finalize_annotations_and_publish` rebuilds each mangled variant's
        // `codegen_view` from. Legs R2 (inner multi-sig-dispatch) and R1 (inline
        // gate) ride the shared `monomorphise_call`/`infer_apply` seams, firing for
        // any minted body regardless of which settlement point drove it.
        let multi_sig_defns =
            Self::collect_defns_for_mono(working_program, MonoDefnFamily::MultiSig);
        debug_assert_eq!(
            single_sig_defns.len() + multi_sig_defns.len(),
            working_program
                .iter()
                .filter(|t| matches!(t, TopLevel::Defn(_)))
                .count(),
            "the SingleSig + MultiSig mono-harvest families MUST partition every \
             top-level Defn exactly once (arch W2a pin — complementary AND total); \
             a later-added defn family that reaches neither is this assert's job to \
             catch loudly"
        );
        self.pass4_monomorphise(
            state,
            &multi_sig_defns,
            &constrained_fn_names,
            &mut accumulator.bodies,
        )?;

        // MC-X4 / MC-X4b — the SINGLE-SIG consumer RE-HARVEST at the settlement
        // point (P26 — record from settled state). A poly callee consuming a
        // MULTI-SIG fn's bare return (`(mycount (build 3))` in a single-sig body,
        // or `(unwrap (build 3))` over an explicit generic ADT field) had its arg type — the
        // multi-sig call's RESULT — as a residual `Var` at the PRE-drain single-sig
        // pass-4 (line ~1023), because a multi-sig call's return settles only in the
        // drain (`resolve_pending_overloads`) + Phase A. So `collect_mono_call_sites`'
        // concreteness gate SKIPPED the consumer's call and no ground `mycount$Vec$Int`
        // / `unwrap$Box` instance minted → codegen `undefined function`.
        //
        // Now that the drain + `finalize_multi_sig_variant_types` have settled every
        // multi-sig return, RE-RUN the single-sig harvest: `resolve_expr_types`
        // re-derives each consumer's arg type through the now-settled `state.subst`
        // (→ concrete), so the instance mints and its call-site carrier lands — both
        // reach the `finalize_annotations_and_publish` codegen-view rebuild below
        // (Phase 5). Idempotent for the instances the pre-drain pass already minted:
        // `register_mono_entry` preserves the existing `got_slot`, and the
        // concreteness gate re-admits the same concrete args. Runs in the SAME
        // post-settlement / pre-sweep window as the D3 MultiSig harvest above (the
        // §11.8.3 "one parameterized fn at two settlement points" precedent, extended
        // to the single-sig consumer face). `class=carrier-loss`.
        self.pass4_monomorphise(
            state,
            &single_sig_defns,
            &constrained_fn_names,
            &mut accumulator.bodies,
        )?;

        // Sweep post-pass outputs from self.state into the accumulator (the
        // single authoritative source for the final CheckResult).
        self.sweep_post_pass_outputs(state, accumulator);

        // Phase 5: final callee write + re-annotate every defn/impl AST from the
        // settled side maps + subst, rebuilding each `Concrete{slot}`
        // codegen_view post-mono.
        self.finalize_annotations_and_publish(
            state,
            accumulator,
            working_program,
            &multi_sig_mangled_names,
        )?;

        // Pass 5: interprocedural ownership inference (S102 CS-1..4;
        // `design/typecheck/ownership-inference.md`). A post-pass over the
        // now-settled cluster — mono done, callees written, `codegen_view`
        // rebuilt post-mono. Read-path increment: summaries are emitted but
        // UNconsumed by codegen (backend mechanisms are Wave 11), so the pass
        // is behaviour-neutral. Toggle-gated at its entry (`CRANELISP_NO_OWNERSHIP`
        // set ⇒ emits nothing, §13.5).
        crate::ownership::run_pass5(self, state);

        // Build CheckResult from the accumulator (authoritative source).
        // Sprint 57 Wave 2 step 4: CheckResult slimmed to `{ warnings, display }`.
        // The legacy `method_resolutions` / `expr_types` / `mono_defns` /
        // `constrained_fn_names` / `default_method_defns` fields were retired —
        // their data lives on annotated AST nodes and `ModuleEntry::Def` entries
        // (symbol-table registrations above are the durable carriers).
        let result = CheckResult {
            warnings: std::mem::take(&mut accumulator.warnings),
            display: None,
            // Computed above (before the `expr_types` sweep) — the 0611 carrier.
            unresolved_dispatch,
        };

        Ok(result)
    }

    /// Phase 5 (finalize) tail — the AST re-annotation / re-key / publish pass
    /// extracted from `finalize_check_result_inner` (`program-decomposition.md`
    /// §2.1 P5). Reads the now-settled side maps + subst; the callee writeback
    /// is the 0472 seam and the per-`Concrete{slot}` `codegen_view` rebuild is
    /// the post-mono view (§10.2 pattern-ctor sidecar threaded through).
    pub(super) fn finalize_annotations_and_publish(
        &self,
        state: &mut CheckState,
        accumulator: &mut ModuleCheckAccumulator,
        working_program: &[TopLevel],
        _multi_sig_mangled_names: &MangledNamesByBase,
    ) -> Result<(), CranelispError> {
        // Resolve all accumulated expr_types through the final substitution.
        let resolved_expr_types: HashMap<Span, Type> = accumulator
            .expr_types
            .iter()
            .map(|(span, ty)| (*span, apply(&state.subst, ty)))
            .collect();

        // Step 1b: AST annotation is primarily per-defn (check_form_body_single_defn,
        // check_form_body_multi_sig, check_impl_method, check_hkt_impl_method,
        // monomorphise_call). However, cross-defn substitution refinement (e.g.,
        // constrained fns pinned by call sites) and batch post-passes (Phase 3
        // re-resolve, Pass 5 overloads/auto-curry) may add new resolutions after
        // per-defn annotation. Re-annotate ASTs that have new information.
        //
        // S84 ConcreteType arc (FIXME 0394/0395): final publication consumes the
        // checked-body ledger only after mono/dispatch settlement, annotates from
        // `accumulator.resolutions`, and builds each `Concrete` codegen view in
        // that same atomic settlement. No body/view was published earlier.
        //
        // Scope: only a `UserFn { Concrete{slot} }` entry is a body-AST-node-typed
        // codegen target (§3.1.1) — its view is the one the backend backstop
        // guards. Mono-instance entries already populated their post-mono view at
        // the `register_mono_entry` seam (their bodies are built post-subst with
        // the dispatch already resolved); they are not re-walked here.
        {
            // Snapshot the pattern-ctor sidecar BEFORE the mutable symbol-table
            // borrow — `current_symbol_table_mut(state)` borrows `state` mutably,
            // so the codegen-view rebuild inside the closure cannot also read
            // `state.method_resolutions` (§10.2 requires the sidecar to reach
            // `from_expr`). The map is per-cluster (spans → FQSymbols), cheap.
            let pattern_ctors_for_views = accumulator.resolutions.pattern_ctors.clone();
            let var_refs_for_views = accumulator.resolutions.var_refs.clone();
            let apply_refs_for_views = accumulator.resolutions.apply_refs.clone();
            let sym_table = &mut self.current_symbol_table_mut(state);
            // Reannotate `existing` from the final side maps + subst, then, for a
            // `Concrete{slot}` codegen target, rebuild `codegen_view` from the
            // refreshed (post-mono) variant. Returns `Result` (S114 carrier
            // flip): `build_concrete_codegen_view` propagates the located
            // `ViewBuildError::Unresolved` gate error rather than swallowing a
            // real-span resolution miss into the lenient fallback.
            let reannotate_and_refresh_view = |name: &Symbol,
                                               sym_table: &mut SymbolTable<C, L>,
                                               resolved_expr_types: &HashMap<Span, Type>,
                                               method_resolutions: &HashMap<Span, ResolvedCall>,
                                               subst: &Subst|
             -> Result<(), CranelispError> {
                let Some(callable) = sym_table
                    .get(name.as_ref())
                    .and_then(Binding::callable)
                    .cloned()
                else {
                    return Ok(());
                };
                let scheme = callable.arm.scheme.clone();
                let (mut existing, kind, callees) = match callable.arm.life {
                    Life::Concrete {
                        ast: Some(ast),
                        callees,
                        ..
                    } => (ast, None, callees),
                    Life::Template {
                        body: TemplateBody::Ast(ast),
                        kind,
                        callees,
                    } => (ast, Some(kind), callees),
                    _ => return Ok(()),
                };
                annotate_variant_from_maps(&mut existing, resolved_expr_types, method_resolutions);
                apply_subst_to_variant(subst, &mut existing);
                if let Some(kind) = kind {
                    sym_table
                        .settle_checked_template(name, scheme, existing, kind, callees)
                        .map_err(crate::result::lifecycle_error)?;
                } else if let Some(view) = build_concrete_codegen_view(
                    name,
                    &existing,
                    &scheme,
                    &pattern_ctors_for_views,
                    &var_refs_for_views,
                    &apply_refs_for_views,
                )? {
                    sym_table
                        .settle_checked_concrete(name, scheme, existing, view, callees)
                        .map_err(crate::result::lifecycle_error)?;
                }
                Ok(())
            };
            // Impl registration has already resolved the trait and target and
            // minted the exact method symbols. Re-annotation consumes those
            // settled names directly; reconstructing them from `TraitImpl`
            // syntax would discard canonical identity (Principles 24 and 26).
            for defn in &accumulator.default_method_defns {
                reannotate_and_refresh_view(
                    &defn.name,
                    sym_table,
                    &resolved_expr_types,
                    &accumulator.resolutions.resolved_calls,
                    &state.subst,
                )?;
            }
        }

        let checked_bodies = std::mem::take(&mut accumulator.bodies).into_checked()?;
        let mut overload_drafts: HashMap<Symbol, Vec<(usize, Symbol, CallableArmDraft)>> =
            HashMap::new();
        for mut checked in checked_bodies {
            let name = checked.registration.publication_name.clone();
            annotate_variant_from_maps(
                &mut checked.ast,
                &resolved_expr_types,
                &accumulator.resolutions.resolved_calls,
            );
            apply_subst_to_variant(&state.subst, &mut checked.ast);

            let mut body_spans = HashSet::new();
            collect_expr_spans(&checked.ast.body, &mut body_spans);
            let late_resolutions: HashMap<Span, ResolvedCall> = accumulator
                .resolutions
                .resolved_calls
                .iter()
                .filter(|(span, _)| body_spans.contains(span))
                .map(|(span, resolution)| (*span, resolution.clone()))
                .collect();
            checked
                .callees
                .extend(self.harvest_callees(state, &late_resolutions, &HashMap::new()));
            checked.callees.sort_by(|a, b| {
                a.module
                    .as_ref()
                    .cmp(b.module.as_ref())
                    .then(a.symbol.as_ref().cmp(b.symbol.as_ref()))
            });
            checked.callees.dedup();

            let scheme = self
                .current_symbol_table(state)
                .view()
                .lookup(&name)
                .and_then(Binding::callable)
                .map(|callable| callable.arm.scheme.clone())
                .ok_or_else(|| CranelispError::TypeError {
                    message: format!("internal: missing declaration for checked body `{name}`"),
                    location: ErrorLocation::from_span(checked.registration.span),
                })?;
            // `__expr` is an execution boundary, not a reusable polymorphic
            // definition. A result-only residual below a preserved constructor
            // therefore takes the already-approved bounded-defaulting path and
            // receives a concrete execution scheme/view. Keep the checked AST
            // unchanged: int reads its original inferred type for REPL display
            // while the producer/release boundary reads the concrete view.
            //
            // The two §3.11.2 display-only shapes stay templates: a bare name
            // or literal empty vector is rendered without execution, so minting
            // a runtime capability for it would be the wrong lifecycle.
            let display_only_expr = name.as_ref() == "__expr"
                && match &checked.ast.body {
                    Expr::Var { .. } => true,
                    Expr::VecLit { elements, .. } => elements.is_empty(),
                    _ => false,
                };
            let defaulted_expr =
                if name.as_ref() == "__expr"
                    && !display_only_expr
                    && !scheme.ty.is_concrete()
                    && scheme.constraints.is_empty()
                {
                    let ast = default_residual_parameters(&checked.ast, &scheme)?;
                    let result = ast.body.inferred_type().cloned().ok_or_else(|| {
                        CranelispError::TypeError {
                            message: "internal: defaulted `__expr` body has no inferred type"
                                .into(),
                            location: ErrorLocation::from_span(ast.span),
                        }
                    })?;
                    let execution_scheme = Scheme {
                        type_vars: Vec::new(),
                        constraints: HashMap::new(),
                        ty: Type::Fn(Vec::new(), Box::new(result)),
                    };
                    Some((ast, execution_scheme))
                } else {
                    None
                };
            let draft = if scheme.ty.is_concrete() && scheme.constraints.is_empty() {
                let view = build_concrete_codegen_view(
                    &name,
                    &checked.ast,
                    &scheme,
                    &accumulator.resolutions.pattern_ctors,
                    &accumulator.resolutions.var_refs,
                    &accumulator.resolutions.apply_refs,
                )?
                .ok_or_else(|| CranelispError::TypeError {
                    message: format!("could not build concrete view for `{name}`"),
                    location: ErrorLocation::from_span(checked.registration.span),
                })?;
                CallableArmDraft::concrete_body(
                    scheme.clone(),
                    checked
                        .ast
                        .params
                        .iter()
                        .map(|(param, _)| param.clone())
                        .collect(),
                    checked.ast.clone(),
                    view,
                    checked.callees.clone(),
                )
            } else if let Some((defaulted_ast, execution_scheme)) = defaulted_expr {
                let view = build_concrete_codegen_view(
                    &name,
                    &defaulted_ast,
                    &execution_scheme,
                    &accumulator.resolutions.pattern_ctors,
                    &accumulator.resolutions.var_refs,
                    &accumulator.resolutions.apply_refs,
                )?
                .ok_or_else(|| CranelispError::TypeError {
                    message: "could not build concrete view for `__expr`".into(),
                    location: ErrorLocation::from_span(checked.registration.span),
                })?;
                CallableArmDraft::concrete_body(
                    execution_scheme,
                    Vec::new(),
                    checked.ast.clone(),
                    view,
                    checked.callees.clone(),
                )
            } else {
                let kind = if scheme.constraints.is_empty() {
                    TemplateKind::Parametric
                } else {
                    TemplateKind::Constrained(Box::new(ConstrainedMeta::new(
                        scheme.constraints.clone(),
                    )))
                };
                CallableArmDraft::template(
                    scheme.clone(),
                    checked
                        .ast
                        .params
                        .iter()
                        .map(|(param, _)| param.clone())
                        .collect(),
                    TemplateBody::Ast(checked.ast.clone()),
                    kind,
                    checked.callees.clone(),
                )
            };

            match checked.registration.target {
                BodyTarget::Direct(_) => {
                    let settled_scheme = draft.scheme.clone();
                    match draft.settlement {
                        cranelisp_types::CallableArmSettlement::ConcreteBody {
                            ast,
                            view,
                            callees,
                        } => {
                            self.current_symbol_table_mut(state)
                                .settle_checked_concrete(&name, settled_scheme, ast, view, callees)
                                .map_err(crate::result::lifecycle_error)?;
                        }
                        cranelisp_types::CallableArmSettlement::Template {
                            body: TemplateBody::Ast(ast),
                            kind,
                            callees,
                        } => self
                            .current_symbol_table_mut(state)
                            .settle_checked_template(&name, settled_scheme, ast, kind, callees)
                            .map_err(crate::result::lifecycle_error)?,
                        cranelisp_types::CallableArmSettlement::Template { .. } => {
                            unreachable!("invariant: checked source body draft is AST-backed")
                        }
                        _ => unreachable!("invariant: callable-arm settlement is closed here"),
                    }
                }
                BodyTarget::MultiSignatureClause { group, clause } => {
                    overload_drafts
                        .entry(group)
                        .or_default()
                        .push((clause, name, draft));
                }
            }
        }

        for (group, mut entries) in overload_drafts {
            entries.sort_by_key(|(clause, _, _)| *clause);
            for (expected, (actual, _, _)) in entries.iter().enumerate() {
                if *actual != expected {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "internal: overload `{group}` has non-contiguous clause roster"
                        ),
                        location: ErrorLocation::from_span(Span::SYNTHETIC),
                    });
                }
            }
            let source = working_program.iter().find_map(|form| match form {
                TopLevel::Defn(defn) if defn.name == group && defn.is_multi_sig() => Some(defn),
                _ => None,
            });
            let Some(source) = source else {
                return Err(CranelispError::TypeError {
                    message: format!("internal: missing source declaration for overload `{group}`"),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                });
            };
            let mut table = self.current_symbol_table_mut(state);
            for (_, temporary_name, _) in &entries {
                table
                    .discard_declared(temporary_name)
                    .map_err(crate::result::lifecycle_error)?;
            }
            table
                .install_overloaded(
                    group,
                    source.docstring.clone(),
                    0,
                    entries.into_iter().map(|(_, _, draft)| draft).collect(),
                    source.visibility,
                )
                .map_err(crate::result::lifecycle_error)?;
        }
        Ok(())
    }

    // =================================================================
    // Unified multi-form check driver — drives `check_forms`'s internal
    // pipeline (Pass 1 register, Pass 2 check bodies, finalize) over a
    // `&[TopLevel]` slice and returns the `CheckResult` (including display
    // info). The production entry surface is `check_forms` in `form.rs`,
    // which discards the display-bearing `CheckResult`; this driver retains
    // it so in-crate tests can assert on inferred types / schemes.
    // =================================================================

    /// Collect the program's `Defn`s belonging to ONE monomorphisation family
    /// (§11.8.3). The SINGLE parameterized harvest-input selector (arch W2a pin
    /// — NEVER a forked sibling of `collect_single_sig_defns`): invoked at the
    /// two mono settlement points with complementary families, so every `Defn`
    /// reaches EXACTLY one harvest invocation:
    ///
    /// - `SingleSig` — the pass-4 single-sig mono (`finalize.rs:1015`), untouched.
    /// - `MultiSig` — the post-`finalize_multi_sig_variant_types` clause-body
    ///   harvest (§11.8.3 leg D3), where multi-sig clauses are settled concrete.
    ///
    /// The `is_multi_sig()` partition is complementary AND total by construction:
    /// a `Defn` is multi-sig or it is not. The `debug_assert_eq!` inline in
    /// `finalize_check_result_inner` (at the second, `MultiSig` harvest call)
    /// makes "a later-added defn family silently skipped" a loud failure, not a
    /// silent hole (arch pin: filter must be total).
    pub(super) fn collect_defns_for_mono(
        program: &[TopLevel],
        family: MonoDefnFamily,
    ) -> Vec<&Defn> {
        program
            .iter()
            .filter_map(|top| {
                let TopLevel::Defn(defn) = top else {
                    return None;
                };
                let matches = match family {
                    MonoDefnFamily::SingleSig => !defn.is_multi_sig(),
                    MonoDefnFamily::MultiSig => defn.is_multi_sig(),
                };
                matches.then_some(defn)
            })
            .collect()
    }

    /// Collect only single-sig Defn entries (skip multi-sig) — the `SingleSig`
    /// family of [`Self::collect_defns_for_mono`].
    pub(super) fn collect_single_sig_defns(program: &[TopLevel]) -> Vec<&Defn> {
        Self::collect_defns_for_mono(program, MonoDefnFamily::SingleSig)
    }
}

/// The two complementary monomorphisation-harvest families (§11.8.3, arch W2a
/// pin). Every top-level `Defn` belongs to exactly one; the two harvest
/// invocations (pass-4 single-sig, post-Phase-A multi-sig) partition the set.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum MonoDefnFamily {
    /// Single-signature defns — the pass-4 mono (`finalize.rs:1015`).
    SingleSig,
    /// Multi-signature defns — the post-`finalize_multi_sig_variant_types`
    /// clause-body harvest (leg D3).
    MultiSig,
}

#[cfg(test)]
mod tests;
