use super::*;

mod ambiguity;
#[cfg(test)]
pub(super) use ambiguity::AmbiguousForm;


impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Merge a `FormCheckResult` into the module's accumulator.
    ///
    /// Called after each `check_form()` to accumulate per-form results
    /// into the module-level state. Also eagerly writes callees to
    /// `ModuleEntry` in the symbol table (Decision 21) so that the
    /// scheduler can read them immediately without waiting for
    /// `finalize_check_result`.
    /// Merge a per-form check result into the module accumulator.
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
        state: &mut CheckState,
        accumulator: &mut ModuleCheckAccumulator,
        result: FormCheckResult,
    ) {
        // Write callees to ModuleEntry eagerly (Decision 21).
        if !result.call_graph_edges.is_empty() {
            let mut guard = self.current_symbol_table_mut(state);
            write_callees_to_module_entries(&mut *guard, &result.call_graph_edges);
        }

        accumulator.method_resolutions.extend(result.method_resolutions);
        accumulator.pattern_ctors.extend(result.pattern_ctors);
        accumulator.var_refs.extend(result.var_refs);
        accumulator.apply_refs.extend(result.apply_refs);
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


    /// Re-generalize every defn's scheme from its `defn_type_vars` source vars
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
        for (name, (param_types, ret_ty)) in &accumulator.defn_type_vars {
            let fn_type = Type::Fn(
                param_types.iter().map(|t| self.apply_subst(state, t)).collect(),
                Box::new(self.apply_subst(state, ret_ty)),
            );
            let scheme = self.generalize(state, &fn_type);
            let mut st = self.current_symbol_table_mut(state);
            // Demoting a false-positive constrained template (its constraints
            // vanished after final substitution) — the re-slotting decision is
            // the SAME structural gate as the determination point (FIXME 0374,
            // Principle 20): slot ⟺ concrete.
            //   - constraints vanished AND scheme concrete → `Concrete{slot}`
            //     (reuse the entry's own concrete slot if any, else allocate).
            //   - constraints vanished BUT scheme still generic (`Type::Var`)
            //     → `Polymorphic` (slot-less); only its mono instances slot.
            // A constrained template that generalised to a still-generic
            // unconstrained type must NOT be re-slotted `Concrete` — that would
            // re-introduce the non-concrete-def-with-slot leak.
            // A `Constrained` OR `Polymorphic` template whose regeneralized
            // scheme is now constraint-free is a re-slotting candidate (both are
            // slot-less templates that may have become concrete). The
            // re-slotting follows the SAME structural gate as the determination
            // point (FIXME 0374, Principle 20): slot ⟺ concrete.
            let is_reslot_candidate = scheme.constraints.is_empty()
                && matches!(
                    st.get(name.as_ref()),
                    Some(ModuleEntry::Def { kind, .. })
                        if matches!(
                            kind.as_ref(),
                            DefKind::UserFn {
                                fn_state: UserFnState::Constrained(_)
                                    | UserFnState::Polymorphic(_)
                            }
                        )
                );
            // Compute the demoted slot before the `get_mut` borrow so the
            // `&mut st` allocate doesn't alias the entry borrow. Only the
            // concrete branch needs a slot. A `Polymorphic` def whose scheme
            // collapsed to a concrete type (e.g. `g : ∀a.a→a` pinned to
            // `(Fn [Int] Int)` by a direct concrete call `(g 1)` + the post-mono
            // regeneralisation) MUST become `Concrete{slot}` — otherwise it is a
            // slot-less `Polymorphic` arm carrying a concrete scheme, an
            // inconsistent state where a same-program caller cannot resolve it
            // through a slot (the REPL mutual-forward-ref `undefined function`
            // symptom).
            // Keep `Polymorphic` (slot-less) whenever the def is still
            // non-concrete (S84 Wave 1b TOTAL gate — slot ⟺ concrete, no
            // monomorphisable-from-params carve-out). Otherwise allocate a slot:
            // a concrete scheme is a plain `Concrete{slot}`. A result-only-var
            // scheme (`(Fn [] (Option a))`) stays `Polymorphic` here; if it is a
            // test-fn entry it is given a concrete slotted instance by the
            // test-fn mono-root pass (`register_test_fn_mono_roots`).
            let stay_polymorphic = is_reslot_candidate && !scheme.ty.is_concrete();
            let demoted_slot = if is_reslot_candidate && !stay_polymorphic {
                Some(match existing_callable_slot(&st, name.as_ref()) {
                    Some(s) => s,
                    None => st
                        .allocate_got_slot()
                        .map_err(crate::result::got_exhausted_error)?,
                })
            } else {
                None
            };
            if let Some(ModuleEntry::Def { scheme: s, kind, ast, .. }) =
                st.symbols.get_mut(name)
            {
                *s = scheme.clone();
                if is_reslot_candidate {
                    if let Some(got_slot) = demoted_slot {
                        **kind = DefKind::UserFn {
                            fn_state: UserFnState::Concrete { got_slot, mode_summary: None },
                        };
                    } else if let Some(variant) = ast.clone() {
                        // Still non-concrete: slot-less `Polymorphic`, carrying
                        // the stored annotated body + new scheme for later
                        // monomorphisation. (For a `Constrained` false-positive
                        // that stays generic-unconstrained this is the correct
                        // demotion; for a `Polymorphic` that stayed generic this
                        // is idempotent.)
                        **kind = DefKind::UserFn {
                            fn_state: UserFnState::Polymorphic(Box::new(ParametricFn {
                                variant,
                                scheme: scheme.clone(),
                            })),
                        };
                    }
                }
            }
        }

        Ok(())
    }


    /// Scoped re-generalize + reslot restricted to entries CURRENTLY in the
    /// `Polymorphic` state (S110 C-4). This is [`Self::regeneralize_defn_schemes`]
    /// with a `Polymorphic`-only gate: it recomputes each still-`Polymorphic`
    /// defn's scheme from its `defn_type_vars` source vars through the final
    /// substitution and, when that scheme is now fully concrete, reslots the entry
    /// to `Concrete{slot}` (the SAME structural gate — slot ⟺ concrete — as the
    /// two full regeneralize passes).
    ///
    /// **Why a scoped pass, not a third full `regeneralize_defn_schemes`.** The
    /// spurious-poly caller this fixes (`main` calling an overloaded/multi-arity
    /// fn, whose return var is only pinned by `resolve_pending_overloads` AFTER the
    /// FIXME-0349 re-generalize) needs one more generalize once the overload drain
    /// settles its return var. But a full re-generalize UNCONDITIONALLY overwrites
    /// EVERY `defn_type_vars` entry's stored scheme (`*s = scheme`) — including the
    /// `Concrete` instances `register_test_fn_mono_roots` minted, whose
    /// `defn_type_vars` signature is still the pre-mint poly `(Fn [] (Option a))`.
    /// That would demote a mono-root's concrete scheme back to poly (the finalize
    /// ordering hazard; `test_fn_registered_as_mono_root_gets_concrete_instance`).
    /// Gating on the current `Polymorphic` state leaves every `Concrete` entry —
    /// mono-roots and ordinary concrete defns alike — untouched, and only re-settles
    /// the spuriously-poly callers. A genuinely polymorphic defn
    /// (`(defn empty [] [])`) recomputes to a still-non-concrete scheme and stays
    /// `Polymorphic`, unchanged.
    pub(super) fn regeneralize_only_polymorphic(
        &self,
        state: &mut CheckState,
        accumulator: &ModuleCheckAccumulator,
    ) -> Result<(), CranelispError> {
        for (name, (param_types, ret_ty)) in &accumulator.defn_type_vars {
            // Gate: ONLY re-settle entries currently registered `Polymorphic`.
            // A `Concrete` entry (mono-root or ordinary concrete defn) is skipped
            // so its stored scheme is never overwritten.
            let is_polymorphic = matches!(
                self.current_symbol_table(state).view().lookup(name),
                Some(ModuleEntry::Def { kind, .. })
                    if matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Polymorphic(_) }
                    )
            );
            if !is_polymorphic {
                continue;
            }
            let fn_type = Type::Fn(
                param_types.iter().map(|t| self.apply_subst(state, t)).collect(),
                Box::new(self.apply_subst(state, ret_ty)),
            );
            let scheme = self.generalize(state, &fn_type);
            // A scheme that acquired constraints is left to the constrained-fn
            // path — never reslotted `Concrete` here (mirrors the reslot gate in
            // `regeneralize_defn_schemes`).
            if !scheme.constraints.is_empty() {
                continue;
            }
            // Reslot ⟺ concrete (the S84 Wave 1b TOTAL slot gate): a
            // `Polymorphic` entry whose scheme collapsed to a concrete type (the
            // overloaded-call caller pinned by `resolve_pending_overloads`) becomes
            // `Concrete{slot}`, reusing its own callable slot if any; a scheme that
            // is still generic stays `Polymorphic`.
            let mut st = self.current_symbol_table_mut(state);
            let demoted_slot = if scheme.ty.is_concrete() {
                Some(match existing_callable_slot(&st, name.as_ref()) {
                    Some(s) => s,
                    None => st
                        .allocate_got_slot()
                        .map_err(crate::result::got_exhausted_error)?,
                })
            } else {
                None
            };
            if let Some(ModuleEntry::Def { scheme: s, kind, ast, .. }) =
                st.symbols.get_mut(name)
            {
                *s = scheme.clone();
                if let Some(got_slot) = demoted_slot {
                    **kind = DefKind::UserFn {
                        fn_state: UserFnState::Concrete { got_slot, mode_summary: None },
                    };
                } else if let Some(variant) = ast.clone() {
                    // Still non-concrete: keep it slot-less `Polymorphic`, carrying
                    // the refreshed scheme for later monomorphisation (idempotent).
                    **kind = DefKind::UserFn {
                        fn_state: UserFnState::Polymorphic(Box::new(ParametricFn {
                            variant,
                            scheme: scheme.clone(),
                        })),
                    };
                }
            }
        }

        Ok(())
    }


    /// Re-settle the stored schemes of already-determined **`Polymorphic`**
    /// cluster members from their `defn_type_vars` source vars through the
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
    ) {
        for (name, (param_types, ret_ty)) in &accumulator.defn_type_vars {
            // Only already-determined `Polymorphic` templates are re-tie
            // candidates. The read guard is a temporary in this `matches!`.
            let is_poly_determined = matches!(
                self.current_symbol_table(state).view().lookup(name),
                Some(ModuleEntry::Def { kind, .. })
                    if matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Polymorphic(_) }
                    )
            );
            if !is_poly_determined {
                continue;
            }
            let fn_type = Type::Fn(
                param_types.iter().map(|t| self.apply_subst(state, t)).collect(),
                Box::new(self.apply_subst(state, ret_ty)),
            );
            let scheme = self.generalize(state, &fn_type);
            // Pure-parametric only (mirror the 0344 writeback gate). A scheme
            // that acquired constraints is left to the constrained-fn path.
            if !scheme.constraints.is_empty() {
                continue;
            }
            if let Some(ModuleEntry::Def { scheme: s, .. }) =
                self.current_symbol_table_mut(state).symbols.get_mut(name)
            {
                *s = scheme;
            }
        }
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
                        self.resolve_value_position_trait_methods(state, internal_defn.body(), false)?;
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
                if let ModuleEntry::Def { kind, scheme, ast, .. } = entry {
                    match kind.as_ref() {
                        // Trait-constrained polymorphism: classic constrained
                        // fn marker.
                        DefKind::UserFn { fn_state: UserFnState::Constrained(_) } => {
                            constrained_fn_names.insert(name.clone());
                        }
                        // Pure parametric polymorphism registered by a previous
                        // `check_forms` call (Additive cross-call shape): the
                        // scheme is still polymorphic (`scheme.type_vars` non-empty)
                        // and we have the annotated `ast`. The current
                        // cluster's call sites against this name need
                        // monomorphisation just as if it were constrained —
                        // backend codegen requires concrete CLIF types.
                        // `get_constrained_fn` synthesises a `ConstrainedFn`
                        // view from `ast + scheme` for this case. Matches the
                        // non-constrained `UserFn` states (`Concrete` /
                        // `NotDetermined`) — the slot, if any, is irrelevant here.
                        DefKind::UserFn { fn_state }
                            if !matches!(fn_state, UserFnState::Constrained(_))
                                && !scheme.type_vars.is_empty()
                                && ast.is_some() =>
                        {
                            constrained_fn_names.insert(name.clone());
                        }
                        _ => {}
                    }
                }
            }
        }

        constrained_fn_names
    }


    /// Surface deferred field-accessor / binding collisions as non-fatal
    /// warnings (FIXME 0351(a), spec §5.2.6 safe disposition): the accessor was
    /// suppressed (the existing binding wins) and the clash is reported so it is
    /// never silent. Drained so a redefining REPL re-check does not double-report.
    pub(super) fn drain_accessor_collisions(&self, state: &mut CheckState) {
        for (accessor_name, type_name) in std::mem::take(&mut state.deferred_accessor_collisions) {
            state.warnings.push(cranelisp_types::Warning {
                kind: cranelisp_types::WarningKind::ShadowedName,
                message: format!(
                    "field accessor `{accessor_name}` for type `{type_name}` \
                     conflicts with a name already bound to `{accessor_name}`; \
                     the accessor is suppressed and the existing binding is kept"
                ),
                span: Span::SYNTHETIC,
            });
        }
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
        let taken = std::mem::take(&mut state.method_resolutions);
        accumulator.method_resolutions.extend(taken.resolved_calls);
        // S110 W0.1b (§1.1.1) / S114 carrier flip: post-pass typed-verdict
        // inserts (the fn-value mono-rewrite carrier; the finalize-drained
        // auto-curry leg) land in `state.method_resolutions.{var_refs,apply_refs}`
        // AFTER the per-form snapshots that feed the accumulator. Sweep BOTH
        // typed maps into the accumulator so the finalize view-rebuild
        // (`finalize_annotations_and_publish`) sees them.
        accumulator.var_refs.extend(taken.var_refs);
        accumulator.apply_refs.extend(taken.apply_refs);
        // S110 W3.1 (§1.1.3, FIXME 0622): sweep the THIRD `MethodResolutions`
        // sidecar too. Harmless today (no post-pass records pattern ctors into
        // `state.method_resolutions` — the mono/test-root rechecks swap in their
        // own per-instance maps), but a partial sweep of a 3-field struct is how
        // the next map-provenance starvation hides. Extend all three so the
        // accumulator is the total authoritative source (behaviour-invariant).
        accumulator.pattern_ctors.extend(taken.pattern_ctors);
        accumulator.expr_types.extend(
            std::mem::take(&mut state.expr_types),
        );
        accumulator.warnings.extend(
            std::mem::take(&mut state.warnings),
        );
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
            &accumulator.defn_type_vars,
            &mut multi_sig_mangled_names,
        )?;

        // Pass 3: detect constrained polymorphic functions (cluster result +
        // accumulator carry + Additive live-table scan).
        let single_sig_defns = Self::collect_single_sig_defns(working_program);
        let constrained_fn_names =
            self.collect_all_constrained_names(state, &single_sig_defns, accumulator, strategy);

        // Pass 4: monomorphise constrained function call sites.
        // Side effect: registers mono specialisations on the symbol table via
        // `register_mono_entry` inside `monomorphise_call`. The returned
        // Vec<MonoDefn> was carried on CheckResult.mono_defns pre-slim; no
        // longer needed — mono entries live on SymbolTable.
        // S84 Phase-3 (FIXME 0392): each instance's concrete-boundary `MonoExpr`
        // view is set ON its `ModuleEntry::Def.codegen_view` at
        // `register_mono_entry` (produces-but-unread until the backend read-flip,
        // FIXME 0391). The validation payoff (every instance's body run through
        // `MonoExpr::from_expr` at the seam) is unchanged; the transitional
        // parallel `Vec<MonoDefnVariant>` return is retired.
        let _mono_defns =
            self.pass4_monomorphise(state, &single_sig_defns, &constrained_fn_names)?;

        // FIXME 0349 — re-generalize after monomorphisation. pass4's call-site
        // result propagation (`monomorphise_call`) can pin a caller's
        // previously-loose result var (a forward-referenced callee left it
        // polymorphic). Re-running generalization makes the caller's STORED
        // scheme reflect that pinning, so a spuriously-polymorphic caller
        // collapses to its true monomorphic scheme and the backend emits a
        // direct call to the mono variant rather than the polymorphic template.
        self.regeneralize_defn_schemes(state, accumulator)?;

        // S84 Wave 1b (FIXME 0374/0378 issue 3): register discovered `test-*`
        // entry points as monomorphisation ROOTS — mint a concrete
        // `(Fn [] (Option String))` instance under the bare name for any
        // slot-less `Polymorphic` degenerate test fn (`(defn test-x [] None)`).
        // Run AFTER both `regeneralize_defn_schemes` passes so the regeneralize's
        // unconditional scheme-writeback cannot demote the minted concrete
        // scheme back to `(Option a)`. The discovery readers
        // (`discover_test_names` / `discover_eligible_tests`) read the concrete
        // instance's slot under the same name.
        self.register_test_fn_mono_roots(state)?;

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
        self.resolve_pending_overloads(state)?;
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
        // scheme back to its poly `defn_type_vars` signature (the finalize ordering
        // hazard the mono-root comment guards; `test_fn_registered_as_mono_root_
        // gets_concrete_instance`). Genuinely polymorphic defns (`(defn empty []
        // [])`, scheme stays `(Fn [] (Vec a))`) are non-concrete after
        // re-generalize and stay `Polymorphic`.
        self.regeneralize_only_polymorphic(state, accumulator)?;

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
        if let Some(amb) = self.find_ambiguous_top_level_form(
            state,
            accumulator,
            working_program,
        ) {
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
        self.pass4_monomorphise(state, &multi_sig_defns, &constrained_fn_names)?;

        // MC-X4 / MC-X4b — the SINGLE-SIG consumer RE-HARVEST at the settlement
        // point (P26 — record from settled state). A poly callee consuming a
        // MULTI-SIG fn's bare return (`(mycount (build 3))` in a single-sig body,
        // or `(unwrap (build 3))` over an untyped ADT field) had its arg type — the
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
        self.pass4_monomorphise(state, &single_sig_defns, &constrained_fn_names)?;

        // Surface any field-accessor synthesis collisions with a NON-accessor
        // binding (FIXME 0351(a)) as non-fatal warnings.
        self.drain_accessor_collisions(state);

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
        accumulator: &ModuleCheckAccumulator,
        working_program: &[TopLevel],
        multi_sig_mangled_names: &MangledNamesByBase,
    ) -> Result<(), CranelispError> {
        // Final callee write (Decision 21): overwrite the eager writes from
        // merge_form_result with the final canonical version that includes any
        // edges from post-passes.
        if !accumulator.call_graph_edges.is_empty() {
            let mut guard = self.current_symbol_table_mut(state);
            write_callees_to_module_entries(&mut *guard, &accumulator.call_graph_edges);
        }

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
        // S84 ConcreteType arc (FIXME 0394/0395): rebuild each `Concrete{slot}`
        // entry's `codegen_view` HERE, from the now-post-mono-annotated `ast`.
        // The single-sig population at `check_form_body_single_defn` ran at body-
        // check time — BEFORE `pass4_monomorphise` rewrote this caller's call-node
        // `resolved_call` to its `SigDispatch{mangled}` target (`(id 7)`'s `id`
        // call → `SigDispatch{id$Int}`). That early view carried a stale
        // `resolved_call: None` on the polymorphic call, so the backend could not
        // consume it (it rebuilt from `ast` instead — the dual-source FIXME 0395
        // forecloses). This re-annotation block has just refreshed `existing`
        // (the `ast`) from `accumulator.method_resolutions` (now carrying the
        // post-mono `SigDispatch`s) — so rebuilding the view from `existing` HERE
        // makes `codegen_view` POST-mono-correct. The backend reads it on the live
        // path; the dual-source collapses to one (Principle 7).
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
            let pattern_ctors_for_views = accumulator.pattern_ctors.clone();
            let var_refs_for_views = accumulator.var_refs.clone();
            let apply_refs_for_views = accumulator.apply_refs.clone();
            let sym_table = &mut self.current_symbol_table_mut(state);
            // Reannotate `existing` from the final side maps + subst, then, for a
            // `Concrete{slot}` codegen target, rebuild `codegen_view` from the
            // refreshed (post-mono) variant. Returns `Result` (S114 carrier
            // flip): `build_concrete_codegen_view` propagates the located
            // `ViewBuildError::Unresolved` gate error rather than swallowing a
            // real-span resolution miss into the lenient fallback.
            let reannotate_and_refresh_view =
                |name: &Symbol,
                 entry: &mut ModuleEntry<C>,
                 resolved_expr_types: &HashMap<Span, Type>,
                 method_resolutions: &HashMap<Span, ResolvedCall>,
                 subst: &Subst|
                 -> Result<(), CranelispError> {
                    if let ModuleEntry::Def { ast: Some(existing), kind, codegen_view: cv, .. } =
                        entry
                    {
                        annotate_variant_from_maps(existing, resolved_expr_types, method_resolutions);
                        apply_subst_to_variant(subst, existing);
                        if matches!(
                            kind.as_ref(),
                            DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                        ) {
                            *cv = build_concrete_codegen_view(
                                name,
                                existing,
                                &pattern_ctors_for_views,
                                &var_refs_for_views,
                                &apply_refs_for_views,
                            )?;
                        }
                    }
                    Ok(())
                };
            for top in working_program {
                match top {
                    TopLevel::Defn(defn) if defn.is_multi_sig() => {
                        // S91 Wave-7 (FIXME 0432 Face A): re-annotate each
                        // variant body under its MANGLED key. The internal
                        // `{name}__v{i}` entries were removed-and-reinserted as
                        // mangled names by `register_mangled_variants` (Pass
                        // 2.5), so a stale internal-key lookup misses and an
                        // in-body self-call's `SigDispatch` resolution (written
                        // by `resolve_pending_overloads`) never lands on the
                        // body — the backend then falls back to the undefined
                        // bare name. Look up the live mangled keys instead.
                        if let Some(mangled_names) = multi_sig_mangled_names.get(&defn.name) {
                            for mangled_name in mangled_names {
                                if let Some(entry) = sym_table.symbols.get_mut(mangled_name) {
                                    reannotate_and_refresh_view(
                                        mangled_name,
                                        entry,
                                        &resolved_expr_types,
                                        &accumulator.method_resolutions,
                                        &state.subst,
                                    )?;
                                }
                            }
                        }
                    }
                    TopLevel::Defn(defn) => {
                        if let Some(entry) = sym_table.symbols.get_mut(&defn.name) {
                            reannotate_and_refresh_view(
                                &defn.name,
                                entry,
                                &resolved_expr_types,
                                &accumulator.method_resolutions,
                                &state.subst,
                            )?;
                        }
                    }
                    TopLevel::TraitImpl(ti) => {
                        for method in &ti.methods {
                            let target_name = ti.target.head_ref().map(|r| r.name.as_ref()).unwrap_or("");
                            let mangled = format!("{}.{}${}", ti.trait_name, method.name, target_name);
                            let mangled_sym = Symbol::from(mangled.as_str());
                            if let Some(entry) = sym_table.symbols.get_mut(&mangled_sym) {
                                reannotate_and_refresh_view(
                                    &mangled_sym,
                                    entry,
                                    &resolved_expr_types,
                                    &accumulator.method_resolutions,
                                    &state.subst,
                                )?;
                            }
                        }
                    }
                    _ => {}
                }
            }
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
                let TopLevel::Defn(defn) = top else { return None };
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
