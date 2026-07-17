use super::*;

/// Per-form typecheck result.
///
/// Returned by `check_form()` for each (form, pass) invocation. The caller
/// feeds this to `merge_form_result()` to accumulate into module-level state.
/// In v4, the scheduler also uses these fields for per-symbol codegen readiness.
#[derive(Debug)]
/// A located §3.11.1 codegen-reaching ambiguity, enriched with the offending
/// arity clause + param for the diagnostic (0576).
pub(super) struct AmbiguousForm {
    /// The enclosing `defn` name.
    pub(super) name: Symbol,
    /// The reference-site span of the unpinned value position.
    pub(super) span: Span,
    /// The offending clause's arity — `Some` only for a MULTI-arity `defn` (a
    /// single-sig defn has one obvious clause, so it keeps the plain message).
    pub(super) clause_arity: Option<usize>,
    /// The unpinned param/binder name, when the position is a bare non-synthetic
    /// `Var` (0568: never a `__`-prefixed internal binder).
    pub(super) param: Option<Symbol>,
}


impl AmbiguousForm {
    /// The user-facing ambiguity message. Names the offending arity CLAUSE and
    /// unpinned PARAM when known (0576) — "each arity clause is type-checked
    /// independently" (§5.1.2), so the fix is a per-clause annotation — and falls
    /// back to the plain fn-level message otherwise.
    pub(super) fn message(&self) -> String {
        // The synthetic REPL/eval wrapper: never leak the internal `__expr`
        // binder into user text (0568, spec §3.3.3 MUST (e)). A bare §3.11
        // ambiguity message naming no internal symbol.
        if self.name.as_ref() == "__expr" {
            return "ambiguous type; add a `:Type` annotation to pin the type of \
                    this expression (spec §3.11)"
                .to_string();
        }
        let where_ = match self.clause_arity {
            Some(arity) => format!("the {arity}-arg arity clause of `{}`", self.name),
            None => format!("`{}`", self.name),
        };
        match &self.param {
            Some(p) => format!(
                "ambiguous type: the parameter `{p}` in {where_} is not pinned — \
                 each arity clause is type-checked independently (spec §5.1.2), so \
                 add a `:Type` annotation to `{p}` in that clause"
            ),
            None => format!(
                "ambiguous type; add an annotation to pin the type of the \
                 polymorphic value bound in {where_}"
            ),
        }
    }
}


/// Which of the §3.11 gate's two timing-incompatible duties a
/// [`TypeCheckEnv::find_ambiguous_top_level_form`] pass performs.
///
/// The gate historically carried BOTH duties in one pre-drain pass, which is
/// unsound: they need OPPOSITE positions relative to `resolve_pending_overloads`
/// (the single overload/self-call drain). Splitting them by defn shape lets each
/// run at its correct position (S110 review "gate/drain ordering composition").
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum AmbiguityScanPhase {
    /// §5.1.2 clause-independence leg — scans MULTI-ARITY defns ONLY, and MUST
    /// run PRE-`resolve_pending_overloads`. A multi-clause defn's per-clause
    /// param vars must stay UNPINNED for the verdict: resolving a deferred
    /// self-call first would let it acquire a sibling clause's concrete param
    /// type, masking the genuine cross-variant ambiguity (the C-4 constraint;
    /// `multi_clause_defn_self_call_is_ambiguous_not_panic`).
    ClauseIndependence,
    /// §3.11.1 value-position scan — scans SINGLE-CLAUSE defns and the `__expr`
    /// eval wrapper, and MUST run POST-drain (after `resolve_pending_overloads`,
    /// `resolve_auto_curry`, and the C-4 `regeneralize_only_polymorphic`). A
    /// deferred-overload return var in a value position (`(let [r (h 7)] r)`) is
    /// only unified to the selected variant's concrete return by the drain, and
    /// a caller left spuriously `Polymorphic` at gate time is only collapsed to
    /// `Concrete` (its body then scannable) by the scoped regeneralize — so the
    /// verdict must read the SETTLED types (B1 wrong-reject / B2 wrong-accept).
    ValueScan,
}



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
        accumulator.resolved_targets.extend(result.resolved_targets);
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


    /// Find a CODEGEN-REACHING value position whose finalised type retains an
    /// unconstrained `Type::Var` that no reachable use site pins (spec §3.11.1 —
    /// the ambiguity rule). Returns the offending `(name, span)` so the caller
    /// raises the located `TypeError` ("ambiguous type; add an annotation").
    ///
    /// **Scope (the delicate part — disposition triple, spec §3.11):**
    ///
    /// - **§3.11.1 (REJECT):** a `let`-bound value that must become a runtime
    ///   value while a type var is free, with nothing pinning it — the canonical
    ///   `(let [x (identity None)] (match x [None 0 (Some _) 1]))` shape: `x` has
    ///   type `(Option a)`, `a` is unpinned (the `match` scrutinises only the
    ///   tag), `x` is consumed at runtime. THIS is the codegen-reaching position
    ///   the check fires on. A `let`-binding is the canonical §3.11.1 worked
    ///   example; the value is forced to a concrete runtime representation that
    ///   does not exist while `a` is free.
    ///
    /// - **§3.11.2 (DISPLAY, not error):** a BARE top-level polymorphic value at
    ///   the REPL (`None`, `[]`) is `__expr`'s own body, NOT a `let`-binding —
    ///   it is displayed via introspection, never compiled to a runtime value,
    ///   so it is OUT of scope here (the check only inspects `let`-binding values,
    ///   not the `__expr` result itself).
    ///
    /// - **§3.11.3 (ADMIT):** a named polymorphic defn (`(defn empty [] [])`,
    ///   `(defn ambig [] None)`) is sound and dead-for-codegen until instantiated.
    ///   Its body is the defn result, not a `let`-binding, so it is never flagged.
    ///   The structural slot gate makes such a def slot-less `Polymorphic`; the
    ///   ambiguity check never inspects a defn's own result type.
    ///
    /// The check resolves each `let`-binding value's type through the final
    /// substitution (`state.subst`) and flags a residual free var that sits
    /// INSIDE a structure (`(Option a)`, `(Vec a)`) — a bare-`Var` value type is
    /// a transient unresolved-dispatch shape pinned by its use, skipped.
    /// A located §3.11.1 ambiguity, enriched (0576) with the offending arity
    /// CLAUSE (`clause_arity`, `Some` only for a multi-arity `defn`) and the
    /// unpinned PARAM name (`param`, absent when the position is not a bare
    /// binder or is synthetic).
    pub(super) fn find_ambiguous_top_level_form(
        &self,
        state: &CheckState,
        accumulator: &ModuleCheckAccumulator,
        working_program: &[TopLevel],
        phase: AmbiguityScanPhase,
    ) -> Option<AmbiguousForm> {
        // The ClauseIndependence (pre-drain) analogue of the ValueScan leg's
        // resolved-`SigDispatch` exemption (OA-1): a resolved multi-sig/overload
        // call (`(h 7)`) let-bound inside a multi-arity clause is verdicted here
        // PRE-drain, where its return var is still a fresh placeholder; the drain
        // (`resolve_pending_overloads`, below) will pin it to the selected
        // variant's CONCRETE return. Collect those about-to-be-pinned vars so such
        // a binding is not spuriously flagged, WITHOUT running the drain (which the
        // clause-independence position forbids — a self-call would acquire a
        // sibling clause's concrete param type). A genuinely-unresolved overload
        // (`sum-to`'s free-arg self-call) contributes nothing, so its free arg
        // stays flagged. Empty for the ValueScan phase (no multi-arity scanned).
        let benign_overload_vars = match phase {
            AmbiguityScanPhase::ClauseIndependence => {
                self.collect_pending_overload_result_vars(state)
            }
            AmbiguityScanPhase::ValueScan => std::collections::HashSet::new(),
        };

        for top in working_program {
            let TopLevel::Defn(defn) = top else { continue };
            // The two duties partition the defns by shape (S110 duty-split):
            //   - MULTI-ARITY defns are verdicted PRE-drain (clause independence);
            //   - SINGLE-CLAUSE defns + `__expr` are verdicted POST-drain (value
            //     scan, so a deferred-overload return var / spuriously-poly caller
            //     is settled first).
            // A defn is scanned in exactly ONE phase — never both.
            let is_multi_arity = defn.variants.len() > 1;
            let in_phase = match phase {
                AmbiguityScanPhase::ClauseIndependence => is_multi_arity,
                AmbiguityScanPhase::ValueScan => !is_multi_arity,
            };
            if !in_phase {
                continue;
            }

            if is_multi_arity {
                // §5.1.2 clause independence: each arity clause is type-checked
                // INDEPENDENTLY, and carries NO type information into or out of its
                // siblings. A clause's params therefore have NO legitimately-
                // polymorphic vars of their own — a param whose type stays free
                // after checking that clause's own body is the §5.1.2 ambiguity the
                // author MUST pin with an annotation, and the sibling clauses'
                // annotations never rescue it. So `allowed_vars` for the per-clause
                // scan carries NO clause-param vars: multi-arity clause params are
                // NON-polymorphic.
                //
                // The one exemption is OA-1: the benign pending-overload return
                // vars — a resolved multi-sig/overload call (`(h 7)`) whose return
                // var is only a fresh placeholder pre-drain and the drain will pin
                // concrete (`collect_pending_overload_result_vars`). Those are not
                // free-at-root, so `(let [r (h 7)] r)` binding of a concrete-arg
                // overload call is not spuriously flagged (OA-1a/b).
                //
                // CS-4.1 B-1 revert removed the CS-4 `∪ (written ∩ result-free)`
                // term (it exempted a written `:a` param that flows to the clause
                // result, but such a param can ALSO be pinned by a delegating
                // self-call to a sibling clause's concrete type — the drain then
                // acquires the sibling's concrete types (spec §5.1.2 forbids this
                // back-flow) and publishes an `:Int`-declared body over a `String`
                // pointer). Whether a multi-arity clause param may be legitimately
                // polymorphic is an UNRULED normative question (I-C, §5.1.2 says
                // NO); default to the written spec.
                //
                // B-1 has a SECOND leak vector through OA-1 itself (NOT covered by
                // the AP-1-term revert): when a clause's body ascribes a resolved
                // self-call result to a written param var (`([:a p :a rot] :a (rp2
                // p rot 0))`), the `:a` ascription UNIFIES the overload call's
                // return var with the param var `a`, so `benign_overload_vars`
                // resolves to `a` and would exempt the PARAM — re-opening the exact
                // memory-unsafe wrong-accept (`(rp2 "x" "y")` returns an Int over a
                // String arg forced into the `:Int` sibling clause). Enforce
                // "clause params are non-polymorphic" STRUCTURALLY: subtract each
                // clause's own param-type free vars from the benign set, so an
                // OA-1 exemption can never reach a clause param regardless of how a
                // self-call aliased it. (Subtracting only PARAM vars, never the
                // result vars, keeps OA-1b's returned fresh let-var `r` exempt —
                // its param types are concrete `:Int`, contributing no free var.)
                for (i, variant) in defn.variants.iter().enumerate() {
                    let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));
                    let mut allowed_vars = benign_overload_vars.clone();
                    if let Some((param_types, _ret)) =
                        accumulator.defn_type_vars.get(&internal_name)
                    {
                        for pt in param_types {
                            for v in cranelisp_types::free_vars(&self.apply_subst(state, pt)) {
                                allowed_vars.remove(&v);
                            }
                        }
                    }
                    if let Some((span, param)) =
                        self.find_ambiguous_value_position(state, &variant.body, &allowed_vars)
                    {
                        return Some(AmbiguousForm {
                            name: defn.name.clone(),
                            span,
                            clause_arity: Some(variant.params.len()),
                            param,
                        });
                    }
                }
                continue;
            }

            // §3.11.1 value-position scan for SINGLE-CLAUSE defns + `__expr`.
            //
            // The vars LEGITIMATELY polymorphic for this defn are the free vars
            // of its finalised function type — these are exactly what generalise
            // into the defn's scheme and are pinned per-instantiation by
            // monomorphisation (§4.4). A value-position type whose free vars are
            // ALL in this set is sound; a var OUTSIDE it is free-at-root →
            // ambiguous. This admits the polymorphic-accumulator fold while
            // rejecting an unpinned `(Option a)` in a concrete-scheme `main`.
            // The synthetic `__expr` REPL/eval wrapper is an EXECUTION BOUNDARY
            // (the value is evaluated NOW), not a reusable polymorphic template:
            // no residual var is legitimately quantifiable, so `allowed_vars` is
            // EMPTY (except the RD-3 benign resolved-dispatch stale vars) and the
            // polymorphic-skip below is suppressed (0585 VP-3/4/5).
            let is_entry_eval = defn.name.as_ref() == "__expr";
            let sig = accumulator.defn_type_vars.get(&defn.name);
            let allowed_vars: std::collections::HashSet<u32> = if is_entry_eval {
                // `__expr`'s only sound residual vars are the STALE vars left by a
                // RESOLVED dispatch (`(add2 3 4)` resolves its Int impl by
                // argument but the method-return var is not always unified back —
                // RD-3); those compute concretely at runtime. Exempts `r` in
                // `(let [r (add2 3 4)] r)` while still flagging a genuinely-free
                // generic value ref (`gcount` in `(if c gcount gother)`, VP-3).
                let mut benign = std::collections::HashSet::new();
                for variant in &defn.variants {
                    self.collect_resolved_dispatch_result_vars(state, &variant.body, &mut benign);
                }
                benign
            } else {
                sig.map(|(param_types, ret_ty)| {
                    let mut vars = std::collections::HashSet::new();
                    for t in param_types {
                        vars.extend(cranelisp_types::free_vars(&self.apply_subst(state, t)));
                    }
                    vars.extend(cranelisp_types::free_vars(&self.apply_subst(state, ret_ty)));
                    vars
                })
                .unwrap_or_default()
            };
            // §3.11.3 disposition 1 — a POLYMORPHIC definition (its own signature
            // retains a free type var after substitution) is a sound scheme:
            // every free var in its body is a scheme var, pinned per-instantiation
            // by monomorphisation, NOT free-at-root. Skip the body scan entirely.
            // This also keeps the verdict robust against the 0344 cross-defn
            // generalize/instantiate var-id reconciliation gap.
            let defn_is_polymorphic = !is_entry_eval && !allowed_vars.is_empty();
            if defn_is_polymorphic {
                continue;
            }
            for variant in &defn.variants {
                if let Some((span, param)) =
                    self.find_ambiguous_value_position(state, &variant.body, &allowed_vars)
                {
                    return Some(AmbiguousForm {
                        name: defn.name.clone(),
                        span,
                        // Single-clause defn: the plain fn-level message (no arity
                        // clause qualifier).
                        clause_arity: None,
                        param,
                    });
                }
            }
        }
        None
    }


    /// The ClauseIndependence (pre-drain) analogue of the ValueScan leg's
    /// resolved-`SigDispatch` exemption (OA-1). Collect the return vars of pending
    /// multi-sig/overload calls that WILL resolve, at the drain, to exactly one
    /// variant with a CONCRETE return — a `(h 7)`-shaped call whose return var is
    /// a fresh placeholder only because `resolve_pending_overloads` has not run
    /// yet (it runs AFTER this leg, per the clause-independence position). Such a
    /// var is not free-at-root; the drain pins it concrete.
    ///
    /// Read-only — it mirrors `resolve_pending_overloads`'s exact-match logic
    /// WITHOUT unifying, so a self-call's params are never acquired. A genuinely
    /// unresolved overload (no unique concrete-return match — `sum-to`'s
    /// free-arg self-call) contributes nothing, so its free arg stays flagged.
    pub(super) fn collect_pending_overload_result_vars(
        &self,
        state: &CheckState,
    ) -> std::collections::HashSet<u32> {
        let mut out = std::collections::HashSet::new();
        for (_span, base_name, arg_types, ret_type_var) in &state.pending_overload_resolutions {
            let concrete_args: Vec<Type> =
                arg_types.iter().map(|t| self.apply_subst(state, t)).collect();
            let Some(variants) = state.resolved_overloads.get(base_name) else {
                continue;
            };
            // The SAME overload-selection predicate the drain uses (Principle 7,
            // I-B): only a UNIQUE concrete-return match contributes a benign var.
            if let OverloadSelection::Unique(only) =
                select_unique_overload_variant(variants, &concrete_args)
            {
                let resolved_ret = self.apply_subst(state, &only.1);
                if resolved_ret.is_concrete() {
                    out.extend(cranelisp_types::free_vars(
                        &self.apply_subst(state, ret_type_var),
                    ));
                }
            }
        }
        out
    }


    /// POSITION-COMPLETE §3.11.1 ambiguity scan (S84 Wave 2, FIXME 0379/0380 —
    /// belt-and-braces ruling). Recursively scan an expression and fire the
    /// per-node verdict on the resolved type of EVERY codegen-reaching value
    /// position `for_each_child_expr` visits — not only `let` bindings. Returns
    /// the offending value's span.
    ///
    /// **Why position-complete (the 0379 hole).** The old scanner only applied
    /// the verdict on `Expr::Let` binding values, but a free `Type::Var` reaches
    /// codegen through many NON-`let` value positions — a `match` scrutinee
    /// (`(Pure (match (id Non) …))`), a fn-call arg, a vec element, a ctor field,
    /// an `if` branch, a `ParBind` binding. Those were recursed-into but not
    /// CHECKED, so an unpinned `(Option a)` in such a position slipped past both
    /// this check AND the backend codegen. The recursion was already complete (via
    /// `for_each_child_expr`); only the verdict was `let`-gated. This lifts the
    /// verdict to every value-producing child.
    ///
    /// **The verdict is FULL CONCRETENESS (spec/03-types.md §3.11.1, tightened
    /// commit `2290aa9`).** A codegen-reaching value whose resolved type is NOT
    /// fully concrete — i.e. retains ANY residual free `Type::Var` — is the
    /// §3.11.1 ambiguity error. There is **no representation-based exemption**:
    /// `(Vec a)`, `(Fn [a] a)`, `(Option a)`, a bare `Type::Var`, a `TyConApp`
    /// head — all reject when unpinned at a codegen-reaching value position, even
    /// when their machine shape is determinate. The strictness is full
    /// concreteness, NOT machine-shape determinacy.
    ///
    /// The verdict is therefore `!ty.is_concrete()` (equivalently
    /// `ConcreteType::from_type(ty).is_err()`) — the SAME full-concreteness
    /// predicate that gates the GOT-slot at the typecheck slot gate, and the same
    /// verdict the backend `ConcreteType` boundary encodes (no `Var` admissible).
    /// The two sides agree by construction (Principle 7; FIXME 0386,
    /// `design/arch/concrete-boundary-type.md` §1.4 / §3.1). Under full
    /// monomorphisation-from-roots a genuinely free var in a codegen-reaching
    /// position means NO root pins it → ambiguous (§3.11.1); the §4.4
    /// `allowed_vars` filter in [`Self::find_ambiguous_value_position`] excludes
    /// the scheme-quantified vars that are pinned per-instantiation (the
    /// polymorphic-accumulator fold's body positions), so this verdict fires only
    /// on a genuinely free-at-root var.
    pub(super) fn is_codegen_ambiguous_type(&self, ty: &Type) -> bool {
        !ty.is_concrete()
    }


    /// The per-node ambiguity verdict for a codegen-reaching VALUE position,
    /// grounded in the dispatch OUTCOME at a dispatch position (R16/R17;
    /// `return-poly-dispatch-signal.md` §3.2a) and in surface concreteness
    /// otherwise.
    ///
    /// - **Dispatch position** — the child is an `Apply` whose callee resolves
    ///   as a trait method. Consult the OUTCOME: the position is ambiguous IFF
    ///   the dispatch is a genuinely-unresolved return-type-poly dispatch
    ///   (`method_self_in_return` AND `method_return_dispatch_type` still `None`
    ///   after subst — `(zed)`, `:Zeroable (zed)`). A RESOLVED dispatch
    ///   (arg-directed `(add2 3 4)`, or context-pinned) is EXEMPT even when its
    ///   recorded surface type is a stale residual var — the RD-3 false-positive
    ///   fence, the exact cell the surface-concreteness gate reverted on (S109).
    /// - **Every other value** (a bare generic value ref `gcount`, a poly ctor
    ///   `None`, a `(Vec a)` let-binding) — the surface predicate `!is_concrete()`
    ///   is the verdict (§3.11.1, unchanged).
    fn value_position_is_ambiguous(&self, state: &CheckState, child: &Expr, resolved: &Type) -> bool {
        if let Expr::Apply { callee, span, .. } = child
            && let Expr::Var { name, .. } = callee.as_ref()
            && self.method_to_trait_with_state(state, name).is_some()
        {
            // Dispatch position — the OUTCOME is the discriminator, not the
            // (possibly stale) surface type.
            return self.method_self_in_return(state, name.as_ref())
                && self.method_return_dispatch_type(state, name, *span).is_none();
        }
        self.is_codegen_ambiguous_type(resolved)
    }


    /// Collect the free vars in the RESULT type of every RESOLVED trait-method
    /// dispatch in `expr` — the "benign stale vars" (RD-3). An arg-directed or
    /// context-pinned dispatch (`(add2 3 4)`) computes concretely at runtime,
    /// but its recorded result type may retain a residual var that is not
    /// unified back after subst. Those vars propagate into surrounding value
    /// positions (`(let [r (add2 3 4)] r)` — `r` inherits the stale var) and
    /// must NOT be read as §3.11 ambiguity at the `__expr` execution boundary.
    /// A genuinely-unresolved return-poly dispatch (`(zed)`) is EXCLUDED, so
    /// its var stays free-at-root and ambiguous.
    fn collect_resolved_dispatch_result_vars(
        &self,
        state: &CheckState,
        expr: &Expr,
        out: &mut std::collections::HashSet<u32>,
    ) {
        if let Expr::Apply { callee, span, .. } = expr {
            // A RESOLVED trait-method dispatch (arg-directed / context-pinned) —
            // NOT a genuinely-unresolved return-poly dispatch (RD-3, unchanged).
            let resolved_trait_dispatch = if let Expr::Var { name, .. } = callee.as_ref() {
                self.method_to_trait_with_state(state, name).is_some()
                    && !(self.method_self_in_return(state, name.as_ref())
                        && self.method_return_dispatch_type(state, name, *span).is_none())
            } else {
                false
            };
            // S110 B1 — a RESOLVED multi-sig/overload call (sig-dispatch) is also
            // benign. `resolve_pending_overloads` (the sole drain, run BEFORE this
            // POST-drain LEG-2 scan) unified the call's fresh return var with the
            // selected variant's concrete return AND recorded a `SigDispatch` at
            // the span; if any residual var lingers on the recorded surface type
            // it computes concretely at runtime, exactly like the trait case. This
            // exempts `r` in `(let [r (h 7 8)] r)` (the 2-arity sibling cell) with
            // the same discipline as the trait fence — a genuinely-unresolved
            // overload leaves NO `SigDispatch` and is not exempted.
            let resolved_overload = matches!(
                state.method_resolutions.resolved_calls.get(span),
                Some(cranelisp_types::ResolvedCall::SigDispatch { .. })
            );
            if (resolved_trait_dispatch || resolved_overload)
                && let Some(ty) = state.expr_types.get(span)
            {
                let resolved = self.apply_subst(state, ty);
                out.extend(cranelisp_types::free_vars(&resolved));
            }
        }
        for_each_child_expr(expr, |child| {
            self.collect_resolved_dispatch_result_vars(state, child, out);
        });
    }



    /// Returns the span of the first codegen-reaching value position carrying a
    /// free-at-root `Type::Var`, plus the offending binder NAME when that
    /// position is a bare `Expr::Var` (a param/`let` use) — so the diagnostic can
    /// name the unpinned param (0576). A synthetic `__`-prefixed binder is NOT
    /// surfaced (0568 — never leak an internal binder into user text).
    pub(super) fn find_ambiguous_value_position(
        &self,
        state: &CheckState,
        expr: &Expr,
        allowed_vars: &std::collections::HashSet<u32>,
    ) -> Option<(Span, Option<Symbol>)> {
        // The CALLEE of an `Apply` is a DISPATCH position, not a runtime value
        // position — an overloaded / multi-sig / trait-method callee carries a
        // transient bare `Type::Var` pinned-away by sig/dictionary resolution
        // (the §4.2 table lists `Apply { args }`, NOT the callee). Recurse INTO
        // the callee (a nested ambiguous arg there is still caught) but never
        // apply the per-node verdict ON it.
        let callee_span = match expr {
            Expr::Apply { callee, .. } => Some(callee.span()),
            _ => None,
        };

        // Apply the per-node verdict to every value-producing child, then recurse
        // into it. `for_each_child_expr` is the single child-enumeration source
        // of truth — visiting its children covers `Apply.args`, `Match`
        // scrutinee + arm bodies, `If` branches, `VecLit` elements, `ConstrADT`
        // fields, `Let`/`ParBind` bindings + body, `Lambda`/`Trace`/`Annotate`
        // inner — i.e. EVERY codegen-reaching value position.
        let mut found: Option<(Span, Option<Symbol>)> = None;
        for_each_child_expr(expr, |child| {
            if found.is_some() {
                return;
            }
            // The `working_program` ASTs are the INPUT shapes (their
            // `inferred_type` fields are unset — annotation lands on the stored
            // `ModuleEntry::Def.ast`). Read each child's type from
            // `state.expr_types` by span (still populated at the finalisation
            // boundary, before the accumulator drain), resolved through the final
            // substitution. Same mechanism the old `let`-leg used.
            let resolved = child
                .inferred_type()
                .map(|ty| apply(&state.subst, ty))
                .or_else(|| {
                    state
                        .expr_types
                        .get(&child.span())
                        .map(|ty| apply(&state.subst, ty))
                });
            if Some(child.span()) != callee_span
                && let Some(resolved) = resolved
                // The verdict: NOT fully concrete at a codegen-reaching value
                // position — ANY residual free `Type::Var` is the §3.11.1
                // ambiguity error (full concreteness, no representation
                // exemption; spec/03-types.md §3.11.1, tightened). A direct
                // constructor value (`None`, `(Some x)`) at an unpinned type is
                // rejected too — its tag-vs-pointer determinacy does NOT rescue
                // the unpinned var (the FIXME-0382 direct-constructor skip is
                // removed; `(is-some None)` is now the clean ambiguity error,
                // the spec's own worked example).
                //
                // BUT at a DISPATCH position (an `Apply` whose callee is a trait
                // method) the verdict consults the dispatch OUTCOME, not surface
                // concreteness (R16/R17; `return-poly-dispatch-signal.md` §3.2a):
                // an ARG-directed dispatch (`(add2 3 4)`) resolves its impl and
                // computes fine, yet the abstract method-return var recorded at
                // its span is not always unified back to the concrete return, so
                // `!is_concrete()` reads a STALE var and false-fires (the exact
                // S109-revert cell, RD-3). The outcome discriminates: a resolved
                // dispatch is exempt; only a genuinely-unresolved return-poly
                // dispatch (`(zed)`, `:Zeroable (zed)`) is ambiguous.
                && self.value_position_is_ambiguous(state, child, &resolved)
                // §4.4 nuance: a value position whose free vars are ALL
                // quantified into the enclosing defn's scheme is SOUND — the var
                // is pinned per-instantiation by monomorphisation (this admits
                // the polymorphic-accumulator fold's body positions). Only a var
                // OUTSIDE the defn's quantified set is free-at-root and genuinely
                // un-pinnable → ambiguous.
                // §4.4 nuance: a value position whose free vars are ALL
                // quantified into the enclosing defn's scheme is SOUND — pinned
                // per-instantiation by monomorphisation. For a CONCRETE-scheme
                // defn (the only kind scanned here — polymorphic defns are skipped
                // at the caller per §3.11.3 disposition 1) `allowed_vars` is empty,
                // so any free var is free-at-root → ambiguous.
                && cranelisp_types::free_vars(&resolved)
                    .iter()
                    .any(|v| !allowed_vars.contains(v))
            {
                // Name the unpinned binder when the position is a bare `Var`
                // (a param / `let` use), skipping synthetic `__`-prefixed
                // binders so the internal name never leaks (0568/0576).
                let binder = match child {
                    Expr::Var { name, .. } if !name.as_ref().starts_with("__") => {
                        Some(name.clone())
                    }
                    _ => None,
                };
                found = Some((child.span(), binder));
                return;
            }
            // Not flagged at this position — descend.
            found = self.find_ambiguous_value_position(state, child, allowed_vars);
        });
        found
    }


    /// Phase 3 (finalize): re-resolve deferred trait calls with the final
    /// substitution across every defn body (`program-decomposition.md` §2.1 P1).
    /// Per-defn resolution already ran in `check_form_body`, but cross-defn
    /// substitution refinement (e.g. constrained fns pinned by call sites) may
    /// enable additional resolutions. Updates the side maps for backward
    /// compatibility; AST annotation is already done per-defn. A multi-sig defn
    /// fans per `__v{i}` variant (the register-side internal-defn keys).
    pub(super) fn reresolve_deferred_calls(&self, state: &mut CheckState, working_program: &[TopLevel]) {
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
                        self.resolve_deferred_trait_calls(state, internal_defn.body());
                        self.resolve_value_position_trait_methods(state, internal_defn.body(), false);
                    }
                } else {
                    self.resolve_deferred_trait_calls(state, defn.body());
                    self.resolve_value_position_trait_methods(state, defn.body(), false);
                }
            }
        }
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
        // S110 W0.1b (§1.1.1): post-pass `resolved_targets` inserts (the
        // fn-value mono-rewrite carrier; the finalize-drained auto-curry leg)
        // land in `state.method_resolutions.resolved_targets` AFTER the per-form
        // snapshots that feed `accumulator.resolved_targets`. Sweep them into the
        // accumulator so the finalize view-rebuild
        // (`finalize_annotations_and_publish`) sees them — the carrier rides
        // UNREAD until W1, so this is behaviour-invariant.
        accumulator.resolved_targets.extend(taken.resolved_targets);
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
        self.reresolve_deferred_calls(state, working_program);

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

        // FIXME 0373(ii) / 0374 / 0378 — §3.11.1 ambiguity check (SECONDARY
        // backstop; the structural slot gate above is the PRIMARY SIGSEGV-
        // prevention mechanism), split into its two timing-incompatible duties
        // (S110 review "gate/drain ordering composition"). Per the user ruling
        // 2026-06-16 (spec §3.11 disposition triple), this check fires ONLY for a
        // CODEGEN-REACHING unpinned polymorphic value (§3.11.1 — a `let`-bound
        // value consumed at runtime while a type var is free), NOT for a bare
        // REPL polymorphic value (§3.11.2 — displayed via introspection) nor a
        // named polymorphic defn (§3.11.3 — sound, dead-for-codegen).
        //
        // LEG 1 — §5.1.2 clause independence, PRE-drain. A MULTI-ARITY defn's
        // per-clause param vars must be verdicted while still UNPINNED: running
        // AFTER `resolve_pending_overloads` (below) would let a deferred
        // cross-variant self-call acquire a sibling clause's concrete param type,
        // masking a genuine ambiguity (`multi_clause_defn_self_call_is_ambiguous_
        // not_panic`). Its position is UNCHANGED from before the split. The
        // §3.11.1 value scan for SINGLE-CLAUSE defns + `__expr` moves POST-drain
        // (LEG 2, below) so a deferred-overload return var / spuriously-poly
        // caller is settled first (B1/B2).
        if let Some(amb) = self.find_ambiguous_top_level_form(
            state,
            accumulator,
            working_program,
            AmbiguityScanPhase::ClauseIndependence,
        ) {
            return Err(CranelispError::TypeError {
                message: amb.message(),
                location: ErrorLocation::from_span(amb.span),
            });
        }

        // Pass 5: drain the deferred multi-sig/overload resolutions and
        // auto-curry. `resolve_pending_overloads` has exactly ONE call site (this
        // one) — the SINGLE drain of `state.pending_overload_resolutions`, which
        // `infer.rs` fills whenever a call targets an overloaded base (it mints a
        // fresh return var and defers, NOT resolving per-defn). It unifies each
        // deferred call's return var with the selected variant's concrete return
        // and records the `SigDispatch` resolution at the call span. (Corrects the
        // former "already resolved per-defn" comment — I1: nothing drains
        // per-defn; this ordering is load-bearing for the LEG-2 value scan below.)
        self.resolve_pending_overloads(state)?;
        self.resolve_auto_curry(state);

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
        // gets_concrete_instance`). It runs AFTER the §5.1.2 clause-independence
        // LEG (LEG 1, above) — which relies on a self-recursive multi-clause
        // defn's own param vars staying UNPINNED (a self-call would otherwise
        // acquire a sibling clause's concrete param type) — so that gate has
        // already errored before any overload resolution runs. Genuinely
        // polymorphic defns (`(defn empty [] [])`, scheme stays `(Fn [] (Vec a))`)
        // are non-concrete after re-generalize and stay `Polymorphic`.
        self.regeneralize_only_polymorphic(state, accumulator)?;

        // LEG 2 — §3.11.1 value-position scan for SINGLE-CLAUSE defns + `__expr`,
        // POST-drain (the S110 duty-split). It runs AFTER `resolve_pending_overloads`
        // (so a deferred-overload return var in a value position — `(let [r (h 7)]
        // r)` — is unified to the variant's concrete return, no false-reject: B1)
        // AND AFTER `regeneralize_only_polymorphic` (so a caller left spuriously
        // `Polymorphic` at drain time — `(defn main [] (let [u []] (Pure (h 7))))`
        // — is collapsed to `Concrete`, its unpinned-`[]` body then SCANNED rather
        // than poly-skipped: B2). It stays BEFORE `sweep_post_pass_outputs`
        // (below), which drains `state.expr_types` that both this scan and
        // `collect_unresolved_dispatch` read by span.
        if let Some(amb) = self.find_ambiguous_top_level_form(
            state,
            accumulator,
            working_program,
            AmbiguityScanPhase::ValueScan,
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

        // S91 Wave-7 (FIXME 0432 Face A): a multi-sig variant whose body
        // contains an in-body self-call has a return type that is only pinned
        // once `resolve_pending_overloads` resolves that self-call. But the
        // variant return types were captured into `resolved_overloads`, the
        // persisted `DefKind::Overloaded` base entry, and the mangled entries'
        // schemes back in `resolve_multi_sig_overloads` (Pass 2.5) — BEFORE
        // that resolution. Without this refresh the variant return stays a free
        // var: a later REPL cluster rehydrates `resolved_overloads` from the
        // stale persisted `OverloadVariant.ret_type` and a call to the variant
        // displays an unresolved type (`:a` instead of `:primitives/Int`).
        self.refresh_multi_sig_variant_ret_types(state, &multi_sig_mangled_names);

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
        );

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


    /// Collect the return-type-polymorphic dispatch sites that remained
    /// UNRESOLVED after the final substitution (the class-(b) carrier signal;
    /// `design/typecheck/return-poly-dispatch-signal.md` §3). A site qualifies
    /// when its callee is a nullary `Self`-returning trait method (`(zed)` with
    /// `zed [] self`) whose return-directed dispatch never selected an impl —
    /// `dispatch.rs::method_return_dispatch_type` still `None` at finalize (the
    /// recorded return type is still a free var). This is grounded in the
    /// dispatch OUTCOME, NOT surface concreteness, so an arg-directed dispatch
    /// (`(add2 3 4)`, whose method is not `Self`-returning and whose args
    /// selected the impl) is NEVER in the set — the S109-revert false-positive
    /// fence (RD-3).
    pub(super) fn collect_unresolved_dispatch(
        &self,
        state: &CheckState,
        working_program: &[TopLevel],
    ) -> Vec<UnresolvedDispatchSite> {
        let mut sites = Vec::new();
        for top in working_program {
            if let TopLevel::Defn(defn) = top {
                for variant in &defn.variants {
                    self.collect_unresolved_dispatch_in_expr(state, &variant.body, false, &mut sites);
                }
            }
        }
        sites
    }


    /// Recursive worker for [`Self::collect_unresolved_dispatch`]. `under_annotate`
    /// is set when the immediate parent is an `Expr::Annotate` — a `(zed)` that
    /// STAYS unresolved despite an annotation means the annotation is a
    /// non-disambiguating value-position CONSTRAINT (`:Zeroable (zed)`, R17); a
    /// concrete-type annotation (`:Int (zed)`) would have RESOLVED the dispatch,
    /// so it would never reach here.
    fn collect_unresolved_dispatch_in_expr(
        &self,
        state: &CheckState,
        expr: &Expr,
        under_annotate: bool,
        sites: &mut Vec<UnresolvedDispatchSite>,
    ) {
        if let Expr::Apply { callee, args, span, .. } = expr
            && args.is_empty()
            && let Expr::Var { name, .. } = callee.as_ref()
            && self.method_self_in_return(state, name.as_ref())
            && self.method_return_dispatch_type(state, name, *span).is_none()
        {
            sites.push(UnresolvedDispatchSite {
                span: *span,
                method: name.clone(),
                gap: if under_annotate {
                    DispatchGap::ValuePositionConstraint
                } else {
                    DispatchGap::ReturnTypePoly
                },
            });
        }
        let child_under_annotate = matches!(expr, Expr::Annotate { .. });
        for_each_child_expr(expr, |child| {
            self.collect_unresolved_dispatch_in_expr(state, child, child_under_annotate, sites);
        });
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
    ) {
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
            let resolved_targets_for_views = accumulator.resolved_targets.clone();
            let sym_table = &mut self.current_symbol_table_mut(state);
            // Reannotate `existing` from the final side maps + subst, then, for a
            // `Concrete{slot}` codegen target, rebuild `codegen_view` from the
            // refreshed (post-mono) variant.
            let reannotate_and_refresh_view =
                |name: &Symbol,
                 entry: &mut ModuleEntry<C>,
                 resolved_expr_types: &HashMap<Span, Type>,
                 method_resolutions: &HashMap<Span, ResolvedCall>,
                 subst: &Subst| {
                    if let ModuleEntry::Def { ast: Some(existing), kind, codegen_view: cv, .. } =
                        entry
                    {
                        annotate_variant_from_maps(existing, resolved_expr_types, method_resolutions);
                        apply_subst_to_variant(subst, existing);
                        if matches!(
                            kind.as_ref(),
                            DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                        ) {
                            *cv = build_concrete_codegen_view(name, existing, &pattern_ctors_for_views, &resolved_targets_for_views);
                        }
                    }
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
                                    );
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
                            );
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
                                );
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    // =================================================================
    // Unified multi-form check driver — drives `check_forms`'s internal
    // pipeline (Pass 1 register, Pass 2 check bodies, finalize) over a
    // `&[TopLevel]` slice and returns the `CheckResult` (including display
    // info). The production entry surface is `check_forms` in `form.rs`,
    // which discards the display-bearing `CheckResult`; this driver retains
    // it so in-crate tests can assert on inferred types / schemes.
    // =================================================================


    /// Collect only single-sig Defn entries (skip multi-sig).
    pub(super) fn collect_single_sig_defns(program: &[TopLevel]) -> Vec<&Defn> {
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

}
