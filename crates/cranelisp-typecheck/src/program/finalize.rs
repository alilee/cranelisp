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
    ) {
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
                Some(existing_callable_slot(&st, name.as_ref())
                    .unwrap_or_else(|| st.allocate_got_slot()))
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
    ) -> Option<AmbiguousForm> {
        for top in working_program {
            let TopLevel::Defn(defn) = top else { continue };
            // The vars LEGITIMATELY polymorphic for this defn are the free vars
            // of its finalised function type — these are exactly what generalise
            // into the defn's scheme and are pinned per-instantiation by
            // monomorphisation (§4.4: "a var quantified into the scheme is
            // fine"). A value-position type whose free vars are ALL in this set
            // is sound; a value position carrying a var OUTSIDE it is genuinely
            // un-pinnable (free-at-root) → ambiguous. This is the discriminator
            // that admits the polymorphic-accumulator fold (`reduce`'s body
            // positions carry `reduce`'s own scheme vars) while rejecting an
            // unpinned `(Option a)` in a concrete-scheme defn like `main`.
            let sig = accumulator.defn_type_vars.get(&defn.name);
            let allowed_vars: std::collections::HashSet<u32> = sig
                .map(|(param_types, ret_ty)| {
                    let mut vars = std::collections::HashSet::new();
                    for t in param_types {
                        vars.extend(cranelisp_types::free_vars(&self.apply_subst(state, t)));
                    }
                    vars.extend(cranelisp_types::free_vars(&self.apply_subst(state, ret_ty)));
                    vars
                })
                .unwrap_or_default();
            // §3.11.3 disposition 1 — a POLYMORPHIC definition (its own signature
            // retains a free type var after substitution) is a sound scheme:
            // EVERY free var in its body is a scheme var, pinned per-instantiation
            // by monomorphisation at concrete use sites, NOT free-at-root. The
            // codegen-reaching ambiguity error (§3.11.1 / disposition 2) is a
            // property of a use at a CONCRETE-scheme definition (`main`-like) that
            // leaves a var unpinned — never of a polymorphic definition. Skip the
            // body scan for a polymorphic defn entirely. This also keeps the
            // full-concreteness verdict robust against the 0344 cross-defn
            // generalize/instantiate var-id reconciliation gap: a polymorphic
            // defn's body may carry a body-local instantiation var that the
            // pre-body `defn_type_vars` signature did not record by the same id
            // (the fold `collect`'s `vec-push : (Fn [(Vec a) a] (Vec a))` arg) —
            // that var is quantifiable, not ambiguous (§3.11.3). The narrowing is
            // disposition-faithful: a non-concrete signature ⇒ disposition 1.
            let defn_is_polymorphic = !allowed_vars.is_empty();
            if defn_is_polymorphic {
                continue;
            }
            let multi_arity = defn.variants.len() > 1;
            for variant in &defn.variants {
                if let Some((span, param)) =
                    self.find_ambiguous_value_position(state, &variant.body, &allowed_vars)
                {
                    return Some(AmbiguousForm {
                        name: defn.name.clone(),
                        span,
                        // The offending CLAUSE (0576) — named by its arity only
                        // for a multi-arity `defn`, so a single-sig defn keeps the
                        // plain message.
                        clause_arity: multi_arity.then_some(variant.params.len()),
                        param,
                    });
                }
            }
        }
        None
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
                && self.is_codegen_ambiguous_type(&resolved)
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
        self.regeneralize_defn_schemes(state, accumulator);

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
        self.regeneralize_defn_schemes(state, accumulator);

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
        // prevention mechanism). Per the user ruling 2026-06-16 (spec §3.11
        // disposition triple), this check fires ONLY for a CODEGEN-REACHING
        // unpinned polymorphic value (§3.11.1 — a `let`-bound value consumed at
        // runtime while a type var is free), NOT for a bare REPL polymorphic
        // value (§3.11.2 — displayed via introspection) nor a named polymorphic
        // defn (§3.11.3 — sound, dead-for-codegen). `find_ambiguous_top_level_form`
        // is scoped to `let`-binding value positions, so the two REPL display
        // guards stay green and named poly defns are admitted.
        if let Some(amb) = self.find_ambiguous_top_level_form(state, accumulator, working_program) {
            return Err(CranelispError::TypeError {
                message: amb.message(),
                location: ErrorLocation::from_span(amb.span),
            });
        }

        // Pass 5: overloads and auto-curry already resolved per-defn.
        // Drain any remaining entries (e.g., from mono defn generation).
        self.resolve_pending_overloads(state)?;
        self.resolve_auto_curry(state);

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
