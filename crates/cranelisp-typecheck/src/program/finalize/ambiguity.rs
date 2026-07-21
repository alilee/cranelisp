//! The §3.11 / §3.11.1 codegen-ambiguity scan — the finalize post-pass that
//! decides whether a residual free type variable REACHES a codegen position
//! (reject, with the located `AmbiguousForm` diagnostic) or is a legitimately
//! polymorphic definition / result-only var (admit), plus the §3.11 companion
//! signal `collect_unresolved_dispatch` (a return-type-polymorphic dispatch that
//! selected no impl — `design/typecheck/return-poly-dispatch-signal.md`).
//!
//! Cut out of `program/finalize.rs` at the S115 W4 re-budget (FIXME 0722): the
//! scan is a self-contained admission decision over the settled substitution,
//! with no state channel shared with the finalize driver beyond the read-only
//! `CheckState`.

use super::*;

#[derive(Debug)]
/// A located §3.11.1 codegen-reaching ambiguity, enriched with the offending
/// arity clause + param for the diagnostic (0576).
pub(crate) struct AmbiguousForm {
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
    /// unpinned PARAM when known (0576) and falls back to the plain fn-level
    /// message otherwise.
    ///
    /// **S112 re-grounding (MS-8, §5.1.2 back-flow).** A multi-signature `defn`
    /// is inference-equivalent to its clauses written as separate,
    /// mutually-recursive functions (spec §5.1.2, settled S111 `c9f05b64`), so a
    /// clause left genuinely unpinned is the §3.11 ambiguity the *equivalent
    /// standalone function* would also raise — NOT an artefact of "each arity
    /// clause is type-checked independently." The message keeps the per-clause
    /// naming (arity + param) but cites §3.11 / the standalone-equivalence
    /// rationale, never the retired independence framing.
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
                "ambiguous type: the parameter `{p}` in {where_} remains unpinned \
                 after inference — the equivalent standalone function would also \
                 fail to infer it (spec §3.11); add a `:Type` annotation to `{p}`"
            ),
            None => format!(
                "ambiguous type; add an annotation to pin the type of the \
                 polymorphic value bound in {where_} (spec §3.11)"
            ),
        }
    }
}

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
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
            let is_multi_arity = defn.variants.len() > 1;

            if is_multi_arity {
                // §5.1.2 back-flow (S112 leg a, FIXME 0642). A multi-signature
                // `defn` is inference-equivalent to its clauses written as
                // separate, mutually-recursive top-level functions (spec §5.1.2,
                // settled S111 `c9f05b64`). There is NO clause-independence
                // barrier: a clause pinned by a sibling self-call carries that
                // sibling's concrete param types — the back-flow admitted by
                // `resolve_pending_overloads`, which runs BEFORE this POST-drain
                // scan (the former pre-drain `ClauseIndependence` leg is deleted).
                //
                // Each clause is scanned with the SAME logic a single-clause defn
                // uses (below): `allowed_vars` = the free vars of that clause's
                // SETTLED (`apply_subst`-applied, post-drain) `__vN` signature.
                //   - A clause pinned concrete by a sibling self-call (`rp4`'s
                //     `p`/`rot`) has an EMPTY allowed set → scanned; nothing free
                //     remains → admitted (back-flow).
                //   - A clause left genuinely polymorphic (`([:a x] x)`) has a
                //     NON-empty allowed set → the `defn_is_polymorphic` skip →
                //     admissible (§5.1.2 admissible-poly), exactly as a single-sig
                //     polymorphic defn (§3.11.3 disposition 1).
                //   - A clause param GENUINELY unpinned at a codegen-reaching
                //     position (neither its own body nor any sibling self-call
                //     pins it) → the §3.11 ambiguity error — the same disposition
                //     the equivalent standalone function would get.
                for (i, variant) in defn.variants.iter().enumerate() {
                    let internal_name = Symbol::from(format!("{}__v{}", defn.name, i));
                    let allowed_vars: std::collections::HashSet<u32> = accumulator
                        .defn_type_vars
                        .get(&internal_name)
                        .map(|(param_types, ret_ty)| {
                            let mut vars = std::collections::HashSet::new();
                            for t in param_types {
                                vars.extend(cranelisp_types::free_vars(&self.apply_subst(state, t)));
                            }
                            vars.extend(cranelisp_types::free_vars(&self.apply_subst(state, ret_ty)));
                            vars
                        })
                        .unwrap_or_default();
                    // A genuinely-polymorphic clause is admissible — its free vars
                    // quantify into the clause's own scheme, pinned per-
                    // instantiation by monomorphisation. Skip the body scan,
                    // exactly as the single-clause `defn_is_polymorphic` skip below.
                    if !allowed_vars.is_empty() {
                        continue;
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
}

#[cfg(test)]
mod tests;
