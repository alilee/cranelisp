---
number: 0374
target: /typecheck
filed_by: /arch
filed_at: 2026-06-16
sprint_filed: 83
refers_to: design/arch/bounded-contexts.md §2 (monomorphisation-from-roots note), design/arch/bounded-contexts.md §3 invariant 9, crates/cranelisp-typecheck/src/program.rs + crates/cranelisp-typecheck/src/traits.rs (collect_local_parametric_calls, monomorphise_inner_parametric_hops), commits 5634dd3 + 9e57330 + the 0355 machinery
status: open
---

## S84 Wave 1 — PARTIALLY DELIVERED (/dev, 2026-06-16)

The SIGSEGV-prevention core landed (clean, zero regressions); the ambiguity
backstop is deferred. Disposition:

- **DELIVERED — the structural slot gate (`slot ⟺ concrete`).** Single-sig
  (`program.rs` determination point) + multi-sig variant + the
  `regeneralize_defn_schemes` demotion now route a non-concrete unconstrained
  def to the slot-less `UserFnState::Polymorphic` arm. **Refinement:** the gate
  fires only when the def is monomorphisable FROM A CALL SITE
  (`fn_type_is_monomorphisable_from_params` — param-position vars). A
  result-only-var def (`(Fn [] (Option a))` — a `test-*` discovery root, a
  `None`-returning fn) stays `Concrete`-with-a-slot: it cannot be monomorphised
  by args and is an entry point, not a polymorphic template. `__expr` is
  likewise excluded (a top-level value to evaluate). This refinement avoided
  ~30 regressions (test discovery, REPL display, multi-sig `__expr`).
- **DELIVERED — systematic mono-from-roots for the Wave-0 `(Box a)` gap.** Three
  collectors extend `pass4_monomorphise`: (a) the broadened
  `collect_local_parametric_calls` (now also triggers on an all-concrete-args
  direct call `(g 1)` to a `Polymorphic` callee, not only a bare-`Var` result —
  the 0344 fold is preserved by the all-args-concrete guard); (b)
  `collect_parametric_fn_value_args` (a polymorphic fn passed as a HOF argument
  value — the `(thru mk …)` shape — mints `mk$Int` and rewrites the fn-value
  `Var` in the enclosing stored AST to the mangled name so the backend takes the
  concrete slot); (c) monomorphic self-recursion dispatch in `monomorphise_call`
  (`collect_self_apply_calls` — a `Polymorphic` fn's self-call redirects to its
  own mono instance, since the original is slot-less). Both Wave-0 box guards
  flipped GREEN; all bare-Int GREEN-stay guards + the 0344/0349 fold canary held.
- **DELIVERED — cache 5→6 bump** (`crates/cranelisp-backend/src/cache/mod.rs`,
  the `Polymorphic` serde arm; the single backend touch).
- **DEFERRED — the 0373(ii) ambiguity backstop.** Implemented
  (`find_ambiguous_top_level_form`) but wired-but-dormant: enabling it regresses
  pre-existing self-documenting-REPL display tests that assert spec-§3.11-
  forbidden behaviour (bare `None`/`[]` display). Blocked on /spec + /repl + /qa
  arbitration — **FIXME 0378**. The slot gate already makes a residual
  `Type::Var` structurally unconstructable at codegen, so the deferral does NOT
  re-open the SIGSEGV; the ambiguity check is the design's named SECONDARY
  backstop. Its two Wave-0 guards
  (`mono_ambiguous_unconstrained_top_level_var_rejected_neg`,
  `mono_ambiguous_neg_does_not_reach_codegen`) carry RED until 0378 is ruled.

This FIXME stays OPEN: the gate + box-mono core is done, but the ambiguity-rule
half of the reshaped resolution is deferred to 0378. 0375 (/backend) is now
unblocked for the SIGSEGV-prevention purpose (a `Type::Var` no longer reaches
`classify` as a callable for the monomorphisable-from-params shapes), but the
result-only-var carve-out means concreteness is not yet TOTAL — see 0378 issue 3
(test-fns-as-roots) before 0375's `classify(Type::Var)→unreachable!` lands.

# Typecheck: Tier 2 — systematic full monomorphisation from the roots (no Type::Var reaches codegen)

## Issue

The 0373 investigation settled full monomorphisation-from-roots as the architectural target (rank-1 HM ⇒ complete; keeps representation backend-internal; the only sound fix over the rejected runtime-RC-witness / tagged-value alternatives). The architecture is recorded at `bounded-contexts.md` §2 (typecheck) + §3 invariant 9 (backend RC soundness).

**S83 delivered Tier 1 + Tier 1.5** (`5634dd3`, `9e57330`): polymorphic-**result-hop** monomorphisation, same-module and cross-module, routed through the 0355 machinery (`collect_local_parametric_calls`, `monomorphise_inner_parametric_hops`). This closed the SIGSEGV that motivated the investigation but covers only a subset — the result-hop / 0355-constrained / cross-module cases.

**Tier 2 is the systematic remainder:** generalise the per-`(Def, type-args)` instance model so that **every reachable fn instance** has fully concrete parameter and result types, under any reachable instantiation — so NO `Type::Var` reaches the codegen boundary. This is the prerequisite for backend RC soundness: while a `Type::Var` can flow to codegen, `HeapCategory::classify(Type::Var)` falls back to `Mixed` and emits the unsound `<1024` RC guard (negative/`≥1024` `Int` misread as a heap pointer → use-after-free on the dec path; BC §3 invariant 9 has the full statement).

## S84 RE-SHAPE — the structural slot-gate is primary; mono is forced by the representation (user-ratified 2026-06-16)

A user architectural ruling (mid-S84-Phase-5) generalises Principle 20 and re-grounds this FIXME. **The invariant: a GOT slot is the value-capability of a CONCRETE callable — a def has a slot ⟺ its type is fully concrete (no `Type::Var`; `Type::is_concrete()`).** This is broader than S83's "a constrained template has no slot": a *plain parametric/generic* def (`id : ∀a. a→a`, a HOF whose result is `(Box a)`) carries **no trait constraints** yet is **not** concrete, and must equally be slot-less. Only its monomorphised concrete instances are slotted.

**Confirmed leak (the root this FIXME must close).** The S83 slot-allocation gate tests **`constraints.is_empty()` (trait-bounds-emptiness) when it must test `is_concrete()` (no `Type::Var`)**:
- `crates/cranelisp-typecheck/src/program.rs:947` (single-sig) — `let constrained_fn = if !trial_scheme.constraints.is_empty() { …Constrained… } else { …allocate_got_slot()… Concrete… };`
- `crates/cranelisp-typecheck/src/program.rs:1143` (multi-sig) — same predicate, same `else`-arm `allocate_got_slot()` at `:1165`.
- Reuse / writeback legs sharing the constraint-emptiness gate: `:919`, `:1129`, `:1312` (`existing_callable_slot` / `redef_slots`).

A generic-but-unconstrained def falls into the `else` arm → `UserFnState::Concrete { got_slot }` **while still carrying a `Type::Var`** (`crates/cranelisp-types/src/module.rs:1710` `UserFnState`). That non-concrete-def-with-slot reaches `HeapCategory::classify(Type::Var)` (`crates/cranelisp-backend/src/heap.rs:456`) → the unsound `<1024` RC guard → the `(Box a)`-through-HOF SIGSEGV the Wave-0 guard `mono_tier2_generic_adt_field_through_hof_no_crash` pins.

## Proposed resolution (re-shaped)

**Two coupled changes — the structural gate AND the systematic mono — land together:**

1. **Correct the slot-allocation gate to `is_concrete()` (the structural primary; Principle 18/20).** At the determination point in `finalize_check_form` (`program.rs:947`/`:1143` + the reuse legs `:919`/`:1129`/`:1312`), allocate the `Concrete { got_slot }` arm **only when the finalised type is fully concrete** (`!trial_scheme.ty.contains_var()`, i.e. `trial_scheme.ty.is_concrete()` — the `cranelisp-types` helper landed by /arch in this sprint, `crates/cranelisp-types/src/types.rs`). A determined-but-non-concrete **unconstrained** generic def must get a **slot-less** `fn_state` — a new `UserFnState` arm sibling to `Constrained` (working name `Polymorphic` / parametric: slot-less, distinguished from `Constrained` only in *why* — unpinned type vars vs trait dictionaries). This makes `Concrete{slot} ∧ non-concrete-type` **unconstructable** (BC §7 "Callability is structural", S84 generalisation). *Whether the slot-less state is a distinct new `UserFnState` variant or a reuse of the existing slot-less shape is /design(typecheck) + /dev(typecheck)'s call within the `cranelisp-types` shape — /arch fixes only that `Concrete` carries `got_slot` and is constructed only when `is_concrete()`.*

2. **Systematic full mono-from-roots so the slot-less set is genuinely the never-used-as-a-value set.** Generalise the Tier-1/1.5 polymorphic-result-hop machinery (`collect_local_parametric_calls` `program.rs:2491`, `monomorphise_inner_parametric_hops` `traits.rs:1731`, `collect_apply_var_calls` `traits.rs:1888`) into a cluster-level worklist/fixpoint over reachable `(Def, concrete-type-args)` instances, EXTENDING `pass4_monomorphise` (`program.rs:2300`) — NOT a parallel pass (Principle 7). **Wave-0 scope refinement: the deliverable gap is the `(Box a)`-field-through-HOF instance, NOT the bare-Int HOF instances** (those already mono cleanly — GREEN-stay guards). With the gate corrected, "is this def concrete?" is answered by *whether it has a slot* — so coverage is forced by the representation: mint a concrete slotted instance for every *reachable* use; anything left slot-less is either never-used-as-a-value (fine) or the 0373(ii) ambiguity error. **Pinned risk: the 0344/0349 fold-accumulator over-monomorphisation** — the `collect_local_parametric_calls` result-var gate deliberately preserves the fold accumulator's shape; the gate-relaxation must not re-collapse it (the 0344/0349 unit tests + `mono_tier2_fold_accumulator_not_over_monomorphised` canary are the guards).

3. **Ambiguity check (0373 ii) is a SECONDARY backstop.** `Type::contains_var()` at the post-inference finalisation boundary (`finalize_check_result_inner`, between `regeneralize_defn_schemes` `program.rs:1349` and `pass4_monomorphise` `program.rs:1438`) raises `CheckError::AmbiguousType` for a residual top-level var no reachable instantiation pins. Under total Tier-2 coverage + the structural gate, this catches only genuinely-ambiguous top-level forms — it is not the mechanism that prevents the SIGSEGV (the slot gate is).

**Cross-crate impact:**
- **`cranelisp-types`:** `Type::is_concrete()` LANDED by /arch this sprint (one additive `public-api.txt` line; `crates/cranelisp-types/src/types.rs`). **IF a new `UserFnState` variant is added** (the slot-less `Polymorphic` arm), that is a `cranelisp-types` shape change owned by /arch — file FIXME `target: /arch` for the variant, OR /arch lands it in the same wave; it is one additive enum variant, no `public-api.txt` removal. `UserFnState` already serde-derives.
- **typecheck:** the corrected gate + the systematic enumeration (above). No new boundary signature; more `MonoDefn`/`Defn` instances through the existing enumeration.
- **backend:** no slot-read change — `callable_got_slot()` already returns the slot off the matched variant; a slot-less arm simply returns `None` (the path is `resolve_got_target` at `crates/cranelisp-backend/src/compiler/mod.rs:186`). 0375 makes `classify(Type::Var)` a backstop that can never fire.
- **cache schema (`CACHE_SCHEMA_VERSION`, `crates/cranelisp-backend/src/cache/mod.rs:154`, currently `5`):** **IF a new `UserFnState` variant lands, the serde shape of `DefKind`/`UserFnState` changes → bump 5→6** (the no-serde-shape-change-without-a-bump discipline, cache/mod.rs §71). This bump is /backend's (the const lives in `cranelisp-backend`), landed in the SAME change-set as the variant. If the slot-less state reuses an existing serde shape, no bump. /design(typecheck) determines which in Wave 1; flag to /backend if a variant is added.

The fix lands with unit tests at the typecheck seam per the per-fix discipline (the gate-correction unit test: a generic-unconstrained def gets NO slot; a concrete instance DOES); the e2e is the Wave-0 `mono_tier2_generic_adt_field_through_hof_no_crash` + `mono_tier2_all_modes_concreteness_equivalence` flipping green (coordinate with /qa).

## Operational implication / Context

**Gates two downstream FIXMEs:**
- **0373 part (iii)** (/spec) — relaxing §12.1 to backend-internal representation is gated on Tier 2 concreteness.
- **0375** (/backend) — making `classify(Type::Var)` an assert/panic and retiring the `<1024` guard from the `Type::Var` path is gated on Tier 2 guaranteeing concrete types at codegen.

Companion: FIXME 0373 part (i)/(ii) (/spec — state rank-1 HM; ambiguity rule). Likely a dedicated sprint (the investigation framed Tier 2 as the systematic remainder warranting its own increment). Architecture conclusion: `bounded-contexts.md` §2 + §3 invariant 9.
