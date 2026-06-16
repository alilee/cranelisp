---
number: 0384
target: /typecheck
filed_by: /arch
filed_at: 2026-06-16
sprint_filed: 84
refers_to: design/arch/concrete-boundary-type.md §4 (Phase 4 parts A/B/C), §2.2, §2.7; crates/cranelisp-typecheck/src/traits.rs (monomorphise_inner_parametric_hops, monomorphise_call mono-population seam, build_mangled_name); crates/cranelisp-typecheck/src/program.rs (local_parametric_call_triggers, collect_local_parametric_calls); crates/cranelisp-types/src/module.rs:640 (defined_symbols); src/worker.rs:620 (derive_codegen_batch::try_push)
status: open
---

# Phase 4 — mono-completeness (A) + generic-body-codegen elimination (B): every mono instance is `MonoExpr`-convertible; `Polymorphic` stops being a codegen target

## Issue

Phase 2b (mono population, `traits.rs:~1479`) landed with an interim
`allowed_vars` carve-out (`traits.rs:1514`) that ADMITS a monomorphised
instance whose body retains scheme-quantified `Type::Var`s — producing **no
`MonoExpr`** for that instance. The witness is `reduce-loop$Vec+Int+Int` (the
0344/0349 fold helper): `from_expr` returns `Err(NotConcrete::Var(34))` and the
carve-out swallows it.

**Phase 3 (backend consumes `MonoExpr`) cannot proceed until EVERY instance has
a `MonoExpr`.** The carve-out must become dead code; every minted instance must
be fully concrete.

Separately, a slot-less `Polymorphic` generic template is STILL emitted to
codegen (the 317× fire, FIXME 0381) because `defined_symbols()`
(`module.rs:640`) and `derive_codegen_batch::try_push` (`worker.rs:620`) both
exclude only `Constrained`/`Overloaded`, not `Polymorphic`.

## Root cause (part A) — diagnosed concretely (/arch, 2026-06-16)

The `reduce-loop$Vec+Int+Int` instance is a **spurious partial instance**. It is
minted by `monomorphise_inner_parametric_hops` (`traits.rs:1860`) recursing into
`reduce`'s body `(reduce-loop f init v (vec-len v) 0)`. At that point `f`,
`init`/`acc`, and the element type are still `reduce`'s OWN generic scheme vars
(`Var34`=accumulator, `Var31`=element); only `(vec-len v)→Int` and `0→Int` are
concrete. The hop is minted because the collection gate
`local_parametric_call_triggers` (`program.rs:3217`) **trigger-1**
(`result_is_bare_var`) fires (`reduce-loop`'s result IS `Var34`). So
`monomorphise_call` runs with `concrete_param_types =
[(Fn[Var34,Var31]→Var34), Var34, (Vec Var31), Int, Int]` — partial. The
genuine concrete instance `reduce-loop$Int+Vec+Int+Int` is ALSO minted (via the
concrete `reduce$Int+Vec` chain) and DOES succeed. The partial is redundant +
incomplete. (Also: `build_mangled_name` `filter_map`-drops the Var params, giving
the lossy `$Vec+Int+Int` name — a latent collision hazard.)

## Proposed resolution

See `design/arch/concrete-boundary-type.md` §4 for the full design. In brief:

**Part A — mono-completeness (DELETE the spurious mint, don't "complete" it):**
1. `monomorphise_inner_parametric_hops` (`traits.rs:~1892`) — add an
   all-args-concrete guard before minting an inner hop (skip if any
   `inner_arg_types[k]` is not `is_concrete()` after subst).
2. `local_parametric_call_triggers` (`program.rs:3217`) — **Option 1
   (preferred):** collapse trigger-1 + trigger-2 into a single
   all-args-concrete predicate (a mono instance is minted iff every arg is
   concrete; its result is then concrete by the per-instance re-check). Verify
   the 0373 result-hop guards stay green; if a genuine result-hop needs minting
   on a bare-var result with non-concrete args, escalate FIXME `target: /arch`.
3. `build_mangled_name`/`concrete_type_name` (`traits.rs:2065`) — add a
   `debug_assert!` that every param is concrete (turn the silent var-drop into a
   tripwire).
4. Mono-population seam (`traits.rs:1514–1558`) — DELETE the `allowed_vars`
   block + the `Err(NotConcrete::Var(id)) if allowed_vars.contains(&id) => {}`
   arm; keep the genuine-ambiguity-error arm. The deletion IS the completeness
   proof.

**Part C — 0344 reconciliation:** Part A touches no unification — it only
narrows which instances are minted. The subst-isolation at `traits.rs:1923–1943`
stays. Distinct concrete instantiations stay distinct by construction. The 0344
canary (`tests/regression.rs::mono_tier2_fold_accumulator_not_over_monomorphised`
+ `tests/spec_04_expressions.rs::polymorphic_accumulator_fold_does_not_over_unify`
+ the 0344/0349 unit guards) MUST stay green. NOTE: the fold e2e may stay red on
a *separate, pre-existing* 0344 inference-side over-unification bug
(`program.rs:912`) — that is NOT a Phase-4 gate; the Phase-4 obligation is only
that no partial instance is minted and `from_expr` succeeds on every minted one.

**Part B — generic-body-codegen elimination (lands AFTER part A):** add
`| DefKind::UserFn { fn_state: UserFnState::Polymorphic(_) }` to the excluded set
in BOTH `defined_symbols()` (`module.rs:641`, /dev typecheck) AND
`derive_codegen_batch::try_push` (`worker.rs:620`, /dev int). Consolidate to one
shared predicate if the wave allows (Principle 7). Rewrite the
`module.rs:631–639` rustdoc to state the `Polymorphic`/`Constrained` codegen-
target symmetry. No new int prelude-loading code path — the concrete-instance
codegen path already exists; part B is subtractive at the gate.

## Operational implication / Context

- **Sub-phase order: A strictly before B.** A makes every minted instance
  concrete (carve-out deletable). B then removes the template fallback. B-before-A
  would emit no template AND leave incomplete instances with no `MonoExpr`.
- **One /dev wave, two sub-steps** is plausible (the completeness fix is a gate
  tightening, not a body-rewrite). Part A's unit tests green before part B's
  filter flips.
- **Unit tests (mandatory):** part A — a fold-shape instance mints ONLY concrete
  `reduce-loop` instances (no `$Vec+Int+Int` partial); `from_expr` succeeds on
  every minted instance; the 0373 result-hop guards stay green. Part B —
  `defined_symbols()` + `derive_codegen_batch` exclude a `Polymorphic` entry,
  include its `Concrete` mono instance.
- **E2E validation (the HIGH-risk gate):** after A+B, the full prelude/stdlib
  suite is green with NO generic template emitted (317× gone — FIXME 0381's
  fire). Every prelude-using e2e + the stdlib exemplar tests are witnesses.
- **Cross-crate handoff:** part A is wholly `cranelisp-typecheck` (/dev
  typecheck). Part B is `cranelisp-types` `defined_symbols()` (the type lives in
  /arch-owned `cranelisp-types`, but the filter body is a /dev-typecheck edit —
  the signature is unchanged so no facade move) + `src/worker.rs` (/dev int).
  Coordinate the two filter sites in lockstep. **This unblocks Phase 3** (backend
  consumes `MonoExpr`, FIXME-tracked separately) and **closes FIXME 0381** (part
  B) — the deferred 0375 backstop is DELETED in Phase 3, not re-armed.
