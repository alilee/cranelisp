---
number: 0522
target: /dev  # cranelisp-backend
filed_by: /sprint  # from /review of B3.2 coupled borrow-elision (ffd3b67)
filed_at: 2026-07-04
sprint_filed: 102
refers_to: crates/cranelisp-backend/src/compiler/control_flow/fn_as_value.rs:436-451 (emit_d24_adaptation); crates/cranelisp-backend/src/compiler/rc_emission.rs:302 (protect_return_value); crates/cranelisp-backend/src/ownership_facts.rs:87 (vec-get Borrowed+ProjectionOf); design/backend/ownership-codegen.md §3.3/§3.4
status: open
---

# emit_d24_adaptation ProjectionOf arm — mis-ordering (latent UAF) + protect double-count — MUST fix before §3.3

## Issue (from /review of the B3.2 coupled borrow-elision core, `ffd3b67`)

Two coupled defects in the `ProjectionOf` arm of `emit_d24_adaptation`, both
**currently DORMANT** (no live UAF in `ffd3b67`), that activate the moment §3.3
(in-frame projection propagation) lands OR the analysis routes a
`ProjectionOf`-result user fn to a value-use:

1. **Mis-ordering → latent UAF.** Borrowed-param decs run BEFORE the ProjectionOf
   materialization inc:
   ```
   for i: if param i Borrowed { dec(arg[i]) }      // dec FIRST
   if result == ProjectionOf(_) { inc(result) }     // inc AFTER
   ```
   For summary `{param k = Borrowed, result = ProjectionOf(k)}` (exactly
   `vec-get`'s declared shape, `ownership_facts.rs:87`), `dec(arg[k])` can free
   the object `result` projects into (rc==1), then `inc(result)` touches freed
   memory → UAF + dangling return. **Fix**: emit the materialization inc BEFORE
   the Borrowed decs, or exclude the projection-root param from the dec loop.

2. **Double-count → latent leak.** The moded callee's `protect_return_value`
   (`rc_emission.rs:302`) still incs a non-`Fresh` result (`return_is_fresh_by_summary`
   elides only `Fresh`), so a wrapped ProjectionOf-result fn is inc'd once by the
   callee's protect AND again by the wrapper adaptation → over-retain by 1.
   **Fix**: reconcile — the adaptation inc and the callee protect must not both
   fire for a ProjectionOf result.

## Why dormant now
`vec-get` (the only Borrowed+ProjectionOf leaf) is inline-lowered at
`fn_as_value.rs:549–557` BEFORE the adaptation arms, so its summary never reaches
`emit_d24_adaptation`; and user functions currently compose to `Fresh`/`AliasOf`
(traced `get0 [v] (vec-get v 0)` → `result=Fresh`), so no ProjectionOf-result
user fn reaches the wrapper.

## Coupled with the §3.1/§3.5 asymmetry (also from /review)
The §3.1 direct-call path applies NO result-mode handling — a ProjectionOf/AliasOf
result is treated as an owned rc=1 temp (self-consistent today: callee protect incs,
caller decs as owned). When §3.3 changes the callee to return an un-inc'd borrowed
view, ALL THREE sites must change together: the direct-caller (bind into
`borrowed_vars`, no dec), the wrapper (drop the now-correct single materialization),
and the callee. **§3.3 must land as one coupled change across the three sites, with
this ordering/double-count fix as its precondition.**

## Operational implication
No failing test today (unreachable — hence a FIXME, not a repro, per the
testless-future-work exception). Resolve as the FIRST step of §3.3 (or standalone
pre-emptive hardening). The B3.2 core is sound as shipped without it.
