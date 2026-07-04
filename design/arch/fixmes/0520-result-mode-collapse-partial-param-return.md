---
number: 0520
target: /dev  # cranelisp-typecheck (pass5 result-mode); /sprint re-routed from /design — resolution is a join-lattice fix, not a design-space question
filed_by: /dev
filed_at: 2026-07-04
sprint_filed: 102
refers_to: design/typecheck/ownership-inference.md §4.2, design/arch/ownership-inference.md §4.4, design/backend/ownership-codegen.md §3.3
status: open
---

# ABI-half `result` collapses a partial control-flow param-return to `Fresh`

## Issue

`pass5_ownership` sets a callable's `ModeSummary.result` to `ResultMode::Fresh`
when the function returns one of its **parameters through a partial control-flow
path** — i.e. some but not all return arms yield the param. The ABI-half is
documented SOUND (8b review); this is a concrete counterexample surfaced by the
B3.2 backend consumer.

Observed (`CRANELISP_OWNERSHIP_TRACE=1`), `tests/fixtures/clif_baseline/corpus/04_vec_cow_loop.cl`:

```
(defn build [v :Int i :Int n]
  (if (eq-i64 i n) v                       ; base case returns param v
    (build (vec-push v i) (add-i64 i 1) n)))
;; → build: modes=[Owned, Copy, Copy] result=Fresh flow=[IntoResult, …]
```

`build` returns param `v` in the base case, so its result mode must be
`AliasOf(0)` (or a conservative may-alias), **not** `Fresh`. The analysis DOES
detect the flow (`flow[0]=IntoResult`), but `result` still collapses to `Fresh`.

Contrast — the analysis IS correct when the alias is total:
- `(defn idv [v] v)` → `result=AliasOf(0)` ✓
- `(defn viaif [b v] (if b v v))` → `result=AliasOf(1)` ✓ (both arms same param)
- `(defn wrap [v] (idv v))` → `result=AliasOf(0)` ✓ (direct-Apply composition)

Only the **partial** case (`(if c v (fresh …))`, tail-recursion whose base
returns a param) collapses to `Fresh`.

## Why it matters (soundness, not cosmetics)

A backend consumer that trusts `result=Fresh` to mean "not aliased to any
param/binding" will elide a needed RC operation and free the returned param →
UAF that RC balance cannot catch. B3.2's `protect_return_value` elision hit
exactly this: the unrestricted `result==Fresh` gate SIGABRTed `build`
(`04_vec_cow_loop`). B3.2 shipped with a **consumer-side counterweight** — the
elision is restricted to a direct `Apply` body, which structurally excludes the
control-flow-collapse class (`design/backend/ownership-codegen.md` §3.3,
`return_is_fresh_by_summary`). That is a narrowing, not a cure: the same latent
unsoundness constrains the FULL §3.1/§3.2 caller/callee borrow-elision and the
§3.5 result-mode consumption, which cannot rely on `result` alone for
if/match/tail bodies until the analysis widens partial param-returns.

## Proposed resolution

Widen `result` at the join: when a param may reach the result on ANY return path
(the `flow=IntoResult` the analysis already computes), the result mode must be at
least the conservative may-alias — `AliasOf(i)` when a single param, or a
widened "may-alias-a-param" point if the design wants a distinct lattice element.
`Fresh` must be reserved for provably-no-param-reaches-result. `/design`
(typecheck) sizes whether this is a join-lattice fix in `pass5_ownership` or a
carrier addition; the backend then drops the `Apply`-body restriction and trusts
`result` for all body shapes.

## Operational implication / Context

Until resolved, backend borrow-elision consumers must treat `result=Fresh` as
reliable ONLY for direct-`Apply` bodies (the fixpoint composes Apply results
correctly). The B3.2 `return_is_fresh_by_summary` restriction is the standing
guard; its rationale + the `build` repro are documented at the seam.
