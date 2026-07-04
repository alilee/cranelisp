---
number: 0511
target: /design
filed_by: /dev
filed_at: 2026-07-04
sprint_filed: 102
refers_to: design/typecheck/ownership-inference.md §6, §13.2 CS-3, §3.4
status: open
---

# pass5 §6 session memo needs a session-owned threaded field — the checker env is per-call/borrow-only

## Issue

§13.2 CS-3 specifies "the §6 session memo (`DashMap` on the checker env, keyed
`(template home, mangled name)`)", and §6 motivates it for repeated mints + the
R3 incremental path (§3.4 leverage point 4). But `TypeCheckEnv`
(`crates/cranelisp-typecheck/src/checker.rs`) is **constructed fresh per
`check_forms` invocation** and borrows *all* its state (`modules`, `next_id`,
`module_aliases`, `prelude_fallback` are each `&'a`). A memo field that outlives
one compile therefore cannot be an owned field on the env (it would reset every
call); it must be a **session-owned `&'a DashMap` threaded from `int`** through
`TypeCheckEnv::new` / `new_with_staging` (the same shape as `prelude_fallback`)
— a cross-crate signature change `int` must make, out of scope for a
typecheck-narrow `/dev` visit.

## Proposed resolution

`/design` (typecheck) decides whether the cross-invocation session memo is worth
the plumbing, given §6's own note that **determinism makes its absence a
re-compute cost, never a wrong result**. Options:

1. **Thread a session-owned memo field** — `int` owns a
   `DashMap<(FQSymbol, JitSymbol), ModeSummary>`, passes `&'a` into the env
   constructors; pass5 reads/writes it. Enables the R3 incremental fast path
   (§3.4-4). Requires an `int`-side change (cite the constructor signature).
2. **Keep the in-pass memo only** (the S102 CS-3 landing) — each compile
   converges each callable once; repeated mints within one compile are map hits.
   Cross-invocation re-inference re-computes deterministically (equal result).
   Sufficient for increment I; the R3 machinery is not yet consuming summaries
   (Wave 9+), so the incremental fast path has no live consumer to accelerate.

## Operational implication / Context

S102 CS-3 shipped option 2 (in-pass memo). It is sound and behaviour-neutral;
the only cost is re-computing unchanged instantiations across separate REPL
turns — invisible until the R3 summary-diff gate consumes summaries (Wave 9+).
Recommend deferring option 1 until an R3 turn-latency measurement (the §3.4
interactive budget lane, `/qa` part-17) shows the re-inference cost is material.
No `cranelisp-types` edit either way — the memo is typecheck-internal state.
