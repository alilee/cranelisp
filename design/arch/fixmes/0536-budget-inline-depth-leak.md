---
number: 0536
target: /design
filed_by: /qa
filed_at: 2026-07-07
sprint_filed: 104
refers_to: crates/cranelisp-intrinsics/src/ivar.rs (create-gate), design/backend/lenient-eval.md §3.6, tests/plan/s104-utilization-measurement.md §8.7
status: open
---

# Budget-inline depth leak — the create-gate inline arm advances no SPARK_DEPTH

## Issue

The create-gate (`lenient-eval.md` §3.6.2; `crates/cranelisp-intrinsics/src/ivar.rs`)
has two arms: the **budget-granted** arm allocates IVars/thunks and sparks, and
the **over-budget inline** arm falls back to sequential arg codegen. The depth cap
`CRANELISP_SPARK_MAX_DEPTH` decides sparking by comparing the current `SPARK_DEPTH`
against the cap.

**The inline arm advances no `SPARK_DEPTH`.** When a child is *budget-inlined*
(over-budget → run inline), it executes at the **same depth** as its parent, so its
own sparkable sub-args re-test the depth cap against an unincremented depth and
**re-spark at the same level**. The effect: a budget-inlined child re-sparks, and
the intended depth ceiling is not enforced past the point where inlining kicks in.

**Consequence — D cannot exceed ~log2(cap) without a backend hook on the inline
arm.** At D=3 the fixtures are safely under the leak (F5 collapses 619K → ~14
spawns, §8.7). But raising the cap re-exposes it: **F5 re-explodes to ~1.3M spawns
at D=4** — the inline arm's un-advanced depth lets the fib-explosion re-populate.
D=3 is safely under; the leak becomes load-bearing only when the depth budget wants
to scale (exactly what FIXME 0535's density-aware-depth deep arm asks for).

## Proposed resolution

**Advance `SPARK_DEPTH` on the create-gate inline arm.** A budget-inlined child is
one more level of nesting; its `SPARK_DEPTH` must increment just as a sparked child's
would, so its sub-args test the cap against the correct (deeper) depth and stop
re-sparking at the ceiling. The hook is on the inline arm of the create-gate in
`ivar.rs` (and any parallel inline fallback in the backend emit) — a backend/intrinsics
change, not a design-only note.

## Operational implication / Context

- This is a **backend follow-on** to the S104 depth-cap work. It is dormant at the
  shipped D=3 default (no fixture crosses the leak there), so it is **not an S104
  defect** — but it **caps the depth-aware work**: FIXME 0535's density-aware depth
  wants alloc-free strands to go *deeper* than D=3, and this leak is the reason D
  cannot scale past ~log2(cap) until the inline arm advances depth. Land this hook
  and the depth budget becomes free to scale.
- Owner: `/design`(cranelisp-backend) rules the §3.6 depth-accounting contract;
  `/dev(cranelisp-backend)` implements the `ivar.rs` inline-arm hook. Retarget to
  `/dev` directly if `/design` judges the §3.6 contract already covers it and only
  the code hook is missing.
- Repro signal for `/qa` when this is actioned: the F5 spawn count as a function of
  `CRANELISP_SPARK_MAX_DEPTH` — ~14 at D=3, ~1.3M at D=4 today; after the fix the
  D=4 spawn count must stay O(cores × depth), not re-explode. (Perf-lane, not a
  nextest guard — the §8 F5 lane.)
