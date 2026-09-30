---
id: ACT-1022
title: Lead — a non-recursive match arm whose if-branch pushes into a vector reads two unreleased allocations
status: open
priority: advisory
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - tests/plan/s122-evidence-delta.md
  - spec/12-runtime.md §12.3.1
---

## Observation

This is an unreduced lead from the ACT-1021 reduction, whose record is retained
in [the S122 evidence plan](../../tests/plan/s122-evidence-delta.md#retained-records-of-the-deleted-filings).
The source is the
`test` scratch log `repl16_5-checked4.log`, on source diff `66d4f7a4…`. It is
not committed evidence.

- **Probe P1.** It has no recursion. `(pick pair true [])` is defined as
  `(match pair [(Pair name _) (if keep (vec-push lines (run-one pair)) lines)])`,
  and its result goes straight into `vec-len`.
  - With `keep=true`, `CRANELISP_RC_STATS` read 8 allocations and 6
    deallocations. The exit was clean and no seam violation was reported.
- **Balanced siblings, same log:**
  - P1 with `keep=false`, 7/7;
  - P2, a String result, and P4, no match binder: balanced with `keep` either
    way;
  - L1 and L2, `vec-len` over a temporary or a bound vector, 5/5.
- **Class:** ordinary leak, residual +2. The mechanism is unknown. The
  siblings are not single-difference controls, so nothing is attributed.
  The balanced P4 suggests the match wrapper, but that is not established.

## Disposition

Under the approved K2 ordinary-leak rule, this gets no S122 fix. It is a lead,
not a committed RED, like ACT-1015. When it is resumed, `test` first commits a
`MarginalPair`: P1 with `keep=true` against the same program without the
`match` wrapper. QA then attributes it.

**Refuted if** that pair balances, or if the residual is the macro-turn
compile share (0889) rather than runtime retention.
