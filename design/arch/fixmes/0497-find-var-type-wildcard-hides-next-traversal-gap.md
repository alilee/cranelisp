---
number: 0497
target: /backend
filed_by: /review
filed_at: 2026-07-01
sprint_filed: 98
refers_to: crates/cranelisp-backend/src/compiler/rc_emission.rs (find_var_type_in_expr), crates/cranelisp-backend/src/heap.rs (collect_var_uses), crates/cranelisp-backend/src/compiler/control_flow/free_vars.rs (collect_free_vars), design/backend/ring2-rc.md §2.3
status: open
---

# `find_var_type_in_expr` keeps a `_ => None` wildcard — the exact trap that shipped the 0494 double-free; make it exhaustive

## Severity
Important (structural hardening at a heap-safety seam — not a live bug; the 0494 fix is correct)

## Issue
FIXME 0494 (fix `5ca6ef2`) was a heap double-free: `find_var_type_in_expr`
(`rc_emission.rs`, backing `derive_param_type_from_body`) did not descend into
`MonoExpr::LaunchContinue` / `MonoExpr::ConstrADT`, so a `conn` param used ONLY
inside a launched sub-tree was left un-typed in `variable_types`, its consuming
inc was skipped, and the poll state-closure drop glue dec'd an un-inc'd borrowed
`Connection` → SIGABRT.

The fix adds the two missing arms and is correct + complete: after it, every
MonoExpr variant carrying sub-expressions is traversed and `_ => None` now only
catches the four literal leaves.

**But the `_ => None` wildcard remains** — and that wildcard is the mechanism by
which the bug shipped silently. `find_var_type_in_expr` has two sibling recursive
MonoExpr traversals used for the same RC/lifetime decisions:

- `heap.rs::collect_var_uses` — **exhaustive** (explicit `IntLit|FloatLit|BoolLit|StringLit => {}`, no wildcard).
- `free_vars.rs::collect_free_vars` — **exhaustive** (same).

Both already handled `LaunchContinue` + `ConstrADT`. When those variants were
added, the two exhaustive siblings failed to compile and were updated; the third
sibling silently fell through `_ => None` and carried the un-typed-param
heap-safety bug to production. This is a P8 mirror where the wildcard defeated the
compiler's exhaustiveness check at the one site where it mattered most (RC
emission — a miss is a use-after-free, not a wrong answer).

## Proposed resolution
Replace `_ => None` in `find_var_type_in_expr` with the explicit four literal
arms (`IntLit | FloatLit | BoolLit | StringLit => None`), matching its two
exhaustive siblings. Then the next MonoExpr variant that carries a sub-expression
forces a compile error at this seam instead of a silent runtime double-free
(Principle 18 — enforce invariants structurally; Principle 7 — the three sibling
traversals should share the same exhaustive shape). Low effort, high value: the
bug that just cost a full sprint of localization cannot recur by omission.

Optionally note in a comment (or a shared doc) that all three MonoExpr
RC/lifetime traversals must stay exhaustive for this reason.

## Operational implication / Context
Discovered during the S98 /review consolidated pass on the RC/lifetime-critical
changes. The 0494 fix itself is sound (verified: no over-inc — the traversal
reports a single param type by first-match `.or_else`, does not count; the
consuming inc restores net-zero balance against the drop-glue dec). This FIXME is
purely about preventing the next instance of the same class. No behavioural
change, no test flip — just converting one wildcard to exhaustive arms.
