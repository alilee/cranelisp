---
number: 0446
target: /repl
filed_by: /sprint
filed_at: 2026-06-27
sprint_filed: 92
refers_to: repl/spec.md §0 (CLI invocation contract), user/cli-reference.md, design/backend/lenient-eval.md §3.6
status: open
---

# Give the execution env knobs (`CRANELISP_SPARK_BUDGET`, `CRANELISP_NO_LENIENT`) a normative home in the CLI contract

## Issue

Sprint 92 documented two execution environment variables in `user/cli-reference.md`
as an interim, as-built measure:

- `CRANELISP_SPARK_BUDGET=N` — caps concurrent parallel work (`0` ⇒ serial; unset
  ⇒ core-scaled default);
- `CRANELISP_NO_LENIENT=1` — disables auto-parallelism (serial baseline).

But the `user/` convention is to **cross-link a normative source, not originate a
contract**, and these knobs currently have **no normative listing**: `repl/spec.md`
§0 lists the agent/`NO_COLOR` env vars but not these; `CRANELISP_SPARK_BUDGET`
exists only in `design/backend/lenient-eval.md §3.6` + the S92 sprint record.
`user/cli-reference.md` now documents them with an explicit "normative home being
settled — FIXME tracks it" note (a deliberate landing spot left for this FIXME).

## Proposed resolution

`/repl` adds a one-row-per-knob entry to the `repl/spec.md §0` CLI-invocation-contract
env-var table (the same surface that already lists the agent/`NO_COLOR` vars), so
`user/cli-reference.md` can cross-link it and drop the interim "as-built" caveat. If
`/repl` judges these belong in the language spec instead (they govern §12.4.3
evaluation), re-target to `/spec` — but a single normative home is the goal.

## Operational implication / Context

- **No defect, no failing test** — a documentation-ownership/normative-home gap; a
  design FIXME is the right record.
- Low priority: the knobs are documented as-built in `user/cli-reference.md` in the
  interim; this just settles where the contract lives so the user doc cross-links
  rather than originates.
- Note: `CRANELISP_NO_LENIENT` predates S92 (Sprint 25) and was never given a
  normative home either — this FIXME closes both.
