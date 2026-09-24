---
number: 0914
target: /qa
filed_by: /repl
filed_at: 2026-07-26
sprint_filed: 118
refers_to: src/repl/commands.rs::handle_mem;
  design/int/result-owner.md §4.2.1;
  repl/spec/03-slash-commands.md;
  tests/repl_introspection.rs::mem_with_expr_emits_signed_delta_line;
  tests/plan/s122-evidence-delta.md
status: open
---

# `/mem <expr>` delta window must include the result release — closure tails

## Current state (verified 2026-09-24)

- `design/int/result-owner.md` §4.2.1 rules shape (a): the command observes
  the result, drives `release_program_result()` through the one chokepoint,
  then closes the counter window. `/time` deliberately keeps its eval-only
  window.
- `src/repl/commands.rs::handle_mem` now formats the result, releases it and
  only then samples the closing counters (S122 working tree).
- `mem_with_expr_emits_signed_delta_line` was strengthened with a warmed
  scalar control and a separately checked heap result. It failed as intended
  before the change (heap `live +1`) and passes after it (S122 evidence
  delta, Q6).

## Remaining obligation

1. `qa` accepts or rejects the Q6 evidence at the S122 gate, including
   whether the required unit pin at the sampling-order seam exists.
2. `spec` removes the interim clause in `repl/spec/03-slash-commands.md` that
   treats the delta form's exclusion as a known non-conformance.
3. `test` updates the closing section of `repl/demos/memory-lifecycle.demo`,
   which still says the delta window closes before the result is released.

## Closure

All three are done.
