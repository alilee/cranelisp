---
id: ACT-1018
title: Attribute the 51 allocations a warm serial Sudoku solve retains
status: deferred
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - tests/exemplar_ownership_residue_s116.rs
  - tests/plan/PLAN.md
  - spec/12-runtime.md §12.3.1
---

## Request

A warm serial Sudoku solve retains 51 allocations it should release. Attribute
them to the programs and types that strand them. Then retain a reduced,
spec-traced failing reproduction and route the repair to its owner.

## Observation

- **Cell.** `exemplar_ownership_residue_s116::sudoku_warm_serial_solve_retains_nothing`
  asserts exact warm balance, as `tests/plan/PLAN.md` allocates. It is RED.
  - The warm solve reads 26457 allocations against 26406 deallocations, a
    residual of **51**.
  - The same count appeared in two runs.
  - Source `f0d1006f…`; log `.local/s122-final-test/exemplar-exact.log`.
- **The premise holds.** `warm_cache_hit_control_carries_no_ambient_residual`
  passes in the same binary, so the warm ambient term is 0. The 51 is runtime
  retention by the solve, not the macro-turn compile residual (0889).
- **Classification.** An ordinary leak: both children exit cleanly, and there
  is no seam violation.
- **Not established.** The bounded run checked no allocator-armed mode.
- **History.** The earlier cell's `<= 1_400` threshold hid this number. It is
  new intake, never a threshold.

## Disposition

S122 applies the approved K2/K7 ordinary-leak rule
([final disposition](../../tests/plan/s122-evidence-delta.md#final-disposition-proposal-2026-09-30)).
The RED stays committed and un-ignored as the record, and it is carried to S123
under K7. This is the first deferral. `sprint` confirms the application with the
user at the Phase-5 checkpoint, because the RED came from K3 rather than a K2
pair.

## Completion evidence

- A reduced reproduction, measured as a marginal pair or as a warm cell with an
  executed premise, isolates at least one stranded type and its site.
- The owning repair turns the exemplar cell GREEN at exact balance.
- The same exemplar measurement is rerun on the control and corrected builds,
  and the remaining residual is stated as a number (0 at closure).
- An allocator-armed run shows no safety face, or any face found is routed as
  memory-unsafe.
