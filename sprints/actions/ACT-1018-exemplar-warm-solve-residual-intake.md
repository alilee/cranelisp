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
under K7. This is the first deferral. Because the RED came from K3 rather than
a K2 pair, the user confirmed this use of the rule separately, with the
Phase-5 checkpoint on 2026-09-30
([checkpoint carries](../../tests/plan/s122-evidence-delta.md#phase-5-checkpoint-carries-approved-2026-09-30)).
It carries beside the ordinary-leak lead
[ACT-1022](ACT-1022-match-arm-branch-push-residual-lead.md); no link between
the two is established.

## Completion evidence

- A reduced reproduction, measured as a marginal pair or as a warm cell with an
  executed premise, isolates at least one stranded type and its site.
- The owning repair turns the exemplar cell GREEN at exact balance.
- The same exemplar measurement is rerun on the control and corrected builds,
  and the remaining residual is stated as a number (0 at closure).
- An allocator-armed run shows no safety face, or any face found is routed as
  memory-unsafe.

## U′ re-measure (qa, 2026-11-16, S123 W2)

The residual falls from 51 to **2** on the U′ build. The 2 is one block per
`print` call in `main`.

- **Measurement.** Warm serial `solver.cl`, fresh scratch copy, the
  committed cell's sequence. The control compiler `ee8959c0…` reads 51 with
  moves on and 556 with moves off. The U′ compiler `77bb2dd9…` reads 2 in
  both polarities ([evidence delta §3.10](../../tests/plan/s123-evidence-delta.md#310-u-cost-and-residue-readings-and-the-w2-suite)).
  The committed cell is still RED, now at 2.
- **The solve itself retains nothing.** A driver that solves the same puzzle
  1, 8 or 64 times and prints nothing balances exactly on both compilers.
- **One block per `print`.** In the same warm project, a `main` of
  `(print "a")` retains 1 and two `print` calls joined by `bind` retain 2.
  `(Pure 0)` retains 0. The counts are the same on both compilers and in
  both polarities, so this part predates U′. Under `CRANELISP_RC_TRACE`, the
  first block allocated (the printed `String`) is never released, while the
  effect node is freed.
- **Not established.** Which release is missing. The stdlib-free path,
  `(platform stdio)` with no prelude, allocates nothing the counters see, so
  the stranded block belongs to the stdlib-prelude path to `print`. That path
  is outside the suite's stdlib-free reach. The next step is a reduction
  under the stdlib conformance exception or by `dev`(stdlib), followed by a
  control that differs only in that path.
- **Still owed for closure.** The completion evidence above, unchanged.
