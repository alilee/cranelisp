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

## After stack placement retired (qa, 2026-11-18, `1a3ab46e`)

- **The cell still reads 2:** 14,872 allocations against 14,870 frees. The
  allocation count rose because no constructor is stack-placed; the residual
  did not move.
- **It is not ACT-1050's producer.** With the stdlib prelude, the `stdio`
  platform, `CRANELISP_NO_LENIENT=1` and the category census
  (`CRANELISP_CATEGORY_CENSUS`), cold and warm alike:

  | `main` | Allocations, frees | Census records |
  |---|---|---|
  | `(print "a")` | 2, 1 | none |
  | `(bind (print "a") (fn [u] (print "b")))` | 6, 4 | 2, absent arm |
  | the same with the continuation bound by `let` first | 6, 4 | none |
  | `(Pure 0)` | 1, 1 | none |

  The let-bound twin differs from the inline form only in whether the
  bind-chain rewrite fires, and retains the same 2. A single `print` retains
  1 with no `bind` at all.
- **Consequence.** ACT-1050's correction is predicted to leave this cell at
  2, so the planned re-measure after it (O-1018) will not close this record.
  No S124 change-set owns the stranded block. The reduction named above is
  still the next step and is unscheduled.
- **Refuted if** the cell reads 0 on the tree that corrects ACT-1050.

## After ACT-1050's correction (qa, 2026-11-18, `8667a868`)

O-1018, taken on the tree that corrects ACT-1050: the guard reads **2**
(14,872 allocations, 14,870 deallocations). The prediction above holds and
its refutation clause did not fire. The residual is not the bind-chain
rewrite's. This record carries on the number 2; the reduction is still
unscheduled, and the carry is the user's decision.

## After the exemplar's entry moved (qa, 2026-11-18, `2d3a5b3e`)

- **The guard no longer measures.** `exemplar/solver.cl` is a library since
  `efa4d8df` and has no `main`, so the cell's cold run is refused and the
  cell fails before it reads a balance. The workload moved unchanged to
  `exemplar/smoke.cl`.
- **The residual is still 2.** A warm `--run smoke.cl` on a scratch copy,
  with the cell's environment, reads 14,872 allocations against 14,870
  frees, twice. The former tree's `solver.cl`, run as an entry on the same
  compiler, reads the same two numbers, so the split changed nothing the
  cell measures.
- **`test` re-points the cell at `smoke.cl`** and keeps the assertion at
  exact balance. It then fails on the residual of 2, which is this record's
  defect; the number is not written into the assertion.

## The stdlib-free path reproduces it (qa, 2026-11-20)

`dev`(stdlib) reported, and `qa` confirmed on the debug binary built from
`39db1bb1`: the block is stranded with no stdlib on the path. **The
statement above that the stdlib-free path "allocates nothing the counters
see" is withdrawn,** and with it the conclusion that the block belongs to
the stdlib-prelude path.

`CRANELISP_LIB` at an empty directory, no prelude, `CRANELISP_NO_LENIENT=1`,
`CRANELISP_RC_STATS=1`, `--run`, cold and warm alike:

| `main` | Allocations, frees |
|---|---|
| `(print "a")`, `stdio` | 2, 1 |
| `(print "a")`, `test-capture` | 2, 1 |
| `(let [s "a"] (print s))` | 2, 1 |
| `(print (str-concat "a" "b"))` | 4, 3 |
| `(bind (Pure 0) (fn [u] (print "a")))` | 5, 4 |
| `(bind (print "a") (fn [u] (print "b")))` | 6, 4 |
| `(bind (Pure "abc") (fn [s] (print s)))` | **5, 5** |
| `(Pure 0)` | 1, 1 |
| `(commutative-noop)`, `test-capture` | 1, 1 |

- **Candidates.** The stdlib is not one. Both platforms strand the block,
  so it is not `stdio`'s `print` alone. What remains: the platform crate's
  consuming capture, which both use; the backend's transfer of a heap
  argument at a platform call; the runtime's disposal of the effect node.
- **One discriminating reading, not a mechanism.** The block is stranded
  when the argument is a value the caller owns outright (a literal, a
  `let`-bound literal, a concatenation). It is released when the argument
  is a continuation's parameter. `qa` did not read which release is absent
  in the first case or present in the second.
- **Not read.** The linked binary; a platform function other than `print`
  that takes a heap argument.
- **A reduction is now inside the suite's reach.** T-PRINT-BALANCE is
  allocated to `test` in the
  [S124 evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test).
  It discharges the first item of the completion evidence when committed.

## Evidence state (qa, 2026-11-20, `b72742f7`)

T-PRINT-BALANCE is committed (`dce11541`) and accepted: the literal and the
concatenation subjects fail on balance in `--run` and linked, 2 against 1
and 4 against 3, and the four controls balance. The linked binary strands
the block too. The first item of the completion evidence is discharged;
the module is still not attributed.
