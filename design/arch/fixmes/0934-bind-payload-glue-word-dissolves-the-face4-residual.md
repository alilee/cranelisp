---
number: 0934
target: /qa
filed_by: /arch
filed_at: 2026-07-28
sprint_filed: 119
refers_to: design/backend/non-concrete-release-contract.md;
  design/intrinsics/ownership-and-disposal.md;
  design/backend/s122-closure.md;
  crates/cranelisp-intrinsics/src/drop.rs;
  tests/spec_10_io.rs;
  tests/concurrency_fanout.rs
status: deferred
retargeted_by: /arch
retargeted_at: 2026-09-25
---

## Disposition: carried to S123 under K7 (user, 2026-09-30)

- **Carried.** The cancellation face below carries to S123 in the K7 runtime
  concurrency package, approved with the Phase-5 checkpoint
  ([checkpoint carries](../../../tests/plan/s122-evidence-delta.md#phase-5-checkpoint-carries-approved-2026-09-30)).
  First deferral of this face; no earlier count is recorded for the filing,
  which has been open since S119.
- **S122 K2 (done).** The unrun-`Bind` face balanced and is retired; see
  below.

# `Pure` payload release: only the cancellation face lacks an executing witness

## Current state (verified 2026-09-30)

- **Mechanism delivered.**
  - Every `Pure` node carries a payload-glue witness, stamped at construction.
  - The intrinsics IO teardown releases a nested payload through it
    (`crates/cranelisp-intrinsics/src/drop.rs`, `IO_PURE_GLUE_OFFSET`).
  - Contracts: the release contract's
    [IO node section](../../backend/non-concrete-release-contract.md#5-the-io-node-and-its-release-face-4-delivered)
    and intrinsics [ownership and disposal](../../intrinsics/ownership-and-disposal.md).
- **Unrun-`Bind` face retired (qa, 2026-09-30).**
  `spec_10_io::unrun_bind_over_heap_payload_pure_discard_balances` passes.
  - It discards an unrun `(bind (Pure (str-concat …)) k)`.
  - Control 1/1, subject 7/7: a marginal of +6/+6 and a residual of 0, both
    exiting 0.
  - `CRANELISP_RC_DEC_CHECK` is armed.
  - Source `f0d1006f…`; log `.local/s122-final-test/k2-pairs.log`.

## Remaining obligation (`qa`)

The cancellation face has no executing balance observation. The 0907/0934 row of
`design/backend/s122-closure.md` routes it to `qa` and the runtime owners.

- **The face.** A `select` or `race` branch that loses while holding a `Pure`
  with a heap payload.
- **Why existing evidence does not cover it.**
  `concurrency_fanout::fresh_select_in_continuation_rc_balanced` balances a
  losing branch with a scalar payload only.
- **What the K2 cell does not establish.** It does not show that loser
  disposal shares the unrun-`Bind` teardown.

**First S123 act.** `test` runs one armed executing balance observation of a
losing branch that holds a heap-payload `Pure`. Its control is the same
program with a scalar payload.

## S124 observation: not a defect (qa, 2026-11-16, at `4b58ab93`)

- **The face balances.** With `CRANELISP_RC_TRACE=1` under `--run`, a
  `select` and a `race` whose losing branch is a `Pure` holding a
  `str-concat` result each read 13 allocations and 13 frees. Their scalar
  controls read 7/7 and 4/4. Four suspended-loser shapes over `poll-pool`
  balance as well (11/11 to 19/19).
- **Limit.** These were scratch probes without `CRANELISP_RC_DEC_CHECK`.
- **Allocation.** `test` commits the pair as fence F-0934 of the
  [S124 evidence delta](../../../tests/plan/s124-evidence-delta.md#43-fixme-0934--the-cancellation-face-balances),
  armed, in every mode. It is expected to pass on arrival.

## Closure

F-0934 is committed and passes; `qa` then deletes this filing.
