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
status: open
retargeted_by: /arch
retargeted_at: 2026-09-25
---

## S122 disposition (user-approved 2026-09-30)

Under the [approved S122 disposition](../../../tests/plan/s122-evidence-delta.md#final-disposition-proposal-2026-09-30):

- **S122 work (K2), evidence only.** `test` measures one marginal pair for a heap payload in an unrun `Bind`. A balanced pair retires this filing. A confirmed ordinary leak becomes a committed RED carried to S123 under K7. A double discharge, use-after-free or corruption returns to the user with its attribution for a fix decision.

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

The approved K2 package named only the unrun-`Bind` face, so this face has no
approved package. `sprint` presents it to the user as a carry candidate (K7,
runtime concurrency) or as S122 work.

## Closure

An executing balance observation of a losing heap-payload branch passes, or
`qa` records the evidence that already discriminates it.
