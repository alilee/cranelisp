---
id: ACT-1025
title: A worker module test's requeue was refused once in a full run and passed in isolation
status: resolved
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - src/worker/tests.rs::dispatch_without_a_stored_continuation_retires_nothing
  - src/scheduler.rs::requeue_for_typecheck
  - src/session_v4/lifecycle.rs::register_module_with_source
---

## Observation

- **One failure.** In `dev`(backend)'s full `cargo nextest run --no-fail-fast`
  on 2026-09-30, `worker::tests::dispatch_without_a_stored_continuation_retires_nothing`
  failed at `src/worker/tests.rs:4413`: `requeue_without_continuation(&user)`
  returned `false` (`.local/s122-tail-cow-dev/full-suite.log`).
- **Passes otherwise.** It passed in isolation on the pre-change tree and on
  the final tree (97/97 worker tests).
- **Not this change's surface.** The test exists at HEAD `e4062202`, and the
  backend amendment does not touch its path.

## Attribution: provisional

- **Not test ordering.** Nextest runs each test in its own process, so the
  variance lies inside this test's process: thread interleaving under
  whole-suite load.
- **Where `false` can come from.** `requeue_for_typecheck` returns `false`
  for an unknown module, or for one in `TypecheckWorking` or
  `TypecheckBlocked`.
- **What the fixture assumes.** `removal_session` returns after
  `register_module`, which waits in `wait_inmem_complete_blocking`. The test
  then assumes that `user`'s pool is terminal.
- **Hypothesis.** The waiter can wake before the pool reaches its terminal
  transition, or a background claim can re-enter `TypecheckWorking`.
  - The `h` slot precondition passes either way, because the definitions are
    installed before `notify_typecheck_done`.
- **Refuted if** the pool is terminal when the requeue is refused.
- **Class.** Not assigned until the pool is observed.

## Recommendation (bounded)

No repeated stress, and no source fix under this intake.

1. **`dev`(src), source read.** Establish the order of
   `notify_inmem_codegen_complete` and `notify_typecheck_done`, and whether
   `wait_inmem_complete_blocking` guarantees a terminal pool on return.
2. **`dev`(src), module test.** Make the test self-attributing: assert
   `user`'s pool before the requeue, with the pool named in the message. The
   next occurrence then distinguishes a fixture assumption from a scheduler
   ordering defect.
3. **QA** classifies from the first read or the next occurrence:
   - a fixture assumption is corrected by `dev` in the test;
   - a product ordering defect gets a narrow reproduction under the
     control discipline.

## Completion

The failure is attributed, and either corrected with its evidence or carried
with the user's approval.

## Disposition: carried to S123 in K10 (user, 2026-09-30)

Approved with the Phase-5 checkpoint, beside 0694's run-dependent members,
as bounded attribution that preserves the observation and falsifier above
([checkpoint carries](../../tests/plan/s122-evidence-delta.md#phase-5-checkpoint-carries-approved-2026-09-30)).
First deferral. It did not recur in K4's full run or the checkpoint suite.
Recommendation steps 1 and 2 are the first S123 acts.

## Resolution (qa, 2026-11-15, S123 W0)

- **Classified: a fixture assumption, not a product ordering defect.**
  At W0, `src/worker.rs::notify_processed_ready` published in-memory
  completion before `notify_typecheck_done`, so `wait_inmem_complete_blocking`
  could return while `user` was `TypecheckWorking`, and `requeue_for_typecheck`
  then refused. The fixture assumed a terminal pool.
- **Control.** At W0 a scheduler unit test reached the unsettled pool
  deterministically and `dev` observed it failing first with this action's
  symptom. W1's fused source-pass transition
  ([int §6.1.2](../../design/int/int.md#612-the-entry-is-settled-before-the-eval-thread-owns-it))
  made that state unconstructable and deleted the test; the current pins are
  `src/scheduler/tests.rs::source_pass_ready_leaves_a_terminal_pool_so_a_requeue_is_accepted`
  and `src/scheduler/tests.rs::symbol_completion_never_completes_a_working_module`.
  Refuted if a requeue is refused with the pool terminal.
- **Correction.** `dispatch_without_a_stored_continuation_retires_nothing`
  in `src/worker/tests.rs` asserts the terminal pool, naming it, before the
  requeue; the fixture's extra settle wait was removed once the fused
  transition landed.
- **Product reach.** The startup hand-off residual that `dev` reported is
  closed by the same fused transition.
- Delete this action once
  [FIXME 0694](../../design/arch/fixmes/0694-qa-suite-count-nonreproducible-two-interleaving-dependent-guards.md),
  `design/int/int.md` and `tests/plan/s122-evidence-delta.md` no longer link
  it. Verified 2026-11-15 (S123 W1): FIXME 0694 still links it.
