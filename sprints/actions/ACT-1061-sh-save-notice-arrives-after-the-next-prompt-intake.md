---
id: ACT-1061
title: Under load, the reload notice for a save made by a `/sh` turn appears after the next prompt
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-16
refers_to:
  - repl/spec/14-file-watching.md
  - src/watch.rs
  - src/main.rs
  - tests/user_samples.rs
  - tests/scripts/user_samples.py
  - user/guide/live-development.md
  - tests/plan/s124-evidence-delta.md
---

## Observation

- **Suite.** `user_samples::sample_checker_detects_wrong_output_and_unclassified_fences_then_clears`
  failed once in the S124 opening run and passed alone. In `qa`'s full run at
  `4b58ab93` on 2026-11-16 it failed again, and so did
  `user_samples::user_documentation_samples_match_the_compiler`. Both failed
  on the same line shape: after `/sh printf … > math.cl` the expected
  `[updated: math.cl]` and `[updated: user.cl]` were absent from that turn's
  output.
- **Reproduced outside the suite.** The fixture group's transcript, piped to
  `target/debug/cranelisp` in a scratch directory under twenty busy
  processes on fourteen CPUs, gave the suite's symptom in 1 of 12 runs. The
  `/sh` turn printed nothing; both notices appeared after the next prompt
  and before the next result, which was the new value, 29. Twenty unloaded
  runs showed the notices at the `/sh` turn every time.
- **Nothing is lost.** The next evaluation observed the rebuilt definition
  in every run.

## Attribution: provisional

- **Mechanism.** `FileWatcher::poll_changes` in `src/watch.rs` reads the
  operating system's change notifications without blocking. The poll after a
  turn can run before the notification for that turn's own `/sh` write has
  been delivered; the poll before the next turn then reports it, after the
  prompt is written.
- **Seam observation.** The late transcript places the notices between the
  next prompt and its result, which is where the pre-turn poll writes.
- **Control.** A sibling whose `/sh` command sleeps 0.5 s after the write,
  inside the same turn, showed the notices at the `/sh` turn in 12 of 12
  loaded runs. At this rate (1 in 12) the contrast is weak; the attribution
  stays provisional.
- **Refuted if** a run shows the notice late although the notification was
  already queued when the post-turn poll ran, or the sibling with the settle
  time shows it late.
- **Class:** a required report taken from a notification whose delivery
  the reporter does not control: `notification-only-detection`.

## Classification: a product defect (user ruling S124-Q6, 2026-11-17)

[§14.2](../../repl/spec/14-file-watching.md#142-eager-recompilation) now
requires a watched save completed by a turn's own `/sh` to be rebuilt and
reported before that turn's next prompt, regardless of notification
delivery. The late placement is therefore a defect in `src/`, in S124 scope.

- **Deterministic face, found 2026-11-17.** A watched module that is a hard
  link, rewritten by `/sh` through its other name in an unwatched directory,
  delivers no notification at all. The save was never reported and `(f)`
  kept its old value in 3 of 3 runs, including after a later settled turn.
  The control, the same write through the watched name, reported at the
  `/sh` turn. This is the reproduction; it withholds the notification
  without depending on load.
- **Correction, designed:**
  [REPL lifecycle §1.2](../../design/int/repl-lifecycle.md#12-poll-and-reload),
  "A `/sh` turn's own save is compared, not awaited".
- **Evidence:** conditions T-1061 and M-1061 in the
  [evidence delta §3.6](../../tests/plan/s124-evidence-delta.md#36-repro-1061--a-sh-save-reported-without-its-notification).

## Evidence authority

`user_samples` is the M-3 maintenance check. Its failure blocks the claim
that the user guides match the compiler; it does not gate compiler
acceptance. Until this is settled, a suite count names both `user_samples`
tests as run-dependent, outside the stable failing set
([PLAN, traceability](../../tests/plan/PLAN.md#traceability-and-authoring)).

## Completion evidence

T-1061 fails before the correction and passes after it, with M-1061's armed
and unarmed legs; both `user_samples` tests pass; and 40 loaded runs of the
fixture transcript on the corrected build show the notices at the `/sh` turn
in every run, against the 1-in-12 late rate recorded above.
