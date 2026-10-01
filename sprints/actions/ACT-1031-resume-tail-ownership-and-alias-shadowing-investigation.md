---
id: ACT-1031
title: Resume the deferred tail-argument ownership and alias-shadowing investigation
status: deferred
priority: required
from: sprint
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - sprints/actions/ACT-1029-alias-map-same-name-overwrite-lead.md
  - sprints/actions/ACT-1030-let-wrapped-tail-forward-uaf-intake.md
  - tests/vec_push_match_binder_same_name_shadow.rs
  - tests/plan/s122-evidence-delta.md
  - design/backend/ownership-codegen.md §13.3
---

## User decision

On 2026-09-30 the user directs that this investigation be recorded for future
work and that current work move to another task. The user then approved the
carry to S123 with the Phase-5 checkpoint, together with the remaining
ownership-codegen leads L2–L7, L9 and L10
(`design/backend/ownership-codegen.md` §13.3;
[checkpoint carries](../../tests/plan/s122-evidence-delta.md#phase-5-checkpoint-carries-approved-2026-09-30)).
First deferral. This does not resolve the observed memory-safety fault or
accept the compiler as production-ready.

## Re-entry

- QA first reopens the canonical observations and attribution in
  [ACT-1030](ACT-1030-let-wrapped-tail-forward-uaf-intake.md), and the
  still-unconfirmed alias-map lead in
  [ACT-1029](ACT-1029-alias-map-same-name-overwrite-lead.md).
- The first probe's renamed-binder control aborts under the memory checker;
  its subject has not run. Preserve the failing, unignored regression cell.
- Resume QA's existing two-cell delta: discriminate the let-wrapped tail
  argument fault, then isolate same-name alias shadowing. Observe halves
  separately so an abort cannot hide the other half. Do not repeat the
  invalid first pair as proof of the alias-map mechanism.
- Then probe the remaining leads L2–L7, L9 and L10 against the predictions
  §13.3 states for them. L2 and L6 are already implicated in ACT-1030's hypothesis.
  Each confirmed lead becomes its own intake; each refuted one is recorded
  in §13.3 by its owner, `design`(backend).
- Dispatch under the model direction the user gave on 2026-09-30, recorded in
  the active sprint plan's Phase-5 checkpoint section.
- State the authorized purpose plainly: local synthetic regression tests
  of our own compiler, checking value semantics and ownership. Preserve
  host safeguards and permissions; report false refusals accurately.
- A confirmed mechanism routes to backend design and development. Public
  API or normative contract changes retain their existing user gates.

## Completion

Both canonical items have measured dispositions: the observed fault is fixed
and its guard passes with a valid control, and the alias-shadowing lead is
confirmed and corrected or refuted. Each remaining lead is refuted, or
confirmed and filed as its own intake. Retire this coordination action with those
outcomes; preserve any unresolved obligation in its canonical filing.
