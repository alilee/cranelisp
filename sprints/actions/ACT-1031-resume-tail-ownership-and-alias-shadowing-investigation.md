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
---

## User decision

On 2026-09-30 the user directs that this investigation be recorded for future
work and that current work move to another task. First deferral of this
resumption action, proposed for S123. This does not resolve the observed
memory-safety fault or accept the compiler as production-ready.

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
- The user requests a lower model for future work. Choose and record the
  exact model before dispatch; no model switch has yet been executed.
- State the authorized purpose plainly: local synthetic regression tests
  of our own compiler, checking value semantics and ownership. Preserve
  host safeguards and permissions; report false refusals accurately.
- A confirmed mechanism routes to backend design and development. Public
  API or normative contract changes retain their existing user gates.

## Completion

Both canonical items have measured dispositions: the observed fault is fixed
and its guard passes with a valid control, and the alias-shadowing lead is
confirmed and corrected or refuted. Retire this coordination action with those
outcomes; preserve any unresolved obligation in its canonical filing.
