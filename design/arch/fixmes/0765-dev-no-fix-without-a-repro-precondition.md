---
number: 0765
target: /dev
filed_by: /sprint
filed_at: 2026-07-21
sprint_filed: 115
refers_to: sprints/METHOD.md §2.2 "Repro before fix (binding, added S115)" +
  .claude/commands/dev.md
status: open
---

# /dev precondition: no fix without a repro (state the rule forward, at the point of temptation)

## Issue

METHOD §2.2 now binds "repro before fix", with `/review` as the enforcement
gate (FIXME 0764). The gate catches the lapse; the precondition prevents it.
`/dev` is where the temptation actually occurs — mid-wave, mechanism in hand,
with the fix obvious and the reduction feeling like a detour.

S115 W3b is the worked example in both directions: the `/dev` agent's
diagnosis was exemplary (it refused to patch two candidate mechanisms blind and
proved which were live), and it still left one tier owed to a FIXME and two
measured leaks as prose — because nothing in its own brief said *the
reproduction is the deliverable, and it comes first*.

## Proposed resolution

In `.claude/commands/dev.md`, add a short precondition near the test-discipline
text:

- **No fix without a repro.** Before writing a fix — including for a defect you
  discover yourself, mid-wave, that nobody dispatched you for — reduce it and
  commit the reduction as a failing test at the tier you own (unit, always).
  Reduce *first*: the fix frequently becomes obvious during isolation, and the
  reduced form is what exposes the category rather than the instance.
- **A tier you do not own is requested in-wave, not deferred.** Ask `/sprint`
  for `/testing` (e2e) or `/qa` (attribution, matrix placement) inside the same
  wave. Filing a FIXME "for next sprint" is not available for a defect you have
  already measured — that is the "test owed" anti-pattern (METHOD §2.2).
- **Report every additional defect you found.** A change-set that fixes more
  than it was sent for is a good outcome; each extra fix carries its own repro,
  and `/review` treats a missing one as a Blocker (FIXME 0764).

Pair it with the existing instrumentation-question requirement — the two are
answered at the same moment, from the same freshly-held mechanism.
