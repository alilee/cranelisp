---
number: 0764
target: /review
filed_by: /sprint
filed_at: 2026-07-21
sprint_filed: 115
refers_to: sprints/METHOD.md §2.2 "Repro before fix (binding, added S115)" +
  .claude/commands/review.md (verdict criteria / findings-severity section)
status: open
---

# Add "repro before fix" to /review's verdict criteria as a Blocker-class check

## Issue

METHOD §2.2 now binds: no defect is fixed before its minimal reproduction is
committed, including defects the fixing skill discovers itself mid-wave. The
rule states that **enforcement lives at `/review`** — because a rule that is
only an aspiration in the fixing skill's own head is the one that lapses under
wave pressure (S115 evidence: W3b's `/dev` found three further live leaks while
isolating FIXME 0749, fixed all of them correctly, and left the e2e tier owed
to a FIXME; separately FIXME 0760's two *measured* leaks — exact
allocs/deallocs at 100 iterations — lived as FIXME prose with no failing test
until an audit caught it).

`/review` already treats an unguarded narrowing as a Blocker (Principle 25).
This is the same shape one level up: an unguarded *fix*.

## Proposed resolution

In `.claude/commands/review.md`, add to the verdict criteria:

- **Blocker** — a fix in the change-set whose defect has no committed minimal
  reproduction in the *same* change-set. The repro must be minimal (a
  sprawling repro does not establish the category), committed (not FIXME
  prose, not a measurement quoted in a commit message), and at the tier the
  fixing skill owns, with any missing tier requested in-wave rather than
  deferred.
- Corollary check: when a change-set fixes MORE defects than it was dispatched
  for (the common and valuable case), each additional defect needs its own
  repro. "It rode along with the main fix" is the exact path by which a
  category ships unguarded.
- Not a Blocker: a defect whose reduction was genuinely attempted and failed
  (intermittent / environment-dependent), where the attempt and its evidence
  are recorded. Judge the recorded evidence, not the absence of a test.

Keep the wording short and place it beside the existing narrowing check so the
two read as the same discipline at two altitudes.
