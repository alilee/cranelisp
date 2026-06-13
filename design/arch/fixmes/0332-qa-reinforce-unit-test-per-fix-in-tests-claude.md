---
number: 0332
target: /qa
filed_by: /sprint
filed_at: 2026-06-13
sprint_filed: 81
refers_to: tests/CLAUDE.md, CLAUDE.md §Testing, sprints/METHOD.md §Phase 5, memory/feedback_unit_test_per_fix.md
status: open
---

# Reinforce the unit-test-per-fix policy in tests/CLAUDE.md (point-of-use)

## Issue

A new project policy was established Sprint 81 (user-directed) and landed in root
`CLAUDE.md` §Testing + `sprints/METHOD.md` §Phase 5: **every fix lands with a unit
test (mandatory); the need for an integration/e2e test is assessed BEFORE the fix is
written; failing test(s) first, fix + test in the same change-set; no "test owed"
follow-up FIXMEs.**

`tests/CLAUDE.md` is `/qa`-owned and is the doc read at the point of authoring tests.
The policy should be reinforced there (the two-tier unit/e2e strategy already lives
there) so test-authoring sessions see it at the point of use, not only via the root
`CLAUDE.md` chain.

## Proposed resolution

`/qa` adds a short subsection to `tests/CLAUDE.md` stating the unit-test-per-fix +
assess-e2e-before-fix discipline, cross-referencing root `CLAUDE.md` §Testing and the
two-tier strategy, and the failing-first / same-change-set rule. Optionally note the
unit-vs-e2e decision heuristic (e2e when observable end-to-end or crossing
`--run`/`--link`/REPL).

## Operational implication / Context

NOT blocking. Root `CLAUDE.md` already binds all agents (the strongest surface); this
is point-of-use reinforcement in the test-authoring doc. Skill-def reinforcement
(`.claude/commands/qa.md` / `dev.md`) is optional — root `CLAUDE.md` covers it.
