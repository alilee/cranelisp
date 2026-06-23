---
number: 0433
target: /spec
filed_by: /docs
filed_at: 2026-06-23
sprint_filed: 90
refers_to: spec/04-* §4.8.4, spec/06-pattern-matching.md §6.2
status: open
---

# Literal patterns: §4.8.4 example contradicts §6.2 grammar

## Issue
While authoring the `/syntax` cheat-sheet (S90 Pillar 1), `/docs` found that
literal patterns are **rejected by the binary** but **shown in the spec**:

- `(match 0 [0 "zero" _ "other"])` → `invalid pattern` (same for String/Bool literals).
- `spec` §4.8.4 shows a literal-`0` match example as valid.
- `spec/06-pattern-matching.md §6.2`'s pattern grammar lists only **constructor /
  wildcard / variable** patterns — no literal patterns. The binary follows §6.2.

So §4.8.4 and §6.2 contradict each other. Discovered during verified-compiling
authoring (every cheat-sheet example must compile on the live REPL); the `patterns`
topic was authored to §6.2's grammar and `case` documented as the value-dispatch tool,
so the asset is correct regardless of the resolution.

## Proposed resolution
`/spec` arbitrates which is normative:
- If literal patterns are **not** a language feature → fix §4.8.4 (remove/rewrite the
  literal-`0` example to a `case` or guard form), and the contradiction closes
  documentation-only (no compiler work).
- If literal patterns **should** be supported → this is a compiler gap (a defect), and
  `/qa` owes a failing-not-ignored repro + the owning compiler skill implements §6.2
  literal-pattern support. (Per CLAUDE.md, a defect needs the failing test, not just this
  FIXME.)

## Operational implication / Context
Low urgency — not on the S90 critical path (the cheat-sheet sidesteps it). But it is a
spec-internal contradiction that will mislead any reader (human or the embedded agent
pulling `/syntax patterns`) until reconciled. Surfaced S90 Wave 1; transcribed by
`/sprint` on `/docs`'s behalf.
