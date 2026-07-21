---
number: 0741
target: /qa
filed_by: /review
filed_at: 2026-07-21
sprint_filed: 115
refers_to: tests/regression.rs::shared_state_field_count_at_target_14 — the
  SharedState pub-field-count boundary guard bumped 16→17 (S115 W2, FIXME 0604
  declared_exports field).
status: open
---

# SharedState field-count guard: ratify the 16→17 bump + the stale function name

## Severity
Suggestion

## Issue

`tests/regression.rs`'s SharedState pub-field-count guard was bumped 16→17 in
change-set `d9f2caea` to admit the new `declared_exports` field (FIXME 0604
§2.2). The bump is mechanical and designed-to-admit — the field is int-internal,
unserialized, no types/schema/public-api impact, and the assert message
documents the addition alongside the two prior sanctioned additions
(`prelude_fallback`, `run_mode`). SPRINT.md §Notes (W2 entry) flags "/qa ratify"
for this boundary edit. This is the ratification request.

Separately: the guard function is still named
`shared_state_field_count_at_target_14` — a name stale since the 14→16 bump two
sprints of edits ago and now doubly stale at 17. The name no longer names the
target it guards.

## Proposed resolution

- `/qa` ratifies the 16→17 bump as a sanctioned field addition (mechanical, no
  parking-map creep — the guard's actual purpose, guarding that
  `module_sexps`/`suspend_states` do not return, is unaffected).
- Rename the function to drop the frozen numeral (e.g.
  `shared_state_pub_field_count_guard`) or track it to the live target, so it
  does not accrete a third stale numeral at the next legitimate addition.

## Context

`/review`(src) S115 W2. Boundary-edit ratification per the arch baseline-diff
discipline; the rename is cosmetic cleanup of a name the guard outgrew.
