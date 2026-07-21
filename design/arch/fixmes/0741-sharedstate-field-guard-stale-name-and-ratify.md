---
number: 0741
target: /testing — /qa ratified the bump 2026-07-21; residual = the guard re-shape (was /qa)
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

## /qa DISPOSITION (2026-07-21) — bump RATIFIED; re-targeted to /testing for the residual

**The 16→17 bump is RATIFIED** as a sanctioned field addition: `declared_exports`
is int-internal, unserialized, on the `prelude_fallback` model, with no
types/schema/public-api impact, and the guard's actual purpose — that
`module_sexps`/`suspend_states` do not creep back — is untouched. No parking-map
creep. The in-body comment (`tests/regression.rs:3287-3294`) documents the
addition alongside the two prior sanctioned ones. The cross-boundary edit into a
`/testing`-owned test was correct in substance; this is the process step,
discharged. Record: `tests/plan/s115-test-plan.md` §8.3.

**Residual → `/testing`** (`target:` re-pointed). A rename alone only defers the
next stale numeral, so the specified re-shape is BOTH halves:

1. assert the two forbidden fields are **ABSENT by name** (`module_sexps`,
   `suspend_states`) — a direct, non-rotting statement of what the guard
   protects;
2. **retain** the count as a creep tripwire under a numeral-free name (e.g.
   `shared_state_pub_field_count_guard`), sanctioned additions listed in-body as
   today; refresh the preceding comment block, which still narrates the
   14/15/16 lineage.

Batchable with the other W7 `/testing` riders. Delete this file when it lands.
