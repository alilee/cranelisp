---
number: 0014
target: /backend
filed_by: /unknown
filed_at: 2026-05-01
sprint_filed: 64
refers_to: crates/cranelisp-backend/plan-backend.md:36, crates/cranelisp-backend/plan-backend.md:613
status: open
migrated_from_inline: true
---

# 0014 — `plan-backend.md` references retired `run-tests` special form

## Issue

`crates/cranelisp-backend/plan-backend.md` line 36 lists `run-tests` as a Ring 4 feature, but the `(run-tests init pass-fn fail-fn)` special form has been retired — replaced by the `discover-tests` / `run-test` builtins (`spec/appendix-a-builtins.md §A`). The line should be updated to list the builtins (or drop `run-tests` entirely).

Also see line 613: `HIGH-4: compile_run_tests is 233 lines` — that deferral is moot because the special form no longer exists; confirm `compile_run_tests` is deleted from the backend tree, or update the resolution line. Filed Sprint 57 planning.

## Source location

`crates/cranelisp-backend/plan-backend.md:36` (Ring 4 feature list) and `crates/cranelisp-backend/plan-backend.md:613` (HIGH-4 entry).

## Context

The Ring 4 feature list enumerates compiler features that the backend ships. Both line 36 and the HIGH-4 entry reference a special form whose lifetime ended when test discovery was refactored to the builtin shape.

## Proposed resolution

Edit line 36 to list `discover-tests` / `run-test` (or drop the bullet); audit `compile_run_tests` in the backend tree and either delete the function or update HIGH-4 with current resolution. Update the line's reference to `spec/appendix-a-builtins.md §A`.
