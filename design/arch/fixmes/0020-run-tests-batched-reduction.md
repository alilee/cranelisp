---
number: 0020
target: /int
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint60_run_tests_reduction.rs:80, design/backend/defects-456-reduction.md §"Sprint 60 Wave 2 Round 3"
status: open
migrated_from_inline: true
---

# 0020 — `/run-tests` batched reduction (S60 Round 3)

## Issue

Per `memory/feedback_repros_join_suite.md`: four reductions are failing tests (each bounds the defect shape). The fifth is a passing negative control that proves the defect is specific to REPL-eval'd imports. All five are regression guards. Pick up from `design/backend/defects-456-reduction.md §"Sprint 60 Wave 2 Round 3 — run-tests batched reduction"`.

The owning skill could be `/int` (REPL-eval / session orchestration) OR `/backend` (codegen). Per `defects-456-reduction.md §"Owning skill"`, the leading hypothesis names `/int` (`session_v4::regenerate_backing_file` or the enclosing REPL-eval path); see also FIXME 0028.

## Source location

`tests/sprint60_run_tests_reduction.rs:80` (file-header FIXME).

## Context

The reduction file commits 5 tests committed as the durable record of the Sprint 60 Wave 2 Round 3 narrowing. Continued reduction work picks up from the `defects-456-reduction.md` design doc.

## Proposed resolution

`/int` (or `/backend` if reduction surfaces a codegen-layer cause) reads the reduction commentary, runs the failing tests, and continues reducing or fixes the underlying defect.
