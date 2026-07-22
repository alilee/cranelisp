---
number: 0857
target: /qa
filed_by: /sprint
filed_at: 2026-07-22
sprint_filed: 116
refers_to: audits/cranelisp-intrinsics-s115.md §2.3 and §6 R-7; tests/plan/s115-instrumentation-matrix.md; tests/ms_p6_mode_self_tests.rs
status: open
---

# Regrade R8 diagnostic modes against live detection proof

## Issue

Accepted audit recommendation R-7, `/qa` portion. R8 cites line 55 of `ms_p6_mode_self_tests.rs` as an e2e plant, but that line is inside the retired test's tombstone. M1 and M2 are currently asserted-but-unproven under QA's own detection-proof bar.

## Proposed resolution

Remove or repair the dead citation, grade each mode at its actually proven tier, and promote grades only after FIXME 0848 lands fail-on-revert detection evidence.
