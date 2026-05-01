---
number: 0068
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:278
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0068 — d45 multiple tests with contains? /run-tests does not crash

## Issue

If d45_single passes but this fails, the defect is the *second* run_test_by_name invocation in the batch leaking or double-free'ing the first test's return value. Classic last-use / RC decrement interaction with the batched dispatch loop.

## Test name

`d45_multiple_tests_with_contains_run_tests_no_crash`

## Test purpose

Multiple tests in the same module, each doing a str-concat+contains?. Tests if iteration across tests is the trigger, or body shape alone.

## Source location

`tests/sprint59_defects456_repro.rs:278`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster). Sibling entries: 0065–0067, 0069–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
