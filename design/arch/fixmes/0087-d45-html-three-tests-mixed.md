---
number: 0087
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:1586
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0087 — d45 html three tests with second grid-build does not crash

## Issue

3 tests, third uses a SECOND grid-build function (build-mixed-helper — nested if picking among 3 variants). If crashes, two distinct Vec-of-ADT-building functions in same module is the trigger.

## Test name

`d45_html_three_tests_mixed_no_crash`

## Test purpose

Add a second make-grid variant building MIXED cells (Given 5, Solved 3, Given 1) via a nested if-chain. A third test uses it. Probes whether two distinct grid-build functions in the same module are needed to trigger the crash.

## Source location

`tests/sprint59_defects456_repro.rs:1586`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster). Sibling entries: 0065–0086, 0088–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
