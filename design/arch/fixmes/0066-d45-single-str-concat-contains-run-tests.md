---
number: 0066
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:214
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0066 — d45 single str-concat+contains? /run-tests does not crash

## Issue

Isolates whether a single str-concat+contains? test body through /run-tests is enough to crash. If PASS: need to widen to multiple tests or a deeper string. If FAIL: this one test shape is sufficient — the defect is in str-concat / contains? / run_test_by_name dispatch for Option-returning bodies.

## Test name

`d45_single_str_concat_contains_run_tests_no_crash`

## Test purpose

One test body that does a 2-link str-concat + contains? — html.cl's `test-form-page-has-inputs` shape minimised, no Option ADT in body, no wrap-tag, no css. Driven through /run-tests.

## Source location

`tests/sprint59_defects456_repro.rs:214`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster). Sibling entries: 0065, 0067–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
