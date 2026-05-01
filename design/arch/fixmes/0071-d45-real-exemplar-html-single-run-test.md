---
number: 0071
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:354
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0071 — d45 real exemplar html single run-test does not crash

## Issue

If this test passes and `d45_real_exemplar_html_run_tests_no_crash` fails, defect is in the /run-tests dispatch loop, not the individual run-test call. If this ALSO fails, the defect is in evaluating a single html.cl test body (narrower).

## Test name

`d45_real_exemplar_html_single_run_test_no_crash`

## Test purpose

Single-test variant: just invoke `(run-test "test-wrap-tag")` against the real exemplar/html.cl (copied into a fresh TempDir). The earlier /port Wave 6 finding said single run-test invocations work; only batched /run-tests crash. Pins that finding.

## Source location

`tests/sprint59_defects456_repro.rs:354`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster). Sibling entries: 0065–0070, 0072–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
