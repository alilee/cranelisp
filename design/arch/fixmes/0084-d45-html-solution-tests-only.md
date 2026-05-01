---
number: 0084
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:1420
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0084 — d45 html solution tests only does not crash

## Issue

only 3 Grid-touching tests. If crashes, we've pinned the axis to solution-page tests. If PASS, need to keep other tests.

## Test name

`d45_html_solution_tests_only_no_crash`

## Test purpose

Strip: remove form-page tests + test-td + test-wrap-tag + test-error-page-*. Keep ONLY the 3 solution-page tests (which touch Grid via cross-module match). Cross-module-ADT-in-test-body is the remaining axis.

## Source location

`tests/sprint59_defects456_repro.rs:1420`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster). Sibling entries: 0065–0083, 0085–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
