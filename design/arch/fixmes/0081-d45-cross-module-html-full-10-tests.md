---
number: 0081
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:1116
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0081 — d45 cross-module html full 10 tests does not crash

## Issue

10-test synthetic batch closely matching html.cl's shape. If FAIL: we've reduced to a synthetic 2-file pair. If PASS: something more specific to html.cl (perhaps the exact dependency on grid.cl's additional symbols / 20 test-* defns sitting in the grid module even though they're not called) is load-bearing.

## Test name

`d45_cross_module_html_full_10_tests_no_crash`

## Test purpose

Expands the html-like batch to 10 tests, matching html.cl's test count, with the same mix: small pure-string + Grid-build + page-derivation (contains?).

## Source location

`tests/sprint59_defects456_repro.rs:1116`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster — Phase-2 cross-module fixture probing). Sibling entries: 0065–0080, 0082–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
