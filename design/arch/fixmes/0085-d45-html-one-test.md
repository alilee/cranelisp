---
number: 0085
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:1468
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0085 — d45 html one test does not crash

## Issue

one test, one function that builds a nested string via cross-module match. Simplified solution-cell signature.

## Test name

`d45_html_one_test_no_crash`

## Test purpose

Radical strip: ONE test, minimal solution-page (inline the row helpers flat). All that remains: build a grid, call a function that matches on cross-module ADT + str-concats, `contains?` the result.

## Source location

`tests/sprint59_defects456_repro.rs:1468`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster). Sibling entries: 0065–0084, 0086–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
