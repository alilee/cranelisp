---
number: 0086
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:1519
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0086 — d45 html two tests does not crash

## Issue

2 tests doing same Grid-build + page. If crashes, the batched dispatch with shared make-grid trampoline reproduces.

## Test name

`d45_html_two_tests_no_crash`

## Test purpose

Two tests sharing the same make-grid + page. If crashes, batched dispatch of 2 Grid-building tests reproduces. If PASS, the crash also needs the test-solution-page-mixed shape (build-mixed-helper).

## Source location

`tests/sprint59_defects456_repro.rs:1519`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster). Sibling entries: 0065–0085, 0087–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
