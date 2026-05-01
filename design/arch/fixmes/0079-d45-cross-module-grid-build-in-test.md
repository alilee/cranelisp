---
number: 0079
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:903
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0079 — d45 cross-module Grid build in test does not crash

## Issue

one test that builds (Grid (Vec Cell)) using a cross-module constructor. If FAIL: cross-module Grid-build via batched /run-tests is the trigger. If PASS: needs MORE in the test body (string concat + Grid use combined).

## Test name

`d45_cross_module_grid_build_in_test_no_crash`

## Test purpose

mymod actually BUILDS a Grid via a helper (mirroring `make-all-ones-grid` in html.cl); test body verifies the constructed cell value through `cell-at`/`cell-value`.

## Source location

`tests/sprint59_defects456_repro.rs:903`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster — Phase-2 cross-module fixture probing). Sibling entries: 0065–0078, 0080–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
