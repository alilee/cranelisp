---
number: 0076
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:786
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0076 — d45 ten str-concat bodies /run-tests does not crash

## Issue

If this passes but d45_real_exemplar_html fails, the defect is NOT batch-size driven: it specifically needs html.cl's imports (grid.cl) or one of its specific helpers (build-all-ones-helper constructs a Vec of 81 Grid cells). The presence of the grid.cl dep chain — and specifically the Grid ADT and Vec of Cell work — may be load-bearing.

## Test name

`d45_ten_str_bodies_run_tests_no_crash`

## Test purpose

Ten tests with str-concat bodies returning None. Probes whether the issue is about THE NUMBER OF tests in the batch, or specifically about html.cl's content.

## Source location

`tests/sprint59_defects456_repro.rs:786`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster). Sibling entries: 0065–0075, 0077–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
