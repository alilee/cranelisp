---
number: 0070
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:316
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0070 — d45 real exemplar html /run-tests does not crash

## Issue

Runs /run-tests against the real exemplar/html.cl. Because all synthetic reductions above pass, this test isolates the defect to something load-bearing that html.cl has but the synthetic modules don't:

  (a) html.cl imports grid.cl which defines its own Cell/Grid ADTs — synthetic module has no dep chain. Cross-module ADT RC?
  (b) html.cl has 15+ defns including build-all-ones-helper + Grid constructor usage — something about size / JIT finalize batch?
  (c) html.cl's test bodies use make-all-ones-grid which calls Grid + vec-push in a loop — the ADT-wrapped Vec flow is unique to html.cl vs. the synthetic modules.

Resolver must strip html.cl further — try removing test-solution-page-* tests (those that touch Grid), then test-td / test-wrap-tag (which are pure strings). The mid-point determines whether (a), (b), or (c) is the axis.

## Test name

`d45_real_exemplar_html_run_tests_no_crash`

## Test purpose

Loads the real exemplar/html.cl in-situ (copied into a fresh TempDir) and runs `/run-tests html` (triggers batch dispatch of ALL html test-* fns).

## Source location

`tests/sprint59_defects456_repro.rs:316`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster). Sibling entries: 0065–0069, 0071–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
