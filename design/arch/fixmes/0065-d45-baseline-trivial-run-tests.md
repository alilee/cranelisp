---
number: 0065
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:181
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0065 — d45 baseline trivial /run-tests does not crash

## Issue

If this test PASSES consistently, the crash is not a bare "/run-tests dispatches N tests" issue. Narrows attention to body shape. If this test FAILS (crashes), then the defect is in the batched dispatch loop itself, independent of body content.

## Test name

`d45_baseline_trivial_run_tests_no_crash`

## Test purpose

Baseline /run-tests probe: a single trivial test body returning `None`. Asserts no signal crash and that the test was actually discovered/executed (guards against vacuous pass if discovery breaks).

## Source location

`tests/sprint59_defects456_repro.rs:181`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster — html / Grid SIGSEGV defect cluster). Sibling entries: 0066–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
