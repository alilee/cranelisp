---
number: 0077
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:833
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0077 — d45 cross-module ADT basic does not crash

## Issue

cross-module ADT constructor + match in a test body. If PASS: cross-module ADT alone is not enough; need Vec or Grid wrapper.

## Test name

`d45_cross_module_adt_basic_no_crash`

## Test purpose

Minimum cross-module shape: `lib` exports a Cell ADT; `mymod` imports it + uses `(Given 5)` constructor + match in ONE test body. Smallest "two-file" reduction.

## Source location

`tests/sprint59_defects456_repro.rs:833`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster — Phase-2 cross-module fixture probing). Sibling entries: 0065–0076, 0078–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
