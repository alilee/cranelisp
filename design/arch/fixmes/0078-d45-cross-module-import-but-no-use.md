---
number: 0078
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:875
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0078 — d45 cross-module import but no use does not crash

## Issue

mymod imports Grid-ADT symbols but never builds one; tests are pure-string. If PASS: the IMPORT alone doesn't trigger. Crash requires test bodies to actually USE the cross-module ADT.

## Test name

`d45_cross_module_import_but_no_use_no_crash`

## Test purpose

Two pure-string tests (wrap-tag + contains?) where mymod imports the cross-module Grid-ADT symbols but never constructs one. Probes whether the import alone, without use, triggers the crash.

## Source location

`tests/sprint59_defects456_repro.rs:875`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster — Phase-2 cross-module fixture probing). Sibling entries: 0065–0077, 0079–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
