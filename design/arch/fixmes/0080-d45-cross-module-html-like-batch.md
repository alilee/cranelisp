---
number: 0080
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:985
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0080 — d45 cross-module html-like batch does not crash

## Issue

4 tests including Grid-build + cross-module match + deep str-concat nesting. Closely mirrors html.cl's test surface.

## Test name

`d45_cross_module_html_like_batch_no_crash`

## Test purpose

Combines the prior reductions: html-like mix of tests — some pure string (wrap-tag), some build a Grid via a helper and do `contains?` on a derived string. Mirrors html.cl's test block layout.

## Source location

`tests/sprint59_defects456_repro.rs:985`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster — Phase-2 cross-module fixture probing). Sibling entries: 0065–0079, 0081–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
