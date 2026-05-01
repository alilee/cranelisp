---
number: 0083
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:1328
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0083 — d45 html minus css does not crash

## Issue

real html.cl minus the css function. If STILL crashes, css is not the culprit. If PASS, css's massive str-concat depth is the trigger.

## Test name

`d45_html_no_css_no_crash`

## Test purpose

Keep ALL 10 tests but remove the `css` function (giant str-concat) and simplify form-page / error-page / solution-page so they don't invoke css. Probes whether the deeply nested `css` function is load-bearing.

## Source location

`tests/sprint59_defects456_repro.rs:1328`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster). Sibling entries: 0065–0082, 0084–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
