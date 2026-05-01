---
number: 0067
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:248
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0067 — d45 wrap-tag html-verbatim /run-tests does not crash

## Issue

Copies html.cl test-wrap-tag verbatim minus the exemplar imports. If this test FAILS (crashes), the defect reproduces on a single 5-deep str-concat composition + str-eq. That pinpoints the likely culprit to either (a) the nested str-concat RC accounting for intermediate strings, (b) str-eq's consuming convention for one-shot strings, or (c) the Option return-value handling in run_test_by_name when the body produces a heap value (None/Some) as last op.

## Test name

`d45_wrap_tag_html_verbatim_run_tests_no_crash`

## Test purpose

Inlined `wrap-tag` (5-deep nested str-concat) + `test-wrap-tag` (str-eq compare returning Option). Verbatim from html.cl with no dependency on grid.cl / css. Driven through /run-tests.

## Source location

`tests/sprint59_defects456_repro.rs:248`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster). Sibling entries: 0065–0066, 0068–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
