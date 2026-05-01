---
number: 0069
target: /backend
filed_by: /qa
filed_at: 2026-05-01
sprint_filed: 64
refers_to: tests/sprint59_defects456_repro.rs:300
status: open
migrated_from_inline: true
split_from_cluster: 0024
---

# 0069 — d45 form-shaped body /run-tests does not crash

## Issue

form.cl uses substring/split which are additional RC-sensitive primitives. This minimal form-shaped body probes whether the Option(Some "...") form itself — heap-string argument to Some constructor — is the crash surface.

## Test name

`d45_form_shaped_body_run_tests_no_crash`

## Test purpose

form.cl's simplest test shape — process-pair / substring / split are not under suspicion here; this is just a minimal let + str-eq + Option.

## Source location

`tests/sprint59_defects456_repro.rs:300`

## Cluster context

This entry was split from cluster 0024 (Sprint 59 Defects 4/5/6 reduction cluster). Sibling entries: 0065–0068, 0070–0090.

## Proposed resolution

`/backend` reads `design/backend/defects-456-reduction.md` for the hypothesis catalogue and runs the cluster as a unit. Continue reduction (or land the fix) until all currently-failing tests in the file pass.
