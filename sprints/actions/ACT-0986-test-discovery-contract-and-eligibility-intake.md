---
id: ACT-0986
title: Reconcile test-discovery eligibility and published contract evidence
status: open
priority: required
from: arch
to: qa
sprint: 122
filed_at: 2026-09-22
refers_to:
  - design/arch/test-discovery.md
  - spec/appendix-a-builtins.md
  - src/session_v4/test_runner.rs
  - src/repl/commands.rs
---

## Request

Assess the source-read discrepancies retained in the current test-discovery
design. They were not exercised during documentation cleanup:

- The slash command uses `discover_test_names` (prefix, zero parameters,
  compiled body); the extern uses `discover_eligible_tests` (exact return
  scheme as well). Determine the user-visible difference with a valid test
  control and a mis-typed test candidate.
- The spec requires a discovery-time warning for excluded mis-typed tests.
  The extern comments assign it to the slash-command path, whose inspected
  handler emits no such warning. Establish the observed behavior.
- The 2026-09-22 user ruling settles the return type as a direct vector:
  introspection notionally produces a constant. The pure result
  contract is recorded in REPL section 16.3 and Appendix A; their coverage is
  marked Uncovered S122 for QA reassessment.
  No IO implementation change is required by this ruling.
- Spec assessment corrected the initial sugar observation: the reference
  library supplies `discover-here` in `stdlib/testing/runner.cl`. The primitive
  itself takes a vector. The user approved correcting the spec signature and
  runner calls to vectors and documenting the optional macro separately; those
  corrections are applied. The user settled empty-vector scope on 2026-09-22:
  retain the session current module, without recursive import traversal. QA
  reassesses evidence for scope and the corrected call shapes.
  Broader project regression discovery is deferred in
  [ACT-0988](ACT-0988-project-regression-discovery.md).
- Appendix A still describes unresolved-symbol failure under --link; the
  design and existing link tests describe an earlier named compile-time refusal.
  The proposed normative correction was held when the user chose future
  capability parity between normal run and release execution, with an explicit
  test-harness mode. Coordinate this requirement through
  [ACT-0988](ACT-0988-project-regression-discovery.md); do not treat the proposed
  wording permitting discovery in ordinary --run as approved.

- The spec call-shape pass found additional problems in the programmatic-use
  example: match-arm grouping and nested constructor patterns differ from the
  current grammar, and helper imports are incomplete. Assess a runnable example
  against settled syntax; keep this distinct from discovery behavior changes.
  The frontend parse-only test `test_discover_tests_no_arg_builds_as_apply`
  also needs its requirement attribution checked: parsing an application is
  separate from accepting its arity during typechecking.

## Completion evidence

Record requirement authority and evidence separately for each discrepancy.
Confirmed defects need narrow unignored spec-traced reproductions and controls;
no assertion or runtime change is authorized by this filing alone. Any unsettled
language choice returns to the user through spec, one decision at a time.

## Approved carry: ordinary-run discovery

On 2026-09-27 the user approved carrying DT-1's confirmed `--run` defect
with the explicit test-harness work in
[ACT-0988](ACT-0988-project-regression-discovery.md). Enabling discovery in
ordinary `--run` now would add capability that the approved `--test`
direction relocates. This carry applies only to DT-1, not the other intake
items in this action.

Source rechecked on approval: `discover_tests_extern` in
`src/session_v4/test_runner.rs` returns an empty vector when its runner state
is absent. The unignored regression
`tests/spec_12_runtime.rs::discover_tests_named_module_under_run_counts_its_tests`
expects three tests and observes zero. Keep that guard failing until the
approved harness requirements and implementation settle its replacement.
The carry neither accepts silent empty discovery as correct nor selects new
REPL or CLI semantics.

Provenance: arch session `d96c6803-f6bb-41af-9b27-55ce03ad1d30`; sprint reopened
both discovery scans, the slash-command handler and Appendix A before filing.


## Requirement assessment

Spec session `25b7b7c9-1981-41b9-94db-c9e27c94316e` recovered conflicting S76
return-type authority. The user subsequently chose notionally constant
introspection and the direct vector result (2026-09-22). The return-type
question is settled. The subsequent user ruling also settles empty-vector
module scope as the session current module; evidence reassessment remains open.
Warning and exact eligibility requirements are settled. Early linked-mode
refusal was the anticipated replacement for an explicitly interim unresolved
symbol failure. The proposed replacement prose remains unapproved; the later
mode-parity ruling and deferred harness work are recorded in ACT-0988.
