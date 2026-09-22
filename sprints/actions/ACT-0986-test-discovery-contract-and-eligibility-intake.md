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
  itself takes a vector; REPL spec examples wrongly present the convenience
  forms as primitive calls. The empty-vector current-module meaning also needs
  arbitration: the implementation uses the session module, while earlier
  rationale described a caller-module literal. Keep these issues distinct.
- Appendix A still describes unresolved-symbol failure under --link; the
  design and existing link tests describe an earlier named compile-time refusal.
  Reconcile that stale implementation description through spec.

## Completion evidence

Record requirement authority and evidence separately for each discrepancy.
Confirmed defects need narrow unignored spec-traced reproductions and controls;
no assertion or runtime change is authorized by this filing alone. Any unsettled
language choice returns to the user through spec, one decision at a time.

Provenance: arch session `d96c6803-f6bb-41af-9b27-55ce03ad1d30`; sprint reopened
both discovery scans, the slash-command handler and Appendix A before filing.


## Requirement assessment

Spec session `25b7b7c9-1981-41b9-94db-c9e27c94316e` recovered conflicting S76
return-type authority. The user subsequently chose notionally constant
introspection and the direct vector result (2026-09-22). The return-type
question is settled; the remaining module-scope question is separate.
Warning and exact eligibility requirements are settled. Early linked-mode
refusal was the anticipated replacement for an explicitly interim unresolved
symbol failure; its stale prose needs correction under the normative edit gate.
