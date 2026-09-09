---
id: ACT-0958
title: Restore positively armed failed-turn recovery and diagnostic coverage
status: open
priority: required
from: sprint
to: qa
sprint: 121
filed_at: 2026-09-09
refers_to:
  - tests/spec_11_stdlib.rs
  - tests/plan/s117-test-plan.md §3.3
  - repl/spec/18-redefinition.md
---

## Request

The user approved deferral to the top of the next sprint while wrapping S121.
Coordinate this evidence repair with the now-reproduced generic redefinition
defect; the permanent unignored public tests, not a duplicate filing, retain
that defect. Establish its implementation owner from the scalar RED and vector
SIGSEGV sibling before designing a fix. Do not assume both share a cause.

The four failed-codegen witnesses in `tests/spec_11_stdlib.rs` use a
`vec-flatten` trigger that now succeeds. None asserts its initial failure or
child-process success; two can pass without exercising failure recovery.
Restore the allocated failed-turn publication, recovery and diagnostic
evidence without weakening its requirements. Require the intended failure to
occur and verify process completion and subsequent observations independently.
If no legitimate public codegen-failure trigger exists, return the testability
decision to the user rather than inventing faulty language behavior or silently
claiming coverage. Reconcile stale test-side section references in the same visit.

## Completion evidence

QA identifies a stable, positively armed failure/control and the narrowest
appropriate evidence layer; test implements that allocation. Each witness
fails when its intended failure is absent or its required recovery/diagnostic
is wrong. The public generic-redefinition REDs remain enabled until a separately
designed, unit-guarded fix turns them green. Coverage records distinguish that
successful-redefinition defect from failed-turn semantics. No compiler fix,
new production test seam, API or specification change is authorized by this carry.
