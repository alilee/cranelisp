---
id: ACT-0979
title: Establish platform function-type rejection evidence
status: deferred
priority: normal
from: spec
to: qa
sprint: 122
filed_at: 2026-09-22
refers_to:
  - spec/10-io.md
  - design/arch/platform-interface.md
---

## S122 disposition (user-approved 2026-09-30)

Under the [approved S122 disposition](../../tests/plan/s122-evidence-delta.md#final-disposition-proposal-2026-09-30):

- **Carried to S123 (K6, C3).** First deferral. A `spec` question precedes the RED: does "contain" extend through a named ADT's fields?

## Approved requirement

The user approved explicitly prohibiting function types in platform parameter
and result types and requiring rejection of such declarations. The canonical
requirement is `spec/10-io.md` §10.10.1. This retires the former promise of host
closure-invocation and reference-count callbacks, contrary to the S98 boundary
ruling. The changed requirement is uncovered; enforcement has not been verified.

## Next disposition

QA assesses existing evidence and allocates the smallest discriminating
rejection case and ordinary-signature control. Assess containment in parameter
and result types against the approved requirement, not only a direct top-level
function parameter. If the implementation accepts a forbidden declaration,
retain an unignored spec-traced reproduction and route the confirmed defect to
the appropriate implementation owner. No callback capability or public ABI
change is authorized by this action.

Provenance: spec assessment session `7b345e8f-c2fb-4ada-bac2-4d6213a2da16`;
user ruling 2026-09-22: “State the boundary and require rejection”.
