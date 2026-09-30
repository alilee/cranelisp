---
id: ACT-0981
title: Assess automatic IO scheduling in multi-signature bodies
status: deferred
priority: normal
from: design
to: qa
sprint: 122
filed_at: 2026-09-22
---

## S122 disposition (user-approved 2026-09-30)

Under the [approved S122 disposition](../../tests/plan/s122-evidence-delta.md#final-disposition-proposal-2026-09-30):

- **Carried to S123 (K7, R4).** First deferral.

## Intake and next disposition

Source reading confirms the scheduling pass skips multi-signature functions
and multi-signature impl methods; single-signature impl methods are scheduled.
The broad automatic-scheduling requirement may therefore be unmet. No wrong
output or observed latency difference has been reproduced.

After ACT-0980, QA assesses a single-signature versus multi-clause twin using
the observation already used for independent commutative binds. Allocate a
minimal reproduction only with a discriminating supported observation. A
confirmed failure routes to Binary/int design and dev; lack of an observation
is a testability question, not evidence of conformance. Any proposed narrowing
of the language requirement returns to the user through spec.

Provenance: design `592f93c0-b976-4974-8495-8f4f7fce2f30` and QA
`2775f537-568e-413c-ad70-504650addb1c`, S122 integration-document consolidation.
