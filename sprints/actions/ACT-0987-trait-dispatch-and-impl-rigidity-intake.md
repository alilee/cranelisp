---
id: ACT-0987
title: Assess trait primitive identity and impl-method rigidity leads
status: deferred
priority: required
from: design
to: qa
sprint: 122
filed_at: 2026-09-22
refers_to:
  - design/typecheck/traits.md
  - design/typecheck/inference.md
---

## S122 disposition (user-approved 2026-09-30)

Under the [approved S122 disposition](../../tests/plan/s122-evidence-delta.md#final-disposition-proposal-2026-09-30):

- **Carried to S123 (K5, N3).** First deferral.

## Request

Assess the unexecuted source-read leads retained in the designs:

- Traits open items: primitive dispatch matches bare trait/method/type names.
  Determine whether unrelated same-spelled identities bypass the selected impl.
- Inference open item: impl-method constraint rigidity is reachable now that
  annotated bodies parse. Reconcile the existing requirement through spec
  before choosing an expected outcome.

QA allocates minimal discriminating reproductions and controls, records each
lead's disposition, and routes confirmed defects. These observations are not
executed failure evidence and do not authorize a language change.

Source provenance: design session `772de8bd-8e98-42f5-8b52-93ff7c889a39`.
Sprint reopened the primitive dispatch table, body-frame construction and the
frontend impl-body parser before filing. The designs own the detailed leads;
this action supplies the intake route.
