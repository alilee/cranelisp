---
id: ACT-0980
title: Investigate declaration preservation after warm-cache restart
status: open
priority: high
from: design
to: qa
sprint: 122
filed_at: 2026-09-22
---

## Intake and next disposition

Design source reading suggests regeneration may omit cache-restored type,
trait and impl declarations lacking introspection records. This is an
unconfirmed potential user-source-loss defect, not an observed failure.

QA first verifies the applicable persistence requirement and existing evidence.
Allocate a fresh-tempdir warm-cache restart reproduction, using the existing
function-preservation case as a control that differs in declaration kind.
If the requirement is silent, route the question to spec before authoring an
acceptance assertion. Retain any confirmed failing, unignored reproduction;
route implementation to Binary/int design. A cache/schema change must follow
architecture and public-interface approval rules. A passing discriminating
case refutes the lead and remains useful variant coverage.

Provenance: design `592f93c0-b976-4974-8495-8f4f7fce2f30` and QA
`2775f537-568e-413c-ad70-504650addb1c`, S122 integration-document consolidation.
