---
id: ACT-0978
title: Assess remaining platform test trace obligations
status: open
priority: normal
from: arch
to: qa
sprint: 122
filed_at: 2026-09-22
refers_to:
  - design/arch/platform-interface.md
  - tests/platform_errors.rs
  - tests/concurrency_poll_edge_guards.rs
  - tests/exemplar_web.rs
---

## Observations requiring disposition

The platform-contract consolidation found three test-side claims needing QA
assessment. These are source-read leads, not reproduced compiler defects:

- `tests/platform_errors.rs` defers a dispatch-error round-trip to removed
  FIXME 0289. Determine whether existing evidence discharges that obligation.
- `tests/concurrency_poll_edge_guards.rs` cites the platform design for capacity
  convention and an edge-line claim that its cited section did not state.
- `tests/exemplar_web.rs` attributes a one-request-then-exit guard to the platform
  contract, but that contract did not specify it.

Assess each observation against canonical requirements and current assertions.
Repair stale traces or remove spent commentary where sufficient; allocate a
minimal independent reproduction only if a material evidence gap survives.
Do not create new requirements to justify existing test prose.

Provenance: arch session `5fb048ba-09e4-416e-9ee6-9cf90f43d420`, S122 platform
contract cleanup. No behavior change or test execution occurred in that pass.
