---
number: 0225
target: /qa
filed_by: /qa
filed_at: 2026-05-27
sprint_filed: 71
refers_to: design/arch/facades/cranelisp-platform-audit-s69.md §4 C2, tests/plan/sprint71-platform.md §3
status: deferred
deferred_to: 72
deferred_at: 2026-05-28
deferred_rationale: |
  Sprint 71 Wave 1 gate disposition. Filed in Phase 3 explicitly to
  carry forward. Conformance-triad evolution belongs in a separate
  sprint (target 72) alongside 0218, 0224, 0227, 0228 — same axis,
  one coherent landing rather than scattered point patches.
---

# `#[non_exhaustive]` annotation appearance/removal mechanical-coverage gap (audit C2)

## Issue

`OwnedPlatformFnDescriptor` carries `#[non_exhaustive]` per `cranelisp-platform/public-api.txt:168`; CLOwned correctly does not. The text-grep `facade_compliance.rs` only checks substring presence of the type name; it does not check the `#[non_exhaustive]` attribute prefix. A regression silently dropping `#[non_exhaustive]` on `OwnedPlatformFnDescriptor` would pass conformance and silently break Principle 14's post-load owned descriptor's field-set evolution discipline.

## Proposed resolution

Add a PIF-row coverage of the `#[non_exhaustive]` attribute presence on the types where it is required (currently `OwnedPlatformFnDescriptor`). Per cargo-public-api's emission shape this should be greppable in the baseline file; the PIF row asserts the line appears.

## Operational implication / Context

The audit recommended this for S70 `/qa` enhancement. Sprint 71 carried forward because its scope is `cranelisp-platform` API addition + facade retirement, not conformance-triad evolution. Closure is mechanical and small-sprint-sized.
