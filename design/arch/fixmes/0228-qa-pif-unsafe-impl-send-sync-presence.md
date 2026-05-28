---
number: 0228
target: /qa
filed_by: /qa
filed_at: 2026-05-27
sprint_filed: 71
refers_to: design/arch/facades/cranelisp-platform-audit-s69.md §4 C5, tests/plan/sprint71-platform.md §3
status: deferred
deferred_to: 72
deferred_at: 2026-05-28
deferred_rationale: |
  Sprint 71 Wave 1 gate disposition. Filed in Phase 3 explicitly to
  carry forward. PIF-row coverage of `unsafe impl Send/Sync` presence
  belongs in the conformance-triad-enhancement sprint (target 72)
  alongside 0218, 0224, 0225, 0227.
---

# `unsafe impl Send/Sync` presence mechanical-coverage gap (audit C5)

## Issue

`unsafe impl Send for PlatformFn` + `unsafe impl Sync for PlatformFn` (at `crates/cranelisp-platform/src/lib.rs:97–98`) are load-bearing: removing them breaks the IO trampoline's ability to hold platform-fn pointers across threads. Conversely, adding `unsafe impl Send/Sync` to a type that should NOT have those auto-traits silently expands the safety surface. Neither change is caught by the current conformance triad.

## Proposed resolution

Add PIF-row coverage of `unsafe impl Send/Sync` claims per type. Assert presence (or absence) against the facade's documented invariants (post-Sprint-71 retirement: per the rustdoc + BC §5 narrative).

## Operational implication / Context

The audit explicitly named this for S70 `/qa` enhancement. Sprint 71 carried forward because its scope is API addition + facade retirement, not conformance-triad evolution. Sprint 71's facade retirement folds the F3 + F4 narrative into source rustdoc + BC §5 (covering the `unsafe impl Send/Sync for PlatformFn` justification + the auto-projected `!Send + !Sync` on `OwnedPlatformFnDescriptor` + `PlatformManifest`); the mechanical-check FIXME complements that narrative landing with executable enforcement.
