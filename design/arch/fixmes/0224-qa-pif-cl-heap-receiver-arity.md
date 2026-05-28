---
number: 0224
target: /qa
filed_by: /qa
filed_at: 2026-05-27
sprint_filed: 71
refers_to: design/arch/facades/cranelisp-platform-audit-s69.md §4 C1, tests/plan/sprint71-platform.md §3
status: deferred
deferred_to: 72
deferred_at: 2026-05-28
deferred_rationale: |
  Sprint 71 Wave 1 gate disposition. Filed in Phase 3 explicitly to
  carry forward — Sprint 71 scope is `cranelisp-platform` API
  additions + facade retirement, not conformance-triad evolution.
  Folded into the future conformance-triad-enhancement sprint (target
  72) alongside 0218, 0225, 0227, 0228 for a coherent landing.
---

# CLHeap method receiver/arity mechanical-coverage gap (audit C1)

## Issue

The S69 facade audit identified that the conformance triad cannot catch a `CLHeap` method receiver/arity drift — e.g., `inc_rc(&self)` silently flipping to `inc_rc(self)`. Text-grep on `facade_compliance.rs` sees the name `inc_rc` and passes; public-api diff would flag it only if the baseline isn't co-regenerated.

## Proposed resolution

Add a PIF-row covering the structural signature (receiver type + return type) per `CLHeap` method. The row goes in the existing PIF infrastructure (whichever file `/qa` is currently using for per-item structural assertions); the assertion shape is mechanical (no DLL-author repro needed). One-sprint scoped enhancement; not Sprint 71 because the surface change in that sprint is API addition not conformance-triad evolution.

## Operational implication / Context

The audit explicitly named this gap as a `/qa` enhancement target for S70 (or later); Sprint 71 carried it forward because Sprint 71 narrowed scope to `cranelisp-platform` API + facade retirement. Once landed, the gap closes against all current and future `CLHeap`-impl types (CLInt, CLBool, CLFloat, CLString, CLOwned, CLIO, and the new `CLAdt<T>` joining the family in Sprint 71).
