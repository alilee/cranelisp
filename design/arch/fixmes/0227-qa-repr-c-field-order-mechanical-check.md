---
number: 0227
target: /qa
filed_by: /qa
filed_at: 2026-05-27
sprint_filed: 71
refers_to: design/arch/facades/cranelisp-platform-audit-s69.md §4 C4, tests/plan/sprint71-platform.md §3
status: deferred
deferred_to: 72
deferred_at: 2026-05-28
deferred_rationale: |
  Sprint 71 Wave 1 gate disposition. Filed in Phase 3 explicitly to
  carry forward. The (a) `cbindgen`-diff vs (b) `offset_of!`-table
  choice is sprint-sized in its own right and belongs in the
  conformance-triad-enhancement sprint (target 72) alongside 0218,
  0224, 0225, 0228. Sprint 71 ships the A4 policy (`ABI_VERSION`
  bump on layout-affecting change) which is the author-discipline
  protection; mechanical enforcement is the still-open gap.
---

# `#[repr(C)]` struct field-order mechanical-coverage gap (audit C4)

## Issue

`PlatformManifest` and `PlatformFn` are `#[repr(C)]` per Principle 14. A field-order reshuffle that changed byte offsets (e.g., swapping `param_count` and `type_sig`) would NOT be caught by `facade_compliance.rs` (all field names still appear) NOR by `public_api_relocations.rs` (cargo-public-api emits fields as an unordered set). The only failure mode is runtime: a DLL written against the old layout loads, reads garbage at every offset past the swap.

`ABI_VERSION` bump is the documented author-discipline protection (per A4); Sprint 71 lands the policy (1 → 2) but does not add mechanical enforcement.

## Proposed resolution

Either (a) generate `cbindgen` C-header on every CI run and diff against a frozen baseline header committed to the repo, OR (b) author an explicit per-field offset assertion test using `std::mem::offset_of!` against a frozen offset table. The audit recommended (a) as the more durable fix because it surfaces the layout change to DLL authors at integration time. /qa picks one.

`HostCallbacks` (which grew in Sprint 71) should be added to the protected set in the same enhancement.

## Operational implication / Context

The mechanical-enforcement gap is the largest C-hole this layer carries; the new ADT-traversal API in Sprint 71 increases the surface area at risk because `CLAdt`'s field-traversal correctness depends on the DLL's parsed-schema-offsets matching cranelisp's actual heap layout — a schema/layout mismatch is a runtime explosion. Closing this gap eventually closes the layout-drift hazard for the whole platform-crate's `#[repr(C)]` set.
