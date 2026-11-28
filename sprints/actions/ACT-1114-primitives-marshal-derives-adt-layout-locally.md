---
id: ACT-1114
title: Converge the primitives Sexp marshaller on the intrinsics ADT layout
status: open
priority: advisory
from: sprint
to: design
sprint: 125
filed_at: 2026-11-27
refers_to:
  - design/arch/bounded-contexts.md
  - design/intrinsics/heap-layout.md
  - crates/cranelisp-primitives/src/marshal.rs
  - crates/cranelisp-intrinsics/src/alloc.rs
---

## Request

`design` on primitives converges `crates/cranelisp-primitives/src/marshal.rs`
on `cranelisp_intrinsics::alloc::HeapAdt`, through the approved but unbuilt
"ADT layout edge" in `design/arch/interfaces.md` (R10-9, user-approved
2026-11-17). Either the layout census covers this module, or the gap becomes a
named residual.

Verified 2026-11-27: lines 42–45 derive the tag and field offsets from
`HeapHeader::SIZE` and a local `FIELD_STRIDE`, not from `HeapAdt`. Invariant 2
of [bounded contexts, intrinsics](../../design/arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics)
names this module as an exception.
The binary's copy, `src/marshal.rs`, converges in S125 Phase 6b, because
`src/` is that sprint's focus module.

## Completion evidence

No ADT offset is defined in primitives, and the census or a named residual
covers the module.
