---
id: ACT-0959
title: Assess a full ownership-returning public allocation API redesign
status: open
priority: advisory
from: sprint
to: arch
sprint: 122
filed_at: 2026-09-10
refers_to:
  - crates/cranelisp-intrinsics/src/alloc.rs
  - crates/cranelisp-intrinsics/src/heap_string.rs
  - crates/cranelisp-intrinsics/src/vec_runtime.rs
  - design/runtime/s119-typed-consume-funnel.md
  - sprints/s122-primitives-allocation-proposal.md
---

## Request

At the next sprint's scope review, consider a full redesign of public Rust
allocation and construction APIs so ownership is represented at the producer
boundary. The user requested this future alternative on 2026-09-10 while
approving S122's limited private construction/traversal/storage amendment.
This action is future architecture work, not a prerequisite for that amendment
or approval to implement a public API redesign.

Source verified on filing: opened the implementations of `alloc_with_rc`,
`alloc_string`, and `vec_strings_from_owned` in the three intrinsics files
above. The first initializes the header before caller payload construction;
the second returns a completed String; the third assumes child ownership at
call entry and guards incomplete construction through unwind. Their current
raw pointer/word interfaces leave ownership assertions to consumers.

Arch should compare the approved private adapters with a public construction
boundary that returns typed ownership where a value is fully initialized.
Distinguish raw allocation from completed values; simply returning an owner
from the raw allocator risks permitting typed disposal before payload readiness.
Assess child transfer into ADT/Vec storage, borrowed child projection, partial
initialization and error/unwind cleanup, existing Rust consumers, and emitted
and platform ABI compatibility. Compare the reduction in trusted raw conversions
with migration and maintenance cost. Route the selected design to the affected
crate design owners in coordinated invocations.

## Completion evidence

Produce an architecture recommendation with exact proposed public signatures,
producer/consumer migration scope, compatibility and schema/ABI effects,
expected public baseline changes, and the evidence needed for construction,
transfer and cleanup. Return the proposed public delta to the user before
implementation. An explicit decision to retain the limited design may resolve
this assessment with its rationale; filing it does not commit a future sprint
to redesign implementation.
