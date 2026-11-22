---
id: ACT-1111
title: Give the trace value entry points typed parameters, one entry per representation
status: open
priority: required
from: sprint
to: arch
sprint: 124
filed_at: 2026-11-22
refers_to:
  - design/arch/interfaces.md (row B18)
  - crates/cranelisp-intrinsics/src/trace.rs::cranelisp_collect_trace
  - crates/cranelisp-intrinsics/src/trace_format.rs::cranelisp_trace_format
---

## Request

Carry the user's direction of 2026-11-22 on the runtime's trace value entry
points into a later sprint. Asked to confirm the Phase 6b public-API line
`cranelisp_collect_trace(value: i64, descriptor_ptr: i64) -> i64`, the user
said:

> why do we make these functions take i64 params? that seems like a loss of
> type information.

> The big missed trick here is that we should have (at least) two functions
> so that the parameters can be typed (ie. an enum or multiple functions).
> compiler would emit the right call.

`arch` recorded the exact delta it would put through the public-API gate as
[row B18](../../design/arch/interfaces.md), escalated and not approved. The
user decided to carry the work: "let's have an action for the carry of the
typed builtins." The `(i64, i64)` line stands in the intrinsics baseline
until then.

The carried work, each part returning to the gate when scheduled:

1. Row B18: the collect and format entries become one entry per
   representation, with the described entry taking a typed descriptor
   pointer. It includes the bounded-contexts sentence on handles in emitted
   signatures, which the user has not yet accepted.
2. The rest of the trace family states pointers, lengths and handles.
3. The intrinsics catalog describes each parameter's register class, so a
   float and a truth value are typed as themselves.
4. The remaining intrinsics entry points, with ACT-0959.

`arch` observed that the next sprint's trace and display work opens the same
entries (the unrecorded root, the `#io` and `#closure` markers), and that
designing part 3 before part 1 avoids typing floats and truth values twice.
That is input to scoping, not a schedule.

## Completion evidence

- The user's decision on row B18 and its bounded-contexts sentence.
- Each part built under an approved gate row, or declined with its reason.
- The intrinsics baseline shows no entry that takes a value with a
  run-time description of its own type as two untyped words.
