---
id: ACT-1110
title: An unrecorded trace root is named `::skipped::` and has an empty result
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-22
refers_to:
  - spec/04-expressions.md §4.12.6
  - spec/04-expressions.md §4.12.5
  - design/intrinsics/trace-runtime.md §7.2
  - crates/cranelisp-intrinsics/src/trace.rs
---

## Authority

The user ruled S124-Q17 and Q18 on 2026-11-22 (`spec` at `2fe6d28f`).
[Spec §4.12.6](../../spec/04-expressions.md): a form that does not activate
instrumentation returns an unrecorded trace whose root is named
`::untraced::`, with no parameters, and whose result is the body's value
formatted; the result MUST NOT be empty merely because the form did not
record. §4.12.5: a form entered inside an unrecorded form MUST NOT raise
and returns an unrecorded trace.

## Classification: nonconforming by source; not reproduced

- **In source.** `crates/cranelisp-intrinsics/src/trace.rs` names the root
  of a skipped form `::skipped::`.
  [Trace runtime §7.2](../../design/intrinsics/trace-runtime.md) records
  its result as empty, "current behaviour; open".
- **`qa` did not observe it.** A form is unrecorded only when another
  thread holds the trace role, and no fixture built from user commands
  selects that.
- **§4.12.5's new clause** is as `arch` reports it: the guard permits
  entry. `qa` did not observe that either.
- **Severity: wrong value,** in a state a program reaches only under
  concurrent tracing.

## Routing

- **`qa` holds this action.**
- **No `test` cell.** This is a named residual: the state cannot be
  selected from a program.
- **`dev`(intrinsics), with the correction:** module rows over the collect
  entry's skipped state for the name, the rendered result, and the inner
  form. `arch`'s row B18 is with the user.

## Completion evidence

The module rows pass and were seen to fail first.
