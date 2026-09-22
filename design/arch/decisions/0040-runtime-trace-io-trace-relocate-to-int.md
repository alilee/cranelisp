---
number: 0040
title: IO observation is a callback contract registered with intrinsics; observer state belongs to the binary
status: operative for IO observation; the `(trace ...)` half is withdrawn
---

# 0040 — IO observation is an intrinsics callback contract; observer state belongs to the binary

This record is a citation anchor, not an authority. It retires when the
citations listed under [Retirement](#retirement) are repointed; nothing in it
is missing from the homes below.

## Ruling in force

- Intrinsics defines the IO-event taxonomy and one registration point. It holds
  no observer state and composes no diagnostics.
- The binary owns every consumer-side mechanism: ring buffers, the
  environment-variable filter, the panic hook, formatting and the dump.
- The binary registers its observer only when IO tracing is requested. With no
  observer registered, each trampoline emission site costs one relaxed atomic
  load and a branch, in every build mode including `--link`.
- The dependency edge is binary → intrinsics only. Intrinsics never names the
  binary's observer types; the binary maps the intrinsics taxonomy onto its own.

Current homes:

- [Intrinsics context](../bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics)
  — the registration point is in scope; observability state and diagnostics
  composition are out of scope.
- [Binary context](../bounded-contexts.md#6-binary-int-src-cratescranelisp-exe-bundle)
  — development tooling owns the observability ring buffers.
- Module rustdoc in `crates/cranelisp-intrinsics/src/io_observer.rs` — the
  exact registration, emission and threading contract.
- Module rustdoc in `src/io_trace.rs` — activation, taxonomy mapping and the
  host-allocator-only storage rule.

## Int hosting — observer state

The binary hosts the observer and its state in `src/io_trace.rs`. The heading
keeps the identity that module's rustdoc cites; the original section also
placed the `(trace ...)` runtime in the binary, and that part is withdrawn.

## Why observation stays out of intrinsics

Intrinsics' runtime semantics depend only on the running program
([Principle 01](../principles/01-decoupling-over-convenience.md)). Hosting
ring buffers, filters and formatters there made a development-tooling concern a
dependency of every linked executable. A callback slot keeps the production
cost to one load while the taxonomy stays with the trampoline that emits it
([Principle 02](../principles/02-narrow-interfaces.md)). Widening the
intrinsics context to admit diagnostics was considered and rejected for that
reason.

## Withdrawn half

The user withdrew the `(trace ...)` half on 2026-06-04. The record had made
`(trace ...)` a REPL/`--run`-only form, placed the trace runtime and its symbol
registration in the binary, and removed trace symbols from linked executables.
None of that is current:

- `(trace ...)` is available in every build mode
  ([spec 4.12.9](../../../spec/04-expressions.md#4129-build-mode-availability)).
- The trace runtime is an ordinary intrinsics family published through the
  catalog.
- [Execution tracing](../tracing.md) is the sole authority for the trace
  architecture. Do not reconstruct a mode restriction, a binary-hosted trace
  runtime or a link-time rejection from this record's Git history.

## Retirement

No content awaits extraction. The record deletes in the change that repoints:

| Citation | Repoint to |
|---|---|
| `src/io_trace.rs` module rustdoc, line 2 | the intrinsics and binary context links above |
| `crates/cranelisp-intrinsics/src/io_observer.rs` module rustdoc, line 1 ("per Decision 40") | no change needed; it already names the intrinsics context |
| `tests/s68_primitives_uniform.rs`, the `// spec:` block of `s68_trace_in_link_mode_rejected_at_link_time` | the spec 4.12.9 link above alone; the test's premise contradicts that section and is routed to `qa` |
| [Decision 43](0043-runtime-split-into-primitives-intrinsics.md) cross-reference to this file | the intrinsics context link above |
| [Label index](README.md) row 40 | the two BC links and [Execution tracing](../tracing.md) |
