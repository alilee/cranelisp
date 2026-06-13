---
number: 0336
target: /int
filed_by: /qa
filed_at: 2026-06-13
sprint_filed: 81
refers_to: design/arch/fixmes/0021-io-trace-microbenchmark-harness.md, crates/cranelisp-intrinsics (record_event / io_observer), src/Cargo.toml ([[bin]]-only), design/backend/io-trampoline-trace.md §9 AC 2
status: open
---

# int: expose an in-process bench accessor for `record_event` (unblocks 0021)

## Issue

FIXME 0021 (io-trace off-path microbench) is blocked on a packaging fact: the
release-mode criterion bench it calls for must measure the `record_event`
filter-off cost at **nanosecond resolution, in-process**, against a no-op
baseline — to establish the `<1%` bound per `design/backend/io-trampoline-trace.md`
§9 AC 2.

The blocker: `cranelisp` (the `src/` crate) is **`[[bin]]`-only**. A `benches/`
criterion bench is a separate compilation unit that can only depend on a
crate's **library** target. With no `[lib]` target (and no `pub` benchmark
accessor) the bench cannot import `record_event` / the observability internals
to call them in-process.

A subprocess-driven measurement (spawn the binary, time it externally) was
considered and rejected by the prior assessment: process-spawn + I/O jitter
swamps the nanosecond signal, so it cannot meet the `<1%` AC. The measurement
must be in-process.

## Proposed resolution

`/int` provides ONE of:

1. **A `[lib]` target** for `src/` (alongside the existing `[[bin]]`) exposing
   the observability surface (`record_event` + whatever filter/registration
   state the off-path measurement needs) so a `benches/` criterion bench can
   link it; OR
2. **A narrow `pub` benchmark accessor** — a small, explicitly bench-only entry
   point (e.g. `pub fn bench_record_event_off_path(...)` behind a `bench`
   feature, or a thin re-export) that hands the bench an in-process handle to
   the filter-off `record_event` path without exposing the full session
   internals.

Either way the goal is: a release-mode criterion bench can call the filter-off
`record_event` path in-process, toggle `CRANELISP_IO_TRACE` on/off, and measure
the per-call cost at nanosecond resolution.

## Operational implication / Context

Once the accessor exists, the bench-relocation work is **/qa's** (0021 stays
`target: /qa`): author the criterion bench, establish the actual bound, and
tighten the integration-test ceiling in `tests/sprint61_observability_io.rs`.
0021 is updated to record that it is blocked on this FIXME (0336).
