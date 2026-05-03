---
number: 0128
target: /runtime
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/legacy/observability_io.rs
status: open
---

# Harvest tests/legacy/observability_io.rs into cranelisp-runtime io_trace unit tests

## Issue

The Sprint 64 test-port quarantined `tests/legacy/observability_io.rs`
(446 LOC, 7 tests). The file tests `cranelisp_runtime::io_trace::*`
internal API:

- `TrampolineEnter`, `TrampolineExit`, `PlatformEffect`, `BindEnter`,
  `ContPush`, `ContPop` event-type observation in stderr.
- Ring-buffer capacity bounds (`io_trace_ring_buffer_bounded_by_capacity`).
- Trace-event leakage check on cache `.meta.json` files.
- Off-path subprocess wall-clock ceiling under no-trace conditions.

These are Rust-internal observations of the trace channel. Three of
the seven tests resolved at Sprint 61 Wave 4 close (the
`io_trace_hello_io_*` cluster, fixed by `emit_capture_return_inc`).
The remaining four assert directly on
`cranelisp_runtime::io_trace::EventType` shapes and ring-buffer
capacity — pure internal observations.

## Proposed resolution

- `io_trace_hello_io_emits_full_trampoline_sequence`,
  `io_trace_hello_io_observes_core_sequential_event_types`,
  `io_trace_platformeffect_carries_scheduling_class_byte`: translate
  into `#[cfg(test)]` modules inside
  `crates/cranelisp-runtime/src/io_trace.rs` adjacent to the event-type
  emitter functions. Use `cranelisp_frontend::parse` +
  `build_program` + a programmatic trampoline driver if available; if
  not, retain a thin subprocess invocation but keep it as a unit test
  rather than an integration test (the trace API surface is what's
  under test, not language behaviour).
- `io_trace_unset_means_no_event_output_to_stderr`,
  `io_trace_event_types_absent_from_cache_meta_json`,
  `io_trace_ring_buffer_bounded_by_capacity`: translate into
  `crates/cranelisp-runtime/src/io_trace.rs` `#[cfg(test)]` modules
  using direct ring-buffer construction + drain.
- `io_trace_off_path_subprocess_completes_within_generous_ceiling`:
  this test is the harness-robustness ledger entry that fired only
  under concurrent nextest load. The new harness's per-test TempDir
  isolates subprocess invocations so that contention does not
  perturb wall-clock measurements. Two paths:
  1. **Delete** — the e2e form would no longer need this test; the
     individual `tests/spec_10_io.rs` IO tests run cleanly under
     concurrent nextest because each owns its TempDir.
  2. **Translate** as a runtime micro-benchmark guarding off-path
     trampoline overhead, parameterised by the spec ceiling
     (`design/backend/io-trampoline-trace.md §9 AC 2`). Belongs in
     `crates/cranelisp-runtime/benches/`, not unit tests.
  Recommend path 2 if the ceiling is load-bearing; path 1 otherwise.

Note on relocation: per FIXME 0103 + Decision 0040, `trace.rs` and
`io_trace.rs` may relocate from `cranelisp-runtime` to `src/int/` in
S65+. The harvest target follows the trace module's home at the time
of harvest.

When complete, delete `tests/legacy/observability_io.rs` and remove
its row from `tests/legacy/README.md`. Git history preserves
provenance.

## Operational implication / Context

This harvest is a coverage-preservation commitment from S64. None of
the assertions are user-observable spec coverage; they are
trace-channel surface assertions. Until harvest, the trace channel is
exercised indirectly by every IO test in `tests/spec_10_io.rs` (every
`--run` invocation that succeeds proves the trace doesn't crash the
binary). The taxonomy assertions matter when /runtime changes the
trace event shape and could regress tooling that reads stderr traces.
