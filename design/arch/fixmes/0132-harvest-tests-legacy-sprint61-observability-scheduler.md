---
number: 0132
target: /int
filed_by: /qa
filed_at: 2026-05-04
sprint_filed: 64
refers_to: tests/legacy/sprint61_observability_scheduler.rs, tests/legacy/sprint61_observability_shared.rs
status: open
---

# Harvest tests/legacy/sprint61_observability_{scheduler,shared}.rs into src/ + cranelisp-runtime unit tests

## Issue

The Sprint 64 test-port quarantined two scheduler-observability files:

- `tests/legacy/sprint61_observability_scheduler.rs` (483 LOC, 9 tests) —
  exercises `cranelisp::observability::*` Rust API
  (`SchedulerTraceTag`, `SchedulerTracePayload`, `TraceFilter`,
  `parse_filter_from_env_value`, `record_module_event`,
  `dump_thread_buffer`, `dump_all_buffers`, `publish_thread_buffer`,
  `SCHEDULER_TRACE_BUFFER_CAPACITY`). Three subprocess tests use
  `CRANELISP_SCHEDULER_TRACE` end-to-end via stderr.

- `tests/legacy/sprint61_observability_shared.rs` (251 LOC, 3 tests) —
  cross-cutting invariants between scheduler trace and IO trace:
  `trace_instant_anchor()` returns the same `&'static Instant`; trace
  types do not appear in boundary-crate sources; merge-sort across both
  trace types is monotonic on `(timestamp, thread_ord_id)`.

Neither file has a direct e2e analogue. `CRANELISP_SCHEDULER_TRACE` is a
debugging aid like the other `CRANELISP_*_TRACE` env vars — not a spec'd
language behaviour.

## Proposed resolution

Per FIXMEs 0098 + 0103 + Decision 0040, `trace.rs` and `io_trace.rs` may
relocate from `cranelisp-runtime` to `src/` (with the runtime keeping
just the `IoObserver` callback contract). This harvest follows the trace
modules' home at the time of harvest.

### Scheduler file (9 tests)

- **Rust-API cluster** (6 tests) — translate into `#[cfg(test)]` modules
  inside the file that owns the trace data structures (likely
  `src/observability.rs` post-decomposition):
  - `scheduler_trace_filter_parse_is_pure_and_deterministic` —
    `parse_filter_from_env_value` test cases.
  - `scheduler_trace_events_have_monotonic_timestamps_within_each_thread`
    — drive thread-local buffer; assert non-decreasing timestamp.
  - `scheduler_trace_dump_merge_sorted_across_threads` — multi-thread
    drive + merge-sort assertion.
  - `scheduler_trace_filter_by_module_name_matches_only_that_module` /
    `_neg_other_modules_absent` — `TraceFilter::Selective` matcher
    behaviour.
  - `scheduler_trace_ring_buffer_capacity_matches_design` — capacity
    constant + FIFO wrap behaviour.

- **Subprocess cluster** (3 tests) — translate into integration tests
  inside the trace module's owning crate (one binary subprocess per
  test):
  - `scheduler_trace_subprocess_dump_contains_module_state_transitions`
  - `scheduler_trace_unset_means_no_dump_marker_on_stderr`
  - `scheduler_trace_subprocess_dump_has_multiple_event_types_under_all_filter`

### Shared file (3 tests)

- `scheduler_and_io_trace_share_timestamp_domain` — translate into a
  unit test alongside `trace_instant_anchor` (cranelisp-runtime if it
  remains there, or src/ post-relocation).
- `trace_event_types_do_not_appear_in_boundary_crate_sources` — this is
  a workspace-level lint, not a unit test. Either: (a) keep as a
  `#[cfg(test)]` filesystem walk in cranelisp-runtime (or whatever the
  trace's home is post-relocation); or (b) promote to a clippy-level
  custom lint or a CI grep job. Recommend (a) — minimal infra, runs in
  the standard test suite.
- `merge_across_both_logs_uses_shared_anchor_and_orderable_keys` —
  structural property of the trace data shapes; translate into a unit
  test alongside the trace types.

## Operational implication / Context

This harvest is a coverage-preservation commitment from S64. Until it
lands, both files are inert. Until then, the `CRANELISP_SCHEDULER_TRACE`
debugging surface is exercised manually by `/dev` work that uses the
trace; a regression would surface in that work's next debug session.

The two files share a single FIXME (this one) because they share an
owning crate (the trace modules' future home — `src/` per Decision 0040)
and a timeline. Splitting into separate FIXMEs would force two
near-identical resolution commits.

When complete, delete `tests/legacy/sprint61_observability_scheduler.rs`
and `tests/legacy/sprint61_observability_shared.rs` and remove their
rows from `tests/legacy/README.md`. Git history preserves provenance.
