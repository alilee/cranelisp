---
number: 0132
target: /qa
filed_by: /qa
filed_at: 2026-05-04
sprint_filed: 64
refers_to: tests/legacy/sprint61_observability_scheduler.rs, tests/legacy/sprint61_observability_shared.rs
status: open
harvested_by: /dev int (S81 W-E)
---

## S81 W-E harvest (/dev int) — DONE for the int-side; remaining action is /qa deletion + e2e

The int-owned Rust-API observability assertions are ported into
`src/observability.rs` `#[cfg(test)] mod tests`:
- `harvest_scheduler_trace_env_var_name_is_stable` (env-var name contract)
- `harvest_trace_event_types_absent_from_boundary_crate_sources` (boundary-crate
  hygiene scan over types/frontend/typecheck)

The remaining Rust-API assertions of both legacy files (filter parse, ring-buffer
capacity/wrap, dump-clears, disabled/selective filter, shared-anchor stability,
cross-thread merge-sort monotonicity, thread_ord distinctness) were ALREADY
covered by the pre-existing `src/observability.rs` test cluster
(`parse_filter_*`, `ring_buffer_wraps_at_capacity`, `dump_clears_thread_buffer`,
`disabled_filter_suppresses_record`, `selective_filter_drops_non_matching`,
`anchor_is_the_shared_runtime_anchor`, `merge_sort_across_threads_is_monotonic`,
`thread_ord_ids_are_distinct_per_thread`) — not re-ported.

**NOT ported (route to /qa as integration/e2e):**
- The 3 subprocess tests (`scheduler_trace_subprocess_dump_contains_module_state_transitions`,
  `scheduler_trace_unset_means_no_dump_marker_on_stderr`,
  `scheduler_trace_subprocess_dump_has_multiple_event_types_under_all_filter`) —
  they launch the `cranelisp` binary with `CRANELISP_SCHEDULER_TRACE` set and
  parse the stderr dump. That is e2e (binary subprocess); it cannot be an int
  unit test and `tests/` is /qa-owned.
- The 2 cross-channel tests (`scheduler_and_io_trace_share_timestamp_domain`,
  `merge_across_both_logs_uses_shared_anchor_and_orderable_keys`) couple the int
  scheduler trace AND `cranelisp_runtime::io_trace` — two trace channels. The
  shared-anchor half is already covered int-side; the joint merge-sort property
  spans two crates and fits an e2e/runtime co-owned test better.

**Remaining action (/qa):** delete both legacy files, remove their README rows,
and (optionally) author the 3 subprocess + 2 cross-channel tests as e2e in
`tests/` if the `CRANELISP_SCHEDULER_TRACE` debugging surface warrants e2e
guarding. The runtime-side `observability_io`/`rc_alloc_trace` harvests (FIXMEs
0128/0129) remain `target: /runtime` and are out of int's scope.

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
