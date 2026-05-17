---
number: 0207
target: /design (intrinsics)
filed_by: /dev (intrinsics)
filed_at: 2026-05-16
sprint_filed: 67
refers_to: design/arch/facades/intrinsics.md §"Trace functions (`trace::cranelisp_trace_*`)", design/arch/facades/intrinsics.md §"`io_trace::*`", design/arch/facades/intrinsics.md §"IO observation", crates/cranelisp-intrinsics/public-api.txt
status: open
---

# Delete §"Trace functions" + §"`io_trace::*`" from intrinsics facade

## Issue

Per Decision 40 (Path B1, amended 2026-05-16) and FIXME 0198 close
(this sprint), the following are gone from `cranelisp-intrinsics`:

- The 12 `cranelisp_trace_*` JIT-emitted-call functions (relocated to
  int `src/trace.rs` by FIXME 0202).
- The `consume_trace_call` per-type drop helper (relocated to int
  `src/trace.rs` by this FIXME — TraceCall ADT layout is owned by int).
- The entire `io_trace.rs` ring-buffer body: `record_event`,
  per-thread buffers, `TraceFilter` parser, `dump_*`, `flush_to_stderr`,
  `publish_thread_buffer`, `format_event_line`, `install_panic_hook`,
  `IoTraceFlushGuard`, `trace_instant_anchor`, `IO_TRACE_BUFFER_CAPACITY`,
  `IoTraceTag`, `IoTracePayload`, `IoTraceEvent` (all relocated to int
  `src/io_trace.rs` by FIXME 0202).

The post-deletion intrinsics surface for trace/io observation is the
~50-line `IoObserver` extension-point contract on `io_observer.rs`:
`register_io_observer`, `emit`, `trace_anchor`, `IoEvent`, `IoEventTag`,
`IoObserver` — already documented in §"IO observation" (which stays
current).

The facade still carries the pre-deletion sections marked
"RELOCATING TO `int` IN S67 WAVE 4". Post-Wave-4, those sections have
no referent and need to delete.

## Proposed resolution

In `design/arch/facades/intrinsics.md`:

1. Delete §"Trace functions (`trace::cranelisp_trace_*`)" in full.
2. Delete §"`io_trace::*`" in full.
3. Delete the §"Drop glue" entry for `consume_trace_call` (or rewrite
   that section's TraceCall mention as a pointer to int's `src/trace.rs`
   if reviewers prefer narrative continuity).
4. Verify §"IO observation (extension point)" remains current and is
   self-sufficient — it already describes the surviving surface.

After the facade edit, the facade compliance test
(`tests/facade_compliance.rs`) and `tests/facade_pif_rows.rs::row_30`
+ `row_33` continue to pass against the regenerated baseline
(`crates/cranelisp-intrinsics/public-api.txt`, 248 lines as of
this commit; the trace + io_trace + `consume_trace_call` entries are
gone).

## Operational implication / Context

The deletion is mechanical — the source-side relocation has landed and
the baseline has been regenerated. The facade is the last document
that still refers to the pre-relocation shape.

`facades/intrinsics.md` §"Module inventory" table also needs to drop
the `trace` and `io_trace` rows; `crates/cranelisp-intrinsics/src/lib.rs`
top-of-file inventory is already updated and can serve as the source
of truth.
