//! Transitional shim — `io_trace.rs` content lives in
//! `cranelisp-intrinsics::io_trace` per FIXME 0103 Phase 1 (Sprint 66
//! Wave 3b-1, Decision 40). This module re-exports the relocated public
//! surface so existing consumers (runtime's own `io.rs`, int's
//! `src/main.rs`, exe-bundle, etc.) compile unchanged until they migrate
//! their `cranelisp_runtime::io_trace::*` imports to
//! `cranelisp_intrinsics::io_trace::*` in Wave 3b-2.
//!
//! At the broader D43 runtime split (FIXME 0150) this module disappears
//! along with the rest of `cranelisp-runtime`.

pub use cranelisp_intrinsics::io_trace::{
    IO_TRACE_BUFFER_CAPACITY, IoTraceEvent, IoTracePayload, IoTraceTag, FlushGuard, TraceFilter,
    dump_all_buffers, dump_thread_buffer, flush_to_stderr, format_event_line,
    install_panic_hook, publish_thread_buffer, record_event, trace_instant_anchor,
};
