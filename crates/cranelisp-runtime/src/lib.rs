//! cranelisp-runtime — transitional crate, mid-D43 migration.
//!
//! Per FIXME 0150 (Decision 43): `cranelisp-runtime` is being split into
//! `cranelisp-primitives` (user-callable, symbol-table addressable) and
//! `cranelisp-intrinsics` (backend-emitted-call targets). Wave 3b-1
//! relocated the IoObserver + io_trace; Wave 3b-2d.1 (current commit)
//! relocates the remaining backend-emitted-call targets (alloc, drop,
//! rc, panic, ivar, io, vec, string, trace) into `cranelisp-intrinsics`.
//!
//! What remains in this crate:
//! - `marshal` — `quote-sexp`, `sconcat` (user-callable Sexp marshaling).
//! - `primitives/{int,float,bool}` — conversion primitives + operator
//!   wrappers (`int-to-string`, `parse-int`, `float-to-string`,
//!   `bool-to-string`, `cranelisp_op_*`).
//! - `io_trace` — thin shim re-exporting from `cranelisp_intrinsics::io_trace`.
//! - Pre-existing re-exports of every relocated symbol, so consumers
//!   (backend, int, exe-bundle, integration tests) continue to compile
//!   against `cranelisp_runtime::*` paths.
//!
//! These remaining surfaces move to `cranelisp-primitives` in β-2 of
//! D43's sequencing; `cranelisp-runtime` then retires.

// Modules still hosted here (user-callable; future cranelisp-primitives).
pub mod marshal;
pub mod primitives;

// Thin shim re-exporting from cranelisp-intrinsics (Wave 3b-1).
pub mod io_trace;

// ────────────────────────────────────────────────────────────────────────────
// Submodule re-exports for relocated content. Each `pub use` makes the
// `cranelisp_runtime::<submod>::*` path resolve to `cranelisp_intrinsics`'s
// implementation. No new logic; pure forwarding.
// ────────────────────────────────────────────────────────────────────────────

pub use cranelisp_intrinsics::alloc;
pub use cranelisp_intrinsics::drop;
pub use cranelisp_intrinsics::io;
pub use cranelisp_intrinsics::ivar;
pub use cranelisp_intrinsics::panic;
pub use cranelisp_intrinsics::rc;
pub use cranelisp_intrinsics::string;
pub use cranelisp_intrinsics::trace;
pub use cranelisp_intrinsics::vec;

// ────────────────────────────────────────────────────────────────────────────
// Flat re-exports — preserved verbatim from the pre-relocation public API
// (per the public-api.txt baseline). Path resolves through the submodule
// re-exports above; both `cranelisp_runtime::heap_alloc` and
// `cranelisp_runtime::alloc::heap_alloc` continue to work.
// ────────────────────────────────────────────────────────────────────────────

// Runtime infrastructure (registered as runtime/alloc, runtime/dealloc, etc.)
pub use cranelisp_intrinsics::alloc::{heap_alloc, heap_alloc_payload, heap_dealloc};
pub use cranelisp_intrinsics::panic::runtime_panic;
pub use cranelisp_intrinsics::rc::rc_underflow_check;

// String infrastructure (registered as runtime/alloc_string, runtime/string_read)
pub use cranelisp_intrinsics::string::{heap_alloc_string, string_read};

// Vec runtime primitives.
pub use cranelisp_intrinsics::vec::{
    vec_drop, vec_len, vec_new, vec_push_copy, vec_push_grow, vec_set_copy,
};

// Extern primitives still hosted here (string side — moves to primitives in β-2).
pub use cranelisp_intrinsics::string::{
    str_char_at, str_concat, str_contains, str_ends_with, str_eq, str_join, str_len,
    str_replace, str_split, str_starts_with, str_substring, str_to_lower, str_to_upper,
    str_trim, string_identity,
};

// Conversion primitives (still in runtime; move to primitives in β-2).
pub use primitives::bool::bool_to_string;
pub use primitives::float::float_to_string;
pub use primitives::int::{
    cranelisp_op_add, cranelisp_op_div, cranelisp_op_eq, cranelisp_op_ge, cranelisp_op_gt,
    cranelisp_op_le, cranelisp_op_lt, cranelisp_op_mul, cranelisp_op_neq, cranelisp_op_sub,
    int_to_string, parse_int,
};

// Marshal primitives.
pub use marshal::{quote_sexp, sconcat};

// IO trampoline.
pub use cranelisp_intrinsics::io::{cranelisp_run_io, run_io_trampoline};

// IO trampoline event log (Sprint 61 Slice 0 observability) — relocated to
// intrinsics in Wave 3b-1. These flat re-exports preserve the pre-relocation
// names that `int`'s session startup and other consumers use.
pub use cranelisp_intrinsics::io_trace::{
    FlushGuard as IoTraceFlushGuard, IoTraceEvent, IoTracePayload, IoTraceTag, TraceFilter,
    dump_all_buffers as io_trace_dump_all_buffers,
    dump_thread_buffer as io_trace_dump_thread_buffer,
    flush_to_stderr as io_trace_flush_to_stderr,
    install_panic_hook as io_trace_install_panic_hook,
    publish_thread_buffer as io_trace_publish_thread_buffer,
    record_event as io_trace_record_event, trace_instant_anchor,
};

// IVar intrinsics for lenient evaluation.
pub use cranelisp_intrinsics::ivar::{ivar_create, ivar_force, ivar_spark};

// Trace runtime (registered as cranelisp_trace_*).
pub use cranelisp_intrinsics::trace::{
    cranelisp_collect_trace, cranelisp_trace_children, cranelisp_trace_enter,
    cranelisp_trace_exit, cranelisp_trace_first_child_nanos, cranelisp_trace_format,
    cranelisp_trace_name, cranelisp_trace_nanos, cranelisp_trace_params,
    cranelisp_trace_restore_got, cranelisp_trace_result, cranelisp_trace_swap_got,
};

// Public Rust API for tests + binary crate.
pub use cranelisp_intrinsics::alloc::{
    alloc_count, alloc_with_rc, bytes_allocated, bytes_current, bytes_peak,
    dealloc_count, reset_counts,
};
#[cfg(debug_assertions)]
pub use cranelisp_intrinsics::alloc::is_live;
pub use cranelisp_intrinsics::rc::is_rc_trace_enabled;
pub use cranelisp_intrinsics::string::{HeapString, alloc_string, read_string_as_str};
