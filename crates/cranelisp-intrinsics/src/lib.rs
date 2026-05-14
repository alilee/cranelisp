//! Cranelisp intrinsics — backend-emitted-call targets.
//!
//! Per facade `design/arch/facades/intrinsics.md` (Decision 43): backend-
//! emitted-call targets — runtime support code with stable ABI contracts
//! called by JIT-emitted code or by the IO trampoline. NOT callable from
//! user code; ABI tightly coupled to backend's codegen choices.
//!
//! ## Wave 3b-2d.1 status (FIXME 0150 source migration, intrinsics half)
//!
//! Wave 3b-1 (commit 9e4d9b1) relocated `io_observer.rs` + `io_trace.rs`
//! from `cranelisp-runtime` into this crate. Wave 3b-2d.1 (the present
//! commit) absorbs the remaining backend-emitted-call targets from
//! `cranelisp-runtime/src/`:
//!
//! | Source (former runtime) | Destination |
//! |---|---|
//! | `alloc.rs`  | `cranelisp_intrinsics::alloc`  — heap allocator, RC header layout |
//! | `drop.rs`   | `cranelisp_intrinsics::drop`   — consume_* drop-glue helpers |
//! | `rc.rs`     | `cranelisp_intrinsics::rc`     — RC trace + underflow check + consume_shallow |
//! | `panic.rs`  | `cranelisp_intrinsics::panic`  — `runtime/panic` for match-exhaustiveness |
//! | `ivar.rs`   | `cranelisp_intrinsics::ivar`   — IVar primitives (lenient eval) |
//! | `io.rs`     | `cranelisp_intrinsics::io`     — `cranelisp_run_io` IO trampoline |
//! | `vec.rs`    | `cranelisp_intrinsics::vec`    — Vec layout + ops (Cow + drop) |
//! | `string.rs` | `cranelisp_intrinsics::string` — HeapString layout + string ops |
//! | `trace.rs`  | `cranelisp_intrinsics::trace`  — `(trace ...)` GOT-swap support |
//!
//! `cranelisp-runtime` keeps thin re-export shims so existing consumers
//! (backend, int, exe-bundle, tests) continue to compile against
//! `cranelisp_runtime::*` paths unchanged. Runtime additionally still
//! hosts `marshal.rs` (`quote-sexp`, `sconcat`) and `primitives/` (user-
//! callable converters and operator wrappers) — those move to
//! `cranelisp-primitives` in β-2.
//!
//! Per Decision 43, the categorical line is: backend-emitted-call targets
//! (this crate) vs user-callable, symbol-table addressable primitives
//! (still in runtime; future `cranelisp-primitives`).

pub mod alloc;
pub mod drop;
pub mod io;
pub mod io_observer;
pub mod io_trace;
pub mod ivar;
pub mod panic;
pub mod rc;
pub mod string;
pub mod trace;
pub mod vec;

pub use io_observer::{IoEvent, IoEventTag, IoObserver, register_io_observer, trace_anchor};

// Public Rust API re-exports for ergonomic access by tests and consumers.
pub use alloc::{
    alloc_count, alloc_with_rc, bytes_allocated, bytes_current, bytes_peak,
    dealloc_count, heap_alloc, heap_alloc_payload, heap_dealloc, reset_counts,
};
#[cfg(debug_assertions)]
pub use alloc::is_live;
pub use panic::{runtime_panic, take_runtime_error};
pub use rc::{is_rc_trace_enabled, rc_underflow_check};
pub use string::{HeapString, alloc_string, heap_alloc_string, read_string_as_str, string_read};
pub use vec::{vec_drop, vec_len, vec_new, vec_push_copy, vec_push_grow, vec_set_copy};
pub use io::{cranelisp_run_io, run_io_trampoline};
pub use ivar::{ivar_create, ivar_force, ivar_spark};
pub use trace::{
    cranelisp_collect_trace, cranelisp_trace_children, cranelisp_trace_enter,
    cranelisp_trace_exit, cranelisp_trace_first_child_nanos, cranelisp_trace_format,
    cranelisp_trace_name, cranelisp_trace_nanos, cranelisp_trace_params,
    cranelisp_trace_restore_got, cranelisp_trace_result, cranelisp_trace_swap_got,
};
