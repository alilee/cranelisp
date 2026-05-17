//! Cranelisp intrinsics — backend-emitted-call targets.
//!
//! Per facade `design/arch/facades/intrinsics.md` (Decision 43): backend-
//! emitted-call targets — runtime support code with stable ABI contracts
//! called by JIT-emitted code or by the IO trampoline. NOT callable from
//! user code; ABI tightly coupled to backend's codegen choices.
//!
//! ## Sprint 67 Wave 3 — FIXME 0180 close (string/vec relocation)
//!
//! The user-callable string operations (15 fns: `str-concat`, `str-len`, …)
//! and `vec-len` physically lived here until Sprint 67 Wave 3. They have
//! now been lifted into `cranelisp-primitives::{string, vec}` per Decision 43
//! and `design/arch/facades/primitives.md`. The backend-emitted-call
//! infrastructure remains here under renamed modules:
//!
//! | Was | Now | Why |
//! |---|---|---|
//! | `cranelisp_intrinsics::string::*` | `cranelisp_intrinsics::heap_string::*` | Avoid public-api confusion with `cranelisp_primitives::string` |
//! | `cranelisp_intrinsics::vec::*`    | `cranelisp_intrinsics::vec_runtime::*` | Same reasoning for the Vec runtime helpers |
//!
//! ## Sprint 67 Wave 4 — FIXMEs 0198 + 0202 (trace relocation)
//!
//! Per Decision 40 (Path B1, amended 2026-05-16), `(trace ...)` is a
//! REPL/`--run`-only special form. The 12 `cranelisp_trace_*` JIT-emitted-
//! call function bodies, the trace stack + GOT-swap machinery, the
//! io_trace ring buffer + dump + panic-hook infrastructure, and the
//! TraceCall ADT consumer (`consume_trace_call`) have all relocated to
//! int (`src/trace.rs` + `src/io_trace.rs`). The surviving intrinsics
//! surface is the IoObserver extension point on `io_observer.rs` —
//! registration API + IoEvent/IoEventTag callback contract + the
//! `trace_anchor` instant.
//!
//! ## Module inventory (post-FIXME-0198)
//!
//! | Module | Role |
//! |---|---|
//! | `alloc`        | Heap allocator, RC header layout |
//! | `drop`         | `consume_*` drop-glue helpers (Sexp/SList/Vec/IO/closure) |
//! | `io`           | `cranelisp_run_io` IO trampoline |
//! | `io_observer`  | IoObserver registration + `IoEvent`/`IoEventTag` + `trace_anchor` |
//! | `ivar`         | IVar primitives (lenient eval) |
//! | `panic`        | `runtime/panic` for match-exhaustiveness |
//! | `rc`           | RC trace + underflow check + consume_shallow |
//! | `heap_string`  | HeapString layout + alloc/read helpers |
//! | `vec_runtime`  | Vec layout + ops (Cow + drop) |

pub mod alloc;
pub mod drop;
pub mod heap_string;
pub mod io;
pub mod io_observer;
pub mod ivar;
pub mod panic;
pub mod rc;
pub mod vec_runtime;

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
pub use io::{cranelisp_run_io, run_io_trampoline};
pub use ivar::{ivar_create, ivar_force, ivar_spark};
