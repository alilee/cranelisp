//! Cranelisp intrinsics — runtime-callable extern fns and IO observer host.
//!
//! Per facade `design/arch/facades/intrinsics.md`: this crate hosts the
//! IoObserver registration site (per FIXME 0103 / Decision 40) and the
//! relocated `io_trace.rs` thread-local ring-buffer infrastructure that
//! pre-Sprint-66 lived in `cranelisp-runtime`.
//!
//! ## Wave 3b-1 status (FIXME 0103 Phase 1)
//!
//! - `io_observer.rs` — NEW. `IoEvent`, `IoEventTag`, `IoObserver`,
//!   `register_io_observer`, `trace_anchor` per facade §"IO observation".
//! - `io_trace.rs` — physically relocated from `cranelisp-runtime` (the
//!   thread-local ring-buffer trace). Self-contained (no `crate::` deps).
//!   `cranelisp-runtime` keeps a thin `pub use cranelisp_intrinsics::io_trace::*`
//!   shim so existing consumers (`io.rs`, int, exe-bundle) compile
//!   unchanged.
//! - `trace.rs` — NOT yet relocated. It depends on `cranelisp_runtime::alloc`,
//!   `cranelisp_runtime::string`, `cranelisp_runtime::drop`,
//!   `cranelisp_runtime::rc`. Moving it without dragging those in would
//!   require a circular dep (intrinsics → runtime → intrinsics). It will
//!   migrate atomically with the broader D43 split in Wave 3b-2/3
//!   (FIXME 0150).
//!
//! ## Wave 3b-2 (next, FIXME 0103 Phase 2)
//!
//! The `int` agent migrates the ring-buffer + flush-guard machinery from
//! this crate's `io_trace.rs` into `src/io_trace/`, rewires runtime's
//! `io.rs` to emit through `io_observer::emit` instead of direct
//! `io_trace::record_event`, and registers an observer at int session
//! startup. Once that lands, `io_trace.rs` here can shrink to whatever
//! the trampoline still calls directly (likely nothing).

pub mod io_observer;
pub mod io_trace;

pub use io_observer::{IoEvent, IoEventTag, IoObserver, register_io_observer, trace_anchor};
