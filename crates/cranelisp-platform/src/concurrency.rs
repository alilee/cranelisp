//! Host-reactor C-ABI — the one genuinely new designed artifact of the
//! effect-concurrency track (`design/arch/effect-concurrency.md` §12). Under the
//! single-ABI cutover (`platform-interface.md` §6.8.0) these types are CORE
//! (ungated) at [`crate::ABI_VERSION`] = 8.
//!
//! The A2 model: **the host owns the reactor; platforms are C-ABI async
//! *leaves*.** A platform does the non-blocking syscall (it owns the *what*); on
//! `WouldBlock` it registers interest through a host-provided [`HostCtx`] vtable
//! and a C-ABI [`Waker`], and the host's single reactor (epoll / io_uring /
//! kqueue) owns the *when* and re-polls. The platform carries no runtime and
//! never learns an async concept.
//!
//! Under the single-ABI cutover (`design/arch/platform-interface.md` §6.8.0)
//! these host-reactor ABI types are **CORE (ungated)** — the unified
//! [`crate::PlatformFn`] carries a [`ConcurrencyDescriptor`] for every effect, and
//! any platform may declare a poll-shape leaf whose [`PollFn`] the host reactor
//! drives. The former dual-channel `ConcurrentPlatformFn` /
//! `ConcurrentPlatformManifest` are **deleted** (absorbed into the unified
//! `PlatformFn` / `PlatformManifest`).
//!
//! `#[repr(C)]` layout governed by [`crate::ABI_VERSION`] (= 8), per Principle 14.
//! None of these types is `#[non_exhaustive]`: a layout contract evolves by an
//! explicit ABI bump, not by source-evolution guards.

use core::ffi::c_void;

pub use cranelisp_types::{ConcurrencyDescriptor, Poll};

/// The C-ABI projection of `std::task::RawWakerVTable` — four `extern "C"`
/// function pointers over the waker's opaque `data`.
#[repr(C)]
pub struct WakerVTable {
    /// Wake the strand, consuming the waker (the host reactor calls this when the
    /// registered fd / timer fires).
    pub wake: unsafe extern "C" fn(data: *const c_void),
    /// Wake the strand without consuming the waker.
    pub wake_by_ref: unsafe extern "C" fn(data: *const c_void),
    /// Clone the waker (the platform may stash a clone to wake itself later).
    pub clone: unsafe extern "C" fn(data: *const c_void) -> Waker,
    /// Drop the waker's `data`.
    pub drop: unsafe extern "C" fn(data: *const c_void),
}

/// The C-ABI projection of `std::task::Waker` — a `(data, vtable)` fat-pointer
/// pair the platform calls (or hands to a [`HostCtx`] `register_*`) to ask the
/// host reactor to re-poll the suspended effect when its fd / timer is ready.
#[repr(C)]
pub struct Waker {
    /// Opaque waker payload, passed back to each [`WakerVTable`] callback.
    pub data: *const c_void,
    /// The waker's vtable.
    pub vtable: *const WakerVTable,
}

/// The host-provided reactor vtable handed to every poll-fn call. On `WouldBlock`
/// a platform registers interest through one of the `register_*` callbacks,
/// supplying the [`Waker`] the host reactor will fire when the resource is ready.
///
/// "Platforms own the *what*; the host owns the *when*" (§12). Cancellation is the
/// host simply ceasing to poll + dropping the effect node, whose state-closure
/// `drop_glue_ptr` runs the (optional) [`crate::PlatformFn::drop_state`] hook —
/// the platform never truly blocks, so nothing is ever stuck inside a syscall.
#[repr(C)]
pub struct HostCtx {
    /// Register read-readiness on a raw fd; the reactor wakes `waker` when readable.
    pub register_readable:
        unsafe extern "C" fn(host: *const c_void, fd: i32, waker: *const Waker),
    /// Register write-readiness on a raw fd; the reactor wakes `waker` when writable.
    pub register_writable:
        unsafe extern "C" fn(host: *const c_void, fd: i32, waker: *const Waker),
    /// Register a timer; the reactor wakes `waker` at `deadline_nanos` (monotonic).
    pub register_timer:
        unsafe extern "C" fn(host: *const c_void, deadline_nanos: u64, waker: *const Waker),
    /// Opaque host reactor handle, passed back as `host` to each `register_*`.
    pub host: *const c_void,
}

/// The strongly-typed poll-fn signature over this crate's [`HostCtx`] /
/// [`Waker`] — the projection of `cranelisp_types::PollFn` (which uses opaque
/// `c_void` for the host pointers because the type crate sits below this one in
/// the DAG). Both describe the **same C-ABI**.
pub type PollFn = unsafe extern "C" fn(
    state: *mut c_void,
    host: *const HostCtx,
    waker: *const Waker,
) -> Poll;
// ---------------------------------------------------------------------
// Historical note (single-ABI cutover, §6.8.0): `ConcurrentPlatformFn` and
// `ConcurrentPlatformManifest` were DELETED here — the unified `crate::PlatformFn`
// / `crate::PlatformManifest` carry both blocking and poll-shape effects natively
// (each effect's shape is `concurrency.blocking`). The reserved `drop_state`
// poll-leaf teardown hook moved onto `crate::PlatformFn`.
// ---------------------------------------------------------------------
