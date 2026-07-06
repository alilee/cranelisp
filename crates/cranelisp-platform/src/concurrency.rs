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

pub use cranelisp_types::{Acquire, ConcurrencyDescriptor, Poll, ResourceRole};

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
    /// **v9 ctx-vtable — acquire a token permit** (`effect-concurrency.md` §4.1.1).
    /// A poll-fn projects a scheduling `token` from the handle it holds and calls
    /// this at the start of each poll (a `token == 0` commutative leaf omits it).
    /// `Acquire::Acquired` ⇒ a permit is held, proceed; `Acquire::Parked` ⇒ no permit
    /// free — the host enqueued `waker` on the token's permit-wait queue and the leaf
    /// returns `Poll::Pending` (backpressure). Idempotent per in-flight effect (the
    /// host keys held permits by the waker's identity), so a re-poll re-`acquire`s
    /// without double-counting. Release is **trampoline-owned** (on `Ready`/cancel) —
    /// there is deliberately NO `release` entry (cancel never re-enters the poll-fn).
    pub acquire: unsafe extern "C" fn(
        host: *const c_void,
        token: u64,
        capacity: u32,
        waker: *const Waker,
    ) -> Acquire,
    /// **v9 ctx-vtable — retire a token's scheduling identity** (a Retire/`close`
    /// leaf calls this after `close(r)`). Drops the token's permit pool and wakes any
    /// permit-waiters to observe the gone resource. Idempotent (`effect-concurrency.md`
    /// §4.1.1); a full-duplex handle's `close` retires both per-direction tokens.
    pub retire: unsafe extern "C" fn(host: *const c_void, token: u64),
    /// Opaque host reactor handle, passed back as `host` to each callback.
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

// ---------------------------------------------------------------------
// v9 ctx-vtable layout tier (FIXME 0501/0502)
//
// concurrency.rs is pure `#[repr(C)]` ABI: the load-bearing invariant is
// LAYOUT STABILITY (Principle 14 — a field reorder or size change silently
// breaks every platform DLL's GOT-indirect dispatch). The host<->platform
// vtable types (`HostCtx`, `Waker`, `WakerVTable`) have NO layout pins
// anywhere; these pin their size/offset/align across the v9 contract.
//
// The `acquire`/`retire` RUNTIME pairing (double-retire, use-after-retire
// under the debug tripwires) lives in the HOST reactor (`src/`/int), not in
// this crate — a platform declares the vtable *shape* but never implements
// it — so those cells are out-of-crate and are covered by the reactor's own
// tier. Here we pin the acquire/retire result-enum ABI + the role byte the
// `ConcurrencyDescriptor` carries. The descriptor/Poll layout pins live in
// `cranelisp_types::scheduling::tests` (cited, not duplicated).
// spec: design/arch/effect-concurrency.md §12 / §4.1.1 (the A2 ctx-vtable).
// ---------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::{align_of, offset_of, size_of};

    /// Pointer size on this target — every vtable field is pointer-sized.
    const PTR: usize = size_of::<*const c_void>();

    // layout: WakerVTable is four extern "C" fn pointers, contiguous, in order.
    #[test]
    fn waker_vtable_layout_is_four_contiguous_fn_ptrs() {
        assert_eq!(offset_of!(WakerVTable, wake), 0);
        assert_eq!(offset_of!(WakerVTable, wake_by_ref), PTR);
        assert_eq!(offset_of!(WakerVTable, clone), 2 * PTR);
        assert_eq!(offset_of!(WakerVTable, drop), 3 * PTR);
        assert_eq!(size_of::<WakerVTable>(), 4 * PTR);
        assert_eq!(align_of::<WakerVTable>(), PTR);
    }

    // layout: Waker is the (data, vtable) fat-pointer pair.
    #[test]
    fn waker_layout_is_data_then_vtable() {
        assert_eq!(offset_of!(Waker, data), 0);
        assert_eq!(offset_of!(Waker, vtable), PTR);
        assert_eq!(size_of::<Waker>(), 2 * PTR);
        assert_eq!(align_of::<Waker>(), PTR);
    }

    // layout / matrix: HostCtx is the six-slot v9 ctx-vtable in the documented
    // order — the three register_* callbacks, then acquire, then retire, then
    // the opaque host handle. A reorder breaks the C-ABI the host hands every
    // poll-fn.
    #[test]
    fn host_ctx_v9_vtable_layout_is_stable() {
        assert_eq!(offset_of!(HostCtx, register_readable), 0);
        assert_eq!(offset_of!(HostCtx, register_writable), PTR);
        assert_eq!(offset_of!(HostCtx, register_timer), 2 * PTR);
        assert_eq!(offset_of!(HostCtx, acquire), 3 * PTR);
        assert_eq!(offset_of!(HostCtx, retire), 4 * PTR);
        assert_eq!(offset_of!(HostCtx, host), 5 * PTR);
        assert_eq!(size_of::<HostCtx>(), 6 * PTR, "six pointer-sized slots");
        assert_eq!(align_of::<HostCtx>(), PTR);
    }

    // ABI: the acquire result enum crosses the C-ABI as a plain i32 with byte-
    // stable discriminants — `Acquired = 0` (proceed), `Parked = 1` (backpressure).
    // Untested elsewhere; it is the return of `HostCtx::acquire`.
    #[test]
    fn acquire_result_is_repr_i32_acquired_zero_parked_one() {
        assert_eq!(Acquire::Acquired as i32, 0);
        assert_eq!(Acquire::Parked as i32, 1);
        assert_eq!(size_of::<Acquire>(), size_of::<i32>());
    }

    // role byte: the per-effect leaf role rides one byte of ConcurrencyDescriptor
    // (§4.1.1). Its discriminants are the manifest fact E2 grounds on —
    // None/Produce/Consume/Retire = 0/1/2/3, `#[repr(u8)]`. The descriptor's
    // FIELD offsets are pinned in cranelisp_types::scheduling::tests; here we pin
    // the re-exported role byte's own discriminant values (unpinned there).
    #[test]
    fn resource_role_byte_discriminants_are_stable() {
        assert_eq!(ResourceRole::None as u8, 0);
        assert_eq!(ResourceRole::Produce as u8, 1);
        assert_eq!(ResourceRole::Consume as u8, 2);
        assert_eq!(ResourceRole::Retire as u8, 3);
        assert_eq!(size_of::<ResourceRole>(), 1);
    }

    // re-export identity: concurrency.rs's strongly-typed PollFn is the same
    // C-ABI shape as the type-crate PollFn — a conforming poll-fn coerces to it.
    // This pins that concurrency.rs re-projects, not redeclares, the contract.
    #[test]
    fn strongly_typed_poll_fn_coerces_a_conforming_leaf() {
        unsafe extern "C" fn leaf(
            _state: *mut c_void,
            _host: *const HostCtx,
            _waker: *const Waker,
        ) -> Poll {
            Poll::Ready
        }
        let _f: PollFn = leaf;
        // The projection's host pointers are pointer-sized (opaque in the type
        // crate, strongly typed here) — same C-ABI.
        assert_eq!(size_of::<*const HostCtx>(), PTR);
        assert_eq!(size_of::<*const Waker>(), PTR);
    }
}
