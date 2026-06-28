//! ABI-v7 host-reactor C-ABI — the one genuinely new designed artifact of the
//! effect-concurrency track (`design/arch/effect-concurrency.md` §12).
//!
//! The A2 model: **the host owns the reactor; platforms are C-ABI async
//! *leaves*.** A platform does the non-blocking syscall (it owns the *what*); on
//! `WouldBlock` it registers interest through a host-provided [`HostCtx`] vtable
//! + a C-ABI [`Waker`], and the host's single reactor (epoll / io_uring / kqueue)
//! owns the *when* and re-polls. The platform carries no runtime and never learns
//! an async concept.
//!
//! These are **layout contracts only** — landed as the v7 boundary `/dev`
//! implements next sprint/stretch, gated behind the off-by-default `concurrency`
//! feature so they enter neither the default build nor the `public-api.txt`
//! frozen edge (and so the v6 `PlatformFn` / `PlatformManifest` / `HostCallbacks`
//! field-order tables in `tests/facade_pif_rows.rs` stay green). Host
//! implementation of the reactor + the migration of `PlatformFn` →
//! [`ConcurrentPlatformFn`] is the slice-2 reactor work.
//!
//! `#[repr(C)]` layout governed by [`crate::ABI_VERSION`] (= 7), per Principle 14.
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
/// `drop_glue_ptr` runs the (optional) [`ConcurrentPlatformFn::drop_state`] hook —
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

/// The strongly-typed v7 poll-fn signature over this crate's [`HostCtx`] /
/// [`Waker`] — the projection of `cranelisp_types::PollFn` (which uses opaque
/// `c_void` for the host pointers because the type crate sits below this one in
/// the DAG). Both describe the **same C-ABI**.
pub type PollFn = unsafe extern "C" fn(
    state: *mut c_void,
    host: *const HostCtx,
    waker: *const Waker,
) -> Poll;

/// The ABI-v7 manifest function entry — the poll-shape successor to
/// [`crate::PlatformFn`].
///
/// Two layout changes from v6 `PlatformFn`:
/// 1. `ptr: *const u8` (a blocking `extern "C"` fn) becomes `poll: PollFn` (the
///    poll-shape async leaf). The GOT-indirect dispatch mechanism is unchanged —
///    only the *signature shape* the slot holds changes (§12).
/// 2. `scheduling_class: u32` is subsumed by `concurrency: ConcurrencyDescriptor`
///    (token + cardinality + global_budget + blocking generalize the three
///    scheduling classes — §5).
///
/// `jit_name` was already retired at ABI v3 (FIXME 0288); dispatch is GOT-indirect
/// against `__cranelisp_got_platform_<name>`, so there is nothing further to drop.
///
/// **S94 R1 — the ratified backend↔intrinsics node seam.** The host does NOT call
/// `poll` directly at the effect site; instead the backend's poll-construction arm
/// loads `poll` from the GOT and bakes it as the **code_ptr of a host-built
/// state-closure** (`[header | code_ptr=poll | drop_glue_ptr | env = result-slot +
/// i64 args + scratch]`), wrapped in a new `IO_TAG_EFFECT_POLL` node. The
/// trampoline's async Effect arm `.await`s an `EffectPoll` that calls
/// `poll(state=env, host, waker)`. This is why this entry carries `poll` +
/// (reserved) `drop_state` but NO `make_state` export: the host marshals args into
/// the closure env (the established closure-construction codegen), so state
/// construction stays host-internal. See `effect-concurrency.md` Appendix B
/// §"ratified backend↔intrinsics seam" + `platform-interface.md` §6.8.
///
/// This is landed as the contract; the migration of the `declare_platform!` macro
/// (emit poll-fns + descriptors) and the host loader (`manifest_to_descriptors`,
/// `got_slot` adoption) from `PlatformFn` to this shape is the slice-2 reactor
/// implementation. Field order is the v7 byte layout; it is **not yet frozen** (no
/// real cdylib has shipped against v7), so the reserved `drop_state` slot was
/// appended in place at S94 R1 with no `ABI_VERSION` bump.
#[repr(C)]
pub struct ConcurrentPlatformFn {
    /// Name as seen by cranelisp code (e.g. "read-line").
    pub name: *const u8,
    pub name_len: usize,
    /// The poll-shape effect fn. The manifest's order IS the GOT slot order
    /// (`platform-interface.md` §5.1); the host adopts `got_slot = manifest index`.
    pub poll: PollFn,
    /// The platform's optional state-teardown hook — the leaf's contribution to
    /// the host-built **state-closure**'s `drop_glue_ptr` (S94 R1 ratified seam,
    /// `effect-concurrency.md` Appendix B §"ratified backend↔intrinsics seam").
    ///
    /// **RESERVED-BUT-INERT until the cancellation slice** (≥ 7), in the exact
    /// reserve-now discipline as [`ConcurrencyDescriptor::global_budget`]: present
    /// now solely so the cancellation slice does not force a second ABI bump
    /// (7→8). The v7 contract is **not yet frozen** (no real cdylib has shipped
    /// against it), so this field is inserted **in place between [`poll`](Self::poll)
    /// and [`param_count`](Self::param_count)** in the still-dormant v7 layout —
    /// **no `ABI_VERSION` bump** (sprint S94 R1). The field-order guard
    /// `concurrent_platform_fn_repr_c_field_order_v7` pins this exact position.
    ///
    /// Why it exists: in the ratified closure-env node model the leaf's `state`
    /// rides the host-built state-closure env, whose `drop_glue_ptr` runs on the
    /// trampoline's existing `consume_io_tree` drop walk and frees the **RC'd
    /// captured args** (host-known). A leaf that allocates **platform-private
    /// heap** (a libc buffer, a connection struct — host-opaque) cannot be freed
    /// by host-generated glue; this export is the platform's hook the host bakes
    /// as (part of) the closure's `drop_glue_ptr`, consumed at node construction
    /// exactly as [`poll`](Self::poll) is. `None` (the C-ABI null fn-ptr) ⇒ the
    /// inline env suffices and host glue alone drops the node — the S94 in-tree
    /// demo's case. Cancellation (later slice) = the host ceases to poll + the
    /// node drops ⇒ this runs; the platform never truly blocks.
    pub drop_state: Option<unsafe extern "C" fn(state: *mut c_void)>,
    /// Number of i64 parameters.
    pub param_count: u32,
    /// Type signature as a fully-qualified S-expression string.
    pub type_sig: *const u8,
    pub type_sig_len: usize,
    /// Docstring for the function.
    pub docstring: *const u8,
    pub docstring_len: usize,
    /// Array of parameter-name pointers.
    pub param_names: *const *const u8,
    /// Array of parameter-name lengths (parallel to `param_names`).
    pub param_name_lens: *const usize,
    /// Number of parameter names.
    pub param_name_count: usize,
    /// The per-effect concurrency contract — generalizes v6 `scheduling_class`.
    pub concurrency: ConcurrencyDescriptor,
}

// Safety: same contract as `PlatformFn` — every pointer is read-only `'static`
// data (string-literal bytes / leaked descriptors) or a code pointer; none is
// mutated, and DLL pages stay mapped for the session (BC §5 invariant 6). The IO
// trampoline reads descriptors from multiple worker threads.
unsafe impl Send for ConcurrentPlatformFn {}
unsafe impl Sync for ConcurrentPlatformFn {}

/// The ABI-v7 **concurrent manifest** — the poll-shape successor to
/// [`crate::PlatformManifest`] (FIXME 0457, `platform-interface.md` §6.8).
///
/// A v7 platform that declares poll-shape effects exposes them through this
/// **separate** manifest type + a **separate** export symbol
/// (`cranelisp_concurrent_manifest`), deliberately NOT by reinterpreting the v6
/// `PlatformFn` array (that would break v6's byte-identical layout). It mirrors
/// [`crate::PlatformManifest`] field-for-field except `functions` points at a
/// [`ConcurrentPlatformFn`] array (poll-fns + per-fn [`ConcurrencyDescriptor`])
/// instead of a `PlatformFn` array.
///
/// The concurrency-built host (`src/platform.rs`) dlsym-probes
/// `cranelisp_concurrent_manifest` FIRST; on a hit it lifts the entries via
/// [`crate::concurrent_manifest_to_descriptors`]; on a miss it falls back to the
/// v6 `cranelisp_platform_manifest_<name>` path. v6 platforms + the default
/// (non-concurrency) host are untouched.
///
/// `#[repr(C)]` layout-contract type governed by [`crate::ABI_VERSION`] (= 7),
/// per Principle 14. Gated `#[cfg(feature = "concurrency")]` so it stays off the
/// default build + the frozen `public-api.txt` edge until the reactor wires it.
#[repr(C)]
pub struct ConcurrentPlatformManifest {
    /// Must match `cranelisp_platform::ABI_VERSION`.
    pub abi_version: u32,
    /// Platform name `(ptr, len)` — not NUL-terminated (same convention as
    /// [`crate::PlatformManifest`]).
    pub name: *const u8,
    pub name_len: usize,
    /// Platform version `(ptr, len)`.
    pub version: *const u8,
    pub version_len: usize,
    /// The poll-shape function entries. Manifest order IS GOT slot order
    /// (`platform-interface.md` §5.1); the host adopts `got_slot = manifest index`.
    pub functions: *const ConcurrentPlatformFn,
    pub function_count: usize,
}

// Safety: same contract as `PlatformManifest` — every pointer is read-only
// `'static` data or a code pointer; none is mutated, and DLL pages stay mapped
// for the session (BC §5 invariant 6).
unsafe impl Send for ConcurrentPlatformManifest {}
unsafe impl Sync for ConcurrentPlatformManifest {}
