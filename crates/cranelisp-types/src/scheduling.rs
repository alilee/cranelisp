//! Scheduling class for platform functions.
//!
//! `SchedulingClass` is plain manifest data attached to platform DLL
//! functions. It governs two things:
//!
//! 1. How `bind!` chains are compiled — sequential-chain vs. parallel-safe.
//! 2. How the IO trampoline schedules nodes during IO forcing.
//!
//! The type lives at the bottom of the dependency DAG (`cranelisp-types`)
//! so that it can appear both on `DefKind::PlatformEffect` (a sibling
//! variant on `ModuleEntry::Def.kind` — promoted from the retired
//! `PrimitiveKind::PlatformEffect` sub-discriminator per S69 Submission 36)
//! and in the platform-ABI surface
//! (`cranelisp-platform::PlatformFn::scheduling_class`) without forcing a
//! `cranelisp-types -> cranelisp-platform` dependency edge (which would
//! violate Principle 3 — `cranelisp-types` depends on nothing).
//!
//! `cranelisp-platform` re-exports this type as `cranelisp_platform::SchedulingClass`
//! so every existing consumer (platform DLLs, `declare_platform!` macro
//! users) continues to compile unchanged.

use serde::{Deserialize, Serialize};

/// Scheduling class for a platform function — declared in the platform manifest,
/// read by the IO trampoline and the `bind!` chain compiler.
///
/// **If unsure, choose `Sequential`**. It is the conservative class:
/// always correct, at the cost of foregoing parallelism. The other classes
/// are *optimizations* you opt into when you can prove the property holds.
///
/// Decision guide for platform authors:
///
/// - **Sequential** — the function touches shared mutable state visible across
///   calls (stdout, a global log, a shared file handle, a process-wide cache).
///   Two calls cannot be reordered or run in parallel without changing observable
///   behaviour. *Pick this if you are not sure.*
///
/// - **Commutative** — the function has no shared state across calls. Two calls
///   to the same function with different arguments are independent (HTTP GET to
///   different URLs, time queries, opening unrelated files). Safe to reorder
///   and to parallelize with other Commutative effects.
///
/// - **ResourceSerial** — the function carries a per-resource token (set via
///   `CLIO::effect_on_resource(token, ...)`). Calls with *different* tokens are
///   independent; calls with the *same* token must remain ordered. (e.g. writes
///   to per-connection sockets — independent across connections, ordered within.)
///
/// `Default::default()` returns `Sequential`. The variant discriminants
/// (`Sequential = 0`, `Commutative = 1`, `ResourceSerial = 2`) are the C-ABI
/// values carried in the platform manifest.
#[repr(u32)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum SchedulingClass {
    /// Always execute in order relative to other effects -- global shared resource
    /// (e.g. stdin, stdout, a global log). Never placed in a Par node.
    #[default]
    Sequential = 0,
    /// Fully independent -- no shared state between calls. Always safe to parallelize
    /// with other Commutative effects (e.g. HTTP requests, time queries, `open`).
    Commutative = 1,
    /// Parallel across different resource tokens; sequential within the same token.
    /// The platform function sets the token via `CLIO::effect_on_resource(token, ...)`.
    ResourceSerial = 2,
}

impl SchedulingClass {
    /// Convert a u32 discriminant to SchedulingClass, defaulting to Sequential on unknown values.
    pub fn from_u32(v: u32) -> Self {
        match v {
            1 => Self::Commutative,
            2 => Self::ResourceSerial,
            _ => Self::Sequential,
        }
    }
}

// ===========================================================================
// ABI-v7 concurrency contracts (effect-concurrency track, slice 2)
//
// These are the cross-crate *layout contracts* the slice-2 async substrate is
// built against. They are landed as code (the contract `/dev` implements next
// sprint/stretch) but gated behind the off-by-default `concurrency` feature so
// they enter neither the default build nor the `public-api.txt` frozen edge
// until the reactor implementation wires them (mirroring the `test-support`
// feature's out-of-baseline discipline). The default suite stays byte-identical.
//
// Manifestation: `design/arch/effect-concurrency.md` §5 (descriptor), §6
// (substrate), §12 (the A2 C-ABI-async leaf model); `design/arch/CLAUDE.md`
// notes the cascade. The descriptor generalizes `SchedulingClass` (above).
// ===========================================================================

/// The per-effect concurrency contract a platform declares in its manifest
/// (ABI v7) — a finite, declarative **generalization of [`SchedulingClass`]**
/// (`design/arch/effect-concurrency.md` §5).
///
/// `#[repr(C)]` layout contract: it crosses the platform-DLL C-ABI as raw bytes
/// in the v7 manifest entry (`cranelisp_platform::ConcurrentPlatformFn`), so its
/// layout is governed by `cranelisp_platform::ABI_VERSION` (Principle 14), **not**
/// by `#[non_exhaustive]` source-evolution guards. Deliberately **not**
/// `#[non_exhaustive]` — a layout contract evolves by an explicit ABI bump.
///
/// # Fields and their async-substrate mapping (§5 table)
///
/// - `token` — the conflict domain. Effects sharing a **non-zero** token serialize
///   on that token's `Semaphore`; `token == 0` is unrestricted (the `Commutative`
///   case — no conflict). This is the *static* conflict identity declared in the
///   manifest; a `ResourceSerial` effect additionally narrows to a *dynamic*
///   per-resource token at runtime (via `CLIO::effect_on_resource`).
/// - `cardinality` — permits available on `token` = the safe-parallelism / pool
///   size. `1` = serial within the token (today's `ResourceSerial`); `N` = a
///   bounded pool (the cardinality-N case you could not express before); `0` =
///   unbounded (`Commutative`).
/// - `global_budget` — **INERT until slice 4.** The optional cap on total in-flight
///   effects of this kind = the backpressure threshold. The slice-2 scheduler reads
///   only `0` (= no budget); any non-zero value is **reserved** and its abstraction
///   is the slice-4 decision (FIXME 0442). The field is present now **solely to
///   avoid a second ABI bump (7→8) when slice 4 lands** (sprint R5/§6).
/// - `blocking` — pool routing: `0` = a non-blocking poll leaf (routed to the host
///   reactor); `1` = a blocking effect (routed to the rayon / `spawn_blocking` pool).
///   The one genuinely **new** decision the descriptor drives (§7).
/// - `_reserved` — explicit tail padding to keep the `#[repr(C)]` size 8-byte
///   aligned and leave a named, zero-initialised slot for a future inert field
///   without a layout-disturbing insert. MUST be zero.
#[cfg(feature = "concurrency")]
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConcurrencyDescriptor {
    /// Conflict domain; `0` = unrestricted. Non-zero tokens share a semaphore.
    pub token: u64,
    /// Permits on `token` = safe parallelism / pool size. `1` = serial, `N` = pool, `0` = unbounded.
    pub cardinality: u32,
    /// INERT until slice 4 (backpressure). `0` = no budget; non-zero reserved (FIXME 0442).
    pub global_budget: u32,
    /// `0` = non-blocking poll leaf (reactor); `1` = blocking (rayon / spawn_blocking).
    pub blocking: u8,
    /// Reserved tail padding; MUST be zero. Keeps the layout stable for future inert fields.
    pub _reserved: [u8; 3],
}

#[cfg(feature = "concurrency")]
impl ConcurrencyDescriptor {
    /// The conservative migration bridge from a v6 [`SchedulingClass`] to a v7
    /// descriptor. Maps the three classes onto token/cardinality; `blocking` is
    /// **orthogonal** to scheduling class (a class says nothing about whether an
    /// effect blocks), so the bridge picks the conservative `blocking = 1`. A
    /// native v7 manifest declares `blocking` explicitly rather than relying on
    /// this default.
    pub const fn from_scheduling_class(c: SchedulingClass) -> Self {
        match c {
            // Globally ordered: one shared token, cardinality 1.
            SchedulingClass::Sequential => Self {
                token: 1,
                cardinality: 1,
                global_budget: 0,
                blocking: 1,
                _reserved: [0; 3],
            },
            // No shared state: unrestricted, unbounded parallelism.
            SchedulingClass::Commutative => Self {
                token: 0,
                cardinality: 0,
                global_budget: 0,
                blocking: 1,
                _reserved: [0; 3],
            },
            // Per-resource token (narrowed dynamically); serial within a token.
            SchedulingClass::ResourceSerial => Self {
                token: 0,
                cardinality: 1,
                global_budget: 0,
                blocking: 1,
                _reserved: [0; 3],
            },
        }
    }
}

/// C-ABI poll result (ABI v7) — the return of a poll-shape effect fn.
///
/// `#[repr(i32)]` so it crosses the C-ABI as a plain int (no niche assumptions).
/// It is the FFI collapse of `std::task::Poll`: `Ready` means the effect produced
/// its result (written through the effect's state / out-param); `Pending` means
/// the effect registered interest via the [`PollFn`]'s `HostCtx` waker and must be
/// re-polled when woken. Sync / non-blocking effects simply return `Ready`
/// immediately (§12 — blocking-style and poll-style coexist).
#[cfg(feature = "concurrency")]
#[repr(i32)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Poll {
    /// The effect completed; its result is available through the state object.
    Ready = 0,
    /// The effect would block; interest is registered, re-poll on wake.
    Pending = 1,
}

/// The ABI-v7 poll-fn signature shape — `poll(state, *HostCtx, *Waker) -> Poll`
/// (`design/arch/effect-concurrency.md` §12).
///
/// At the bottom of the dependency DAG `cranelisp-types` cannot name the host
/// reactor's `HostCtx` / `Waker` (those live in `cranelisp-platform`, which
/// depends on this crate — Principle 3 forbids the inverse edge). So the
/// type-crate shape uses opaque `*const c_void` for the two host pointers; the
/// platform crate re-projects this as a strongly-typed `cranelisp_platform::PollFn`
/// over its own `HostCtx` / `Waker`. Both describe the **same C-ABI**.
#[cfg(feature = "concurrency")]
pub type PollFn = unsafe extern "C" fn(
    state: *mut core::ffi::c_void,
    host_ctx: *const core::ffi::c_void,
    waker: *const core::ffi::c_void,
) -> Poll;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_is_sequential() {
        assert_eq!(SchedulingClass::default(), SchedulingClass::Sequential);
    }

    #[test]
    fn from_u32_maps_known_discriminants() {
        assert_eq!(SchedulingClass::from_u32(0), SchedulingClass::Sequential);
        assert_eq!(SchedulingClass::from_u32(1), SchedulingClass::Commutative);
        assert_eq!(SchedulingClass::from_u32(2), SchedulingClass::ResourceSerial);
        assert_eq!(SchedulingClass::from_u32(99), SchedulingClass::Sequential);
    }

    #[test]
    fn serde_roundtrip_preserves_variant() {
        for cls in [
            SchedulingClass::Sequential,
            SchedulingClass::Commutative,
            SchedulingClass::ResourceSerial,
        ] {
            let json = serde_json::to_string(&cls).expect("serialize");
            let rt: SchedulingClass = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(cls, rt);
        }
    }

    // Lane-liveness smoke for the `concurrency` feature test lane (FIXME 0449,
    // resolved by /arch S93 — `cargo nt-concurrency`). Proves a
    // `#[cfg(feature = "concurrency")]` test body actually EXECUTES under the
    // lane; without the lane these gated guards would be invisible coverage
    // under the canonical (feature-off) `cargo nt`. Deliberately shallow — the
    // substantive layout/bridge guards are the S93 §2B tests (/qa + /dev); this
    // only asserts the lane reaches a gated body and the gated `src` types
    // compile + construct.
    #[cfg(feature = "concurrency")]
    #[test]
    fn concurrency_lane_executes_gated_tests_smoke() {
        let d = ConcurrencyDescriptor::from_scheduling_class(SchedulingClass::Sequential);
        assert_eq!(d._reserved, [0u8; 3]);
    }

    // ======================================================================
    // S93 §2B — ABI-v7 dormant-contract guards (/qa, Phase-5 Stage-1).
    //
    // Gated `#[cfg(feature = "concurrency")]` so they compile out under the
    // canonical feature-off `cargo nt` and RUN only under `cargo nt-concurrency`
    // (FIXME 0449 lane, resolved /arch S93). They verify the LANDED v7 layout
    // contract — written against the dormant types `/arch` landed in Phase 3,
    // so they pass the moment the assertion matches the contract (the
    // dormant-contract guard the reactor implementation is built against).
    // ======================================================================

    // spec: design/arch/effect-concurrency.md §5 — the conservative v6→v7
    // bridge. `from_scheduling_class` maps the three scheduling classes onto the
    // descriptor's {token, cardinality, global_budget, blocking}; `_reserved`
    // MUST stay all-zero for every class (the inert tail).
    #[cfg(feature = "concurrency")]
    #[test]
    fn concurrency_descriptor_from_scheduling_class_bridges_three_classes() {
        let seq = ConcurrencyDescriptor::from_scheduling_class(SchedulingClass::Sequential);
        assert_eq!(seq.token, 1, "Sequential = one shared token");
        assert_eq!(seq.cardinality, 1, "Sequential = serial");
        assert_eq!(seq.global_budget, 0, "budget inert until slice 4");
        assert_eq!(seq.blocking, 1, "bridge is conservative: blocking");
        assert_eq!(seq._reserved, [0u8; 3]);

        let com = ConcurrencyDescriptor::from_scheduling_class(SchedulingClass::Commutative);
        assert_eq!(com.token, 0, "Commutative = unrestricted (no conflict)");
        assert_eq!(com.cardinality, 0, "Commutative = unbounded");
        assert_eq!(com.global_budget, 0);
        assert_eq!(com.blocking, 1);
        assert_eq!(com._reserved, [0u8; 3]);

        let rs = ConcurrencyDescriptor::from_scheduling_class(SchedulingClass::ResourceSerial);
        assert_eq!(rs.token, 0, "ResourceSerial token narrowed dynamically");
        assert_eq!(rs.cardinality, 1, "ResourceSerial = serial within a token");
        assert_eq!(rs.global_budget, 0);
        assert_eq!(rs.blocking, 1);
        assert_eq!(rs._reserved, [0u8; 3]);
    }

    // spec: design/arch/effect-concurrency.md §5 — the descriptor crosses the
    // platform-DLL C-ABI as raw bytes (`ConcurrentPlatformFn.concurrency`), so
    // its `#[repr(C)]` field offsets + size are a FROZEN v7 layout contract
    // (governed by ABI_VERSION, not source-evolution guards). The inert
    // `global_budget` slot MUST be present now (reserved to avoid a 7→8 bump
    // when slice 4 lands — SPRINT.md arch R5 / FIXME 0442).
    #[cfg(feature = "concurrency")]
    #[test]
    fn concurrency_descriptor_repr_c_layout_and_inert_budget_present() {
        use core::mem::{align_of, offset_of, size_of};
        assert_eq!(offset_of!(ConcurrencyDescriptor, token), 0);
        assert_eq!(offset_of!(ConcurrencyDescriptor, cardinality), 8);
        // The inert backpressure slot is present and at the frozen offset.
        assert_eq!(offset_of!(ConcurrencyDescriptor, global_budget), 12);
        assert_eq!(offset_of!(ConcurrencyDescriptor, blocking), 16);
        assert_eq!(offset_of!(ConcurrencyDescriptor, _reserved), 17);
        assert_eq!(align_of::<ConcurrencyDescriptor>(), 8);
        // 8 (token) + 4 (cardinality) + 4 (budget) + 1 (blocking) + 3 (_reserved)
        // = 20, rounded up to the 8-byte alignment = 24. The frozen v7 size.
        assert_eq!(size_of::<ConcurrencyDescriptor>(), 24);
    }

    // spec: design/arch/effect-concurrency.md §12 — `Poll` is the FFI collapse of
    // `std::task::Poll`, `#[repr(i32)]` so it crosses the C-ABI as a plain int.
    // The discriminants are byte-stable: Ready = 0, Pending = 1.
    #[cfg(feature = "concurrency")]
    #[test]
    fn poll_repr_i32_ready_zero_pending_one() {
        assert_eq!(Poll::Ready as i32, 0);
        assert_eq!(Poll::Pending as i32, 1);
        assert_eq!(core::mem::size_of::<Poll>(), core::mem::size_of::<i32>());
    }
}
