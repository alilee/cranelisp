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
//! and in the platform-ABI surface (derived onto the host-side
//! `cranelisp-platform::OwnedPlatformFnDescriptor::scheduling_class` from the
//! unified `PlatformFn::concurrency` — the single-ABI cutover removed the former
//! standalone `PlatformFn::scheduling_class` field) without forcing a
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
// Unified-ABI concurrency contracts (effect-concurrency track) — ABI v8
//
// These are the cross-crate *layout contracts* of the single platform ABI. As of
// the S96 single-ABI cutover (`design/arch/platform-interface.md` §6.8) they are
// **core, ungated** surface: there is ONE platform ABI in which each effect is
// independently blocking or poll-shape via its `ConcurrencyDescriptor`. The former
// off-by-default `concurrency` feature (which kept these dormant + off the frozen
// `public-api.txt` edge while v6 coexistence was preserved) is RETIRED — there are
// no out-of-tree v6 DLLs to preserve compatibility with, so the descriptor is part
// of every platform manifest entry. The host *reactor* that drives poll-shape
// leaves stays optional behind `cranelisp-intrinsics`'s `concurrency-runtime`
// feature (mio/futures); these ABI *types* do not.
//
// Manifestation: `design/arch/platform-interface.md` §6.8 (the single-ABI
// cutover) + `design/arch/effect-concurrency.md` §5 (descriptor), §12 (the A2
// C-ABI-async leaf model). The descriptor generalizes `SchedulingClass` (above):
// a blocking effect's descriptor is synthesized from its `SchedulingClass` via
// `from_scheduling_class`; a poll-shape effect declares its descriptor natively.
// ===========================================================================

/// Per-EFFECT static leaf **role** — a compile-time manifest fact (ABI v9,
/// `effect-concurrency.md` §4.1.1 / `platform-interface.md` §6.8.0b). It grounds
/// inference E2 (a Produce leaf mints a fresh resource ⇒ a fresh disjoint token) and
/// documents the leaf for the platform-writer's guide. **The trampoline does NOT branch
/// on `role` at runtime** — there is no stamp/read; the platform poll-fn does ALL
/// runtime scheduling via the `ctx` vtable (`acquire`/`register_*`/`retire`).
///
/// `#[repr(u8)]`: it rides one byte of `ConcurrencyDescriptor` (the former `_reserved`
/// tail), so its layout is governed by `cranelisp_platform::ABI_VERSION` (Principle 14),
/// not source-evolution guards. `Default` is `None` (the zero discriminant), so a
/// zero-initialised descriptor reads `role: None`.
#[repr(u8)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum ResourceRole {
    /// The effect neither produces nor consumes a scheduling resource (a tokenless /
    /// `Commutative` leaf — a bare timer, a fire-and-forget log, `bind-listener`, `sleep`).
    #[default]
    None = 0,
    /// The effect **mints** a resource handle whose later use is admission-controlled
    /// (`open` / `accept` / `connect`): it drives `acquire`/`register` on the
    /// establishment resource and, at `Ready`, mints the handle ADT carrying the new `r`.
    Produce = 1,
    /// The effect **operates on** a previously-produced handle and serializes within that
    /// resource (`read` / `write` / `send`): it reads `r` off the handle's genuine field,
    /// projects the token, and `ctx.acquire`s it.
    Consume = 2,
    /// The effect **ends** a resource's scheduling identity (`close`): `close(r)` +
    /// `ctx.retire(token)` for each of the resource's tokens.
    Retire = 3,
}

/// C-ABI result of a token-permit acquisition the platform poll-fn requests via the
/// `ctx` vtable's `acquire` (ABI v9, `effect-concurrency.md` §4.1.1). `Acquired` ⇒ a
/// permit is held (proceed); `Parked` ⇒ no permit free — the host enqueued the waker on
/// the token's permit-wait queue and the leaf returns `Pending` (backpressure). The host
/// keys held permits by the in-flight effect's identity, so `acquire` is idempotent per
/// effect (a re-poll re-`acquire`s without double-counting). Release is trampoline-owned
/// (on `Ready`/cancel) — there is no `release` vtable entry.
///
/// `#[repr(i32)]` so it crosses the C-ABI as a plain int. Re-exported by
/// `cranelisp_platform`; the `HostCtx::acquire` fn-pointer returns it.
#[repr(i32)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Acquire {
    /// A permit on the token is held; the leaf proceeds with its syscall.
    Acquired = 0,
    /// No permit free; the waker is enqueued — the leaf returns `Pending`.
    Parked = 1,
}

/// The per-effect concurrency contract a platform declares in its manifest
/// (the unified single-ABI platform contract, `platform-interface.md` §6.8.0) —
/// a finite, declarative **generalization of [`SchedulingClass`]**
/// (`design/arch/effect-concurrency.md` §5).
///
/// `#[repr(C)]` layout contract: it crosses the platform-DLL C-ABI as raw bytes
/// in the unified manifest entry (`cranelisp_platform::PlatformFn::concurrency`),
/// so its layout is governed by `cranelisp_platform::ABI_VERSION` (Principle 14), **not**
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
    /// The per-effect static leaf **role** (`None`/`Produce`/`Consume`/`Retire`) — a
    /// compile-time manifest fact grounding inference E2 + documenting the leaf for the
    /// platform-writer's guide (ABI v9, `effect-concurrency.md` §4.1.1). The trampoline
    /// does NOT branch on it at runtime — the poll-fn does all scheduling via the `ctx`
    /// vtable (`acquire`/`register_*`/`retire`). Consumes one byte of the former
    /// `_reserved: [u8; 3]` tail; existing field offsets + the struct size are unchanged.
    pub role: ResourceRole,
    /// Reserved tail padding; MUST be zero. Keeps the layout stable for future inert fields.
    pub _reserved: [u8; 2],
}

impl ConcurrencyDescriptor {
    /// Synthesize a **blocking** effect's descriptor from its [`SchedulingClass`]
    /// — the canonical sugar the unified `declare_platform!` macro uses to lower a
    /// blocking effect declared with `scheduling:` rather than a full `descriptor:`.
    /// Maps the three classes onto token/cardinality; `blocking` is **orthogonal**
    /// to scheduling class (a class says nothing about whether an effect blocks),
    /// so a blocking effect's synthesized descriptor sets `blocking = 1`. A
    /// poll-shape effect declares its descriptor natively (`blocking = 0`) and does
    /// not use this. (Formerly the v6→v7 compat bridge; under the single ABI it is
    /// the blocking-effect descriptor sugar — `platform-interface.md` §6.8.)
    pub const fn from_scheduling_class(c: SchedulingClass) -> Self {
        match c {
            // Globally ordered: one shared token, cardinality 1.
            SchedulingClass::Sequential => Self {
                token: 1,
                cardinality: 1,
                global_budget: 0,
                blocking: 1,
                role: ResourceRole::None,
                _reserved: [0; 2],
            },
            // No shared state: unrestricted, unbounded parallelism.
            SchedulingClass::Commutative => Self {
                token: 0,
                cardinality: 0,
                global_budget: 0,
                blocking: 1,
                role: ResourceRole::None,
                _reserved: [0; 2],
            },
            // Per-resource token (narrowed dynamically); serial within a token.
            SchedulingClass::ResourceSerial => Self {
                token: 0,
                cardinality: 1,
                global_budget: 0,
                blocking: 1,
                role: ResourceRole::None,
                _reserved: [0; 2],
            },
        }
    }

    /// Best-effort inverse of [`from_scheduling_class`](Self::from_scheduling_class):
    /// map a descriptor's `token`/`cardinality` conflict-domain axis onto the
    /// nearest [`SchedulingClass`]. The host still carries `scheduling_class` on
    /// `DefKind::PlatformEffect` (the conflict-domain axis, orthogonal to the
    /// `poll_shape` dispatch axis), so the v7 loader derives it from the lifted
    /// descriptor through this map (FIXME 0457; `platform-interface.md` §6.8).
    ///
    /// `blocking` is deliberately ignored — it is the orthogonal dispatch axis,
    /// carried separately as `poll_shape`, and says nothing about conflict domain.
    /// The map is the inverse of the three `from_scheduling_class` images, with a
    /// conservative default for shapes those images do not cover (a native
    /// cardinality-N pool ⇒ `Commutative`, the closest unbounded-parallel class):
    ///
    /// - `token != 0`              ⇒ `Sequential`    (a shared conflict domain)
    /// - `token == 0, cardinality == 0` ⇒ `Commutative`   (unbounded, no conflict)
    /// - `token == 0, cardinality == 1` ⇒ `ResourceSerial` (serial within a token)
    /// - `token == 0, cardinality >= 2` ⇒ `Commutative`   (bounded pool — nearest)
    pub const fn nearest_scheduling_class(&self) -> SchedulingClass {
        if self.token != 0 {
            SchedulingClass::Sequential
        } else if self.cardinality == 0 {
            SchedulingClass::Commutative
        } else if self.cardinality == 1 {
            SchedulingClass::ResourceSerial
        } else {
            SchedulingClass::Commutative
        }
    }
}

/// C-ABI poll result (the unified platform ABI) — the return of a poll-shape effect fn.
///
/// `#[repr(i32)]` so it crosses the C-ABI as a plain int (no niche assumptions).
/// It is the FFI collapse of `std::task::Poll`: `Ready` means the effect produced
/// its result (written through the effect's state / out-param); `Pending` means
/// the effect registered interest via the [`PollFn`]'s `HostCtx` waker and must be
/// re-polled when woken. Sync / non-blocking effects simply return `Ready`
/// immediately (§12 — blocking-style and poll-style coexist).
#[repr(i32)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Poll {
    /// The effect completed; its result is available through the state object.
    Ready = 0,
    /// The effect would block; interest is registered, re-poll on wake.
    Pending = 1,
}

/// The poll-fn signature shape — `poll(state, *HostCtx, *Waker) -> Poll`
/// (`design/arch/effect-concurrency.md` §12).
///
/// At the bottom of the dependency DAG `cranelisp-types` cannot name the host
/// reactor's `HostCtx` / `Waker` (those live in `cranelisp-platform`, which
/// depends on this crate — Principle 3 forbids the inverse edge). So the
/// type-crate shape uses opaque `*const c_void` for the two host pointers; the
/// platform crate re-projects this as a strongly-typed `cranelisp_platform::PollFn`
/// over its own `HostCtx` / `Waker`. Both describe the **same C-ABI**.
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
        assert_eq!(
            SchedulingClass::from_u32(2),
            SchedulingClass::ResourceSerial
        );
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
    #[test]
    fn concurrency_lane_executes_gated_tests_smoke() {
        let d = ConcurrencyDescriptor::from_scheduling_class(SchedulingClass::Sequential);
        assert_eq!(d.role, ResourceRole::None);
        assert_eq!(d._reserved, [0u8; 2]);
    }

    // spec: design/arch/platform-interface.md §6.8 (FIXME 0457) —
    // `nearest_scheduling_class` is the best-effort inverse of
    // `from_scheduling_class` (token/cardinality → nearest class), the v7
    // loader's derivation of the still-required `scheduling_class`. Round-trips
    // the three canonical images; ignores `blocking` (the orthogonal axis); maps
    // a cardinality-N pool to the nearest unbounded-parallel class.
    #[test]
    fn nearest_scheduling_class_inverts_from_scheduling_class() {
        for cls in [
            SchedulingClass::Sequential,
            SchedulingClass::Commutative,
            SchedulingClass::ResourceSerial,
        ] {
            let d = ConcurrencyDescriptor::from_scheduling_class(cls);
            assert_eq!(
                d.nearest_scheduling_class(),
                cls,
                "round-trip must recover the source class for {cls:?}"
            );
        }
        // `blocking` is ignored — a poll-shape (blocking == 0) Commutative-shaped
        // descriptor still maps to Commutative.
        let poll = ConcurrencyDescriptor {
            token: 0,
            cardinality: 0,
            global_budget: 0,
            blocking: 0,
            role: ResourceRole::None,
            _reserved: [0; 2],
        };
        assert_eq!(
            poll.nearest_scheduling_class(),
            SchedulingClass::Commutative
        );
        // A native cardinality-N pool maps to the nearest unbounded class.
        let pool = ConcurrencyDescriptor {
            token: 0,
            cardinality: 4,
            global_budget: 0,
            blocking: 0,
            role: ResourceRole::None,
            _reserved: [0; 2],
        };
        assert_eq!(
            pool.nearest_scheduling_class(),
            SchedulingClass::Commutative
        );
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
    #[test]
    fn concurrency_descriptor_from_scheduling_class_bridges_three_classes() {
        let seq = ConcurrencyDescriptor::from_scheduling_class(SchedulingClass::Sequential);
        assert_eq!(seq.token, 1, "Sequential = one shared token");
        assert_eq!(seq.cardinality, 1, "Sequential = serial");
        assert_eq!(seq.global_budget, 0, "budget inert until slice 4");
        assert_eq!(seq.blocking, 1, "bridge is conservative: blocking");
        assert_eq!(seq.role, ResourceRole::None);
        assert_eq!(seq._reserved, [0u8; 2]);

        let com = ConcurrencyDescriptor::from_scheduling_class(SchedulingClass::Commutative);
        assert_eq!(com.token, 0, "Commutative = unrestricted (no conflict)");
        assert_eq!(com.cardinality, 0, "Commutative = unbounded");
        assert_eq!(com.global_budget, 0);
        assert_eq!(com.blocking, 1);
        assert_eq!(com.role, ResourceRole::None);
        assert_eq!(com._reserved, [0u8; 2]);

        let rs = ConcurrencyDescriptor::from_scheduling_class(SchedulingClass::ResourceSerial);
        assert_eq!(rs.token, 0, "ResourceSerial token narrowed dynamically");
        assert_eq!(rs.cardinality, 1, "ResourceSerial = serial within a token");
        assert_eq!(rs.global_budget, 0);
        assert_eq!(rs.blocking, 1);
        assert_eq!(rs.role, ResourceRole::None);
        assert_eq!(rs._reserved, [0u8; 2]);
    }

    // spec: design/arch/effect-concurrency.md §5 — the descriptor crosses the
    // platform-DLL C-ABI as raw bytes (`PlatformFn.concurrency`), so its
    // `#[repr(C)]` field offsets + size are a FROZEN layout contract (governed by
    // ABI_VERSION, not source-evolution guards). The `global_budget` slot is the
    // slice-4 degree carrier (SPRINT.md arch R5 / FIXME 0442).
    #[test]
    fn concurrency_descriptor_repr_c_layout_and_inert_budget_present() {
        use core::mem::{align_of, offset_of, size_of};
        assert_eq!(offset_of!(ConcurrencyDescriptor, token), 0);
        assert_eq!(offset_of!(ConcurrencyDescriptor, cardinality), 8);
        // The inert backpressure slot is present and at the frozen offset.
        assert_eq!(offset_of!(ConcurrencyDescriptor, global_budget), 12);
        assert_eq!(offset_of!(ConcurrencyDescriptor, blocking), 16);
        // v9: `role` consumes the byte the former `_reserved[0]` held (offset 17);
        // `_reserved` shrinks to `[u8; 2]` at offset 18. Offsets + size are unchanged.
        assert_eq!(offset_of!(ConcurrencyDescriptor, role), 17);
        assert_eq!(offset_of!(ConcurrencyDescriptor, _reserved), 18);
        assert_eq!(align_of::<ConcurrencyDescriptor>(), 8);
        // 8 (token) + 4 (cardinality) + 4 (budget) + 1 (blocking) + 1 (role) +
        // 2 (_reserved) = 20, rounded up to the 8-byte alignment = 24. Unchanged from v8.
        assert_eq!(size_of::<ConcurrencyDescriptor>(), 24);
    }

    // spec: design/arch/effect-concurrency.md §12 — `Poll` is the FFI collapse of
    // `std::task::Poll`, `#[repr(i32)]` so it crosses the C-ABI as a plain int.
    // The discriminants are byte-stable: Ready = 0, Pending = 1.
    #[test]
    fn poll_repr_i32_ready_zero_pending_one() {
        assert_eq!(Poll::Ready as i32, 0);
        assert_eq!(Poll::Pending as i32, 1);
        assert_eq!(core::mem::size_of::<Poll>(), core::mem::size_of::<i32>());
    }
}
