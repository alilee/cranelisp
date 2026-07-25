//! IO observation extension point per Decision 40. The contract is carried by
//! the crate-root `//!` rustdoc + `design/arch/bounded-contexts.md` §4b —
//! Intrinsics.
//!
//! Intrinsics defines the observation taxonomy and a registration API;
//! all consumer-side state (ring buffers, panic hooks, formatters,
//! dump-to-stderr, merge-sort) lives in `int`'s `src/io_trace/`. The IO
//! trampoline (in this crate's [`crate::io`] module) emits events through the
//! registered observer via a relaxed-load null check on the hot path.
//!
//! Production batch (`--link`, non-trace `--run`) does NOT register an
//! observer and pays one relaxed-load null check per IO call site
//! (one conditional branch after optimisation).
//!
//! ## Threading
//!
//! `register_io_observer` is thread-safe. The slot is an
//! `AtomicUsize` holding the observer fn's integer address; readers use
//! `Ordering::Acquire` so any observer state
//! published before registration is visible to the reading thread. Writers
//! use `Ordering::Release`. Last write wins under happens-before order.
//!
//! Pass `None` to unregister; subsequent IO events are no-ops on the hot
//! path until another observer registers.

use std::sync::OnceLock;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

// ---------------------------------------------------------------------------
// Event taxonomy
// ---------------------------------------------------------------------------

/// IO trampoline event tag — the variants reflect the trampoline's state
/// machine transitions (per `design/backend/io-trampoline-trace.md §3`).
///
/// `#[non_exhaustive]` per facade — adding a new tag is a minor revision
/// (consumers must not match-exhaustively on this enum without a default
/// arm).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
#[non_exhaustive]
pub enum IoEventTag {
    /// Top of `cranelisp_run_io` / `run_io_trampoline`.
    TrampolineEnter,
    /// Return from `run_io_trampoline`.
    TrampolineExit,
    /// `IO_TAG_PURE` arm hit — value extracted.
    PureStep,
    /// `IO_TAG_BIND` arm — continuation pushed onto stack.
    BindEnter,
    /// Continuation has been invoked and a new `current` installed.
    BindExit,
    /// Just before `call_effect_thunk` — platform effect dispatched.
    PlatformEffect,
    /// `cont_stack.push`.
    ContPush,
    /// `cont_stack.pop`.
    ContPop,
    /// `dispatch_par_branches` launched a single branch.
    ParSpark,
    /// Serial-group `WorkItem` started.
    ParSerialGroupEnter,
    /// `dispatch_par_branches` completed; results assembled.
    ParJoin,
    /// Reserved — resource-token barrier hit (Slice 4 / not currently
    /// emitted).
    ParBarrierForce,
}

/// IO trampoline event payload — one variant per `IoEventTag` family.
///
/// `#[non_exhaustive]` per facade. All variants are plain POD; no heap
/// allocation. The full struct (tag + payload + per-thread sequencing
/// metadata that the consumer adds) is intended to fit in a 64-byte
/// cache line.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum IoEvent {
    /// `TrampolineEnter` — root tree pointer.
    TrampolineEnter { io_ptr: i64 },
    /// `TrampolineExit` — final result value returned from the trampoline.
    TrampolineExit { result: i64 },
    /// `PureStep` — the value extracted from the Pure node and whether
    /// the Pure node itself was produced inside the trampoline (fresh)
    /// or came from the caller's tree.
    PureStep { value: i64, is_fresh: bool },
    /// `BindEnter` — pointers to the Bind node's inner subtree and
    /// continuation closure, plus the fresh flag.
    BindEnter {
        inner_ptr: i64,
        cont_ptr: i64,
        is_fresh: bool,
    },
    /// `BindExit` — the new `current` installed after calling the
    /// continuation.
    BindExit { new_current: i64 },
    /// `PlatformEffect` — thunk pointer, resource token, and scheduling
    /// class (as `u8`; `cranelisp_types::SchedulingClass::from_u32`
    /// decodes the discriminant at dump time).
    PlatformEffect {
        thunk_ptr: i64,
        resource_token: i64,
        scheduling_class: u8,
    },
    /// `ContPush` / `ContPop` — pointer to the continuation closure,
    /// the fresh flag, and the resulting stack depth after the op.
    Cont {
        cont_ptr: i64,
        is_fresh: bool,
        new_depth: u32,
    },
    /// `ParSpark` — parent Par node, branch index within the parent,
    /// resource token grouping this branch.
    ParSpark {
        parent_ptr: i64,
        branch_idx: u32,
        token: i64,
    },
    /// `ParSerialGroupEnter` — the shared token and the number of
    /// branches this group will execute sequentially.
    ParSerialGroupEnter { token: i64, branch_count: u32 },
    /// `ParJoin` — parent Par node and the total branch count joined.
    ParJoin { parent_ptr: i64, count: u32 },
    /// `ParBarrierForce` — reserved; carries only the blocked token.
    ParBarrierForce { token: i64 },
}

/// IO observer callback signature.
///
/// The observer is invoked synchronously by the IO trampoline at every
/// instrumented call site. It MUST be panic-free (or use `catch_unwind`
/// internally); a panic in the observer propagates out of the JIT-emitted
/// call path with undefined behaviour.
///
/// Calling convention is `extern "C"`-equivalent fn pointer — the observer
/// runs in the calling thread.
pub type IoObserver = fn(IoEventTag, &IoEvent);

// ---------------------------------------------------------------------------
// Observer slot
// ---------------------------------------------------------------------------

/// Address of the currently-registered observer fn, or `0` = unregistered.
///
/// Stored as the `usize` numeric address of the [`IoObserver`] fn pointer
/// (`AtomicPtr<fn(_,_)>` is not directly representable). LOW-2 / FIXME 0370: this
/// holds the fn pointer's *integer address* via the guaranteed `fn as usize` /
/// `usize as fn` cast pair — NOT a data↔fn `transmute` (which Rust does not
/// bless even though it works on every current target). The cast round-trips
/// losslessly: `fn as usize` is a well-defined fn-pointer-to-integer cast, and
/// `addr as IoObserver` is its inverse for a value originally produced from a
/// valid `IoObserver`. Decision 11's ABI already assumes pointer-sized fn
/// pointers, so the `usize` slot is wide enough.
static OBSERVER_SLOT: AtomicUsize = AtomicUsize::new(0);

/// Replace the registered observer atomically.
///
/// Pass `Some(f)` to register `f` (any previous observer is replaced).
/// Pass `None` to unregister — subsequent events become no-ops on the
/// trampoline hot path until another observer registers.
///
/// Thread-safe from any thread; last write wins under happens-before
/// ordering. Callers do not reason about Acquire/Release — the API
/// commits to the contract.
///
/// Cost when unregistered: one relaxed `AtomicPtr` load + null check
/// per emit site (one conditional branch after optimisation).
pub fn register_io_observer(observer: Option<IoObserver>) {
    // `f as usize` is a guaranteed fn-pointer-to-integer cast; `0` marks the
    // unregistered slot (a valid fn pointer is never address 0). No transmute.
    let addr: usize = match observer {
        Some(f) => f as usize,
        None => 0,
    };
    OBSERVER_SLOT.store(addr, Ordering::Release);
}

/// Internal hot-path emit. Called by the IO trampoline at every
/// instrumented site. When no observer is registered, costs one
/// `Acquire` load + null check + branch.
///
/// Kept `pub` so the in-crate IO trampoline (`crate::io`, i.e.
/// `cranelisp_run_io`) can call it directly on the hot path without
/// going through any indirection.
#[inline]
pub fn emit(tag: IoEventTag, event: &IoEvent) {
    let addr = OBSERVER_SLOT.load(Ordering::Acquire);
    if addr == 0 {
        return;
    }
    // SAFETY: `addr` was written by `register_io_observer` as `f as usize` from a
    // valid `IoObserver`. LOW-2 / FIXME 0370: this is an *integer*→fn-pointer
    // transmute, which the Rust reference explicitly blesses (the canonical way
    // to reconstitute a fn pointer stored as an integer), unlike the prior
    // *data-pointer* (`*mut ()`)→fn-pointer transmute that sat on the boundary of
    // what the reference guarantees. `usize` is pointer-sized (Decision 11), so
    // the widths match and the round-trip is lossless.
    let observer: IoObserver = unsafe { std::mem::transmute::<usize, IoObserver>(addr) };
    observer(tag, event);
}

// ---------------------------------------------------------------------------
// Shared monotonic anchor
// ---------------------------------------------------------------------------

/// Process-origin anchor for timestamping IO events. First call sets it
/// to `Instant::now()`; every subsequent call returns the same reference.
/// Consumers (int's IO trace ring buffer + int's scheduler trace) derive
/// their monotonic-ns timestamps from this anchor so cross-trace
/// merge-sort is possible.
///
/// Per facade §"IO observation" — kept here so int's scheduler trace
/// and the IO trace share the same origin.
pub fn trace_anchor() -> &'static Instant {
    static TRACE_ANCHOR: OnceLock<Instant> = OnceLock::new();
    TRACE_ANCHOR.get_or_init(Instant::now)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
