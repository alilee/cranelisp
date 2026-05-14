//! GOT-population observation extension point per Decision 40-pattern + FIXME
//! 0099 and `facades/backend.md` §"GOT-population observation (extension
//! point)".
//!
//! Backend defines the observation taxonomy and a registration API; all
//! consumer-side state (ring buffer, env-var activation, panic-safe formatter,
//! flush-to-stderr dump) lives in `int`'s `src/got_trace/` parallel to
//! `src/io_trace/` post-Decision-40 relocation. This is the third instance of
//! the project's consistent observability pattern (alongside `io_trace` and
//! `scheduler_trace`).
//!
//! The events fire from `compile_to_module`'s post-finalize code-pointer
//! collection site (where each defined function's fresh-build address is in
//! hand — `JitWrite`) and from `Linker::load_object`'s symbol-resolution loop
//! (`LinkerWrite`). The `Redefinition` variant is published here for the
//! consumer (int) to emit when its symbol-table write detects an existing
//! `Code::Jit` for the entry — that site lives outside backend today and is
//! wired in Wave 3b-2.
//!
//! Production batch (`--link`, non-trace `--run`) does NOT register an
//! observer and pays one relaxed-load null check per emit site (one
//! conditional branch after optimisation).
//!
//! ## Threading
//!
//! `register_got_observer` is thread-safe. The slot is an `AtomicPtr<()>`;
//! readers use `Ordering::Acquire` so any observer state published before
//! registration is visible to the reading thread. Writers use
//! `Ordering::Release`. Last write wins under happens-before order.
//!
//! Pass `None` to unregister; subsequent emits are no-ops on the hot path
//! until another observer registers.

use std::sync::atomic::{AtomicPtr, Ordering};

use cranelisp_types::{ModuleFullPath, Symbol};

// ---------------------------------------------------------------------------
// Event taxonomy
// ---------------------------------------------------------------------------

/// GOT-population event tag — names the lifecycle moment that produced the
/// slot write.
///
/// `#[non_exhaustive]` per facade — adding a new tag is a minor revision
/// (consumers must not match-exhaustively on this enum without a default
/// arm).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
#[non_exhaustive]
pub enum GotEventTag {
    /// Fresh JIT build wrote a callable address into a GOT slot for a
    /// freshly-compiled symbol. Fires from `compile_to_module`'s
    /// post-finalize collection of `try_get_finalized_function` results
    /// for every defined symbol that produced a runtime pointer.
    JitWrite,
    /// Cache-hit load wrote a callable address into a GOT slot for a
    /// symbol resolved from a `.o` file. Fires from `Linker::load_object`
    /// as each text-section symbol's address is resolved.
    LinkerWrite,
    /// A GOT slot already populated by an earlier `JitWrite` or
    /// `LinkerWrite` was overwritten by a fresh address (REPL
    /// redefinition). Backend publishes this tag for the consumer to
    /// emit when its symbol-table write site detects the prior
    /// population — that detection lives in `int` (Decision-41 future
    /// state moves the detection here, but it is not the Wave 3b-1
    /// state).
    Redefinition,
}

/// Provenance of the address a GOT-write event published. Distinguishes
/// the JIT lifecycle owner (`Jit`) from the cache-load lifecycle owner
/// (`Linker`) — the same per-symbol address may flow through either
/// origin over the symbol's lifetime.
///
/// `#[non_exhaustive]` per facade.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum GotProvenance {
    /// Fresh JIT build via `JITModule::get_finalized_function`. The
    /// inner address is the lifecycle owner's identity for
    /// correlation (e.g., the `Jit` struct address); not load-bearing
    /// for value semantics — observer consumers use it only for
    /// merge-sort or trace cross-referencing.
    Jit { jit_addr: usize },
    /// Cache-hit load via `Linker::load_object`. The inner address is
    /// the linker's identity for correlation.
    Linker { linker_addr: usize },
}

/// GOT-population event payload. One per slot-write. All fields are
/// `Copy` so the struct can be passed by reference into the observer
/// without heap allocation on the emit hot path; the `module` and
/// `symbol` newtypes are passed by reference fields (not owned) for the
/// same reason.
///
/// `#[non_exhaustive]` per facade — adding new fields is a minor
/// revision.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct GotEvent {
    /// The module whose GOT received the write.
    pub module: ModuleFullPath,
    /// The bare symbol name whose slot was populated.
    pub symbol: Symbol,
    /// GOT slot index within `module`'s GOT table.
    pub slot: usize,
    /// The fn pointer value written into the slot.
    pub ptr: *const u8,
    /// Origin of the address — JIT-freshly-built vs cache-loaded.
    pub provenance: GotProvenance,
}

// SAFETY: GotEvent carries a `*const u8` which is not Send/Sync by default,
// but the pointer is only an observation payload — the observer must NOT
// dereference it. Marking the event Send+Sync allows consumers to enqueue
// events on per-thread ring buffers and merge across threads at flush time.
unsafe impl Send for GotEvent {}
unsafe impl Sync for GotEvent {}

/// GOT observer callback signature.
///
/// The observer is invoked synchronously by the emit site. It MUST be
/// panic-free (or use `catch_unwind` internally); a panic in the
/// observer propagates out of the backend call path with undefined
/// behaviour.
///
/// Calling convention is `extern "Rust"` fn pointer — the observer runs
/// in the calling thread.
pub type GotObserver = fn(GotEventTag, &GotEvent);

// ---------------------------------------------------------------------------
// Observer slot
// ---------------------------------------------------------------------------

/// Atomic pointer to the currently-registered observer. Null = unregistered.
///
/// Stored as `AtomicPtr<()>` carrying a transmuted fn pointer because
/// `AtomicPtr<fn(_,_)>` is not directly representable. The transmute is
/// sound: function pointers are `*const ()` on every supported platform
/// (Decision 11 ABI assumes pointer-sized fn pointers).
static OBSERVER_SLOT: AtomicPtr<()> = AtomicPtr::new(std::ptr::null_mut());

/// Replace the registered observer atomically.
///
/// Pass `Some(f)` to register `f` (any previous observer is replaced).
/// Pass `None` to unregister — subsequent events become no-ops on the
/// emit hot path until another observer registers.
///
/// Thread-safe from any thread; last write wins under happens-before
/// ordering. Callers do not reason about Acquire/Release — the API
/// commits to the contract.
///
/// Cost when unregistered: one relaxed `AtomicPtr` load + null check
/// per emit site (one conditional branch after optimisation).
pub fn register_got_observer(observer: Option<GotObserver>) {
    let ptr: *mut () = match observer {
        Some(f) => f as *mut (),
        None => std::ptr::null_mut(),
    };
    OBSERVER_SLOT.store(ptr, Ordering::Release);
}

/// Internal hot-path emit. Called by the GOT-write sites in backend
/// (`compile_to_module`'s post-finalize loop and
/// `Linker::load_object`'s symbol-resolution loop) and by the future
/// Decision-41 backend-side write_code site that will detect
/// redefinition. When no observer is registered, costs one `Acquire`
/// load + null check + branch.
///
/// Made `pub` so the int-side consumer (Wave 3b-2) can call `emit` for
/// the `Redefinition` tag from its symbol-table write site without
/// going through any indirection.
#[inline]
pub fn emit(tag: GotEventTag, event: &GotEvent) {
    let raw = OBSERVER_SLOT.load(Ordering::Acquire);
    if raw.is_null() {
        return;
    }
    // SAFETY: `raw` was written by `register_got_observer` from a valid
    // `GotObserver` fn pointer. Function pointers are pointer-sized on every
    // supported platform; transmute round-trips losslessly.
    let observer: GotObserver = unsafe { std::mem::transmute::<*mut (), GotObserver>(raw) };
    observer(tag, event);
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering as StdOrdering};

    // Process-global observer state means these tests cannot run truly
    // concurrently; nextest runs each test in its own process so this is
    // safe under the project's `cargo nt` invocation. Within a single
    // process the tests serialise via the OBSERVER_SLOT mutation +
    // unregister-at-end discipline.

    static TEST_OBSERVER_CALLS: AtomicUsize = AtomicUsize::new(0);
    static LAST_TAG_BITS: AtomicUsize = AtomicUsize::new(usize::MAX);

    fn record_observer(tag: GotEventTag, _event: &GotEvent) {
        TEST_OBSERVER_CALLS.fetch_add(1, StdOrdering::Relaxed);
        LAST_TAG_BITS.store(tag as usize, StdOrdering::Relaxed);
    }

    fn reset_counters() {
        TEST_OBSERVER_CALLS.store(0, StdOrdering::Relaxed);
        LAST_TAG_BITS.store(usize::MAX, StdOrdering::Relaxed);
    }

    fn fake_event() -> GotEvent {
        GotEvent {
            module: ModuleFullPath::from("user"),
            symbol: Symbol::from("foo"),
            slot: 0,
            ptr: 0xDEAD_BEEF as *const u8,
            provenance: GotProvenance::Jit { jit_addr: 0xABCD },
        }
    }

    #[test]
    fn unregistered_emit_is_no_op() {
        // Defensively make sure no observer is left from another test.
        register_got_observer(None);
        reset_counters();
        emit(GotEventTag::JitWrite, &fake_event());
        assert_eq!(
            TEST_OBSERVER_CALLS.load(StdOrdering::Relaxed),
            0,
            "unregistered emit must not invoke any observer",
        );
    }

    #[test]
    fn register_then_emit_delivers_event() {
        reset_counters();
        register_got_observer(Some(record_observer));
        emit(GotEventTag::LinkerWrite, &fake_event());
        // Cleanup BEFORE asserting — keep the OBSERVER_SLOT clean for siblings.
        register_got_observer(None);

        assert_eq!(
            TEST_OBSERVER_CALLS.load(StdOrdering::Relaxed),
            1,
            "observer must be invoked once per emit when registered",
        );
        assert_eq!(
            LAST_TAG_BITS.load(StdOrdering::Relaxed),
            GotEventTag::LinkerWrite as usize,
            "observer must receive the correct tag",
        );
    }

    #[test]
    fn unregister_after_register_disables_emit() {
        reset_counters();
        register_got_observer(Some(record_observer));
        emit(GotEventTag::JitWrite, &fake_event());
        register_got_observer(None);
        let count_before = TEST_OBSERVER_CALLS.load(StdOrdering::Relaxed);
        emit(GotEventTag::Redefinition, &fake_event());
        let count_after = TEST_OBSERVER_CALLS.load(StdOrdering::Relaxed);
        assert_eq!(
            count_before, count_after,
            "post-unregister emit must not invoke the observer",
        );
    }

    #[test]
    fn last_observer_wins() {
        static FIRST_CALLS: AtomicUsize = AtomicUsize::new(0);
        static SECOND_CALLS: AtomicUsize = AtomicUsize::new(0);
        fn first(_t: GotEventTag, _e: &GotEvent) {
            FIRST_CALLS.fetch_add(1, StdOrdering::Relaxed);
        }
        fn second(_t: GotEventTag, _e: &GotEvent) {
            SECOND_CALLS.fetch_add(1, StdOrdering::Relaxed);
        }
        FIRST_CALLS.store(0, StdOrdering::Relaxed);
        SECOND_CALLS.store(0, StdOrdering::Relaxed);

        register_got_observer(Some(first));
        register_got_observer(Some(second));
        emit(GotEventTag::JitWrite, &fake_event());
        register_got_observer(None);

        assert_eq!(
            FIRST_CALLS.load(StdOrdering::Relaxed),
            0,
            "old observer must not fire after replacement"
        );
        assert_eq!(
            SECOND_CALLS.load(StdOrdering::Relaxed),
            1,
            "new observer must fire"
        );
    }

    #[test]
    fn all_three_tags_round_trip_through_observer() {
        // Sanity: every published tag variant flows through emit to the
        // observer correctly. Catches the "added a tag but forgot the
        // dispatch path" regression.
        reset_counters();
        register_got_observer(Some(record_observer));
        for tag in [
            GotEventTag::JitWrite,
            GotEventTag::LinkerWrite,
            GotEventTag::Redefinition,
        ] {
            emit(tag, &fake_event());
        }
        register_got_observer(None);
        assert_eq!(
            TEST_OBSERVER_CALLS.load(StdOrdering::Relaxed),
            3,
            "each emit must invoke the observer exactly once"
        );
    }
}
