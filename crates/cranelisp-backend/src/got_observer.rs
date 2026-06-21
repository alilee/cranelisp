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
mod tests;
