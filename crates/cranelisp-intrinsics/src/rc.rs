//! Reference counting trace logging and debug helpers.
//!
//! When `CRANELISP_RC_TRACE=1`, logs every alloc/free/inc/dec with pointer
//! address and RC value to stderr. Gated behind `cfg(debug_assertions)`.
//!
//! The backend emits RC inc/dec inline as atomic_rmw — NOT as extern function
//! calls. This module provides the trace logging infrastructure that both the
//! runtime (alloc/free) and the backend (inc/dec underflow check) can use.
//!
//! ## Consuming helper
//!
//! Decision 24 (Sprint 56 Step 2c) introduces a uniform consuming calling
//! convention. Externs implemented in Rust must dec their own heap arguments
//! if they do not return them. `consume_shallow` provides the canonical way
//! to do this for any heap value with no embedded heap sub-references (String,
//! plain Trace ADT pointers — the caller should use specialised paths for Vec,
//! ADTs with heap fields, and closures where inline drop glue is already
//! emitted by the backend).

use std::sync::LazyLock;
use std::sync::atomic::{AtomicBool, AtomicI64, Ordering};

use cranelisp_types::HeapHeader;

use crate::alloc;

/// Whether RC trace logging is enabled. Checked once at process start.
static RC_TRACE_ENABLED: LazyLock<AtomicBool> = LazyLock::new(|| {
    let enabled = std::env::var("CRANELISP_RC_TRACE")
        .map(|v| v == "1")
        .unwrap_or(false);
    AtomicBool::new(enabled)
});

/// Log an RC operation (alloc, free, inc, dec) to stderr if tracing is enabled.
///
/// Only active in debug builds. In release builds this is a no-op.
#[inline]
pub fn rc_trace(op: &str, ptr: i64, rc: i64) {
    #[cfg(debug_assertions)]
    {
        if RC_TRACE_ENABLED.load(Ordering::Relaxed) {
            let tag = if ptr > 0x1000 { unsafe { *((ptr as isize + 16) as *const i64) } } else { -1 };
            eprintln!("[RC] {op:>5} {ptr:#x} rc={rc} tag@16={tag}");
        }
    }
    #[cfg(not(debug_assertions))]
    {
        let _ = (op, ptr, rc);
    }
}

/// Check if RC trace logging is currently enabled.
pub fn is_rc_trace_enabled() -> bool {
    RC_TRACE_ENABLED.load(Ordering::Relaxed)
}

/// Consume a heap argument: atomically dec RC; if it was 1, free the allocation.
///
/// This is the canonical "extern received a heap arg, does not return it,
/// must release its reference" operation. It is safe for:
///   - String (HeapString — no heap sub-references)
///   - Trace ADT (Trace contains heap fields, but freeing it unconditionally
///     would leave fields dangling — use only when the caller's semantics match)
///   - Any heap object with NO heap-typed fields
///
/// NOT safe for Vec (separate data buffer to free), closures (embedded drop
/// glue), or ADTs with heap fields (need drop glue to recursively dec fields).
/// Those have specialised code paths.
///
/// No-op for values below `NULLARY_TAG_THRESHOLD` (bare nullary tags of
/// Mixed-category ADTs).
///
/// # Safety
///
/// `ptr` must be either a valid heap base pointer whose RC is > 0, or a
/// bare nullary tag (< NULLARY_TAG_THRESHOLD).
#[inline]
pub fn consume_shallow(ptr: i64) {
    if ptr < cranelisp_types::NULLARY_TAG_THRESHOLD as i64 {
        return; // bare tag — no heap alloc to dec
    }
    // SAFETY: caller guarantees ptr is a valid heap base with RC > 0.
    let rc_ptr = unsafe {
        &*((ptr as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const AtomicI64)
    };
    let old_rc = rc_ptr.fetch_sub(1, Ordering::Release);
    debug_assert!(
        old_rc > 0,
        "consume_shallow underflow: ptr={ptr:#x} had rc={old_rc} before decrement"
    );
    rc_trace("dec", ptr, old_rc - 1);
    if old_rc == 1 {
        std::sync::atomic::fence(Ordering::Acquire);
        // SAFETY: RC reached 0, no other references exist.
        unsafe { alloc::dealloc(ptr as *mut u8) };
    }
}

/// Increment the reference count of a heap value (shallow).
///
/// The blessed extern-Rust RC-inc entry point — the inc-half mirror of
/// [`consume_shallow`]. Use this anywhere a Rust-implemented extern creates a
/// new reference to a heap value it received or is sharing (e.g. an item
/// copied into a fresh ADT cell, or an identity-share that returns its arg
/// with a fresh count). Single owner for the shallow-inc discipline
/// (Principle 7) — open-coded `fetch_add` / `*rc_ptr += 1` at extern call
/// sites must route through here.
///
/// No-op for values below `NULLARY_TAG_THRESHOLD` (bare nullary tags of
/// Mixed-category ADTs — not heap pointers).
///
/// # Ordering
///
/// Uses `fetch_add(1, Ordering::Release)`. Release is the NFR C.4.1 floor
/// ("RC increment MUST use at least Release ordering"; `spec/appendix-c-nfr.md`
/// §C.4.1) and matches the backend's inline `atomic_rmw` inc (SeqCst ≥ Release)
/// and the existing atomic share path. An inc creates a new reference; the
/// Release publishes any writes that established the new reference before the
/// count is observed by another thread (the symmetric counterpart to the dec's
/// Release + free-path Acquire fence in `consume_shallow`).
///
/// # Safety
///
/// `ptr` must be either a valid heap base pointer whose RC is > 0, or a bare
/// nullary tag (< `NULLARY_TAG_THRESHOLD`).
#[inline]
pub fn rc_inc(ptr: i64) {
    if ptr < cranelisp_types::NULLARY_TAG_THRESHOLD as i64 {
        return; // bare tag — no heap alloc to inc
    }
    // SAFETY: caller guarantees ptr is a valid heap base with RC > 0.
    let rc_ptr = unsafe {
        &*((ptr as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const AtomicI64)
    };
    let old_rc = rc_ptr.fetch_add(1, Ordering::Release);
    rc_trace("inc", ptr, old_rc + 1);
}

/// RC underflow check — called from JIT-generated inline dec code.
///
/// The backend emits `atomic_rmw(Sub, ...)` inline. After the sub, if the
/// old RC value was <= 0 (underflow), the backend calls this function for
/// diagnostic logging and debug assertion.
///
/// In release builds, this is a no-op (the JIT should not emit the call).
///
/// Linker symbol: `runtime/rc_underflow_check` (per runtime/* convention).
#[unsafe(export_name = "runtime/rc_underflow_check")]
pub extern "C-unwind" fn rc_underflow_check(ptr: i64, old_rc: i64) -> i64 {
    debug_assert!(
        old_rc > 0,
        "RC underflow: ptr={ptr:#x} had rc={old_rc} before decrement"
    );
    rc_trace("UNDERFLOW", ptr, old_rc);
    0
}

#[cfg(test)]
mod tests;
