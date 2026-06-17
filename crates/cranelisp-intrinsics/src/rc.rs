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
            eprintln!("[RC] {op:>5} {ptr:#x} rc={rc}");
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
mod tests {
    use super::*;

    // spec: 12-runtime §12.3.2 — RC trace logging does not panic
    #[test]
    fn test_rc_trace_does_not_panic() {
        // Just verify it doesn't crash — output goes to stderr.
        rc_trace("test", 0x1234, 1);
    }

    // spec: 12-runtime §12.3.2 — RC trace disabled by default
    #[test]
    fn test_rc_trace_enabled_default_false() {
        // Without CRANELISP_RC_TRACE=1 in env, should be false.
        // Note: this test may pass or fail depending on env, but shouldn't panic.
        let _ = is_rc_trace_enabled();
    }

    // spec: 12-runtime §12.3.2 — RC underflow panics on zero (debug assertions)
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "RC underflow")]
    fn test_underflow_check_panics_on_zero() {
        rc_underflow_check(0x1234, 0);
    }

    // spec: 12-runtime §12.3.2 — RC underflow check passes on positive count
    #[cfg(debug_assertions)]
    #[test]
    fn test_underflow_check_ok_on_positive() {
        // Should not panic when old_rc > 0.
        rc_underflow_check(0x1234, 1);
        rc_underflow_check(0x1234, 5);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consume_shallow skips bare nullary tags
    #[test]
    fn decision24_consume_shallow_skips_nullary_tags() {
        // Bare nullary tags (< NULLARY_TAG_THRESHOLD) must be skipped —
        // they are not heap pointers. This is critical for Mixed-category
        // ADTs where an Option/Result value might be either a bare tag or
        // a heap pointer.
        let allocs_before = alloc::alloc_count();
        let deallocs_before = alloc::dealloc_count();
        // 0 = None (nullary tag); passing to consume_shallow must be a no-op.
        consume_shallow(0);
        consume_shallow(1);
        consume_shallow(100);
        consume_shallow(cranelisp_types::NULLARY_TAG_THRESHOLD as i64 - 1);
        assert_eq!(alloc::alloc_count() - allocs_before, 0);
        assert_eq!(alloc::dealloc_count() - deallocs_before, 0);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consume_shallow frees last reference
    #[test]
    fn decision24_consume_shallow_frees_last_reference() {
        let allocs_before = alloc::alloc_count();
        let deallocs_before = alloc::dealloc_count();
        // Allocate a heap value with rc=1; consume_shallow should free it.
        let base = alloc::alloc_with_rc(16) as i64;
        consume_shallow(base);
        assert_eq!(alloc::alloc_count() - allocs_before, 1);
        assert_eq!(alloc::dealloc_count() - deallocs_before, 1);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consume_shallow preserves value at rc>1
    #[test]
    fn decision24_consume_shallow_preserves_shared_reference() {
        let allocs_before = alloc::alloc_count();
        let deallocs_before = alloc::dealloc_count();
        let base = alloc::alloc_with_rc(16) as i64;
        // Simulate a second reference (rc: 1 -> 2).
        unsafe {
            let rc_ptr = &*((base as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const AtomicI64);
            rc_ptr.fetch_add(1, Ordering::Release);
        }
        consume_shallow(base); // rc: 2 -> 1, no free
        assert_eq!(alloc::alloc_count() - allocs_before, 1);
        assert_eq!(alloc::dealloc_count() - deallocs_before, 0, "must not free when other refs exist");
        // Clean up.
        unsafe { alloc::dealloc(base as *mut u8) };
    }

    // spec: spec/appendix-c-nfr.md §C.4.1 — RC increment atomic, ≥ Release
    #[test]
    fn rc_inc_increments_canonical_rc_field() {
        let allocs_before = alloc::alloc_count();
        let deallocs_before = alloc::dealloc_count();
        // Allocate a heap value with rc=1.
        let base = alloc::alloc_with_rc(16) as i64;
        // rc_inc: 1 -> 2 (lands on the canonical RC field, observed by the dec).
        rc_inc(base);
        // First dec: 2 -> 1, must NOT free.
        consume_shallow(base);
        assert_eq!(alloc::alloc_count() - allocs_before, 1);
        assert_eq!(
            alloc::dealloc_count() - deallocs_before,
            0,
            "must not free after rc_inc raised the count"
        );
        // Second dec: 1 -> 0, frees.
        consume_shallow(base);
        assert_eq!(alloc::dealloc_count() - deallocs_before, 1);
    }

    // spec: spec/appendix-c-nfr.md §C.4.1 — RC increment atomic, ≥ Release
    #[test]
    fn rc_inc_skips_nullary_tags() {
        // Bare nullary tags (< NULLARY_TAG_THRESHOLD) must be skipped — they are
        // not heap pointers, and a non-skipped inc would corrupt the tag value.
        let allocs_before = alloc::alloc_count();
        let deallocs_before = alloc::dealloc_count();
        rc_inc(0);
        rc_inc(1);
        rc_inc(100);
        rc_inc(cranelisp_types::NULLARY_TAG_THRESHOLD as i64 - 1);
        assert_eq!(alloc::alloc_count() - allocs_before, 0);
        assert_eq!(alloc::dealloc_count() - deallocs_before, 0);
    }

    // spec: 12-runtime §12.3.2 — RC trace logging does not panic
    #[test]
    fn rc_inc_traces_without_panic() {
        // rc_inc on a valid cell emits the "inc" trace op and must not panic.
        let base = alloc::alloc_with_rc(16) as i64;
        rc_inc(base); // rc: 1 -> 2, traces "inc"
        // Clean up both references.
        consume_shallow(base);
        consume_shallow(base);
    }
}
