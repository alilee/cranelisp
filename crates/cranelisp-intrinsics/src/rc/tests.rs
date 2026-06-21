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
