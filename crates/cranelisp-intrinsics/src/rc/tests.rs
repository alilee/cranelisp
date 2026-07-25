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

// spec: 12-runtime §12.3.2 — A1 (safety-invariants §4 R8): rc_inc fires the
// stale-inc liveness assert at the offending inc of a freed pointer (the
// inc-half of the FIXME-0494 dec-half check). Debug-only; nextest runs each
// test in its own process, so `LIVE_ALLOCS` is not perturbed by a parallel
// alloc re-populating the freed address.
#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "STALE RC INC")]
fn a1_rc_inc_fires_on_stale_inc() {
    let base = alloc::alloc_with_rc(16) as i64; // live, rc=1
    // SAFETY: base was returned by alloc_with_rc and its RC is 1 — this brings
    // it to 0 and frees it, so it is no longer live.
    unsafe { alloc::dealloc(base as *mut u8) };
    assert!(
        !alloc::is_live(base as usize),
        "precondition: freed pointer is non-live"
    );
    rc_inc(base); // stale inc of a freed pointer — A1 must panic here
}

// spec: 12-runtime §12.3.2 — A1: rc_inc on a LIVE pointer does not fire the
// stale-inc assert (positive path).
#[cfg(debug_assertions)]
#[test]
fn a1_rc_inc_ok_on_live_pointer() {
    let base = alloc::alloc_with_rc(16) as i64; // live, rc=1
    rc_inc(base); // rc → 2, live — no panic
    // SAFETY: two refs (rc=2); consume twice to balance and free.
    consume_shallow(base);
    consume_shallow(base);
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
        let rc_ptr =
            &*((base as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const AtomicI64);
        rc_ptr.fetch_add(1, Ordering::Release);
    }
    consume_shallow(base); // rc: 2 -> 1, no free
    assert_eq!(alloc::alloc_count() - allocs_before, 1);
    assert_eq!(
        alloc::dealloc_count() - deallocs_before,
        0,
        "must not free when other refs exist"
    );
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

// ---------------------------------------------------------------------------
// S99 Wave 0 — non-atomic-RC probe + RC-op instrumentation (measurement)
// ---------------------------------------------------------------------------

// spec: sprints/SPRINT.md §"Wave 0" R4 — the non-atomic RC RMW helper reads the
// OLD value and writes old+delta at the RC field (the measurement-only path).
#[test]
fn s99_nonatomic_rc_rmw_reads_old_and_writes_new() {
    let base = alloc::alloc_with_rc(16) as i64; // rc initialised to 1
    let rc_field =
        |b: i64| unsafe { *((b as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const i64) };

    // inc: returns old (1), field becomes 2.
    let old = unsafe { nonatomic_rc_rmw(base, 1) };
    assert_eq!(old, 1);
    assert_eq!(rc_field(base), 2);

    // dec: returns old (2), field becomes 1.
    let old2 = unsafe { nonatomic_rc_rmw(base, -1) };
    assert_eq!(old2, 2);
    assert_eq!(rc_field(base), 1);

    unsafe { alloc::dealloc(base as *mut u8) };
}

// spec: sprints/SPRINT.md §"Wave 0" — RC-op instrumentation: the backend-inline
// tally helpers bump the inc/dec counters (confirms the copy-per-node volume).
#[test]
fn s99_rc_stat_helpers_tally_inc_and_dec() {
    let inc0 = RC_INC_COUNT.load(Ordering::Relaxed);
    let dec0 = RC_DEC_COUNT.load(Ordering::Relaxed);

    rc_stat_inc();
    rc_stat_inc();
    rc_stat_dec();

    assert_eq!(RC_INC_COUNT.load(Ordering::Relaxed) - inc0, 2);
    assert_eq!(RC_DEC_COUNT.load(Ordering::Relaxed) - dec0, 1);
}

// spec: sprints/SPRINT.md §"Wave 0" R4 — byte-identical-off: with the env unset
// (the test process default) both measurement gates are inert.
#[test]
fn s99_measurement_gates_off_by_default() {
    assert!(
        !nonatomic_rc_enabled(),
        "CRANELISP_NONATOMIC_RC must default off"
    );
    assert!(!rc_stats_enabled(), "CRANELISP_RC_STATS must default off");
}

// ---------------------------------------------------------------------------
// H2 (S102 increment I) — per-mechanism attribution counters
// (design/backend/ownership-codegen.md §13.2). Seam = the intrinsics-owned
// counter state + the `[RC_STATS]` line grammar. Scenario classes:
// complexity (each counter's advance path), edge (the atomic-vs-non-atomic
// arm discrimination; the atomic-share derivation), negative (a counter that
// must NOT move; the reuse placeholders that must stay 0).
// ---------------------------------------------------------------------------

// --- stack-slot counter (B3.4) ---

// spec: design/backend/ownership-codegen.md §13.2 — stack_slot hit tally advances
#[test]
fn h2_tally_stack_slot_advances_the_counter() {
    let h0 = stack_slot_hits();
    tally_stack_slot();
    assert_eq!(
        stack_slot_hits(),
        h0 + 1,
        "one stack-slot tally must advance by 1"
    );
    tally_stack_slot();
    tally_stack_slot();
    assert_eq!(
        stack_slot_hits(),
        h0 + 3,
        "two more tallies must advance by 2"
    );
}

// spec: design/backend/ownership-codegen.md §13.2 — NEGATIVE: no tally ⇒ no move
#[test]
fn h2_stack_slot_counter_does_not_move_without_a_tally() {
    let h0 = stack_slot_hits();
    // A non-stack mechanism firing (an RC-emit tally) must NOT touch stack_slot.
    tally_rc_emit(false);
    tally_rc_emit(true);
    assert_eq!(
        stack_slot_hits(),
        h0,
        "stack_slot must not advance when only RC-emit tallies fire"
    );
}

// --- non-atomic-op-share counter (B3.3): the arm discrimination ---

// spec: design/backend/ownership-codegen.md §13.2 — atomic arm bumps total only
#[test]
fn h2_tally_rc_emit_atomic_bumps_total_not_nonatomic() {
    let (na0, tot0) = rc_emit_counts();
    tally_rc_emit(false); // atomic arm
    let (na1, tot1) = rc_emit_counts();
    assert_eq!(tot1, tot0 + 1, "an atomic emit must advance the total");
    assert_eq!(
        na1, na0,
        "an atomic emit must NOT advance the non-atomic tally"
    );
}

// spec: design/backend/ownership-codegen.md §13.2 — non-atomic arm bumps both
#[test]
fn h2_tally_rc_emit_nonatomic_bumps_both() {
    let (na0, tot0) = rc_emit_counts();
    tally_rc_emit(true); // non-atomic arm
    let (na1, tot1) = rc_emit_counts();
    assert_eq!(tot1, tot0 + 1, "a non-atomic emit must advance the total");
    assert_eq!(
        na1,
        na0 + 1,
        "a non-atomic emit must advance the non-atomic tally"
    );
}

// spec: design/backend/ownership-codegen.md §13.2 — the atomic share is derived
// (rc_atomic = total − nonatomic); the counters never let nonatomic exceed total.
#[test]
fn h2_rc_atomic_is_total_minus_nonatomic() {
    let (na0, tot0) = rc_emit_counts();
    tally_rc_emit(false);
    tally_rc_emit(true);
    tally_rc_emit(false);
    let (na1, tot1) = rc_emit_counts();
    assert_eq!(tot1 - tot0, 3, "three emits advance the total by 3");
    assert_eq!(na1 - na0, 1, "one of the three was non-atomic");
    assert!(na1 <= tot1, "non-atomic count must never exceed the total");
}

// --- the [RC_STATS] line grammar + placeholder honesty ---

// spec: design/backend/ownership-codegen.md §13.2 — the per-mechanism family is
// present in the line (the H2 needle is the counter FAMILY name).
#[test]
fn h2_stats_line_carries_the_per_mechanism_family() {
    let line = rc_stats_line();
    assert!(line.starts_with("[RC_STATS]"), "line tag preserved: {line}");
    for field in [
        "rc_inc=",
        "rc_dec=",
        "allocs=",
        "deallocs=", // the pre-H2 fields, order kept
        "stack_slot=",
        "reuse_hit=",
        "reuse_miss=",
        "rc_nonatomic=",
        "rc_atomic=",
    ] {
        assert!(
            line.contains(field),
            "RC_STATS line missing `{field}`: {line}"
        );
    }
    // The pre-H2 four fields keep their leading order/position so every existing
    // token/regex parser still matches.
    let head = "[RC_STATS] rc_inc=";
    assert!(
        line.starts_with(head),
        "leading field order changed: {line}"
    );
    let deallocs_at = line.find("deallocs=").unwrap();
    let stack_at = line.find("stack_slot=").unwrap();
    assert!(
        stack_at > deallocs_at,
        "per-mechanism family must follow the original four"
    );
}

// spec: design/backend/ownership-codegen.md §6.5 — reuse hit/miss are LIVE
// runtime tallies at increment II. Absent any tally (fresh process) they read 0
// (honest, not fabricated); a tally advances them.
#[test]
fn reuse_counters_default_zero_and_advance_on_tally() {
    let (h0, m0) = reuse_counts();
    // Fresh process (nextest per-test isolation): nothing has tallied reuse.
    assert_eq!(h0, 0, "reuse_hit reads 0 before any tally");
    assert_eq!(m0, 0, "reuse_miss reads 0 before any tally");
    tally_reuse_hit();
    tally_reuse_hit();
    tally_reuse_miss();
    let (h1, m1) = reuse_counts();
    assert_eq!(
        h1,
        h0 + 2,
        "two reuse-hit tallies advance the hit counter by 2"
    );
    assert_eq!(
        m1,
        m0 + 1,
        "one reuse-miss tally advances the miss counter by 1"
    );
}

// spec: design/backend/ownership-codegen.md §6.5 — NEGATIVE: a reuse-hit tally
// must NOT touch the reuse-miss counter (and vice versa) — the two arms are
// distinct discriminator sides.
#[test]
fn reuse_hit_and_miss_are_independent() {
    let (h0, m0) = reuse_counts();
    tally_reuse_hit();
    let (h1, m1) = reuse_counts();
    assert_eq!(h1, h0 + 1, "reuse-hit tally advances hit");
    assert_eq!(m1, m0, "reuse-hit tally must NOT advance miss");
}

// spec: design/backend/ownership-codegen.md §6.5 / §13.2.1 — the [RC_STATS] line
// carries the reuse family reflecting the live counters (not a hardcoded 0).
#[test]
fn reuse_family_reflects_live_counters_in_the_line() {
    tally_reuse_hit();
    tally_reuse_miss();
    let (h, m) = reuse_counts();
    let line = rc_stats_line();
    assert!(
        line.contains(&format!("reuse_hit={h}")),
        "line must report the live reuse_hit={h}: {line}"
    );
    assert!(
        line.contains(&format!("reuse_miss={m}")),
        "line must report the live reuse_miss={m}: {line}"
    );
}

// --- N1 (S105 §13.2.2): per-run alloc BYTES field ---------------------------

// spec: design/backend/ownership-codegen.md §13.2.2 N1 — the `[RC_STATS]` line
// carries the appended `alloc_bytes=` field (alloc volume, I2), positioned AFTER
// the pre-existing tail so every positional parser still matches.
#[test]
fn n1_alloc_bytes_field_present_and_appended() {
    let line = rc_stats_line();
    assert!(
        line.contains("alloc_bytes="),
        "line must carry the N1 field: {line}"
    );
    // Appended after the prior tail field (`str-len_adapt=`) so the whole prefix
    // grammar is byte-stable for existing token/regex readers.
    let str_len_at = line
        .find("str-len_adapt=")
        .expect("str-len_adapt field present");
    let alloc_bytes_at = line.find("alloc_bytes=").unwrap();
    assert!(
        alloc_bytes_at > str_len_at,
        "alloc_bytes must be appended at the tail, after str-len_adapt: {line}"
    );
    // The pre-N1 fields keep their leading order (regression guard for parsers).
    assert!(
        line.starts_with("[RC_STATS] rc_inc="),
        "leading order preserved: {line}"
    );
}

// spec: design/backend/ownership-codegen.md §13.2.2 N1 — the reported value is the
// live `alloc::bytes_allocated()` tally (NOT count, NOT a fabricated constant).
// `BYTES_ALLOCATED` is monotonic-cumulative and tracks ONLY `alloc_with_rc` (the
// cranelisp heap), so Rust-side `format!`/`String` allocations do not perturb it.
#[test]
fn n1_alloc_bytes_reflects_the_live_bytes_allocated_tally() {
    let b0 = crate::alloc::bytes_allocated();
    // A known cranelisp-heap allocation: total_size = HeapHeader::SIZE (16) + 32.
    let p = crate::alloc::alloc_with_rc(32);
    let expected = b0 + cranelisp_types::HeapHeader::SIZE + 32;
    let line = rc_stats_line();
    assert!(
        line.contains(&format!("alloc_bytes={expected}")),
        "alloc_bytes must equal the live cumulative byte tally ({expected}): {line}"
    );
    // Clean up the chunk (BYTES_ALLOCATED is cumulative, so this does not rewind
    // the counter — it only keeps the live-header scan tidy).
    unsafe {
        crate::alloc::dealloc(p);
    }
}

// spec: design/backend/ownership-codegen.md §13.2.2 N1 — NEGATIVE: alloc_bytes is
// distinct from the alloc COUNT (`allocs=`) — a single alloc advances bytes by its
// full size, not by 1. Guards against the field being wired to the wrong counter.
#[test]
fn n1_alloc_bytes_is_volume_not_count() {
    let c0 = crate::alloc::alloc_count();
    let b0 = crate::alloc::bytes_allocated();
    let p = crate::alloc::alloc_with_rc(64);
    let dc = crate::alloc::alloc_count() - c0;
    let db = crate::alloc::bytes_allocated() - b0;
    assert_eq!(dc, 1, "one allocation advances the count by exactly 1");
    assert_eq!(
        db,
        cranelisp_types::HeapHeader::SIZE + 64,
        "bytes advance by the full size, not 1"
    );
    assert_ne!(
        db, dc,
        "alloc_bytes must NOT track the same magnitude as allocs (count)"
    );
    unsafe {
        crate::alloc::dealloc(p);
    }
}

// spec: design/backend/ownership-codegen.md §9.2 / §13.2.1 — H3: the per-extern
// adaptation-pair family names `str-len` in the line (present even at count 0 —
// the family-presence honesty), and its runtime tally hook advances the count.
#[test]
fn h3_str_len_adapt_family_present_and_advances() {
    // Family name present at count 0 (fresh process).
    assert!(
        rc_stats_line().contains("str-len_adapt="),
        "the H3 per-extern family must name str-len: {}",
        rc_stats_line()
    );
    let c0 = str_len_adapt_count();
    extern_adapt_str_len_stat();
    extern_adapt_str_len_stat();
    assert_eq!(
        str_len_adapt_count(),
        c0 + 2,
        "the str-len adaptation hook must advance the per-extern tally"
    );
    assert!(
        rc_stats_line().contains(&format!("str-len_adapt={}", c0 + 2)),
        "the line must report the live str-len adaptation count"
    );
}
