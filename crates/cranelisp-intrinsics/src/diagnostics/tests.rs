//! Self-tests for the tier-5 memory-safety diagnostic modes (design §6 MS-P6):
//! each mode's mechanism is exercised directly at its seam. The env-gated
//! process-start behaviour is proven end-to-end by the `/qa` oracle lane (which
//! sets the env vars); here we drive the mechanism functions with fresh
//! instances so a fault the mode must catch is planted and observed.

use super::*;

// M1 — quarantine withholds freed blocks and never re-hands their addresses.
// spec: 12-runtime §12.3 — R8 alloc/free balance (safety-invariants §4 R8, M1)
#[test]
fn quarantine_withholds_all_blocks_without_cap() {
    let mut q = Quarantine::new();
    let layout = Layout::from_size_align(24, 8).unwrap();
    // SAFETY: each block is allocated with `layout` and ownership is handed to
    // the quarantine; with no cap none is released, so we drain+free at the end.
    let bases: Vec<usize> = (0..5)
        .map(|_| unsafe { std::alloc::alloc(layout) } as usize)
        .collect();
    for &b in &bases {
        unsafe { q.withhold(b as *mut u8, layout, None) };
    }
    assert_eq!(
        q.blocks.len(),
        5,
        "all 5 withheld, none released (unbounded)"
    );
    assert_eq!(q.retained_bytes, 5 * 24);
    for (base, l) in q.blocks.drain(..) {
        // SAFETY: withheld (never freed) — released exactly once here.
        unsafe { std::alloc::dealloc(base as *mut u8, l) };
    }
}

// M1 cap — past the byte cap, the OLDEST blocks release FIFO; the newest stay
// quarantined (the recent-free UAF, the common case, stays caught).
// spec: 12-runtime §12.3 — R8 alloc/free balance (safety-invariants §4 R8, M1 cap)
#[test]
fn quarantine_fifo_releases_oldest_past_cap() {
    let mut q = Quarantine::new();
    let layout = Layout::from_size_align(24, 8).unwrap();
    // SAFETY: real allocations; the two oldest are released by `withhold` under
    // the cap, the three newest are drained+freed at the end.
    let bases: Vec<usize> = (0..5)
        .map(|_| unsafe { std::alloc::alloc(layout) } as usize)
        .collect();
    let cap = Some(72); // 3 blocks * 24 bytes
    for &b in &bases {
        unsafe { q.withhold(b as *mut u8, layout, cap) };
    }
    assert!(q.retained_bytes <= 72, "retained bytes bounded by the cap");
    assert_eq!(q.blocks.len(), 3, "3 newest remain, 2 oldest released FIFO");
    let remaining: Vec<usize> = q.blocks.iter().map(|(b, _)| *b).collect();
    assert_eq!(
        remaining,
        vec![bases[2], bases[3], bases[4]],
        "the NEWEST blocks stay quarantined; the coldest reopen for reuse"
    );
    for (base, l) in q.blocks.drain(..) {
        // SAFETY: withheld (never freed) — released exactly once here.
        unsafe { std::alloc::dealloc(base as *mut u8, l) };
    }
}

// M2 — scrub writes the poison word over the whole allocation (header+payload).
// spec: 12-runtime §12.3 — R8 (safety-invariants §4 R8, M2 poison)
#[test]
fn scrub_writes_poison_over_whole_allocation() {
    let total = 40usize; // header(16) + 3 i64 payload words
    let layout = Layout::from_size_align(total, 8).unwrap();
    // SAFETY: fresh allocation; scrubbed then freed with the same layout.
    let base = unsafe { std::alloc::alloc_zeroed(layout) };
    unsafe { scrub(base, total) };
    for i in 0..(total / 8) {
        let w = unsafe { *(base as *const u64).add(i) };
        assert_eq!(w, POISON_WORD, "i64 word {i} is poisoned");
    }
    unsafe { std::alloc::dealloc(base, layout) };
}

// M2 — a HeapString payload is `len` raw bytes, so total_size may be a
// non-multiple of 8; the byte-wise tail must still be poisoned.
// spec: 12-runtime §12.3 — R8 (safety-invariants §4 R8, M2 tail)
#[test]
fn scrub_poisons_nonmultiple_of_8_tail() {
    let total = 27usize; // 3 full words + 3 tail bytes
    let layout = Layout::from_size_align(total, 8).unwrap();
    // SAFETY: fresh allocation; scrubbed then freed with the same layout.
    let base = unsafe { std::alloc::alloc_zeroed(layout) };
    unsafe { scrub(base, total) };
    let poison_bytes = POISON_WORD.to_le_bytes();
    for i in 0..total {
        let b = unsafe { *base.add(i) };
        assert_eq!(b, poison_bytes[i % 8], "byte {i} is poisoned");
    }
    unsafe { std::alloc::dealloc(base, layout) };
}

// M3 — the parity hard-check reports an imbalance on a leaked or double-freed
// synthetic ledger and stays silent when balanced (drives the exit-check logic
// without registering an atexit or aborting).
// spec: 12-runtime §12.3 — R8 alloc/free balance (safety-invariants §4 R8, M3)
#[test]
fn parity_report_flags_leak() {
    let r = alloc_parity_report(10, 9, &[]);
    assert!(r.is_some(), "allocs > deallocs is a leak");
    assert!(r.unwrap().contains("LEAK"));
}

// spec: 12-runtime §12.3 — R8 (safety-invariants §4 R8, M3 double-free face)
#[test]
fn parity_report_flags_double_free() {
    let r = alloc_parity_report(9, 10, &[]);
    assert!(r.is_some(), "deallocs > allocs is a double-free");
    assert!(r.unwrap().contains("DOUBLE-FREE"));
}

// spec: 12-runtime §12.3 — R8 (safety-invariants §4 R8, M3 debug live-set face)
#[test]
fn parity_report_flags_nonempty_live_set() {
    let r = alloc_parity_report(5, 5, &[(0x1000, 24, 0x3)]);
    assert!(
        r.is_some(),
        "a non-empty live set at exit is a leak even at count parity"
    );
    assert!(r.unwrap().contains("live set non-empty"));
}

// spec: 12-runtime §12.3 — R8 (safety-invariants §4 R8, M3 balanced)
#[test]
fn parity_report_none_when_balanced() {
    assert!(alloc_parity_report(5, 5, &[]).is_none());
    assert!(alloc_parity_report(0, 0, &[]).is_none());
}

// ---------------------------------------------------------------------------
// §7.5 — the shared seam PREcheck (design §10 `diagnostics` (precheck) row)
// ---------------------------------------------------------------------------

// Normal/positive: a well-formed live base passes. The header words are read
// from a REAL production allocation (not a synthetic pair), so the predicate is
// pinned against what `alloc_with_rc` actually writes.
// spec: 12-runtime §12.3 — R8 (safety-invariants §4 R8 / diagnostic-modes §7.5)
#[test]
fn precheck_accepts_a_well_formed_live_production_base() {
    let base = crate::alloc::alloc_with_rc(24) as i64;
    // SAFETY: `base` is a live allocation of 40 bytes; words 0 and 8 are the header.
    let (size, rc) = unsafe {
        (
            crate::heap_access::read_i64(base, 0),
            crate::heap_access::read_i64(base, 8),
        )
    };
    assert_eq!(size, 40, "header alloc_size = HeapHeader::SIZE + payload");
    assert_eq!(rc, 1, "alloc_with_rc initialises rc to 1");
    assert_eq!(seam_precheck_verdict(size, rc), None);
    crate::rc::consume_shallow(base);
}

// Edge: the smallest legal allocation is exactly `HeapHeader::SIZE` (a
// payload-less header), and a large-but-constructible size is legal. Both must
// be accepted or the armed lane rejects real programs.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.5 header plausibility)
#[test]
fn precheck_accepts_smallest_and_largest_legal_sizes() {
    assert!(header_size_plausible(HeapHeader::SIZE as i64), "exactly SIZE");
    assert!(header_size_plausible(1 << 40), "a large constructible layout");
    assert_eq!(seam_precheck_verdict(HeapHeader::SIZE as i64, 1), None);
}

// Edge, and the reason the design's "8-aligned size" clause is NOT implemented:
// a `HeapString` payload is `len` field + `byte_len` RAW bytes, so a 3-byte
// string's `alloc_size` is 27 — a legitimate, deliberately ragged size. An
// alignment predicate on the size value would hard-fail every string dec under
// `CRANELISP_RC_DEC_CHECK`. This row is the false-positive fence.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.5; HeapString ragged sizes)
#[test]
fn precheck_accepts_a_ragged_heap_string_size() {
    let base = crate::heap_string::alloc_string(b"abc") as i64;
    // SAFETY: live allocation; word 0 is the header alloc_size.
    let size = unsafe { crate::heap_access::read_i64(base, 0) };
    assert_eq!(size, 27, "16 header + 8 len + 3 raw bytes — not 8-aligned");
    assert!(
        header_size_plausible(size),
        "a ragged HeapString size MUST NOT be rejected"
    );
    crate::rc::consume_shallow(base);
}

// Negative: an interior/non-base address's word@0 is a tag / length / field
// value, far below `HeapHeader::SIZE` — the A2 face.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.5 / §7.3 A2)
#[test]
fn precheck_rejects_sizes_below_the_header() {
    for bogus in [0, 1, 3, 8, 15] {
        assert!(!header_size_plausible(bogus), "alloc_size {bogus} < SIZE");
        assert!(
            seam_precheck_verdict(bogus, 1).is_some(),
            "alloc_size {bogus} must be rejected even with a plausible rc"
        );
    }
}

// Negative: a poisoned (M2-scrubbed) or quarantined base reads `POISON_WORD` at
// word@0 — negative as an `i64`, and no constructible `Layout` as a `usize`.
// This is what makes the A3/A4 rows produce a located seam message instead of a
// `Layout` panic.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.5 / §7.3 A3, A4)
#[test]
fn precheck_rejects_a_poisoned_header_word() {
    let poisoned = POISON_WORD as i64;
    assert!(poisoned < 0, "POISON_WORD is negative read as i64");
    assert!(!header_size_plausible(poisoned));
    assert!(seam_precheck_verdict(poisoned, poisoned).is_some());
    // And read as an unsigned magnitude it still forms no Layout.
    assert!(!header_size_plausible(i64::MAX), "isize-overflowing size");
}

// Negative: a released target's rc is `0` (or wild-negative under poison). The
// verdict rejects both, and reports the SIZE predicate first when both fail.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.5 rc predicate)
#[test]
fn precheck_rejects_nonpositive_rc() {
    for rc in [0, -1, i64::MIN] {
        let why = seam_precheck_verdict(40, rc).expect("rc {rc} must be rejected");
        assert!(why.contains("rc is <= 0"), "verdict names the rc predicate: {why}");
    }
    assert_eq!(seam_precheck_verdict(40, 1), None, "rc = 1 is accepted");
}

// The precheck must not touch the words it validates — rejection precedes (and
// replaces) mutation. Driven unarmed here (the verdict is pure); the armed
// end-to-end proof is the A1 triplet, whose seam message reports `rc=0`: had the
// check run post-mutation it would report `rc=1`.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.5 validation-before-mutation)
#[test]
fn precheck_verdict_does_not_mutate_the_header() {
    let base = crate::alloc::alloc_with_rc(8) as i64;
    // SAFETY: live allocation; header words are readable/writable.
    unsafe { crate::heap_access::write_i64(base, 8, 0) };
    let (size, rc) = unsafe {
        (
            crate::heap_access::read_i64(base, 0),
            crate::heap_access::read_i64(base, 8),
        )
    };
    assert!(seam_precheck_verdict(size, rc).is_some(), "rc = 0 is rejected");
    // SAFETY: same live allocation.
    let rc_after = unsafe { crate::heap_access::read_i64(base, 8) };
    assert_eq!(rc_after, 0, "the rejected call left the rc word untouched");
    // Restore the rc so the block frees cleanly (keeps the process balanced).
    unsafe { crate::heap_access::write_i64(base, 8, 1) };
    crate::rc::consume_shallow(base);
}

// Byte-identical-off: with no env set every gate reads its off value, so no
// mode perturbs an op. (End-to-end byte-identity is the full suite staying green
// with no env set; this pins the gate defaults at the seam.)
// spec: 12-runtime §12.3 — R8 (safety-invariants §4 R8, byte-identical-off)
#[test]
fn all_gates_default_off() {
    // NOTE: this test process must run with none of the mode env vars set (the
    // canonical nextest invocation). Each gate is cached at first read.
    assert!(!quarantine_enabled());
    assert!(!scrub_enabled());
    assert!(!parity_hard_enabled());
    assert!(!parity_dump_enabled());
    assert!(!rc_check_release_enabled());
    assert!(quarantine_max_bytes().is_none());
}
