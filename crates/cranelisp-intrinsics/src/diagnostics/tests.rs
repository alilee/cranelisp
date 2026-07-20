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
    assert_eq!(q.blocks.len(), 5, "all 5 withheld, none released (unbounded)");
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
    assert!(r.is_some(), "a non-empty live set at exit is a leak even at count parity");
    assert!(r.unwrap().contains("live set non-empty"));
}

// spec: 12-runtime §12.3 — R8 (safety-invariants §4 R8, M3 balanced)
#[test]
fn parity_report_none_when_balanced() {
    assert!(alloc_parity_report(5, 5, &[]).is_none());
    assert!(alloc_parity_report(0, 0, &[]).is_none());
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
