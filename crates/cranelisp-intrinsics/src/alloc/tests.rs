use super::*;

// Tests use delta-based assertions (snapshot before/after) because
// global counters are shared across parallel tests.

// spec: 12-runtime §12.3.1 — heap alloc/dealloc round-trip with RC header
#[test]
fn test_alloc_and_dealloc_round_trip() {
    let allocs_before = alloc_count();
    let deallocs_before = dealloc_count();

    let base = alloc_with_rc(32);
    assert!(!base.is_null());

    // Check header.
    unsafe {
        let alloc_size = *(base as *const i64);
        assert_eq!(alloc_size, 48); // 16 header + 32 payload
        let rc = *(base.add(8) as *const i64);
        assert_eq!(rc, 1);
    }

    assert!(alloc_count() - allocs_before >= 1);

    unsafe { dealloc(base) };

    assert!(dealloc_count() - deallocs_before >= 1);
}

// spec: 12-runtime §12.3.1 — allocation tracking counters (alloc count, bytes)
#[test]
fn test_tracking_counters() {
    let allocs_before = alloc_count();
    let deallocs_before = dealloc_count();
    let allocated_before = bytes_allocated();

    let a = alloc_with_rc(8);
    let b = alloc_with_rc(16);
    assert!(alloc_count() - allocs_before >= 2);
    assert!(bytes_allocated() - allocated_before >= 24 + 32); // (16+8) + (16+16)

    unsafe { dealloc(a) };
    assert!(dealloc_count() - deallocs_before >= 1);

    unsafe { dealloc(b) };
    assert!(dealloc_count() - deallocs_before >= 2);
}

// spec: 12-runtime §12.3.2 — live allocation tracking (debug assertions)
#[cfg(debug_assertions)]
#[test]
fn test_live_allocs_tracking() {
    let base = alloc_with_rc(16);
    assert!(is_live(base as usize));

    unsafe { dealloc(base) };
    assert!(!is_live(base as usize));
}

// spec: 12-runtime §12.3.1 — double free detection (debug assertions)
#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "double free")]
fn test_double_free_detected() {
    let base = alloc_with_rc(16);
    unsafe {
        dealloc(base);
        dealloc(base); // should panic
    }
}

// spec: 12-runtime §12.3.1 — extern "C" alloc/dealloc interface for JIT
#[test]
fn test_extern_c_interface() {
    let allocs_before = alloc_count();
    let deallocs_before = dealloc_count();

    let ptr = heap_alloc(24);
    assert_ne!(ptr, 0);

    // Check header via the returned base pointer.
    unsafe {
        let alloc_size = *(ptr as *const i64);
        assert_eq!(alloc_size, 40); // 16 + 24
        let rc = *((ptr as *const u8).add(8) as *const i64);
        assert_eq!(rc, 1);
    }

    assert!(alloc_count() - allocs_before >= 1);
    heap_dealloc(ptr);
    assert!(dealloc_count() - deallocs_before >= 1);
}

// spec: 12-runtime §12.3.1 / design/platform/host-wiring-s76.md §2 —
// cranelisp_alloc_with_tag produces the backend ConstrADT heap layout for a
// zero-field data constructor: [total_size | rc=1 | tag@16].
//
// Offsets cross-checked against cranelisp-backend `HeapAdt`: TAG_OFFSET = 16
// (HeapHeader::SIZE), FIELDS_START = 24. payload_size(0) = 8 (tag only).
#[test]
fn test_alloc_with_tag_zero_fields() {
    let base = cranelisp_alloc_with_tag(3, 0, std::ptr::null());
    assert_ne!(base, 0);
    let base = base as *const u8;
    unsafe {
        // Header: total_size = 16 (header) + 8 (tag slot).
        let total_size = *(base as *const i64);
        assert_eq!(total_size, 24, "header total_size = 16 + 8 (tag)");
        // RC initialised to 1 by alloc_with_rc.
        let rc = *(base.add(HeapHeader::RC_OFFSET as usize) as *const i64);
        assert_eq!(rc, 1);
        // Tag at payload+0 (base + 16 = HeapAdt::TAG_OFFSET). The u32 tag in
        // a zeroed 8-byte slot reads back as the i64 the backend stores.
        let tag_i64 = *(base.add(HeapHeader::SIZE) as *const i64);
        assert_eq!(tag_i64, 3, "tag at payload+0 reads back as i64");
    }
    unsafe { dealloc(base as *mut u8) };
}

// spec: 12-runtime §12.3.1 / design/platform/host-wiring-s76.md §2 —
// cranelisp_alloc_with_tag produces the backend ConstrADT layout for a
// 2-field data constructor: [total_size | rc=1 | tag@16 | f0@24 | f1@32].
//
// Mirrors cranelisp-backend `emit_adt_construct` (tag at TAG_OFFSET=16,
// fields at field_offset(0)=24, field_offset(1)=32) and the intrinsics-own
// trace.rs `alloc_adt` walk (PAYLOAD_OFFSET=16, FIELD0_OFFSET=24).
#[test]
fn test_alloc_with_tag_two_fields() {
    let fields: [i64; 2] = [0x1111_2222_3333_4444, -7];
    let base = cranelisp_alloc_with_tag(1, 2, fields.as_ptr());
    assert_ne!(base, 0);
    let base = base as *const u8;
    unsafe {
        // Header: total_size = 16 + 8 (tag) + 16 (two fields) = 40.
        let total_size = *(base as *const i64);
        assert_eq!(total_size, 40, "header total_size = 16 + 8 + 2*8");
        let rc = *(base.add(HeapHeader::RC_OFFSET as usize) as *const i64);
        assert_eq!(rc, 1);
        // Tag at offset 16 (HeapAdt::TAG_OFFSET).
        let tag_i64 = *(base.add(16) as *const i64);
        assert_eq!(tag_i64, 1);
        // Fields at offsets 24 and 32 (HeapAdt::field_offset(0/1)) — copied
        // verbatim from fields_ptr.
        let f0 = *(base.add(24) as *const i64);
        let f1 = *(base.add(32) as *const i64);
        assert_eq!(f0, 0x1111_2222_3333_4444);
        assert_eq!(f1, -7);
    }
    unsafe { dealloc(base as *mut u8) };
}

// spec: 12-runtime §12.3.1 — the upper 4 bytes of the tag slot are zero pad
// (alloc_with_rc zero-initialises), so a small u32 tag round-trips as i64.
#[test]
fn test_alloc_with_tag_pad_bytes_zero() {
    let base = cranelisp_alloc_with_tag(0xABCD, 0, std::ptr::null());
    let base = base as *const u8;
    unsafe {
        let tag_u32 = *(base.add(HeapHeader::SIZE) as *const u32);
        let pad_u32 = *(base.add(HeapHeader::SIZE + 4) as *const u32);
        assert_eq!(tag_u32, 0xABCD);
        assert_eq!(pad_u32, 0, "4 pad bytes after the u32 tag are zero");
    }
    unsafe { dealloc(base as *mut u8) };
}

// spec: 12-runtime §12.3.1 — zero-payload allocation (header only)
#[test]
fn test_zero_payload() {
    // Zero payload is valid — just a bare header (alloc_size + rc).
    let base = alloc_with_rc(0);
    unsafe {
        let alloc_size = *(base as *const i64);
        assert_eq!(alloc_size, 16); // header only
    }
    unsafe { dealloc(base) };
}

// ---------------------------------------------------------------------------
// Ruling 7 (S118) / S116 ruling 5 — the subtractive API change
// ---------------------------------------------------------------------------

// The counter family has NO reset seam, and no consumer-less peak accessor. This
// is a structural property, not a style choice: `reset_counts()` could zero the
// counters that are the M3 alloc/free-parity check's only evidence, so its
// absence is what makes the ledger trustworthy (Principle 18). The row greps the
// module source AND the committed public-API baseline, so a re-introduction
// fails here rather than in a later audit — and the rustdoc cannot silently
// resurrect a dangling `[`reset_counts`]` intra-doc link either.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §9.4; bounded-contexts §4b inv 8)
#[test]
fn counter_family_has_no_reset_seam_in_source_or_baseline() {
    let src = include_str!("../alloc.rs");
    let baseline = include_str!("../../public-api.txt");
    for gone in ["reset_counts", "bytes_peak"] {
        assert!(
            !src.contains(gone),
            "{gone} must be absent from alloc.rs source AND rustdoc (S118 ruling 7)"
        );
        assert!(
            !baseline.contains(gone),
            "{gone} must be absent from the committed public-api.txt baseline"
        );
    }
    // The four survivors are still there — the change is subtractive only.
    for kept in [
        "alloc_count",
        "dealloc_count",
        "bytes_allocated",
        "bytes_current",
    ] {
        assert!(baseline.contains(kept), "{kept} must survive");
    }
}

// The surviving counters are process-lifetime evidence: the three monotonic ones
// never decrease, and `bytes_current` tracks live bytes (falls on release). A
// consumer needing a window snapshots and subtracts — which this row does.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §9.4)
#[test]
fn surviving_counters_are_monotonic_process_lifetime_evidence() {
    let (a0, d0, b0, live0) = (
        alloc_count(),
        dealloc_count(),
        bytes_allocated(),
        bytes_current(),
    );
    let base = alloc_with_rc(24);
    assert_eq!(alloc_count(), a0 + 1);
    assert_eq!(bytes_allocated(), b0 + 40);
    assert_eq!(bytes_current(), live0 + 40, "live bytes rise on alloc");
    // SAFETY: `base` was just returned by `alloc_with_rc` and is unfreed.
    unsafe { dealloc(base) };
    assert_eq!(dealloc_count(), d0 + 1);
    assert_eq!(
        bytes_allocated(),
        b0 + 40,
        "cumulative bytes never decrease — no reset seam can zero them"
    );
    assert_eq!(bytes_current(), live0, "live bytes fall back on release");
    assert!(alloc_count() >= a0 && dealloc_count() >= d0);
}
