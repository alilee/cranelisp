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
    assert!(
        header_size_plausible(HeapHeader::SIZE as i64),
        "exactly SIZE"
    );
    assert!(
        header_size_plausible(1 << 40),
        "a large constructible layout"
    );
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
        assert!(
            why.contains("rc is <= 0"),
            "verdict names the rc predicate: {why}"
        );
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
    assert!(
        seam_precheck_verdict(size, rc).is_some(),
        "rc = 0 is rejected"
    );
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

// ===========================================================================
// §7.1/§7.2 — the closed plant protocol (design §10 `diagnostics` (protocol))
// ===========================================================================

// Acceptance item 4 — UNARMED BYTE-INERTNESS at the seam. With the arm variable
// absent there is no plant, no state, no counter adjustment and no allocation:
// the hook is one cached `Option` read returning `NoAction`. This row runs on
// every ordinary suite run (as do the plant child bodies below, which no-op
// unarmed — §7.6 makes byte-inertness continuously executed rather than claimed).
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.2, acceptance item 4)
#[test]
fn plant_protocol_is_inert_when_unarmed() {
    let obs = fault_observation();
    assert!(obs.plant.is_none(), "no plant without the arm variable");
    assert!(!obs.fired);
    assert_eq!(obs.planted_base, 0);
    assert_eq!(obs.planted_total_size, 0);
    assert_eq!(
        obs.quarantine_retained_bytes, 0,
        "M1 off ⇒ zero retention, and the quarantine is never constructed"
    );

    let before = (crate::alloc::alloc_count(), crate::alloc::dealloc_count());
    for event in [
        FaultEvent::PostAlloc {
            base: 0x1000,
            total_size: PLANT_MARKER_TOTAL,
        },
        FaultEvent::PreFree {
            base: 0x1000,
            total_size: PLANT_MARKER_TOTAL,
        },
        FaultEvent::PostFree {
            base: 0x1000,
            total_size: PLANT_MARKER_TOTAL,
            withheld: false,
        },
    ] {
        assert_eq!(test_fault_event(event), FaultAction::NoAction);
    }
    let after = (crate::alloc::alloc_count(), crate::alloc::dealloc_count());
    assert_eq!(before, after, "the unarmed hook adjusts no counter");
    assert!(
        ledger_plant_report_line().is_none(),
        "no plant-identity line without a fired ledger plant"
    );
}

// The arm string is exact: the protocol version, not the sprint of landing. Any
// other value — including a near-miss and a spelling supplied without the arm —
// is FULLY off, never a partial plant.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.1 activation)
#[test]
fn only_the_exact_arm_string_arms_the_protocol() {
    assert_eq!(FAULT_ARM_VALUE, "s116-detection-proof-v1");
    for (arm, spelling) in [
        (None, None),
        (None, Some("M3Leak")),
        (Some(""), Some("M3Leak")),
        (Some("s116-detection-proof-v0"), Some("M3Leak")),
        (Some("S116-Detection-Proof-v1"), Some("M3Leak")),
        (Some("detection-proof"), Some("M3Leak")),
    ] {
        assert!(
            matches!(parse_plant_spec(arm, spelling), PlantSpec::Off),
            "arm={arm:?} spelling={spelling:?} must be fully off"
        );
    }
}

// All eight closed spellings parse to their own plant, and the spelling is the
// report identity (round-trip). A spelling set that drifts from the test-plan
// names would silently disarm the committed e2e children.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.1 closed enum)
#[test]
fn all_eight_plant_spellings_parse_and_round_trip() {
    assert_eq!(FaultPlant::ALL.len(), 8);
    for p in FaultPlant::ALL {
        match parse_plant_spec(Some(FAULT_ARM_VALUE), Some(p.spelling())) {
            PlantSpec::Armed(got) => assert_eq!(got, p, "{} parses to itself", p.spelling()),
            _ => panic!("{} must parse", p.spelling()),
        }
    }
    // Surrounding whitespace is trimmed, not a config error.
    assert!(matches!(
        parse_plant_spec(Some(FAULT_ARM_VALUE), Some("  M3Leak\n")),
        PlantSpec::Armed(FaultPlant::M3Leak)
    ));
}

// Negative: unknown, empty, and MULTIPLE spellings are hard test-configuration
// errors — never a partial plant, and never a silently-different plant.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.1 config errors)
#[test]
fn unknown_empty_or_multiple_spellings_are_configuration_errors() {
    for spelling in [
        None,
        Some(""),
        Some("   "),
        Some("M9Nonesuch"),
        Some("m3leak"),
        Some("M3Leak,M1StaleReuse"),
        Some("M3Leak M1StaleReuse"),
    ] {
        assert!(
            matches!(
                parse_plant_spec(Some(FAULT_ARM_VALUE), spelling),
                PlantSpec::ConfigError(_)
            ),
            "spelling {spelling:?} must be a hard config error"
        );
    }
}

// Deterministic selection: a row needing a SPECIFIC allocation captures the
// exact marker size and nothing else, and fires exactly once however many
// events arrive.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.2 plant selection)
#[test]
fn marker_size_selection_captures_only_the_intended_allocation() {
    let state = PlantState::new(FaultPlant::A1ZeroRc);
    // Every non-marker allocation is left alone.
    for total_size in [24, 40, PLANT_MARKER_TOTAL - 8, PLANT_MARKER_TOTAL + 8] {
        assert_eq!(
            fault_event_armed(
                &state,
                FaultEvent::PostAlloc {
                    base: 0x2000,
                    total_size
                }
            ),
            FaultAction::NoAction,
            "total_size {total_size} is not the marker"
        );
    }
    assert!(!state.fired.load(Ordering::Relaxed), "not yet claimed");
    // The marker allocation is captured — identity recorded, no memory touched.
    assert_eq!(
        fault_event_armed(
            &state,
            FaultEvent::PostAlloc {
                base: 0xBEEF_0000,
                total_size: PLANT_MARKER_TOTAL,
            }
        ),
        FaultAction::CapturePlant
    );
    assert_eq!(state.planted_base.load(Ordering::Relaxed), 0xBEEF_0000);
    assert_eq!(
        state.planted_total_size.load(Ordering::Relaxed),
        PLANT_MARKER_TOTAL
    );
    // One shot: a second marker allocation is NOT captured.
    assert_eq!(
        fault_event_armed(
            &state,
            FaultEvent::PostAlloc {
                base: 0xCAFE_0000,
                total_size: PLANT_MARKER_TOTAL,
            }
        ),
        FaultAction::NoAction
    );
    assert_eq!(
        state.planted_base.load(Ordering::Relaxed),
        0xBEEF_0000,
        "the recorded identity is not overwritten"
    );
}

// The two ledger plants fire at their OWN event only, once, and take no other
// action. `M3Leak` suppresses one discharge; `M3OverFree` adds one.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.2 closed action set)
#[test]
fn ledger_plants_act_only_at_their_own_event_and_once() {
    let leak = PlantState::new(FaultPlant::M3Leak);
    let ev_alloc = || FaultEvent::PostAlloc {
        base: 0x3000,
        total_size: PLANT_MARKER_TOTAL,
    };
    let ev_pre = || FaultEvent::PreFree {
        base: 0x3000,
        total_size: PLANT_MARKER_TOTAL,
    };
    let ev_post = || FaultEvent::PostFree {
        base: 0x3000,
        total_size: PLANT_MARKER_TOTAL,
        withheld: false,
    };
    assert_eq!(
        fault_event_armed(&leak, ev_alloc()),
        FaultAction::NoAction,
        "a leak plant does not capture allocations"
    );
    assert_eq!(fault_event_armed(&leak, ev_post()), FaultAction::NoAction);
    assert_eq!(
        fault_event_armed(&leak, ev_pre()),
        FaultAction::SuppressFree
    );
    assert_eq!(
        fault_event_armed(&leak, ev_pre()),
        FaultAction::NoAction,
        "exactly one discharge is suppressed"
    );

    let over = PlantState::new(FaultPlant::M3OverFree);
    assert_eq!(fault_event_armed(&over, ev_alloc()), FaultAction::NoAction);
    assert_eq!(fault_event_armed(&over, ev_pre()), FaultAction::NoAction);
    assert_eq!(
        fault_event_armed(&over, ev_post()),
        FaultAction::ExtraDischarge
    );
    assert_eq!(
        fault_event_armed(&over, ev_post()),
        FaultAction::NoAction,
        "exactly one extra discharge"
    );
}

// Negative: the six identity-capturing plants NEVER take a ledger action — a
// mis-wired arm that let an A-row suppress a free would corrupt the M3 ledger
// evidence for every other row.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.2 closed action set)
#[test]
fn identity_plants_take_no_ledger_action() {
    for p in [
        FaultPlant::M1StaleReuse,
        FaultPlant::M2StaleRead,
        FaultPlant::A1ZeroRc,
        FaultPlant::A2InteriorPointer,
        FaultPlant::A3FreedPointer,
        FaultPlant::A4MalformedHeader,
    ] {
        let state = PlantState::new(p);
        for event in [
            FaultEvent::PreFree {
                base: 0x4000,
                total_size: PLANT_MARKER_TOTAL,
            },
            FaultEvent::PostFree {
                base: 0x4000,
                total_size: PLANT_MARKER_TOTAL,
                withheld: true,
            },
        ] {
            assert_eq!(
                fault_event_armed(&state, event),
                FaultAction::NoAction,
                "{} must not touch the ledger",
                p.spelling()
            );
        }
    }
}

// The report identity the committed e2e pins (`tests/intrinsics_m3_detection_s116.rs`
// asserts the plant spelling + `alloc` + `dealloc` + lowercase `parity`/`imbalance`).
// Only the two LEDGER plants can produce a parity imbalance, so only they get a
// line — a plant line on a non-ledger row would be a false claim.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.2 report identity)
#[test]
fn ledger_plant_report_line_matches_the_committed_e2e_identity() {
    for p in [FaultPlant::M3Leak, FaultPlant::M3OverFree] {
        let line = ledger_plant_line_for(p);
        assert!(line.contains(p.spelling()), "{line}");
        assert!(line.contains("alloc"), "{line}");
        assert!(line.contains("dealloc"), "{line}");
        assert!(line.contains("parity"), "lowercase parity: {line}");
        assert!(line.contains("imbalance"), "lowercase imbalance: {line}");
    }
    for p in FaultPlant::ALL {
        assert_eq!(
            p.is_ledger_plant(),
            matches!(p, FaultPlant::M3Leak | FaultPlant::M3OverFree),
            "{} ledger classification",
            p.spelling()
        );
    }
}

// ===========================================================================
// §7.3/§7.6 — the eight detection-proof triplets
// ===========================================================================
//
// Each row is a triplet of FRESH SUBPROCESSES: **positive** (plant + detector
// under test → the named observation + the expected failure mode), **clean
// control** (detector, no plant → normal exit, no report), **negative control**
// (plant, detector under test OFF → observation absent, no UB executed).
// Removing or bypassing a detector must make the committed positive FAIL rather
// than false-green — that is the fail-on-revert polarity
// `tests/plan/s118-test-plan.md` §3.1 makes a hard per-row acceptance input.
//
// ARMING DISCIPLINE (§7.1, arch ruling 3). Nothing here is armed in the parent
// process: no `set_var` anywhere (against a `LazyLock` ledger it is a silent
// no-op that merely LOOKS armed — the worst outcome for a detection proof), and
// no ambient `CRANELISP_*` is inherited. Every leg is a child `Command` with
// `.env_clear()` plus the enumerated allow-list in `spawn_child`.
//
// CHILD SHAPE (§7.6). Children re-exec this very test binary via
// `current_exe()`, selecting the child body by test name. Each child body is an
// ORDINARY non-`#[ignore]`d `#[test]` that returns immediately when unarmed, so
// (a) the normal suite executes every body unarmed on every run — acceptance
// item 4 as a continuously-executed property rather than a claim — and (b) no
// spec-bearing assertion hides behind `#[ignore]`.
//
// DEBUG-TWIN DISCRIMINATION (§7.5). In the debug profile each A-seam has two
// faces: the always-on `debug_assert!` twin (`panicked at …`) and the env-gated
// release check (`[CRANELISP RC/ALLOC SEAM VIOLATION]`). The triplets prove the
// RELEASE face and discriminate by PREFIX — the positive asserts it is present
// and names the plant's seam; the negative control asserts it is ABSENT. A
// negative-control child may still terminate abnormally through the twin: that
// is the UB containment doing its job, and it is recorded as the row's expected
// negative-control failure mode, never mistaken for the detector's observation.
//
// THE CHILDREN RUN IN THE DEBUG PROFILE by construction (the crate's test
// binary). The A2/A3/A4 negative controls depend on it: their containment is the
// debug twin. A release-profile child would need a different containment story.

use std::process::Command;

/// The located-hard-fail prefix — the RELEASE face the triplets prove.
const SEAM_PREFIX: &str = "[CRANELISP RC/ALLOC SEAM VIOLATION]";

// The detector variables, spelled once. Never set in this process; only ever
// handed to a child `Command`.
const M1_QUARANTINE: &str = "CRANELISP_QUARANTINE_FREED";
const M2_SCRUB: &str = "CRANELISP_SCRUB_FREED";
const M3_PARITY: &str = "CRANELISP_ALLOC_PARITY";
const A_GATE: &str = "CRANELISP_RC_DEC_CHECK";

/// One child run's captured outcome.
struct ChildRun {
    label: String,
    success: bool,
    output: String,
}

impl ChildRun {
    fn has(&self, needle: &str) -> bool {
        self.output.contains(needle)
    }

    #[track_caller]
    fn assert_contains(&self, needle: &str) {
        assert!(
            self.has(needle),
            "[{}] expected {needle:?} in child output:\n{}",
            self.label,
            self.output
        );
    }

    #[track_caller]
    fn assert_absent(&self, needle: &str) {
        assert!(
            !self.has(needle),
            "[{}] {needle:?} MUST NOT appear in child output:\n{}",
            self.label,
            self.output
        );
    }

    #[track_caller]
    fn assert_terminated_abnormally(&self) {
        assert!(
            !self.success,
            "[{}] child MUST terminate abnormally:\n{}",
            self.label, self.output
        );
    }

    #[track_caller]
    fn assert_exited_normally(&self) {
        assert!(
            self.success,
            "[{}] child MUST exit normally:\n{}",
            self.label, self.output
        );
    }

    /// The RELEASE face is present and names this seam, before any mutation.
    #[track_caller]
    fn assert_seam_rejection(&self, site: &str) {
        self.assert_contains(SEAM_PREFIX);
        self.assert_contains("PRECHECK rejected");
        self.assert_contains(site);
        self.assert_terminated_abnormally();
    }

    /// The RELEASE face is absent (the negative-control observation).
    #[track_caller]
    fn assert_no_seam_rejection(&self) {
        self.assert_absent(SEAM_PREFIX);
    }
}

/// The libtest name of a child body in this binary (`module::path::fn`, with the
/// crate name stripped — libtest names are crate-root-relative).
fn child_path(name: &str) -> String {
    let m = module_path!();
    let m = m.split_once("::").map(|(_, rest)| rest).unwrap_or(m);
    format!("{m}::{name}")
}

/// Spawn ONE fresh child: `env_clear` + an explicitly enumerated allow-list,
/// exactly one plant spelling (or none), the exact arm string, and the named
/// detectors. `CRANELISP_QUARANTINE_MAX_BYTES` is never set — a FIFO release
/// would reopen the reuse window the M1/A3/A4 rows depend on (§7.3 A4 note).
fn spawn_child(
    label: &str,
    child: &str,
    plant: Option<FaultPlant>,
    detectors: &[&str],
) -> ChildRun {
    let exe = std::env::current_exe().expect("current_exe for the plant child");
    let mut cmd = Command::new(&exe);
    cmd.env_clear();
    // The one inherited value: the dynamic-loader path this binary may need.
    if let Some(p) = std::env::var_os("LD_LIBRARY_PATH") {
        cmd.env("LD_LIBRARY_PATH", p);
    }
    for d in detectors {
        cmd.env(d, "1");
    }
    if let Some(p) = plant {
        cmd.env("CRANELISP_TEST_FAULTS", FAULT_ARM_VALUE)
            .env("CRANELISP_TEST_FAULT", p.spelling());
    }
    cmd.args([&child_path(child), "--exact", "--nocapture"]);
    let out = cmd.output().expect("spawn the plant child");
    let mut output = String::from_utf8_lossy(&out.stderr).into_owned();
    output.push_str(&String::from_utf8_lossy(&out.stdout));
    ChildRun {
        label: label.to_string(),
        success: out.status.success(),
        output,
    }
}

/// Is this process the armed child for `expect`? Every child body's first line.
fn armed_child_for(expect: FaultPlant) -> bool {
    fault_observation().plant == Some(expect)
}

/// A child body's proof that the hook captured the PRODUCTION allocation (not a
/// fixture-fabricated address).
fn assert_plant_captured(base: i64) {
    let obs = fault_observation();
    assert!(obs.fired, "the production PostAlloc event must have fired");
    assert_eq!(
        obs.planted_base, base,
        "the plant must name the production-allocated base"
    );
    assert_eq!(obs.planted_total_size, PLANT_MARKER_TOTAL);
    eprintln!(
        "PLANT-CAPTURED base={base:#x} total={}",
        obs.planted_total_size
    );
}

// ---------------------------------------------------------------------------
// The shared clean-control workload (detector on, NO plant)
// ---------------------------------------------------------------------------

/// A CORRECT heap workload through every seam the detectors watch: `rc_inc`,
/// `consume_shallow`, the drop-glue `atomic_dec_rc` funnel, `alloc_with_rc` and
/// `dealloc`. Every allocation is released, so an armed detector that fires here
/// is firing on a correct program.
///
/// Runs unarmed in the ordinary suite too (it is just a balanced heap workload);
/// the clean-control legs spawn it with a detector armed and no plant.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.3 clean controls)
#[test]
fn clean_heap_workload_balances_at_every_seam() {
    let before = (crate::alloc::alloc_count(), crate::alloc::dealloc_count());

    // A marker-size block, shared then released twice.
    let block = crate::alloc::alloc_with_rc(PLANT_MARKER_PAYLOAD) as i64;
    crate::rc::rc_inc(block);
    crate::rc::consume_shallow(block);
    crate::rc::consume_shallow(block);

    // A ragged-size HeapString (total 27 — NOT 8-aligned; the armed
    // header-plausibility precheck MUST accept it).
    let s = crate::heap_string::alloc_string(b"abc") as i64;
    crate::rc::rc_inc(s);
    crate::rc::consume_shallow(s);
    crate::rc::consume_shallow(s);

    // A scalar Sexp through the drop-glue funnel (`atomic_dec_rc`).
    let sexp = crate::alloc::alloc_with_rc(24) as i64;
    // SAFETY: `sexp` is a live 40-byte allocation; tag@16 and field0@24 are payload.
    unsafe {
        crate::heap_access::write_i64(sexp, 16, 0); // SexpInt
        crate::heap_access::write_i64(sexp, 24, 7);
    }
    crate::drop::consume_sexp(sexp);

    let after = (crate::alloc::alloc_count(), crate::alloc::dealloc_count());
    assert_eq!(
        after.0 - before.0,
        after.1 - before.1,
        "the clean workload must balance exactly"
    );
    eprintln!(
        "CLEAN-WORKLOAD balanced allocs={} deallocs={}",
        after.0, after.1
    );
}

// ---------------------------------------------------------------------------
// Child bodies (ordinary tests; each no-ops unless armed for its own plant)
// ---------------------------------------------------------------------------

// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.3 row M1StaleReuse)
#[test]
fn plant_child_m1_stale_reuse() {
    if !armed_child_for(FaultPlant::M1StaleReuse) {
        return;
    }
    let base = crate::alloc::alloc_with_rc(PLANT_MARKER_PAYLOAD) as i64;
    assert_plant_captured(base);

    // Free through the production funnel (rc 1 → 0 → `dealloc`).
    crate::rc::consume_shallow(base);
    let retained = fault_observation().quarantine_retained_bytes;
    eprintln!("M1-RETAINED bytes={retained}");

    if retained == 0 {
        // NEGATIVE-CONTROL leg (M1 off). The detector's own observable is zero
        // retention and the fixture STOPS here: touching a block the system
        // allocator has reclaimed would obtain the control's polarity by
        // executing UB, and asserting "the base IS re-handed" would encode a
        // system-allocator reuse assumption (§7.3 row note).
        eprintln!("M1-NO-RETENTION (control)");
        return;
    }

    // POSITIVE leg. The withheld base is never re-handed …
    let mut again = Vec::with_capacity(64);
    for _ in 0..64 {
        let p = crate::alloc::alloc_with_rc(PLANT_MARKER_PAYLOAD) as i64;
        assert_ne!(p, base, "a quarantined base was re-handed by alloc_with_rc");
        again.push(p);
    }
    eprintln!("M1-NOREUSE k=64");
    // … and a stale RC op on it is seam-rejected (the consequence M1 makes
    // deterministic: `is_live` stays false forever, and the M2 poison the row
    // also arms makes the header implausible).
    crate::rc::rc_inc(base);
    eprintln!("M1-NO-REJECTION");
    for p in again {
        crate::rc::consume_shallow(p);
    }
}

// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.3 row M2StaleRead)
#[test]
fn plant_child_m2_stale_read() {
    if !armed_child_for(FaultPlant::M2StaleRead) {
        return;
    }
    const SENTINEL: i64 = 0x5EED_5EED_5EED;
    let base = crate::alloc::alloc_with_rc(PLANT_MARKER_PAYLOAD) as i64;
    assert_plant_captured(base);
    // Fixture write (never the hook) through the single mechanical read/write
    // owner: a sentinel at payload@16.
    // SAFETY: `base` is a live marker allocation; offset 16 is its first payload word.
    unsafe { crate::heap_access::write_i64(base, 16, SENTINEL) };

    // Free through the production funnel. Both legs arm M1, so the block stays
    // MAPPED and the read below is never a read of unmapped memory.
    crate::rc::consume_shallow(base);
    // SAFETY: the block is withheld by M1 (quarantined, still mapped).
    let word = unsafe { crate::heap_access::read_i64(base, 16) };
    eprintln!("M2-READBACK word={word:#x}");

    if word == SENTINEL {
        // NEGATIVE-CONTROL leg (M2 off): the same read returns the pre-free
        // sentinel and no poison-derived rejection occurs.
        eprintln!("M2-NO-POISON (control)");
        return;
    }
    // POSITIVE leg: the freed payload reads EXACTLY the poison word …
    assert_eq!(
        word as u64, POISON_WORD,
        "a scrubbed payload must read exactly POISON_WORD"
    );
    eprintln!("M2-POISON exact");
    // … and a stale RC op on the poisoned base is seam-rejected.
    crate::rc::rc_inc(base);
    eprintln!("M2-NO-REJECTION");
}

// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.3 row M3Leak)
#[test]
fn plant_child_m3_leak() {
    if !armed_child_for(FaultPlant::M3Leak) {
        return;
    }
    let base = crate::alloc::alloc_with_rc(PLANT_MARKER_PAYLOAD) as i64;
    // The production discharge is SUPPRESSED at `PreFree`: the block is
    // genuinely leaked, so the ledger stays truthful.
    crate::rc::consume_shallow(base);
    let (allocs, deallocs) = (crate::alloc::alloc_count(), crate::alloc::dealloc_count());
    eprintln!("M3-LEDGER allocs={allocs} deallocs={deallocs}");
    assert!(
        allocs > deallocs,
        "a suppressed discharge must leave allocs > deallocs"
    );
    // The atexit parity check fires after this body returns (positive leg) or
    // does not exist at all (negative-control leg, parity off).
}

// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.3 row M3OverFree)
#[test]
fn plant_child_m3_over_free() {
    if !armed_child_for(FaultPlant::M3OverFree) {
        return;
    }
    let base = crate::alloc::alloc_with_rc(PLANT_MARKER_PAYLOAD) as i64;
    // One EXTRA ledger discharge at `PostFree` — no memory is freed twice.
    crate::rc::consume_shallow(base);
    let (allocs, deallocs) = (crate::alloc::alloc_count(), crate::alloc::dealloc_count());
    eprintln!("M3-LEDGER allocs={allocs} deallocs={deallocs}");
    assert!(
        deallocs > allocs,
        "the extra discharge must leave deallocs > allocs"
    );
}

// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.3 row A1ZeroRc)
#[test]
fn plant_child_a1_zero_rc() {
    if !armed_child_for(FaultPlant::A1ZeroRc) {
        return;
    }
    let base = crate::alloc::alloc_with_rc(PLANT_MARKER_PAYLOAD) as i64;
    assert_plant_captured(base);
    // Fixture write: zero the planted allocation's RC. The block stays LIVE
    // throughout, so the `is_live` twin never fires in either leg.
    // SAFETY: `base` is a live marker allocation; offset 8 is its rc word.
    unsafe { crate::heap_access::write_i64(base, 8, 0) };
    eprintln!("PLANT-APPLIED a1 rc=0");

    crate::rc::rc_inc(base);

    // NEGATIVE-CONTROL leg (gate off): the inc resurrected the block to rc=1;
    // the fixture frees it cleanly. Reaching this line at all is the control's
    // observation. (POSITIVE leg aborts inside `rc_inc`, before the `fetch_add`
    // — which the reported `rc=0` proves: post-mutation it would read 1.)
    // SAFETY: same live allocation.
    let rc = unsafe { crate::heap_access::read_i64(base, 8) };
    eprintln!("A1-NO-REJECTION rc={rc}");
    crate::rc::consume_shallow(base);
}

// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.3 row A2InteriorPointer)
#[test]
fn plant_child_a2_interior_pointer() {
    if !armed_child_for(FaultPlant::A2InteriorPointer) {
        return;
    }
    let base = crate::alloc::alloc_with_rc(PLANT_MARKER_PAYLOAD) as i64;
    assert_plant_captured(base);
    // Fixture write: an ADT-shaped tag at payload@16, so the INTERIOR address's
    // word@0 is a tag value (3) rather than an allocation size — the A2 face.
    // SAFETY: `base` is a live marker allocation; offsets 16/24 are payload.
    unsafe {
        crate::heap_access::write_i64(base, 16, 3);
        crate::heap_access::write_i64(base, 24, 0);
    }
    let interior = base + HeapHeader::SIZE as i64;
    eprintln!("PLANT-APPLIED a2 interior={interior:#x}");

    crate::rc::consume_shallow(interior);

    // Unreached in BOTH legs in the debug profile: the positive aborts at the
    // seam precheck; the negative control aborts at the `is_live` debug twin
    // (its recorded, contained failure mode — no `fetch_sub` is executed
    // either way, so no control obtains its polarity through UB).
    eprintln!("A2-NO-REJECTION");
    crate::rc::consume_shallow(base);
}

// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.3 row A3FreedPointer)
#[test]
fn plant_child_a3_freed_pointer() {
    if !armed_child_for(FaultPlant::A3FreedPointer) {
        return;
    }
    let base = crate::alloc::alloc_with_rc(PLANT_MARKER_PAYLOAD) as i64;
    assert_plant_captured(base);
    // Free through the production funnel; both legs arm M1+M2 so the base stays
    // MAPPED (containment) and poisoned.
    crate::rc::consume_shallow(base);
    eprintln!(
        "PLANT-APPLIED a3 freed base={base:#x} retained={}",
        fault_observation().quarantine_retained_bytes
    );

    // Route the stale dec through the drop-glue funnel (`atomic_dec_rc`) — the
    // ordinary entry point every recursive drop-glue leaf uses. No test calls
    // the seam directly.
    crate::drop::consume_closure(base);

    // Unreached in BOTH legs: positive aborts at the seam precheck; the
    // negative control aborts at the `is_live` twin before the `fetch_sub`.
    eprintln!("A3-NO-REJECTION");
}

// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.3 row A4MalformedHeader)
#[test]
fn plant_child_a4_malformed_header() {
    if !armed_child_for(FaultPlant::A4MalformedHeader) {
        return;
    }
    let base = crate::alloc::alloc_with_rc(PLANT_MARKER_PAYLOAD) as i64;
    assert_plant_captured(base);
    // Fixture write: a malformed header size. Both legs arm M1 UNCAPPED, so
    // `dealloc` never reaches `std::alloc::dealloc` and a wrong `Layout` is
    // never used to free (containment).
    // SAFETY: `base` is a live marker allocation; offset 0 is its size word.
    unsafe { crate::heap_access::write_i64(base, 0, 8) };
    eprintln!("PLANT-APPLIED a4 header=8");

    // SAFETY: `base` was returned by `alloc_with_rc` and has not been freed. The
    // header is deliberately malformed — which is the fault under test, and the
    // reason the precheck must reject BEFORE `Layout` construction.
    unsafe { crate::alloc::dealloc(base as *mut u8) };

    // Unreached in BOTH legs: positive aborts at the hoisted precheck; the
    // negative control aborts at the debug header-integrity twin.
    eprintln!("A4-NO-REJECTION");
}

// ---------------------------------------------------------------------------
// The eight row triplets (positive / clean control / negative control)
// ---------------------------------------------------------------------------

// Row M1 — quarantine. Positive: retention > 0, the base is never re-handed
// across K=64 same-layout requests, and a stale `rc_inc` on it is seam-rejected.
// Fail-on-revert: with quarantine reverted (`scrub_and_dispose` never
// withholding) the positive's `M1-RETAINED bytes=<non-zero>` and the seam
// rejection both disappear — the child takes the control branch and EXITS
// NORMALLY, so `assert_terminated_abnormally` fails.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.3 row M1StaleReuse)
#[test]
fn m1_quarantine_detection_triplet() {
    let pos = spawn_child(
        "M1 positive",
        "plant_child_m1_stale_reuse",
        Some(FaultPlant::M1StaleReuse),
        &[M1_QUARANTINE, M2_SCRUB, A_GATE],
    );
    pos.assert_contains("PLANT-CAPTURED");
    pos.assert_contains(&format!("M1-RETAINED bytes={PLANT_MARKER_TOTAL}"));
    pos.assert_contains("M1-NOREUSE k=64");
    pos.assert_seam_rejection("rc_inc");
    pos.assert_absent("M1-NO-REJECTION");

    let clean = spawn_child(
        "M1 clean control",
        "clean_heap_workload_balances_at_every_seam",
        None,
        &[M1_QUARANTINE, M2_SCRUB, A_GATE],
    );
    clean.assert_contains("CLEAN-WORKLOAD balanced");
    clean.assert_no_seam_rejection();
    clean.assert_absent("M1StaleReuse");
    clean.assert_exited_normally();

    let neg = spawn_child(
        "M1 negative control (quarantine OFF)",
        "plant_child_m1_stale_reuse",
        Some(FaultPlant::M1StaleReuse),
        &[M2_SCRUB, A_GATE],
    );
    neg.assert_contains("M1-RETAINED bytes=0");
    neg.assert_contains("M1-NO-RETENTION (control)");
    neg.assert_no_seam_rejection();
    neg.assert_exited_normally();
}

// Row M2 — scrub. Positive: the freed payload reads EXACTLY `POISON_WORD` through
// the shared `heap_access` accessor, then the stale RC op is seam-rejected.
// Fail-on-revert: with scrubbing reverted the read returns the pre-free sentinel,
// the child takes the control branch and exits normally — the positive's
// `M2-POISON exact` and seam assertions both fail.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.3 row M2StaleRead)
#[test]
fn m2_scrub_detection_triplet() {
    let pos = spawn_child(
        "M2 positive",
        "plant_child_m2_stale_read",
        Some(FaultPlant::M2StaleRead),
        &[M1_QUARANTINE, M2_SCRUB, A_GATE],
    );
    pos.assert_contains("PLANT-CAPTURED");
    pos.assert_contains("M2-POISON exact");
    pos.assert_seam_rejection("rc_inc");
    pos.assert_absent("M2-NO-REJECTION");

    let clean = spawn_child(
        "M2 clean control",
        "clean_heap_workload_balances_at_every_seam",
        None,
        &[M1_QUARANTINE, M2_SCRUB, A_GATE],
    );
    clean.assert_contains("CLEAN-WORKLOAD balanced");
    clean.assert_no_seam_rejection();
    clean.assert_exited_normally();

    let neg = spawn_child(
        "M2 negative control (scrub OFF)",
        "plant_child_m2_stale_read",
        Some(FaultPlant::M2StaleRead),
        &[M1_QUARANTINE, A_GATE],
    );
    neg.assert_contains("M2-NO-POISON (control)");
    neg.assert_no_seam_rejection();
    neg.assert_exited_normally();
}

// Row M3 leak — the suppressed discharge reaches the real always-on counters,
// the atexit report (naming the plant), then abnormal termination.
// Fail-on-revert: with the atexit parity check reverted the child exits 0 with no
// report — both the abnormal-termination and the report assertions fail.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.3 row M3Leak)
#[test]
fn m3_leak_detection_triplet() {
    let pos = spawn_child(
        "M3 leak positive",
        "plant_child_m3_leak",
        Some(FaultPlant::M3Leak),
        &[M3_PARITY],
    );
    pos.assert_contains("M3-LEDGER");
    pos.assert_contains("test-fault plant M3Leak fired");
    pos.assert_contains("[ALLOC_PARITY] IMBALANCE");
    pos.assert_contains("LEAK (allocs > deallocs");
    pos.assert_contains("ALLOC_COUNT=");
    pos.assert_terminated_abnormally();

    let clean = spawn_child(
        "M3 clean control",
        "clean_heap_workload_balances_at_every_seam",
        None,
        &[M3_PARITY],
    );
    clean.assert_contains("CLEAN-WORKLOAD balanced");
    clean.assert_absent("[ALLOC_PARITY]");
    clean.assert_absent("M3Leak");
    clean.assert_exited_normally();

    let neg = spawn_child(
        "M3 leak negative control (parity OFF)",
        "plant_child_m3_leak",
        Some(FaultPlant::M3Leak),
        &[],
    );
    neg.assert_contains("M3-LEDGER");
    neg.assert_absent("[ALLOC_PARITY]");
    neg.assert_exited_normally();
}

// Row M3 over-free — the `deallocs > allocs` report polarity + atexit wiring.
// HONESTY (§7.2): this proves the polarity and the wiring, NOT a real
// double-free; the real double-free face is the debug `LIVE_ALLOCS.remove`
// assert. `/qa`'s regrade must grade it there, not higher.
// Fail-on-revert: with the atexit check reverted the child exits 0 with no report.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.3 row M3OverFree)
#[test]
fn m3_over_free_detection_triplet() {
    let pos = spawn_child(
        "M3 over-free positive",
        "plant_child_m3_over_free",
        Some(FaultPlant::M3OverFree),
        &[M3_PARITY],
    );
    pos.assert_contains("M3-LEDGER");
    pos.assert_contains("test-fault plant M3OverFree fired");
    pos.assert_contains("[ALLOC_PARITY] IMBALANCE");
    pos.assert_contains("DOUBLE-FREE (deallocs > allocs");
    pos.assert_terminated_abnormally();

    let clean = spawn_child(
        "M3 over-free clean control",
        "clean_heap_workload_balances_at_every_seam",
        None,
        &[M3_PARITY],
    );
    clean.assert_absent("[ALLOC_PARITY]");
    clean.assert_absent("M3OverFree");
    clean.assert_exited_normally();

    let neg = spawn_child(
        "M3 over-free negative control (parity OFF)",
        "plant_child_m3_over_free",
        Some(FaultPlant::M3OverFree),
        &[],
    );
    neg.assert_contains("M3-LEDGER");
    neg.assert_absent("[ALLOC_PARITY]");
    neg.assert_exited_normally();
}

// Row A1 — the `rc_inc` release face. Positive: the seam names `rc_inc` and
// reports `rc=0`, which is the BEFORE-the-`fetch_add` proof (post-mutation it
// would report `rc=1`).
// Fail-on-revert: with the precheck reverted (or moved back below the RMW) the
// child resurrects the block to rc=1, prints `A1-NO-REJECTION rc=1` and exits 0.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.3 row A1ZeroRc, §7.5)
#[test]
fn a1_zero_rc_detection_triplet() {
    let pos = spawn_child(
        "A1 positive",
        "plant_child_a1_zero_rc",
        Some(FaultPlant::A1ZeroRc),
        &[A_GATE],
    );
    pos.assert_contains("PLANT-APPLIED a1 rc=0");
    pos.assert_seam_rejection("rc_inc");
    pos.assert_contains("rc=0");
    pos.assert_absent("A1-NO-REJECTION");

    let clean = spawn_child(
        "A1 clean control",
        "clean_heap_workload_balances_at_every_seam",
        None,
        &[A_GATE],
    );
    clean.assert_contains("CLEAN-WORKLOAD balanced");
    clean.assert_no_seam_rejection();
    clean.assert_exited_normally();

    let neg = spawn_child(
        "A1 negative control (gate OFF)",
        "plant_child_a1_zero_rc",
        Some(FaultPlant::A1ZeroRc),
        &[],
    );
    neg.assert_contains("A1-NO-REJECTION rc=1");
    neg.assert_no_seam_rejection();
    neg.assert_exited_normally();
}

// Row A2 — the `consume_shallow` release face on an interior (non-base) address.
// Positive: the header-plausibility predicate rejects `alloc_size=3` before the
// `fetch_sub`. Negative control: the debug `is_live` twin aborts the child
// BEFORE the RMW — the recorded, contained negative failure mode; the seam prefix
// is absent, which is the row's observation.
// Fail-on-revert: with the precheck reverted the armed leg falls through to the
// debug twin, so the seam prefix disappears and the positive fails.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.3 row A2InteriorPointer, §7.5)
#[test]
fn a2_interior_pointer_detection_triplet() {
    let pos = spawn_child(
        "A2 positive",
        "plant_child_a2_interior_pointer",
        Some(FaultPlant::A2InteriorPointer),
        &[A_GATE],
    );
    pos.assert_contains("PLANT-APPLIED a2 interior=");
    pos.assert_seam_rejection("consume_shallow");
    pos.assert_contains("alloc_size=3");
    pos.assert_absent("A2-NO-REJECTION");

    let clean = spawn_child(
        "A2 clean control",
        "clean_heap_workload_balances_at_every_seam",
        None,
        &[A_GATE],
    );
    clean.assert_contains("CLEAN-WORKLOAD balanced");
    clean.assert_no_seam_rejection();
    clean.assert_exited_normally();

    let neg = spawn_child(
        "A2 negative control (gate OFF)",
        "plant_child_a2_interior_pointer",
        Some(FaultPlant::A2InteriorPointer),
        &[],
    );
    neg.assert_no_seam_rejection();
    neg.assert_contains("STALE RC DEC (consume_shallow)");
    neg.assert_absent("A2-NO-REJECTION");
}

// Row A3 — the drop-glue `atomic_dec_rc` release face on a logically-freed
// (M1-retained, M2-poisoned) base, reached through the ordinary
// `drop::consume_closure` entry point. Negative control: the `is_live` twin
// aborts before the RMW (contained by M1 keeping the base mapped).
// Fail-on-revert: with the precheck reverted the armed leg falls through to the
// twin and the seam prefix disappears.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.3 row A3FreedPointer, §7.5)
#[test]
fn a3_freed_pointer_detection_triplet() {
    let pos = spawn_child(
        "A3 positive",
        "plant_child_a3_freed_pointer",
        Some(FaultPlant::A3FreedPointer),
        &[M1_QUARANTINE, M2_SCRUB, A_GATE],
    );
    pos.assert_contains("PLANT-APPLIED a3 freed");
    pos.assert_seam_rejection("atomic_dec_rc (drop glue)");
    pos.assert_absent("A3-NO-REJECTION");

    let clean = spawn_child(
        "A3 clean control",
        "clean_heap_workload_balances_at_every_seam",
        None,
        &[M1_QUARANTINE, M2_SCRUB, A_GATE],
    );
    clean.assert_contains("CLEAN-WORKLOAD balanced");
    clean.assert_no_seam_rejection();
    clean.assert_exited_normally();

    let neg = spawn_child(
        "A3 negative control (gate OFF)",
        "plant_child_a3_freed_pointer",
        Some(FaultPlant::A3FreedPointer),
        &[M1_QUARANTINE, M2_SCRUB],
    );
    neg.assert_no_seam_rejection();
    neg.assert_contains("STALE RC DEC (drop glue)");
    neg.assert_absent("A3-NO-REJECTION");
}

// Row A4 — the `dealloc` release face on a malformed header, rejected BEFORE
// `Layout` construction and disposal. Both legs arm M1 uncapped so a wrong
// `Layout` is never used to free (and `CRANELISP_QUARANTINE_MAX_BYTES` is never
// set — a FIFO release would defeat that containment). Negative control: the
// debug header-integrity twin aborts first.
// Fail-on-revert: with the hoisted precheck reverted to its old position (below
// the debug block) the armed leg trips the twin instead and the seam prefix
// disappears — which is exactly why the hoist is itself a detected regression.
// spec: 12-runtime §12.3 — R8 (diagnostic-modes §7.3 row A4MalformedHeader, §7.5)
#[test]
fn a4_malformed_header_detection_triplet() {
    let pos = spawn_child(
        "A4 positive",
        "plant_child_a4_malformed_header",
        Some(FaultPlant::A4MalformedHeader),
        &[M1_QUARANTINE, A_GATE],
    );
    pos.assert_contains("PLANT-APPLIED a4 header=8");
    pos.assert_seam_rejection("dealloc:");
    pos.assert_contains("alloc_size 8");
    pos.assert_absent("A4-NO-REJECTION");

    let clean = spawn_child(
        "A4 clean control",
        "clean_heap_workload_balances_at_every_seam",
        None,
        &[M1_QUARANTINE, A_GATE],
    );
    clean.assert_contains("CLEAN-WORKLOAD balanced");
    clean.assert_no_seam_rejection();
    clean.assert_exited_normally();

    let neg = spawn_child(
        "A4 negative control (gate OFF)",
        "plant_child_a4_malformed_header",
        Some(FaultPlant::A4MalformedHeader),
        &[M1_QUARANTINE],
    );
    neg.assert_no_seam_rejection();
    neg.assert_contains("HEAP HEADER CORRUPTED");
    neg.assert_absent("A4-NO-REJECTION");
}
