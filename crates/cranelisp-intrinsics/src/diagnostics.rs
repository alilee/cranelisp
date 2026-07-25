//! Memory-safety diagnostic modes (tier-5) + the release variant of the RC/alloc
//! seam asserts (tier-3).
//!
//! Design: `design/intrinsics/diagnostic-modes.md` (the R8 `dynamic-lane`
//! mechanism of `design/arch/safety-invariants.md` §4). Three independent,
//! default-OFF, process-start env-gated allocator behaviours plus the release
//! variant of the seam checks. All hook the two existing single-sourced funnels
//! (`alloc::alloc_with_rc`, `alloc::dealloc`) plus the two always-on counters —
//! nothing new is tracked.
//!
//! | Env var | Mode | Effect |
//! |---|---|---|
//! | `CRANELISP_QUARANTINE_FREED` | M1 | withhold freed blocks from the system allocator (no reuse) |
//! | `CRANELISP_QUARANTINE_MAX_BYTES=N` | M1 cap | FIFO-release the oldest withheld blocks once retained bytes exceed `N` |
//! | `CRANELISP_SCRUB_FREED` | M2 | poison header+payload with `0xDEAD2FEE_DEAD2FEE` at the free seam |
//! | `CRANELISP_ALLOC_PARITY` | M3 | atexit hard-check `ALLOC_COUNT == DEALLOC_COUNT` (+ empty live-set in debug); dump then abort on imbalance |
//! | `CRANELISP_ALLOC_PARITY_DUMP` | M3 dump | atexit print-and-continue ledger, no abort |
//! | `CRANELISP_RC_DEC_CHECK` | A1–A4 | release-gate the RC/alloc seam checks (reuses the existing dec-check gate) |
//!
//! **Byte-identical-off (hard discipline):** with every var unset each op runs
//! exactly today's code — one cached bool load per gate, no branch taken, no
//! quarantine list constructed, no atexit registered. The modes are Rust bodies
//! inside the intrinsic funnels, not codegen — no emitted-IR change, no ABI /
//! catalog / `cranelisp-types` surface, identical in `--run`/REPL/`--link`.
//!
//! **Composition + fixed order** inside `dealloc` (design §4): capture
//! `FREED_TRACKED` identity → (M2) scrub → (M1) quarantine-or-release → bump
//! `DEALLOC_COUNT`. The three gates are independent and compose freely.

use std::alloc::Layout;
use std::collections::VecDeque;
use std::sync::atomic::{AtomicBool, AtomicI64, AtomicUsize, Ordering};
use std::sync::{LazyLock, Mutex};

use cranelisp_types::HeapHeader;

// ---------------------------------------------------------------------------
// Env gates (cached at process start; one bool load per query when off)
// ---------------------------------------------------------------------------

/// M1 — withhold freed blocks so a freed address is never re-handed by
/// `alloc_with_rc` (`is_live` stays `false` forever ⇒ the stale-dec asserts fire
/// deterministically). Off ⇒ the quarantine list is never constructed.
#[inline]
pub(crate) fn quarantine_enabled() -> bool {
    static E: LazyLock<bool> =
        LazyLock::new(|| std::env::var_os("CRANELISP_QUARANTINE_FREED").is_some());
    *E
}

/// M1 retention cap in bytes. `None` ⇒ unbounded (the repro/lane default —
/// every freed block is kept). `Some(n)` ⇒ FIFO-release the coldest blocks once
/// retained bytes exceed `n`.
#[inline]
fn quarantine_max_bytes() -> Option<usize> {
    static E: LazyLock<Option<usize>> = LazyLock::new(|| {
        std::env::var("CRANELISP_QUARANTINE_MAX_BYTES")
            .ok()
            .and_then(|v| v.trim().parse::<usize>().ok())
    });
    *E
}

/// M2 — poison the whole allocation (header + payload) at the free seam.
#[inline]
pub(crate) fn scrub_enabled() -> bool {
    static E: LazyLock<bool> =
        LazyLock::new(|| std::env::var_os("CRANELISP_SCRUB_FREED").is_some());
    *E
}

/// M3 — the located hard-check face (abort on imbalance at exit).
#[inline]
fn parity_hard_enabled() -> bool {
    static E: LazyLock<bool> =
        LazyLock::new(|| std::env::var_os("CRANELISP_ALLOC_PARITY").is_some());
    *E
}

/// M3 — the print-and-continue dump face (no abort).
#[inline]
fn parity_dump_enabled() -> bool {
    static E: LazyLock<bool> =
        LazyLock::new(|| std::env::var_os("CRANELISP_ALLOC_PARITY_DUMP").is_some());
    *E
}

/// A1–A4 release gate — reuses the existing `CRANELISP_RC_DEC_CHECK` env so a
/// release/`--link` lane opts in to the seam checks without a new flag (design
/// §5). Off ⇒ the release-variant `if` never fires (the debug `debug_assert!`s
/// are unaffected — they are always-on in debug).
#[inline]
pub(crate) fn rc_check_release_enabled() -> bool {
    static E: LazyLock<bool> =
        LazyLock::new(|| std::env::var_os("CRANELISP_RC_DEC_CHECK").is_some());
    *E
}

/// Registers the M3 atexit parity check the first time either parity gate is
/// observed on. Called once per `alloc_with_rc` (a single cached bool load when
/// off). Idempotent — the `LazyLock` body runs at most once.
#[inline]
pub(crate) fn ensure_parity_registered() {
    static REGISTERED: LazyLock<bool> = LazyLock::new(|| {
        if parity_hard_enabled() || parity_dump_enabled() {
            // SAFETY: `check_alloc_parity_atexit` is a plain `extern "C" fn()`
            // with no arguments — the shape `libc::atexit` requires.
            unsafe {
                libc::atexit(check_alloc_parity_atexit);
            }
        }
        true
    });
    let _ = *REGISTERED;
}

// ---------------------------------------------------------------------------
// A1–A4 — the located seam hard-fail (tier-3, in-process invariant breach)
// ---------------------------------------------------------------------------

/// Report a RC/alloc seam-invariant breach to stderr and abort non-zero. An
/// in-process invariant breach is a compiler defect (ladder §2.3) — a located
/// hard-fail, never release UB and never a laundered `Result`.
#[cold]
#[inline(never)]
pub(crate) fn seam_hard_fail(msg: &str) -> ! {
    eprintln!("[CRANELISP RC/ALLOC SEAM VIOLATION] {msg}");
    std::process::abort();
}

// ---------------------------------------------------------------------------
// §7.5 — the shared seam PREcheck (validation strictly before mutation)
// ---------------------------------------------------------------------------
//
// The single owner (Principle 7) of the env-gated RC/alloc seam validation.
// Hoisted to the TOP of `rc::rc_inc`, `rc::consume_shallow` and
// `drop::atomic_dec_rc` — above the RMW they guard AND above the always-on
// `debug_assert!` twins. Two reasons, both load-bearing (design §7.5):
//
//  1. **Validation before mutation** (Principle 25 — a narrowing whose check
//     runs after the narrowed operation is not a check). The pre-S118 shape
//     ran every gated check AFTER its `fetch_add`/`fetch_sub`, so the seam
//     could only ever report a mutation it had already performed.
//  2. **The debug twins pre-empt the gate.** Unit/e2e children run in the
//     debug profile where `debug_assert!(is_live(..))` is live; a planted
//     fault trips the twin and the gated check is never reached, so a
//     detection proof would fail against a *working* detector.
//
// The post-RMW gates in those three seams deliberately STAY: the precheck
// covers the single-threaded planted case, the post-RMW check keeps the
// concurrent-race window. Both emit the same `[CRANELISP RC/ALLOC SEAM
// VIOLATION]` prefix.
//
// Byte-identical-off: armed only by `CRANELISP_RC_DEC_CHECK`, whose cached
// bool load is already on these paths — no new load, branch, or emitted IR.

/// Is `alloc_size` (the word at base+0) a plausible allocation size?
///
/// The **release face** of "the target is a live allocation base". The
/// `is_live` half needs the `#[cfg(debug_assertions)]` `LIVE_ALLOCS` side
/// table, so the release lane has never had one; this is its honest
/// approximation, and `/qa`'s R8 regrade must grade it at that tier — a
/// **plausibility check, not a proof of basehood** (design §7.5).
///
/// It rejects exactly two shapes the plants exercise:
/// - an **interior / non-base** address, whose word@0 is an ADT tag, a length,
///   or a field value rather than a size (A2);
/// - a **poisoned or otherwise clobbered** base, whose word@0 is
///   `0xDEAD2FEE_DEAD2FEE` — negative as an `i64`, and far past any layout
///   Rust can construct when read as a `usize` (A3, A4).
///
/// Deliberately NOT part of the predicate: 8-alignment of the *size value*.
/// `HeapString`'s payload is `8 + byte_len` **raw bytes**, so a legitimate
/// 3-byte string's `alloc_size` is `27` — an alignment clause on the size
/// would hard-fail every string dec in the armed lane. The Layout-validity
/// clause achieves the design's stated goal (a located seam message instead of
/// a `Layout` panic on a poisoned header) without that false-positive class.
#[inline]
pub(crate) fn header_size_plausible(alloc_size: i64) -> bool {
    match usize::try_from(alloc_size) {
        Ok(size) => size >= HeapHeader::SIZE && Layout::from_size_align(size, 8).is_ok(),
        Err(_) => false,
    }
}

/// The precheck predicate, pure over the two header words it reads, so both
/// polarities are unit-testable without arming a gate or aborting a process
/// (Principle 5). `None` ⇒ accept; `Some(reason)` ⇒ reject with `reason`.
pub(crate) fn seam_precheck_verdict(alloc_size: i64, rc: i64) -> Option<&'static str> {
    if !header_size_plausible(alloc_size) {
        return Some(
            "header alloc_size is not a plausible allocation size (< HeapHeader::SIZE, \
             negative, or no valid Layout) — an interior/non-base address, or a \
             poisoned/quarantined base",
        );
    }
    if rc <= 0 {
        return Some("rc is <= 0 — the target was already released (stale/poisoned)");
    }
    None
}

/// Validate an alleged heap base at an RC seam **before** the seam mutates it.
/// No-op unless [`rc_check_release_enabled`]; on rejection, a located
/// [`seam_hard_fail`] naming `site`, the pointer, and which predicate failed.
///
/// Callers MUST have applied the nullary-tag guard first (a bare Mixed-category
/// tag is not a heap pointer and has no header to read).
///
/// Fault risk is a signal, not a regression: the armed precheck dereferences
/// the alleged base's first two words, so a wholly wild pointer may fault at
/// the read — a located crash AT the offending seam, strictly better than the
/// silent RMW it replaces, and reachable only with the gate armed.
#[inline]
pub(crate) fn seam_precheck(ptr: i64, site: &'static str) {
    if !rc_check_release_enabled() {
        return;
    }
    seam_precheck_armed(ptr, site);
}

/// The armed body of [`seam_precheck`], out-of-line so the off path stays one
/// cached bool load.
#[inline(never)]
fn seam_precheck_armed(ptr: i64, site: &'static str) {
    // SAFETY: `ptr` is the alleged base of a heap allocation at an RC seam
    // (past the nullary-tag guard). Reading the two header words is exactly
    // what the seam is about to do to the RC field; see the fault-risk note.
    let alloc_size = unsafe { crate::heap_access::read_i64(ptr, 0) };
    let rc =
        unsafe { &*((ptr as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const AtomicI64) }
            .load(Ordering::Relaxed);
    if let Some(why) = seam_precheck_verdict(alloc_size, rc) {
        seam_hard_fail(&format!(
            "{site}: PRECHECK rejected ptr {ptr:#x} BEFORE mutation — {why} \
             (header alloc_size={alloc_size}, rc={rc})"
        ));
    }
}

// ---------------------------------------------------------------------------
// §7.1/§7.2 — the closed test-only fault-plant protocol (crate-private)
// ---------------------------------------------------------------------------
//
// The injection seam is **crate-private and diagnostic-test-only in purpose**,
// but is compiled into the executable so an e2e subprocess can prove the real
// counter→atexit→report→abort wiring through the production binary. It adds no
// `pub` item, catalog entry, exported symbol, Cargo feature, ABI, heap-layout,
// or emitted-IR change.
//
// **Both sets are CLOSED** (Principle 6 — this enumeration IS the complexity
// budget, and what stops a general fault API from growing here):
//
// | Event | Site | Legal actions |
// |---|---|---|
// | `PostAlloc` | `alloc_with_rc`, after header + counters + tracking | `NoAction`, `CapturePlant` |
// | `PreFree`   | `dealloc`, after the `total_size` read, before the debug block | `NoAction`, `SuppressFree` |
// | `PostFree`  | `dealloc`, after the `DEALLOC_COUNT` bump | `NoAction`, `ExtraDischarge` |
//
// The hook only ever OBSERVES (`CapturePlant`) or applies one of the two closed
// ledger actions. **Every corruption is a FIXTURE write** through
// `heap_access::write_i64` against the production-allocated identity the hook
// recorded — zeroing an RC (A1), forming an interior address (A2), writing a
// bogus header (A4), the pre-free sentinel (M2). That separation is what keeps
// this from becoming an arbitrary-pointer-write API while every plant still
// acts on a real production allocation (Principle 5). There are deliberately no
// counter setters, no callback registration, and no replacement allocator; RC
// plants enter through the ordinary `rc_inc`/`consume_shallow`/`atomic_dec_rc`
// entry points and no test calls `seam_hard_fail` directly.
//
// **Arming is lane-scoped by construction** (§7.1, arch ruling 3): both exact
// child-environment values are required, arming is legal ONLY inside a spawned
// child `Command` with `.env_clear()` plus an enumerated allow-list, and
// `std::env::set_var` is never used — every gate is a `LazyLock` read once per
// process and the ledger + quarantine are process-global, so an in-process
// toggle is an order-dependent no-op that merely LOOKS armed.

/// The protocol-version arm string. Keeps its `s116-` spelling deliberately: it
/// is the protocol version, not the sprint of landing, and the committed e2e
/// children (`tests/intrinsics_m3_detection_s116.rs`) pin it — changing it would
/// silently disarm those cells.
pub(crate) const FAULT_ARM_VALUE: &str = "s116-detection-proof-v1";

/// The exact marker payload size the row fixtures allocate so a plant can select
/// ONE deterministic production identity by size — no address guessing. Chosen
/// as a size the compiler never emits in a plant child.
pub(crate) const PLANT_MARKER_PAYLOAD: usize = 776;

/// The `total_size` a marker allocation reports at `PostAlloc`.
const PLANT_MARKER_TOTAL: usize = HeapHeader::SIZE + PLANT_MARKER_PAYLOAD;

/// The closed set of plants — the eight spellings
/// `tests/plan/s118-test-plan.md` §3.1 names, one per detector row.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(crate) enum FaultPlant {
    /// M1 — free a marker block, then observe retention / non-reuse and a
    /// seam-rejected stale RC op on the withheld base.
    M1StaleReuse,
    /// M2 — free a marker block carrying a sentinel, then read poison back.
    M2StaleRead,
    /// M3 — suppress exactly one production discharge (a genuine leak).
    M3Leak,
    /// M3 — one extra ledger discharge (no memory is freed twice).
    M3OverFree,
    /// A1 — zero a marker block's RC, then `rc_inc` it.
    A1ZeroRc,
    /// A2 — hand an interior (non-base) address to a dec funnel.
    A2InteriorPointer,
    /// A3 — dec a logically-freed (M1-retained) base.
    A3FreedPointer,
    /// A4 — corrupt a marker block's header, then `dealloc` it.
    A4MalformedHeader,
}

impl FaultPlant {
    /// The exact env spelling / report identity of this plant.
    pub(crate) const fn spelling(self) -> &'static str {
        match self {
            FaultPlant::M1StaleReuse => "M1StaleReuse",
            FaultPlant::M2StaleRead => "M2StaleRead",
            FaultPlant::M3Leak => "M3Leak",
            FaultPlant::M3OverFree => "M3OverFree",
            FaultPlant::A1ZeroRc => "A1ZeroRc",
            FaultPlant::A2InteriorPointer => "A2InteriorPointer",
            FaultPlant::A3FreedPointer => "A3FreedPointer",
            FaultPlant::A4MalformedHeader => "A4MalformedHeader",
        }
    }

    /// The eight spellings, in declaration order (unit-matrix + parse coverage).
    pub(crate) const ALL: [FaultPlant; 8] = [
        FaultPlant::M1StaleReuse,
        FaultPlant::M2StaleRead,
        FaultPlant::M3Leak,
        FaultPlant::M3OverFree,
        FaultPlant::A1ZeroRc,
        FaultPlant::A2InteriorPointer,
        FaultPlant::A3FreedPointer,
        FaultPlant::A4MalformedHeader,
    ];

    fn parse(s: &str) -> Option<FaultPlant> {
        FaultPlant::ALL.into_iter().find(|p| p.spelling() == s)
    }

    /// Does this plant inject an alloc/free LEDGER fault? Only these two can
    /// produce a parity imbalance, so only these two prepend the plant-identity
    /// line to the M3 atexit report (§7.2 report identity).
    const fn is_ledger_plant(self) -> bool {
        matches!(self, FaultPlant::M3Leak | FaultPlant::M3OverFree)
    }
}

/// The three lifecycle events the two production funnels report.
pub(crate) enum FaultEvent {
    /// `alloc_with_rc`, after header init + counters + tracking.
    PostAlloc { base: i64, total_size: usize },
    /// `dealloc`, after the `total_size` header read, before the debug block.
    PreFree { base: i64, total_size: usize },
    /// `dealloc`, after the `DEALLOC_COUNT` bump.
    PostFree {
        base: i64,
        total_size: usize,
        /// Whether M1 withheld the block instead of releasing it. Part of the
        /// §7.2 payload contract (a fixture-visible property of the free that
        /// just happened); no action in the closed set consumes it today, and it
        /// is NOT dropped from the event — narrowing the payload would make a
        /// future ledger action re-derive it at the seam.
        #[allow(dead_code)]
        withheld: bool,
    },
}

/// The three actions a funnel may be asked to take, and nothing else.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(crate) enum FaultAction {
    /// The only action on the unarmed path.
    NoAction,
    /// Record `(base, total_size)` in the one-shot plant slot. No memory is
    /// touched — this is how a fixture obtains a *production-allocated*
    /// identity to corrupt or observe.
    CapturePlant,
    /// `dealloc` returns immediately: no `LIVE_ALLOCS` removal, no
    /// scrub/quarantine, no `DEALLOC_COUNT` bump. The block is **genuinely
    /// leaked**, so M3's ledger stays truthful.
    SuppressFree,
    /// Bump `DEALLOC_COUNT` once more without touching memory. **Honesty note
    /// for the 0857 regrade:** this is the only UB-free route to the
    /// `deallocs > allocs` polarity, so the M3 over-free row proves the *report
    /// polarity and atexit wiring*, not a real double-free. The real
    /// double-free face remains the debug `LIVE_ALLOCS.remove` assert (A4/§3) —
    /// grade it there, not higher.
    ExtraDischarge,
}

/// The one-shot plant slot. `fired` is claimed by compare/exchange, so a plant
/// fires at most once however many events reach the hook.
struct PlantState {
    plant: FaultPlant,
    fired: AtomicBool,
    planted_base: AtomicI64,
    planted_total_size: AtomicUsize,
}

impl PlantState {
    fn new(plant: FaultPlant) -> PlantState {
        PlantState {
            plant,
            fired: AtomicBool::new(false),
            planted_base: AtomicI64::new(0),
            planted_total_size: AtomicUsize::new(0),
        }
    }

    /// Claim the single shot. `true` for exactly one caller.
    fn claim(&self, base: i64, total_size: usize) -> bool {
        if self
            .fired
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            return false;
        }
        self.planted_base.store(base, Ordering::Relaxed);
        self.planted_total_size.store(total_size, Ordering::Relaxed);
        true
    }
}

/// A test-configuration error in the arm/spelling pair. Never a partial plant:
/// the parse is total and the hook hard-fails on it rather than arming
/// something the fixture did not ask for.
enum PlantSpec {
    /// Arm variable absent or any other value ⇒ fully off, no state at all.
    Off,
    Armed(FaultPlant),
    ConfigError(String),
}

/// Parse the `(CRANELISP_TEST_FAULTS, CRANELISP_TEST_FAULT)` pair. Pure over its
/// inputs so every negative polarity (absent / wrong arm / empty / unknown /
/// multiple spellings) is unit-testable without touching a process environment.
fn parse_plant_spec(arm: Option<&str>, spelling: Option<&str>) -> PlantSpec {
    match arm {
        Some(a) if a == FAULT_ARM_VALUE => {}
        // Absent, non-UTF8, or any other value: fully off.
        _ => return PlantSpec::Off,
    }
    let raw = match spelling {
        Some(s) => s,
        None => {
            return PlantSpec::ConfigError(format!(
                "{FAULT_ARM_VALUE} is armed but CRANELISP_TEST_FAULT names no plant"
            ));
        }
    };
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return PlantSpec::ConfigError("CRANELISP_TEST_FAULT is empty".to_string());
    }
    if trimmed.contains(',') || trimmed.split_whitespace().count() > 1 {
        return PlantSpec::ConfigError(format!(
            "CRANELISP_TEST_FAULT names more than one plant ({trimmed:?}); exactly one is legal"
        ));
    }
    match FaultPlant::parse(trimmed) {
        Some(p) => PlantSpec::Armed(p),
        None => PlantSpec::ConfigError(format!(
            "CRANELISP_TEST_FAULT {trimmed:?} is not a known plant; legal spellings: {}",
            FaultPlant::ALL
                .iter()
                .map(|p| p.spelling())
                .collect::<Vec<_>>()
                .join(", ")
        )),
    }
}

/// A test-configuration error, reported and fatal. Distinct prefix from
/// [`seam_hard_fail`] so a mis-armed child can never be mistaken for a detected
/// fault (the triplets discriminate on the seam prefix).
#[cold]
#[inline(never)]
fn plant_config_error(msg: &str) -> ! {
    eprintln!("[CRANELISP TEST-FAULT CONFIG ERROR] {msg}");
    std::process::abort();
}

/// The process-wide plant, parsed once. `None` on the unarmed path — no state
/// construction, no allocation, no counter adjustment (acceptance item 4).
///
/// Timing, stated honestly: the parse runs at the FIRST hook call, which is the
/// `PostAlloc` of the process's first allocation. A configuration error
/// therefore aborts there rather than at `main`'s first instruction — but it
/// aborts **before any plant state exists and before any action is applied**,
/// which is the invariant that matters (§7.1: never a partial plant). Forcing
/// the parse earlier would mean a fourth hook call on the allocation hot path
/// for no additional guarantee.
static PLANT: LazyLock<Option<PlantState>> = LazyLock::new(|| {
    let arm = std::env::var("CRANELISP_TEST_FAULTS").ok();
    let spelling = std::env::var("CRANELISP_TEST_FAULT").ok();
    match parse_plant_spec(arm.as_deref(), spelling.as_deref()) {
        PlantSpec::Off => None,
        PlantSpec::Armed(p) => Some(PlantState::new(p)),
        // Before any plant is constructed and before any action is applied —
        // never a partial plant.
        PlantSpec::ConfigError(msg) => plant_config_error(&msg),
    }
});

/// The ONE production hook. Returns [`FaultAction::NoAction`] whenever the arm
/// variable is absent (one cached `Option` read, no branch taken).
#[inline]
pub(crate) fn test_fault_event(event: FaultEvent) -> FaultAction {
    match &*PLANT {
        None => FaultAction::NoAction,
        Some(state) => fault_event_armed(state, event),
    }
}

/// The armed dispatch, factored out so the event × plant matrix (including the
/// marker-size selection negatives) is unit-testable with a locally-constructed
/// `PlantState` — no env, no subprocess (Principle 5).
fn fault_event_armed(state: &PlantState, event: FaultEvent) -> FaultAction {
    use FaultPlant as P;
    match (state.plant, event) {
        // Rows needing a SPECIFIC allocation select deterministically by the
        // exact marker size. Anything else is left alone.
        (
            P::M1StaleReuse
            | P::M2StaleRead
            | P::A1ZeroRc
            | P::A2InteriorPointer
            | P::A3FreedPointer
            | P::A4MalformedHeader,
            FaultEvent::PostAlloc { base, total_size },
        ) if total_size == PLANT_MARKER_TOTAL => {
            if state.claim(base, total_size) {
                FaultAction::CapturePlant
            } else {
                FaultAction::NoAction
            }
        }
        // Rows that only need *an* allocation fire on the first matching event —
        // which is what lets the same two spellings work identically in a Rust
        // unit child and in the compiler-binary e2e child.
        (P::M3Leak, FaultEvent::PreFree { base, total_size }) => {
            if state.claim(base, total_size) {
                FaultAction::SuppressFree
            } else {
                FaultAction::NoAction
            }
        }
        (
            P::M3OverFree,
            FaultEvent::PostFree {
                base, total_size, ..
            },
        ) => {
            if state.claim(base, total_size) {
                FaultAction::ExtraDischarge
            } else {
                FaultAction::NoAction
            }
        }
        _ => FaultAction::NoAction,
    }
}

/// The single read-only fixture observation (§7.2) — no setters, no state
/// mutation. A fixture reads the production-allocated identity the hook
/// recorded and the detector's own observable (M1 retention).
pub(crate) struct FaultObservation {
    pub(crate) plant: Option<FaultPlant>,
    pub(crate) fired: bool,
    /// The `(base, total_size)` captured from a production `PostAlloc`/free
    /// event. Read by the §7.3 row fixtures.
    #[allow(dead_code)]
    pub(crate) planted_base: i64,
    /// Read by the §7.3 row fixtures.
    #[allow(dead_code)]
    pub(crate) planted_total_size: usize,
    /// M1's own observable — bytes currently withheld from the system
    /// allocator. `0` when M1 is off, WITHOUT constructing the quarantine.
    /// Read by the §7.3 row fixtures.
    #[allow(dead_code)]
    pub(crate) quarantine_retained_bytes: usize,
}

/// Read the plant slot + M1 retention. Constructs nothing; when M1 is off the
/// quarantine `LazyLock` is not even touched.
pub(crate) fn fault_observation() -> FaultObservation {
    let (plant, fired, planted_base, planted_total_size) = match &*PLANT {
        None => (None, false, 0, 0),
        Some(s) => (
            Some(s.plant),
            s.fired.load(Ordering::Acquire),
            s.planted_base.load(Ordering::Relaxed),
            s.planted_total_size.load(Ordering::Relaxed),
        ),
    };
    let quarantine_retained_bytes = if quarantine_enabled() {
        QUARANTINE
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .retained_bytes
    } else {
        0
    };
    FaultObservation {
        plant,
        fired,
        planted_base,
        planted_total_size,
        quarantine_retained_bytes,
    }
}

/// The plant-identity line the M3 atexit report prepends when a LEDGER plant
/// fired (§7.2). Its exact shape is pinned by the committed e2e
/// (`tests/intrinsics_m3_detection_s116.rs`), which asserts the child's stderr
/// contains the plant spelling, `alloc`, `dealloc`, and lowercase
/// `parity`/`imbalance`. The clean-control sibling must produce no such line and
/// must not print a plant spelling anywhere.
fn ledger_plant_report_line() -> Option<String> {
    let obs = fault_observation();
    match obs.plant {
        Some(p) if obs.fired && p.is_ledger_plant() => Some(ledger_plant_line_for(p)),
        _ => None,
    }
}

/// The report-identity format, pure over the plant so the exact shape the
/// committed e2e asserts is pinned by a unit row too.
fn ledger_plant_line_for(plant: FaultPlant) -> String {
    format!(
        "[ALLOC_PARITY] test-fault plant {} fired — injected alloc/dealloc parity imbalance",
        plant.spelling()
    )
}

// ---------------------------------------------------------------------------
// M2 — scrub-freed-memory poisoning
// ---------------------------------------------------------------------------

/// The poison word: `0xDEAD2FEE_DEAD2FEE` ("dead to free"). Chosen so a stale
/// read is deterministically wrong in every interpretation — a wild negative as
/// an Int/tag, a non-canonical (faulting) pointer, and a wild count as an RC
/// field (trips the `old_rc > 0` underflow check, never reaches the free arm).
pub(crate) const POISON_WORD: u64 = 0xDEAD2FEE_DEAD2FEE;

/// Overwrite the whole allocation (`total_size` bytes from `base`: header +
/// payload) with the poison pattern. i64-word aligned, with a byte-wise tail for
/// non-multiple-of-8 sizes (a `HeapString` payload is `len` raw bytes).
///
/// # Safety
/// `base` must address `total_size` writable bytes (a live allocation being
/// freed). Called at the free seam before release-or-quarantine.
pub(crate) unsafe fn scrub(base: *mut u8, total_size: usize) {
    let full_words = total_size / 8;
    let wp = base as *mut u64;
    for i in 0..full_words {
        // SAFETY: word `i` is within the `total_size`-byte allocation.
        unsafe { wp.add(i).write(POISON_WORD) };
    }
    let tail = total_size % 8;
    if tail != 0 {
        let bytes = POISON_WORD.to_le_bytes();
        // SAFETY: the tail bytes are the trailing `tail` bytes of the allocation.
        let bp = unsafe { base.add(full_words * 8) };
        for (i, &b) in bytes.iter().take(tail).enumerate() {
            // SAFETY: byte `full_words*8 + i` is within the allocation.
            unsafe { bp.add(i).write(b) };
        }
    }
}

// ---------------------------------------------------------------------------
// M1 — no-reuse-after-free quarantine
// ---------------------------------------------------------------------------

/// A process-global FIFO of freed-but-withheld blocks. Constructed lazily —
/// only when M1 is first observed on (off ⇒ zero cost).
struct Quarantine {
    /// `(base, layout)` in free order; oldest at the front (FIFO release order).
    blocks: VecDeque<(usize, Layout)>,
    retained_bytes: usize,
}

impl Quarantine {
    fn new() -> Self {
        Quarantine {
            blocks: VecDeque::new(),
            retained_bytes: 0,
        }
    }

    /// Withhold a freed block. If `cap` is set and retained bytes exceed it,
    /// physically release the oldest blocks (FIFO) until back under the cap —
    /// reopening the reuse window for the *coldest* blocks only.
    ///
    /// # Safety
    /// `base` was allocated with `layout` and its logical ownership is
    /// transferred to the quarantine (the caller must not free it). Any block
    /// released here is freed exactly once (it was withheld, never freed).
    unsafe fn withhold(&mut self, base: *mut u8, layout: Layout, cap: Option<usize>) {
        self.retained_bytes = self.retained_bytes.saturating_add(layout.size());
        self.blocks.push_back((base as usize, layout));
        if let Some(cap) = cap {
            while self.retained_bytes > cap {
                match self.blocks.pop_front() {
                    Some((old_base, old_layout)) => {
                        self.retained_bytes = self.retained_bytes.saturating_sub(old_layout.size());
                        // SAFETY: `old_base` was allocated with `old_layout` and
                        // has been withheld (never freed) until now.
                        unsafe { std::alloc::dealloc(old_base as *mut u8, old_layout) };
                    }
                    None => break,
                }
            }
        }
    }
}

static QUARANTINE: LazyLock<Mutex<Quarantine>> = LazyLock::new(|| Mutex::new(Quarantine::new()));

/// The scrub → quarantine-or-release step of `dealloc` (the fixed-order tail,
/// after the `FREED_TRACKED` identity capture). Returns `true` if the block was
/// **withheld** (the caller must NOT physically free it); `false` ⇒ the caller
/// releases it to the system allocator exactly as today.
///
/// # Safety
/// `base` is a live allocation of `total_size` bytes with `layout`, about to be
/// freed. `total_size == layout.size()`.
pub(crate) unsafe fn scrub_and_dispose(base: *mut u8, layout: Layout, total_size: usize) -> bool {
    if scrub_enabled() {
        // SAFETY: `base..base+total_size` is the whole live allocation.
        unsafe { scrub(base, total_size) };
    }
    if quarantine_enabled() {
        let cap = quarantine_max_bytes();
        let mut q = QUARANTINE.lock().unwrap_or_else(|e| e.into_inner());
        // SAFETY: ownership of `(base, layout)` transfers to the quarantine.
        unsafe { q.withhold(base, layout, cap) };
        true
    } else {
        false
    }
}

// ---------------------------------------------------------------------------
// M3 — paired alloc/free hard-check
// ---------------------------------------------------------------------------

/// Build the imbalance dump, or `None` when balanced. Pure over its inputs so
/// the hard-check logic is unit-testable without registering an atexit or
/// aborting. `live` is the debug live-set snapshot `(addr, size, payload@16)`;
/// empty in release (the live set cannot be enumerated without the debug side
/// table, so release catches only the count imbalance).
fn alloc_parity_report(
    allocs: usize,
    deallocs: usize,
    live: &[(usize, usize, i64)],
) -> Option<String> {
    if allocs == deallocs && live.is_empty() {
        return None;
    }
    let mut s = String::new();
    let delta = allocs as i128 - deallocs as i128;
    let face = if delta > 0 {
        "LEAK (allocs > deallocs — blocks never freed)"
    } else if delta < 0 {
        "DOUBLE-FREE (deallocs > allocs — a block freed twice)"
    } else {
        "LEAK (live set non-empty at exit)"
    };
    s.push_str(&format!(
        "[ALLOC_PARITY] IMBALANCE — {face}\n\
         [ALLOC_PARITY]   ALLOC_COUNT={allocs} DEALLOC_COUNT={deallocs} delta={delta}\n"
    ));
    if !live.is_empty() {
        s.push_str(&format!(
            "[ALLOC_PARITY]   surviving live allocations: {}\n",
            live.len()
        ));
        for (addr, size, payload) in live.iter().take(64) {
            s.push_str(&format!(
                "[ALLOC_PARITY]     {addr:#x} size={size} payload@16={payload:#x}\n"
            ));
        }
        if live.len() > 64 {
            s.push_str(&format!(
                "[ALLOC_PARITY]     … and {} more\n",
                live.len() - 64
            ));
        }
    }
    Some(s)
}

/// The balanced-ledger line for the dump-only face (print-and-continue).
fn balanced_ledger(allocs: usize, deallocs: usize, live_len: usize) -> String {
    format!(
        "[ALLOC_PARITY] balanced: ALLOC_COUNT={allocs} DEALLOC_COUNT={deallocs} live={live_len}"
    )
}

/// The atexit handler registered by [`ensure_parity_registered`]. On imbalance
/// under `CRANELISP_ALLOC_PARITY` it dumps and aborts non-zero; under
/// `CRANELISP_ALLOC_PARITY_DUMP` alone it prints and continues (never aborts).
extern "C" fn check_alloc_parity_atexit() {
    let allocs = crate::alloc::alloc_count();
    let deallocs = crate::alloc::dealloc_count();
    let live = live_snapshot();
    let hard = parity_hard_enabled();
    let dump = parity_dump_enabled();

    match alloc_parity_report(allocs, deallocs, &live) {
        Some(report) => {
            // §7.2: name the injected fault BEFORE the report, so a report says
            // *which* plant produced it. Absent unless a ledger plant fired.
            if let Some(line) = ledger_plant_report_line() {
                eprintln!("{line}");
            }
            eprint!("{report}");
            if hard {
                // Located hard-fail: an alloc/free imbalance is a compiler defect
                // (in-process invariant breach) — dump above, then abort.
                std::process::abort();
            }
            // dump-only mode: print-and-continue (already printed).
        }
        None => {
            if dump {
                if let Some(line) = ledger_plant_report_line() {
                    eprintln!("{line}");
                }
                eprintln!("{}", balanced_ledger(allocs, deallocs, live.len()));
            }
        }
    }
}

/// Debug live-set snapshot for the exit dump; empty in release (no side table).
#[inline]
fn live_snapshot() -> Vec<(usize, usize, i64)> {
    #[cfg(debug_assertions)]
    {
        crate::alloc::live_alloc_snapshot()
    }
    #[cfg(not(debug_assertions))]
    {
        Vec::new()
    }
}

/// Explicit mid-run parity dump (print-and-continue), for bisecting a long run.
/// A `pub(crate)` mechanism callable in-process; safe to call any time.
#[allow(dead_code)]
pub(crate) fn dump_alloc_parity() {
    let allocs = crate::alloc::alloc_count();
    let deallocs = crate::alloc::dealloc_count();
    let live = live_snapshot();
    match alloc_parity_report(allocs, deallocs, &live) {
        Some(report) => eprint!("{report}"),
        None => eprintln!("{}", balanced_ledger(allocs, deallocs, live.len())),
    }
}

#[cfg(test)]
mod tests;
