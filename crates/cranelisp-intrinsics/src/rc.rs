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

use std::sync::atomic::{AtomicBool, AtomicI64, AtomicU64, Ordering};
use std::sync::{LazyLock, Once};

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

// ---------------------------------------------------------------------------
// S99 Wave 0 — RC-atomicity probe + RC-op/alloc instrumentation (measurement)
// ---------------------------------------------------------------------------
//
// Two independent, env-gated, OFF-BY-DEFAULT measurement facilities. BOTH are
// byte-identical-off: with the env unset, the blessed atomic RC paths run
// exactly as before. These mirror the backend-side codegen switches in
// `cranelisp-backend::heap` (arch Phase-2 ruling R4) so a whole run is
// consistently instrumented / non-atomic across the inline-emitted and
// intrinsic-implemented RC loci.
//
//   * `CRANELISP_NONATOMIC_RC` — execute NON-ATOMIC RC inc/dec (plain
//     load-modify-store) instead of an atomic RMW. **UNSOUND above one worker**
//     (a lost-update race corrupts the count → use-after-free / leak). It exists
//     ONLY to isolate the atomic-*instruction* cost at a single-worker spark
//     pool (`RAYON_NUM_THREADS=1`). NEVER ship it; it is excluded from the
//     canonical `cargo nextest run`.
//   * `CRANELISP_RC_STATS` — tally RC inc + RC dec operation counts across a run
//     (these intrinsic-side dec/inc paths + the backend-inline ops via the
//     `runtime/rc_stat_{inc,dec}` catalog helpers), printed once to stderr at
//     process exit together with the alloc/dealloc counts. Confirms the
//     copy-per-node RC-bump volume directly. Zero overhead when off.
//
// NOTE (scope): the IVar spark-machinery RC in `ivar.rs` deliberately stays
// SeqCst-atomic (BC §4b invariant 3) and is NOT covered by either switch — it is
// a small fixed per-spark cost shared by the atomic and non-atomic configs, not
// the per-node data RC the volume claim is about (arch R4 named `heap.rs` +
// `rc.rs`/`drop.rs` only).

/// Whether the NON-ATOMIC RC measurement build is active. Read once. Off ⇒ the
/// blessed atomic RC paths run unchanged (byte-identical-off).
#[inline]
pub(crate) fn nonatomic_rc_enabled() -> bool {
    static E: LazyLock<bool> =
        LazyLock::new(|| std::env::var_os("CRANELISP_NONATOMIC_RC").is_some());
    *E
}

/// Non-atomic read-modify-write of the RC field at `ptr` (offset `RC_OFFSET`).
/// Returns the OLD value. Measurement-only — a data race above one worker.
///
/// # Safety
/// `ptr` must be a valid heap base pointer with a readable/writable RC i64.
#[inline]
pub(crate) unsafe fn nonatomic_rc_rmw(ptr: i64, delta: i64) -> i64 {
    // SAFETY: caller guarantees ptr is a valid heap base with an aligned RC i64.
    let p = unsafe { (ptr as *mut u8).add(HeapHeader::RC_OFFSET as usize) as *mut i64 };
    let old = unsafe { *p };
    unsafe { *p = old + delta };
    old
}

static RC_INC_COUNT: AtomicU64 = AtomicU64::new(0);
static RC_DEC_COUNT: AtomicU64 = AtomicU64::new(0);
static STATS_ATEXIT: Once = Once::new();

/// Whether RC-op/alloc instrumentation is active. Read once; the first `true`
/// read registers the at-exit printer. Zero cost when off (one cached load).
#[inline]
pub(crate) fn rc_stats_enabled() -> bool {
    static E: LazyLock<bool> = LazyLock::new(|| {
        let on = std::env::var_os("CRANELISP_RC_STATS").is_some();
        if on {
            ensure_stats_atexit();
        }
        on
    });
    *E
}

/// Register the process-exit RC-stats printer exactly once.
fn ensure_stats_atexit() {
    // SAFETY: `print_rc_stats` is a plain `extern "C" fn()` with no arguments,
    // the shape `libc::atexit` requires.
    STATS_ATEXIT.call_once(|| unsafe {
        libc::atexit(print_rc_stats);
    });
}

/// Tally one RC inc. Called from the backend-inline `runtime/rc_stat_inc`
/// catalog helper and the intrinsic-side [`rc_inc`].
#[inline]
pub(crate) fn tally_rc_inc() {
    RC_INC_COUNT.fetch_add(1, Ordering::Relaxed);
}

/// Tally one RC dec. Called from the backend-inline `runtime/rc_stat_dec`
/// catalog helper and the intrinsic-side dec paths ([`consume_shallow`],
/// `drop::atomic_dec_rc`).
#[inline]
pub(crate) fn tally_rc_dec() {
    RC_DEC_COUNT.fetch_add(1, Ordering::Relaxed);
}

// ---------------------------------------------------------------------------
// H2 (S102 increment I) — per-mechanism attribution counters
// ---------------------------------------------------------------------------
//
// The B3 read path landed three ownership mechanisms (borrow-elision B3.2,
// confined non-atomic RC B3.3, escape→stack-slot B3.4). The `[RC_STATS]`
// surface attributes them per-mechanism for the I-G3/I-G7 acceptance gates.
//
// These are **codegen-time** counts (accumulated while the backend LOWERS a
// program), NOT runtime tallies — so there is no emitted IR call and the
// byte-identical-off discipline is untouched (a stat-family printed
// unconditionally never perturbs the compiled code). The backend
// (`cranelisp-backend`, which depends on this crate) is the sole writer,
// pushing via [`tally_stack_slot`] / [`tally_rc_emit`] at emission time; this
// crate OWNS the counters because it owns the process-exit print surface (the
// backend cannot: no dependency edge points the other way). In `--run`/JIT the
// compile and run share one process, so the counts are populated before the
// at-exit printer reads them; in `--link` the run is a separate process that
// did no codegen, so its per-mechanism counts are honestly zero.
//
// `reuse_hit` / `reuse_miss` are inert placeholders at increment I — the
// slot-reuse (drop-guided reuse-token) mechanism is increment-II uniqueness-
// track work (`design/backend/ownership-codegen.md` §6). They print as `0` so
// the counter FAMILY is present; they gain a writer when reuse lands.

/// Backend-emitted stack-slot allocations (B3.4 escape→stack-slot). Codegen-
/// time, process-global, monotone.
static STACK_SLOT_HITS: AtomicU64 = AtomicU64::new(0);
/// Total emitted inline RC ops (B3.3 arm-discrimination denominator).
static RC_EMIT_TOTAL: AtomicU64 = AtomicU64::new(0);
/// Emitted RC ops that took the NON-ATOMIC arm (B3.3 confined RC).
static RC_EMIT_NONATOMIC: AtomicU64 = AtomicU64::new(0);

// ---------------------------------------------------------------------------
// H2 reuse counters (increment II, §6.5) — LIVE runtime tallies
// ---------------------------------------------------------------------------
//
// `reuse_hit` / `reuse_miss` are the drop-guided-reuse / COW discriminator
// (`design/backend/ownership-codegen.md` §6.5). Because reuse permission is
// **dynamic** (rc==1 per call), the hit/miss split at a COW/reuse site is a
// RUNTIME tally (like `rc_inc`/`rc_dec`, not the codegen-time `stack_slot` /
// `rc_nonatomic` family): the backend emits a `runtime/reuse_hit` /
// `runtime/reuse_miss` catalog-helper call on the in-place-reuse / copy arm of
// every `emit_vec_set_cow_core` / `emit_vec_push_cow_core` site, ONLY under its
// codegen-time `CRANELISP_RC_STATS` gate (off ⇒ no emitted IR ⇒ byte-identical
// codegen — the §2.2 discipline). At increment II these become non-zero the
// moment a unique vec is mutated in place.
static REUSE_HIT_COUNT: AtomicU64 = AtomicU64::new(0);
static REUSE_MISS_COUNT: AtomicU64 = AtomicU64::new(0);

// ---------------------------------------------------------------------------
// H3 per-extern adaptation-pair attribution (increment II, §9.2 / §13.2.1)
// ---------------------------------------------------------------------------
//
// The L-D5 sibling-funding decision rule (`design/backend/ownership-codegen.md`
// §9.2) is report-graded off a RUNTIME name-keyed tally of the Decision-24
// adaptation pairs (a consuming dec, optionally paired with an adaptation inc)
// paid at each hand-audited extern's statically-resolved call sites. Increment I
// ships the pattern plus exactly ONE template instance — `str-len` — so the
// family is a single registered extern. The backend emits a `runtime/extern_
// adapt_str_len` catalog-helper call at each `str-len` call site, ONLY under its
// codegen-time `CRANELISP_RC_STATS` gate (off ⇒ no emitted IR ⇒ byte-identical).
// The name is printed in the family unconditionally under the gate (present even
// at count 0 — the placeholder-honesty discipline the `reuse_*` family follows),
// so `/qa`'s L-D5 attribution lane reads the per-extern pair population.
static STR_LEN_ADAPT_COUNT: AtomicU64 = AtomicU64::new(0);

/// Tally one backend-emitted stack-slot allocation (B3.4). Called from
/// `cranelisp-backend::heap::emit_stack_alloc` at codegen time.
#[inline]
pub fn tally_stack_slot() {
    STACK_SLOT_HITS.fetch_add(1, Ordering::Relaxed);
}

/// Tally one emitted inline RC op, discriminating the non-atomic arm (B3.3
/// confined RC) from the atomic arm. Called once per emitted inc/dec from
/// `cranelisp-backend::heap::use_nonatomic_arm` at codegen time.
#[inline]
pub fn tally_rc_emit(nonatomic: bool) {
    RC_EMIT_TOTAL.fetch_add(1, Ordering::Relaxed);
    if nonatomic {
        RC_EMIT_NONATOMIC.fetch_add(1, Ordering::Relaxed);
    }
}

/// Codegen-time stack-slot-hit count (B3.4). The print surface's source for
/// `stack_slot=…`; also read back by the backend's `heap::stack_slot_hits`
/// accessor so its unit matrix reads the single source of truth.
pub fn stack_slot_hits() -> u64 {
    STACK_SLOT_HITS.load(Ordering::Relaxed)
}

/// Tally one drop-guided-reuse / COW **hit** (in-place reuse arm taken at
/// runtime, §6.5). Runtime tally — called from the backend-emitted
/// `runtime/reuse_hit` hook and (in-process) the intrinsic-side accessor tests.
#[inline]
pub(crate) fn tally_reuse_hit() {
    REUSE_HIT_COUNT.fetch_add(1, Ordering::Relaxed);
}

/// Tally one drop-guided-reuse / COW **miss** (copy arm taken at runtime, §6.5).
#[inline]
pub(crate) fn tally_reuse_miss() {
    REUSE_MISS_COUNT.fetch_add(1, Ordering::Relaxed);
}

/// Runtime `(reuse_hit, reuse_miss)` tallies (§6.5). `#[cfg(test)]`: unlike the
/// codegen-time `stack_slot_hits`/`rc_emit_counts` (which the backend reads back
/// as the SSOT for its H2 unit matrix), the reuse split is a RUNTIME tally, so
/// the backend never reads it — the only consumer is this crate's own counter
/// unit tests. Kept off both the public surface AND the non-test build (no
/// facade entry owed, no dead-code in release).
#[cfg(test)]
pub(crate) fn reuse_counts() -> (u64, u64) {
    (
        REUSE_HIT_COUNT.load(Ordering::Relaxed),
        REUSE_MISS_COUNT.load(Ordering::Relaxed),
    )
}

/// Runtime per-extern adaptation-pair count for `str-len` (H3 / §9.2 template
/// instance). `#[cfg(test)]` (runtime tally; consumed only by this crate's tests).
#[cfg(test)]
pub(crate) fn str_len_adapt_count() -> u64 {
    STR_LEN_ADAPT_COUNT.load(Ordering::Relaxed)
}

/// Codegen-time `(non_atomic_ops, total_ops)` RC-emission counts (B3.3). The
/// print surface's source for `rc_nonatomic=…`/`rc_atomic=…`; also read back by
/// the backend's `heap::rc_emit_counts` accessor.
pub fn rc_emit_counts() -> (u64, u64) {
    (
        RC_EMIT_NONATOMIC.load(Ordering::Relaxed),
        RC_EMIT_TOTAL.load(Ordering::Relaxed),
    )
}

/// At-exit printer (stderr): RC inc/dec + alloc/dealloc counts + the H2
/// per-mechanism attribution family, printed once. The first four fields
/// (`rc_inc rc_dec allocs deallocs`) keep their order and position so every
/// existing token/regex parser matches; the per-mechanism family is appended.
///
/// Grammar (`design/backend/ownership-codegen.md` §13.2): `stack_slot` =
/// codegen stack-slot hits (B3.4); `reuse_hit`/`reuse_miss` = increment-II
/// placeholders (always `0` until slot-reuse lands, §6); `rc_nonatomic`/
/// `rc_atomic` = emitted-op arm split (B3.3), consumer computes the share
/// `rc_nonatomic / (rc_nonatomic + rc_atomic)`.
extern "C" fn print_rc_stats() {
    eprintln!("{}", rc_stats_line());
}

/// Build the `[RC_STATS]` line (pure — reads the process-global counters, does
/// no I/O). Factored out of [`print_rc_stats`] so the grammar (field order,
/// per-mechanism family, placeholder honesty) is unit-testable without capturing
/// stderr at process exit.
fn rc_stats_line() -> String {
    let inc = RC_INC_COUNT.load(Ordering::Relaxed);
    let dec = RC_DEC_COUNT.load(Ordering::Relaxed);
    let allocs = alloc::alloc_count();
    let deallocs = alloc::dealloc_count();
    let stack_slot = STACK_SLOT_HITS.load(Ordering::Relaxed);
    let reuse_hit = REUSE_HIT_COUNT.load(Ordering::Relaxed);
    let reuse_miss = REUSE_MISS_COUNT.load(Ordering::Relaxed);
    let rc_nonatomic = RC_EMIT_NONATOMIC.load(Ordering::Relaxed);
    let rc_atomic = RC_EMIT_TOTAL
        .load(Ordering::Relaxed)
        .saturating_sub(rc_nonatomic);
    let str_len_adapt = STR_LEN_ADAPT_COUNT.load(Ordering::Relaxed);
    format!(
        "[RC_STATS] rc_inc={inc} rc_dec={dec} allocs={allocs} deallocs={deallocs} \
         stack_slot={stack_slot} reuse_hit={reuse_hit} reuse_miss={reuse_miss} \
         rc_nonatomic={rc_nonatomic} rc_atomic={rc_atomic} str-len_adapt={str_len_adapt}"
    )
}

/// Backend-inline RC-inc tally hook (S99). Emitted as a `runtime/rc_stat_inc`
/// call before each inline atomic inc ONLY under the backend's codegen-time
/// `CRANELISP_RC_STATS` gate (off ⇒ never emitted ⇒ byte-identical codegen).
/// `pub(crate)` + catalog-registered by fn pointer — NOT part of the crate's
/// public surface.
#[unsafe(export_name = "runtime/rc_stat_inc")]
pub(crate) extern "C" fn rc_stat_inc() -> i64 {
    ensure_stats_atexit();
    tally_rc_inc();
    0
}

/// Backend-inline RC-dec tally hook (S99). Sibling of [`rc_stat_inc`].
#[unsafe(export_name = "runtime/rc_stat_dec")]
pub(crate) extern "C" fn rc_stat_dec() -> i64 {
    ensure_stats_atexit();
    tally_rc_dec();
    0
}

/// Backend-inline reuse-**hit** tally hook (increment II, §6.5). Emitted on the
/// in-place / reuse arm of a COW/reuse site ONLY under the backend's codegen-time
/// `CRANELISP_RC_STATS` gate (off ⇒ never emitted ⇒ byte-identical codegen).
/// `pub(crate)` + catalog-registered by fn pointer — NOT part of the public API.
#[unsafe(export_name = "runtime/reuse_hit")]
pub(crate) extern "C" fn reuse_hit_stat() -> i64 {
    ensure_stats_atexit();
    tally_reuse_hit();
    0
}

/// Backend-inline reuse-**miss** tally hook (increment II, §6.5). Sibling of
/// [`reuse_hit_stat`] — emitted on the copy arm of a COW/reuse site.
#[unsafe(export_name = "runtime/reuse_miss")]
pub(crate) extern "C" fn reuse_miss_stat() -> i64 {
    ensure_stats_atexit();
    tally_reuse_miss();
    0
}

/// Backend-inline per-extern adaptation-pair tally hook for `str-len` (H3 /
/// §9.2 template instance). Emitted at each `str-len` call site ONLY under the
/// backend's codegen-time `CRANELISP_RC_STATS` gate.
#[unsafe(export_name = "runtime/extern_adapt_str_len")]
pub(crate) extern "C" fn extern_adapt_str_len_stat() -> i64 {
    ensure_stats_atexit();
    STR_LEN_ADAPT_COUNT.fetch_add(1, Ordering::Relaxed);
    0
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
    // FIXME 0494 localization: catch a dec of an already-freed pointer AT the dec.
    #[cfg(debug_assertions)]
    debug_assert!(
        alloc::is_live(ptr as usize),
        "STALE RC DEC (consume_shallow): dec of non-live heap pointer {ptr:#x} — \
         already freed + reclaimed; the dec corrupts the reused chunk. (FIXME 0494.)"
    );
    if rc_stats_enabled() {
        tally_rc_dec();
    }
    let old_rc = if nonatomic_rc_enabled() {
        // S99 measurement-only: NON-ATOMIC dec — UNSOUND above one worker.
        // SAFETY: caller guarantees ptr is a valid heap base with RC > 0.
        unsafe { nonatomic_rc_rmw(ptr, -1) }
    } else {
        // SAFETY: caller guarantees ptr is a valid heap base with RC > 0.
        let rc_ptr = unsafe {
            &*((ptr as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const AtomicI64)
        };
        rc_ptr.fetch_sub(1, Ordering::Release)
    };
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
    if rc_stats_enabled() {
        tally_rc_inc();
    }
    let old_rc = if nonatomic_rc_enabled() {
        // S99 measurement-only: NON-ATOMIC inc — UNSOUND above one worker.
        // SAFETY: caller guarantees ptr is a valid heap base with RC > 0.
        unsafe { nonatomic_rc_rmw(ptr, 1) }
    } else {
        // SAFETY: caller guarantees ptr is a valid heap base with RC > 0.
        let rc_ptr = unsafe {
            &*((ptr as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const AtomicI64)
        };
        rc_ptr.fetch_add(1, Ordering::Release)
    };
    rc_trace("inc", ptr, old_rc + 1);
}

/// FIXME 0494 localization — stale-dec liveness check, called from JIT-generated
/// inline dec code ONLY when the backend was invoked with `CRANELISP_RC_DEC_CHECK`
/// set (a codegen-time gate — off by default ⇒ zero emitted call ⇒ byte-identical).
///
/// The backend emits inline RC dec as `atomic_rmw Sub`, so a dec of an
/// already-freed heap value (e.g. a closure drop-glue dec'ing a stale capture on
/// the launched-strand teardown, FIXME 0494 bug #2) silently corrupts the reused
/// chunk — invisible to every Rust-side guard because the write is JIT. This hook,
/// emitted just before the atomic sub, validates the pointer is a currently-live
/// tracked allocation and fires AT the stale dec with the exact pointer + JIT stack.
///
/// Linker symbol: `runtime/rc_dec_check`. `pub(crate)` (catalog references it by fn
/// pointer) — not part of the crate's public surface.
#[unsafe(export_name = "runtime/rc_dec_check")]
pub(crate) extern "C" fn rc_dec_check(ptr: i64) -> i64 {
    #[cfg(debug_assertions)]
    {
        if ptr >= cranelisp_types::NULLARY_TAG_THRESHOLD as i64
            && !alloc::is_live(ptr as usize)
        {
            let info = alloc::freed_info(ptr as usize);
            panic!(
                "STALE RC DEC (JIT inline): about to dec non-live heap pointer {ptr:#x} \
                 — already freed and reclaimed; this dec corrupts the reused chunk. \
                 Freed-value (size, payload@16) = {info:?}. (FIXME 0494 bug #2 — \
                 double-free on launched-strand teardown; a poll-effect state-closure \
                 leaf arg baked without an inc while still owned by an enclosing \
                 continuation.)"
            );
        }
    }
    let _ = ptr;
    0
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
