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
use std::sync::{LazyLock, Mutex};

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
