//! IVar — write-once synchronization cells for lenient evaluation.
//!
//! IVars are heap-allocated, RC-managed values used by the backend's
//! sparkability analysis to evaluate independent `let` bindings in parallel.
//!
//! ## Heap Layout (base-pointer convention, Decision 10)
//!
//! ```text
//! Base pointer ->
//!   +0   alloc_size: i64   (= 48)
//!   +8   rc: i64           (initial: 1, atomic)
//!   +16  state: i64        (atomic — PENDING/EVALUATING/RESOLVED)
//!   +24  value: i64        (result, valid when state = RESOLVED)
//!   +32  thunk: i64        (closure pointer — zero-arg thunk)
//!   +40  error: i64        (heap String ptr of the thunk's runtime panic, or 0;
//!                           published with `value` under the RESOLVED store —
//!                           the fork-join error-slot ferry, test-discovery.md §6)
//! ```
//!
//! ## The fork-join error-slot ferry (`design/arch/test-discovery.md` §6)
//!
//! Lenient eval sparks pure bindings onto rayon workers. A thunk's runtime panic
//! lands in the *worker's* `RUNTIME_ERROR` thread-local — a different slot than
//! the joining thread reads. To stay observationally equivalent to sequential
//! evaluation (spec §12.4.3, first-error-wins), the thunk-running side calls
//! `panic::take_runtime_error()` after the thunk and **ferries** any `Some(msg)`
//! into the IVar's `error` field (worker-side). Every reader of the resolved
//! IVar (the claimant after evaluation, and any spin-waiter) re-raises a non-zero
//! `error` into its own slot via `panic::set_runtime_error` (join-side,
//! first-error-wins) and yields the sentinel.
//!
//! ## State Machine
//!
//! - PENDING (0) -> EVALUATING (1): via CAS in `ivar_force`
//! - EVALUATING (1) -> RESOLVED (2): via store in `ivar_force`
//!
//! All atomics use SeqCst (Decision 13).
//!
//! See `design/backend/lenient-eval.md` for the full design.

use std::cell::Cell;
use std::sync::LazyLock;
use std::sync::atomic::{AtomicI64, AtomicIsize, AtomicU64, Ordering};

use crate::alloc::{alloc_with_rc, dealloc};

// ── Spark-stats profiling instrumentation (CRANELISP_SPARK_STATS=1) ──────────
// Counts spark instances + ivar_force outcomes + the utilization-model signals
// (S104 Wave 0, `tests/plan/s104-utilization-measurement.md` §3). Gated behind
// an env var; **zero cost when off** — the hot paths read a single `LazyLock`
// bool and skip every counter (no atomics executed when disabled), matching the
// `CRANELISP_NO_LENIENT` / `SPARK_BUDGET` idioms. Origin: S103 FIXME-0534.
static SPARK_SPAWNS: AtomicU64 = AtomicU64::new(0);
static FORCE_CALLS: AtomicU64 = AtomicU64::new(0);
static FORCE_FASTPATH_RESOLVED: AtomicU64 = AtomicU64::new(0);
static FORCE_CLAIM_WINS: AtomicU64 = AtomicU64::new(0);
static FORCE_SPIN_WAITS: AtomicU64 = AtomicU64::new(0);
static FORCE_SPIN_ITERS: AtomicU64 = AtomicU64::new(0);
/// S104 Wave 0 — the "continue-serial" half of the spawn/serial ratio
/// (§3, `tests/plan/s104-utilization-measurement.md`). Incremented once per
/// create-gate site that takes the direct/inline arm (`spark_budget_try_reserve`
/// returns `0` — the over-budget branch, `lenient-eval.md` §3.6.2) instead of
/// sparking.
static SPARK_SERIAL_CONTINUES: AtomicU64 = AtomicU64::new(0);
/// S104 Wave 0 — count of spark bodies *currently executing* (a worker running a
/// thunk in `ivar_force`'s claim-win arm), and its high-water mark. This is the
/// utilization signal M-dynamic will later read (measurement-only in Wave 0):
/// the number that must move parked→busy. Distinct from `IN_FLIGHT_SPARKS`
/// (reserved/created, not necessarily executing).
static SPARK_EXECUTING: AtomicI64 = AtomicI64::new(0);
static SPARK_PEAK_EXECUTING: AtomicU64 = AtomicU64::new(0);
static SPARK_STATS_ATEXIT: std::sync::Once = std::sync::Once::new();

fn spark_stats_enabled() -> bool {
    static E: LazyLock<bool> = LazyLock::new(|| {
        let on = std::env::var_os("CRANELISP_SPARK_STATS").is_some();
        if on {
            SPARK_STATS_ATEXIT.call_once(|| unsafe {
                libc::atexit(print_spark_stats);
            });
        }
        on
    });
    *E
}

/// RAII bracket around one executing spark body: inc `SPARK_EXECUTING` + bump the
/// peak high-water on entry, dec on exit (even on a Rust unwind). Constructed
/// **only** when spark-stats is enabled (`spark_stats_enabled().then(...)`), so
/// the executing/peak atomics never run on the hot path when off.
struct PeakGuard;

impl PeakGuard {
    fn enter() -> PeakGuard {
        let cur = (SPARK_EXECUTING.fetch_add(1, Ordering::Relaxed) + 1) as u64;
        let mut peak = SPARK_PEAK_EXECUTING.load(Ordering::Relaxed);
        while cur > peak {
            match SPARK_PEAK_EXECUTING.compare_exchange_weak(
                peak,
                cur,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(p) => peak = p,
            }
        }
        PeakGuard
    }
}

impl Drop for PeakGuard {
    fn drop(&mut self) {
        SPARK_EXECUTING.fetch_sub(1, Ordering::Relaxed);
    }
}

extern "C" fn print_spark_stats() {
    eprintln!(
        "[SPARK_STATS] spawns={} serial_continues={} peak_executing={} \
         force_calls={} force_fastpath_resolved={} force_claim_wins={} \
         force_spin_waits={} force_spin_iters={}",
        SPARK_SPAWNS.load(Ordering::Relaxed),
        SPARK_SERIAL_CONTINUES.load(Ordering::Relaxed),
        SPARK_PEAK_EXECUTING.load(Ordering::Relaxed),
        FORCE_CALLS.load(Ordering::Relaxed),
        FORCE_FASTPATH_RESOLVED.load(Ordering::Relaxed),
        FORCE_CLAIM_WINS.load(Ordering::Relaxed),
        FORCE_SPIN_WAITS.load(Ordering::Relaxed),
        FORCE_SPIN_ITERS.load(Ordering::Relaxed),
    );
}

/// IVar states.
const PENDING: i64 = 0;
const EVALUATING: i64 = 1;
const RESOLVED: i64 = 2;

/// **IVar-force wait policy** (`CRANELISP_IVAR_SPIN`, S104 Wave 2d). The
/// EVALUATING-wait arm of [`ivar_force`] (a thread that lost the claim CAS and
/// must wait for the claimant to publish RESOLVED) uses a **bounded backoff**
/// that yields the core, so N early-finishing waiters do not starve the 1
/// running straggler by busy-spinning at 100% CPU (the F3 floor violation:
/// imbalanced-search wall inflated ~7.5× over serial when idle waiters burned
/// the cores the straggler's own thread needed). The backoff escalates:
///
/// 1. a short bounded `spin_loop()` burst ([`WAIT_SPIN_BURST`]) — cheap and
///    latency-optimal for the overwhelmingly common fast-resolve case (the
///    claimant publishes within a few hundred ns);
/// 2. then a `yield_now()` burst ([`WAIT_YIELD_BURST`]) — hands the core to the
///    OS scheduler so the computing thread runs;
/// 3. then a capped short `sleep` ([`WAIT_SLEEP`]) for genuinely long waits — a
///    waiter blocked on a multi-second straggler parks instead of spinning,
///    freeing its core entirely.
///
/// Setting `CRANELISP_IVAR_SPIN=1` restores the pre-Wave-2d **pure busy-spin**
/// (`loop { load; spin_loop() }`) for A/B comparison. The wait policy is a
/// scheduling choice only — the CAS/state-machine protocol and the
/// work-conservation claim-compute semantics (module `//!` §State Machine, the
/// fork-join ferry) are byte-for-byte identical on either path; only the *wait*
/// changes. Read once per process via `LazyLock`.
static IVAR_SPIN: LazyLock<bool> =
    LazyLock::new(|| std::env::var("CRANELISP_IVAR_SPIN").is_ok_and(|v| v == "1"));

/// Backoff schedule for [`ivar_force`]'s EVALUATING-wait arm ([`IVAR_SPIN`]).
/// The first `WAIT_SPIN_BURST` wait iterations busy-spin (fast-resolve latency);
/// the next `WAIT_YIELD_BURST` yield the core; beyond that each iteration sleeps
/// `WAIT_SLEEP`. Tuned so a fast resolve pays only cheap spins while a long wait
/// (the F3 straggler) drops to a ~parked poll that does not starve the runner.
const WAIT_SPIN_BURST: u32 = 128;
const WAIT_YIELD_BURST: u32 = 512;
const WAIT_SLEEP: std::time::Duration = std::time::Duration::from_micros(50);

/// Global in-flight-spark counter — the reservation half of the backend
/// create-gate budget (`design/backend/lenient-eval.md` §3.6, Sprint 92).
///
/// Counts spark permits currently reserved against the pool. The backend's
/// create-gate calls [`spark_budget_try_reserve`] *before* allocating any
/// IVar/thunk: a granted batch of `n` permits commits `n` spawns (the lenient
/// arm); an over-budget reject commits zero (the direct arm — no allocation).
/// Each spawned spark releases exactly one permit on completion via
/// [`InFlightGuard`]'s drop, so `reserve(n)` ↔ `n` spawns ↔ `n` guard drops is
/// balanced by construction. This bounds *total* in-flight sparks (and thus
/// IVar/thunk allocation) to `O(cap)` regardless of recursion depth, restoring
/// the never-slower-than-serial floor for over-sparking shapes (e.g. naive
/// recursive `(add-i64 (fib …) (fib …))`).
///
/// `AtomicIsize` (not `Usize`): a stray over-decrement goes negative (still
/// `< cap` ⇒ keeps granting) rather than wrapping to a huge value that would
/// silently wedge the budget to permanent-direct.
///
/// The decision is invisible to the program result: the gate's lenient and
/// direct arms produce byte-for-byte identical values (spawned-vs-direct is a
/// scheduling choice only); only the allocation/concurrency profile differs.
static IN_FLIGHT_SPARKS: AtomicIsize = AtomicIsize::new(0);

/// The **saturation-shaped spark gate** toggle (`CRANELISP_SATURATION_GATE=1`,
/// Sprint 99 Wave 1c measurement spike, FIXME 0459).
///
/// **OFF by default** — a measurement spike under ablation, not yet default-on.
/// When unset the create-gate cap stays at the pre-S99 `4 × threads` static
/// budget, so the emitted code AND the runtime reservation are **byte-identical**
/// to before. When set, the cap drops to exactly `rayon::current_num_threads()`
/// — a *saturation* policy rather than a generous static budget: a batch is
/// granted (⇒ sparked) only while there is spare worker capacity right now
/// (`in_flight < threads`); once the pool is saturated the reservation is
/// rejected and the create-gate's **direct arm runs the branch INLINE** on the
/// current thread (the existing correct sequential lowering). Bounding
/// concurrent sparks at worker-count keeps the overflow subtree thread-local, so
/// its in-leaf vec-COW cell refcounts are touched by one thread instead of
/// bouncing across cores. The spark-vs-inline choice is a scheduling decision
/// only — both arms produce byte-identical values — so correctness holds on and
/// off by construction. Read once per process via `LazyLock`.
static SATURATION_GATE: LazyLock<bool> = LazyLock::new(|| {
    std::env::var("CRANELISP_SATURATION_GATE").is_ok_and(|v| v == "1")
});

/// **M-dynamic — the utilization-axis multiplier `k`** (S104 Wave 2, Stage 3;
/// `design/backend/lenient-eval.md` §2.8.3, gate G1). The in-flight-spark cap
/// defaults to `k × rayon::current_num_threads()` with **`k = 2`** (~2/core),
/// **default-on**. This is the utilization axis of the S104 utilization model:
/// the emergent ~2/core collapse (§2.8.3) is delivered by tightening this cap so
/// deeper spark sites see a full pool (`IN_FLIGHT_SPARKS ≥ cap`) and take the
/// create-gate's direct/inline arm, capping recursive over-sparking to ~2/core.
///
/// **NOT a new counter — a re-parameterization of the existing create-gate cap**
/// (§2.8.3; the FIXME-0442 one-counter ruling). Only the `SPARK_BUDGET` default
/// multiplier + its default polarity move (`4 → 2`, default-on); the
/// `spark_budget_try_reserve` primitive, `IN_FLIGHT_SPARKS`, and every codegen
/// seam are unchanged.
///
/// The env override `CRANELISP_SPARK_CORE_MULT=k` (gate G1) lets the single-shot
/// measurement sweep `k` cheaply — it is the tunable ~2/core knob AND the
/// M-dynamic on/off selector for the `{mstatic-only, mdynamic-only, both}`
/// measurement configs:
/// - `k = 2` — M-dynamic default (the ~2/core cap collapse; the shipped policy);
/// - `k = 1` — tightest collapse (== the [`SATURATION_GATE`] cap);
/// - `k = 4` — the **pre-Wave-2 default**, i.e. **M-dynamic effectively OFF**
///   (the old `4 × threads` static budget — use this for the `mstatic-only` row);
/// - `k = 0` — cap `0` ⇒ [`spark_budget_try_reserve`] always rejects ⇒ fully
///   serial (identical to `CRANELISP_SPARK_BUDGET=0`).
///
/// A non-parsing value falls back to the default `2`. Read once per process via
/// `LazyLock`. Lower precedence than an explicit `CRANELISP_SPARK_BUDGET=N` and
/// than [`SATURATION_GATE`] (see [`effective_spark_cap`]).
static SPARK_CORE_MULT: LazyLock<usize> = LazyLock::new(|| {
    std::env::var("CRANELISP_SPARK_CORE_MULT")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or(2)
});

/// The cap on [`IN_FLIGHT_SPARKS`]. Default `k × rayon::current_num_threads()`
/// with **`k = 2`** (M-dynamic, S104 Wave 2 — the ~2/core utilization cap;
/// [`SPARK_CORE_MULT`]). `k` is enough slack for load imbalance while keeping
/// live IVar/thunk memory and scheduler pressure `O(threads)` and capping
/// recursive over-sparking to ~2/core. The env override
/// `CRANELISP_SPARK_BUDGET=N` sets the cap explicitly (style consistent with
/// `CRANELISP_NO_LENIENT`); a non-parsing value falls back to the default; `=0`
/// makes [`spark_budget_try_reserve`] always reject ⇒ every gate site takes the
/// direct arm (≡ fully serial at the runtime layer). `CRANELISP_SPARK_CORE_MULT=k`
/// re-parameterizes the multiplier (default-on M-dynamic; `k=4` recovers the
/// pre-Wave-2 `4×` budget). The `CRANELISP_SATURATION_GATE=1` toggle (with no
/// explicit budget) tightens the cap to exactly the worker count (`1×`); see
/// [`effective_spark_cap`], [`SATURATION_GATE`], and [`SPARK_CORE_MULT`]. Read
/// once per process via `LazyLock`.
static SPARK_BUDGET: LazyLock<usize> = LazyLock::new(|| {
    let explicit = std::env::var("CRANELISP_SPARK_BUDGET")
        .ok()
        .and_then(|v| v.parse::<usize>().ok());
    effective_spark_cap(
        explicit,
        *SATURATION_GATE,
        *SPARK_CORE_MULT,
        rayon::current_num_threads(),
    )
});

/// Compute the in-flight-spark cap from the four inputs, kept pure and
/// side-effect-free so the policy is unit-testable without touching the
/// process-global `LazyLock`/env (Principle 5 — testability is structural).
///
/// Precedence:
/// 1. an explicit `CRANELISP_SPARK_BUDGET=N` override always wins (a manual cap);
/// 2. else the **saturation gate** caps at exactly `num_threads` — spark iff a
///    worker is free right now, else inline the overflow (Wave 1c, `1×`);
/// 3. else the **M-dynamic** default `core_mult × num_threads` — the ~2/core
///    utilization cap with `core_mult = 2` by default (S104 Wave 2, §2.8.3).
///    `core_mult = 4` recovers the pre-Wave-2 static budget (M-dynamic off);
///    `core_mult = 0` yields cap `0` (always-reject ⇒ fully serial).
fn effective_spark_cap(
    explicit: Option<usize>,
    saturation_gate: bool,
    core_mult: usize,
    num_threads: usize,
) -> usize {
    if let Some(n) = explicit {
        return n;
    }
    if saturation_gate {
        return num_threads;
    }
    core_mult * num_threads
}

/// Whether a batch of `n` permits fits under `cap` given `cur` already in
/// flight. `true` ⇒ spare capacity ⇒ grant (spark); `false` ⇒ saturated /
/// over-budget ⇒ reject (the caller inlines the branch via the direct arm).
/// All-or-nothing: a batch overflowing the cap by even 1 does not fit.
fn budget_grants(cur: isize, n: isize, cap: isize) -> bool {
    cur + n <= cap
}

/// RAII release of one [`IN_FLIGHT_SPARKS`] permit. Placed at the top of the
/// spawned rayon closure so the permit reserved by the create-gate's
/// [`spark_budget_try_reserve`] is released exactly once per spark — even on a
/// Rust unwind (an allocation failure or internal bug), not just on normal
/// completion. A *leaked* permit is the dangerous direction: it would
/// permanently lower the effective budget, drifting the system toward
/// permanent-direct (silent serial degradation no test would obviously catch).
/// See `design/backend/lenient-eval.md` §3.6 "Release accounting".
struct InFlightGuard;

impl Drop for InFlightGuard {
    fn drop(&mut self) {
        IN_FLIGHT_SPARKS.fetch_sub(1, Ordering::SeqCst);
    }
}

// **Hierarchical decline — depth-allowance form** (S104 Wave 2b→2e, gate G3;
// `design/backend/lenient-eval.md` §2.8.4). A thread-local **spark-nesting depth
// counter** ([`SPARK_DEPTH`]): the logical nesting depth of the spark body the
// current thread is executing. The top call (main, no thunk) is depth 0; every
// level deeper into the spark tree is +1. A nested create-gate site takes the
// inline/direct arm (`spark_budget_try_reserve` returns `0`) only when
// `SPARK_DEPTH >= SPARK_MAX_DEPTH`; **below** that threshold a strand MAY re-spark
// (still subject to the ~2/core `IN_FLIGHT_SPARKS` cap). So the top `MAX_DEPTH`
// levels of the spark tree fan out; everything below inlines.
//
// **Why a depth allowance, not a boolean (Wave 2e).** The Wave-2c boolean form
// ("inside a spark body ⇒ inline everything") collapsed each dispatched strand's
// ENTIRE subtree to one sequential unit. That bounds spawns to `O(cores)` (curing
// F5's 619K-spawn fib explosion) but also caps a *balanced coarse* tree to the
// handful of splits the main spine can reach on its own (F6: peak ~8, ~1.9×) —
// it leaves a balanced compute D&C's parallelism on the table. The depth counter
// generalizes the boolean: `MAX_DEPTH = 1` reproduces the Wave-2c collapse
// (dispatched strands inline immediately); a larger `MAX_DEPTH` lets a *bounded*
// tree keep fanning out for `MAX_DEPTH` levels — up to `2^MAX_DEPTH` inline
// strands — so a balanced 16-leaf tree (F6) fills the cores while a deep recursion
// (F5 fib) still collapses once it descends past `MAX_DEPTH` (`2^MAX_DEPTH` spawns
// then inline, independent of recursion depth).
//
// **Why structural, not emergent.** The concurrent-cap (`SPARK_BUDGET`) bounds
// *concurrent* in-flight sparks (memory footprint = `O(cap)`) but **permits
// recycle**: when a strand completes it frees a permit and the next recursive
// node grabs it and sparks again, so *total* spawn count over a recursion stays
// `O(nodes)` — the 0534 scheduler overhead. The cap is the wrong lever for spawn
// *rate*. The depth cutoff collapses it structurally: once a strand descends past
// `MAX_DEPTH` its whole remaining subtree runs sequentially with no nested
// sparking, so total spawns stay `~2^MAX_DEPTH = O(cores)`.
//
// **Depth is the *logical* tree depth, propagated across the spawn boundary.**
// The counter is incremented by +1 in `ivar_force`'s claim-compute arm (the single
// choke point where a thunk runs — reached both from `ivar_spark`'s dispatched
// closure AND from an inline barrier-force). To keep a *stolen* child at its true
// logical depth (a fresh rayon worker rests at 0, not at its parent's depth),
// `ivar_spark` captures the sparking thread's depth and its spawned closure
// restores that base before running `ivar_force` — so the claim-arm +1 lands the
// child at `parent + 1` whether it runs inline or on a stolen worker. The counter
// is a module-private thread-local — **no new export**.
//
// **Symmetric across main and workers (Wave 2e).** Unlike the Wave-2c worker-only
// boolean (which deliberately did NOT flag the main-thread claim arm, to keep the
// main spine sparking), the depth model increments on BOTH the main and worker
// claim arms: the main spine now *also* inlines once it descends past `MAX_DEPTH`,
// and the Wave-2c "worker-only vs both-paths" hazard is gone — the both-paths
// boolean collapsed to ~2 cores only because a depth-1 flag inlined the WHOLE
// remaining subtree; a `MAX_DEPTH`-deep allowance lets the main spine spark its
// top `MAX_DEPTH` levels before inlining, so cores stay fed.
thread_local! {
    static SPARK_DEPTH: Cell<u32> = const { Cell::new(0) };
}

/// Compute the default [`SPARK_MAX_DEPTH`] from the worker count: `floor(log2(n))`
/// (clamped to `≥ 1`). Kept pure for unit testing (Principle 5).
///
/// A depth-`D` cutoff lets the spark tree fan out to up to `2^D` strands before
/// inlining. The default is deliberately **conservative** — `2^D ≤ n`, half the
/// `2 × n` concurrent [`SPARK_BUDGET`] cap — for a measured reason: the depth
/// counter only advances at `ivar_force` boundaries, so a *budget-induced* inline
/// (a create-gate declined because [`IN_FLIGHT_SPARKS`] is at the cap, not because
/// the depth allowance is spent) direct-calls its child at the SAME fork-depth. A
/// deep recursion (e.g. F5's `fib`) that gets budget-inlined at a shallow depth
/// then re-sparks via permit-recycle at that shallow depth — the 0534 spawn
/// explosion — once the fan-out approaches the concurrent cap and the depth cutoff
/// no longer bites first. Keeping `2^D ≤ n` (fan-out well under the `2n` cap) makes
/// the depth cutoff bite *before* budget pressure, so a deep recursion collapses to
/// `~2^D` spawns while a bounded coarse tree (F6: 16 alloc-free leaves) still fans
/// out to fill the cores (measured on a 10-core host: `D = 3` ⇒ F6 peak≈12,
/// ~3.4×; F5 stays at 14 spawns; `D ≥ 4` re-explodes F5 to >1M spawns via the
/// budget-inline leak). `n ≤ 1` clamps to depth 1 (the Wave-2c boolean collapse).
///
/// `CRANELISP_SPARK_MAX_DEPTH=D` overrides this for the ablation sweep; a larger
/// `D` on an alloc-free shape (F6) is safe and faster, but risks the budget-inline
/// re-explosion on deep alloc-heavy recursions — the leak is a backend/design
/// concern (the direct/inline arm has no runtime hook to advance the depth, so it
/// cannot be closed in the runtime alone; `design/backend/lenient-eval.md` §2.8.4).
fn default_spark_max_depth(num_threads: usize) -> u32 {
    if num_threads <= 1 {
        return 1;
    }
    // floor(log2(n)) = (bit width of n) − 1 = index of the highest set bit.
    u32::BITS - 1 - (num_threads as u32).leading_zeros()
}

/// The **spark-nesting depth allowance** `MAX_DEPTH` (`CRANELISP_SPARK_MAX_DEPTH`,
/// S104 Wave 2e, gate G3). A create-gate site inlines (declines to spark) once the
/// current thread's [`SPARK_DEPTH`] reaches this value, so the top `MAX_DEPTH`
/// levels of the spark tree fan out and everything below runs sequentially. Read
/// once per process via `LazyLock`.
///
/// Default: [`default_spark_max_depth`]`(rayon::current_num_threads())` —
/// `floor(log2(threads))`, a conservative allowance that fans a balanced tree out
/// to ~`threads` strands while keeping the fan-out under the concurrent
/// [`SPARK_BUDGET`] cap so a deep recursion still collapses (see
/// [`default_spark_max_depth`] for the budget-inline-leak rationale).
/// `CRANELISP_SPARK_MAX_DEPTH=D` overrides it:
/// - `D = 0` ⇒ every site inlines (`SPARK_DEPTH ≥ 0` always) — fully collapsed,
///   ≡ the pre-lenient serial floor at the runtime layer;
/// - `D = 1` ⇒ the Wave-2c boolean collapse (a dispatched strand inlines its whole
///   subtree; only the main spine's top split sparks);
/// - larger `D` ⇒ up to `2^D` inline strands.
///
/// A non-parsing value falls back to the computed default. Orthogonal to
/// [`HIER_DECLINE_ON`] (`CRANELISP_HIER_DECLINE=0` disables the depth check
/// entirely).
static SPARK_MAX_DEPTH: LazyLock<u32> = LazyLock::new(|| {
    std::env::var("CRANELISP_SPARK_MAX_DEPTH")
        .ok()
        .and_then(|v| v.parse::<u32>().ok())
        .unwrap_or_else(|| default_spark_max_depth(rayon::current_num_threads()))
});

/// The **hierarchical-decline** on/off toggle (`CRANELISP_HIER_DECLINE`, S104
/// Wave 2b; depth-allowance form since Wave 2e, gate G3). `0`/`off` ⇒ the depth
/// mechanism is disabled entirely (the [`SPARK_DEPTH`] counter is never touched
/// and [`spark_budget_try_reserve`] never consults it) — the emergent-cap
/// ablation, where only the concurrent [`SPARK_BUDGET`] cap throttles. Anything
/// else (including unset) ⇒ on (the default depth-allowance form). Read once per
/// process via `LazyLock`.
static HIER_DECLINE_ON: LazyLock<bool> = LazyLock::new(|| {
    !matches!(
        std::env::var("CRANELISP_HIER_DECLINE").as_deref(),
        Ok("0") | Ok("off")
    )
});

/// RAII bracket over one level of spark-nesting depth. Two constructors:
///
/// - [`enter`](SparkDepthGuard::enter) — `+1`: descend one spark level. Armed
///   around the `call(thunk)` in [`ivar_force`]'s claim-compute arm (the single
///   choke point where a thunk runs), so a thunk at logical depth `k` executes
///   with [`SPARK_DEPTH`]` == k`.
/// - [`enter_base`](SparkDepthGuard::enter_base) — restore a captured parent
///   depth: armed at the top of [`ivar_spark`]'s spawned closure so a *stolen*
///   child (running on a fresh worker that rests at depth 0) picks up its parent's
///   depth before the claim-arm `+1` lands it at `parent + 1`.
///
/// Both save the previous value and restore it on drop — even on a Rust unwind out
/// of the thunk — so nested brackets never corrupt an outer strand's depth.
struct SparkDepthGuard(u32);

impl SparkDepthGuard {
    /// Descend one level (`SPARK_DEPTH += 1`), saving the previous depth.
    fn enter() -> SparkDepthGuard {
        SparkDepthGuard(SPARK_DEPTH.with(|c| {
            let prev = c.get();
            c.set(prev + 1);
            prev
        }))
    }

    /// Restore a captured `base` depth (used to propagate a parent's depth to a
    /// stolen child), saving the previous depth.
    fn enter_base(base: u32) -> SparkDepthGuard {
        SparkDepthGuard(SPARK_DEPTH.with(|c| c.replace(base)))
    }
}

impl Drop for SparkDepthGuard {
    fn drop(&mut self) {
        SPARK_DEPTH.with(|c| c.set(self.0));
    }
}

/// Try to reserve `n` permits for the `n` sparkable arguments/bindings of one
/// backend create-gate site (`design/backend/lenient-eval.md` §3.6.1).
///
/// Returns `1` if the **whole** batch was granted — the caller MUST then
/// create+spark exactly `n` IVars, each of which releases one permit on
/// completion via [`InFlightGuard`]'s drop. Returns `0` if over budget — the
/// caller MUST take the direct arm and allocate nothing.
///
/// All-or-nothing and TOCTOU-free: the `n` permits are committed in a single CAS
/// so `cap` is a genuine bound, not a soft target that N concurrent sites each
/// blow past. The over-budget path is **load-only** (no RMW) — keeping the
/// per-node floor residual tiny under an over-sparking explosion. `cap == 0`
/// (env `CRANELISP_SPARK_BUDGET=0`) ⇒ `cur + n > 0` for all `n ≥ 1` ⇒ always
/// rejects ⇒ every site takes the direct arm (≡ fully serial at the runtime
/// layer). SeqCst throughout (Decision 13).
#[unsafe(export_name = "cranelisp_spark_budget_try_reserve")]
pub extern "C" fn spark_budget_try_reserve(n: i64) -> i64 {
    let cap = *SPARK_BUDGET as isize;
    let n = n as isize;
    let stats = spark_stats_enabled();
    // Structural hierarchical decline — depth-allowance form (§2.8.4, gate G3,
    // Wave 2e): if this thread's spark-nesting depth has reached MAX_DEPTH, every
    // nested candidate takes the inline/direct arm — independent of the concurrent
    // counter — so once a strand descends past the allowance its ENTIRE remaining
    // subtree runs sequentially with no further sparking. Below MAX_DEPTH a strand
    // MAY re-spark (subject to the concurrent cap), letting a bounded tree fan out
    // to ~2^MAX_DEPTH strands. Gated by CRANELISP_HIER_DECLINE (default-on); when
    // off, the depth is ignored and only the concurrent cap throttles (the
    // emergent-cap ablation).
    if *HIER_DECLINE_ON && SPARK_DEPTH.with(|c| c.get()) >= *SPARK_MAX_DEPTH {
        if stats {
            SPARK_SERIAL_CONTINUES.fetch_add(1, Ordering::Relaxed);
        }
        return 0;
    }
    // Fast reject (the common case under explosion): a single load, no RMW.
    if !budget_grants(IN_FLIGHT_SPARKS.load(Ordering::SeqCst), n, cap) {
        if stats {
            SPARK_SERIAL_CONTINUES.fetch_add(1, Ordering::Relaxed);
        }
        return 0;
    }
    // Commit the whole batch atomically (CAS loop) — all-or-nothing.
    loop {
        let cur = IN_FLIGHT_SPARKS.load(Ordering::SeqCst);
        if !budget_grants(cur, n, cap) {
            if stats {
                SPARK_SERIAL_CONTINUES.fetch_add(1, Ordering::Relaxed);
            }
            return 0;
        }
        if IN_FLIGHT_SPARKS
            .compare_exchange(cur, cur + n, Ordering::SeqCst, Ordering::SeqCst)
            .is_ok()
        {
            return 1;
        }
    }
}

/// Field offsets from base pointer (base-pointer convention).
const STATE_OFFSET: isize = 16;
const VALUE_OFFSET: isize = 24;
const THUNK_OFFSET: isize = 32;
const ERROR_OFFSET: isize = 40;
const RC_OFFSET: isize = 8;

/// Offset of code_ptr within a closure (Decision 11).
/// Closure layout: [header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]
const CLOSURE_CODE_PTR_OFFSET: isize = 16;

/// Offset of drop_glue_ptr within a closure from the base pointer.
const CLOSURE_DROP_GLUE_OFFSET: isize = 24;

/// Allocate an IVar cell. Sets state=PENDING, stores the thunk pointer.
/// Returns the base pointer.
///
/// The thunk is a zero-arg Cranelisp closure with HeapClosure layout.
///
/// # Safety
/// `thunk` must be a valid base pointer to a HeapClosure with rc > 0.
#[unsafe(export_name = "cranelisp_ivar_create")]
pub extern "C" fn ivar_create(thunk: i64) -> i64 {
    // 32 bytes payload: state(8) + value(8) + thunk(8) + error(8)
    // allocator adds 16-byte header = 48 bytes total
    let base = alloc_with_rc(32);
    // SAFETY: base is a valid allocation of 48 bytes. We write fields at
    // known offsets within the payload area.
    unsafe {
        *((base as isize + STATE_OFFSET) as *mut i64) = PENDING;
        *((base as isize + VALUE_OFFSET) as *mut i64) = 0;
        *((base as isize + THUNK_OFFSET) as *mut i64) = thunk;
        *((base as isize + ERROR_OFFSET) as *mut i64) = 0;
    }
    base as i64
}

/// Increment the IVar's RC and submit a force-and-dec task to the rayon
/// global thread pool.
///
/// **Always spawns** (`design/backend/lenient-eval.md` §3.4, Sprint 92). The
/// spawn-vs-direct decision is no longer taken here — the backend's create-gate
/// (§3.6) already decided this cell is worth sparking, via a runtime
/// [`spark_budget_try_reserve`] check emitted *before* the IVar was even
/// allocated. By the time `ivar_spark` runs, the lenient arm has been chosen, so
/// the only correct action is to spawn. The spawn task releases its one reserved
/// spark-budget permit on completion (or unwind) via [`InFlightGuard`]'s drop.
///
/// # Safety
/// `ivar` must be a valid base pointer to an IVar with rc > 0.
#[unsafe(export_name = "cranelisp_ivar_spark")]
pub extern "C" fn ivar_spark(ivar: i64) -> i64 {
    // Inc RC — the spark task holds a reference.
    //
    // Deliberate, owned divergence from the blessed `rc::rc_inc` entry point
    // (which is Release). This inc KEEPS SeqCst: it is load-bearing — paired
    // with the spark's later `fetch_sub(1, SeqCst)` on the same RC field and
    // interleaved with the IVar state-machine's SeqCst atomics (STATE_OFFSET
    // CAS, the value/error publish-stores). The module discipline is "all
    // atomics use SeqCst (Decision 13)" (see module `//!`), a single uniform
    // total order the fork-join correctness argument is verified against.
    // Demoting this one atomic to Release would break that invariant for no
    // benefit (one inc per spark, not a hot path). Per `/arch` ruling:
    // FIXME 0397; `design/arch/bounded-contexts.md` §4b invariant 3 (table row
    // `ivar.rs::ivar_spark` — KEEP SeqCst). Do NOT route this through `rc_inc`.
    // SAFETY: ivar is a valid base pointer; RC at offset 8 is an aligned i64.
    unsafe {
        let rc_ptr = (ivar as isize + RC_OFFSET) as *const AtomicI64;
        (*rc_ptr).fetch_add(1, Ordering::SeqCst);
    }

    if spark_stats_enabled() {
        SPARK_SPAWNS.fetch_add(1, Ordering::Relaxed);
    }

    // Structural hierarchical decline (§2.8.4, gate G3, Wave 2e). Capture the
    // sparking thread's current spark-nesting depth so a *stolen* child — which
    // may run on a fresh rayon worker resting at depth 0 — is placed at its true
    // logical depth. The spawned closure restores this base before forcing, so the
    // claim-arm +1 in `ivar_force` lands the child at `parent + 1` regardless of
    // which worker ends up running it. Read only when the mechanism is on.
    let parent_depth = if *HIER_DECLINE_ON {
        SPARK_DEPTH.with(|c| c.get())
    } else {
        0
    };

    rayon::spawn(move || {
        // Release the in-flight-spark reservation on normal completion OR on a
        // Rust unwind (§3.6). Placed FIRST so its `drop` runs last, after the
        // RC dec below — and runs even if anything in this closure unwinds.
        let _in_flight_guard = InFlightGuard;

        // Restore the captured parent depth for the dynamic extent of this
        // dispatched spark (§2.8.4, gate G3, Wave 2e): the fresh worker rests at
        // depth 0, so without this a stolen deep child would look shallow and
        // over-spark. `ivar_force`'s claim arm then adds the +1 that lands the
        // thunk at `parent + 1`. Armed in every mode but off; the guard restores
        // the worker's resting depth on scope exit even if `ivar_force` unwinds.
        {
            let _depth_base =
                (*HIER_DECLINE_ON).then(|| SparkDepthGuard::enter_base(parent_depth));
            // Force the IVar (evaluate thunk if still PENDING).
            ivar_force(ivar);
        }

        // The ferry stashes any thunk panic in the IVar's error field and
        // `ivar_force` re-raises it into THIS (worker) thread's slot. The worker
        // is throwaway and its slot must not pollute later rayon work scheduled
        // onto the same thread, so clear it here — the joining `ivar_force` on
        // the consuming thread re-raises from the IVar field independently
        // (test-discovery.md §6).
        let _ = crate::panic::take_runtime_error();

        // Dec RC — spark task's reference is released.
        // SAFETY: ivar is still valid (we hold a reference from the inc above).
        let old_rc = unsafe {
            let rc_ptr = (ivar as isize + RC_OFFSET) as *const AtomicI64;
            (*rc_ptr).fetch_sub(1, Ordering::SeqCst)
        };

        if old_rc == 1 {
            // RC reached 0 — free the IVar (and its ferried error String, if any).
            std::sync::atomic::fence(Ordering::Acquire);
            // SAFETY: RC was 1 (now 0), no other references exist.
            unsafe { dealloc_ivar(ivar) };
        }
    });

    0
}

/// Deallocate an IVar cell, first freeing any ferried error String it holds.
///
/// The fork-join error-slot ferry (test-discovery.md §6) may stash a heap String
/// pointer in the cell's `error` field (offset 40) when a sparked thunk panics.
/// `reraise_ferried_error` decodes that String *without consuming it* so every
/// joiner re-raises the same message, which means the String outlives every read
/// and must be freed when the cell itself is freed. Both production dealloc paths
/// — `ivar_spark`'s RC-to-0 branch and the backend's `emit_rc_dec_for_ivar`
/// (which calls this symbol) — route through here so neither leaks the String.
///
/// The error String is always rc=1 (created fresh by the worker in `ivar_force`,
/// never shared), so a plain `dealloc` is correct — no RC dec is required.
///
/// # Safety
/// `ivar` must be a valid IVar base pointer whose RC has reached 0.
#[unsafe(export_name = "cranelisp_ivar_dealloc")]
pub extern "C" fn ivar_dealloc(ivar: i64) -> i64 {
    // SAFETY: caller guarantees `ivar` is a valid IVar base pointer at rc=0.
    unsafe { dealloc_ivar(ivar) };
    0
}

/// Inner helper: free the ferried error String (if non-null) then the cell.
///
/// # Safety
/// `ivar` must be a valid IVar base pointer whose RC has reached 0.
unsafe fn dealloc_ivar(ivar: i64) {
    // SAFETY: ivar is a valid base pointer; error at offset 40 is an aligned i64.
    let error_str = unsafe { *((ivar as isize + ERROR_OFFSET) as *const i64) };
    if error_str != 0 {
        // The ferried error is a plain HeapString with no recursive heap fields
        // and rc=1 — free it directly.
        // SAFETY: a non-zero error field is a valid HeapString base pointer.
        unsafe { dealloc(error_str as *mut u8) };
    }
    // SAFETY: caller guarantees rc reached 0; no other references exist.
    unsafe { dealloc(ivar as *mut u8) };
}

/// Force an IVar to resolution. Returns the result value.
///
/// - If PENDING: CAS to EVALUATING, call thunk, store result, set RESOLVED.
/// - If EVALUATING: spin-wait until RESOLVED.
/// - If RESOLVED: return value immediately.
///
/// # Safety
/// `ivar` must be a valid base pointer to an IVar with rc > 0.
#[unsafe(export_name = "cranelisp_ivar_force")]
pub extern "C" fn ivar_force(ivar: i64) -> i64 {
    // SAFETY: ivar is a valid base pointer. state at offset 16 is an aligned i64.
    let state_ptr = unsafe { &*((ivar as isize + STATE_OFFSET) as *const AtomicI64) };

    let stats = spark_stats_enabled();
    if stats {
        FORCE_CALLS.fetch_add(1, Ordering::Relaxed);
    }

    // Fast path: already resolved.
    let state = state_ptr.load(Ordering::SeqCst);
    if state == RESOLVED {
        if stats {
            FORCE_FASTPATH_RESOLVED.fetch_add(1, Ordering::Relaxed);
        }
        reraise_ferried_error(ivar);
        return unsafe { *((ivar as isize + VALUE_OFFSET) as *const i64) };
    }

    // Try to claim the thunk.
    match state_ptr.compare_exchange(PENDING, EVALUATING, Ordering::SeqCst, Ordering::SeqCst) {
        Ok(_) => {
            if stats {
                FORCE_CLAIM_WINS.fetch_add(1, Ordering::Relaxed);
            }
            // We won the CAS — evaluate the thunk.
            let thunk = unsafe { *((ivar as isize + THUNK_OFFSET) as *const i64) };

            // Load code_ptr from the closure (offset 16 from base pointer).
            let code_ptr = unsafe { *((thunk as isize + CLOSURE_CODE_PTR_OFFSET) as *const i64) };

            // First-error-wins protection for INLINE thunk execution (§12.4.3,
            // `design/backend/lenient-eval.md` §3.6 "Ferry soundness — inline
            // spark"). On the inline-claim path (the budget's over-cap branch,
            // or any time the consuming thread itself wins this CAS) the calling
            // thread IS the consumer, so its runtime-error slot may already hold
            // a FIRST error set by an earlier barrier-forced sibling. The thunk
            // about to run calls `runtime_panic`, which UNCONDITIONALLY
            // overwrites that slot; the `take_runtime_error` below would then
            // clear it — clobbering first-error-wins. Save the caller's slot
            // before the thunk and restore it (first-error-wins) afterward so an
            // inline panic can never stomp an already-set first error. On the
            // spawn path the thunk runs on a throwaway worker slot (empty),
            // making this save/restore a harmless no-op there — keeping
            // `ivar_force` uniform across the inline and spawned paths.
            let saved_caller_error = crate::panic::take_runtime_error();

            // Call code_ptr(env_ptr) where env_ptr is the thunk's base pointer.
            let call: extern "C" fn(i64) -> i64 =
                unsafe { std::mem::transmute(code_ptr as *const ()) };
            // S104 Wave 0 — bracket the executing spark body so
            // SPARK_PEAK_EXECUTING records the max concurrent bodies (the
            // utilization signal). Only armed when spark-stats is on; dropped
            // right after the thunk returns so the count reflects *executing*,
            // not merely-claimed, sparks.
            let peak_guard = stats.then(PeakGuard::enter);
            // Structural hierarchical decline — depth-allowance form (§2.8.4, gate
            // G3, Wave 2e). This is the SINGLE choke point where a thunk runs —
            // reached both from `ivar_spark`'s dispatched worker closure AND from an
            // inline barrier-force on the main thread or a worker. Descend one spark
            // level around the call so a thunk at logical depth `k` executes with
            // `SPARK_DEPTH == k`: combined with `ivar_spark`'s base-restore, this
            // gives `parent + 1` whether the child ran inline or on a stolen worker.
            // Symmetric across main and workers (no worker-only exemption): the depth
            // allowance lets the main spine spark its top MAX_DEPTH levels before
            // inlining, so the Wave-2c both-paths collapse-to-2-cores hazard (a
            // depth-1 flag inlining the WHOLE subtree) does not recur. Scoped tightly
            // around the call so it restores even if the thunk unwinds.
            let result = {
                let _depth_guard = (*HIER_DECLINE_ON).then(SparkDepthGuard::enter);
                call(thunk)
            };
            drop(peak_guard);

            // Fork-join error-slot ferry (worker-side): if the thunk raised a
            // runtime panic, it landed in THIS thread's slot. Take it and stash
            // it in the IVar's error field so the joining thread can re-raise it
            // (test-discovery.md §6). Sentinel `result` (0) is published as-is.
            let error_str = match crate::panic::take_runtime_error() {
                Some(msg) => crate::heap_string::alloc_string(msg.as_bytes()) as i64,
                None => 0,
            };

            // Restore the caller's pre-existing first error (first-error-wins):
            // if the slot already held a first error, it goes back BEFORE the
            // join-side re-raise, so this cell's later error cannot displace it.
            if let Some(msg) = saved_caller_error {
                crate::panic::set_runtime_error(msg);
            }

            // Store result + error, then publish RESOLVED state (the release of
            // both fields to spin-waiters).
            unsafe {
                *((ivar as isize + VALUE_OFFSET) as *mut i64) = result;
                *((ivar as isize + ERROR_OFFSET) as *mut i64) = error_str;
            }
            state_ptr.store(RESOLVED, Ordering::SeqCst);

            // Join-side re-raise on the claimant's own thread (first-error-wins).
            reraise_ferried_error(ivar);

            // Dec the thunk closure's RC. The thunk was created with rc=1
            // and is no longer needed after evaluation. Call its drop glue
            // (if any) to dec captured heap values, then dec/free the
            // closure itself.
            unsafe {
                let drop_glue_ptr =
                    *((thunk as isize + CLOSURE_DROP_GLUE_OFFSET) as *const i64);
                if drop_glue_ptr != 0 {
                    // Drop glue signature: extern "C" fn(env_ptr: i64) -> i64
                    let drop_glue: extern "C" fn(i64) -> i64 =
                        std::mem::transmute(drop_glue_ptr as *const ());
                    drop_glue(thunk);
                }
                // Dec the thunk closure's own RC.
                let rc_ptr = (thunk as isize + RC_OFFSET) as *const AtomicI64;
                let old_rc = (*rc_ptr).fetch_sub(1, Ordering::SeqCst);
                if old_rc == 1 {
                    std::sync::atomic::fence(Ordering::Acquire);
                    dealloc(thunk as *mut u8);
                }
            }

            result
        }
        Err(_) => {
            if stats {
                FORCE_SPIN_WAITS.fetch_add(1, Ordering::Relaxed);
            }
            // Another thread claimed it — wait until RESOLVED. Bounded backoff
            // that yields the core (S104 Wave 2d, [`IVAR_SPIN`]): a short spin
            // burst (cheap for the common fast-resolve case), then `yield_now`,
            // then a capped short sleep — so N early-finishing waiters do NOT
            // busy-spin at 100% CPU and starve the 1 running straggler (the F3
            // imbalanced-search floor violation). `CRANELISP_IVAR_SPIN=1`
            // restores the pure busy-spin for comparison. The wait is the ONLY
            // thing that changes: the RESOLVED handshake / ferry re-raise is
            // identical to the pure-spin path.
            let pure_spin = *IVAR_SPIN;
            let mut waits: u32 = 0;
            loop {
                if stats {
                    FORCE_SPIN_ITERS.fetch_add(1, Ordering::Relaxed);
                }
                let s = state_ptr.load(Ordering::SeqCst);
                if s == RESOLVED {
                    // Join-side re-raise: a panic captured by the claimant is
                    // published in the error field under the RESOLVED store
                    // (test-discovery.md §6).
                    reraise_ferried_error(ivar);
                    return unsafe { *((ivar as isize + VALUE_OFFSET) as *const i64) };
                }
                if pure_spin {
                    std::hint::spin_loop();
                    continue;
                }
                // Escalating backoff: spin → yield → capped sleep.
                waits = waits.saturating_add(1);
                if waits <= WAIT_SPIN_BURST {
                    std::hint::spin_loop();
                } else if waits <= WAIT_SPIN_BURST + WAIT_YIELD_BURST {
                    std::thread::yield_now();
                } else {
                    std::thread::sleep(WAIT_SLEEP);
                }
            }
        }
    }
}

/// Re-raise a ferried thunk panic into the calling thread's slot
/// (first-error-wins, test-discovery.md §6). Reads the IVar's `error` field
/// (valid once RESOLVED): a non-zero heap-String ptr is decoded and set via
/// `panic::set_runtime_error`. Idempotent — calling it from multiple readers
/// keeps the FIRST error in each reader's slot.
///
/// The error String is left in the IVar's field (freed with the IVar by
/// `ivar_dealloc`); decoding it does not consume it, so every joiner sees the
/// same message.
fn reraise_ferried_error(ivar: i64) {
    // SAFETY: caller observed RESOLVED before calling, so the error field is
    // published. A non-zero value is a valid heap-String base pointer.
    let error_str = unsafe { *((ivar as isize + ERROR_OFFSET) as *const i64) };
    if error_str != 0 {
        let msg = unsafe { crate::heap_string::read_str_for_ferry(error_str) };
        crate::panic::set_runtime_error(msg);
    }
}

#[cfg(test)]
mod tests;
