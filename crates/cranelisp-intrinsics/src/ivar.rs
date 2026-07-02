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

use std::sync::LazyLock;
use std::sync::atomic::{AtomicI64, AtomicIsize, Ordering};

use crate::alloc::{alloc_with_rc, dealloc};

/// IVar states.
const PENDING: i64 = 0;
const EVALUATING: i64 = 1;
const RESOLVED: i64 = 2;

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

/// The cap on [`IN_FLIGHT_SPARKS`]. Default `4 × rayon::current_num_threads()`
/// (a small multiple of the pool width — enough slack for load imbalance while
/// keeping live IVar/thunk memory and scheduler pressure `O(threads)`). The env
/// override `CRANELISP_SPARK_BUDGET=N` sets it explicitly (style consistent with
/// `CRANELISP_NO_LENIENT`); a non-parsing value falls back to the default; `=0`
/// makes [`spark_budget_try_reserve`] always reject ⇒ every gate site takes the
/// direct arm (≡ fully serial at the runtime layer). The
/// `CRANELISP_SATURATION_GATE=1` toggle (with no explicit budget) tightens the
/// default to exactly the worker count (see [`effective_spark_cap`] and
/// [`SATURATION_GATE`]). Read once per process via `LazyLock`.
static SPARK_BUDGET: LazyLock<usize> = LazyLock::new(|| {
    let explicit = std::env::var("CRANELISP_SPARK_BUDGET")
        .ok()
        .and_then(|v| v.parse::<usize>().ok());
    effective_spark_cap(explicit, *SATURATION_GATE, rayon::current_num_threads())
});

/// Compute the in-flight-spark cap from the three inputs, kept pure and
/// side-effect-free so the policy is unit-testable without touching the
/// process-global `LazyLock`/env (Principle 5 — testability is structural).
///
/// Precedence:
/// 1. an explicit `CRANELISP_SPARK_BUDGET=N` override always wins (a manual cap);
/// 2. else the **saturation gate** caps at exactly `num_threads` — spark iff a
///    worker is free right now, else inline the overflow (Wave 1c);
/// 3. else the default `4 × num_threads` static budget (pre-S99 behaviour).
fn effective_spark_cap(explicit: Option<usize>, saturation_gate: bool, num_threads: usize) -> usize {
    if let Some(n) = explicit {
        return n;
    }
    if saturation_gate {
        return num_threads;
    }
    4 * num_threads
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
    // Fast reject (the common case under explosion): a single load, no RMW.
    if !budget_grants(IN_FLIGHT_SPARKS.load(Ordering::SeqCst), n, cap) {
        return 0;
    }
    // Commit the whole batch atomically (CAS loop) — all-or-nothing.
    loop {
        let cur = IN_FLIGHT_SPARKS.load(Ordering::SeqCst);
        if !budget_grants(cur, n, cap) {
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

    rayon::spawn(move || {
        // Release the in-flight-spark reservation on normal completion OR on a
        // Rust unwind (§3.6). Placed FIRST so its `drop` runs last, after the
        // RC dec below — and runs even if anything in this closure unwinds.
        let _in_flight_guard = InFlightGuard;

        // Force the IVar (evaluate thunk if still PENDING).
        ivar_force(ivar);

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

    // Fast path: already resolved.
    let state = state_ptr.load(Ordering::SeqCst);
    if state == RESOLVED {
        reraise_ferried_error(ivar);
        return unsafe { *((ivar as isize + VALUE_OFFSET) as *const i64) };
    }

    // Try to claim the thunk.
    match state_ptr.compare_exchange(PENDING, EVALUATING, Ordering::SeqCst, Ordering::SeqCst) {
        Ok(_) => {
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
            let result = call(thunk);

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
            // Another thread claimed it — spin-wait until RESOLVED.
            loop {
                let s = state_ptr.load(Ordering::SeqCst);
                if s == RESOLVED {
                    // Join-side re-raise: a panic captured by the claimant is
                    // published in the error field under the RESOLVED store
                    // (test-discovery.md §6).
                    reraise_ferried_error(ivar);
                    return unsafe { *((ivar as isize + VALUE_OFFSET) as *const i64) };
                }
                std::hint::spin_loop();
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
