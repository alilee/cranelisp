use super::*;
use crate::alloc::alloc_with_rc;
use std::sync::atomic::AtomicBool;
use std::time::{Duration, Instant};

/// Build a minimal closure that returns a constant value.
/// Layout: [header(16) | code_ptr(8) | drop_glue_ptr(8) | capture(8)]
fn make_const_thunk(value: i64) -> i64 {
    extern "C" fn const_fn(env_ptr: i64) -> i64 {
        // Load captured value from offset 32 (CAPTURES_START)
        unsafe { *((env_ptr as isize + 32) as *const i64) }
    }

    let base = alloc_with_rc(24); // code_ptr + drop_glue + 1 capture = 24
    unsafe {
        // code_ptr at offset 16
        *((base as isize + 16) as *mut i64) = const_fn as *const () as i64;
        // drop_glue_ptr at offset 24 (0 = no heap captures)
        *((base as isize + 24) as *mut i64) = 0;
        // capture: the constant value at offset 32
        *((base as isize + 32) as *mut i64) = value;
    }
    base as i64
}

// spec: 12-runtime §12.4.3 — IVar create sets initial state to PENDING
#[test]
fn test_ivar_create() {
    let thunk = make_const_thunk(42);
    let ivar = ivar_create(thunk);

    unsafe {
        let state = *((ivar as isize + STATE_OFFSET) as *const i64);
        assert_eq!(state, PENDING);
        let stored_thunk = *((ivar as isize + THUNK_OFFSET) as *const i64);
        assert_eq!(stored_thunk, thunk);

        // Alloc size should be 48 (16 header + 32 payload).
        let alloc_size = *(ivar as *const i64);
        assert_eq!(alloc_size, 48);
        // RC should be 1
        let rc = *((ivar as isize + RC_OFFSET) as *const i64);
        assert_eq!(rc, 1);
    }

    // Clean up
    unsafe { dealloc(ivar as *mut u8) };
    unsafe { dealloc(thunk as *mut u8) };
}

// spec: 12-runtime §12.4.3 — IVar force evaluates thunk and returns result
#[test]
fn test_ivar_force_evaluates_thunk() {
    let thunk = make_const_thunk(99);
    let ivar = ivar_create(thunk);

    let result = ivar_force(ivar);
    assert_eq!(result, 99);

    // State should be RESOLVED
    unsafe {
        let state = *((ivar as isize + STATE_OFFSET) as *const i64);
        assert_eq!(state, RESOLVED);
    }

    // Force again — should return cached value
    let result2 = ivar_force(ivar);
    assert_eq!(result2, 99);

    // Clean up — thunk was already freed by ivar_force (B2 fix).
    unsafe { dealloc(ivar as *mut u8) };
}

// spec: 12-runtime §12.4.3 — IVar spark submits to thread pool and force works
#[test]
fn test_ivar_spark_and_force() {
    let thunk = make_const_thunk(77);
    let ivar = ivar_create(thunk);

    ivar_spark(ivar);

    // Force from main thread — either evaluates or waits for spark task
    let result = ivar_force(ivar);
    assert_eq!(result, 77);

    // Dec our reference (spark task also decs)
    let old_rc = unsafe {
        let rc_ptr = (ivar as isize + RC_OFFSET) as *const AtomicI64;
        (*rc_ptr).fetch_sub(1, Ordering::SeqCst)
    };
    if old_rc == 1 {
        std::sync::atomic::fence(Ordering::Acquire);
        unsafe { dealloc(ivar as *mut u8) };
    }
    // Note: if old_rc > 1, the spark task will free it
    // Thunk was already freed by ivar_force (B2 fix).
}

// spec: 12-runtime §12.4.3 — Multiple IVars can be sparked and forced concurrently
#[test]
fn test_multiple_ivars() {
    let values = vec![10, 20, 30, 40, 50];
    let mut ivars = Vec::new();
    let mut thunks = Vec::new();

    for &v in &values {
        let thunk = make_const_thunk(v);
        let ivar = ivar_create(thunk);
        ivar_spark(ivar);
        ivars.push(ivar);
        thunks.push(thunk);
    }

    // Force all — results should match
    for (i, &ivar) in ivars.iter().enumerate() {
        let result = ivar_force(ivar);
        assert_eq!(result, values[i]);
    }

    // Cleanup
    for &ivar in &ivars {
        let old_rc = unsafe {
            let rc_ptr = (ivar as isize + RC_OFFSET) as *const AtomicI64;
            (*rc_ptr).fetch_sub(1, Ordering::SeqCst)
        };
        if old_rc == 1 {
            std::sync::atomic::fence(Ordering::Acquire);
            unsafe { dealloc(ivar as *mut u8) };
        }
    }
    // Thunks were already freed by ivar_force (B2 fix).
}

/// Build a zero-arg thunk that raises a runtime panic and returns 0.
fn make_panicking_thunk() -> i64 {
    extern "C" fn boom_fn(_env_ptr: i64) -> i64 {
        let msg = "ivar boom";
        crate::panic::runtime_panic(msg.as_ptr(), msg.len());
        0
    }
    let base = alloc_with_rc(16); // code_ptr + drop_glue, no captures
    unsafe {
        *((base as isize + 16) as *mut i64) = boom_fn as *const () as i64;
        *((base as isize + 24) as *mut i64) = 0; // no drop glue
    }
    base as i64
}

// spec: 12-runtime §12.4.3 — a thunk panic is ferried through the IVar so the
// forcing (joining) thread re-raises it, instead of silently swallowing it.
#[test]
fn test_ivar_force_ferries_panic_to_joiner() {
    let _ = crate::panic::take_runtime_error(); // clear
    let thunk = make_panicking_thunk();
    let ivar = ivar_create(thunk);

    // Force on this (the joining) thread — the thunk panics; the ferry
    // stashes the message in the IVar's error field and re-raises it here.
    let result = ivar_force(ivar);
    assert_eq!(result, 0, "panicked thunk yields the sentinel 0");

    let err = crate::panic::take_runtime_error();
    assert!(
        err.is_some(),
        "panic must be re-raised on the joining thread"
    );
    assert!(
        err.unwrap().contains("ivar boom"),
        "the ferried message must be the thunk's panic"
    );

    // The error field holds the heap String; `ivar_dealloc` frees both it
    // and the cell (the production drop path).
    unsafe {
        let err_str = *((ivar as isize + ERROR_OFFSET) as *const i64);
        assert!(err_str != 0, "error field must hold the ferried String");
        ivar_dealloc(ivar);
    }
}

// spec: 12-runtime §12.4.3 — deallocating a panicked IVar must free the
// ferried error String, not just the cell (production drop path; without
// this the heap String leaks on every fork-join panic).
#[test]
#[cfg(debug_assertions)]
fn test_ivar_dealloc_frees_ferried_error_string() {
    let _ = crate::panic::take_runtime_error(); // clear
    let thunk = make_panicking_thunk();
    let ivar = ivar_create(thunk);

    // Force so the ferry stashes the error String in the cell.
    let _ = ivar_force(ivar);
    let _ = crate::panic::take_runtime_error(); // drain re-raised slot

    let err_str = unsafe { *((ivar as isize + ERROR_OFFSET) as *const i64) };
    assert!(err_str != 0, "error field must hold the ferried String");
    assert!(
        crate::alloc::is_live(err_str as usize),
        "error String must be live before dealloc"
    );

    // Production drop path: dealloc the cell.
    ivar_dealloc(ivar);

    assert!(
        !crate::alloc::is_live(err_str as usize),
        "ivar_dealloc must free the ferried error String (no leak)"
    );
    assert!(
        !crate::alloc::is_live(ivar as usize),
        "ivar_dealloc must free the cell itself"
    );
}

// spec: 12-runtime §12.4.3 — ivar_dealloc on a clean (non-panicked) IVar
// frees the cell and does not touch the (null) error field.
#[test]
#[cfg(debug_assertions)]
fn test_ivar_dealloc_clean_frees_cell() {
    let thunk = make_const_thunk(7);
    let ivar = ivar_create(thunk);
    let _ = ivar_force(ivar); // thunk freed here

    ivar_dealloc(ivar);
    assert!(
        !crate::alloc::is_live(ivar as usize),
        "ivar_dealloc must free the cell"
    );
}

// spec: 12-runtime §12.4.3 — a passing thunk leaves the slot clean (no
// spurious error, the ferry only fires on a real panic).
#[test]
fn test_ivar_force_clean_thunk_leaves_slot_clean() {
    let _ = crate::panic::take_runtime_error(); // clear
    let thunk = make_const_thunk(123);
    let ivar = ivar_create(thunk);

    let result = ivar_force(ivar);
    assert_eq!(result, 123);
    assert!(
        crate::panic::take_runtime_error().is_none(),
        "a clean thunk must not set the error slot"
    );
    unsafe {
        let err_str = *((ivar as isize + ERROR_OFFSET) as *const i64);
        assert_eq!(err_str, 0, "error field must be 0 for a clean thunk");
        dealloc(ivar as *mut u8);
    }
}

// ---------------------------------------------------------------------------
// Spark budget — the create-gate reservation primitive (lenient-eval.md §3.6,
// S92). The budget is a `cranelisp-intrinsics`-internal mechanism: a
// module-static `IN_FLIGHT_SPARKS` (AtomicIsize), a `SPARK_BUDGET` cap, the
// `spark_budget_try_reserve` reservation primitive (called by the backend
// create-gate BEFORE any IVar allocation), and the `InFlightGuard` RAII release
// (one permit per completing spark) — all reachable here via `use super::*`.
//
// As of S92 the spawn-vs-direct decision is taken by the backend gate, NOT in
// `ivar_spark` (which always spawns). The gate reserves `n` permits up front;
// each of the `n` spawned sparks releases one on completion. These tests exercise
// the primitive + release accounting directly (no session, no codegen). They
// mutate a process global, so they rely on nextest's process-per-test isolation
// (the project's mandated runner); each restores the counter to its observed
// baseline as cargo-test-fallback hygiene.
// ---------------------------------------------------------------------------

/// Spin until `pred()` holds or `timeout` elapses; returns whether it held.
fn spin_until(mut pred: impl FnMut() -> bool, timeout: Duration) -> bool {
    let start = Instant::now();
    while start.elapsed() < timeout {
        if pred() {
            return true;
        }
        std::hint::spin_loop();
    }
    pred()
}

// spec: 12-runtime §12.4.3 — `try_reserve` grants a batch that fits under the
// cap, denies one that does not, and is atomic (all-or-nothing) for n>1: a batch
// that overflows the cap by even 1 commits NOTHING (no partial reservation). The
// arithmetic is driven off the live `SPARK_BUDGET` cap so it is independent of
// the LazyLock's actual value (default 4×threads ≥ 4 in a fresh process).
#[test]
fn spark_budget_try_reserve_grants_denies_and_is_atomic() {
    let cap = *SPARK_BUDGET as isize;
    assert!(
        cap >= 2,
        "test precondition: default cap (4×threads) is ≥ 2 in a fresh process"
    );
    let base = IN_FLIGHT_SPARKS.load(Ordering::SeqCst);

    // Grant under cap: reserve(1) commits exactly 1 permit.
    IN_FLIGHT_SPARKS.store(0, Ordering::SeqCst);
    assert_eq!(spark_budget_try_reserve(1), 1, "1 permit fits under cap");
    assert_eq!(
        IN_FLIGHT_SPARKS.load(Ordering::SeqCst),
        1,
        "a grant commits exactly n permits"
    );

    // Deny at cap: a full counter rejects reserve(1) and leaves it unchanged.
    IN_FLIGHT_SPARKS.store(cap, Ordering::SeqCst);
    assert_eq!(spark_budget_try_reserve(1), 0, "no room at the cap");
    assert_eq!(
        IN_FLIGHT_SPARKS.load(Ordering::SeqCst),
        cap,
        "a rejected reservation must not mutate the counter"
    );

    // Atomic batch (n>1): leave exactly 1 slot, request 2 ⇒ reject wholesale,
    // counter unchanged (no partial commit of the 1 that would have fit).
    IN_FLIGHT_SPARKS.store(cap - 1, Ordering::SeqCst);
    assert_eq!(
        spark_budget_try_reserve(2),
        0,
        "a batch overflowing the cap by 1 is rejected all-or-nothing"
    );
    assert_eq!(
        IN_FLIGHT_SPARKS.load(Ordering::SeqCst),
        cap - 1,
        "a rejected n>1 batch commits nothing (no partial reservation)"
    );

    // Exact fit: request exactly the remaining 1 ⇒ grant, counter reaches cap.
    assert_eq!(spark_budget_try_reserve(1), 1, "an exact-fit batch grants");
    assert_eq!(
        IN_FLIGHT_SPARKS.load(Ordering::SeqCst),
        cap,
        "an exact-fit grant commits the whole batch"
    );

    IN_FLIGHT_SPARKS.store(base, Ordering::SeqCst);
}

// spec: 12-runtime §12.4.3 — MANDATORY: the `InFlightGuard` release runs on a
// Rust unwind, so a spawned closure that panics releases its permit and leaves
// `IN_FLIGHT_SPARKS` back at its baseline. A leaked permit would drift the cap
// toward permanent-direct (silent serial degradation no other test catches). A
// real sparked thunk cannot be made to Rust-unwind safely (the thunk is
// `extern "C"` — unwinding out of it aborts the process), so this pins the actual
// mechanism — the guard + counter — under a simulated closure unwind via
// `catch_unwind`, which is exactly the path the spawn closure takes on an
// internal panic.
#[test]
fn spark_budget_panicking_spawned_thunk_counter_returns_to_baseline() {
    let base = IN_FLIGHT_SPARKS.load(Ordering::SeqCst);
    // Simulate the gate reservation (+1) the spawned task holds via its guard.
    IN_FLIGHT_SPARKS.fetch_add(1, Ordering::SeqCst);
    let outcome = std::panic::catch_unwind(|| {
        let _in_flight_guard = InFlightGuard;
        panic!("simulated unwind inside the spawned rayon closure");
    });
    assert!(outcome.is_err(), "the simulated closure must have unwound");
    assert_eq!(
        IN_FLIGHT_SPARKS.load(Ordering::SeqCst),
        base,
        "InFlightGuard::drop must release the permit on the unwind path"
    );
}

// spec: 12-runtime §12.4.3 — release-on-completion: the gate reserves a permit;
// `ivar_spark` (always-spawn) holds it while the task is in flight and does NOT
// itself touch the counter; the spawned worker's `InFlightGuard` drop releases
// exactly that permit on completion ⇒ reserve(1) + 1 spawn + 1 completion nets
// zero against the counter.
#[test]
fn spark_budget_reserve_then_spawn_releases_net_zero() {
    // A gated thunk: the rayon worker spins inside the thunk until we release it,
    // so we can observe the counter while the task is genuinely in flight.
    static GATE: AtomicBool = AtomicBool::new(false);
    GATE.store(false, Ordering::SeqCst);
    extern "C" fn gated_fn(_env_ptr: i64) -> i64 {
        while !GATE.load(Ordering::SeqCst) {
            std::hint::spin_loop();
        }
        55
    }
    let base = IN_FLIGHT_SPARKS.load(Ordering::SeqCst);

    // The create-gate's reservation (what the backend emits before allocating).
    assert_eq!(spark_budget_try_reserve(1), 1, "1 permit fits under cap");
    assert_eq!(
        IN_FLIGHT_SPARKS.load(Ordering::SeqCst),
        base + 1,
        "the gate reservation raises the counter by 1"
    );

    let thunk = {
        let b = alloc_with_rc(16); // code_ptr + drop_glue, no captures
        unsafe {
            *((b as isize + 16) as *mut i64) = gated_fn as *const () as i64;
            *((b as isize + 24) as *mut i64) = 0;
        }
        b as i64
    };
    let ivar = ivar_create(thunk);

    ivar_spark(ivar);
    // `ivar_spark` always spawns and does NOT reserve (the gate already did), so
    // the counter is still the gate's base+1 while the worker is in flight.
    assert_eq!(
        IN_FLIGHT_SPARKS.load(Ordering::SeqCst),
        base + 1,
        "ivar_spark must not reserve (the create-gate owns reservation)"
    );

    // Release the gate; the worker finishes, RC-decs, and the guard releases.
    GATE.store(true, Ordering::SeqCst);
    assert!(
        spin_until(
            || IN_FLIGHT_SPARKS.load(Ordering::SeqCst) == base,
            Duration::from_secs(5),
        ),
        "InFlightGuard::drop must release the permit on completion (net zero)"
    );

    // Cleanup: the worker already dec'd its reference; force + dec ours.
    let result = ivar_force(ivar);
    assert_eq!(result, 55);
    let old_rc = unsafe {
        let rc_ptr = (ivar as isize + RC_OFFSET) as *const AtomicI64;
        (*rc_ptr).fetch_sub(1, Ordering::SeqCst)
    };
    if old_rc == 1 {
        std::sync::atomic::fence(Ordering::Acquire);
        unsafe { dealloc(ivar as *mut u8) };
    }
}

// spec: 12-runtime §12.4.3 — CRANELISP_SPARK_BUDGET=0 ⇒ cap 0 ⇒ `cur + n > 0`
// for all n ≥ 1 ⇒ `try_reserve` rejects every batch (every gate site takes the
// direct arm, no allocation). Relies on nextest process-per-test isolation: the
// env var is set before `SPARK_BUDGET` is first read in THIS fresh process.
#[test]
fn spark_budget_zero_try_reserve_always_rejects() {
    // SAFETY: single-threaded at this point in the test, before any reserve reads
    // the LazyLock; nextest isolates each test in its own process.
    unsafe { std::env::set_var("CRANELISP_SPARK_BUDGET", "0") };
    assert_eq!(
        *SPARK_BUDGET, 0,
        "CRANELISP_SPARK_BUDGET=0 must parse to cap 0 (fresh process precondition)"
    );

    let base = IN_FLIGHT_SPARKS.load(Ordering::SeqCst);
    for n in [1, 2, 5, 100] {
        assert_eq!(
            spark_budget_try_reserve(n),
            0,
            "budget=0 must reject reserve({n})"
        );
    }
    assert_eq!(
        IN_FLIGHT_SPARKS.load(Ordering::SeqCst),
        base,
        "rejected reservations commit nothing"
    );
}

// ---------------------------------------------------------------------------
// Saturation-shaped spark gate (Sprint 99 Wave 1c, FIXME 0459). The gate reuses
// the create-gate reservation machinery verbatim — the only change is the CAP
// policy: `CRANELISP_SATURATION_GATE=1` (with no explicit budget) tightens the
// cap from the default 4×threads static budget to exactly the worker count, so a
// batch is granted (⇒ sparked) only while a worker is free right now and the
// overflow runs INLINE via the create-gate's direct arm. Both the cap policy
// (`effective_spark_cap`) and the grant decision (`budget_grants`) are pure and
// exercised directly here, independent of env/LazyLock (Principle 5).
// ---------------------------------------------------------------------------

// spec: design/backend/lenient-eval.md §3.6 — the saturation gate caps concurrent
// sparks at the worker count (spark iff spare capacity), while an explicit budget
// override still wins and the default stays the 4× static budget (byte-identical
// off).
#[test]
fn saturation_gate_effective_cap_policy() {
    // Gate OFF, M-dynamic default (core_mult = 2): the S104 Wave-2 default is
    // 2× the worker count (~2/core utilization cap, §2.8.3).
    assert_eq!(
        effective_spark_cap(None, false, 2, 1),
        2,
        "off ⇒ 2×threads (k=2)"
    );
    assert_eq!(
        effective_spark_cap(None, false, 2, 8),
        16,
        "off ⇒ 2×threads (k=2)"
    );

    // Gate ON (no explicit budget): cap at exactly the worker count — the
    // saturation policy (spark iff a worker is free; inline the overflow).
    // The saturation gate takes precedence over the M-dynamic multiplier.
    assert_eq!(
        effective_spark_cap(None, true, 2, 1),
        1,
        "saturation ⇒ 1×threads"
    );
    assert_eq!(
        effective_spark_cap(None, true, 2, 8),
        8,
        "saturation ⇒ 1×threads"
    );

    // An explicit `CRANELISP_SPARK_BUDGET` override always wins, gate or not —
    // including the `=0` always-reject cap.
    assert_eq!(
        effective_spark_cap(Some(3), true, 2, 8),
        3,
        "explicit override wins over gate"
    );
    assert_eq!(
        effective_spark_cap(Some(3), false, 2, 8),
        3,
        "explicit override wins by default"
    );
    assert_eq!(
        effective_spark_cap(Some(0), true, 2, 8),
        0,
        "explicit 0 wins (always-reject)"
    );
}

// spec: design/backend/lenient-eval.md §3.6 — the grant decision is the
// saturation test: grant (spark) iff the batch fits under the cap; else reject so
// the caller inlines the overflow on the current thread. All-or-nothing for n>1.
#[test]
fn saturation_gate_budget_grants_iff_spare_capacity() {
    // With the saturation cap == worker-count, model a 4-worker pool (cap=4).
    let cap = 4;
    // Spare capacity: fewer sparks in flight than workers ⇒ grant (spark).
    assert!(budget_grants(0, 1, cap), "empty pool ⇒ spark");
    assert!(
        budget_grants(3, 1, cap),
        "1 free worker ⇒ spark the last slot"
    );
    // Saturated: a full pool rejects ⇒ the caller inlines the branch.
    assert!(
        !budget_grants(4, 1, cap),
        "saturated pool ⇒ inline (no spark)"
    );
    assert!(!budget_grants(5, 1, cap), "over-saturated ⇒ inline");
    // All-or-nothing for a batch: 1 free slot cannot admit a 2-spark batch.
    assert!(
        !budget_grants(3, 2, cap),
        "batch overflowing by 1 ⇒ inline wholesale"
    );
    assert!(budget_grants(2, 2, cap), "an exact-fit batch ⇒ spark");
}

// spec: design/backend/lenient-eval.md §3.6 — end-to-end env wiring:
// `CRANELISP_SATURATION_GATE=1` (with no explicit budget) makes the process-global
// `SPARK_BUDGET` cap resolve to exactly `rayon::current_num_threads()`. Relies on
// nextest process-per-test isolation: the env var is set before `SPARK_BUDGET` is
// first read in THIS fresh process.
#[test]
fn saturation_gate_env_caps_spark_budget_at_worker_count() {
    // SAFETY: single-threaded at this point in the test, before any reserve reads
    // the LazyLock; nextest isolates each test in its own process.
    unsafe { std::env::set_var("CRANELISP_SATURATION_GATE", "1") };
    assert_eq!(
        *SPARK_BUDGET,
        rayon::current_num_threads(),
        "CRANELISP_SATURATION_GATE=1 must cap the spark budget at the worker count \
         (fresh process precondition; no explicit CRANELISP_SPARK_BUDGET)"
    );
    // Sanity: with the cap == worker count, a full pool rejects (inline overflow).
    let cap = *SPARK_BUDGET as isize;
    IN_FLIGHT_SPARKS.store(cap, Ordering::SeqCst);
    assert_eq!(
        spark_budget_try_reserve(1),
        0,
        "at saturation (in_flight == workers) the gate rejects ⇒ inline"
    );
    IN_FLIGHT_SPARKS.store(0, Ordering::SeqCst);
}

// ---------------------------------------------------------------------------
// M-dynamic — the utilization axis (S104 Wave 2, Stage 3; lenient-eval.md
// §2.8.3/§2.8.4, gate G1). M-dynamic is a *re-parameterization* of the existing
// create-gate cap toward `~2 × ncores`, default-on — NOT a new counter. The cap
// default multiplier becomes `SPARK_CORE_MULT` (default `k = 2`), env-overridable
// via `CRANELISP_SPARK_CORE_MULT=k` (the ~2/core tunable knob AND the M-dynamic
// on/off selector: k=4 recovers the pre-Wave-2 `4×` default ⇒ M-dynamic off;
// k=0 ⇒ fully serial). These tests exercise the re-parameterized cap policy
// (`effective_spark_cap`), the cap-boundary spark/inline decision, and the
// hierarchical-decline property (a spark dispatched into a busy pool inlines its
// nested candidates) directly on the pure policy + the live counter, independent
// of codegen. Both `effective_spark_cap` and `budget_grants` are pure (Principle
// 5). The env-wiring tests rely on nextest's process-per-test isolation.
// ---------------------------------------------------------------------------

// spec: design/backend/lenient-eval.md §2.8.3 — M-dynamic re-parameterizes the
// cap to `k × threads`, default `k = 2` (~2/core). The knob sweeps k∈{0,1,2,4}:
// k=2 is the shipped default, k=1 == the saturation cap, k=4 recovers the
// pre-Wave-2 `4×` budget (M-dynamic off), k=0 yields cap 0 (always-reject).
#[test]
fn mdynamic_effective_cap_core_mult_sweep() {
    // Default k=2 across pool widths (~2/core).
    assert_eq!(effective_spark_cap(None, false, 2, 1), 2, "k=2 ⇒ 2×threads");
    assert_eq!(effective_spark_cap(None, false, 2, 4), 8, "k=2 ⇒ 2×threads");
    assert_eq!(
        effective_spark_cap(None, false, 2, 8),
        16,
        "k=2 ⇒ 2×threads"
    );

    // k=1 == the saturation cap (tightest collapse).
    assert_eq!(effective_spark_cap(None, false, 1, 8), 8, "k=1 ⇒ 1×threads");
    // k=4 recovers the pre-Wave-2 static budget (M-dynamic effectively OFF).
    assert_eq!(
        effective_spark_cap(None, false, 4, 8),
        32,
        "k=4 ⇒ pre-Wave-2 4×threads"
    );
    // k=0 ⇒ cap 0 ⇒ always-reject ⇒ fully serial (== CRANELISP_SPARK_BUDGET=0).
    assert_eq!(
        effective_spark_cap(None, false, 0, 8),
        0,
        "k=0 ⇒ cap 0 (fully serial)"
    );

    // Precedence is unchanged: an explicit budget still wins over the multiplier,
    // and the saturation gate still wins over the multiplier default.
    assert_eq!(
        effective_spark_cap(Some(5), false, 2, 8),
        5,
        "explicit budget wins over k"
    );
    assert_eq!(
        effective_spark_cap(None, true, 2, 8),
        8,
        "saturation gate wins over k"
    );
}

// spec: design/backend/lenient-eval.md §2.8.3/§2.8.6 — the M-dynamic cap-boundary:
// a candidate site SPARKS while in-flight sparks are under the ~2/core cap and
// INLINES (direct arm, no IVar emission) once the pool is saturated at the cap.
// Modeled at a 4-core pool with the default k=2 ⇒ cap = 8 (~2/core), driven off
// the pure grant decision so it is independent of the host thread count.
#[test]
fn mdynamic_cap_boundary_sparks_under_inlines_at_cap() {
    let ncores = 4;
    let cap = effective_spark_cap(None, false, 2, ncores) as isize; // 2×4 = 8
    assert_eq!(cap, 8, "k=2 on a 4-core pool ⇒ ~2/core cap of 8");

    // Under the cap ⇒ spark.
    assert!(budget_grants(0, 1, cap), "empty pool ⇒ spark");
    assert!(
        budget_grants(cap - 1, 1, cap),
        "one slot free ⇒ spark the last strand"
    );
    // At / over the cap ⇒ inline (the ~2/core collapse: deeper sites take the
    // direct arm and run their subtree serially, allocation-free).
    assert!(!budget_grants(cap, 1, cap), "saturated at ~2/core ⇒ inline");
    assert!(!budget_grants(cap + 3, 1, cap), "over-saturated ⇒ inline");
    // All-or-nothing for a batch of nested candidates.
    assert!(
        !budget_grants(cap - 1, 2, cap),
        "a 2-batch overflowing by 1 ⇒ inline wholesale"
    );
    assert!(budget_grants(cap - 2, 2, cap), "an exact-fit batch ⇒ spark");
}

// spec: design/backend/lenient-eval.md §2.8.4 — hierarchical decline (the
// connective invariant): a spark dispatched into a BUSY pool inlines its nested
// candidates. Once ~cap strands are in flight (`IN_FLIGHT_SPARKS ≥ cap`), a
// strand's nested spark site's `try_reserve` returns 0 on a single load ⇒ it
// takes the direct arm and runs its subtree serially — no further sparking
// inside the serialized subtree. As a permit frees, a bounded frontier is
// re-admitted. Driven off the live `SPARK_BUDGET` cap so it holds at any host
// thread count.
#[test]
fn mdynamic_hierarchical_decline_busy_pool_inlines_nested() {
    let cap = *SPARK_BUDGET as isize;
    assert!(
        cap >= 2,
        "default cap (k=2 × threads) is ≥ 2 in a fresh process"
    );
    let base = IN_FLIGHT_SPARKS.load(Ordering::SeqCst);

    // Pool saturated at the ~2/core cap: a strand's nested candidate INLINES.
    IN_FLIGHT_SPARKS.store(cap, Ordering::SeqCst);
    assert_eq!(
        spark_budget_try_reserve(1),
        0,
        "busy pool (in_flight == cap) ⇒ nested candidate inlines (hierarchical decline)"
    );
    // A wider nested batch also inlines wholesale.
    assert_eq!(
        spark_budget_try_reserve(2),
        0,
        "busy pool ⇒ nested 2-batch inlines wholesale"
    );
    assert_eq!(
        IN_FLIGHT_SPARKS.load(Ordering::SeqCst),
        cap,
        "declined nested reservations commit nothing (allocation-free direct arm)"
    );

    // A completing strand releases one permit (InFlightGuard drop): a bounded
    // frontier is re-admitted — the next nested candidate sparks again.
    IN_FLIGHT_SPARKS.store(cap - 1, Ordering::SeqCst);
    assert_eq!(
        spark_budget_try_reserve(1),
        1,
        "one permit freed ⇒ re-admit a bounded frontier (nested candidate sparks)"
    );
    assert_eq!(
        IN_FLIGHT_SPARKS.load(Ordering::SeqCst),
        cap,
        "the re-admitted spark commits exactly one permit back to the cap"
    );

    IN_FLIGHT_SPARKS.store(base, Ordering::SeqCst);
}

// spec: design/backend/lenient-eval.md §2.8.3 — end-to-end env wiring:
// `CRANELISP_SPARK_CORE_MULT=1` re-parameterizes the process-global `SPARK_BUDGET`
// cap to `1 × rayon::current_num_threads()` (the tightest ~1/core collapse).
// Relies on nextest process-per-test isolation: the env var is set before
// `SPARK_BUDGET` is first read in THIS fresh process.
#[test]
fn mdynamic_core_mult_1_caps_spark_budget_at_one_per_core() {
    // SAFETY: single-threaded at this point, before any reserve reads the
    // LazyLock; nextest isolates each test in its own process.
    unsafe { std::env::set_var("CRANELISP_SPARK_CORE_MULT", "1") };
    assert_eq!(
        *SPARK_BUDGET,
        rayon::current_num_threads(),
        "CRANELISP_SPARK_CORE_MULT=1 must cap the budget at 1×threads (fresh process)"
    );
}

// spec: design/backend/lenient-eval.md §2.8.3 — the M-dynamic on/off selector:
// `CRANELISP_SPARK_CORE_MULT=4` recovers the pre-Wave-2 `4×threads` default (i.e.
// M-dynamic effectively OFF — the `mstatic-only` measurement config). Relies on
// nextest process-per-test isolation.
#[test]
fn mdynamic_core_mult_4_recovers_prewave2_budget() {
    // SAFETY: single-threaded at this point, before any reserve reads the
    // LazyLock; nextest isolates each test in its own process.
    unsafe { std::env::set_var("CRANELISP_SPARK_CORE_MULT", "4") };
    assert_eq!(
        *SPARK_BUDGET,
        4 * rayon::current_num_threads(),
        "CRANELISP_SPARK_CORE_MULT=4 recovers the pre-Wave-2 4×threads budget \
         (M-dynamic off; fresh process)"
    );
}

// ---------------------------------------------------------------------------
// Structural hierarchical decline — depth-allowance form (S104 Wave 2b→2e, gate
// G3; lenient-eval.md §2.8.4). A thread-local spark-nesting DEPTH counter
// (`SPARK_DEPTH`) tracks the logical nesting depth of the spark body the current
// thread is executing (top call = 0; `+1` per level, incremented around the thunk
// call in `ivar_force`'s claim arm and propagated across the spawn boundary by
// `ivar_spark`'s base-restore). A nested create-gate site inlines
// (`spark_budget_try_reserve` returns 0) only when `SPARK_DEPTH >= SPARK_MAX_DEPTH`;
// below the threshold it MAY spark (subject to the concurrent cap). So the top
// `MAX_DEPTH` levels of the spark tree fan out (up to `2^MAX_DEPTH` strands — a
// balanced coarse tree fills the cores) and everything below inlines (a deep
// recursion collapses to `O(2^MAX_DEPTH)` spawns). `MAX_DEPTH = 1` reproduces the
// Wave-2c boolean collapse; `MAX_DEPTH = 0` inlines everything.
// `CRANELISP_HIER_DECLINE=0` disables the depth check entirely (emergent-cap
// fallback). The counter is a per-thread `Cell`, so each test thread sees its own
// — clean isolation under nextest AND cargo test.
// ---------------------------------------------------------------------------

// spec: design/backend/lenient-eval.md §2.8.4 — the depth cutoff forces the inline
// arm: with spare capacity (so ONLY the depth can decline), `try_reserve` grants
// while `SPARK_DEPTH < MAX_DEPTH` and returns 0 (commits nothing) once
// `SPARK_DEPTH >= MAX_DEPTH`. Driven relative to the process-default MAX_DEPTH
// (machine-dependent) via the depth guard so the test is core-count-agnostic.
#[test]
fn hier_decline_depth_cutoff_forces_inline_at_or_above_max_depth() {
    assert!(
        *HIER_DECLINE_ON,
        "hierarchical decline defaults to on in a fresh process"
    );
    let max = *SPARK_MAX_DEPTH;
    assert!(max >= 1, "the default allowance is clamped to >= 1");

    let base = IN_FLIGHT_SPARKS.load(Ordering::SeqCst);
    // Spare capacity, so the DEPTH is the only thing that can force inline.
    IN_FLIGHT_SPARKS.store(0, Ordering::SeqCst);
    assert_eq!(
        SPARK_DEPTH.with(|c| c.get()),
        0,
        "depth starts at 0 on this thread"
    );

    // Depth 0 < MAX (>= 1) + spare capacity ⇒ grant (a top-level site sparks).
    assert_eq!(
        spark_budget_try_reserve(1),
        1,
        "depth 0 < MAX ⇒ spark under cap"
    );
    IN_FLIGHT_SPARKS.store(0, Ordering::SeqCst); // undo the committed permit

    // Just below the threshold (depth == MAX - 1) still grants.
    {
        let _g = SparkDepthGuard::enter_base(max - 1);
        assert_eq!(
            spark_budget_try_reserve(1),
            1,
            "depth MAX-1 < MAX ⇒ still sparks under the cap"
        );
        IN_FLIGHT_SPARKS.store(0, Ordering::SeqCst);
    }

    // At the threshold (depth == MAX) ⇒ inline regardless of spare capacity.
    {
        let _g = SparkDepthGuard::enter_base(max);
        assert_eq!(
            SPARK_DEPTH.with(|c| c.get()),
            max,
            "guard set the depth to MAX"
        );
        assert_eq!(
            spark_budget_try_reserve(1),
            0,
            "depth >= MAX ⇒ nested site inlines (depth allowance spent)"
        );
        assert_eq!(
            spark_budget_try_reserve(4),
            0,
            "a nested batch inlines wholesale regardless of the counter"
        );
        assert_eq!(
            IN_FLIGHT_SPARKS.load(Ordering::SeqCst),
            0,
            "declined nested reservations commit nothing (allocation-free arm)"
        );
    }
    // Above the threshold ⇒ still inline.
    {
        let _g = SparkDepthGuard::enter_base(max + 5);
        assert_eq!(spark_budget_try_reserve(1), 0, "depth > MAX ⇒ inline");
    }
    // Depth restored to 0 on guard drop ⇒ top-level sites spark again.
    assert_eq!(
        SPARK_DEPTH.with(|c| c.get()),
        0,
        "depth restored on scope exit"
    );
    assert_eq!(
        spark_budget_try_reserve(1),
        1,
        "restored depth 0 ⇒ spark again"
    );

    IN_FLIGHT_SPARKS.store(base, Ordering::SeqCst);
}

// spec: design/backend/lenient-eval.md §2.8.4 — the `SparkDepthGuard` increments
// the depth on entry (`enter` = +1; `enter_base` restores a captured base) and
// restores the previous depth on exit, INCLUDING on a Rust unwind out of the
// bracketed body (the thunk-panic path). Save/restore keeps a nested bracket from
// corrupting an outer strand's depth.
#[test]
fn spark_depth_guard_increments_and_restores_including_nesting_and_unwind() {
    assert_eq!(SPARK_DEPTH.with(|c| c.get()), 0, "depth 0 at start");

    // Normal scope: +1 inside, restored after.
    {
        let _g = SparkDepthGuard::enter();
        assert_eq!(
            SPARK_DEPTH.with(|c| c.get()),
            1,
            "enter() descends one level"
        );
    }
    assert_eq!(SPARK_DEPTH.with(|c| c.get()), 0, "restored on normal exit");

    // Nested enter()s stack: 0 → 1 → 2, and each drop restores the level below.
    {
        let _outer = SparkDepthGuard::enter();
        assert_eq!(SPARK_DEPTH.with(|c| c.get()), 1, "outer at depth 1");
        {
            let _inner = SparkDepthGuard::enter();
            assert_eq!(SPARK_DEPTH.with(|c| c.get()), 2, "inner at depth 2");
        }
        assert_eq!(
            SPARK_DEPTH.with(|c| c.get()),
            1,
            "inner drop restores the outer strand's depth, not 0"
        );
    }
    assert_eq!(SPARK_DEPTH.with(|c| c.get()), 0, "outer drop restores 0");

    // enter_base restores a captured parent depth (the stolen-child propagation
    // path), and a claim-arm +1 on top of it lands at parent + 1.
    {
        let _base = SparkDepthGuard::enter_base(5);
        assert_eq!(
            SPARK_DEPTH.with(|c| c.get()),
            5,
            "enter_base sets the captured base"
        );
        {
            let _claim = SparkDepthGuard::enter();
            assert_eq!(
                SPARK_DEPTH.with(|c| c.get()),
                6,
                "claim-arm +1 lands a stolen child at parent + 1"
            );
        }
        assert_eq!(
            SPARK_DEPTH.with(|c| c.get()),
            5,
            "claim drop restores the base"
        );
    }
    assert_eq!(SPARK_DEPTH.with(|c| c.get()), 0, "base drop restores 0");

    // Unwind: the depth must be restored even if the bracketed body panics — the
    // exact path a thunk that raises a Rust panic takes through the guard's Drop.
    let outcome = std::panic::catch_unwind(|| {
        let _g = SparkDepthGuard::enter();
        assert_eq!(
            SPARK_DEPTH.with(|c| c.get()),
            1,
            "descended before the panic"
        );
        panic!("simulated thunk unwind inside the spark body");
    });
    assert!(outcome.is_err(), "the bracketed body must have unwound");
    assert_eq!(
        SPARK_DEPTH.with(|c| c.get()),
        0,
        "SparkDepthGuard::drop must restore the depth on the unwind path"
    );
}

// spec: design/backend/lenient-eval.md §2.8.4 — the default depth allowance is
// `floor(log2(threads))` (clamped to >= 1): a conservative fan-out kept under the
// concurrent cap so a deep recursion still collapses. Pure formula test.
#[test]
fn default_spark_max_depth_is_floor_log2_clamped() {
    assert_eq!(default_spark_max_depth(0), 1, "degenerate 0 clamps to 1");
    assert_eq!(default_spark_max_depth(1), 1, "single core ⇒ 1");
    assert_eq!(default_spark_max_depth(2), 1, "floor(log2 2) = 1");
    assert_eq!(default_spark_max_depth(3), 1, "floor(log2 3) = 1");
    assert_eq!(default_spark_max_depth(4), 2, "floor(log2 4) = 2");
    assert_eq!(default_spark_max_depth(7), 2, "floor(log2 7) = 2");
    assert_eq!(default_spark_max_depth(8), 3, "floor(log2 8) = 3");
    assert_eq!(
        default_spark_max_depth(10),
        3,
        "floor(log2 10) = 3 (the 10-core host)"
    );
    assert_eq!(default_spark_max_depth(16), 4, "floor(log2 16) = 4");
    assert_eq!(default_spark_max_depth(1024), 10, "floor(log2 1024) = 10");
}

// spec: design/backend/lenient-eval.md §2.8.4 — the end-to-end depth property
// through a real spark, WORKER path (S104 Wave 2e): a granted spark dispatched
// from the main thread (depth 0) runs on a rayon worker at `SPARK_DEPTH == 1`
// (`ivar_spark`'s base-restore of the captured parent depth 0, then the claim-arm
// +1 in `ivar_force`). This is the whole propagation mechanism observed through
// the production seam (`ivar_spark` → worker → `ivar_force` claim arm).
#[test]
fn hier_decline_worker_spark_runs_at_parent_plus_one_depth() {
    static OBSERVED_DEPTH: AtomicI64 = AtomicI64::new(-1);
    extern "C" fn observe_fn(_env: i64) -> i64 {
        // Executing inside the spark body on the worker: record our depth.
        OBSERVED_DEPTH.store(SPARK_DEPTH.with(|c| c.get()) as i64, Ordering::SeqCst);
        7
    }
    let base = IN_FLIGHT_SPARKS.load(Ordering::SeqCst);
    // Model the one in-flight permit reserved for THIS spark (the worker's
    // InFlightGuard drop pairs with it).
    IN_FLIGHT_SPARKS.store(1, Ordering::SeqCst);
    // The main test thread sparks from depth 0.
    assert_eq!(
        SPARK_DEPTH.with(|c| c.get()),
        0,
        "main thread sparks from depth 0"
    );

    let thunk = {
        let b = alloc_with_rc(16); // code_ptr + drop_glue, no captures
        unsafe {
            *((b as isize + 16) as *mut i64) = observe_fn as *const () as i64;
            *((b as isize + 24) as *mut i64) = 0;
        }
        b as i64
    };
    let ivar = ivar_create(thunk);

    // Dispatch onto a rayon worker — the base-restore path. Do NOT call
    // `ivar_force` on this thread (that would race the worker for the CAS and could
    // run the thunk here at the main depth); spin-wait on the published state.
    ivar_spark(ivar);
    let state_ptr = unsafe { &*((ivar as isize + STATE_OFFSET) as *const AtomicI64) };
    let mut spins = 0u64;
    while state_ptr.load(Ordering::SeqCst) != RESOLVED {
        std::hint::spin_loop();
        spins += 1;
        assert!(spins < 5_000_000_000, "worker never resolved the spark");
    }

    assert_eq!(
        unsafe { *((ivar as isize + 24) as *const i64) },
        7,
        "worker computed the thunk result"
    );
    assert_eq!(
        OBSERVED_DEPTH.load(Ordering::SeqCst),
        1,
        "a spark dispatched from depth 0 runs on the worker at depth 1 (parent + 1)"
    );

    // ivar_spark inc'd RC to 2 and the worker dec'd it back to 1; the thunk was
    // freed inside the worker's `ivar_force`. Free the cell.
    unsafe { dealloc(ivar as *mut u8) };
    IN_FLIGHT_SPARKS.store(base, Ordering::SeqCst);
}

// spec: design/backend/lenient-eval.md §2.8.4 — the SYMMETRIC increment (S104
// Wave 2e, replacing the Wave-2c worker-only NEGATION): an inline claim-compute on
// ANY thread — including the main thread at a barrier — increments the depth
// around the thunk, so a thunk claim-computed inline at depth `d` runs at `d + 1`.
// Unlike the Wave-2c boolean (which deliberately did NOT flag the main arm), the
// depth allowance lets the main spine keep sparking for MAX_DEPTH levels before it
// inlines, so the both-paths collapse-to-2-cores hazard does not recur. Here the
// thunk observes its own depth while claim-computed on this thread.
#[test]
fn hier_decline_main_thread_claim_increments_depth() {
    static OBSERVED_DEPTH: AtomicI64 = AtomicI64::new(-1);
    extern "C" fn observe_fn(_env: i64) -> i64 {
        OBSERVED_DEPTH.store(SPARK_DEPTH.with(|c| c.get()) as i64, Ordering::SeqCst);
        7
    }
    let base = IN_FLIGHT_SPARKS.load(Ordering::SeqCst);
    IN_FLIGHT_SPARKS.store(0, Ordering::SeqCst);
    assert_eq!(
        SPARK_DEPTH.with(|c| c.get()),
        0,
        "depth starts at 0 on this thread"
    );

    let thunk = {
        let b = alloc_with_rc(16);
        unsafe {
            *((b as isize + 16) as *mut i64) = observe_fn as *const () as i64;
            *((b as isize + 24) as *mut i64) = 0;
        }
        b as i64
    };
    let ivar = ivar_create(thunk);

    // Inline claim on THIS thread from depth 0: `ivar_force` wins the CAS and runs
    // the thunk under the claim-arm depth guard, so the thunk sees depth 1.
    let result = ivar_force(ivar);
    assert_eq!(result, 7);
    assert_eq!(
        OBSERVED_DEPTH.load(Ordering::SeqCst),
        1,
        "an inline claim-compute from depth 0 runs the thunk at depth 1 (symmetric increment)"
    );
    // Depth is restored to 0 after the claim arm exits.
    assert_eq!(
        SPARK_DEPTH.with(|c| c.get()),
        0,
        "depth restored after the claim arm"
    );

    // Thunk was freed by ivar_force; free the cell.
    unsafe { dealloc(ivar as *mut u8) };
    IN_FLIGHT_SPARKS.store(base, Ordering::SeqCst);
}

// ---------------------------------------------------------------------------
// IVar-force wait backoff (S104 Wave 2d, `IVAR_SPIN`). The EVALUATING-wait arm
// of `ivar_force` (a thread that lost the claim CAS) uses a bounded
// spin→yield→sleep backoff that yields the core so N idle waiters do not starve
// the 1 running claimant. These tests pin the WAIT-side correctness: a value
// forced while another thread is mid-EVALUATING resolves to the right value (no
// deadlock, no lost wakeup), and a ferried panic re-raises correctly through the
// backoff wait (unwind-safe). The wait changes; the RESOLVED handshake + ferry
// do not — so these assert the protocol is preserved across the new wait.
// ---------------------------------------------------------------------------

/// Build a zero-arg thunk that spins on a shared gate before returning `value`,
/// so a second thread is guaranteed to enter the EVALUATING-wait arm (and thus
/// the backoff) while this claimant is still computing.
fn make_gated_const_thunk(gate: &'static AtomicBool, value: i64) -> i64 {
    // Two captures: the gate pointer and the value.
    extern "C" fn gated_fn(env_ptr: i64) -> i64 {
        let gate_ptr = unsafe { *((env_ptr as isize + 32) as *const i64) } as *const AtomicBool;
        let value = unsafe { *((env_ptr as isize + 40) as *const i64) };
        // Spin until released — keeps the IVar EVALUATING so the joiner waits.
        while !unsafe { (*gate_ptr).load(Ordering::SeqCst) } {
            std::hint::spin_loop();
        }
        value
    }
    let base = alloc_with_rc(32); // code_ptr + drop_glue + 2 captures
    unsafe {
        *((base as isize + 16) as *mut i64) = gated_fn as *const () as i64;
        *((base as isize + 24) as *mut i64) = 0; // no drop glue
        *((base as isize + 32) as *mut i64) = gate as *const AtomicBool as i64;
        *((base as isize + 40) as *mut i64) = value;
    }
    base as i64
}

// spec: 12-runtime §12.4.3 — a value forced on a second thread while the
// claimant is mid-EVALUATING resolves (through the backoff wait) to the correct
// value: no deadlock, no lost wakeup. The claimant is gated so the joiner is
// guaranteed to enter the wait arm and exercise the spin→yield→sleep backoff.
#[test]
fn ivar_force_backoff_wait_resolves_to_claimant_value() {
    static GATE: AtomicBool = AtomicBool::new(false);
    GATE.store(false, Ordering::SeqCst);

    let thunk = make_gated_const_thunk(&GATE, 4242);
    let ivar = ivar_create(thunk);

    // Claimant thread: wins the CAS, spins in the gated thunk until released.
    let claimant = std::thread::spawn(move || ivar_force(ivar));

    // Ensure the claimant has claimed (EVALUATING) before we join.
    let state_ptr = unsafe { &*((ivar as isize + STATE_OFFSET) as *const AtomicI64) };
    assert!(
        spin_until(
            || state_ptr.load(Ordering::SeqCst) == EVALUATING,
            Duration::from_secs(5),
        ),
        "claimant must reach EVALUATING"
    );

    // Joiner thread: lost the CAS, must WAIT via the backoff. Give it a real head
    // start into the wait arm (past the spin burst into yield/sleep) before we
    // release the claimant — this is exactly the F3 shape (waiter parked while
    // the straggler runs).
    let joiner = std::thread::spawn(move || ivar_force(ivar));
    std::thread::sleep(Duration::from_millis(20));

    // Release the claimant; both forces must return the claimant's value.
    GATE.store(true, Ordering::SeqCst);
    let claimant_val = claimant.join().expect("claimant thread panicked");
    let joiner_val = joiner.join().expect("joiner thread panicked");
    assert_eq!(claimant_val, 4242, "claimant computes the value");
    assert_eq!(
        joiner_val, 4242,
        "the backoff waiter must resolve to the same value (no lost wakeup)"
    );

    // Two forces each held the cell (rc=1 at create); force does not touch rc,
    // so the single create-time reference is still ours — free the cell + thunk
    // was freed by the claimant's force.
    unsafe { dealloc(ivar as *mut u8) };
}

// spec: 12-runtime §12.4.3 — first-error-wins is preserved across the backoff
// wait: a thunk panic captured by the claimant is ferried and re-raised into a
// backoff-WAITING joiner's slot (the wait path's `reraise_ferried_error` on the
// RESOLVED handshake, unchanged by the backoff).
#[test]
fn ivar_force_backoff_wait_reraises_ferried_panic() {
    static GATE: AtomicBool = AtomicBool::new(false);
    GATE.store(false, Ordering::SeqCst);

    // A gated panicking thunk: spin on the gate, then raise a runtime panic.
    extern "C" fn gated_boom_fn(env_ptr: i64) -> i64 {
        let gate_ptr = unsafe { *((env_ptr as isize + 32) as *const i64) } as *const AtomicBool;
        while !unsafe { (*gate_ptr).load(Ordering::SeqCst) } {
            std::hint::spin_loop();
        }
        let msg = "backoff boom";
        crate::panic::runtime_panic(msg.as_ptr(), msg.len());
        0
    }
    let thunk = {
        let b = alloc_with_rc(24); // code_ptr + drop_glue + 1 capture (gate)
        unsafe {
            *((b as isize + 16) as *mut i64) = gated_boom_fn as *const () as i64;
            *((b as isize + 24) as *mut i64) = 0;
            *((b as isize + 32) as *mut i64) = &GATE as *const AtomicBool as i64;
        }
        b as i64
    };
    let ivar = ivar_create(thunk);

    let claimant = std::thread::spawn(move || {
        let _ = crate::panic::take_runtime_error(); // clear this thread's slot
        let v = ivar_force(ivar);
        let e = crate::panic::take_runtime_error();
        (v, e)
    });

    let state_ptr = unsafe { &*((ivar as isize + STATE_OFFSET) as *const AtomicI64) };
    assert!(
        spin_until(
            || state_ptr.load(Ordering::SeqCst) == EVALUATING,
            Duration::from_secs(5),
        ),
        "claimant must reach EVALUATING"
    );

    let joiner = std::thread::spawn(move || {
        let _ = crate::panic::take_runtime_error(); // clear this thread's slot
        let v = ivar_force(ivar);
        let e = crate::panic::take_runtime_error();
        (v, e)
    });
    std::thread::sleep(Duration::from_millis(20)); // drive the joiner into backoff

    GATE.store(true, Ordering::SeqCst);
    let (cv, ce) = claimant.join().expect("claimant thread panicked");
    let (jv, je) = joiner.join().expect("joiner thread panicked");

    assert_eq!(cv, 0, "panicked thunk yields the sentinel on the claimant");
    assert_eq!(
        jv, 0,
        "panicked thunk yields the sentinel through the backoff wait"
    );
    assert!(
        ce.map(|m| m.contains("backoff boom")).unwrap_or(false),
        "claimant re-raises the ferried panic"
    );
    assert!(
        je.map(|m| m.contains("backoff boom")).unwrap_or(false),
        "the backoff waiter must re-raise the SAME ferried panic (join-side)"
    );

    ivar_dealloc(ivar);
}

/// Build a panicking thunk carrying a custom message (for the dual-panic test).
fn make_panicking_thunk_msg(msg: &'static str) -> i64 {
    // We bake the message pointer/len into two captures so one generic body
    // serves both distinct messages.
    extern "C" fn boom_fn(env_ptr: i64) -> i64 {
        let ptr = unsafe { *((env_ptr as isize + 32) as *const i64) } as *const u8;
        let len = unsafe { *((env_ptr as isize + 40) as *const i64) } as usize;
        crate::panic::runtime_panic(ptr, len);
        0
    }
    let base = alloc_with_rc(32); // code_ptr + drop_glue + 2 captures
    unsafe {
        *((base as isize + 16) as *mut i64) = boom_fn as *const () as i64;
        *((base as isize + 24) as *mut i64) = 0; // no drop glue
        *((base as isize + 32) as *mut i64) = msg.as_ptr() as i64;
        *((base as isize + 40) as *mut i64) = msg.len() as i64;
    }
    base as i64
}

// spec: 12-runtime §12.4.3 — Task B: first-error-wins on the INLINE-claim path.
// Two thunks panic with DISTINCT messages. Forcing the first inline sets the
// caller's slot to "first boom"; forcing the second inline must NOT clobber it —
// the save/restore around the inline thunk keeps the FIRST error (matching a
// sequential left-to-right evaluation that aborts on the first). Run many times
// to prove the outcome is deterministic, not racy. This is the `let`-path /
// inline-claim analogue of the apply-path `apply_arg_dual_panic_first_error_wins`
// e2e — the bug lived in the inline path polluting the caller's error slot.
#[test]
fn ivar_inline_claim_dual_panic_first_error_wins() {
    for i in 0..2000 {
        let _ = crate::panic::take_runtime_error(); // clear the slot

        let a = ivar_create(make_panicking_thunk_msg("first boom"));
        let b = ivar_create(make_panicking_thunk_msg("second boom"));

        // Barrier order: force A first (sets the first error), then B.
        let _ = ivar_force(a);
        let _ = ivar_force(b);

        let err = crate::panic::take_runtime_error();
        let msg = err.unwrap_or_default();
        assert!(
            msg.contains("first boom"),
            "iter {i}: first-error-wins — expected 'first boom', got {msg:?}"
        );
        assert!(
            !msg.contains("second boom"),
            "iter {i}: the second (inline) panic must NOT clobber the first, got {msg:?}"
        );

        // Cleanup both cells (each holds a ferried error String).
        ivar_dealloc(a);
        ivar_dealloc(b);
    }
}
