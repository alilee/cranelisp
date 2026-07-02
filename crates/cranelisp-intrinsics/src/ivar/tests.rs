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
    assert!(err.is_some(), "panic must be re-raised on the joining thread");
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
    // Gate OFF: the pre-S99 default is 4× the worker count (byte-identical off).
    assert_eq!(effective_spark_cap(None, false, 1), 4, "off ⇒ 4×threads");
    assert_eq!(effective_spark_cap(None, false, 8), 32, "off ⇒ 4×threads");

    // Gate ON (no explicit budget): cap at exactly the worker count — the
    // saturation policy (spark iff a worker is free; inline the overflow).
    assert_eq!(effective_spark_cap(None, true, 1), 1, "saturation ⇒ 1×threads");
    assert_eq!(effective_spark_cap(None, true, 8), 8, "saturation ⇒ 1×threads");

    // An explicit `CRANELISP_SPARK_BUDGET` override always wins, gate or not —
    // including the `=0` always-reject cap.
    assert_eq!(effective_spark_cap(Some(3), true, 8), 3, "explicit override wins over gate");
    assert_eq!(effective_spark_cap(Some(3), false, 8), 3, "explicit override wins by default");
    assert_eq!(effective_spark_cap(Some(0), true, 8), 0, "explicit 0 wins (always-reject)");
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
    assert!(budget_grants(3, 1, cap), "1 free worker ⇒ spark the last slot");
    // Saturated: a full pool rejects ⇒ the caller inlines the branch.
    assert!(!budget_grants(4, 1, cap), "saturated pool ⇒ inline (no spark)");
    assert!(!budget_grants(5, 1, cap), "over-saturated ⇒ inline");
    // All-or-nothing for a batch: 1 free slot cannot admit a 2-spark batch.
    assert!(!budget_grants(3, 2, cap), "batch overflowing by 1 ⇒ inline wholesale");
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
