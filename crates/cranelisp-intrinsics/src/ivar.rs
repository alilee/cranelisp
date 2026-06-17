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

use std::sync::atomic::{AtomicI64, Ordering};

use crate::alloc::{alloc_with_rc, dealloc};

/// IVar states.
const PENDING: i64 = 0;
const EVALUATING: i64 = 1;
const RESOLVED: i64 = 2;

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
mod tests {
    use super::*;
    use crate::alloc::alloc_with_rc;

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
}
