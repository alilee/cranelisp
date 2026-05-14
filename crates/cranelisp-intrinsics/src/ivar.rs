//! IVar — write-once synchronization cells for lenient evaluation.
//!
//! IVars are heap-allocated, RC-managed values used by the backend's
//! sparkability analysis to evaluate independent `let` bindings in parallel.
//!
//! ## Heap Layout (base-pointer convention, Decision 10)
//!
//! ```text
//! Base pointer ->
//!   +0   alloc_size: i64   (= 40)
//!   +8   rc: i64           (initial: 1, atomic)
//!   +16  state: i64        (atomic — PENDING/EVALUATING/RESOLVED)
//!   +24  value: i64        (result, valid when state = RESOLVED)
//!   +32  thunk: i64        (closure pointer — zero-arg thunk)
//! ```
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
    // 24 bytes payload: state(8) + value(8) + thunk(8)
    // allocator adds 16-byte header = 40 bytes total
    let base = alloc_with_rc(24);
    // SAFETY: base is a valid allocation of 40 bytes. We write fields at
    // known offsets within the payload area.
    unsafe {
        *((base as isize + STATE_OFFSET) as *mut i64) = PENDING;
        *((base as isize + VALUE_OFFSET) as *mut i64) = 0;
        *((base as isize + THUNK_OFFSET) as *mut i64) = thunk;
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
    // SAFETY: ivar is a valid base pointer; RC at offset 8 is an aligned i64.
    unsafe {
        let rc_ptr = (ivar as isize + RC_OFFSET) as *const AtomicI64;
        (*rc_ptr).fetch_add(1, Ordering::SeqCst);
    }

    rayon::spawn(move || {
        // Force the IVar (evaluate thunk if still PENDING).
        ivar_force(ivar);

        // Dec RC — spark task's reference is released.
        // SAFETY: ivar is still valid (we hold a reference from the inc above).
        let old_rc = unsafe {
            let rc_ptr = (ivar as isize + RC_OFFSET) as *const AtomicI64;
            (*rc_ptr).fetch_sub(1, Ordering::SeqCst)
        };

        if old_rc == 1 {
            // RC reached 0 — free the IVar.
            std::sync::atomic::fence(Ordering::Acquire);
            // SAFETY: RC was 1 (now 0), no other references exist.
            unsafe { dealloc(ivar as *mut u8) };
        }
    });

    0
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

            // Store result and publish RESOLVED state.
            unsafe {
                *((ivar as isize + VALUE_OFFSET) as *mut i64) = result;
            }
            state_ptr.store(RESOLVED, Ordering::SeqCst);

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
                    return unsafe { *((ivar as isize + VALUE_OFFSET) as *const i64) };
                }
                std::hint::spin_loop();
            }
        }
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

            // Alloc size should be 40 (16 header + 24 payload)
            let alloc_size = *(ivar as *const i64);
            assert_eq!(alloc_size, 40);
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
}
