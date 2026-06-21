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
