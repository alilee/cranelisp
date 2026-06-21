use super::*;
use crate::alloc::{alloc_count, dealloc_count};

/// Test helper — read the `len` field of a Vec for assertions. Mirrors
/// `cranelisp_primitives::vec::vec_len` without crossing the crate
/// boundary at test time.
fn test_vec_len(v: i64) -> i64 {
    unsafe { read_len(v as *const u8) }
}

// spec: 12-runtime §12.1.5 — Vec creation with capacity, heap layout [len | cap | data_ptr]
#[test]
fn test_vec_new_basic() {
    let allocs_before = alloc_count();
    let v = vec_new(4);
    assert_ne!(v, 0);
    assert_eq!(test_vec_len(v), 0);

    // Verify fields.
    unsafe {
        let base = v as *const u8;
        assert_eq!(read_cap(base), 4);
        assert!(!read_data_ptr(base).is_null());
    }

    assert!(alloc_count() - allocs_before >= 1);

    // Clean up.
    vec_drop(v, 0);
}

// spec: 12-runtime §12.1.5 — Vec with zero capacity (null data pointer)
#[test]
fn test_vec_new_zero_capacity() {
    let v = vec_new(0);
    assert_ne!(v, 0);
    assert_eq!(test_vec_len(v), 0);
    unsafe {
        assert_eq!(read_cap(v as *const u8), 0);
        assert!(read_data_ptr(v as *const u8).is_null());
    }
    // Drop with no data buffer.
    vec_drop(v, 0);
}

// spec: appendix-a-builtins §A.3 — vec-push grows from empty Vec
#[test]
fn test_vec_push_grow_from_empty() {
    let v = vec_new(0);
    assert_eq!(test_vec_len(v), 0);

    // Push a value — should grow.
    let v = vec_push_grow(v, 42);
    assert_eq!(test_vec_len(v), 1);
    unsafe {
        let data = read_data_ptr(v as *const u8);
        assert_eq!(*data, 42);
        assert!(read_cap(v as *const u8) >= 1);
    }

    vec_drop(v, 0);
}

// spec: appendix-a-builtins §A.3 — vec-push doubles capacity on grow
#[test]
fn test_vec_push_grow_doubles_capacity() {
    let v = vec_new(2);
    // Manually set len = 2 to simulate a full buffer.
    unsafe { write_len(v as *mut u8, 2); }
    unsafe {
        let data = read_data_ptr(v as *const u8);
        *data = 10;
        *data.add(1) = 20;
    }

    let v = vec_push_grow(v, 30);
    assert_eq!(test_vec_len(v), 3);
    unsafe {
        let cap = read_cap(v as *const u8);
        assert_eq!(cap, 4); // doubled from 2
        let data = read_data_ptr(v as *const u8);
        assert_eq!(*data, 10);
        assert_eq!(*data.add(1), 20);
        assert_eq!(*data.add(2), 30);
    }

    vec_drop(v, 0);
}

// spec: 12-runtime §12.3.3 — vec-push copy path preserves original Vec
#[test]
fn test_vec_push_copy_basic() {
    let v = vec_new(2);
    // Manually store elements.
    unsafe {
        let data = read_data_ptr(v as *const u8);
        *data = 100;
        *data.add(1) = 200;
        write_len(v as *mut u8, 2);
    }

    let v2 = vec_push_copy(v, 300, 0);
    assert_eq!(test_vec_len(v2), 3);
    unsafe {
        let data = read_data_ptr(v2 as *const u8);
        assert_eq!(*data, 100);
        assert_eq!(*data.add(1), 200);
        assert_eq!(*data.add(2), 300);
    }

    // Original should be unchanged.
    assert_eq!(test_vec_len(v), 2);

    vec_drop(v, 0);
    vec_drop(v2, 0);
}

// spec: 12-runtime §12.3.3 — vec-set copy path returns new Vec, original unchanged
#[test]
fn test_vec_set_copy_basic() {
    let v = vec_new(3);
    unsafe {
        let data = read_data_ptr(v as *const u8);
        *data = 1;
        *data.add(1) = 2;
        *data.add(2) = 3;
        write_len(v as *mut u8, 3);
    }

    let v2 = vec_set_copy(v, 1, 99, 0);
    assert_eq!(test_vec_len(v2), 3);
    unsafe {
        let data = read_data_ptr(v2 as *const u8);
        assert_eq!(*data, 1);
        assert_eq!(*data.add(1), 99);
        assert_eq!(*data.add(2), 3);
    }

    // Original unchanged.
    unsafe {
        let data = read_data_ptr(v as *const u8);
        assert_eq!(*data.add(1), 2);
    }

    vec_drop(v, 0);
    vec_drop(v2, 0);
}

// spec: 12-runtime §12.3.1 — Vec drop frees all memory (header + data buffer)
#[test]
fn test_vec_drop_with_null_dec_fn() {
    let allocs_before = alloc_count();
    let deallocs_before = dealloc_count();
    let v = vec_new(4);
    unsafe {
        let data = read_data_ptr(v as *const u8);
        *data = 42;
        write_len(v as *mut u8, 1);
    }
    vec_drop(v, 0);
    // Delta-based: at least 1 alloc (vec struct), 1 dealloc (vec struct).
    assert!(alloc_count() - allocs_before >= 1);
    assert!(dealloc_count() - deallocs_before >= 1);
}

/// A simple inc function for testing: increments a global counter.
static INC_CALL_COUNT: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

extern "C" fn test_inc_fn(val: i64) -> i64 {
    INC_CALL_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    val
}

static DEC_CALL_COUNT: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

extern "C" fn test_dec_fn(val: i64) -> i64 {
    DEC_CALL_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    val
}

// spec: 12-runtime §12.3.2 — vec-set copy calls RC inc on retained elements
#[test]
fn test_vec_set_copy_calls_inc_fn() {
    let before = INC_CALL_COUNT.load(std::sync::atomic::Ordering::Relaxed);

    let v = vec_new(3);
    unsafe {
        let data = read_data_ptr(v as *const u8);
        *data = 10;
        *data.add(1) = 20;
        *data.add(2) = 30;
        write_len(v as *mut u8, 3);
    }

    let inc_fn_ptr = test_inc_fn as extern "C" fn(i64) -> i64;
    let v2 = vec_set_copy(v, 1, 99, inc_fn_ptr as usize as i64);

    // inc_fn should have been called for elements at indices 0 and 2 (not 1, the replaced one).
    // Delta-based (>=) because parallel tests share the same INC_CALL_COUNT.
    let after = INC_CALL_COUNT.load(std::sync::atomic::Ordering::Relaxed);
    assert!(after - before >= 2);

    vec_drop(v, 0);
    vec_drop(v2, 0);
}

// spec: 12-runtime §12.3.2 — vec-set copy also inc's the NEW value
//
// Regression for Sprint 77 W-Exemplar / FIXME 0296: the copied Vec gains an
// owning reference to the replacement value, so `vec-set-copy` MUST inc it.
// Without this inc, a heap value consumed into the copied Vec while the
// caller still owns its own reference (and dec's it at scope exit) is freed
// prematurely — a use-after-free that surfaced as the Sudoku-solver runtime
// stack overflow (garbage cell value → unbounded `pow2` recursion).
#[test]
fn test_vec_set_copy_incs_new_value() {
    let before = INC_CALL_COUNT.load(std::sync::atomic::Ordering::Relaxed);

    let v = vec_new(3);
    unsafe {
        let data = read_data_ptr(v as *const u8);
        *data = 10;
        *data.add(1) = 20;
        *data.add(2) = 30;
        write_len(v as *mut u8, 3);
    }

    let inc_fn_ptr = test_inc_fn as extern "C" fn(i64) -> i64;
    let v2 = vec_set_copy(v, 1, 99, inc_fn_ptr as usize as i64);

    // inc_fn must fire for the two retained elements (indices 0, 2) AND for
    // the new value (99) stored at index 1: three incs total.
    let after = INC_CALL_COUNT.load(std::sync::atomic::Ordering::Relaxed);
    assert!(
        after - before >= 3,
        "expected >=3 incs (2 retained + 1 new value), got {}",
        after - before
    );

    vec_drop(v, 0);
    vec_drop(v2, 0);
}

// spec: 12-runtime §12.3.2 — vec-push copy calls RC inc on existing elements
#[test]
fn test_vec_push_copy_calls_inc_fn() {
    let before = INC_CALL_COUNT.load(std::sync::atomic::Ordering::Relaxed);

    let v = vec_new(2);
    unsafe {
        let data = read_data_ptr(v as *const u8);
        *data = 10;
        *data.add(1) = 20;
        write_len(v as *mut u8, 2);
    }

    let inc_fn_ptr = test_inc_fn as extern "C" fn(i64) -> i64;
    let v2 = vec_push_copy(v, 30, inc_fn_ptr as usize as i64);

    // Delta-based (>=) because parallel tests share the same INC_CALL_COUNT.
    let after = INC_CALL_COUNT.load(std::sync::atomic::Ordering::Relaxed);
    assert!(after - before >= 2); // two existing elements

    vec_drop(v, 0);
    vec_drop(v2, 0);
}

// spec: 12-runtime §12.3.1 — Vec drop calls RC dec on all elements
#[test]
fn test_vec_drop_calls_dec_fn() {
    let before = DEC_CALL_COUNT.load(std::sync::atomic::Ordering::Relaxed);

    let v = vec_new(3);
    unsafe {
        let data = read_data_ptr(v as *const u8);
        *data = 10;
        *data.add(1) = 20;
        *data.add(2) = 30;
        write_len(v as *mut u8, 3);
    }

    let dec_fn_ptr = test_dec_fn as extern "C" fn(i64) -> i64;
    vec_drop(v, dec_fn_ptr as usize as i64);

    // Delta-based (>=) because parallel tests could share the same DEC_CALL_COUNT.
    let after = DEC_CALL_COUNT.load(std::sync::atomic::Ordering::Relaxed);
    assert!(after - before >= 3);
}

// spec: appendix-a-builtins §A.3 — vec-push grow preserves existing data
#[test]
fn test_vec_push_grow_preserves_data() {
    // Build a Vec with cap=4, fill it, then push to trigger growth.
    let v = vec_new(4);
    unsafe {
        let data = read_data_ptr(v as *const u8);
        for i in 0..4 {
            *data.add(i) = (i * 10 + 1) as i64;
        }
        write_len(v as *mut u8, 4);
    }

    let v = vec_push_grow(v, 999);
    assert_eq!(test_vec_len(v), 5);
    unsafe {
        let cap = read_cap(v as *const u8);
        assert_eq!(cap, 8); // doubled from 4
        let data = read_data_ptr(v as *const u8);
        assert_eq!(*data, 1);
        assert_eq!(*data.add(1), 11);
        assert_eq!(*data.add(2), 21);
        assert_eq!(*data.add(3), 31);
        assert_eq!(*data.add(4), 999);
    }

    vec_drop(v, 0);
}

// spec: appendix-a-builtins §A.3 — vec-set replaces first element
#[test]
fn test_vec_set_copy_first_element() {
    let v = vec_new(2);
    unsafe {
        let data = read_data_ptr(v as *const u8);
        *data = 1;
        *data.add(1) = 2;
        write_len(v as *mut u8, 2);
    }

    let v2 = vec_set_copy(v, 0, 77, 0);
    unsafe {
        let data = read_data_ptr(v2 as *const u8);
        assert_eq!(*data, 77);
        assert_eq!(*data.add(1), 2);
    }

    vec_drop(v, 0);
    vec_drop(v2, 0);
}

// spec: appendix-a-builtins §A.3 — vec-set replaces last element
#[test]
fn test_vec_set_copy_last_element() {
    let v = vec_new(3);
    unsafe {
        let data = read_data_ptr(v as *const u8);
        *data = 10;
        *data.add(1) = 20;
        *data.add(2) = 30;
        write_len(v as *mut u8, 3);
    }

    let v2 = vec_set_copy(v, 2, 88, 0);
    unsafe {
        let data = read_data_ptr(v2 as *const u8);
        assert_eq!(*data, 10);
        assert_eq!(*data.add(1), 20);
        assert_eq!(*data.add(2), 88);
    }

    vec_drop(v, 0);
    vec_drop(v2, 0);
}

// spec: 12-runtime §12.3.1 — Vec drop frees all memory (verified via alloc/dealloc counter delta)
#[test]
fn test_vec_memory_cleanup() {
    let allocs_before = alloc_count();
    let deallocs_before = dealloc_count();

    let v = vec_new(8);
    unsafe {
        let data = read_data_ptr(v as *const u8);
        for i in 0..5 {
            *data.add(i) = i as i64;
        }
        write_len(v as *mut u8, 5);
    }

    vec_drop(v, 0);
    // Delta-based: at least 1 alloc (vec struct), 1 dealloc (vec struct).
    assert!(alloc_count() - allocs_before >= 1);
    assert!(dealloc_count() - deallocs_before >= 1);
}
