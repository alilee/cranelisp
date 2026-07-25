use super::*;
use crate::alloc::{alloc_count, dealloc_count};
use crate::heap_string::alloc_string;

/// Test helper — read the `len` field of a Vec for assertions. Mirrors
/// `cranelisp_primitives::vec::vec_len` without crossing the crate
/// boundary at test time.
fn test_vec_len(v: i64) -> i64 {
    unsafe { read_len(v as *const u8) }
}

fn heap_rc(base: i64) -> i64 {
    // SAFETY: test callers keep the asserted heap allocation live.
    unsafe { *((base as *const u8).add(8).cast::<i64>()) }
}

#[test]
fn vec_strings_from_owned_constructs_empty_vec() {
    // SAFETY: the empty input transfers no HeapString references.
    let vec = unsafe { vec_strings_from_owned(Vec::new()) };

    // SAFETY: `vec` is the live Vec allocation returned immediately above.
    unsafe {
        assert_eq!(read_len(vec as *const u8), 0);
        assert_eq!(read_cap(vec as *const u8), 0);
        assert!(read_data_ptr(vec as *const u8).is_null());
    }

    crate::drop::consume_vec_of_string(vec);
}

#[test]
fn vec_strings_from_owned_publishes_exact_layout_and_content() {
    let one = alloc_string(b"one") as i64;
    let two = alloc_string(b"two") as i64;
    // SAFETY: `one` and `two` each carry the fresh owned reference transferred
    // by this call.
    let vec = unsafe { vec_strings_from_owned(vec![one, two]) };

    // SAFETY: `vec` remains live and owned by this test through these canonical
    // fixed-offset reads.
    unsafe {
        let base = vec as *const u8;
        assert_eq!(read_len(base), 2);
        assert_eq!(read_cap(base), 2);
        let data = read_data_ptr(base);
        assert!(!data.is_null());
        assert_eq!(*data, one);
        assert_eq!(*data.add(1), two);
    }
    assert_eq!(heap_rc(one), 1);
    assert_eq!(heap_rc(two), 1);

    crate::drop::consume_vec_of_string(vec);
}

#[test]
fn unpublished_vec_strings_cleanup_covers_no_partial_and_full_initialization() {
    for initialized in 0..=2 {
        let one = alloc_string(b"one") as i64;
        let two = alloc_string(b"two") as i64;
        let (base, data) = {
            let mut unpublished = UnpublishedVecStrings::new(vec![one, two]);
            // SAFETY: the guard owns both fresh HeapString references;
            // `initialized` ranges from zero through the two-slot capacity.
            unsafe {
                unpublished.allocate();
                unpublished.initialize_prefix(initialized);
            }
            let base = unpublished.base as usize;
            let data = unpublished.data as usize;
            assert!(crate::alloc::is_live(one as usize));
            assert!(crate::alloc::is_live(two as usize));
            assert!(crate::alloc::is_live(base));
            assert!(databuf_guard::is_live(data));
            (base, data)
        };

        assert!(!crate::alloc::is_live(one as usize));
        assert!(!crate::alloc::is_live(two as usize));
        assert!(!crate::alloc::is_live(base));
        assert!(
            !databuf_guard::is_live(data),
            "the unpublished plain data buffer must be freed"
        );
    }
}

#[test]
fn with_vec_strings_scopes_a_non_owning_read() {
    let one = alloc_string(b"one") as i64;
    let two = alloc_string(b"two") as i64;
    // SAFETY: both fresh HeapString owned references transfer into the Vec.
    let vec = unsafe { vec_strings_from_owned(vec![one, two]) };

    // SAFETY: this test keeps `vec` alive and immutable for the callback, and
    // both live elements are HeapString base pointers.
    let observed = unsafe { with_vec_strings(vec, |elements| elements.to_vec()) };
    assert_eq!(observed, [one, two]);
    assert_eq!(heap_rc(one), 1);
    assert_eq!(heap_rc(two), 1);

    crate::drop::consume_vec_of_string(vec);
}

#[test]
fn with_vec_strings_reads_empty_vec_through_zero_length_sentinel() {
    // SAFETY: the empty input transfers no HeapString references.
    let vec = unsafe { vec_strings_from_owned(Vec::new()) };

    // SAFETY: `vec` is live and immutable for the callback; its canonical
    // zero-capacity representation has null data and no live elements.
    let observed_len = unsafe { with_vec_strings(vec, |elements| elements.len()) };
    assert_eq!(observed_len, 0);

    crate::drop::consume_vec_of_string(vec);
}

#[test]
fn with_vec_strings_does_not_consume_on_callback_unwind() {
    let string = alloc_string(b"still-owned") as i64;
    // SAFETY: the fresh HeapString owned reference transfers into the Vec.
    let vec = unsafe { vec_strings_from_owned(vec![string]) };

    let panic = std::panic::catch_unwind(|| {
        // SAFETY: `vec` remains live and immutable while the callback panics;
        // its sole live element is the HeapString allocated above.
        unsafe { with_vec_strings(vec, |_| panic!("callback panic")) }
    });
    assert!(panic.is_err());
    assert_eq!(heap_rc(string), 1);

    crate::drop::consume_vec_of_string(vec);
}

#[test]
fn with_vec_strings_rejects_invalid_metadata() {
    let vec = vec_new(1);
    // SAFETY: `vec` is a live canonical Vec allocation.
    let real_data = unsafe { read_data_ptr(vec as *const u8) };

    // SAFETY: `vec` is live and this writes its canonical len field; the
    // deliberately invalid value is restored before the Vec is dropped.
    unsafe {
        write_len(vec as *mut u8, -1);
    }
    assert!(
        std::panic::catch_unwind(|| {
            // SAFETY: this deliberately violates only `0 <= len`; the live,
            // aligned Vec base makes the metadata reads themselves valid.
            unsafe { with_vec_strings(vec, |_| ()) }
        })
        .is_err()
    );

    // SAFETY: `vec` remains live and this writes its canonical len field.
    unsafe {
        write_len(vec as *mut u8, 2);
    }
    assert!(
        std::panic::catch_unwind(|| {
            // SAFETY: this deliberately violates only `len <= cap`; the live,
            // aligned Vec base makes the metadata reads themselves valid.
            unsafe { with_vec_strings(vec, |_| ()) }
        })
        .is_err()
    );

    // SAFETY: `vec` remains live and both writes target canonical metadata
    // fields; the real data pointer is retained by the test for final cleanup.
    unsafe {
        write_len(vec as *mut u8, 0);
        write_data_ptr(vec as *mut u8, std::ptr::null_mut());
    }
    assert!(
        std::panic::catch_unwind(|| {
            // SAFETY: this deliberately violates only the positive-capacity
            // data-pointer condition; validation panics before slice creation.
            unsafe { with_vec_strings(vec, |_| ()) }
        })
        .is_err()
    );

    // SAFETY: `vec` remains live and this writes its canonical cap field; the
    // deliberately unrepresentable value is validated before data access.
    unsafe {
        write_cap(vec as *mut u8, i64::MAX);
    }
    assert!(
        std::panic::catch_unwind(|| {
            // SAFETY: this deliberately violates only byte-size
            // representability; validation panics before slice creation.
            unsafe { with_vec_strings(vec, |_| ()) }
        })
        .is_err()
    );

    // SAFETY: restore the original self-consistent metadata, including the
    // owned data allocation, before dropping the Vec.
    unsafe {
        write_cap(vec as *mut u8, 1);
        write_data_ptr(vec as *mut u8, real_data);
    }
    vec_drop(vec, 0);
}

#[test]
fn with_vec_strings_rejects_misaligned_positive_capacity_data() {
    let vec = vec_new(1);
    // SAFETY: `vec` is a live canonical Vec allocation.
    let real_data = unsafe { read_data_ptr(vec as *const u8) };

    // SAFETY: the write targets the live Vec metadata; the intentionally
    // misaligned derived pointer is not dereferenced.
    unsafe {
        write_data_ptr(vec as *mut u8, real_data.cast::<u8>().add(1).cast());
    }
    assert!(
        std::panic::catch_unwind(|| {
            // SAFETY: this deliberately violates only data alignment;
            // validation panics before slice creation.
            unsafe { with_vec_strings(vec, |_| ()) }
        })
        .is_err()
    );

    // SAFETY: restore the original live buffer pointer before dropping `vec`.
    unsafe {
        write_data_ptr(vec as *mut u8, real_data);
    }
    vec_drop(vec, 0);
}

#[test]
fn vec_string_rust_helpers_are_absent_from_emitted_call_catalogue() {
    let names: Vec<_> = crate::intrinsics_table()
        .iter()
        .map(|entry| entry.name)
        .collect();
    assert!(!names.contains(&"vec_strings_from_owned"));
    assert!(!names.contains(&"with_vec_strings"));
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
    unsafe {
        write_len(v as *mut u8, 2);
    }
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
static INC_CALL_COUNT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

extern "C" fn test_inc_fn(val: i64) -> i64 {
    INC_CALL_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    val
}

static DEC_CALL_COUNT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

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

// spec: 12-runtime §12.3.2 — vec-set copy does NOT inc the NEW value (FIXME 0417)
//
// PAIRED-OR-UAF guard (FIXME 0417). `vec_set_copy` inc's ONLY the retained
// copied-over elements; the new `val` stored at `idx` is left to the codegen-
// side consuming inc emitted up-front in `compile_vec_set` (mirroring
// `vec_push_copy`, which likewise does not inc the appended `val`). This pins
// the runtime half of the labour split: the helper must fire inc EXACTLY ONCE
// PER RETAINED ELEMENT and ZERO TIMES for the new value.
//
// The earlier behaviour — `vec_set_copy` inc'ing `val` unconditionally + a
// codegen compensation dec for temporaries — was the asymmetry FIXME 0417
// removed. Reintroducing the unconditional inc here WITHOUT restoring the
// codegen compensation (or vice-versa) is a use-after-free regression of
// FIXME 0296 — hence this test asserts the EXACT retained-only inc count.
//
// Isolate from the parallel-shared counter by using a thread-local count: we
// need an EXACT == assertion (not the delta >= used elsewhere) to prove the new
// value is NOT inc'd. A dedicated single-shot inc fn with its own counter gives
// a contention-free exact count.
#[test]
fn test_vec_set_copy_does_not_inc_new_value() {
    // Dedicated, contention-free counter for an EXACT-count assertion.
    static LOCAL_INC_COUNT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    extern "C" fn local_inc(val: i64) -> i64 {
        LOCAL_INC_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        val
    }

    let v = vec_new(3);
    unsafe {
        let data = read_data_ptr(v as *const u8);
        *data = 10;
        *data.add(1) = 20;
        *data.add(2) = 30;
        write_len(v as *mut u8, 3);
    }

    LOCAL_INC_COUNT.store(0, std::sync::atomic::Ordering::Relaxed);
    let inc_fn_ptr = local_inc as extern "C" fn(i64) -> i64;
    let v2 = vec_set_copy(v, 1, 99, inc_fn_ptr as usize as i64);

    // EXACTLY 2 incs: the two RETAINED elements (indices 0, 2). The new value
    // (99 at index 1) MUST NOT be inc'd — codegen owns its consuming inc.
    let count = LOCAL_INC_COUNT.load(std::sync::atomic::Ordering::Relaxed);
    assert_eq!(
        count, 2,
        "vec_set_copy must inc EXACTLY the 2 retained elements and NOT the new \
         value (FIXME 0417); got {count} incs"
    );

    // Confirm the new value landed correctly regardless of RC.
    unsafe {
        let data = read_data_ptr(v2 as *const u8);
        assert_eq!(*data.add(1), 99);
    }

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
