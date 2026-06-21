use super::*;
use crate::alloc::{alloc_count, alloc_with_rc, dealloc_count};
use crate::heap_string::alloc_string;
use crate::vec_runtime::{vec_drop, vec_new, vec_set_copy};
use cranelisp_types::{TAG_SCONS, TAG_SEXP_LIST, TAG_SEXP_STR};

const TAG_OFF: usize = TAG_OFFSET;
const F0_OFF: usize = FIELD0_OFFSET;
const F1_OFF: usize = FIELD1_OFFSET;

/// Run `build`, capture the allocations it produced, run `release`, and
/// assert the runtime allocator saw exactly as many deallocs as allocs.
/// This is the crate-internal stand-in for the legacy `assert_rc_balanced`.
fn assert_balanced<T>(build: impl FnOnce() -> T, release: impl FnOnce(T)) {
    let allocs_before = alloc_count();
    let deallocs_before = dealloc_count();
    let handle = build();
    let allocated = alloc_count() - allocs_before;
    assert!(allocated > 0, "harness error: build allocated nothing to balance");
    release(handle);
    let deallocated = dealloc_count() - deallocs_before;
    assert_eq!(
        allocated, deallocated,
        "RC imbalance: {allocated} allocs but {deallocated} deallocs"
    );
}

fn write_field(base: i64, offset: usize, value: i64) {
    // SAFETY: `base` is a live alloc with room for the offset (asserted by
    // the payload size each builder requests).
    unsafe { *((base as *mut u8).add(offset) as *mut i64) = value };
}

/// `extern "C" fn(i64) -> i64` element-dec for `vec_drop`, which transmutes
/// `elem_dec_fn` to exactly this ABI. `rc::consume_shallow` is a Rust-ABI
/// `fn(i64)` and cannot be passed directly — this is the ABI-correct shim.
extern "C" fn consume_string_elem(ptr: i64) -> i64 {
    rc::consume_shallow(ptr);
    0
}

fn make_sexp_str(s_ptr: i64) -> i64 {
    let base = alloc_with_rc(16) as i64; // tag + sval
    write_field(base, TAG_OFF, TAG_SEXP_STR);
    write_field(base, F0_OFF, s_ptr);
    base
}

fn make_scons(head: i64, tail: i64) -> i64 {
    let base = alloc_with_rc(24) as i64; // tag + head + tail
    write_field(base, TAG_OFF, TAG_SCONS);
    write_field(base, F0_OFF, head);
    write_field(base, F1_OFF, tail);
    base
}

// spec: spec/12-runtime.md §12.3 — ADT sum (Some "x") frees its String
// field with the container. Legacy `rc_mixed_adt_some_drop_balanced`.
#[test]
fn rc_balance_adt_sum_with_string_field() {
    assert_balanced(
        || make_sexp_str(alloc_string(b"hello") as i64),
        consume_sexp,
    );
}

// spec: spec/12-runtime.md §12.3 — product ADT with two String fields:
// both fields freed with the container. Legacy `rc_u1_3_pair_of_strings`.
#[test]
fn rc_balance_adt_product_two_string_fields() {
    // Model a 2-field product as a SexpList over an SList of two SexpStr
    // wrappers — both String fields and both wrappers must be released.
    assert_balanced(
        || {
            let s1 = make_sexp_str(alloc_string(b"hello") as i64);
            let s2 = make_sexp_str(alloc_string(b"world") as i64);
            let list = make_scons(s1, make_scons(s2, 0));
            let base = alloc_with_rc(16) as i64; // SexpList: tag + items
            write_field(base, TAG_OFF, TAG_SEXP_LIST);
            write_field(base, F0_OFF, list);
            base
        },
        consume_sexp,
    );
}

// spec: spec/12-runtime.md §12.3 — nested ADT (list of two heap Sexps):
// recursive RC walk frees every node. Legacy `rc_adt_nested_option` /
// `rc_u1_3_*` recursive-RC cohort.
#[test]
fn rc_balance_nested_recursive() {
    assert_balanced(
        || {
            let a = make_sexp_str(alloc_string(b"a") as i64);
            let b = make_sexp_str(alloc_string(b"b") as i64);
            let c = make_sexp_str(alloc_string(b"c") as i64);
            make_scons(a, make_scons(b, make_scons(c, 0)))
        },
        consume_slist,
    );
}

// spec: spec/12-runtime.md §12.3 — closure environment freed on drop. A
// bare (capture-less) closure: env struct is released. Legacy
// `rc_closure_no_capture` / `rc_closure_env_alloc`.
#[test]
fn rc_balance_closure_env() {
    assert_balanced(
        || {
            let c = alloc_with_rc(16) as i64; // code_ptr + drop_glue_ptr
            write_field(c, 16, 0); // code_ptr
            write_field(c, 24, 0); // drop_glue_ptr = 0 (no captures)
            c
        },
        consume_closure,
    );
}

// spec: spec/12-runtime.md §12.3 — closure capturing a heap String, with
// backend-style inline drop glue that dec's the capture, frees both the
// env and the captured String. Legacy `rc_closure_captures_string_balanced`.
#[test]
fn rc_balance_closure_captures_string() {
    // Drop glue mirrors the backend's emitted glue: dec the capture at
    // offset 32 (first capture slot), then return.
    extern "C" fn drop_glue_one_string_capture(closure_ptr: i64) {
        // SAFETY: closure_ptr is the live env; the capture i64 lives at +32.
        let capture = unsafe { read_i64(closure_ptr, 32) };
        rc::consume_shallow(capture);
    }
    assert_balanced(
        || {
            let s = alloc_string(b"captured") as i64;
            let c = alloc_with_rc(24) as i64; // code_ptr + drop_glue + 1 capture
            write_field(c, 16, 0); // code_ptr
            write_field(c, 24, drop_glue_one_string_capture as *const () as i64);
            write_field(c, 32, s); // capture slot 0
            c
        },
        consume_closure,
    );
}

// spec: spec/12-runtime.md §12.3 — closure capturing two heap Strings:
// both captures freed by the glue. Legacy
// `rc_u1_5_closure_captures_multiple_heap_values`.
#[test]
fn rc_balance_closure_multiple_captures() {
    extern "C" fn drop_glue_two_string_captures(closure_ptr: i64) {
        // SAFETY: two captures at +32 and +40.
        let c0 = unsafe { read_i64(closure_ptr, 32) };
        let c1 = unsafe { read_i64(closure_ptr, 40) };
        rc::consume_shallow(c0);
        rc::consume_shallow(c1);
    }
    assert_balanced(
        || {
            let a = alloc_string(b"hello") as i64;
            let b = alloc_string(b"world") as i64;
            let c = alloc_with_rc(32) as i64; // code + glue + 2 captures
            write_field(c, 16, 0);
            write_field(c, 24, drop_glue_two_string_captures as *const () as i64);
            write_field(c, 32, a);
            write_field(c, 40, b);
            c
        },
        consume_closure,
    );
}

/// Write the three Vec struct fields directly: len, cap, data_ptr. Element
/// payloads are written through the data buffer `vec_new` already allocated.
fn fill_int_vec(v: i64, elems: &[i64]) {
    // SAFETY: `v` is a live Vec struct from `vec_new(cap)` with cap >= len;
    // the data buffer it owns has room for `elems.len()` i64s.
    unsafe {
        let data = read_i64(v, VEC_DATA_PTR_OFFSET) as *mut i64;
        for (i, e) in elems.iter().enumerate() {
            *data.add(i) = *e;
        }
        *((v as *mut u8).add(VEC_LEN_OFFSET) as *mut i64) = elems.len() as i64;
    }
}

// spec: spec/12-runtime.md §12.3.3 — Vec copy-on-write: after vec-set-copy
// the original and the copied Vec are distinct STRUCT allocations and BOTH
// must be freed (no shared-buffer double-free, no leak). Only the two Vec
// structs are RC-tracked; the data buffers use the untracked plain
// allocator. Legacy `rc_vec_set_copy`.
#[test]
fn rc_balance_vec_cow_set() {
    let allocs_before = alloc_count();
    let deallocs_before = dealloc_count();

    // Build a 3-element Int Vec, then vec-set-copy produces a second,
    // independent Vec (COW). Int elements are NeverHeap (null elem fns).
    let v = vec_new(3); // 1 tracked struct alloc
    fill_int_vec(v, &[1, 2, 3]);
    let allocs_after_first = alloc_count();
    let v2 = vec_set_copy(v, 1, 99, 0); // 1 more tracked struct alloc
    assert_ne!(v, v2, "vec-set-copy must produce a distinct allocation (COW)");
    assert_eq!(
        alloc_count() - allocs_after_first,
        1,
        "vec-set-copy must allocate exactly one new Vec struct"
    );

    // Both Vecs are live and independent. Free both — exact struct balance.
    vec_drop(v, 0);
    vec_drop(v2, 0);

    let allocated = alloc_count() - allocs_before;
    let deallocated = dealloc_count() - deallocs_before;
    assert_eq!(
        allocated, deallocated,
        "Vec COW imbalance: {allocated} struct allocs but {deallocated} struct deallocs"
    );
}

// spec: spec/12-runtime.md §12.3 — Vec of heap Strings: element Strings are
// freed with the Vec. The Vec struct + 3 Strings are RC-tracked; the data
// buffer is not. Legacy `rc_vec_of_strings`.
#[test]
fn rc_balance_vec_of_strings() {
    let allocs_before = alloc_count();
    let deallocs_before = dealloc_count();

    let v = vec_new(3); // 1 tracked struct alloc
    let strs = [
        alloc_string(b"a") as i64,
        alloc_string(b"b") as i64,
        alloc_string(b"c") as i64,
    ]; // 3 tracked string allocs
    fill_int_vec(v, &strs);
    // Drop the Vec with the String element-dec fn so each element is freed.
    vec_drop(v, consume_string_elem as *const () as i64);

    let allocated = alloc_count() - allocs_before;
    let deallocated = dealloc_count() - deallocs_before;
    assert_eq!(
        allocated, deallocated,
        "Vec-of-strings imbalance: {allocated} allocs (struct + 3 strings) but {deallocated} deallocs"
    );
}

// spec: spec/12-runtime.md §12.3 — consuming convention: an extern that
// receives a heap arg it does not return MUST release it (callee owns heap
// params). Legacy `rc_lambda_unused_string_param_freed` /
// `rc_defn_unused_string_param_freed`.
#[test]
fn rc_balance_consume_unused_string_param() {
    assert_balanced(
        || alloc_string(b"hello") as i64,
        rc::consume_shallow,
    );
}

// spec: spec/12-runtime.md §12.3 — multiple unused heap params each freed.
// Legacy `rc_lambda_multiple_unused_heap_params_freed`.
#[test]
fn rc_balance_consume_multiple_unused_params() {
    let allocs_before = alloc_count();
    let deallocs_before = dealloc_count();
    let a = alloc_string(b"x") as i64;
    let b = alloc_string(b"y") as i64;
    rc::consume_shallow(a);
    rc::consume_shallow(b);
    assert_eq!(alloc_count() - allocs_before, 2);
    assert_eq!(dealloc_count() - deallocs_before, 2);
}
