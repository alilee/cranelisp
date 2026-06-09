//! Vec runtime primitives for JIT-compiled Cranelisp code.
//!
//! A Vec value consists of two allocations:
//! - **Vec struct**: `[HeapHeader(16) | len(8) | cap(8) | data_ptr(8)]` = 40 bytes total
//!   Allocated via `alloc_with_rc` (has RC header).
//! - **Data buffer**: `cap * 8` bytes, plain allocation (no RC header).
//!
//! Layout offsets from base pointer:
//! - `+0`:  alloc_size (i64, from HeapHeader)
//! - `+8`:  rc (i64, from HeapHeader)
//! - `+16`: len (i64)
//! - `+24`: cap (i64)
//! - `+32`: data_ptr (i64, pointer to data buffer)
//!
//! All elements are i64 (uniform representation). Only indices `0..len` are live.
//!
//! ## Module name rationale
//!
//! Renamed from `vec` to `vec_runtime` in Sprint 67 Wave 3 (FIXME 0180 close).
//! The user-callable `vec-len` accessor physically lives in
//! `cranelisp-primitives::vec`; everything else here is backend-emitted-call
//! infrastructure (`runtime/vec_new`, `runtime/vec_drop`, the COW paths
//! `vec-set-copy` / `vec-push-copy` / `vec-push-grow`).

use std::alloc::{self, Layout};

use crate::alloc as heap_alloc_mod;

// ---------------------------------------------------------------------------
// Layout constants
// ---------------------------------------------------------------------------

/// Offset of `len` field from base pointer.
///
/// Blessed public-ABI contract (FIXME 0245): `cranelisp-primitives` reads this.
pub const LEN_OFFSET: usize = 16;
/// Offset of `cap` field from base pointer.
///
/// Blessed public-ABI contract (FIXME 0245): `cranelisp-primitives` reads this.
pub const CAP_OFFSET: usize = 24;
/// Offset of `data_ptr` field from base pointer.
///
/// Blessed public-ABI contract (FIXME 0245): `cranelisp-primitives` reads this.
pub const DATA_PTR_OFFSET: usize = 32;
/// Payload size after HeapHeader: len + cap + data_ptr = 24 bytes.
const VEC_PAYLOAD_SIZE: usize = 24;

// Single-source guard: lock the blessed layout-ABI offsets (FIXME 0245).
// Future drift in these values fails the build.
const _: () = assert!(LEN_OFFSET == 16);
const _: () = assert!(CAP_OFFSET == 24);
const _: () = assert!(DATA_PTR_OFFSET == 32);

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Read the `len` field from a Vec base pointer.
///
/// # Safety
/// `base` must point to a valid Vec struct.
#[inline]
unsafe fn read_len(base: *const u8) -> i64 {
    unsafe { *base.add(LEN_OFFSET).cast::<i64>() }
}

/// Read the `cap` field from a Vec base pointer.
///
/// # Safety
/// `base` must point to a valid Vec struct.
#[inline]
unsafe fn read_cap(base: *const u8) -> i64 {
    unsafe { *base.add(CAP_OFFSET).cast::<i64>() }
}

/// Read the `data_ptr` field from a Vec base pointer.
///
/// # Safety
/// `base` must point to a valid Vec struct.
#[inline]
unsafe fn read_data_ptr(base: *const u8) -> *mut i64 {
    unsafe { *base.add(DATA_PTR_OFFSET).cast::<i64>() as *mut i64 }
}

/// Write the `len` field.
#[inline]
unsafe fn write_len(base: *mut u8, len: i64) {
    unsafe { *base.add(LEN_OFFSET).cast::<i64>() = len; }
}

/// Write the `cap` field.
#[inline]
unsafe fn write_cap(base: *mut u8, cap: i64) {
    unsafe { *base.add(CAP_OFFSET).cast::<i64>() = cap; }
}

/// Write the `data_ptr` field.
#[inline]
unsafe fn write_data_ptr(base: *mut u8, data_ptr: *mut i64) {
    unsafe { *base.add(DATA_PTR_OFFSET).cast::<i64>() = data_ptr as i64; }
}

/// Allocate a data buffer of `cap` elements (each i64 = 8 bytes).
/// Returns null if cap == 0.
fn alloc_data_buffer(cap: i64) -> *mut i64 {
    if cap <= 0 {
        return std::ptr::null_mut();
    }
    let byte_size = cap as usize * 8;
    let layout = Layout::from_size_align(byte_size, 8)
        .unwrap_or_else(|_| unreachable!("invariant: valid layout for size {byte_size}"));
    // SAFETY: layout is non-zero (cap > 0).
    let ptr = unsafe { alloc::alloc_zeroed(layout) };
    if ptr.is_null() {
        alloc::handle_alloc_error(layout);
    }
    ptr as *mut i64
}

/// Free a data buffer of `cap` elements.
///
/// # Safety
/// `data_ptr` must have been allocated by `alloc_data_buffer` with the given `cap`.
unsafe fn free_data_buffer(data_ptr: *mut i64, cap: i64) {
    if data_ptr.is_null() || cap <= 0 {
        return;
    }
    let byte_size = cap as usize * 8;
    let layout = Layout::from_size_align(byte_size, 8)
        .unwrap_or_else(|_| unreachable!("invariant: valid layout for size {byte_size}"));
    unsafe { alloc::dealloc(data_ptr as *mut u8, layout) };
}

/// Type alias for element inc/dec callback function pointer.
type ElemFn = extern "C" fn(i64) -> i64;

/// Call an element function if the pointer is non-null.
#[inline]
fn call_elem_fn(fn_ptr: i64, val: i64) {
    if fn_ptr != 0 {
        let f: ElemFn = unsafe { std::mem::transmute(fn_ptr) };
        f(val);
    }
}

// ---------------------------------------------------------------------------
// Extern C interface (called from JIT code)
// ---------------------------------------------------------------------------

/// Allocate a new Vec with the given initial capacity.
///
/// Allocates the Vec struct (40 bytes = 16 header + 24 payload) via `alloc_with_rc`.
/// Allocates a separate data buffer of `cap * 8` bytes.
/// Sets len=0, cap=cap, data_ptr to the data buffer.
/// Returns base pointer to the Vec struct (rc=1).
///
/// JIT name: "runtime/vec_new" — exported via export_name so link-mode resolves.
#[unsafe(export_name = "runtime/vec_new")]
pub extern "C" fn vec_new(cap: i64) -> i64 {
    let base = heap_alloc_mod::alloc_with_rc(VEC_PAYLOAD_SIZE);
    let data = alloc_data_buffer(cap);

    unsafe {
        write_len(base, 0);
        write_cap(base, cap);
        write_data_ptr(base, data);
    }

    base as i64
}

// `vec-len` (user-callable Vec length accessor) physically lives in
// `cranelisp-primitives::vec` post-FIXME-0180. It is referenced from this
// crate only via that path; no shim here.

/// Vec set — copy path.
///
/// Allocates a new Vec, copies all elements from the source (calling `elem_inc_fn`
/// on each copied element for RC), and stores `val` at `idx`.
/// Does NOT dec the old element at `idx` — caller handles that.
/// Returns base pointer to the new Vec (rc=1).
///
/// `elem_inc_fn`: function pointer `(i64) -> i64` for per-element RC inc.
///                Pass 0 (null) for NeverHeap element types.
///
/// JIT name: "vec-set-copy" — exported via export_name so link-mode resolves.
#[unsafe(export_name = "vec-set-copy")]
pub extern "C" fn vec_set_copy(vec: i64, idx: i64, val: i64, elem_inc_fn: i64) -> i64 {
    let src = vec as *const u8;
    unsafe {
        let len = read_len(src);
        let cap = read_cap(src);
        let src_data = read_data_ptr(src);

        // Allocate new Vec struct + data buffer.
        let new_base = heap_alloc_mod::alloc_with_rc(VEC_PAYLOAD_SIZE);
        let new_data = alloc_data_buffer(cap);

        // Copy all elements, calling inc_fn on each.
        for i in 0..len as usize {
            let elem = *src_data.add(i);
            if i as i64 == idx {
                // Store the new value at the target index.
                *new_data.add(i) = val;
            } else {
                *new_data.add(i) = elem;
                call_elem_fn(elem_inc_fn, elem);
            }
        }

        // Inc the new value too: the returned Vec gains an owning reference to
        // `val`, while the caller still holds its own reference (which the
        // caller's scope cleanup will dec). Without this inc, a heap `val`
        // consumed into the copied Vec is double-counted as one reference and
        // freed prematurely when the caller dec's its copy — a use-after-free
        // surfacing as garbage reads on a later access (Sprint 77 W-Exemplar /
        // FIXME 0296). This mirrors the COW mutate-in-place codegen path, which
        // inc's new_val before storing it (`compile_vec_set_cow`). NeverHeap
        // elements pass `elem_inc_fn == 0`, so `call_elem_fn` is a no-op.
        call_elem_fn(elem_inc_fn, val);

        write_len(new_base, len);
        write_cap(new_base, cap);
        write_data_ptr(new_base, new_data);

        new_base as i64
    }
}

/// Vec push — copy path.
///
/// Allocates a new Vec with `len + 1` capacity, copies all existing elements
/// (calling `elem_inc_fn` on each), and appends `val`.
/// Returns base pointer to the new Vec (rc=1).
///
/// JIT name: "vec-push-copy" — exported via export_name so link-mode resolves.
#[unsafe(export_name = "vec-push-copy")]
pub extern "C" fn vec_push_copy(vec: i64, val: i64, elem_inc_fn: i64) -> i64 {
    let src = vec as *const u8;
    unsafe {
        let len = read_len(src);
        let src_data = read_data_ptr(src);

        let new_cap = len + 1;

        // Allocate new Vec struct + data buffer.
        let new_base = heap_alloc_mod::alloc_with_rc(VEC_PAYLOAD_SIZE);
        let new_data = alloc_data_buffer(new_cap);

        // Copy existing elements, calling inc_fn on each.
        for i in 0..len as usize {
            let elem = *src_data.add(i);
            *new_data.add(i) = elem;
            call_elem_fn(elem_inc_fn, elem);
        }

        // Append the new value.
        *new_data.add(len as usize) = val;

        write_len(new_base, len + 1);
        write_cap(new_base, new_cap);
        write_data_ptr(new_base, new_data);

        new_base as i64
    }
}

/// Vec push — growth path.
///
/// Called when the Vec is the unique owner (rc==1) but the data buffer is full
/// (len >= cap). Reallocates the data buffer with doubled capacity (minimum 4),
/// stores val at `data[len]`, increments len. Returns the same Vec pointer.
///
/// JIT name: "vec-push-grow" — exported via export_name so link-mode resolves.
#[unsafe(export_name = "vec-push-grow")]
pub extern "C" fn vec_push_grow(vec: i64, val: i64) -> i64 {
    let base = vec as *mut u8;
    unsafe {
        let len = read_len(base);
        let old_cap = read_cap(base);
        let old_data = read_data_ptr(base);

        // Double capacity (minimum 4).
        let new_cap = if old_cap == 0 { 4 } else { old_cap * 2 };
        let new_data = alloc_data_buffer(new_cap);

        // Copy existing elements to new buffer.
        if len > 0 && !old_data.is_null() {
            std::ptr::copy_nonoverlapping(old_data, new_data, len as usize);
        }

        // Free old data buffer.
        free_data_buffer(old_data, old_cap);

        // Store new value at data[len].
        *new_data.add(len as usize) = val;

        // Update Vec struct fields.
        write_len(base, len + 1);
        write_cap(base, new_cap);
        write_data_ptr(base, new_data);

        vec
    }
}

/// Vec drop glue.
///
/// Loops through elements `0..len`, calling `elem_dec_fn` on each (if non-null).
/// Frees the data buffer, then frees the Vec struct.
///
/// `elem_dec_fn`: function pointer `(i64) -> i64` for per-element RC dec.
///                Pass 0 (null) for NeverHeap element types.
///
/// JIT name: "runtime/vec_drop" — exported via export_name so link-mode resolves.
#[unsafe(export_name = "runtime/vec_drop")]
pub extern "C" fn vec_drop(vec: i64, elem_dec_fn: i64) {
    let base = vec as *mut u8;
    unsafe {
        let len = read_len(base);
        let cap = read_cap(base);
        let data = read_data_ptr(base);

        // Dec each live element.
        if elem_dec_fn != 0 {
            for i in 0..len as usize {
                let elem = *data.add(i);
                call_elem_fn(elem_dec_fn, elem);
            }
        }

        // Free data buffer.
        free_data_buffer(data, cap);

        // Free Vec struct.
        heap_alloc_mod::dealloc(base);
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
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
}
