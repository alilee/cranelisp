//! Vec operations: extern "C" functions for the built-in Vec type.
//!
//! Vec runtime layout (all i64):
//! ```text
//! RC header:  [size | rc]           <- at ptr-16, ptr-8 (from alloc_with_rc)
//! Payload:    [len | cap | data_ptr] <- at ptr+0, ptr+8, ptr+16
//! ```
//! Data buffer is a separate alloc_with_rc allocation containing elements as i64s.
//! Empty Vec: len=0, cap=0, data_ptr=0.

use crate::intrinsics::alloc_with_rc;

/// `vec-get :: (Vec a, Int) -> a`
/// Bounds-checked element access.
#[unsafe(export_name = "vec-get")]
pub extern "C" fn vec_get(vec_ptr: i64, index: i64) -> i64 {
    unsafe {
        let ptr = vec_ptr as *const i64;
        let len = *ptr;
        if index < 0 || index >= len {
            eprintln!("panic: vec-get index {} out of bounds (len {})", index, len);
            std::process::exit(1);
        }
        let data_ptr = *ptr.add(2) as *const i64;
        *data_ptr.add(index as usize)
    }
}

/// `vec-set :: (Vec a, Int, a) -> (Vec a)`
/// Always copies: allocates a new Vec header + data buffer, copies elements,
/// sets element[index] = val, returns the new Vec pointer.
#[unsafe(export_name = "vec-set")]
pub extern "C" fn vec_set(vec_ptr: i64, index: i64, val: i64) -> i64 {
    unsafe {
        let ptr = vec_ptr as *const i64;
        let len = *ptr;
        let cap = *ptr.add(1);
        let old_data = *ptr.add(2) as *const i64;

        if index < 0 || index >= len {
            eprintln!("panic: vec-set index {} out of bounds (len {})", index, len);
            std::process::exit(1);
        }

        // Allocate new header
        let new_header = alloc_with_rc(24) as *mut i64;
        // Allocate new data buffer
        let new_data = alloc_with_rc((cap as usize) * 8) as *mut i64;

        // Copy all elements
        std::ptr::copy_nonoverlapping(old_data, new_data, len as usize);
        // Apply mutation
        *new_data.add(index as usize) = val;

        // Fill header
        *new_header = len;
        *new_header.add(1) = cap;
        *new_header.add(2) = new_data as i64;

        new_header as i64
    }
}

/// `vec-push :: (Vec a, a) -> (Vec a)`
/// Always copies: allocates a new Vec header + data buffer with len+1 elements.
#[unsafe(export_name = "vec-push")]
pub extern "C" fn vec_push(vec_ptr: i64, val: i64) -> i64 {
    unsafe {
        let ptr = vec_ptr as *const i64;
        let len = *ptr;
        let old_data = *ptr.add(2) as *const i64;
        let new_len = len + 1;
        let new_cap = new_len;

        // Allocate new header
        let new_header = alloc_with_rc(24) as *mut i64;
        // Allocate new data buffer
        let new_data = alloc_with_rc((new_cap as usize) * 8) as *mut i64;

        // Copy existing elements
        if len > 0 && !old_data.is_null() {
            std::ptr::copy_nonoverlapping(old_data, new_data, len as usize);
        }
        // Append new element
        *new_data.add(len as usize) = val;

        // Fill header
        *new_header = new_len;
        *new_header.add(1) = new_cap;
        *new_header.add(2) = new_data as i64;

        new_header as i64
    }
}

/// `vec-len :: (Vec a) -> Int`
#[unsafe(export_name = "vec-len")]
pub extern "C" fn vec_len(vec_ptr: i64) -> i64 {
    unsafe { *(vec_ptr as *const i64) }
}

/// `vec-map :: ((fn [a] b), (Vec a)) -> (Vec b)`
/// Applies closure to each element, returns a new Vec.
#[unsafe(export_name = "vec-map")]
pub extern "C" fn vec_map(closure_ptr: i64, vec_ptr: i64) -> i64 {
    unsafe {
        let ptr = vec_ptr as *const i64;
        let len = *ptr;

        // Handle empty vec
        if len == 0 {
            let new_header = alloc_with_rc(24) as *mut i64;
            *new_header = 0;
            *new_header.add(1) = 0;
            *new_header.add(2) = 0;
            return new_header as i64;
        }

        let data_ptr = *ptr.add(2) as *const i64;

        // Load code_ptr from closure[0]
        let closure = closure_ptr as *const i64;
        let code_ptr = *closure;
        let call: extern "C" fn(i64, i64) -> i64 = std::mem::transmute(code_ptr as *const u8);

        // Allocate new header + data buffer
        let new_header = alloc_with_rc(24) as *mut i64;
        let new_data = alloc_with_rc((len as usize) * 8) as *mut i64;

        // Apply closure to each element
        for i in 0..len as usize {
            let elem = *data_ptr.add(i);
            *new_data.add(i) = call(closure_ptr, elem);
        }

        // Fill header
        *new_header = len;
        *new_header.add(1) = len;
        *new_header.add(2) = new_data as i64;

        new_header as i64
    }
}

/// `vec-reduce :: ((fn [b a] b), b, (Vec a)) -> b`
/// Left reduce over Vec elements with an accumulator.
#[unsafe(export_name = "vec-reduce")]
pub extern "C" fn vec_reduce(closure_ptr: i64, init: i64, vec_ptr: i64) -> i64 {
    unsafe {
        let ptr = vec_ptr as *const i64;
        let len = *ptr;

        // Handle empty vec
        if len == 0 {
            return init;
        }

        let data_ptr = *ptr.add(2) as *const i64;

        // Load code_ptr from closure[0]
        let closure = closure_ptr as *const i64;
        let code_ptr = *closure;
        let call: extern "C" fn(i64, i64, i64) -> i64 = std::mem::transmute(code_ptr as *const u8);

        // Fold over elements
        let mut acc = init;
        for i in 0..len as usize {
            let elem = *data_ptr.add(i);
            acc = call(closure_ptr, acc, elem);
        }

        acc
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_vec(elems: &[i64]) -> i64 {
        unsafe {
            let header = alloc_with_rc(24) as *mut i64;
            let len = elems.len() as i64;
            if elems.is_empty() {
                *header = 0;
                *header.add(1) = 0;
                *header.add(2) = 0;
                return header as i64;
            }
            let data = alloc_with_rc(elems.len() * 8) as *mut i64;
            for (i, &e) in elems.iter().enumerate() {
                *data.add(i) = e;
            }
            *header = len;
            *header.add(1) = len;
            *header.add(2) = data as i64;
            header as i64
        }
    }

    #[test]
    fn test_vec_len() {
        let v = make_vec(&[10, 20, 30]);
        assert_eq!(vec_len(v), 3);
    }

    #[test]
    fn test_vec_len_empty() {
        let v = make_vec(&[]);
        assert_eq!(vec_len(v), 0);
    }

    #[test]
    fn test_vec_get() {
        let v = make_vec(&[10, 20, 30]);
        assert_eq!(vec_get(v, 0), 10);
        assert_eq!(vec_get(v, 1), 20);
        assert_eq!(vec_get(v, 2), 30);
    }

    #[test]
    fn test_vec_set() {
        let v = make_vec(&[10, 20, 30]);
        let v2 = vec_set(v, 1, 99);
        // Original unchanged
        assert_eq!(vec_get(v, 1), 20);
        // New vec has mutation
        assert_eq!(vec_get(v2, 1), 99);
        assert_eq!(vec_len(v2), 3);
    }

    #[test]
    fn test_vec_push() {
        let v = make_vec(&[10, 20]);
        let v2 = vec_push(v, 30);
        // Original unchanged
        assert_eq!(vec_len(v), 2);
        // New vec has appended element
        assert_eq!(vec_len(v2), 3);
        assert_eq!(vec_get(v2, 2), 30);
    }

    #[test]
    fn test_vec_push_empty() {
        let v = make_vec(&[]);
        let v2 = vec_push(v, 42);
        assert_eq!(vec_len(v2), 1);
        assert_eq!(vec_get(v2, 0), 42);
    }

    /// Helper to make a mock closure from an extern "C" function pointer.
    /// Allocates a single-slot heap object [code_ptr].
    fn make_closure(code_ptr: *const u8) -> i64 {
        unsafe {
            let closure = alloc_with_rc(8) as *mut i64;
            *closure = code_ptr as i64;
            closure as i64
        }
    }

    extern "C" fn double_fn(_env: i64, x: i64) -> i64 {
        x * 2
    }

    extern "C" fn add_fn(_env: i64, acc: i64, elem: i64) -> i64 {
        acc + elem
    }

    #[test]
    fn test_vec_map() {
        let v = make_vec(&[1, 2, 3]);
        let closure = make_closure(double_fn as *const u8);
        let result = vec_map(closure, v);
        assert_eq!(vec_len(result), 3);
        assert_eq!(vec_get(result, 0), 2);
        assert_eq!(vec_get(result, 1), 4);
        assert_eq!(vec_get(result, 2), 6);
    }

    #[test]
    fn test_vec_map_empty() {
        let v = make_vec(&[]);
        let closure = make_closure(double_fn as *const u8);
        let result = vec_map(closure, v);
        assert_eq!(vec_len(result), 0);
    }

    #[test]
    fn test_vec_reduce() {
        let v = make_vec(&[1, 2, 3, 4]);
        let closure = make_closure(add_fn as *const u8);
        let result = vec_reduce(closure, 0, v);
        assert_eq!(result, 10);
    }

    #[test]
    fn test_vec_reduce_empty() {
        let v = make_vec(&[]);
        let closure = make_closure(add_fn as *const u8);
        let result = vec_reduce(closure, 42, v);
        assert_eq!(result, 42); // returns init
    }
}
