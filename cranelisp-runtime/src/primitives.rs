//! Primitive functions: pure, user-callable, implemented in Rust for bootstrapping.
//! These could eventually be written in cranelisp once sufficient string primitives exist.

pub mod bool;
pub mod float;
pub mod int;
pub mod string;
pub mod vec;

pub use bool::*;
pub use float::*;
pub use int::*;
pub use string::*;
pub use vec::*;

/// Allocate a heap string with the given bytes. Layout: [i64 len][u8 bytes...]
/// The rc header at `ptr - 8` is set to 1 by alloc_with_rc.
pub fn alloc_string(bytes: &[u8]) -> i64 {
    let size = 8 + bytes.len(); // len field + bytes
    let ptr = crate::intrinsics::alloc_with_rc(size);
    unsafe {
        *(ptr as *mut i64) = bytes.len() as i64;
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), ptr.add(8), bytes.len());
        ptr as i64
    }
}
