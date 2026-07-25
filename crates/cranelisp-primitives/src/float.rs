//! Float conversion primitives — user-callable.
//!
//! Per Decision 43 (see the crate-root `//!` and `bounded-contexts.md` §4a):
//! kebab-case JIT name `float-to-string`; registered in the synthetic
//! `primitives` module's symbol table. Wave 3b-2d.2b lifted the body from
//! the pre-D43 runtime crate (`primitives/float.rs`).

use cranelisp_intrinsics::heap_string;

/// Convert a float to its string representation.
/// The float is received as its i64 bit pattern (IEEE 754 double).
/// Returns a new HeapString (rc=1).
pub(crate) fn float_to_string(f_bits: i64) -> i64 {
    let f = f64::from_bits(f_bits as u64);
    let s = if f.fract() == 0.0 && f.is_finite() {
        // Ensure floats like 3.0 display as "3.0" not "3"
        format!("{f:.1}")
    } else {
        format!("{f}")
    };
    heap_string::alloc_string(s.as_bytes()) as i64
}

#[cfg(test)]
mod tests;
