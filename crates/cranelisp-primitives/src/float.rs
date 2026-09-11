//! Float conversion primitives — user-callable.
//!
//! Per Decision 43 (see the crate-root `//!` and `bounded-contexts.md` §4a):
//! kebab-case JIT name `float-to-string`; registered in the synthetic
//! `primitives` module's symbol table. Wave 3b-2d.2b lifted the body from
//! the pre-D43 runtime crate (`primitives/float.rs`).

use cranelisp_intrinsics::handle::Owned;
use cranelisp_intrinsics::heap_string;

use crate::abi_facts::adopt_produced_value;

/// Convert a float to its string representation.
/// The float is received as its i64 bit pattern (IEEE 754 double).
/// Returns a new HeapString (rc=1).
pub(crate) fn float_to_string(f_bits: i64) -> Owned {
    let f = f64::from_bits(f_bits as u64);
    let s = if f.fract() == 0.0 && f.is_finite() {
        // Ensure floats like 3.0 display as "3.0" not "3"
        format!("{f:.1}")
    } else {
        format!("{f}")
    };
    // SAFETY: `alloc_string` returned a fully initialized fresh RC=1 String.
    unsafe { adopt_produced_value(heap_string::alloc_string(s.as_bytes()) as i64) }
}

#[cfg(test)]
mod tests;
