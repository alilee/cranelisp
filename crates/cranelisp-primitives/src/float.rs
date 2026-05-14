//! Float conversion primitives — user-callable.
//!
//! Per Decision 43 + `design/arch/facades/primitives.md`: kebab-case JIT
//! name `float-to-string`; registered in the synthetic `primitives` module's
//! symbol table. Wave 3b-2d.2b lifted the body from
//! `cranelisp-runtime/src/primitives/float.rs`.

use cranelisp_intrinsics::string;

/// Convert a float to its string representation.
/// The float is received as its i64 bit pattern (IEEE 754 double).
/// Returns a new HeapString (rc=1).
#[unsafe(export_name = "float-to-string")]
pub extern "C" fn float_to_string(f_bits: i64) -> i64 {
    let f = f64::from_bits(f_bits as u64);
    let s = if f.fract() == 0.0 && f.is_finite() {
        // Ensure floats like 3.0 display as "3.0" not "3"
        format!("{f:.1}")
    } else {
        format!("{f}")
    };
    string::alloc_string(s.as_bytes()) as i64
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_intrinsics::alloc;

    fn float_bits(f: f64) -> i64 {
        f.to_bits() as i64
    }

    // spec: appendix-a-builtins §A.3 — float-to-string converts whole number float
    #[test]
    fn test_float_to_string_integer() {
        let result = float_to_string(float_bits(3.0));
        unsafe {
            assert_eq!(string::read_string_as_str(result), "3.0");
            alloc::dealloc(result as *mut u8);
        }
    }

    // spec: appendix-a-builtins §A.3 — float-to-string converts fractional float
    #[test]
    fn test_float_to_string_fractional() {
        let result = float_to_string(float_bits(3.14));
        unsafe {
            assert_eq!(string::read_string_as_str(result), "3.14");
            alloc::dealloc(result as *mut u8);
        }
    }

    // spec: appendix-a-builtins §A.3 — float-to-string converts negative float
    #[test]
    fn test_float_to_string_negative() {
        let result = float_to_string(float_bits(-2.5));
        unsafe {
            assert_eq!(string::read_string_as_str(result), "-2.5");
            alloc::dealloc(result as *mut u8);
        }
    }

    // spec: appendix-a-builtins §A.3 — float-to-string converts zero
    #[test]
    fn test_float_to_string_zero() {
        let result = float_to_string(float_bits(0.0));
        unsafe {
            assert_eq!(string::read_string_as_str(result), "0.0");
            alloc::dealloc(result as *mut u8);
        }
    }
}
