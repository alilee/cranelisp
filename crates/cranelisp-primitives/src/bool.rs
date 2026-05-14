//! Boolean conversion primitives — user-callable.
//!
//! Per Decision 43 + `design/arch/facades/primitives.md`: kebab-case JIT
//! name `bool-to-string`; registered in the synthetic `primitives` module's
//! symbol table. Wave 3b-2d.2b lifted the body from
//! `cranelisp-runtime/src/primitives/bool.rs`.

use cranelisp_intrinsics::string;

/// Convert a Bool (0 or 1) to "true" or "false".
/// Returns a new HeapString (rc=1).
#[unsafe(export_name = "bool-to-string")]
pub extern "C" fn bool_to_string(b: i64) -> i64 {
    let s = if b != 0 { "true" } else { "false" };
    string::alloc_string(s.as_bytes()) as i64
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_intrinsics::alloc;

    // spec: appendix-a-builtins §A.3 — bool-to-string converts true
    #[test]
    fn test_bool_to_string_true() {
        let result = bool_to_string(1);
        unsafe {
            assert_eq!(string::read_string_as_str(result), "true");
            alloc::dealloc(result as *mut u8);
        }
    }

    // spec: appendix-a-builtins §A.3 — bool-to-string converts false
    #[test]
    fn test_bool_to_string_false() {
        let result = bool_to_string(0);
        unsafe {
            assert_eq!(string::read_string_as_str(result), "false");
            alloc::dealloc(result as *mut u8);
        }
    }

    // spec: 12-runtime §12.1.1 — nonzero i64 value is truthy (Bool representation)
    #[test]
    fn test_bool_to_string_nonzero_is_true() {
        let result = bool_to_string(42);
        unsafe {
            assert_eq!(string::read_string_as_str(result), "true");
            alloc::dealloc(result as *mut u8);
        }
    }
}
