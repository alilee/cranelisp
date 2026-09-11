//! Boolean conversion primitives — user-callable.
//!
//! Per Decision 43 (see the crate-root `//!` and `bounded-contexts.md` §4a):
//! kebab-case JIT name `bool-to-string`; registered in the synthetic
//! `primitives` module's symbol table. Wave 3b-2d.2b lifted the body from
//! the pre-D43 runtime crate (`primitives/bool.rs`).

use cranelisp_intrinsics::handle::Owned;
use cranelisp_intrinsics::heap_string;

use crate::abi_facts::adopt_produced_value;

/// Convert a Bool (0 or 1) to "true" or "false".
/// Returns a new HeapString (rc=1).
pub(crate) fn bool_to_string(b: i64) -> Owned {
    let s = if b != 0 { "true" } else { "false" };
    // SAFETY: `alloc_string` returned a fully initialized fresh RC=1 String.
    unsafe { adopt_produced_value(heap_string::alloc_string(s.as_bytes()) as i64) }
}

#[cfg(test)]
mod tests {
    use super::*;

    // spec: appendix-a-builtins §A.3 — bool-to-string converts true
    #[test]
    fn test_bool_to_string_true() {
        let result = bool_to_string(1);
        unsafe {
            assert_eq!(
                heap_string::read_string_as_str(result.raw_for_read()),
                "true"
            );
        }
        cranelisp_intrinsics::rc::consume_shallow(result);
    }

    // spec: appendix-a-builtins §A.3 — bool-to-string converts false
    #[test]
    fn test_bool_to_string_false() {
        let result = bool_to_string(0);
        unsafe {
            assert_eq!(
                heap_string::read_string_as_str(result.raw_for_read()),
                "false"
            );
        }
        cranelisp_intrinsics::rc::consume_shallow(result);
    }

    // spec: 12-runtime §12.1.1 — nonzero i64 value is truthy (Bool representation)
    #[test]
    fn test_bool_to_string_nonzero_is_true() {
        let result = bool_to_string(42);
        unsafe {
            assert_eq!(
                heap_string::read_string_as_str(result.raw_for_read()),
                "true"
            );
        }
        cranelisp_intrinsics::rc::consume_shallow(result);
    }
}
