//! Boolean conversion primitives.

use crate::string;

/// Convert a Bool (0 or 1) to "true" or "false".
/// Returns a new HeapString (rc=1).
#[unsafe(no_mangle)]
pub extern "C" fn bool_to_string(b: i64) -> i64 {
    let s = if b != 0 { "true" } else { "false" };
    string::alloc_string(s.as_bytes()) as i64
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::alloc;

    #[test]
    fn test_bool_to_string_true() {
        let result = bool_to_string(1);
        unsafe {
            assert_eq!(string::read_string_as_str(result), "true");
            alloc::dealloc(result as *mut u8);
        }
    }

    #[test]
    fn test_bool_to_string_false() {
        let result = bool_to_string(0);
        unsafe {
            assert_eq!(string::read_string_as_str(result), "false");
            alloc::dealloc(result as *mut u8);
        }
    }

    #[test]
    fn test_bool_to_string_nonzero_is_true() {
        let result = bool_to_string(42);
        unsafe {
            assert_eq!(string::read_string_as_str(result), "true");
            alloc::dealloc(result as *mut u8);
        }
    }
}
