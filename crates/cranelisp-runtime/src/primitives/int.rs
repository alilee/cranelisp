//! Integer conversion primitives.

use crate::alloc;
use crate::string;

/// Convert an integer to its decimal string representation.
/// Returns a new HeapString (rc=1).
#[unsafe(no_mangle)]
pub extern "C" fn int_to_string(n: i64) -> i64 {
    let s = n.to_string();
    string::alloc_string(s.as_bytes()) as i64
}

/// Parse an integer from a string. Returns an Option Int as a heap ADT.
///
/// Returns:
/// - `None`: bare i64 tag 0
/// - `Some(n)`: heap-allocated `[alloc_size | rc | tag=1 | n]`
///
/// Depends on Chunk B (Option type). The runtime constructs the ADT layout
/// directly — it does not need the type system.
#[unsafe(no_mangle)]
pub extern "C" fn parse_int(s: i64) -> i64 {
    // SAFETY: s is a valid HeapString base pointer.
    let str_val = unsafe { string::read_string_as_str(s) };

    match str_val.trim().parse::<i64>() {
        Ok(n) => {
            // Some(n): allocate [tag=1 | n] as payload (16 bytes)
            let base = alloc::alloc_with_rc(16); // tag + 1 field
            // SAFETY: base is valid, has 16 bytes of payload.
            unsafe {
                // tag at HeapHeader::SIZE (offset 16)
                *(base.add(cranelisp_types::HeapHeader::SIZE) as *mut i64) = 1;
                // value at HeapHeader::SIZE + 8 (offset 24)
                *(base.add(cranelisp_types::HeapHeader::SIZE + 8) as *mut i64) = n;
            }
            base as i64
        }
        Err(_) => {
            // None: bare tag 0
            0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    // alloc_count/dealloc_count used via crate::alloc:: in delta assertions

    // spec: appendix-a-builtins §A.3 — int-to-string converts positive integer
    #[test]
    fn test_int_to_string_positive() {
        let result = int_to_string(42);
        unsafe {
            assert_eq!(string::read_string_as_str(result), "42");
            alloc::dealloc(result as *mut u8);
        }
    }

    // spec: appendix-a-builtins §A.3 — int-to-string converts negative integer
    #[test]
    fn test_int_to_string_negative() {
        let result = int_to_string(-7);
        unsafe {
            assert_eq!(string::read_string_as_str(result), "-7");
            alloc::dealloc(result as *mut u8);
        }
    }

    // spec: appendix-a-builtins §A.3 — int-to-string converts zero
    #[test]
    fn test_int_to_string_zero() {
        let result = int_to_string(0);
        unsafe {
            assert_eq!(string::read_string_as_str(result), "0");
            alloc::dealloc(result as *mut u8);
        }
    }

    // spec: appendix-a-builtins §A.3 — parse-int returns Some for valid decimal string
    #[test]
    fn test_parse_int_valid() {
        let allocs_before = crate::alloc::alloc_count();
        let deallocs_before = crate::alloc::dealloc_count();
        let s = string::alloc_string(b"42") as i64;
        let result = parse_int(s);
        // Should be Some(42): heap pointer
        assert!(result > 1024, "expected heap pointer, got {result}");
        unsafe {
            // tag at offset 16 (after HeapHeader)
            let tag = *((result as *const u8).add(16) as *const i64);
            assert_eq!(tag, 1, "expected tag 1 for Some");
            // value at offset 24
            let val = *((result as *const u8).add(24) as *const i64);
            assert_eq!(val, 42);
            alloc::dealloc(s as *mut u8);
            alloc::dealloc(result as *mut u8);
        }
        // Delta-based: at least 2 allocs (string + Some), 2 deallocs.
        assert!(crate::alloc::alloc_count() - allocs_before >= 2);
        assert!(crate::alloc::dealloc_count() - deallocs_before >= 2);
    }

    // spec: appendix-a-builtins §A.3 — parse-int parses negative integer
    #[test]
    fn test_parse_int_negative() {
        let s = string::alloc_string(b"-123") as i64;
        let result = parse_int(s);
        assert!(result > 1024);
        unsafe {
            let tag = *((result as *const u8).add(16) as *const i64);
            assert_eq!(tag, 1);
            let val = *((result as *const u8).add(24) as *const i64);
            assert_eq!(val, -123);
            alloc::dealloc(s as *mut u8);
            alloc::dealloc(result as *mut u8);
        }
    }

    // spec: appendix-a-builtins §A.3 — parse-int returns None for non-numeric string
    #[test]
    fn test_parse_int_invalid() {
        let s = string::alloc_string(b"not a number") as i64;
        let result = parse_int(s);
        assert_eq!(result, 0); // None
        unsafe { alloc::dealloc(s as *mut u8) };
    }

    // spec: appendix-a-builtins §A.3 — parse-int trims whitespace
    #[test]
    fn test_parse_int_whitespace() {
        let s = string::alloc_string(b"  99  ") as i64;
        let result = parse_int(s);
        assert!(result > 1024);
        unsafe {
            let val = *((result as *const u8).add(24) as *const i64);
            assert_eq!(val, 99);
            alloc::dealloc(s as *mut u8);
            alloc::dealloc(result as *mut u8);
        }
    }

    // spec: appendix-a-builtins §A.3 — parse-int returns None for empty string
    #[test]
    fn test_parse_int_empty() {
        let s = string::alloc_string(b"") as i64;
        let result = parse_int(s);
        assert_eq!(result, 0); // None
        unsafe { alloc::dealloc(s as *mut u8) };
    }
}
