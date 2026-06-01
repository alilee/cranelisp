//! Integer conversion primitives — user-callable.
//!
//! Per Decision 43 (see the crate-root `//!` and `bounded-contexts.md` §4a):
//! kebab-case JIT names (`int-to-string`, `parse-int`), registered in the
//! synthetic `primitives` module's symbol table; user-addressable.
//!
//! Wave 3b-2d.2b lifted the bodies from
//! `cranelisp-runtime/src/primitives/int.rs` into this crate. The
//! `cranelisp_op_*` operator-as-value wrappers that previously cohabited
//! that file are backend-emitted-call targets (not user-callable; backend
//! emits direct calls when an operator is referenced as a first-class
//! value) and migrated to `cranelisp-intrinsics::ops` instead.
//! `cranelisp-runtime` keeps thin re-export shims for both halves until
//! that crate retires per FIXME 0150 Phase 5.

use cranelisp_intrinsics::alloc;
use cranelisp_intrinsics::rc;
use cranelisp_intrinsics::heap_string;

/// Convert an integer to its decimal string representation.
/// Returns a new HeapString (rc=1).
#[unsafe(export_name = "int-to-string")]
pub(crate) extern "C" fn int_to_string(n: i64) -> i64 {
    let s = n.to_string();
    heap_string::alloc_string(s.as_bytes()) as i64
}

/// Parse an integer from a string. Returns an Option Int as a heap ADT.
///
/// Returns:
/// - `None`: bare i64 tag 0
/// - `Some(n)`: heap-allocated `[alloc_size | rc | tag=1 | n]`
///
/// Depends on Chunk B (Option type). The runtime constructs the ADT layout
/// directly — it does not need the type system.
/// Parse an integer from a string. Returns an Option Int as a heap ADT.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — dec the heap arg.
#[unsafe(export_name = "parse-int")]
pub(crate) extern "C" fn parse_int(s: i64) -> i64 {
    // SAFETY: s is a valid HeapString base pointer.
    let str_val = unsafe { heap_string::read_string_as_str(s) };

    let result = match str_val.trim().parse::<i64>() {
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
    };
    // Consume the input string reference (Decision 24).
    rc::consume_shallow(s);
    result
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
            assert_eq!(heap_string::read_string_as_str(result), "42");
            alloc::dealloc(result as *mut u8);
        }
    }

    // spec: appendix-a-builtins §A.3 — int-to-string converts negative integer
    #[test]
    fn test_int_to_string_negative() {
        let result = int_to_string(-7);
        unsafe {
            assert_eq!(heap_string::read_string_as_str(result), "-7");
            alloc::dealloc(result as *mut u8);
        }
    }

    // spec: appendix-a-builtins §A.3 — int-to-string converts zero
    #[test]
    fn test_int_to_string_zero() {
        let result = int_to_string(0);
        unsafe {
            assert_eq!(heap_string::read_string_as_str(result), "0");
            alloc::dealloc(result as *mut u8);
        }
    }

    // spec: appendix-a-builtins §A.3 — parse-int returns Some for valid decimal string
    // Decision 24: parse_int consumes its heap arg — test releases only the result.
    #[test]
    fn test_parse_int_valid() {
        let allocs_before = cranelisp_intrinsics::alloc::alloc_count();
        let deallocs_before = cranelisp_intrinsics::alloc::dealloc_count();
        let s = heap_string::alloc_string(b"42") as i64;
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
            // Decision 24: extern consumed s — only dealloc the result.
            alloc::dealloc(result as *mut u8);
        }
        // Delta-based: at least 2 allocs (string + Some), 2 deallocs (extern consumed s; test freed result).
        assert!(cranelisp_intrinsics::alloc::alloc_count() - allocs_before >= 2);
        assert!(cranelisp_intrinsics::alloc::dealloc_count() - deallocs_before >= 2);
    }

    // spec: appendix-a-builtins §A.3 — parse-int parses negative integer
    // Decision 24: parse_int consumes its heap arg.
    #[test]
    fn test_parse_int_negative() {
        let s = heap_string::alloc_string(b"-123") as i64;
        let result = parse_int(s);
        assert!(result > 1024);
        unsafe {
            let tag = *((result as *const u8).add(16) as *const i64);
            assert_eq!(tag, 1);
            let val = *((result as *const u8).add(24) as *const i64);
            assert_eq!(val, -123);
            alloc::dealloc(result as *mut u8);
        }
    }

    // spec: appendix-a-builtins §A.3 — parse-int returns None for non-numeric string
    // Decision 24: parse_int consumes its heap arg — None return means no result heap alloc.
    #[test]
    fn test_parse_int_invalid() {
        let s = heap_string::alloc_string(b"not a number") as i64;
        let result = parse_int(s);
        assert_eq!(result, 0); // None
        // Decision 24: extern consumed s.
    }

    // spec: appendix-a-builtins §A.3 — parse-int trims whitespace
    // Decision 24: parse_int consumes its heap arg.
    #[test]
    fn test_parse_int_whitespace() {
        let s = heap_string::alloc_string(b"  99  ") as i64;
        let result = parse_int(s);
        assert!(result > 1024);
        unsafe {
            let val = *((result as *const u8).add(24) as *const i64);
            assert_eq!(val, 99);
            alloc::dealloc(result as *mut u8);
        }
    }

    // spec: appendix-a-builtins §A.3 — parse-int returns None for empty string
    // Decision 24: parse_int consumes its heap arg.
    #[test]
    fn test_parse_int_empty() {
        let s = heap_string::alloc_string(b"") as i64;
        let result = parse_int(s);
        assert_eq!(result, 0); // None
        // Decision 24: extern consumed s.
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consuming convention, extern parse_int
    #[test]
    fn decision24_parse_int_consumes_heap_arg() {
        let allocs_before = cranelisp_intrinsics::alloc::alloc_count();
        let deallocs_before = cranelisp_intrinsics::alloc::dealloc_count();
        let s = heap_string::alloc_string(b"7") as i64;
        let result = parse_int(s);
        assert!(result > 1024);
        unsafe { alloc::dealloc(result as *mut u8) };
        // 2 allocs (string + Some); 2 deallocs (extern freed string; test freed Some).
        assert_eq!(cranelisp_intrinsics::alloc::alloc_count() - allocs_before, 2);
        assert_eq!(cranelisp_intrinsics::alloc::dealloc_count() - deallocs_before, 2);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — parse_int with None result still consumes arg
    #[test]
    fn decision24_parse_int_none_path_still_consumes_heap_arg() {
        let allocs_before = cranelisp_intrinsics::alloc::alloc_count();
        let deallocs_before = cranelisp_intrinsics::alloc::dealloc_count();
        let s = heap_string::alloc_string(b"not a number") as i64;
        let result = parse_int(s);
        assert_eq!(result, 0); // None
        // 1 alloc (string); 1 dealloc (extern freed string).
        assert_eq!(cranelisp_intrinsics::alloc::alloc_count() - allocs_before, 1);
        assert_eq!(cranelisp_intrinsics::alloc::dealloc_count() - deallocs_before, 1);
    }
}
