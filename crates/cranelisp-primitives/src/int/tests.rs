use super::*;
// alloc_count/dealloc_count used via crate::alloc:: in delta assertions

// spec: appendix-a-builtins §A.3 — int-to-string converts positive integer
#[test]
fn test_int_to_string_positive() {
    let result = int_to_string(42);
    unsafe {
        assert_eq!(heap_string::read_string_as_str(result.raw_for_read()), "42");
    }
    cranelisp_intrinsics::rc::consume_shallow(result);
}

// spec: appendix-a-builtins §A.3 — int-to-string converts negative integer
#[test]
fn test_int_to_string_negative() {
    let result = int_to_string(-7);
    unsafe {
        assert_eq!(heap_string::read_string_as_str(result.raw_for_read()), "-7");
    }
    cranelisp_intrinsics::rc::consume_shallow(result);
}

// spec: appendix-a-builtins §A.3 — int-to-string converts zero
#[test]
fn test_int_to_string_zero() {
    let result = int_to_string(0);
    unsafe {
        assert_eq!(heap_string::read_string_as_str(result.raw_for_read()), "0");
    }
    cranelisp_intrinsics::rc::consume_shallow(result);
}

// spec: appendix-a-builtins §A.3 — parse-int returns Some for valid decimal string
// Decision 24: parse_int consumes its heap arg — test releases only the result.
#[test]
fn test_parse_int_valid() {
    let allocs_before = cranelisp_intrinsics::alloc::alloc_count();
    let deallocs_before = cranelisp_intrinsics::alloc::dealloc_count();
    let s = heap_string::alloc_string(b"42") as i64;
    let result = parse_int(crate::abi_facts::test_owned(s));
    let raw = result.raw_for_read();
    // Should be Some(42): heap pointer
    assert!(raw > 1024, "expected heap pointer, got {raw}");
    unsafe {
        // tag at offset 16 (after HeapHeader)
        let tag = *((raw as *const u8).add(16) as *const i64);
        assert_eq!(tag, 1, "expected tag 1 for Some");
        // value at offset 24
        let val = *((raw as *const u8).add(24) as *const i64);
        assert_eq!(val, 42);
        // Decision 24: extern consumed s — only dealloc the result.
    }
    cranelisp_intrinsics::rc::consume_shallow(result);
    // Delta-based: at least 2 allocs (string + Some), 2 deallocs (extern consumed s; test freed result).
    assert!(cranelisp_intrinsics::alloc::alloc_count() - allocs_before >= 2);
    assert!(cranelisp_intrinsics::alloc::dealloc_count() - deallocs_before >= 2);
}

// spec: appendix-a-builtins §A.3 — parse-int parses negative integer
// Decision 24: parse_int consumes its heap arg.
#[test]
fn test_parse_int_negative() {
    let s = heap_string::alloc_string(b"-123") as i64;
    let result = parse_int(crate::abi_facts::test_owned(s));
    let raw = result.raw_for_read();
    assert!(raw > 1024);
    unsafe {
        let tag = *((raw as *const u8).add(16) as *const i64);
        assert_eq!(tag, 1);
        let val = *((raw as *const u8).add(24) as *const i64);
        assert_eq!(val, -123);
    }
    cranelisp_intrinsics::rc::consume_shallow(result);
}

// spec: appendix-a-builtins §A.3 — parse-int returns None for non-numeric string
// Decision 24: parse_int consumes its heap arg — None return means no result heap alloc.
#[test]
fn test_parse_int_invalid() {
    let s = heap_string::alloc_string(b"not a number") as i64;
    let result = parse_int(crate::abi_facts::test_owned(s));
    assert_eq!(result.raw_for_read(), 0); // None
    cranelisp_intrinsics::rc::consume_shallow(result);
    // Decision 24: extern consumed s.
}

// spec: appendix-a-builtins §A.3 — parse-int trims whitespace
// Decision 24: parse_int consumes its heap arg.
#[test]
fn test_parse_int_whitespace() {
    let s = heap_string::alloc_string(b"  99  ") as i64;
    let result = parse_int(crate::abi_facts::test_owned(s));
    let raw = result.raw_for_read();
    assert!(raw > 1024);
    unsafe {
        let val = *((raw as *const u8).add(24) as *const i64);
        assert_eq!(val, 99);
    }
    cranelisp_intrinsics::rc::consume_shallow(result);
}

// spec: appendix-a-builtins §A.3 — parse-int returns None for empty string
// Decision 24: parse_int consumes its heap arg.
#[test]
fn test_parse_int_empty() {
    let s = heap_string::alloc_string(b"") as i64;
    let result = parse_int(crate::abi_facts::test_owned(s));
    assert_eq!(result.raw_for_read(), 0); // None
    cranelisp_intrinsics::rc::consume_shallow(result);
    // Decision 24: extern consumed s.
}

// spec: design/arch/AGENTS.md Decision 24 — consuming convention, extern parse_int
#[test]
fn decision24_parse_int_consumes_heap_arg() {
    let allocs_before = cranelisp_intrinsics::alloc::alloc_count();
    let deallocs_before = cranelisp_intrinsics::alloc::dealloc_count();
    let s = heap_string::alloc_string(b"7") as i64;
    let result = parse_int(crate::abi_facts::test_owned(s));
    assert!(result.raw_for_read() > 1024);
    cranelisp_intrinsics::rc::consume_shallow(result);
    // 2 allocs (string + Some); 2 deallocs (extern freed string; test freed Some).
    assert_eq!(
        cranelisp_intrinsics::alloc::alloc_count() - allocs_before,
        2
    );
    assert_eq!(
        cranelisp_intrinsics::alloc::dealloc_count() - deallocs_before,
        2
    );
}

// spec: design/arch/AGENTS.md Decision 24 — parse_int with None result still consumes arg
#[test]
fn decision24_parse_int_none_path_still_consumes_heap_arg() {
    let allocs_before = cranelisp_intrinsics::alloc::alloc_count();
    let deallocs_before = cranelisp_intrinsics::alloc::dealloc_count();
    let s = heap_string::alloc_string(b"not a number") as i64;
    let result = parse_int(crate::abi_facts::test_owned(s));
    assert_eq!(result.raw_for_read(), 0); // None
    cranelisp_intrinsics::rc::consume_shallow(result);
    // 1 alloc (string); 1 dealloc (extern freed string).
    assert_eq!(
        cranelisp_intrinsics::alloc::alloc_count() - allocs_before,
        1
    );
    assert_eq!(
        cranelisp_intrinsics::alloc::dealloc_count() - deallocs_before,
        1
    );
}

/// Reads an `Option Int` produced by this module and releases it.
fn take_option_int(result: Owned) -> Option<i64> {
    let raw = result.raw_for_read();
    let value = if raw == 0 {
        None
    } else {
        // SAFETY: a non-zero `Option Int` from `option_int` is a live Some
        // node owned by `result` until the release below.
        unsafe {
            assert_eq!(*((raw as *const u8).add(16) as *const i64), 1, "Some tag");
            Some(*((raw as *const u8).add(24) as *const i64))
        }
    };
    cranelisp_intrinsics::rc::consume_shallow(result);
    value
}

// spec: spec/12-runtime.md §12.7.3 — P-10: checked-quot returns None for a zero divisor.
#[test]
fn checked_quot_zero_divisor_is_none() {
    assert_eq!(take_option_int(checked_quot(1, 0)), None);
    assert_eq!(take_option_int(checked_quot(0, 0)), None);
    assert_eq!(take_option_int(checked_quot(i64::MIN, 0)), None);
}

// spec: spec/12-runtime.md §12.7.3 — P-10: Int.MIN / -1 is None, not a wrapped Some(Int.MIN).
#[test]
fn checked_quot_min_by_minus_one_is_none() {
    assert_eq!(take_option_int(checked_quot(i64::MIN, -1)), None);
}

// spec: spec/12-runtime.md §12.7.3 — P-10: Some quotient truncated toward zero, not floored.
#[test]
fn checked_quot_truncates_toward_zero() {
    assert_eq!(take_option_int(checked_quot(7, -2)), Some(-3));
    assert_eq!(take_option_int(checked_quot(-7, 2)), Some(-3));
    assert_eq!(take_option_int(checked_quot(-7, -2)), Some(3));
    assert_eq!(take_option_int(checked_quot(10, 2)), Some(5));
}

// spec: spec/12-runtime.md §12.7.3 — P-10 boundary: the neighbours of the overflow case are ordinary quotients.
#[test]
fn checked_quot_overflow_neighbours_are_some() {
    assert_eq!(take_option_int(checked_quot(i64::MIN, 1)), Some(i64::MIN));
    assert_eq!(
        take_option_int(checked_quot(i64::MIN + 1, -1)),
        Some(i64::MAX)
    );
    assert_eq!(take_option_int(checked_quot(i64::MAX, -1)), Some(-i64::MAX));
}

// spec: spec/12-runtime.md §12.7.3 — P-10: a Some result is one fresh node, freed by one release; None allocates nothing.
#[test]
fn checked_quot_allocation_balance() {
    let allocs_before = cranelisp_intrinsics::alloc::alloc_count();
    let deallocs_before = cranelisp_intrinsics::alloc::dealloc_count();
    assert_eq!(take_option_int(checked_quot(9, 3)), Some(3));
    assert_eq!(take_option_int(checked_quot(9, 0)), None);
    assert_eq!(
        cranelisp_intrinsics::alloc::alloc_count() - allocs_before,
        1
    );
    assert_eq!(
        cranelisp_intrinsics::alloc::dealloc_count() - deallocs_before,
        1
    );
}
