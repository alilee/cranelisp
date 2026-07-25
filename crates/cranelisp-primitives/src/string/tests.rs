use super::*;

// spec: appendix-a-builtins §A.3 — str-concat concatenates two strings
// Decision 24: str_concat consumes both heap args — only dealloc the result.
#[test]
fn test_str_concat() {
    let a = alloc_string(b"hello, ") as i64;
    let b = alloc_string(b"world!") as i64;
    let result = str_concat(a, b);
    unsafe {
        assert_eq!(read_str(result as *const u8), "hello, world!");
        alloc::dealloc(result as *mut u8);
    }
}

// spec: appendix-a-builtins §A.3 — str-eq returns 1 for equal strings
#[test]
fn test_str_eq_equal() {
    let a = alloc_string(b"same") as i64;
    let b = alloc_string(b"same") as i64;
    assert_eq!(str_eq(a, b), 1);
}

// spec: appendix-a-builtins §A.3 — str-eq returns 0 for different strings
#[test]
fn test_str_eq_not_equal() {
    let a = alloc_string(b"hello") as i64;
    let b = alloc_string(b"world") as i64;
    assert_eq!(str_eq(a, b), 0);
}

// spec: 07-traits §7.7.2 — neq-string returns 0 (false) for equal strings
// (logical negation of str-eq; the `Eq.!=` String dispatch target).
#[test]
fn test_neq_string_equal() {
    let a = alloc_string(b"same") as i64;
    let b = alloc_string(b"same") as i64;
    assert_eq!(neq_string(a, b), 0);
}

// spec: 07-traits §7.7.2 — neq-string returns 1 (true) for different strings.
#[test]
fn test_neq_string_not_equal() {
    let a = alloc_string(b"a") as i64;
    let b = alloc_string(b"b") as i64;
    assert_eq!(neq_string(a, b), 1);
}

// spec: 12-runtime §12.1.2 — string length in bytes
#[test]
fn test_str_len() {
    let s = alloc_string(b"hello") as i64;
    assert_eq!(str_len(s), 5);
}

// spec: appendix-a-builtins §A.3 — substring extracts a slice
#[test]
fn test_str_substring() {
    let s = alloc_string(b"hello world") as i64;
    let result = str_substring(s, 6, 11);
    unsafe {
        assert_eq!(read_str(result as *const u8), "world");
        alloc::dealloc(result as *mut u8);
    }
}

// spec: appendix-a-builtins §A.3 — trim removes whitespace
#[test]
fn test_str_trim() {
    let s = alloc_string(b"  hi  ") as i64;
    let result = str_trim(s);
    unsafe {
        assert_eq!(read_str(result as *const u8), "hi");
        alloc::dealloc(result as *mut u8);
    }
}

// spec: appendix-a-builtins §A.3 — starts-with? returns 1 on prefix match
#[test]
fn test_str_starts_with() {
    let s = alloc_string(b"hello world") as i64;
    let prefix = alloc_string(b"hello") as i64;
    assert_eq!(str_starts_with(s, prefix), 1);
}

// spec: appendix-a-builtins §A.3 — replace replaces all occurrences
#[test]
fn test_str_replace() {
    let s = alloc_string(b"aaabbb") as i64;
    let from = alloc_string(b"a") as i64;
    let to = alloc_string(b"X") as i64;
    let result = str_replace(s, from, to);
    unsafe {
        assert_eq!(read_str(result as *const u8), "XXXbbb");
        alloc::dealloc(result as *mut u8);
    }
}

// spec: appendix-a-builtins §A.3 — split returns every delimited String.
#[test]
fn split_constructs_owned_string_elements() {
    let source = alloc_string(b"alpha,,omega") as i64;
    let separator = alloc_string(b",") as i64;
    let result = str_split(source, separator);

    // SAFETY: `result` is the live Vec-of-String returned by `str_split` and
    // remains immutable for the callback.
    let actual = unsafe {
        cranelisp_intrinsics::vec_runtime::with_vec_strings(result, |elements| {
            elements
                .iter()
                .map(|element| read_str(*element as *const u8).to_owned())
                .collect::<Vec<_>>()
        })
    };
    assert_eq!(actual, ["alpha", "", "omega"]);

    drop_glue::consume_vec_of_string(result);
}

// spec: appendix-a-builtins §A.3 — splitting an empty String is a one-element
// Vec containing the empty String, matching Rust/Cranelisp String semantics.
#[test]
fn split_empty_string_returns_one_owned_empty_element() {
    let source = alloc_string(b"") as i64;
    let separator = alloc_string(b",") as i64;
    let result = str_split(source, separator);

    // SAFETY: `result` is live and immutable for the callback.
    let actual = unsafe {
        cranelisp_intrinsics::vec_runtime::with_vec_strings(result, |elements| {
            elements
                .iter()
                .map(|element| read_str(*element as *const u8).to_owned())
                .collect::<Vec<_>>()
        })
    };
    assert_eq!(actual, [""]);

    drop_glue::consume_vec_of_string(result);
}

// spec: appendix-a-builtins §A.3 — join borrows Vec elements while producing
// a fresh String, then consumes the input Vec and its owned elements.
#[test]
fn split_join_roundtrip_preserves_delimiter_and_lifetimes() {
    let source = alloc_string(b"left::middle::right") as i64;
    let split_separator = alloc_string(b"::") as i64;
    let parts = str_split(source, split_separator);
    // SAFETY: `parts` is live and immutable for the callback. Copying these
    // words records allocation identities only; it does not create ownership.
    let element_allocations =
        unsafe { cranelisp_intrinsics::vec_runtime::with_vec_strings(parts, <[i64]>::to_vec) };
    assert!(alloc::is_live(parts as usize));
    assert!(
        element_allocations
            .iter()
            .all(|element| alloc::is_live(*element as usize))
    );
    let join_separator = alloc_string(b"::") as i64;

    let result = str_join(join_separator, parts);
    assert!(alloc::is_live(result as usize));
    assert!(!alloc::is_live(parts as usize));
    assert!(
        element_allocations
            .iter()
            .all(|element| !alloc::is_live(*element as usize))
    );
    // SAFETY: `result` is the fresh live HeapString returned by `str_join`.
    unsafe {
        assert_eq!(read_str(result as *const u8), "left::middle::right");
    }
    rc::consume_shallow(result);
    assert!(!alloc::is_live(result as usize));
}

// spec: appendix-a-builtins §A.3 — joining an empty Vec returns an empty
// String and consumes the Vec without touching nonexistent elements.
#[test]
fn join_empty_vec_returns_empty_string() {
    // SAFETY: the empty input transfers no HeapString owned references.
    let empty = unsafe { cranelisp_intrinsics::vec_runtime::vec_strings_from_owned(Vec::new()) };
    let separator = alloc_string(b",") as i64;

    let result = str_join(separator, empty);
    // SAFETY: `result` is the fresh live HeapString returned by `str_join`.
    unsafe {
        assert_eq!(read_str(result as *const u8), "");
    }
    rc::consume_shallow(result);
}

#[test]
fn split_and_join_do_not_encode_vec_layout() {
    let source = include_str!("../string.rs");
    assert!(!source.contains("vec_runtime::{DATA_PTR_OFFSET"));
    assert!(!source.contains(".add(DATA_PTR_OFFSET)"));
    assert!(!source.contains(".add(LEN_OFFSET)"));
    assert!(!source.contains("vec_runtime::vec_new"));
    assert!(source.contains("vec_strings_from_owned"));
    assert!(source.contains("with_vec_strings"));
}

// spec: appendix-a-builtins §A.3 — to-upper / to-lower
#[test]
fn test_str_case() {
    let s = alloc_string(b"Hello") as i64;
    let upper = str_to_upper(s);
    unsafe {
        assert_eq!(read_str(upper as *const u8), "HELLO");
        alloc::dealloc(upper as *mut u8);
    }
    let s = alloc_string(b"Hello") as i64;
    let lower = str_to_lower(s);
    unsafe {
        assert_eq!(read_str(lower as *const u8), "hello");
        alloc::dealloc(lower as *mut u8);
    }
}
