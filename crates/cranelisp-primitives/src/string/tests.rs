use super::*;

// spec: appendix-a-builtins §A.3 — str-concat concatenates two strings
// Decision 24: str_concat consumes both heap args — only dealloc the result.
#[test]
fn test_str_concat() {
    let a = alloc_string(b"hello, ") as i64;
    let b = alloc_string(b"world!") as i64;
    let result = str_concat(
        crate::abi_facts::test_owned(a),
        crate::abi_facts::test_owned(b),
    );
    unsafe {
        assert_eq!(read_str(result.as_borrowed()), "hello, world!");
    }
    rc::consume_shallow(result);
}

// spec: appendix-a-builtins §A.3 — str-eq returns 1 for equal strings
#[test]
fn test_str_eq_equal() {
    let a = alloc_string(b"same") as i64;
    let b = alloc_string(b"same") as i64;
    assert_eq!(
        str_eq(
            crate::abi_facts::test_owned(a),
            crate::abi_facts::test_owned(b)
        ),
        1
    );
}

// spec: appendix-a-builtins §A.3 — str-eq returns 0 for different strings
#[test]
fn test_str_eq_not_equal() {
    let a = alloc_string(b"hello") as i64;
    let b = alloc_string(b"world") as i64;
    assert_eq!(
        str_eq(
            crate::abi_facts::test_owned(a),
            crate::abi_facts::test_owned(b)
        ),
        0
    );
}

// spec: 07-traits §7.7.2 — neq-string returns 0 (false) for equal strings
// (logical negation of str-eq; the `Eq.!=` String dispatch target).
#[test]
fn test_neq_string_equal() {
    let a = alloc_string(b"same") as i64;
    let b = alloc_string(b"same") as i64;
    assert_eq!(
        neq_string(
            crate::abi_facts::test_owned(a),
            crate::abi_facts::test_owned(b)
        ),
        0
    );
}

// spec: 07-traits §7.7.2 — neq-string returns 1 (true) for different strings.
#[test]
fn test_neq_string_not_equal() {
    let a = alloc_string(b"a") as i64;
    let b = alloc_string(b"b") as i64;
    assert_eq!(
        neq_string(
            crate::abi_facts::test_owned(a),
            crate::abi_facts::test_owned(b)
        ),
        1
    );
}

// spec: 12-runtime §12.1.2 — string length in bytes
#[test]
fn test_str_len() {
    let s = alloc_string(b"hello") as i64;
    assert_eq!(str_len(crate::abi_facts::test_owned(s)), 5);
}

// spec: design/primitives/primitives.md §2.4 — string-identity moves its
// owner into its result: the same allocation, neither minted nor discharged,
// so the result's one discharge frees it.
#[test]
fn string_identity_moves_its_owner_into_the_result() {
    let raw = alloc_string(b"identity") as i64;
    let result = string_identity(crate::abi_facts::test_owned(raw));
    assert_eq!(result.raw_for_read(), raw);

    rc::consume_shallow(result);
    assert!(!alloc::is_live(raw as usize));
}

// spec: appendix-a-builtins §A.3 — substring extracts a slice
#[test]
fn test_str_substring() {
    let s = alloc_string(b"hello world") as i64;
    let result = str_substring(crate::abi_facts::test_owned(s), 6, 11);
    unsafe {
        assert_eq!(read_str(result.as_borrowed()), "world");
    }
    rc::consume_shallow(result);
}

// spec: appendix-a-builtins §A.3 — trim removes whitespace
#[test]
fn test_str_trim() {
    let s = alloc_string(b"  hi  ") as i64;
    let result = str_trim(crate::abi_facts::test_owned(s));
    unsafe {
        assert_eq!(read_str(result.as_borrowed()), "hi");
    }
    rc::consume_shallow(result);
}

// spec: appendix-a-builtins §A.3 — starts-with? returns 1 on prefix match
#[test]
fn test_str_starts_with() {
    let s = alloc_string(b"hello world") as i64;
    let prefix = alloc_string(b"hello") as i64;
    assert_eq!(
        str_starts_with(
            crate::abi_facts::test_owned(s),
            crate::abi_facts::test_owned(prefix)
        ),
        1
    );
}

// spec: appendix-a-builtins §A.3 — replace replaces all occurrences
#[test]
fn test_str_replace() {
    let s = alloc_string(b"aaabbb") as i64;
    let from = alloc_string(b"a") as i64;
    let to = alloc_string(b"X") as i64;
    let result = str_replace(
        crate::abi_facts::test_owned(s),
        crate::abi_facts::test_owned(from),
        crate::abi_facts::test_owned(to),
    );
    unsafe {
        assert_eq!(read_str(result.as_borrowed()), "XXXbbb");
    }
    rc::consume_shallow(result);
}

// spec: appendix-a-builtins §A.3 — split returns every delimited String.
#[test]
fn split_constructs_owned_string_elements() {
    let source = alloc_string(b"alpha,,omega") as i64;
    let separator = alloc_string(b",") as i64;
    let result = str_split(
        crate::abi_facts::test_owned(source),
        crate::abi_facts::test_owned(separator),
    );

    // SAFETY: `result` is the live Vec-of-String returned by `str_split` and
    // remains immutable for the callback.
    let actual = unsafe {
        cranelisp_intrinsics::vec_runtime::with_vec_strings(result.raw_for_read(), |elements| {
            elements
                .iter()
                .map(|element| read_scoped_vec_string(*element).to_owned())
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
    let result = str_split(
        crate::abi_facts::test_owned(source),
        crate::abi_facts::test_owned(separator),
    );

    // SAFETY: `result` is live and immutable for the callback.
    let actual = unsafe {
        cranelisp_intrinsics::vec_runtime::with_vec_strings(result.raw_for_read(), |elements| {
            elements
                .iter()
                .map(|element| read_scoped_vec_string(*element).to_owned())
                .collect::<Vec<_>>()
        })
    };
    assert_eq!(actual, [""]);

    drop_glue::consume_vec_of_string(result);
}

// spec: design/primitives/primitives.md §2.4 — the private
// caller prepares raw Vec capacity before transferring fresh children to the
// existing guarded receiver; empty and nonempty handoffs both balance.
#[test]
fn typed_vec_handoff_transfers_children_once_after_receiver_readiness() {
    let allocs_before = alloc::alloc_count();
    let deallocs_before = alloc::dealloc_count();

    let empty = vec_strings_from_owned_handles(Vec::new());
    unsafe {
        cranelisp_intrinsics::vec_runtime::with_vec_strings(empty.raw_for_read(), |elements| {
            assert!(elements.is_empty());
        });
    }
    drop_glue::consume_vec_of_string(empty);

    let first = alloc_string(b"first") as i64;
    let second = alloc_string(b"second") as i64;
    let vector = vec_strings_from_owned_handles(vec![
        crate::abi_facts::test_owned(first),
        crate::abi_facts::test_owned(second),
    ]);
    assert!(alloc::is_live(first as usize));
    assert!(alloc::is_live(second as usize));
    unsafe {
        cranelisp_intrinsics::vec_runtime::with_vec_strings(vector.raw_for_read(), |elements| {
            assert_eq!(elements, [first, second])
        });
    }

    drop_glue::consume_vec_of_string(vector);
    assert!(!alloc::is_live(first as usize));
    assert!(!alloc::is_live(second as usize));
    assert_eq!(
        alloc::alloc_count() - allocs_before,
        alloc::dealloc_count() - deallocs_before,
        "empty and nonempty typed Vec handoffs must discharge every allocation"
    );
}

// spec: appendix-a-builtins §A.3 — join borrows Vec elements while producing
// a fresh String, then consumes the input Vec and its owned elements.
#[test]
fn split_join_roundtrip_preserves_delimiter_and_lifetimes() {
    let source = alloc_string(b"left::middle::right") as i64;
    let split_separator = alloc_string(b"::") as i64;
    let parts = str_split(
        crate::abi_facts::test_owned(source),
        crate::abi_facts::test_owned(split_separator),
    );
    let parts_raw = parts.raw_for_read();
    // SAFETY: `parts` is live and immutable for the callback. Copying these
    // words records allocation identities only; it does not create ownership.
    let element_allocations =
        unsafe { cranelisp_intrinsics::vec_runtime::with_vec_strings(parts_raw, <[i64]>::to_vec) };
    assert!(alloc::is_live(parts_raw as usize));
    assert!(
        element_allocations
            .iter()
            .all(|element| alloc::is_live(*element as usize))
    );
    let join_separator = alloc_string(b"::") as i64;

    let result = str_join(crate::abi_facts::test_owned(join_separator), parts);
    let result_raw = result.raw_for_read();
    assert!(alloc::is_live(result_raw as usize));
    assert!(!alloc::is_live(parts_raw as usize));
    assert!(
        element_allocations
            .iter()
            .all(|element| !alloc::is_live(*element as usize))
    );
    // SAFETY: `result` is the fresh live HeapString returned by `str_join`.
    unsafe {
        assert_eq!(read_str(result.as_borrowed()), "left::middle::right");
    }
    rc::consume_shallow(result);
    assert!(!alloc::is_live(result_raw as usize));
}

// spec: appendix-a-builtins §A.3 — joining an empty Vec returns an empty
// String and consumes the Vec without touching nonexistent elements.
#[test]
fn join_empty_vec_returns_empty_string() {
    // SAFETY: the empty input transfers no HeapString owned references.
    let empty = unsafe { cranelisp_intrinsics::vec_runtime::vec_strings_from_owned(Vec::new()) };
    let separator = alloc_string(b",") as i64;

    let result = str_join(
        crate::abi_facts::test_owned(separator),
        crate::abi_facts::test_owned(empty),
    );
    // SAFETY: `result` is the fresh live HeapString returned by `str_join`.
    unsafe {
        assert_eq!(read_str(result.as_borrowed()), "");
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
    let upper = str_to_upper(crate::abi_facts::test_owned(s));
    unsafe {
        assert_eq!(read_str(upper.as_borrowed()), "HELLO");
    }
    rc::consume_shallow(upper);
    let s = alloc_string(b"Hello") as i64;
    let lower = str_to_lower(crate::abi_facts::test_owned(s));
    unsafe {
        assert_eq!(read_str(lower.as_borrowed()), "hello");
    }
    rc::consume_shallow(lower);
}
