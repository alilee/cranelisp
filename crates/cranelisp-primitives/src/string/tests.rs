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
