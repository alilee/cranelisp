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
            assert_eq!(heap_string::read_string_as_str(result), "3.0");
            alloc::dealloc(result as *mut u8);
        }
    }

    // spec: appendix-a-builtins §A.3 — float-to-string converts fractional float
    #[test]
    fn test_float_to_string_fractional() {
        let result = float_to_string(float_bits(3.25));
        unsafe {
            assert_eq!(heap_string::read_string_as_str(result), "3.25");
            alloc::dealloc(result as *mut u8);
        }
    }

    // spec: appendix-a-builtins §A.3 — float-to-string converts negative float
    #[test]
    fn test_float_to_string_negative() {
        let result = float_to_string(float_bits(-2.5));
        unsafe {
            assert_eq!(heap_string::read_string_as_str(result), "-2.5");
            alloc::dealloc(result as *mut u8);
        }
    }

    // spec: appendix-a-builtins §A.3 — float-to-string converts zero
    #[test]
    fn test_float_to_string_zero() {
        let result = float_to_string(float_bits(0.0));
        unsafe {
            assert_eq!(heap_string::read_string_as_str(result), "0.0");
            alloc::dealloc(result as *mut u8);
        }
    }
