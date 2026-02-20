//! String-specific primitive functions.

/// Identity function for strings — show on String just returns the argument.
#[unsafe(export_name = "string-identity")]
pub extern "C" fn string_identity(value: i64) -> i64 {
    value
}

/// Concatenate two heap strings, returning a new heap string.
#[unsafe(export_name = "str-concat")]
pub extern "C" fn str_concat(a: i64, b: i64) -> i64 {
    let (a_str, b_str) = unsafe {
        let a_len = *(a as *const i64) as usize;
        let a_bytes = std::slice::from_raw_parts((a + 8) as *const u8, a_len);
        let b_len = *(b as *const i64) as usize;
        let b_bytes = std::slice::from_raw_parts((b + 8) as *const u8, b_len);
        (
            std::str::from_utf8(a_bytes).unwrap_or(""),
            std::str::from_utf8(b_bytes).unwrap_or(""),
        )
    };

    let result = format!("{}{}", a_str, b_str);
    let len = result.len();
    let ptr = crate::intrinsics::alloc_with_rc(8 + len);
    unsafe {
        *(ptr as *mut i64) = len as i64;
        std::ptr::copy_nonoverlapping(result.as_ptr(), ptr.add(8), len);
    }
    ptr as i64
}

/// Parse a heap string as an integer. Returns Option Int as ADT runtime representation:
/// - None: bare i64 tag 0
/// - Some(n): heap pointer to [tag=1, n]
#[unsafe(export_name = "parse-int")]
pub extern "C" fn parse_int(ptr: i64) -> i64 {
    let s = unsafe {
        let len = *(ptr as *const i64) as usize;
        let bytes = std::slice::from_raw_parts((ptr + 8) as *const u8, len);
        std::str::from_utf8(bytes).unwrap_or("")
    };

    match s.trim().parse::<i64>() {
        Ok(n) => {
            // Some(n): allocate [tag=1, n] with rc header
            let ptr = crate::intrinsics::alloc_with_rc(16);
            unsafe {
                *(ptr as *mut i64) = 1; // tag for Some
                *((ptr as *mut i64).add(1)) = n;
                ptr as i64
            }
        }
        Err(_) => {
            // None: bare tag 0
            0
        }
    }
}
