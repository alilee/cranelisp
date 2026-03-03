/// Read a cranelisp string from a heap pointer (layout: [i64 len][u8 bytes...]).
///
/// # Safety
/// `ptr` must be a valid heap pointer to a cranelisp string (i64 length followed by UTF-8 bytes).
pub unsafe fn read_cranelisp_string(ptr: i64) -> String {
    unsafe {
        let len = *(ptr as *const i64) as usize;
        let bytes = std::slice::from_raw_parts((ptr + 8) as *const u8, len);
        std::str::from_utf8(bytes)
            .unwrap_or("<invalid utf8>")
            .to_string()
    }
}

/// Check if parentheses/brackets are balanced in the input.
/// Skips characters inside string literals.
pub fn parens_balanced(input: &str) -> bool {
    let mut depth = 0i32;
    let mut in_string = false;
    let mut escape = false;
    for ch in input.chars() {
        if escape {
            escape = false;
            continue;
        }
        if in_string {
            match ch {
                '\\' => escape = true,
                '"' => in_string = false,
                _ => {}
            }
        } else {
            match ch {
                '"' => in_string = true,
                '(' | '[' => depth += 1,
                ')' | ']' => depth -= 1,
                _ => {}
            }
        }
    }
    depth <= 0
}
