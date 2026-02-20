//! Int-specific primitive functions.

/// Convert an i64 to its string representation. Returns a string pointer.
/// String layout: [i64 length][u8 bytes...]
#[unsafe(export_name = "int-to-string")]
pub extern "C" fn int_to_string(value: i64) -> i64 {
    let s = value.to_string();
    super::alloc_string(s.as_bytes())
}

// ── Operator wrapper functions ────────────────────────────────────────
// Used when operators are passed as first-class values (e.g., `(let [f +] (f 1 2))`).

#[unsafe(export_name = "cranelisp_op_add")]
pub extern "C" fn op_add(a: i64, b: i64) -> i64 {
    a.wrapping_add(b)
}
#[unsafe(export_name = "cranelisp_op_sub")]
pub extern "C" fn op_sub(a: i64, b: i64) -> i64 {
    a.wrapping_sub(b)
}
#[unsafe(export_name = "cranelisp_op_mul")]
pub extern "C" fn op_mul(a: i64, b: i64) -> i64 {
    a.wrapping_mul(b)
}
#[unsafe(export_name = "cranelisp_op_div")]
pub extern "C" fn op_div(a: i64, b: i64) -> i64 {
    a.wrapping_div(b)
}
#[unsafe(export_name = "cranelisp_op_eq")]
pub extern "C" fn op_eq(a: i64, b: i64) -> i64 {
    if a == b {
        1
    } else {
        0
    }
}
#[unsafe(export_name = "cranelisp_op_lt")]
pub extern "C" fn op_lt(a: i64, b: i64) -> i64 {
    if a < b {
        1
    } else {
        0
    }
}
#[unsafe(export_name = "cranelisp_op_gt")]
pub extern "C" fn op_gt(a: i64, b: i64) -> i64 {
    if a > b {
        1
    } else {
        0
    }
}
#[unsafe(export_name = "cranelisp_op_le")]
pub extern "C" fn op_le(a: i64, b: i64) -> i64 {
    if a <= b {
        1
    } else {
        0
    }
}
#[unsafe(export_name = "cranelisp_op_ge")]
pub extern "C" fn op_ge(a: i64, b: i64) -> i64 {
    if a >= b {
        1
    } else {
        0
    }
}
