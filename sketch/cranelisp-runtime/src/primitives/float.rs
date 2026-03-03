//! Float-specific primitive functions.

/// Convert a float (stored as i64 bits) to its string representation. Returns a string pointer.
#[unsafe(export_name = "float-to-string")]
pub extern "C" fn float_to_string(value: i64) -> i64 {
    let f = f64::from_bits(value as u64);
    let s = format!("{}", f);
    super::alloc_string(s.as_bytes())
}

// ── Operator wrapper functions ────────────────────────────────────────
// Used when float operators are passed as first-class values.

fn to_f64(v: i64) -> f64 {
    f64::from_bits(v as u64)
}
fn from_f64(f: f64) -> i64 {
    f.to_bits() as i64
}

#[unsafe(export_name = "cranelisp_op_fadd")]
pub extern "C" fn op_fadd(a: i64, b: i64) -> i64 {
    from_f64(to_f64(a) + to_f64(b))
}
#[unsafe(export_name = "cranelisp_op_fsub")]
pub extern "C" fn op_fsub(a: i64, b: i64) -> i64 {
    from_f64(to_f64(a) - to_f64(b))
}
#[unsafe(export_name = "cranelisp_op_fmul")]
pub extern "C" fn op_fmul(a: i64, b: i64) -> i64 {
    from_f64(to_f64(a) * to_f64(b))
}
#[unsafe(export_name = "cranelisp_op_fdiv")]
pub extern "C" fn op_fdiv(a: i64, b: i64) -> i64 {
    from_f64(to_f64(a) / to_f64(b))
}
#[unsafe(export_name = "cranelisp_op_feq")]
pub extern "C" fn op_feq(a: i64, b: i64) -> i64 {
    if to_f64(a) == to_f64(b) {
        1
    } else {
        0
    }
}
#[unsafe(export_name = "cranelisp_op_flt")]
pub extern "C" fn op_flt(a: i64, b: i64) -> i64 {
    if to_f64(a) < to_f64(b) {
        1
    } else {
        0
    }
}
#[unsafe(export_name = "cranelisp_op_fgt")]
pub extern "C" fn op_fgt(a: i64, b: i64) -> i64 {
    if to_f64(a) > to_f64(b) {
        1
    } else {
        0
    }
}
#[unsafe(export_name = "cranelisp_op_fle")]
pub extern "C" fn op_fle(a: i64, b: i64) -> i64 {
    if to_f64(a) <= to_f64(b) {
        1
    } else {
        0
    }
}
#[unsafe(export_name = "cranelisp_op_fge")]
pub extern "C" fn op_fge(a: i64, b: i64) -> i64 {
    if to_f64(a) >= to_f64(b) {
        1
    } else {
        0
    }
}
