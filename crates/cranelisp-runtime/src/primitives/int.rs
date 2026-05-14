//! Thin re-export shim — bodies relocated per Wave 3b-2d.2b (FIXME 0150).
//!
//! - `int_to_string`, `parse_int` → `cranelisp_primitives::int` (user-callable)
//! - `cranelisp_op_*` → `cranelisp_intrinsics::ops` (backend-emitted-call targets)
//!
//! Kept so consumers using `cranelisp_runtime::primitives::int::*` and
//! `cranelisp_runtime::{int_to_string, parse_int, cranelisp_op_*}` continue
//! to compile until `cranelisp-runtime` retires (β-3).

pub use cranelisp_primitives::int::{int_to_string, parse_int};
pub use cranelisp_intrinsics::ops::{
    cranelisp_op_add, cranelisp_op_div, cranelisp_op_eq, cranelisp_op_ge, cranelisp_op_gt,
    cranelisp_op_le, cranelisp_op_lt, cranelisp_op_mul, cranelisp_op_neq, cranelisp_op_sub,
};
