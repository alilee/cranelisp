//! Thin re-export shim — body relocated to `cranelisp_primitives::float`
//! per Wave 3b-2d.2b (FIXME 0150). Kept so consumers using
//! `cranelisp_runtime::primitives::float::*` and
//! `cranelisp_runtime::float_to_string` continue to compile until
//! `cranelisp-runtime` retires (β-3).

pub use cranelisp_primitives::float::float_to_string;
