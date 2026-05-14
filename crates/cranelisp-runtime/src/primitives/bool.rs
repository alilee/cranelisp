//! Thin re-export shim — body relocated to `cranelisp_primitives::bool`
//! per Wave 3b-2d.2b (FIXME 0150). Kept so consumers using
//! `cranelisp_runtime::primitives::bool::*` and
//! `cranelisp_runtime::bool_to_string` continue to compile until
//! `cranelisp-runtime` retires (β-3).

pub use cranelisp_primitives::bool::bool_to_string;
