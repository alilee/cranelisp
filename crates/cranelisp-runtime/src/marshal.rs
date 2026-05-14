//! Thin re-export shim — bodies relocated to `cranelisp_primitives::marshal`
//! per Wave 3b-2d.2b (FIXME 0150). Kept so consumers using
//! `cranelisp_runtime::marshal::*` and `cranelisp_runtime::{sconcat,
//! quote_sexp}` continue to compile until `cranelisp-runtime` retires (β-3).

pub use cranelisp_primitives::marshal::{quote_sexp, sconcat};
