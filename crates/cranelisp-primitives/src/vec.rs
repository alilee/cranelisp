//! User-callable Vec primitives — primitives-surface presentation.
//!
//! Per Decision 43 + `design/arch/facades/primitives.md`: `vec-len` is the
//! kebab-case, user-addressable Vec read accessor. Source-residence note:
//! see `crate::string`'s top-of-file comment — the body lives in
//! `cranelisp_intrinsics::vec` for the same wave-scope reason; this module
//! presents the primitives-BC surface via re-export.

pub use cranelisp_intrinsics::vec::vec_len;
