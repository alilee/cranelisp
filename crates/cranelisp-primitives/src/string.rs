//! User-callable string primitives — primitives-surface presentation.
//!
//! Per Decision 43 + `design/arch/facades/primitives.md`: the kebab-case
//! string operations callable from user code (`str-concat`, `str-eq`,
//! `substring`, `split`, etc.) belong to the **primitives** bounded context
//! — they are addressable via the synthetic `primitives` module's symbol
//! table, with kebab-case JIT names.
//!
//! ## Source-residence note (Wave 3b-2d.2, FIXME 0150)
//!
//! The fn bodies physically reside in `cranelisp_intrinsics::string` —
//! they call into the alloc / rc / HeapString helpers defined there, and
//! the legacy `cranelisp-runtime` crate's pre-D43 shims still re-export
//! them along that path so backend's `IntrinsicSymbol` registration table
//! resolves them at `cranelisp_runtime::str_concat` etc.
//!
//! Physically relocating the bodies into this crate requires either an
//! `intrinsics → primitives` Cargo edge (which would form a cycle with the
//! existing `primitives → intrinsics` edge needed for alloc helpers) or
//! editing `cranelisp-runtime` to point its shims here. Both are out of
//! scope for this wave — β-3 territory under FIXME 0150 once runtime
//! retires entirely.
//!
//! This module re-exports the user-callable extern fns from intrinsics so
//! the Rust public-API surface of `cranelisp-primitives` reflects the
//! primitives BC's user-callable set — what consumers should *aim* to
//! import and what `cargo-public-api` records as the as-designed surface.

pub use cranelisp_intrinsics::string::{
    str_char_at, str_concat, str_contains, str_ends_with, str_eq, str_join, str_len,
    str_replace, str_split, str_starts_with, str_substring, str_to_lower, str_to_upper,
    str_trim, string_identity,
};
