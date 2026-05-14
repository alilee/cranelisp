//! Cranelisp primitives — user-callable, symbol-table addressable operations.
//!
//! Per Decision 43 + `design/arch/facades/primitives.md`: this crate hosts the
//! kebab-case, user-addressable primitives whose JIT names appear in the
//! synthetic `primitives` module's symbol table (e.g. `str-concat`, `vec-len`,
//! `substring`, `int-to-string`, `parse-int`, `float-to-string`,
//! `bool-to-string`, `sconcat`, `quote-sexp`). The sibling crate
//! `cranelisp-intrinsics` hosts the backend-emitted-call targets
//! (`runtime/alloc`, `runtime/dealloc`, `runtime/panic`, RC primitives, drop
//! glue, the IO trampoline, the `cranelisp_op_*` operator-as-value
//! wrappers) — those are the codegen-coupled implementation substrate; this
//! crate is the spec-driven user surface that calls into intrinsics as
//! needed.
//!
//! ## Wave 3b-2d.2b status (FIXME 0150 source migration, primitives half — β-2 follow-on)
//!
//! Wave 3b-2d.2 (commit `6654a6e`) lifted the user-callable
//! string + vec functions out of `cranelisp-intrinsics` into this crate via
//! re-export (a Cargo cycle prevented physically moving the bodies — see
//! `design/arch/fixmes/0180-arch-primitives-physical-relocation-blocked-by-runtime-shims.md`).
//!
//! Wave 3b-2d.2b (the present commit) lifts the **remaining user-callable
//! Rust extern fns** that previously lived in `cranelisp-runtime`:
//!
//! | Source (former runtime) | Destination |
//! |---|---|
//! | `marshal::{sconcat, quote_sexp}`                  | `cranelisp_primitives::marshal`  |
//! | `primitives::int::{int_to_string, parse_int}`     | `cranelisp_primitives::int`      |
//! | `primitives::float::float_to_string`              | `cranelisp_primitives::float`    |
//! | `primitives::bool::bool_to_string`                | `cranelisp_primitives::bool`     |
//!
//! The `cranelisp_op_*` operator-as-value wrappers that previously cohabited
//! `primitives::int` are **backend-emitted-call targets** (not user-callable;
//! backend emits direct `Linkage::Import` calls from the operator-as-value
//! codegen path) and migrated to `cranelisp_intrinsics::ops` instead.
//!
//! `cranelisp-runtime` keeps thin re-export shims for every relocated item so
//! existing consumers (backend's `IntrinsicSymbol` registration in
//! `crates/cranelisp-backend/src/jit.rs`, `exe-bundle`, integration tests)
//! continue to compile against `cranelisp_runtime::*` paths. β-3 migrates
//! those call sites to import from `cranelisp_primitives::*` /
//! `cranelisp_intrinsics::*` directly and retires `cranelisp-runtime`.
//!
//! **String + vec re-export note (Wave 3b-2d.2 — unchanged here).** This
//! crate re-exports the user-callable string fns + `vec_len` from
//! `cranelisp-intrinsics`. Physical relocation is blocked by FIXME 0180 (a
//! Cargo cycle would form). The re-exports remain transitional; β-3 +
//! runtime retirement closes that thread.

pub mod bool;
pub mod float;
pub mod int;
pub mod marshal;
pub mod ring0;
pub mod string;
pub mod vec;

pub use ring0::ring0_jit_symbols;

pub use string::{
    str_char_at, str_concat, str_contains, str_ends_with, str_eq, str_join, str_len,
    str_replace, str_split, str_starts_with, str_substring, str_to_lower, str_to_upper,
    str_trim, string_identity,
};

pub use vec::vec_len;

pub use marshal::{quote_sexp, sconcat};

pub use int::{int_to_string, parse_int};
pub use float::float_to_string;
pub use bool::bool_to_string;
