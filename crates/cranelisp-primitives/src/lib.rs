//! Cranelisp primitives — user-callable, symbol-table addressable operations.
//!
//! Per Decision 43 + `design/arch/facades/primitives.md`: this crate hosts the
//! kebab-case, user-addressable primitives whose JIT names appear in the
//! synthetic `primitives` module's symbol table (e.g. `str-concat`, `vec-len`,
//! `substring`). The sibling crate `cranelisp-intrinsics` hosts the
//! backend-emitted-call targets (`runtime/alloc`, `runtime/dealloc`,
//! `runtime/panic`, RC primitives, drop glue, the IO trampoline) — those are
//! the codegen-coupled implementation substrate; this crate is the
//! spec-driven user surface that calls into intrinsics as needed.
//!
//! ## Wave 3b-2d.2 status (FIXME 0150 source migration, primitives half)
//!
//! Wave 3b-1 (commit 9e4d9b1) seeded `cranelisp-intrinsics` with the
//! backend-emitted-call targets formerly in `cranelisp-runtime`. Wave 3b-2d.1
//! (commit e4cc3c9) absorbed the remaining backend-emitted-call targets
//! (alloc, drop, rc, panic, ivar, io, vec, string, trace) into intrinsics.
//! The present wave (3b-2d.2) lifts the **user-callable primitive Rust
//! functions** out of `cranelisp-intrinsics` into this crate.
//!
//! | Functions moved | Destination |
//! |---|---|
//! | `str_concat`, `str_eq`, `str_len`, `string_identity`, `str_substring`, `str_char_at`, `str_split`, `str_join`, `str_replace`, `str_trim`, `str_starts_with`, `str_ends_with`, `str_contains`, `str_to_upper`, `str_to_lower` | `cranelisp_primitives::string` |
//! | `vec_len` | `cranelisp_primitives::vec` |
//!
//! `cranelisp-intrinsics` keeps thin re-export shims (`pub use
//! cranelisp_primitives::string::*` etc.) so existing consumers (backend's
//! `IntrinsicSymbol` registration, integration tests) continue to compile
//! against the legacy `cranelisp_intrinsics::*` paths. The β-3 wave will
//! migrate those call sites to import from `cranelisp_primitives::*`
//! directly and drop the shims.
//!
//! **Functions kept in intrinsics** (and the reason):
//!
//! - `heap_alloc_string`, `string_read` — JIT name uses `runtime/` prefix;
//!   backend-emitted internal helpers, not user-callable.
//! - `alloc_string`, `read_string_as_str`, `HeapString` — Rust-callable
//!   internal helpers used by user-callable primitives in *this* crate. The
//!   HeapString layout is intrinsics-owned per Decision 12 (Principle 14 —
//!   FFI layout discipline).
//! - `vec_new`, `vec_drop` — JIT name uses `runtime/` prefix; backend-emitted
//!   alloc/dealloc helpers, not user-callable.
//! - `vec_set_copy`, `vec_push_copy`, `vec_push_grow` — though kebab-named,
//!   these are the COW *fallback path* emitted by backend `vec_codegen.rs`
//!   when last-use analysis cannot prove in-place mutation is safe. The
//!   user calls `vec-set` / `vec-push`, which the backend inlines via
//!   `vec_codegen.rs` and which may emit calls to these extern fallbacks.
//!   They are backend-emitted-call targets in spirit even though their
//!   names lack the `runtime/` prefix. Re-classification (rename to
//!   `runtime/vec_set_copy` etc., or admit them as primitives proper) is a
//!   forward `/arch` question — left in intrinsics for this wave.
//! - `vec_drop` is `runtime/vec_drop` — backend-emitted drop glue.
//! - `string_identity` — although it has a kebab-case JIT name, it is
//!   directly user-callable via `(Display.show s)` resolution (the trait
//!   impl maps the method to this primitive). Kept in `string.rs` here.
//!
//! Per FIXME 0150 Phase 4-5, β-2 (user-callable converters
//! `int_to_string`/`parse_int`/`float_to_string`/`bool_to_string` plus
//! `cranelisp_op_*` operator wrappers, and the marshal primitives
//! `sconcat`/`quote_sexp`) is the *other* user-callable surface in
//! `cranelisp-runtime/src/{primitives,marshal}.rs`. That migration is left to
//! a follow-on wave per the wave's scope boundary — this wave only relocates
//! the user-callable surface that was already in `cranelisp-intrinsics`.

pub mod string;
pub mod vec;

pub use string::{
    str_char_at, str_concat, str_contains, str_ends_with, str_eq, str_join, str_len,
    str_replace, str_split, str_starts_with, str_substring, str_to_lower, str_to_upper,
    str_trim, string_identity,
};

pub use vec::vec_len;
