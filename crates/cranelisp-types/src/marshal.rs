//! Shared tag constants for runtime Sexp and SList ADT values.
//!
//! These constants define the runtime tag layout for the `Sexp` and `SList`
//! algebraic data types used by the macro system. Both the compiler-side
//! marshal (`src/marshal.rs`) and the runtime-side marshal
//! (`crates/cranelisp-primitives/src/marshal.rs`) import these to stay in sync.
//!
//! **Authoritative source of constructor order**:
//! `register_macros_module()` in `crates/cranelisp-typecheck/src/builtins.rs`.
//! If the constructor order changes there, these constants MUST be updated
//! to match.

// ---------------------------------------------------------------------------
// SList tags — polymorphic at the type level, fixed at runtime.
// Order defined by register_macros_module() → register_slist_type().
// ---------------------------------------------------------------------------

/// SNil: nullary constructor (tag 0).
///
/// Constructor order defined by `register_macros_module()` in
/// `crates/cranelisp-typecheck/src/builtins.rs`.
pub const TAG_SNIL: i64 = 0;

/// SCons: data constructor (tag 1) with fields `[shead, stail]`.
///
/// Constructor order defined by `register_macros_module()` in
/// `crates/cranelisp-typecheck/src/builtins.rs`.
pub const TAG_SCONS: i64 = 1;

// ---------------------------------------------------------------------------
// Sexp tags — all data constructors (no nullary).
// Order defined by register_macros_module() → register_sexp_type().
// ---------------------------------------------------------------------------

/// SexpInt: data constructor (tag 0) with field `[:Int sval]`.
///
/// Constructor order defined by `register_macros_module()` in
/// `crates/cranelisp-typecheck/src/builtins.rs`.
pub const TAG_SEXP_INT: i64 = 0;

/// SexpFloat: data constructor (tag 1) with field `[:Float sval]`.
///
/// Constructor order defined by `register_macros_module()` in
/// `crates/cranelisp-typecheck/src/builtins.rs`.
pub const TAG_SEXP_FLOAT: i64 = 1;

/// SexpBool: data constructor (tag 2) with field `[:Bool sval]`.
///
/// Constructor order defined by `register_macros_module()` in
/// `crates/cranelisp-typecheck/src/builtins.rs`.
pub const TAG_SEXP_BOOL: i64 = 2;

/// SexpStr: data constructor (tag 3) with field `[:String sval]`.
///
/// Constructor order defined by `register_macros_module()` in
/// `crates/cranelisp-typecheck/src/builtins.rs`.
pub const TAG_SEXP_STR: i64 = 3;

/// SexpSym: data constructor (tag 4) with field `[:String sname]`.
///
/// Constructor order defined by `register_macros_module()` in
/// `crates/cranelisp-typecheck/src/builtins.rs`.
pub const TAG_SEXP_SYM: i64 = 4;

/// SexpList: data constructor (tag 5) with field `[:(SList Sexp) sitems]`.
///
/// Constructor order defined by `register_macros_module()` in
/// `crates/cranelisp-typecheck/src/builtins.rs`.
pub const TAG_SEXP_LIST: i64 = 5;

/// SexpBracket: data constructor (tag 6) with field `[:(SList Sexp) sitems]`.
///
/// Constructor order defined by `register_macros_module()` in
/// `crates/cranelisp-typecheck/src/builtins.rs`.
pub const TAG_SEXP_BRACKET: i64 = 6;
/// SexpAnnotated (tag 7), appended so prior constructor tags remain stable.
pub const TAG_SEXP_ANNOTATED: i64 = 7;

#[cfg(test)]
mod tests;
