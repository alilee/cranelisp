// cranelisp-typecheck: Hindley-Milner inference, traits, monomorphisation.
//
// Rings 0-1: Algorithm W unification, type inference for all expression forms
// including string literals and polymorphic ADTs with data constructor fields,
// builtin operator type schemes, exhaustiveness checking.
//
// Architecture: TypeCheckEnv struct with borrowed references to shared state.
// Methods take `&self` (immutable — DashMap and AtomicU32 have interior
// mutability) plus `&mut CheckState` for per-invocation transient state.
//
// State model (Sprint 51):
// - All type definitions, trait declarations, and trait implementations stored
//   on per-module SymbolTables (no global registries).
// - Per-check transient state in `CheckState`, owned by the caller.
// - `&AtomicU32` for TypeId allocation, borrowed from session-owned state.

mod adt;
pub mod builtins;
mod checker;
mod infer;
mod program;
mod resolve;
mod scheme;
mod scope;
pub mod trace;
mod traits;
mod unify;

// Public API
pub use builtins::register_builtins;
pub use checker::{CheckState, TypeCheckEnv};
pub use program::{CheckPass, FormCheckResult, ModuleCheckAccumulator};
pub use trace::{
    SymbolTableEnsureHook, SymbolTableEnsureOutcome, install_symbol_table_ensure_hook,
};

// Re-export boundary types that callers need
pub use cranelisp_types::{
    CheckResult, CranelispError, ReplSnapshot, TopLevel,
};
