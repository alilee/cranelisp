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
//
// Wave 3a-β surface (Sprint 66, 2026-05-13 third amendment):
// - Public cluster-typecheck entry surface is `check_forms` (single free
//   function in `form` module) that the orchestrator
//   (`int::process_cluster`) calls once per cluster. Per Decision 44
//   (amended FIXME 0167 — Approach B + `ClusterContext`; third amendment
//   collapsing the two-pass split), the internal two-pass discipline (spec
//   §5.13.1) is implementation-phase ordering inside `check_forms`'s frame —
//   not facade-exposed. Staging-vs-live access is mediated by
//   `ClusterContext` (in `cluster` module). The pre-S66 `CheckPass`,
//   `FormCheckResult`, and `ModuleCheckAccumulator` public types are
//   removed; per-pass / per-form scaffolding survives `pub(crate)` to keep
//   the internal dispatcher working.

mod adt;
pub mod builtins;
mod checker;
mod cluster;
mod form;
mod infer;
mod program;
mod resolve;
mod result;
mod scheme;
mod scope;
pub mod trace;
mod traits;
mod unify;

// Public API
pub use builtins::register_builtins;
pub use checker::{
    CheckState, TypeCheckEnv, advance_next_id_past_table, register_exports, register_imports,
};
pub use cluster::{ClusterContext, ClusterRead, ClusterWrite};
pub use form::check_forms;
pub use result::{CheckError, CheckResult, ReplSnapshot};
pub use trace::{
    SymbolTableEnsureHook, SymbolTableEnsureOutcome, install_symbol_table_ensure_hook,
};

// Re-export boundary types that callers need (these stay in cranelisp-types).
pub use cranelisp_types::{CranelispError, TopLevel};
