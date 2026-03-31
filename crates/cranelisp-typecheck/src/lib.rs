// cranelisp-typecheck: Hindley-Milner inference, traits, monomorphisation.
//
// Rings 0-1: Algorithm W unification, type inference for all expression forms
// including string literals and polymorphic ADTs with data constructor fields,
// builtin operator type schemes, exhaustiveness checking.
//
// Architecture: TypeChecker struct with borrow-splitting pattern -- hot-path
// functions (unify, fresh_var) take explicit &mut Subst / &mut TypeId parameters
// to avoid &mut self conflicts.
//
// Concurrency (Sprint 40):
// - Phase 1: per-check transient state extracted into `CheckState`
// - Phase 2: `AtomicU32` for TypeId allocation, per-module compilation locks
//   via `try_lock_module()` / `ModuleGuard` RAII guard
// - Phase 3: shared registries (type_defs, trait_registry, impl_registry)
//   behind `RwLock` for parallel-safe access. `check()` remains `&mut self`
//   until the pipeline needs concurrent calls (see checker.rs module doc).

mod adt;
mod builtins;
mod checker;
mod infer;
mod program;
mod resolve;
mod scheme;
mod scope;
mod traits;
mod unify;

// Public API
pub use checker::{CheckState, ModuleGuard, TypeChecker};
pub use program::{CheckPass, FormCheckResult, ModuleCheckAccumulator};

// Re-export boundary types that callers need
pub use cranelisp_types::{
    CheckResult, CranelispError, ReplSnapshot, TopLevel,
};
