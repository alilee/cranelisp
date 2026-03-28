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
//   behind `RwLock` for parallel-safe access.
//
// Sprint 40a Wave 1: `check()` creates a fresh `CheckState` per invocation.
// Transient state does not persist across calls. REPL additive overloads
// are reconstructed from symbol table `DefKind::Overloaded` entries.
// `check()` remains `&mut self` because registration methods mutate
// persistent state; `&self` conversion requires RwLock (Wave 2).

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

// Re-export boundary types that callers need
pub use cranelisp_types::{
    CheckResult, CranelispError, ReplSnapshot, TopLevel,
};
