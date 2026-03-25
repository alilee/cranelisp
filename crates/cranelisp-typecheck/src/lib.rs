// cranelisp-typecheck: Hindley-Milner inference, traits, monomorphisation.
//
// Rings 0-1: Algorithm W unification, type inference for all expression forms
// including string literals and polymorphic ADTs with data constructor fields,
// builtin operator type schemes, exhaustiveness checking.
//
// Architecture: TypeChecker struct with borrow-splitting pattern -- hot-path
// functions (unify, fresh_var) take explicit &mut Subst / &mut TypeId parameters
// to avoid &mut self conflicts.

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
pub use checker::TypeChecker;

// Re-export boundary types that callers need
pub use cranelisp_types::{
    CheckResult, CranelispError, ReplSnapshot, TopLevel,
};
