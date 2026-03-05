// cranelisp-typecheck: Hindley-Milner inference, traits, monomorphisation.
//
// Ring 0 scope: Algorithm W unification, type inference for 10 expression forms,
// builtin operator type schemes, enum ADT type checking and exhaustiveness.
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
mod unify;

// Public API
pub use checker::TypeChecker;

// Re-export boundary types that callers need
pub use cranelisp_types::{
    CheckResult, CranelispError, ReplCheckResult, ReplInput, ReplSnapshot, TopLevel,
};
