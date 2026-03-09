use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

use crate::{
    Defn, JitSymbol, Scheme, Span, Symbol, TraitName, Type, TypeId, TypeName, Warning,
};

/// Map from call site span to how that call was resolved.
pub type MethodResolutions = HashMap<Span, ResolvedCall>;

/// How a function call was resolved by the typechecker.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ResolvedCall {
    /// Resolved to a trait method implementation (Ring 2)
    TraitMethod {
        trait_name: TraitName,
        method_name: Symbol,
        impl_type: TypeName,
        mangled_name: JitSymbol,
    },
    /// Resolved to a specific multi-sig variant (Ring 2)
    SigDispatch { mangled_name: JitSymbol },
    /// Resolved to an auto-curried partial application (Ring 2)
    AutoCurry {
        target_name: Symbol,
        applied_count: usize,
    },
    /// Resolved to a builtin function (inline IR emission).
    /// The name uniquely identifies the Cranelift instruction — e.g. `add-i64` → `iadd`.
    /// No `operand_type` needed: each primitive is monomorphic (name encodes types).
    BuiltinFn {
        name: Symbol,
    },
}

/// A monomorphised function definition with its specific method resolutions.
#[derive(Debug)]
pub struct MonoDefn {
    pub defn: Defn,
    pub resolutions: MethodResolutions,
    /// Per-mono expression types (subset of the full program's expr_types).
    /// Avoids O(n*m) cloning of the full expr_types map for each mono defn.
    pub expr_types: HashMap<Span, Type>,
}

/// Result of type checking a batch compilation unit.
/// Primary boundary type between typecheck and backend.
#[derive(Debug)]
pub struct CheckResult {
    /// How each call site was resolved (trait dispatch, overload, auto-curry, builtin)
    pub method_resolutions: MethodResolutions,
    /// Names of constrained polymorphic functions requiring monomorphisation (Ring 2)
    pub constrained_fn_names: HashSet<Symbol>,
    /// Monomorphised function definitions generated during checking (Ring 2)
    pub mono_defns: Vec<MonoDefn>,
    /// Type of every expression, keyed by span (for codegen heap classification)
    pub expr_types: HashMap<Span, Type>,
    /// Default trait method implementations expanded during checking (Ring 2)
    pub default_method_defns: Vec<Defn>,
    /// Non-fatal warnings accumulated during checking
    pub warnings: Vec<Warning>,
    /// Type definitions registered during checking.
    /// Backend needs this for ADT tag info and match codegen.
    pub type_defs: HashMap<TypeName, TypeDefInfo>,
    /// Map from constructor name to its parent type name.
    /// Backend needs this to look up tag values during match codegen.
    pub constructor_to_type: HashMap<Symbol, TypeName>,
}

/// Result of type checking a single REPL input.
/// Distinct from CheckResult because REPL processes one form at a time
/// and needs the inferred type/scheme for display.
#[derive(Debug)]
pub struct ReplCheckResult {
    /// Inferred type of the expression or definition
    pub ty: Type,
    /// Generalized scheme for defn display (None for bare expressions)
    pub scheme: Option<Scheme>,
    /// How each call site was resolved
    pub method_resolutions: MethodResolutions,
    /// Type of every subexpression
    pub expr_types: HashMap<Span, Type>,
    /// Warnings from this input
    pub warnings: Vec<Warning>,
    /// Type definitions registered by this input (for deftype)
    pub type_defs: HashMap<TypeName, TypeDefInfo>,
    /// Constructor-to-type mappings registered by this input
    pub constructor_to_type: HashMap<Symbol, TypeName>,
    /// Names of constrained polymorphic functions requiring monomorphisation (Ring 2)
    pub constrained_fn_names: HashSet<Symbol>,
    /// Monomorphised function definitions generated during checking (Ring 2)
    pub mono_defns: Vec<MonoDefn>,
    /// Default trait method implementations expanded during checking (Ring 2)
    pub default_method_defns: Vec<Defn>,
}

/// Information about a user-defined type.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeDefInfo {
    pub name: TypeName,
    pub type_params: Vec<Symbol>,
    pub constructors: Vec<ConstructorInfo>,
    pub docstring: Option<String>,
}

/// Information about a single data constructor.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstructorInfo {
    pub name: Symbol,
    pub tag: usize,
    pub fields: Vec<FieldInfo>,
    pub docstring: Option<String>,
    /// If true, the constructor is internal to the compiler — users cannot construct
    /// or pattern-match on it. Example: `IO.Bind` is constructed only by `bind`.
    #[serde(default)]
    pub internal: bool,
}

/// Information about a constructor field (resolved type, not TypeExpr).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FieldInfo {
    pub name: Symbol,
    pub ty: Type,
}

/// Snapshot of typechecker state for REPL error recovery.
///
/// Before processing each REPL input, the typechecker takes a snapshot.
/// If type checking or codegen fails, the snapshot is restored so the
/// session remains in a consistent state.
///
/// Design decision (Wave 1): The typechecker owns the snapshot/restore
/// mechanism. The binary crate calls `snapshot()` before and `restore()`
/// on error. Fields are opaque to the binary crate.
#[derive(Debug, Clone)]
pub struct ReplSnapshot {
    /// Next type variable ID at snapshot time
    pub next_type_id: TypeId,
    /// Symbol keys present in the current module's symbol table at snapshot time.
    /// On restore, any keys not in this set are removed.
    pub symbol_keys: HashSet<Symbol>,
    /// Substitution state at snapshot time
    pub subst_len: usize,
    /// Scope stack depth at snapshot time (number of frames).
    /// On restore, extra frames pushed during a failed check are popped.
    pub scope_depth: usize,
}
