use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

use crate::{
    Defn, FQTraitName, FQTypeName, JitSymbol, Scheme, Span, Symbol, Type, TypeId, Warning,
};

/// Map from call site span to how that call was resolved.
pub type MethodResolutions = HashMap<Span, ResolvedCall>;

/// How a function call was resolved by the typechecker.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ResolvedCall {
    /// Resolved to a trait method implementation (Ring 2)
    TraitMethod {
        trait_name: FQTraitName,
        method_name: Symbol,
        impl_type: FQTypeName,
        mangled_name: JitSymbol,
    },
    /// Resolved to a specific multi-sig variant (Ring 2)
    SigDispatch { mangled_name: JitSymbol },
    /// Resolved to an auto-curried partial application (Ring 2)
    AutoCurry {
        target_name: Symbol,
        applied_count: usize,
        total_count: usize,
        /// When the auto-curried target is a trait method or builtin,
        /// this holds the concrete resolution (e.g., TraitMethod → "add-i64").
        /// The wrapper function uses this to call the resolved target
        /// instead of the abstract trait method name.
        trait_resolution: Option<Box<ResolvedCall>>,
    },
    /// Resolved to a builtin function (inline IR emission).
    /// The name uniquely identifies the Cranelift instruction — e.g. `add-i64` → `iadd`.
    /// No `operand_type` needed: each primitive is monomorphic (name encodes types).
    BuiltinFn {
        name: Symbol,
    },
}

/// A monomorphised function definition with its specific method resolutions.
#[derive(Debug, Clone)]
pub struct MonoDefn {
    pub defn: Defn,
    pub resolutions: MethodResolutions,
    /// Per-mono expression types (subset of the full program's expr_types).
    /// Avoids O(n*m) cloning of the full expr_types map for each mono defn.
    pub expr_types: HashMap<Span, Type>,
}

/// Display information for REPL output (inferred type and optional scheme).
/// Present in CheckResult only when processing REPL input that should display a result.
#[derive(Debug, Clone)]
pub struct DisplayInfo {
    /// Inferred type of the expression or definition
    pub ty: Type,
    /// Generalized scheme for defn display (None for bare expressions)
    pub scheme: Option<Scheme>,
}

/// Transient output of `TypeChecker::check`.
///
/// NOT a boundary type — the durable typecheck output lives on `SymbolTable`
/// entries' `ast`, `scheme`, `callees`, `got_slot`, and `trait_origin` fields.
/// This struct carries only diagnostics and optional REPL display payload.
///
/// Prior to Sprint 57 Wave 2 step 4, this struct also carried
/// `method_resolutions`, `constrained_fn_names`, `mono_defns`, `expr_types`,
/// and `default_method_defns`. Those fields were retired once the Phase-1
/// per-AST-node annotations (`Expr.inferred_type`, `Expr::Apply.resolved_call`)
/// and Phase-2 `ModuleEntry::Def.ast` became the single source of truth.
/// See `design/typecheck/ast-annotation.md` §10 for the audit trail.
#[derive(Debug, Clone)]
pub struct CheckResult {
    /// Non-fatal warnings accumulated during checking.
    pub warnings: Vec<Warning>,
    /// Display info for REPL output (None in batch / module-load mode).
    pub display: Option<DisplayInfo>,
}

/// Information about a user-defined type.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeDefInfo {
    pub name: FQTypeName,
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
