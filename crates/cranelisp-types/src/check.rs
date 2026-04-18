// FIXME(/typecheck): Phase 5 — slim `CheckResult` (a.k.a. CheckOutput) to typecheck-internal state.
// Post-Phase-2, `method_resolutions`, `mono_defns`, `default_method_defns`,
// `constrained_fn_names`, and `expr_types` are duplicate data (canonical source
// is ModuleEntry.ast + annotated AST nodes). Only `warnings` and `display` remain
// as boundary data. See design/backend/ast-sourced-codegen.md §3.7.

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

/// Result of type checking a compilation unit.
/// Unified boundary type between typecheck and backend — used for both
/// batch programs and REPL inputs. REPL inputs set `display` to carry
/// the inferred type/scheme for interactive output.
#[derive(Debug, Clone)]
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
    /// Display info for REPL output (None in batch mode).
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
