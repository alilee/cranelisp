use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use crate::{Defn, FQTraitName, FQTypeName, JitSymbol, Scheme, Span, Symbol, Type};

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

// `CheckResult` relocated to `cranelisp-typecheck::result` per FIXME 0100
// Phase 1 (Principle 15). See `crates/cranelisp-typecheck/src/result.rs`.

/// Information about a user-defined type.
///
/// `constructors: Vec<Symbol>` carries only the constructor NAMES. The
/// per-constructor metadata (tag, field count, type_name, internal flag)
/// lives uniquely on each constructor's own `ModuleEntry::Def` entry at
/// `kind: DefKind::Constructor { .. }` (see facades/types.md §"Symbol table
/// — the single store" §"DefKind"). Field names live on the Def's
/// `param_names`; field types fold into the Def's `scheme` (the constructor's
/// polymorphic function-type signature, e.g., `Some : ∀a. a → Option a`).
///
/// Consumers needing per-ctor metadata walk each name → look up the Def →
/// read the kind discriminator and scheme. No parallel storage; single source
/// of truth.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeDefInfo {
    pub name: FQTypeName,
    pub type_params: Vec<Symbol>,
    pub constructors: Vec<Symbol>,
    pub docstring: Option<String>,
}

// `pub struct ConstructorInfo { ... }` retired — see facades/types.md
// §"Symbol table — the single store" §"DefKind" for the ctor-as-Def shape
// and the migration map below.
//
// Migration map:
//   - .name           → ModuleEntry::Def.name (the symbol-table key)
//   - .tag            → DefKind::Constructor.tag
//   - .fields[i].name → Def.param_names[i]
//   - .fields[i].ty   → folded into Def.scheme (the polymorphic function-type signature)
//   - .docstring      → Def.docstring
//   - .internal       → DefKind::Constructor.internal
//
// `FieldInfo` retained — consumed by `HeapCategory::classify` for heap-layout
// determination. After consumer-cascade migration completes, heap classifier
// derives `FieldInfo` instances from constructor Defs' schemes rather than
// from a pre-built `ConstructorInfo.fields` vector.

/// Information about a constructor field (resolved type, not TypeExpr).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FieldInfo {
    pub name: Symbol,
    pub ty: Type,
}

// `ReplSnapshot` relocated to `cranelisp-typecheck::result` per FIXME 0100
// Phase 1 (Principle 15). See `crates/cranelisp-typecheck/src/result.rs`.
