use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[cfg(test)]
mod tests;

use crate::{
    Defn, FQSymbol, FQTraitName, FQTypeName, JitSymbol, ModuleFullPath, Scheme, Span, Symbol,
    TraitMethodSig, TraitName, Type,
};

/// Per-Span resolved-stage data produced by typecheck, consumed by backend.
///
/// Each field maps an AST-node span to the resolved-stage information that
/// typecheck materialised for that node. The original payload — `resolved_calls`
/// — carries call-site resolution (which `Apply` expression resolved to which
/// trait method / sig variant / curried wrapper / builtin). `pattern_ctors`
/// (S70 finding #4) extends the same pattern to constructor patterns inside
/// `match` arms: the syntactic-stage `Pattern::Constructor.name: SymbolRef`
/// stays on the AST; the resolved-stage `FQSymbol` materialises here, keyed
/// by the pattern's span.
///
/// **Why one struct rather than two.** Pattern-constructor resolution and
/// call-site resolution share the same lifecycle (produced post-typecheck;
/// consumed by backend codegen), the same access shape (per-Span lookup),
/// and the same DTO discipline (data-record; field set IS the contract).
/// Splitting into a sibling `PatternResolutions` would multiply the plumbing
/// through `CheckResult` / `MonoDefn` / cache without adding semantic
/// distinction. The sidecar choice (vs. embedding `Option<FQSymbol>` on
/// `Pattern::Constructor`) was user-arbitrated to mirror the producer/consumer
/// split for `TraitRef` and `TypeRef`: the syntactic-stage type stays on the
/// AST, the resolved-stage data lives adjacent.
///
/// Data-record DTO per `design/arch/bounded-contexts.md` §7 ("Field-level access on state types is discouraged outside the types crate") —
/// each field IS the public contract; serde round-trips structurally. Wrapped
/// (rather than type-aliased) per the facade §"`#[non_exhaustive]` policy"
/// (every public struct/enum MUST be `#[non_exhaustive]`; the policy intent —
/// extensibility, allow adding fields without breaking consumers — cannot
/// apply to a type alias because Rust forbids the attribute on aliases). The
/// wrapper admits future-field additions without breaking the public-api
/// baseline; the `pattern_ctors` field landed in S70 step 3 (finding #4) is
/// the first such addition, vindicating the wrapper choice.
///
/// Grounded by:
/// - `design/arch/bounded-contexts.md` §7 + crate-root `//!` `#[non_exhaustive]` policy (binding)
/// - Decision 47 (FQ binding at resolved-stage boundaries — `pattern_ctors`)
/// - Principle 8 (no interim implementations — the alias was a stand-in
///   that committed the surface to `HashMap` forever)
/// - Principle 13 (`interfaces.md` is auditable + `cargo-public-api`-gateable
///   — the newtype struct is the auditable surface; a type alias to a
///   foreign generic is not)
///
/// Illustrative future fields (not committed): per-call-site context (e.g.,
/// monomorphisation environment carried alongside the resolution); explicit
/// instance-context for trait resolution (e.g., dictionary-passing metadata).
/// Such additions land as new `pub` fields on this struct without consumer
/// churn.
///
/// Closes S69 Submission 31 (audit finding S-DRIFT-8); extended in S70 step 3
/// (sweep finding #4) with `pattern_ctors` for `Pattern::Constructor` FQ
/// resolution at the post-typecheck boundary.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[non_exhaustive]
pub struct MethodResolutions {
    /// Per-`Apply`-span resolution: how typecheck resolved each call site.
    pub resolved_calls: HashMap<Span, ResolvedCall>,
    /// Per-`Pattern::Constructor`-span FQ resolution: the constructor's
    /// fully-qualified symbol (module-defining-the-ADT-constructor +
    /// constructor name) as resolved by typecheck against the scrutinee
    /// type. The syntactic-stage `Pattern::Constructor.name: SymbolRef`
    /// stays on the AST; backend codegen reads this map by pattern span to
    /// recover the FQ identity for tag/layout lookup. Per Decision 47 —
    /// pattern matching is a resolved-stage boundary, and the bare
    /// `Symbol` slipping through was the D47-violation pattern flagged by
    /// the S70 cranelisp-types solidness sweep finding #4.
    pub pattern_ctors: HashMap<Span, FQSymbol>,
    /// Per-reference-span resolved STORAGE identity (S110 0583; mirror of
    /// `pattern_ctors`): the `FQSymbol` under which the referenced `Def`
    /// actually resolved — "whichever storage key HIT" at the typecheck
    /// resolution chokepoint (`design/arch/backend-keyed-consumer.md` §1.1).
    /// It is NOT the written name and NOT a display name: module + the exact
    /// symbol-table key the resolution terminated at (bare `m/f`, canonical
    /// `m/Type.Ctor` for sum ctors, mangled `m/f$Int+Int` for a mono/dispatch
    /// instance, `primitives/add-i64` for a primitive, etc.).
    ///
    /// Keyed by the REFERENCING node's span — `Expr::Var.span` for
    /// value/callee references, `Expr::Apply.span` for dispatch-leg
    /// resolutions that resolve at the `Apply`. Populated by typecheck at the
    /// `infer_var` chokepoint (and dispatch seams); read by
    /// [`crate::MonoExpr::from_expr`] into `MonoExpr::{Var,Apply}.resolved_target`
    /// so the backend performs ONE keyed fetch and never re-resolves a name
    /// (Principle 24 "Resolve once"). Local variables / lambda params are not
    /// table-resolved and carry no entry here.
    #[serde(default)]
    pub resolved_targets: HashMap<Span, FQSymbol>,
}

impl MethodResolutions {
    pub fn new() -> Self {
        Self::default()
    }
}

/// How a function call was resolved by the typechecker.
///
/// `#[non_exhaustive]` per `design/arch/bounded-contexts.md` §7 + crate-root `//!` `#[non_exhaustive]` policy
/// (binding — every public struct/enum in `cranelisp-types` MUST be
/// `#[non_exhaustive]`; the policy intent is extensibility, allowing new
/// variants to be added without breaking consumers). Future variants — e.g.,
/// distinct shapes for platform-effect dispatch, dictionary-passing trait
/// resolution carriers, or speculative-inlining markers — land here without
/// touching the `cargo-public-api` baseline at consumer crates.
///
/// Grounded by:
/// - `design/arch/bounded-contexts.md` §7 + crate-root `//!` `#[non_exhaustive]` policy (binding)
/// - Principle 13 (`interfaces.md` is auditable + `cargo-public-api`-gateable
///   — the attribute is the structural enforcement of evolution discipline)
///
/// Per-variant field documentation: see each variant's struct-variant fields.
/// `TraitMethod` carries `trait_name: FQTraitName` + `impl_type: FQTypeName`
/// per Decision 47 (FQ binding at resolved-stage boundaries — see
/// `design/arch/bounded-contexts.md` §7 "FQTypeName binding").
///
/// Closes S69 Submission 32 (audit finding S-DRIFT-9 + non_exhaustive policy
/// catch-up).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ResolvedCall {
    /// Resolved to a trait method implementation (Ring 2)
    TraitMethod {
        trait_name: FQTraitName,
        method_name: Symbol,
        impl_type: FQTypeName,
        mangled_name: JitSymbol,
        /// The module whose table stores the selected mangled method `Def`
        /// (the impl-WRITER's module — S110 W0.1b,
        /// `design/arch/backend-keyed-consumer.md` §1.1.1). This is the
        /// resolution PRODUCT: `try_resolve_trait_method` reads it off the
        /// `ModuleEntry::TraitImpl` shell that grounds the selected mangle, so
        /// the storage-module carrier (`resolved_targets`) and the `callees`
        /// edge derive the method entry's true home — never `current_module`,
        /// which is wrong for a cross-module trait call (impl written in B,
        /// called from A). Downstream consumers READ this field, never
        /// re-derive. REQUIRED (no `#[serde(default)]`, Principles 18/20).
        impl_module: ModuleFullPath,
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

/// A monomorphised function definition — a thin wrapper over a fully-annotated
/// `Defn`.
///
/// **No side maps (S81 W-G, FIXME 0033).** This type previously carried
/// `resolutions: MethodResolutions` and `expr_types: HashMap<Span, Type>` —
/// Span-keyed side maps materialised by `recheck_body_for_mono`. After the
/// Phase-1 AST-annotation migration those maps are redundant:
/// `monomorphise_call` (in `cranelisp-typecheck::traits`) annotates `defn`
/// in place via `annotate_defn_from_maps` + `apply_subst_to_defn`, so every
/// typed expression carries its `inferred_type` and every `Expr::Apply` /
/// `Expr::Var` carries its `resolved_call` directly on the AST. No consumer
/// read the side maps for information not already on the annotated `defn`:
/// backend codegen reads `mono.defn` (overlaying only the *global*
/// `CheckResult` side maps for legacy scaffolding), and `register_mono_entry`
/// reads `mono.defn` to build the symbol-table entry. The side maps were
/// produced (set to `default()`/empty at construction) but never read —
/// dropping them makes `MonoDefn` a single-field wrapper. Single source of
/// truth (Principle 7): annotations live on the AST, not on a parallel side map.
#[derive(Debug, Clone)]
pub struct MonoDefn {
    pub defn: Defn,
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
/// `kind: DefKind::Constructor { .. }` (see `DefKind::Constructor` rustdoc
/// in `module.rs` and `design/arch/bounded-contexts.md` §7 "Multi-legged
/// authoring"). Field names live on the Def's
/// `param_names`; field types fold into the Def's `scheme` (the constructor's
/// polymorphic function-type signature, e.g., `Some : ∀a. a → Option a`).
///
/// Consumers needing per-ctor metadata walk each name → look up the Def →
/// read the kind discriminator and scheme. No parallel storage; single source
/// of truth.
///
/// **No `docstring` field (S72 Phase B).** The docstring is owned directly by
/// the wrapping `ModuleEntry::TypeDef.docstring` field — single source of
/// truth (Principle 7). Previously `TypeDefInfo.docstring` duplicated /
/// nested the entry's docstring; the entry now owns it canonically and
/// `TypeDefInfo` carries only the type's structural metadata (name,
/// type-parameter binders, constructor names). This parallels the
/// `ModuleEntry::Def` narrowing where `docstring` is a direct entry field,
/// not buried in the embedded AST wrapper.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeDefInfo {
    pub name: FQTypeName,
    pub type_params: Vec<Symbol>,
    pub constructors: Vec<Symbol>,
}

/// Symbol-table-stage trait metadata — the slimmed payload of
/// `ModuleEntry::TraitDecl`.
///
/// **S72 Phase B.** `ModuleEntry::TraitDecl` previously embedded the full
/// frontend AST node `crate::ast::TraitDecl`, which duplicated `visibility`
/// and `docstring` (also carried directly on the entry / on the trait's own
/// AST struct) and dragged the `span: Span` parser coordinate into the
/// runtime symbol-table model. Following the `ModuleEntry::Def` precedent
/// (which carries direct `scheme`/`visibility`/`docstring`/`seq` fields plus
/// a slimmed `ast: Option<DefnVariant>` rather than embedding the full
/// `Defn`), the entry now carries direct `docstring` + `visibility` fields
/// and this slimmed `TraitDeclInfo` payload — only the structural metadata
/// the symbol table actually needs.
///
/// Single source of truth (Principle 7): `docstring` and `visibility` live on
/// the wrapping entry, NOT duplicated here. The frontend AST `TraitDecl`
/// (in `crate::ast`) retains its own `visibility`/`docstring`/`span` — those
/// record what the user wrote at the source layer and are legitimately
/// per-parser-output. The fix is at the symbol-table layer: the entry stops
/// embedding the AST node and stops nesting/duplicating the metadata.
///
/// `methods: Vec<TraitMethodSig>` carries the per-method signatures (name,
/// params, return type, default body, HKT index, span) — the symbol table
/// needs these to resolve trait-method references and typecheck impls against
/// each declared signature (spec §5.4.5).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitDeclInfo {
    // FQTypeName exception 2 (receiver-pinned: payload of ModuleEntry::TraitDecl, keyed local-to-home-module; FQ = FQTraitName::new(home, name))
    pub name: TraitName,
    pub type_params: Vec<Symbol>,
    pub methods: Vec<TraitMethodSig>,
}

// `pub struct ConstructorInfo { ... }` retired — see `DefKind::Constructor`
// rustdoc in `module.rs` and `design/arch/bounded-contexts.md` §7
// "Multi-legged authoring" for the ctor-as-Def shape and the migration map below.
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
