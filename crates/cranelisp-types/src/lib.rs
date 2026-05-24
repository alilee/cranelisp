//! cranelisp-types: shared boundary types for the Cranelisp compiler pipeline.
//! See design/arch/interfaces.md for the complete type catalog.

pub mod span;
pub mod newtype;
pub mod error;
pub mod sexp;
pub mod ast;
pub mod types;
pub mod check;
pub mod parsed;
// `pub mod code` removed in Sprint 58 Wave 3b (Decision 35): the old
// pointer-only `cranelisp_types::Code` struct dissolves in favour of the
// integration layer's `Code` enum at `src/code.rs`, which carries
// `Arc<Jit>` / `Arc<Linker>` retention roots directly. `cranelisp-types`
// stays ignorant of `cranelift_jit::JITModule` (Principle 3); the
// `SymbolTable<C: CodeStore, L: LinkerStore>` parameterisation is the
// DAG-compatible mechanism that lets the integration layer place its
// `Code` enum on `ModuleEntry::Def.code` without inverting the dependency
// edge.
pub mod module;
pub mod got;
pub mod heap;
pub mod pipeline;
pub mod marshal;
pub mod scheduling;
pub mod view;

// Re-export key types at crate root for convenience.
pub use span::Span;
pub use error::{
    CranelispError, ErrorLocation, LineCol, LineColRange, PlatformError,
    ResolutionGap, Warning, WarningKind,
};
pub use parsed::{DefmacroInfo, MacroClause, ParsedEntry};
pub use sexp::Sexp;
pub use ast::{
    ConstructorDef, Defn, DefnVariant, Expr, FieldDef, MatchArm, Pattern, Program,
    TopLevel, TraitDecl, TraitImpl, TraitMethodSig, TypeExpr, Visibility, free_vars_expr,
};
pub use types::{Scheme, Subst, Type, TypeId, apply, free_vars, max_type_var_id, format_type_display, format_type_with_vars, type_var_names};
pub use check::{
    DisplayInfo, FieldInfo, MethodResolutions, MonoDefn, ResolvedCall, TypeDefInfo,
};
// `ConstructorInfo` retired — see crates/cranelisp-types/src/check.rs for the
// migration map and facades/types.md §"Symbol table — the single store"
// §"DefKind" for the ctor-as-Def shape.
// `CheckResult` and `ReplSnapshot` relocated to `cranelisp-typecheck` per
// FIXME 0100 Phase 1 — single-consumer types live with their originating
// crate (Principle 15). `CheckError` was authored directly in
// `cranelisp-typecheck` per the same FIXME (no transitional cranelisp-types
// home).
// `pub use code::Code` removed in Sprint 58 Wave 3b (Decision 35). See
// the `pub mod code` block above for the rationale; the integration
// layer's `Code` enum at `src/code.rs` is the replacement.
pub use scheduling::SchedulingClass;
pub use module::{
    CHAIN_FOLLOW_DEPTH_LIMIT, CodeStore, ConstrainedFn, DefKind, EnsureOutcome, ExportSpec,
    ImplSexp, ImportNames, ImportSpec, LinkerStore, MacroClauseInfo, MacroParam, ModDecl,
    ModuleEntry, OverloadVariant, PlatformSpec, StructuralDeclEntry, SymbolTable,
    ensure_module_exists, for_each_in_module, get_impls_for_type_chain,
    get_implementing_types_chain, install_module, lookup_trait_decl_chain, lookup_type_def_chain,
    resolve_module_by_name_chain, resolve_terminal_entry_and_home,
};
// `PrimitiveKind` enum retired (S69 Submission 36). PlatformEffect promoted
// to its own `DefKind::PlatformEffect { scheduling_class }` sibling variant;
// the prior `Inline` / `Extern` variants were vestigial — see the retirement
// rationale in `module.rs` (block comment where `pub enum PrimitiveKind` used
// to live) and `facades/types.md` §"DefKind".
pub use got::GotTable;
pub use heap::HeapHeader;
// `HeapCategory` relocated to `cranelisp-backend` per S69 Sub 38 — backend-internal
// codegen classification, not a cross-crate substrate. See `facades/backend.md`
// §"Heap classification".
pub use pipeline::{
    CallEdge, CallGraph, CallInfo, CodegenBehaviour, CompileContext, CompileResult,
    GOT_TABLE_SIZE, ModuleStrategy, NULLARY_TAG_THRESHOLD,
};
pub use view::View;
pub use marshal::{
    TAG_SNIL, TAG_SCONS,
    TAG_SEXP_INT, TAG_SEXP_FLOAT, TAG_SEXP_BOOL, TAG_SEXP_STR,
    TAG_SEXP_SYM, TAG_SEXP_LIST, TAG_SEXP_BRACKET,
};

// String newtypes and fully-qualified name types
pub use newtype::{
    FQSymbol, FQTraitName, FQTypeName, JitSymbol, LinkerSymbol, ModuleFullPath, ModuleName, Symbol,
    TraitName, TraitRef, TypeName, TypeRef,
};
