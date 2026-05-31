//! `cranelisp-types` — the universal data substrate for the Cranelisp compiler pipeline.
//!
//! This crate is the **single home for everything that crosses a crate
//! boundary** in the Cranelisp workspace. It depends on nothing inside the
//! workspace, and nothing outside is allowed to invert that direction
//! (Principle 3). Every other compiler crate depends on `cranelisp-types`;
//! `cranelisp-types` depends only on `serde`, `dashmap`, and `std`. The
//! cross-crate bounded context is documented at
//! `design/arch/bounded-contexts.md` §7.
//!
//! # Major surface areas
//!
//! - **Identifier newtypes** ([`Symbol`], [`ModuleName`], [`ModuleFullPath`],
//!   [`TypeName`], [`TraitName`], [`JitSymbol`], [`LinkerSymbol`]) — opaque
//!   string wrappers; the hard rule per `design/arch/CLAUDE.md` §"String
//!   Newtypes" is "never pass bare `String` where any of these is expected".
//! - **Fully-qualified references** ([`FQSymbol`], [`FQTypeName`],
//!   [`FQTraitName`]) — resolved-stage cross-module references. **Binding**
//!   as the cross-crate boundary type for resolved-stage type identifiers,
//!   with two narrow exceptions (syntactic-lift sites at `check_form`;
//!   receiver-pinned helpers where `&self` is the module context).
//! - **Syntactic-stage references** ([`TraitRef`], [`TypeRef`], [`SymbolRef`])
//!   — the `Option<ModuleFullPath>` counterparts to `FQTraitName` /
//!   `FQTypeName` / `FQSymbol` capturing **as-written** qualification before
//!   typecheck lifts to the FQ form. `SymbolRef` is the syntactic-stage
//!   payload for `Pattern::Constructor.name`; resolved-stage `FQSymbol` for
//!   the constructor materialises in `MethodResolutions.pattern_ctors` per
//!   Decision 47.
//! - **AST** ([`Sexp`], [`Expr`], [`Pattern`], [`MatchArm`], [`Defn`],
//!   [`DefnVariant`], [`FieldDef`], [`ConstructorDef`], [`TraitDecl`],
//!   [`TraitImpl`], [`TraitMethodSig`], [`TypeExpr`], [`TopLevel`],
//!   [`Program`], [`Visibility`]) — frontend's structured output;
//!   annotated in-place by typecheck; lowered by backend.
//! - **Resolved type system** ([`Type`], [`Scheme`], [`Subst`], [`TypeId`])
//!   — output of typecheck; consumed by backend.
//! - **Symbol table** ([`SymbolTable`], [`SymbolTables`], [`ModuleEntry`],
//!   [`DefKind`], [`OverloadVariant`], [`ConstrainedFn`],
//!   [`MacroClauseInfo`], [`MacroParam`], [`ImportSpec`], [`ExportSpec`],
//!   [`ImportNames`], [`PlatformSpec`], [`ModDecl`],
//!   [`StructuralDeclEntry`], [`ensure_module_exists`], [`install_module`],
//!   [`EnsureOutcome`], the chain-follow primitives) — THE per-module
//!   store. [`SymbolTables<C, L>`] is the session-level collection
//!   threaded across frontend, typecheck, and the integration layer.
//!   All per-symbol
//!   metadata lives on `ModuleEntry`; structural declarations live as Vec
//!   fields on `SymbolTable`. Generic over `C: CodeStore` (per-function
//!   code carrier) and `L: LinkerStore` (per-module linker carrier);
//!   both default to `()` so crates that don't handle compiled code work
//!   with `SymbolTable<(), ()>` and never see the parameters.
//! - **Module aliases** ([`ModuleAliasEntry`], [`ModuleAliases`]) — the
//!   parallel session-level alias table introduced by spec §8.3.4
//!   (import alias) and §8.4.4 (export mount). Lives at session scope
//!   alongside [`SymbolTables`], keyed by the alias's full path; §8.6.6
//!   qualified-name resolution walks this table by longest-prefix-match.
//!   See `design/arch/bounded-contexts.md` §7 ("Module aliases live at
//!   session level").
//! - **Sealed marker traits** ([`CodeStore`], [`LinkerStore`]) — empty
//!   marker traits with blanket impls per Decision 32. Crates implement
//!   them by virtue of their concrete `C` and `L` satisfying the bounds;
//!   there is no method surface to extend.
//! - **GOT** ([`GotTable`], [`GOT_TABLE_SIZE`]) — per-module Global Offset
//!   Table. Pure data — boxed array of `AtomicPtr<u8>` — with no backend-
//!   specific dependencies. The single source of truth for callable
//!   addresses per S66 post-rollback (`1dc57ae`).
//! - **Typecheck output** ([`MethodResolutions`], [`ResolvedCall`],
//!   [`MonoDefn`], [`TypeDefInfo`], [`TraitDeclInfo`], [`FieldInfo`],
//!   [`DisplayInfo`]) — produced by typecheck (in addition to in-place AST
//!   annotations); consumed by backend.
//! - **Parse-time transients** ([`ParsedEntry`], [`DefmacroInfo`],
//!   [`MacroClause`]) — `cranelisp_frontend::build_form` output consumed
//!   by `cranelisp_typecheck::check_forms`. NEVER lands in `SymbolTable`.
//! - **Heap layout** ([`HeapHeader`], [`NULLARY_TAG_THRESHOLD`]) — the
//!   `#[repr(C)]` header `(alloc_size, rc)` shared between backend codegen
//!   and the intrinsics runtime; offsets are compile-time constants.
//! - **Errors and warnings** ([`CranelispError`], [`PlatformError`],
//!   [`ErrorLocation`], [`LineCol`], [`LineColRange`], [`ResolutionGap`],
//!   [`Warning`], [`WarningKind`]) — every error carries an
//!   `ErrorLocation` per Decision 39; coordinates as data, formatted
//!   downstream by `int`'s display layer.
//! - **Pipeline / orchestration** ([`CodegenBehaviour`],
//!   [`ModuleStrategy`], [`CompileContext`], [`CompileResult`],
//!   [`CallEdge`], [`CallInfo`], [`CallGraph`]) — discrimination + carrier
//!   types threaded between int and backend.
//! - **Marshal tags** ([`TAG_SNIL`], [`TAG_SCONS`], [`TAG_SEXP_INT`] …)
//!   — fixed runtime tag layout for the `Sexp` / `SList` ADTs used by the
//!   macro system. Authoritative constructor order in
//!   `register_macros_module()` in `cranelisp-typecheck::builtins`.
//! - **Scheduling** ([`SchedulingClass`]) — platform-fn classification
//!   used by the IO trampoline and the `bind!` chain compiler.
//! - **View** ([`View`]) — read-only newtype that wraps either two
//!   `&SymbolTable` references (staging + live, cluster mode) or one
//!   (committed mode) per Decision 44; typecheck reads through it.
//! - **Span** ([`Span`]) — byte range in source text; carried on every
//!   AST node and every error.
//!
//! # Cross-cutting invariants
//!
//! - **`#[non_exhaustive]` policy** — every public struct and enum in this
//!   crate is `#[non_exhaustive]`. Adding a variant or field is
//!   non-breaking; consumers cannot exhaustively match or destructure
//!   across crate boundaries. The newtypes (`Symbol`, …) are an
//!   exception — they wrap a single `String` and field access is
//!   structurally prevented by the macro-generated private inner field.
//!   [`SchedulingClass`] is also an exception because it crosses the
//!   platform-DLL C ABI as a `#[repr(u32)]` discriminant — adding a
//!   variant requires a bump of `cranelisp_platform::ABI_VERSION`.
//! - **Newtype discipline** — no bare `String` for anything that names
//!   something in the language. The only bare `String` fields allowed
//!   are error messages, documentation strings, source text, and
//!   user-visible descriptions.
//! - **Module structure** — every submodule is declared `pub(crate)` per
//!   S69 Sub 41 (Principles 13 + 18). The crate-root re-exports below
//!   are the sole public surface; deep paths
//!   (`cranelisp_types::module::SymbolTable`) are not reachable for
//!   consumers.
//! - **Per-entry visibility** — `Visibility` lives once, on the entry.
//!   Every `ModuleEntry` variant carries `visibility: Visibility`; there
//!   is no parallel exports-set sidecar. Cross-module slot lookups
//!   consult the per-entry field directly. Same pattern at adjacent
//!   layers: `ModuleAliasEntry`, form-level `Defn` / `TraitDecl` /
//!   `ModDecl` / `ImportSpec` / `ExportSpec`. See
//!   `design/arch/bounded-contexts.md` §7.
//! - **Cache shape is versioned** — per Decision 34, `SymbolTable.schema_version: u32`
//!   is the canonical version field; cache load checks it before
//!   accepting deserialised state.
//!
//! # Authoritative surface enumeration
//!
//! The full public surface is enumerated at
//! `crates/cranelisp-types/public-api.txt` (regenerated by
//! `cargo public-api` and gated at PR time per
//! `design/arch/CLAUDE.md` §"Baseline-diff discipline").
//!
//! # See also
//!
//! - `design/arch/bounded-contexts.md` §7 — cross-crate types BC statement
//! - `design/arch/principles.md` — architectural principles
//! - `design/arch/CLAUDE.md` — `/arch` operational rules (String Newtypes,
//!   `#[non_exhaustive]` policy, baseline-diff discipline)
//! - `src/CLAUDE.md` — cross-cutting source conventions

// Submodules narrowed to `pub(crate)` per S69 Sub 41 (C-HOLE-6) per
// Principles 13 (interfaces.md auditable; cargo-public-api gateable) +
// 18 (`pub(crate)` defaulting). Crate-root re-exports (further down) are
// the sole public surface; deep paths (`cranelisp_types::module::SymbolTable`)
// are no longer reachable for consumers.
pub(crate) mod span;
pub(crate) mod newtype;
pub(crate) mod error;
pub(crate) mod sexp;
pub(crate) mod ast;
pub(crate) mod types;
pub(crate) mod check;
pub(crate) mod parsed;
// `pub mod code` removed in Sprint 58 Wave 3b (Decision 35): the old
// pointer-only `cranelisp_types::Code` struct dissolves in favour of the
// integration layer's `Code` enum at `src/code.rs`, which carries
// `Arc<Jit>` / `Arc<Linker>` retention roots directly. `cranelisp-types`
// stays ignorant of `cranelift_jit::JITModule` (Principle 3); the
// `SymbolTable<C: CodeStore, L: LinkerStore>` parameterisation is the
// DAG-compatible mechanism that lets the integration layer place its
// `Code` enum on `ModuleEntry::Def.code` without inverting the dependency
// edge.
pub(crate) mod module;
pub(crate) mod got;
pub(crate) mod heap;
pub(crate) mod pipeline;
pub(crate) mod marshal;
pub(crate) mod scheduling;
pub(crate) mod view;

// Tier-2 test-support symbol-table construction helpers. Feature-gated so
// they are visible to OTHER crates' test suites (`cranelisp-typecheck`'s unit
// suite) without entering the production contract: the `public-api.txt`
// baseline is generated WITHOUT `--features test-support`, so `test_support`
// stays out of the frozen edge. Pure `#[cfg(test)]` would be crate-local and
// invisible downstream — hence the feature gate. See
// `design/arch/bounded-contexts.md` §7.
#[cfg(any(test, feature = "test-support"))]
pub mod test_support;

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
    DisplayInfo, FieldInfo, MethodResolutions, MonoDefn, ResolvedCall, TraitDeclInfo, TypeDefInfo,
};
// `ConstructorInfo` retired — see crates/cranelisp-types/src/check.rs for the
// migration map. `CheckResult` and `ReplSnapshot` relocated to
// `cranelisp-typecheck` per FIXME 0100 Phase 1 — single-consumer types live
// with their originating crate (Principle 15). `CheckError` was authored
// directly in `cranelisp-typecheck` per the same FIXME (no transitional
// cranelisp-types home).
// `pub use code::Code` removed in Sprint 58 Wave 3b (Decision 35). See
// the `pub mod code` block above for the rationale; the integration
// layer's `Code` enum at `src/code.rs` is the replacement.
pub use scheduling::SchedulingClass;
pub use module::{
    CHAIN_FOLLOW_DEPTH_LIMIT, CodeStore, ConstrainedFn, DefBuilder, DefKind, EnsureOutcome, ExportSpec,
    ImplSexp, ImportNames, ImportSpec, LinkerStore, MacroClauseInfo, MacroParam, ModDecl,
    ModuleAliasEntry, ModuleAliases, ModuleEntry, OverloadVariant, PlatformSpec,
    StructuralDeclEntry, SymbolTable, SymbolTables, ensure_module_exists, for_each_in_module,
    get_impls_for_type_chain, get_implementing_types_chain, install_module,
    lookup_trait_decl_chain, lookup_type_def_chain, resolve_module_by_name_chain,
    resolve_terminal_entry_and_home,
};
// `PrimitiveKind` enum retired (S69 Submission 36). PlatformEffect promoted
// to its own `DefKind::PlatformEffect { scheduling_class }` sibling variant;
// the prior `Inline` / `Extern` variants were vestigial — see the retirement
// rationale in `module.rs` (block comment where `pub enum PrimitiveKind` used
// to live).
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
    SymbolRef, TraitName, TraitRef, TypeName, TypeRef,
};
