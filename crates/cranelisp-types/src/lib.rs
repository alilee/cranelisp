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
//! - **Type rendering** ([`render_type`], [`PrimitiveNaming`], [`VarNaming`],
//!   [`type_var_names`]) — the single parameterized `Type`-to-string walk
//!   (S87, FIXME 0420), beside `Type`'s `Display` impl. Every renderer in the
//!   workspace delegates to `render_type`; the two config enums select output
//!   convention (`PrimitiveNaming::{Bare, Qualified}`,
//!   `VarNaming::{Numbered, Lettered}`) so a new variant or rendering change
//!   edits one walk, not five (Principles 7 + 15). The dead
//!   `format_type_display` / `format_type_with_vars` free fns retired; their
//!   lettered-var capability lives on as `VarNaming::Lettered`. See
//!   `design/arch/bounded-contexts.md` §7 ("Type rendering").
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
//!   **Callability is structural (S83, FIXME 0356/0357, Principle 20):**
//!   the GOT slot through which an entry is invoked lives on the callable
//!   [`DefKind`] variants ([`UserFnState::Concrete`], [`DefKind::Primitive`],
//!   [`DefKind::Constructor`]) — not as a flat `ModuleEntry::Def` field. A
//!   constrained-fn template ([`ModuleEntry::is_constrained_template`]) is
//!   [`UserFnState::Constrained`], which carries no slot, so it
//!   *structurally cannot* hold a callable address — the once-illegal
//!   pairing is unconstructable. **Generalised in S84 (FIXME 0377):** a slot
//!   ⟺ the def's type is fully concrete (`Type::is_concrete()`), not merely
//!   ⟺ it is unconstrained; a determined-but-non-concrete generic def
//!   ([`UserFnState::Polymorphic`], carrying [`ParametricFn`]) is *also*
//!   slot-less — only its concrete mono instances are callable. The
//!   **callable runtime address** is read
//!   through [`ModuleEntry::callable_got_slot`] (the single read-through
//!   point; trivial since the reshape). The S82 stopgap
//!   (`mark_constrained_template()` flip-and-clear sole-writer +
//!   `assert_well_formed()` phantom-slot guard) is retired. See
//!   `design/arch/bounded-contexts.md` §7 "Callability is structural" and
//!   Principle 20.
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
//! - **Ownership-inference contract** ([`Mode`], [`ModeSummary`],
//!   [`ResultMode`], [`ParamFlow`], [`PrimitiveBody`],
//!   [`ownership_analysis_off`]) — the typecheck→backend memory-model
//!   carrier (S102 CS-A): the mode lattice + per-callable summary riding the
//!   callable [`DefKind`] variants' `mode_summary` slot (read via
//!   [`ModuleEntry::mode_summary`]; ⊤-on-absence accessors live on
//!   `ModeSummary` — the ONE home for conservative reads), advisory site
//!   facts on [`MonoExpr`] alloc/capture/projection nodes, the per-entry
//!   value-use mark, the [`PrimitiveBody`] body/dispatch discriminator
//!   (FIXME 0476 — inline primitives are slot-less by construction;
//!   resolution stops on [`ModuleEntry::is_callable_target`]), and the
//!   read-once `CRANELISP_NO_OWNERSHIP` master toggle. Carrier only — no
//!   analysis logic. See `design/arch/ownership-inference.md` §3.
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
//!   and the intrinsics runtime; offsets are compile-time constants. Plus the
//!   R5 value-representation predicate ([`value_layout`], [`ValueLayout`],
//!   [`VALUE_LAYOUT_MAX_WORDS`]) — the single-sourced Copy/value-layout
//!   verdict both typecheck's `Copy` mode classifier and backend's
//!   `HeapCategory::Value` arm delegate to (soundness-coupled; spine §6.3) —
//!   plus [`type_ctor_names`], the single ctor-name resolver both
//!   `value_layout` and the backend heap classifiers delegate to (FIXME 0528
//!   mirror cure).
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
//! - **Resolution primitive** ([`ResolutionScope`] with its intrinsic prelude
//!   fallback + [`ResolutionScope::resolve`]/[`ResolutionScope::resolve_macro_head`],
//!   the §8.6.4 definition seam [`reject_def_over_binding`],
//!   [`substitute_module_alias`],
//!   [`Resolved`], [`ResolveError`]) — the one query that turns a name into a
//!   resolved symbol-table entry, following imports/reexports, §8.6.6
//!   module-path aliases, visibility, and Principle-17 chain-following. Pure
//!   over `SymbolTables` + `ModuleAliases`; generic over `<C, L>`; no
//!   inference state. The caller supplies the first-hop [`View`] (committed
//!   for int's Pass-1 macro recognition; staging ∪ live for typecheck's
//!   Pass-2/3 body resolution). Consolidates int's former
//!   `SymbolTableMacroResolver` and typecheck's `resolve_*` family onto one
//!   walk. See `bounded-contexts.md` §7 + `interfaces.md` §"Resolution
//!   primitive".
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
pub(crate) mod concrete;
pub(crate) mod mono_expr;
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
pub(crate) mod adt_build;
pub(crate) mod ownership;
pub(crate) mod got;
pub(crate) mod heap;
pub(crate) mod pipeline;
pub(crate) mod marshal;
pub(crate) mod macro_expander;
pub(crate) mod scheduling;
pub(crate) mod view;
pub(crate) mod resolve;

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
pub use types::{Scheme, Subst, Type, TypeId, apply, collect_var_ids_ordered, free_vars, max_type_var_id, render_type, PrimitiveNaming, VarNaming, type_var_names};
// The concrete-only codegen-boundary type (Phase 1 scaffold;
// design/arch/concrete-boundary-type.md). No `Var`/`TyConApp` variant — a
// generic is structurally unrepresentable at the typecheck→backend boundary.
pub use concrete::{ConcreteType, NotConcrete};
// The post-monomorphisation codegen AST (Phase 2a; produces-but-unused).
// `MonoExpr` mirrors `Expr` with `ty: ConcreteType` (non-optional) — a generic
// is structurally unrepresentable on a codegen node. `MonoExpr::from_expr` is the
// fallible builder; its failure is the unified ambiguity / could-not-mono error.
// design/arch/concrete-boundary-type.md §2.4.
pub use mono_expr::{ApplyRef, MonoDefnVariant, MonoExpr, MonoMatchArm, VarRef};
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
// Unified-ABI effect-concurrency layout contracts (ABI v8) — CORE, ungated as of
// the S96 single-ABI cutover (`design/arch/platform-interface.md` §6.8). One
// platform ABI; each effect is blocking or poll-shape via its
// `ConcurrencyDescriptor`. The host *reactor* that drives poll leaves stays
// optional (`cranelisp-intrinsics`'s `concurrency-runtime` feature); these ABI
// *types* are part of every build. See `crates/cranelisp-types/src/scheduling.rs`
// and `design/arch/effect-concurrency.md` §5/§6/§12.
pub use scheduling::{Acquire, ConcurrencyDescriptor, Poll, PollFn, ResourceRole};
pub use module::{
    CHAIN_FOLLOW_DEPTH_LIMIT, CodeStore, ConstrainedFn, DefBuilder, DefKind, EnsureOutcome, ExportSpec,
    GotExhausted,
    ImplSexp, ImportNames, ImportSpec, LinkerStore, MacroClauseInfo, MacroParam, ModDecl,
    ModuleAliasEntry, ModuleAliases, ModuleEntry, OverloadVariant, ParametricFn, PlatformSpec,
    PrimitiveBody, StructuralDeclEntry, SymbolTable, SymbolTables, UserFnState, ensure_module_exists,
    for_each_in_module,
    get_impls_for_type_chain, get_implementing_types_chain, got_data_symbol_name, install_module,
    lookup_trait_decl_chain, lookup_type_def_chain, resolve_module_by_name_chain,
    resolve_terminal_entry_and_home,
};
// ADT-entry builder (S110 R-2, the registration-mirror cure; Principle 24
// "Resolve once"): the ONE derivation of the entry set an ADT registration
// produces — product/sum split, ctor schemes + synthesised `ConstrADT` bodies,
// canonical `member_key(Type, Ctor)` keying + bare-alias edges, the TypeDef.
// Two thin callers: typecheck `adt.rs` (user `deftype`) and int
// `src/bootstrap.rs` (synthetic seeds). Pure — callers keep GOT-slot
// allocation and insertion policy (§8.6.5 contests are typecheck's).
// `design/arch/interfaces.md` §"ADT-entry builder".
pub use adt_build::{AdtCtorSpec, build_adt_entries};
// Ownership-inference carrier types (S102 CS-A) — the typecheck→backend
// memory-model contract: the `Mode` lattice, per-callable `ModeSummary`
// (ABI-bearing `param_modes`/`result` + advisory `param_flow`/`spark_ops`/
// `result_unique`), and the read-once `CRANELISP_NO_OWNERSHIP` master toggle.
// Carrier only — the producing pass is `cranelisp-typecheck`'s
// `pass5_ownership`; consumers are backend emission + the R3 summary-diff
// gate. `design/arch/ownership-inference.md` §3 (spine), BC §7.
pub use ownership::{Mode, ModeSummary, ParamFlow, ResultMode, ownership_analysis_off};
// `PrimitiveKind` enum retired (S69 Submission 36). PlatformEffect promoted
// to its own `DefKind::PlatformEffect { scheduling_class }` sibling variant;
// the prior `Inline` / `Extern` variants were vestigial — see the retirement
// rationale in `module.rs` (block comment where `pub enum PrimitiveKind` used
// to live).
pub use got::GotTable;
pub use heap::HeapHeader;
// R5 value-representation flattening — the single-sourced Copy/value-layout
// predicate consumed by BOTH typecheck's `Copy` mode classifier and backend's
// `HeapCategory::Value` arm (soundness-coupled — a `Copy`-moded param the
// backend did NOT flatten is a UAF; one predicate, both delegate). See
// `design/arch/ownership-inference.md` §6.3 + BC §7.
pub use heap::{VALUE_LAYOUT_MAX_WORDS, ValueLayout, type_ctor_names, value_layout};
// `HeapCategory` relocated to `cranelisp-backend` per S69 Sub 38 — backend-internal
// codegen classification, not a cross-crate substrate. See `facades/backend.md`
// §"Heap classification".
pub use pipeline::{
    CallEdge, CallGraph, CallInfo, CodegenBehaviour, CompileContext, CompileResult,
    GOT_TABLE_SIZE, ModuleStrategy, NULLARY_TAG_THRESHOLD,
};
pub use view::View;
pub use resolve::{
    BindingProvenance, ResolutionScope, Resolved, ResolveError, check_binding_addition,
    bare_member_name, member_key, reject_def_over_binding, substitute_module_alias,
};
pub use macro_expander::{MacroExpander, MacroInvokeError};
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
