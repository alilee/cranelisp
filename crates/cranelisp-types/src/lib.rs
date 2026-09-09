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
//!   [`TraitImpl`], [`UnresolvedTraitMethodSig`], [`TraitMethodSig`],
//!   [`TraitMethodKind`], [`TypeExpr`], [`TopLevel`],
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
//! - **Symbol table** ([`SymbolTable`], [`SymbolTables`], [`Binding`],
//!   [`NameCandidate`], [`Decl`], [`Callable`], [`CallableArm`],
//!   [`OverloadedCallable`], [`MacroDeclaration`], [`MacroClause`],
//!   [`CallableTarget`], [`Life`], [`CallableOrigin`], [`Realization`], [`MacroParam`],
//!   [`ImportSpec`], [`ExportSpec`], [`ImportNames`], [`PlatformSpec`], [`ModDecl`],
//!   [`ensure_module_exists`], [`install_module`],
//!   [`EnsureOutcome`], the chain-follow primitives) — THE per-module
//!   store. Each private per-spelling entry contains an optional canonical
//!   binding and terminal candidate references. Callable lifecycle transitions
//!   are enforced by `SymbolTable` funnels. The symbols map
//!   is private; free reads use lookup and iterator projections. Structural
//!   declaration Vec fields (`imports`/`exports`/`platforms`/
//!   `submodules`) are `pub` and ARE the append contract (direct push,
//!   source/authorship order, no dedup — FIXME 0918 resolved the Decision-39
//!   carrier question by deleting the unused enum carrier). [`SymbolTables<C, L>`] is the session-level collection
//!   threaded across frontend, typecheck, and the integration layer.
//!   Generic over `C: CodeStore` (per-function
//!   code carrier) and `L: LinkerStore` (per-module linker carrier);
//!   both default to `()` so crates that don't handle compiled code work
//!   with `SymbolTable<(), ()>` and never see the parameters.
//!   **Callability is structural:** only [`Life::Concrete`] and
//!   [`Life::Broken`] carry a [`CallableSlot`]; [`Life::Template`],
//!   [`Life::Declared`], [`Life::Inline`] and [`Life::HostPromised`] cannot.
//!   Allocation derives from live claims plus [`RetiredSlot`] tombstones, and
//!   [`SymbolTable::validate_lifecycle`] rechecks restored state.
//! - **Module aliases** ([`ModuleAliasEntry`], [`ModuleAliases`]) — the
//!   parallel session-level alias table introduced by spec §8.3.4
//!   (import alias) and §8.4.4 (export mount). Lives at session scope
//!   alongside [`SymbolTables`], keyed by the alias's full path; §8.6.6
//!   qualified-name resolution walks this table with scoped keyed probes.
//!   See `design/arch/bounded-contexts.md` §7 ("Module aliases live at
//!   session level").
//! - **Sealed marker traits** ([`CodeStore`], [`LinkerStore`]) — empty
//!   marker traits with blanket impls per Decision 32. Crates implement
//!   them by virtue of their concrete `C` and `L` satisfying the bounds;
//!   there is no method surface to extend.
//! - **Ownership-inference contract** ([`Mode`], [`ModeSummary`],
//!   [`ResultMode`], [`ParamFlow`],
//!   [`ownership_analysis_off`]) — the typecheck→backend memory-model
//!   carrier: the mode lattice plus per-callable summary riding
//!   [`Life::Concrete`] (read via [`Binding::mode_summary`]); ⊤-on-absence accessors live on
//!   `ModeSummary` — the ONE home for conservative reads), advisory site
//!   facts on [`MonoExpr`] alloc/capture/projection nodes, the per-entry
//!   value-use mark, and the
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
//!   R5 value-representation predicate ([`value_layout`],
//!   [`value_layout_with_lookup`], [`ValueLayout`],
//!   [`VALUE_LAYOUT_MAX_WORDS`]) — the single-sourced Copy/value-layout
//!   verdict both typecheck's `Copy` mode classifier and backend's
//!   `HeapCategory::Value` arm delegate to (soundness-coupled; spine §6.3) —
//!   with a lookup input for staged declarations or a table adapter for codegen.
//!   [`type_ctor_names`] and the layout walk share one constructor-key
//!   projection, also consumed by the backend heap classifiers. The
//!   instantiation-substituting ctor-field projection
//!   ([`ctor_field_types_at`], [`CtorFieldsAtError`]) — concrete-or-refuse,
//!   never fabricating (S119; register rows R-6/R-16).
//! - **Errors and warnings** ([`CranelispError`], [`PlatformError`],
//!   [`ErrorLocation`], [`LineCol`], [`LineColRange`], [`ResolutionGap`],
//!   [`Warning`], [`WarningKind`]) — every error carries an
//!   `ErrorLocation` per Decision 39; coordinates as data, formatted
//!   downstream by `int`'s display layer.
//! - **Pipeline / orchestration** ([`CodegenBehaviour`],
//!   [`ModuleStrategy`], [`CompileContext`]) — discrimination + carrier
//!   types threaded between int and backend. (The former `CompileResult` +
//!   `CallEdge`/`CallInfo`/`CallGraph` cluster was zero-consumer dead surface,
//!   deleted S119 per FIXME 0918 — the live call-graph mechanism is the
//!   per-callable lifecycle `callees` field, Decision 21.)
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
//!   fallback + [`ResolutionScope::resolve_candidates`]/[`ResolutionScope::resolve`]/
//!   [`ResolutionScope::resolve_macro_head`],
//!   [`substitute_module_alias`],
//!   [`Resolved`], [`ResolveError`]) — the one query that turns a name into a
//!   terminal candidate set, applying §8.6.6 module-path aliases and
//!   visibility. Pure
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
//! - **Exhaustiveness policy** — extensible public payload records are
//!   `#[non_exhaustive]`; in particular, lifecycle records are constructed
//!   through their role-specific constructors or [`SymbolTable`] funnels.
//!   [`NameCandidate`] is a read-only DTO: consumers inspect its fields but
//!   author exposures only through the table facade.
//!   Deliberately closed vocabulary sums remain exhaustive so a new state
//!   breaks every consumer match: [`Decl`],
//!   [`TypeRecord`], [`Life`], [`TemplateBody`], [`TemplateKind`],
//!   [`CallableOrigin`], [`Realization`], [`RetireReason`], [`AdtEntrySpec`],
//!   [`QuoteHead`], [`VarRef`], [`ApplyRef`], and [`ViewBuildError`]. The
//!   ownership-mode vocabulary and `#[repr(C)]`/`#[repr(u32)]` ABI types are
//!   likewise closed because exhaustive matching and stable layout are their
//!   safety contracts. String newtypes and [`View`] need no
//!   `#[non_exhaustive]`: their fields are already private.
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
//!   Every [`Binding`] carries `visibility: Visibility`; there
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
pub(crate) mod ast;
pub(crate) mod check;
pub(crate) mod concrete;
pub(crate) mod error;
pub(crate) mod mono_expr;
pub(crate) mod newtype;
pub(crate) mod parsed;
pub(crate) mod sexp;
pub(crate) mod span;
pub(crate) mod types;
// `pub mod code` removed in Sprint 58 Wave 3b (Decision 35): the old
// pointer-only `cranelisp_types::Code` struct dissolves in favour of the
// integration layer's `Code` enum at `src/code.rs`, which carries
// `Arc<Jit>` / `Arc<Linker>` retention roots directly. `cranelisp-types`
// stays ignorant of `cranelift_jit::JITModule` (Principle 3); the
// `SymbolTable<C: CodeStore, L: LinkerStore>` parameterisation is the
// DAG-compatible mechanism that lets the integration layer place its
// `Code` enum on `Realization::Body.code` without inverting the dependency
// edge.
pub(crate) mod adt_build;
pub(crate) mod got;
pub(crate) mod heap;
pub(crate) mod lifecycle;
pub(crate) mod macro_expander;
pub(crate) mod marshal;
pub(crate) mod module;
pub(crate) mod ownership;
pub(crate) mod pipeline;
pub(crate) mod resolve;
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
pub use ast::{
    ConstructorDef, Defn, DefnVariant, Expr, FieldDef, MatchArm, Pattern, Program, TopLevel,
    TraitDecl, TraitImpl, TraitMethodKind, TraitMethodSig, TypeExpr, UnresolvedTraitMethodSig,
    Visibility, free_vars_expr,
};
pub use error::{
    CranelispError, ErrorLocation, LineCol, LineColRange, PlatformError, ResolutionGap, Warning,
    WarningKind,
};
pub use parsed::{DefmacroInfo, MacroClause as ParsedMacroClause, ParsedEntry};
pub use sexp::{QuoteHead, Sexp, quote_head};
pub use span::Span;
pub use types::{
    PrimitiveNaming, Scheme, Subst, Type, TypeId, VarNaming, apply, collect_var_ids_ordered,
    free_vars, max_type_var_id, render_type, type_var_names,
};
// The concrete-only codegen-boundary type (Phase 1 scaffold;
// design/arch/concrete-boundary-type.md). No `Var`/`TyConApp` variant — a
// generic is structurally unrepresentable at the typecheck→backend boundary.
pub use concrete::{ConcreteType, NotConcrete};
// The post-monomorphisation codegen AST (Phase 2a; produces-but-unused).
// `MonoExpr` mirrors `Expr` with `ty: ConcreteType` (non-optional) — a generic
// is structurally unrepresentable on a codegen node. `MonoExpr::from_expr` is the
// fallible builder; its failure is the unified ambiguity / could-not-mono error.
// design/arch/concrete-boundary-type.md §2.4.
pub use check::{
    DisplayInfo, FieldInfo, MethodResolutions, MonoDefn, ResolvedCall, TraitDeclInfo, TypeDefInfo,
};
pub use mono_expr::{
    ApplyRef, MonoDefnVariant, MonoExpr, MonoMatchArm, VarRef, ViewBuildError,
    is_strict_type_concrete,
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
pub use lifecycle::{
    Binding, BrokenProvenance, Callable, CallableArm, CallableArmDraft, CallableArmId,
    CallableArmSettlement, CallableOrigin, CallableTarget, ConstrainedMeta, Decl, ImplShell,
    InstanceLink, Life, LifecycleError, MacroClause, MacroClauseDraft, MacroDeclaration,
    MonoDemand, NameCandidate, OverloadArm, OverloadedCallable, Realization, RetireReason,
    RetiredSlot, SpecialFormRecord, SynthSpec, TemplateBody, TemplateKind, TraitMethodRecord,
    TraitRecord, TypeRecord,
};
pub use module::{
    BrokenTransition, CHAIN_FOLLOW_DEPTH_LIMIT, CallablePublicationRecord, CallableSlot, CodeStore,
    CompiledOwnerRejection, CompiledPublicationRejection, EnrolOutcome, EnsureOutcome, ExportSpec,
    GotExhausted, ImportNames, ImportSpec, LinkerStore, MacroParam, ModDecl, ModuleAliasEntry,
    ModuleAliases, PlatformSpec, PublicationRecord, RetainedCallables, SlotMintError,
    StagedImplShell, StagedPublicationDecision, SymbolTable, SymbolTables, WrittenTraitImpl,
    drop_glue_symbol_name, enrol_written_trait_impl, ensure_module_exists, for_each_in_module,
    get_implementing_types_chain, get_impls_for_type_chain, got_data_symbol_name, install_module,
    lookup_trait_decl_chain, lookup_type_def_chain, resolve_module_by_name_chain,
    resolve_terminal_entry_and_home,
};
pub use scheduling::{Acquire, ConcurrencyDescriptor, Poll, PollFn, ResourceRole};
// ADT-entry builder (S110 R-2, the registration-mirror cure; Principle 24
// "Resolve once"): the ONE derivation of the entry set an ADT registration
// produces — product/sum split, ctor schemes + synthesised `ConstrADT` bodies,
// canonical `member_key(Type, Ctor)` keying + bare-alias edges, the TypeDef.
// Two thin callers: typecheck `adt.rs` (user `deftype`) and int
// `src/bootstrap.rs` (synthetic seeds). Pure and slotless — callers settle
// callable recipes through the table funnels and keep §8.6.5 contest policy.
// `symbol-table-lifecycle.md` §5.8 controls the lifecycle bridge; the older
// raw-slot wording in `interfaces.md` awaits standing-document reconciliation.
pub use adt_build::{AdtCallableSpec, AdtCtorSpec, AdtEntrySpec, build_adt_entries};
// Ownership-inference carrier types (S102 CS-A) — the typecheck→backend
// memory-model contract: the `Mode` lattice, per-callable `ModeSummary`
// (ABI-bearing `param_modes`/`result` + advisory `param_flow`/`spark_ops`/
// `result_unique`), and the read-once `CRANELISP_NO_OWNERSHIP` master toggle.
// Carrier only — the producing pass is `cranelisp-typecheck`'s
// `pass5_ownership`; consumers are backend emission + the R3 summary-diff
// gate. `design/arch/ownership-inference.md` §3 (spine), BC §7.
pub use ownership::{Mode, ModeSummary, ParamFlow, ResultMode, ownership_analysis_off};
// `PrimitiveKind` enum retired (S69 Submission 36). PlatformEffect promoted
// to its own `CallableOrigin::PlatformEffect { scheduling_class }` record;
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
pub use heap::{
    VALUE_LAYOUT_MAX_WORDS, ValueLayout, type_ctor_names, value_layout, value_layout_with_lookup,
};
// The substituting ctor-field projection (S119 types-first slice; register
// rows R-6/R-16): field types of a ctor AT a concrete instantiation, or a
// refusal — the only legal derivation of instantiated ctor-field types for
// category/glue purposes (the backend's hand-rolled walk retires onto it in
// the S120 wash). Beside the preserved declaration-side model site
// (`value_layout`'s `ctor_field_concrete_types` interior).
pub use heap::{CtorFieldsAtError, ctor_field_types_at};
// `HeapCategory` relocated to `cranelisp-backend` per S69 Sub 38 — backend-internal
// codegen classification, not a cross-crate substrate (canonical home: BC §3 +
// the backend source rustdoc; the per-crate facade specs are retired).
pub use macro_expander::{MacroExpander, MacroInvokeError};
pub use marshal::{
    TAG_SCONS, TAG_SEXP_ANNOTATED, TAG_SEXP_BOOL, TAG_SEXP_BRACKET, TAG_SEXP_FLOAT, TAG_SEXP_INT,
    TAG_SEXP_LIST, TAG_SEXP_STR, TAG_SEXP_SYM, TAG_SNIL,
};
pub use pipeline::{
    CodegenBehaviour, CompileContext, GOT_TABLE_SIZE, ModuleStrategy, NULLARY_TAG_THRESHOLD,
};
pub use resolve::{
    ResolutionScope, ResolveError, Resolved, bare_member_name, member_key, module_alias_key,
    substitute_module_alias, trait_impl_key,
};
pub use view::View;

// String newtypes and fully-qualified name types
pub use newtype::{
    FQSymbol, FQTraitName, FQTypeName, JitSymbol, LinkerSymbol, ModuleFullPath, ModuleName, Symbol,
    SymbolRef, TraitName, TraitRef, TypeName, TypeRef,
};
