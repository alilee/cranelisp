use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::{Arc, Mutex};

use crate::{
    Binding, Callable, CallableArm, CallableArmDraft, CallableArmId, CallableArmSettlement,
    CallableOrigin, CallableTarget, ConcreteType, Decl, DefnVariant, FQSymbol, FQTraitName,
    FQTypeName, GOT_TABLE_SIZE, GotTable, ImplShell, InstanceLink, Life, LifecycleError,
    LinkerSymbol, MacroClause, MacroClauseDraft, MacroDeclaration, ModeSummary, ModuleFullPath,
    ModuleName, MonoDefnVariant, NameCandidate, NotConcrete, OverloadedCallable, Realization,
    RetireReason, RetiredSlot, SchedulingClass, Scheme, Sexp, Span, Symbol, TemplateBody,
    TemplateKind, TraitDeclInfo, TraitMethodRecord, TraitName, Type, TypeDefInfo, TypeId, TypeName,
    Visibility,
};

// --- CodeStore / LinkerStore marker traits (Sprint 58 Wave 3a; Decision 32) ---

/// Empty marker trait for the per-function compiled-code store carried on
/// `Realization::Body.code`.
///
/// This trait is method-free by design (Decision 32). The integration layer
/// chooses the concrete type for `C` (per Decision 35: `Code` enum unifying
/// `Code::Jit { Arc<Jit>, ptr }` and `Code::Linker { Arc<Linker>, ptr }`),
/// and methods that compile, evict, or reclaim code go on the concrete type
/// in the integration layer or `cranelisp-backend`. `cranelisp-types` MUST
/// stay ignorant of `cranelift_jit::JITModule` and the linker — the empty
/// marker is the type-system handle that lets `SymbolTable<C, L>` carry
/// the parameterisation without inverting the dependency edge that
/// Principle 3 protects (`cranelisp-types → cranelisp-backend` is forbidden).
///
/// The blanket `impl<T: Clone + Send + Sync + 'static> CodeStore for T` means any
/// `Clone + Send + Sync + 'static` type the integration layer wants to use as `C`
/// automatically satisfies the bound — no per-call-site `impl` line needed.
/// `()` trivially satisfies it (zero-sized, Clone + Send + Sync + 'static), which
/// is why it works as the default for crates that don't handle compiled
/// code (typecheck, frontend, the bulk of backend).
///
/// See Decision 32 (label index `design/arch/decisions/README.md`) and Decision 35
/// (the integration layer's `Code` enum) and Decision 31 (per-redefinition
/// JIT reclaim — the behavioural payoff this enables).
pub trait CodeStore: Clone + Send + Sync + 'static {}
impl<T: Clone + Send + Sync + 'static> CodeStore for T {}

/// Empty marker trait for the per-module linker store carried on
/// `SymbolTable.linker`.
///
/// Same shape as `CodeStore` but kept distinct so `SymbolTable<C, L>` has
/// two independent type parameters (per-function reclaim and per-module
/// reclaim are separate concerns; cache-restore can supply a `Linker`
/// without supplying a `Code` shape, and vice versa). Per Decision 35,
/// the current integration-layer choice is `L = ()` because per-symbol
/// `Code::Linker.linker: Arc<Linker>` retention covers the only case where
/// a Linker needs to outlive its construction; `L` is reserved for future
/// expansion if a Linker must be retained without any `Code::Linker`
/// referencing it.
///
/// See Decision 32 (label index `design/arch/decisions/README.md`) and Decision 35
/// (`L = ()` rationale).
pub trait LinkerStore: Clone + Send + Sync + 'static {}
impl<T: Clone + Send + Sync + 'static> LinkerStore for T {}

/// Integration's semantic choice for publishing or retiring a slotted live
/// callable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StagedPublicationDecision {
    /// Rebind a slotted staged replacement to the prior published slot.
    PreserveAbi {
        /// Staged binding to publish.
        symbol: Symbol,
    },
    /// Retire the prior slot, either minting a fresh slot for a slotted staged
    /// replacement or removing the live binding when this key is wholly absent
    /// from staging.
    ChangeAbi {
        /// Live binding whose prior ABI generation is retired.
        symbol: Symbol,
    },
}

/// Types-owned facts produced by one committed publication or retirement
/// action.
#[non_exhaustive]
#[must_use = "displaced compiled owners must be retained before publication completes"]
pub struct PublicationRecord<C: CodeStore = ()> {
    /// Table key affected by the publication action.
    pub symbol: Symbol,
    /// Whether a callable binding previously occupied this key.
    pub prior_was_callable: bool,
    /// Per-body target, slot, and owner movements committed for this binding.
    pub bodies: Vec<CallablePublicationRecord<C>>,
}

/// Types-owned facts for one callable body affected by publication.
#[non_exhaustive]
#[must_use = "a displaced compiled owner must be retained"]
pub struct CallablePublicationRecord<C: CodeStore = ()> {
    /// Execution target displaced by this movement, when one existed.
    pub prior_target: Option<CallableTarget>,
    /// Execution target installed by this movement, when one exists.
    pub published_target: Option<CallableTarget>,
    /// Slot claimed by the displaced body generation, when any.
    pub prior_slot: Option<CallableSlot>,
    /// Slot claimed by the published body generation, when any.
    pub published_slot: Option<CallableSlot>,
    /// Runtime body owner displaced by publication, when any.
    pub displaced_owner: Option<C>,
}

/// Refusal which returns the compiled owner submitted for publication.
#[must_use = "the rejected compiled owner must be recovered with into_parts"]
pub struct CompiledOwnerRejection<C: CodeStore = ()> {
    reason: LifecycleError,
    owner: C,
}

impl<C: CodeStore> CompiledOwnerRejection<C> {
    /// Inspect why the current lifecycle state refused the owner.
    pub fn reason(&self) -> &LifecycleError {
        &self.reason
    }

    /// Recover both the refusal and the submitted owner.
    pub fn into_parts(self) -> (LifecycleError, C) {
        (self.reason, self.owner)
    }
}

/// Refusal which returns every compiled owner submitted with a staged module
/// publication.
#[must_use = "rejected compiled owners must be recovered with into_parts"]
pub struct CompiledPublicationRejection<C: CodeStore = ()> {
    reason: LifecycleError,
    compiled_owners: HashMap<CallableTarget, C>,
}

impl<C: CodeStore> CompiledPublicationRejection<C> {
    /// Inspect why the staged publication was refused.
    pub fn reason(&self) -> &LifecycleError {
        &self.reason
    }

    /// Recover both the refusal and every submitted compiled owner.
    pub fn into_parts(self) -> (LifecycleError, HashMap<CallableTarget, C>) {
        (self.reason, self.compiled_owners)
    }
}

/// Result of moving a concrete callable into its retained-slot broken state.
#[non_exhaustive]
#[must_use = "the displaced compiled owner and retained slot must be handled"]
pub struct BrokenTransition<C: CodeStore = ()> {
    /// Slot retained by the broken callable.
    pub slot: CallableSlot,
    /// Runtime body owner displaced by the transition, when any.
    pub displaced_owner: Option<C>,
}

// --- Symbol Table ---

/// Per-module symbol table.
///
/// Mostly pure data (types, schemes, docstrings) with two runtime-only
/// fields: `got` (the per-module Global Offset Table) and `linker`. The GOT
/// holds code pointers that codegen writes and JIT-emitted call sites read;
/// it is `#[serde(skip)]` so cache files stay pointer-free and re-initialise
/// to a fresh null table on deserialise.
///
/// Owned by the **session**: the integration layer constructs the per-session
/// `SymbolTables<Code, ()>` collection (`SharedState.symbol_tables`) at
/// startup and threads it as a shared reference into typecheck (which reads
/// and writes entries through its orchestrator accessors) and backend (which
/// reads type information and writes GOT slots atomically per-slot through
/// `got.store_slot`).
///
/// **GOT slots.** Slot indices are module-local, allocated from the
/// live lifecycle claims and retired-slot tombstones. The private callable
/// mint refuses non-concrete schemes and returns the [`CallableSlot`] witness
/// carried only by slotted lifecycle states.
///
/// Structural declarations (`imports`, `exports`, `platforms`, `submodules`)
/// retain the *original specification* of the module's `(import …)` /
/// `(export …)` / `(platform …)` / `(mod …)` forms — the per-symbol
/// per-spelling `NameCandidate` references are the resolved effects of imports.
/// (Decision 33, Sprint 58; the pre-S58 `ModuleStructure` parallel store is
/// long dissolved into these fields.)
///
/// Generic over `C: CodeStore` (per-function compiled-code store carried by
/// [`Realization::Body`]) and `L: LinkerStore` (per-module linker store
/// carried on `linker`). Both default to `()` so crates that don't handle
/// compiled code (typecheck, frontend, the bulk of backend) work with
/// `SymbolTable` (i.e. `SymbolTable<(), ()>`) and never see the parameters
/// in their signatures. The integration layer instantiates
/// `SymbolTable<Code, ()>` (or similar) in `src/session_v4.rs` (per
/// Decision 35). See Decision 32 for the trait shape and the
/// `pipeline-v4.md` §9.1 normative shape.
///
/// **Serde discipline.** The `linker: Option<L>` field is `#[serde(skip)]`
/// (runtime state), and `code: Option<C>` on [`Realization::Body`] is also
/// `#[serde(skip)]`. The explicit `#[serde(bound = "")]` on the derive
/// suppresses the auto-generated `C: Serialize + Deserialize` and
/// `L: Serialize + Deserialize` bounds that the derive would otherwise
/// emit; without it, even skipped fields' type parameters get
/// trait-bound on serialise/deserialise. `()` trivially implements
/// neither (the marker traits are empty), so omitting the bounds keeps
/// the derive sound for the `()` default and for any concrete `C` /
/// `L` the integration layer chooses.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct SymbolTable<C: CodeStore = (), L: LinkerStore = ()> {
    pub path: ModuleFullPath,
    /// Module-level documentation — the **module preamble** (spec §8.16).
    ///
    /// The module analogue of a callable/facet docstring, but documenting the module **as a whole**
    /// rather than a named symbol — so it lives here on the per-module table,
    /// off the symbol axis entirely (a synthetic binding was rejected:
    /// it would force a fake name into `symbols` and leak into export/import
    /// enumeration — see `bounded-contexts.md` §7).
    ///
    /// `None` for a module with no leading comment block — the common, valid
    /// case (a preamble is purely additive, like the optional prelude, spec
    /// §8.16 / §8.8.3); `Some(text)` carries the preamble text when present.
    /// The stored text is the file's contiguous leading `;;` comment block
    /// with each line's `;;` (or `;`) marker and one following space stripped,
    /// the lines newline-joined (spec §8.16.2). A bare `String` is the correct
    /// carrier: it is documentation text — one of the explicitly-allowed
    /// bare-`String` uses (`design/arch/CLAUDE.md` §"String Newtypes"),
    /// alongside docstrings / source text — so no newtype is warranted.
    ///
    /// **Populated by the frontend reader, not constructed here.** Every
    /// construction site defaults this to `None`; the reader surfaces the
    /// leading comment block (via `Sexp::Comment` preservation, §8.16.3) and
    /// sets it later. The §8.16.5 byte-stable source-regen round-trip re-emits
    /// `Some(text)` verbatim as the leading comment block.
    ///
    /// `#[serde(default)]` so caches written before this field existed
    /// deserialise cleanly as `None`.
    #[serde(default)]
    pub module_preamble: Option<String>,
    symbols: HashMap<Symbol, SymbolEntry<C>>,
    /// Published slot indices that no live binding claims any longer.
    ///
    /// Allocation scans live claims and these tombstones, so a displaced slot
    /// is never reissued to a different callable.
    retired_slots: Vec<RetiredSlot>,
    /// Monotonic per-entry sequence allocator. Every newly-inserted
    /// callable declaration receives `seq = next_seq` and the field is bumped.
    /// Used by `regenerate_backing_file` to emit defns in authorship order
    /// per `repl/spec.md` §15.4(2). Redefinition does NOT reorder:
    /// `insert_or_update` (consumer-side, in `int`) preserves the existing
    /// entry's `seq` value alongside Decision 31's `code` carry-forward.
    /// Replaces the prior `defn_order: Vec<Symbol>` side-table (Decision 39
    /// design upgrade — eliminates side-table drift, matches the
    /// former `next_got_slot` allocation pattern).
    ///
    /// Plain `u64` mutated under the ordinary `&mut SymbolTable` discipline
    /// (the former cursor used the same discipline). This IS the end-state. The former
    /// "facade target: `AtomicU64` / DashMap-inner concurrency cascade"
    /// narrative (S-DRIFT-19/20/21) was formally RETRACTED at S119 (FIXME
    /// 0919; BC §7 records the retraction): per-module writes are serialized
    /// by the DashMap shard guard the orchestrator already holds, so the
    /// atomic-field conversion buys nothing the access pattern needs.
    ///
    /// `#[serde(default)]` so pre-existing caches deserialise as `0` and the
    /// loader re-derives the high-water mark from the maximum `seq` across
    /// loaded entries (consumer-side reconstruction).
    #[serde(default)]
    pub next_seq: u64,
    /// Per-module Global Offset Table. Created when the `SymbolTable` is
    /// constructed (at module registration). Base address is stable for
    /// the module's lifetime. Slot indices are assigned by
    /// settlement/install funnels; code pointers are written atomically by
    /// codegen workers and read by JIT-emitted call sites.
    ///
    /// Wrapped in `Arc` so codegen workers can hold a cheap handle to the
    /// GOT while the `DashMap` read guard is released. Cloning a
    /// `SymbolTable` shares the same underlying GOT via refcount bump — the
    /// GOT is runtime state, not copied data.
    ///
    /// Not serialised: cache reconstruction creates a fresh GOT and
    /// re-populates slot pointers during cache-hit codegen.
    #[serde(skip, default = "default_got_arc")]
    pub got: std::sync::Arc<GotTable>,

    // --- Structural declarations (Sprint 58 Step 5a; Decision 33) ---
    /// User-authored form-level record of `(import …)` declarations in source
    /// order. This is the regeneration source-of-truth (see
    /// `src/save.rs::generate_imports`, spec §6.4); compiler-injected imports
    /// (e.g., the implicit `(import [prelude [*]])` injection) do NOT appear
    /// here. The **effective import set** (per-name resolved bindings) lives
    /// on per-spelling candidate references (`visibility` discriminates
    /// private `(import …)`-edge from public `(export [foreign-sym])`-edge
    /// the private `(import …)` edge from a public re-export edge).
    /// Resolution never walks this form-record: cross-module reachability is
    /// answered per-name by chain-following the per-symbol alias entries
    /// (Principle 17 — closure walks over the import graph are forbidden; the
    /// former `transitive_import_closure` helper is deleted).
    ///
    /// Append-only during the form-by-form classification pass; insertion
    /// order MUST match source order. No deduplication: duplicate `(import …)`
    /// forms within one module produce two entries (the resolver issues a
    /// duplicate-import warning based on this structural record). Per-module:
    /// `imports` on module A's table contains only forms that appeared
    /// lexically in A's source. See `design/typecheck/ast-annotation.md` §11.3
    /// for the full invariants.
    ///
    /// Writer: `/int` (in `src/worker.rs` form-handlers; not typecheck-crate
    /// code). Reader: import-resolver (`crates/cranelisp-typecheck/src/imports.rs`),
    /// `.cl` regenerator (`src/save.rs`).
    #[serde(default)]
    pub imports: Vec<ImportSpec>,
    /// Original `(export [names...])` declarations in source order. Same
    /// append-only / no-dedup discipline as `imports`. See §11.3.
    #[serde(default)]
    pub exports: Vec<ExportSpec>,
    /// Original `(platform "name")` declarations in source order. Same
    /// append-only / no-dedup discipline as `imports`. Consumed by `/int` and
    /// `/platform` (NOT by typecheck — see §11.5).
    #[serde(default)]
    pub platforms: Vec<PlatformSpec>,
    /// Original `(mod child)` / `(mod- child)` declarations in source order;
    /// `visibility == Visibility::Private` distinguishes `(mod-)`. Consumed
    /// by `/int` for submodule loading.
    #[serde(default)]
    pub submodules: Vec<ModDecl>,

    // --- Written-impl cache carrier (S119, FIXME 0869; trait-impl-cache-carrier.md) ---
    /// Trait impls **this module wrote** — the writer-side persistence
    /// projection of the `Decl::ImplShell` discovery shells that fresh
    /// registration placed in each trait's HOME module (Decision 45 as
    /// amended S110). The trait home's own sidecar cannot reliably carry
    /// impls other modules wrote into it (snapshot-ordering/cache-hit races —
    /// `design/arch/trait-impl-cache-carrier.md` §1), so the durable home is
    /// the causal producer: restoration re-derives each shell from this
    /// record via [`enrol_written_trait_impl`] after the writer's dependency
    /// closure installs.
    ///
    /// Upserted by typecheck at the successful `register_trait_impl` seam,
    /// from the same single-source values as the staged shell (one derivation,
    /// two carriers; Principles 24/26). Fresh registration retains the writer's
    /// methods and stages the trait-home shell first; only after every method
    /// checks and settles does it upsert this record as the final fallible table
    /// act, then commit both tokens. Failure rolls methods and shell back without
    /// changing the prior writer record. Vec order is registration order
    /// (deterministic from source; keeps `.meta.json` byte-reproducible).
    ///
    /// **Deliberately NO `#[serde(default)]`** (the schema-22
    /// typed-resolution-carrier precedent): post-bump, absence is a hard
    /// serde error, never a silently-empty default — a default-empty read of
    /// a pre-carrier sidecar would silently reproduce the 0869 defect. Its
    /// addition is a serde shape change: `CACHE_SCHEMA_VERSION` 23→24 rides
    /// this change-set (the ONE S119 window).
    pub written_trait_impls: Vec<WrittenTraitImpl>,

    /// Modules whose tables answered a qualified reference while this module
    /// compiled (`design/arch/interfaces.md` §Qualified lookup dependencies).
    /// Private so the set is insert-only: it has no removal and is rebuilt
    /// only when the module's table is rebuilt from source.
    ///
    /// **Deliberately no `#[serde(default)]`**: an empty default for a
    /// pre-carrier sidecar would under-key cache validity, so absence is a
    /// decode error.
    lookup_dependencies: BTreeSet<ModuleFullPath>,

    // --- Cache schema version (Sprint 58 Step 5b; Decision 34) ---
    /// Schema version of the serialised symbol table. Bumped on every
    /// shape-changing field addition / deletion / type change (additions of
    /// `#[serde(default)]` fields whose default matches a fresh-build value
    /// do NOT require a bump; explicit-default field additions, deletions,
    /// and type changes DO require a bump).
    ///
    /// Cache-load reads this first; mismatch with the current
    /// `CACHE_SCHEMA_VERSION` constant (defined in
    /// `crates/cranelisp-backend/src/cache/mod.rs`, owned by `/backend`) is
    /// treated as cache-stale — the same code path that fires when source
    /// mtime or dependency hash changes.
    ///
    /// `#[serde(default)]` so pre-Sprint-58 caches (which lack the field)
    /// deserialise as `0` and are rejected as version-mismatch by the cache
    /// loader. See Decision 34.
    #[serde(default)]
    pub schema_version: u32,

    // --- Cached object code (Sprint 58 Wave 3a; Decision 32 + Decision 35) ---
    /// Per-module linker store — the retention root for cached `.o`-mapped
    /// code in `--run`/REPL mode after cache-hit. `L = ()` for crates that
    /// don't handle linker state (typecheck, frontend, etc.); the integration
    /// layer wires the concrete `Linker` (or `Arc<Linker>` per Decision 35)
    /// in Wave 3b.
    ///
    /// `#[serde(skip)]` — runtime state. Cache-hit re-derives the field
    /// by re-loading the `.o`; the persisted `.meta.json` carries no linker
    /// state. Per Decision 35, the *current* integration-layer choice is
    /// `L = ()` because per-symbol `Code::Linker.linker: Arc<Linker>`
    /// retention covers every case where a Linker needs to outlive its
    /// construction. The field exists for completeness and forward
    /// compatibility — if a future scenario emerges where a Linker must be
    /// retained without any `Code::Linker` referencing it, `L` can be
    /// reactivated without further generics churn.
    ///
    /// See Decision 32 (`LinkerStore` trait shape), Decision 35 (`Code`
    /// enum + `L = ()` rationale), `interfaces.md` §"Symbol table and binding tree" for
    /// the field-shape contract.
    #[serde(skip)]
    pub linker: Option<L>,
    #[serde(skip, default)]
    transactions: TableTransactions,
}

struct StagedPublicationPlan<C: CodeStore> {
    candidate: SymbolTable<C, ()>,
    records: Vec<PublicationRecord<C>>,
    mutated: Vec<Symbol>,
    compiled_body_targets: Vec<CallableTarget>,
}

#[derive(Clone, Copy)]
enum PlannedAbiDecision {
    Preserve,
    Change,
}

/// Everything visible under one local spelling.
///
/// The canonical declaration is optional because an imported spelling can
/// consist only of references. References always name terminal declarations;
/// they never carry declaration or lifecycle payloads.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
struct SymbolEntry<C: CodeStore = ()> {
    binding: Option<Binding<C>>,
    references: Vec<NameCandidate>,
}

impl<C: CodeStore> SymbolEntry<C> {
    fn empty() -> Self {
        Self {
            binding: None,
            references: Vec::new(),
        }
    }

    fn callable(&self) -> Option<&Callable<C>> {
        self.binding.as_ref().and_then(Binding::callable)
    }

    fn trait_method(&self) -> Option<&TraitMethodRecord> {
        self.binding.as_ref().and_then(Binding::trait_method)
    }

    fn callable_mut(&mut self) -> Option<&mut Callable<C>> {
        self.binding.as_mut().and_then(Binding::callable_mut)
    }
}

impl SymbolEntry<()> {
    fn into_concrete<C: CodeStore>(self) -> SymbolEntry<C> {
        SymbolEntry {
            binding: self.binding.map(Binding::into_concrete),
            references: self.references,
        }
    }
}

#[derive(Debug, Default)]
struct TransactionRegistry {
    retained_callables: HashSet<Symbol>,
    staged_shells: HashSet<Symbol>,
    revisions: HashMap<Symbol, u64>,
}

#[derive(Debug, Default)]
struct TableTransactions(Arc<Mutex<TransactionRegistry>>);

impl Clone for TableTransactions {
    fn clone(&self) -> Self {
        Self::default()
    }
}

fn default_got_arc() -> std::sync::Arc<GotTable> {
    std::sync::Arc::new(GotTable::new())
}

// --- Session-level table aliases (Sprint 70 Phase B; F2/F3 of frontend-audit-s70) ---

/// Session-level map of `ModuleFullPath → SymbolTable<C, L>` — the workspace's
/// shared per-module store.
///
/// `SymbolTables<C, L>` is the canonical name of the per-session collection
/// the integration layer constructs at startup and threads as a shared
/// reference into frontend, typecheck, and backend. The keying domain is
/// `ModuleFullPath`; each entry is the per-module `SymbolTable<C, L>` value
/// held directly inside the [`DashMap`](dashmap::DashMap) shards (no
/// `Arc<…>` wrapper — see drift note below).
///
/// **Why types-crate (Principle 15 — `facade-types-live-with-behavior`).**
/// The alias is consumed by multiple implementation-crate surfaces:
///
/// - `cranelisp-typecheck` — `check_forms(parsed, ctx, symbol_tables: &SymbolTables, module_aliases: &ModuleAliases)` and `check_type_expr(expr, ctx, symbol_tables, module_aliases, current_module, span)` (see `bounded-contexts.md` §2 + Decision 0044; the per-crate `facades/typecheck.md` document was retired in S72 Wave 5)
/// - `cranelisp` (the `int` integration layer) — `SharedState.symbol_tables: SymbolTables<Code, ()>` (see `bounded-contexts.md` §6; the per-crate `facades/int.md` document was retired in S81 W-Retire); int's Pass-1 macro recognition also reads it via the types-owned resolution primitive (`ResolutionScope`)
/// - `cranelisp-backend` — codegen reads `symbol_tables` as the single codegen source (see `bounded-contexts.md` §3)
///
/// (Post-S76 W-Macro `cranelisp-frontend` no longer consumes `SymbolTables` —
/// macro recognition moved to typecheck + int; the frontend is purely
/// syntactic. See `bounded-contexts.md` §1.)
///
/// Multiple consumers → types-crate is the canonical home per the placement
/// heuristic. Any per-typecheck or per-int typedef would (a) defeat
/// the workspace-stable claim, and (b) force one consumer to invert the
/// dep graph onto another — both are direct Principle-3 / Principle-15
/// violations.
///
/// **Decision 32 grounds the parameterisation.** `C: CodeStore` and
/// `L: LinkerStore` are empty marker traits with blanket impls; the
/// integration layer chooses concrete `C = Code, L = ()` (per Decision
/// 35); typecheck and frontend usually see `SymbolTables<(), ()>` because
/// the `()` defaults propagate when no explicit annotation is supplied.
/// The same alias name spans both parameterisations — there is one
/// session-level table name across the workspace.
///
/// **No `Arc<…>` wrapper.** The canonical form holds the per-module
/// `SymbolTable` values directly inside the DashMap shards — the integration
/// layer's `SharedState.symbol_tables: SymbolTables<Code, ()>` is the
/// workspace-stable shape. (An `Arc<SymbolTable>`-wrapped spelling in retired
/// facade text was editorial drift; provenance:
/// `design/arch/facades/frontend-audit-s70.md`.)
///
/// See also `bounded-contexts.md` §7 (types-crate BC; "Module aliases live
/// at session level"), `design/arch/principles/15-facade-types-live-with-behavior.md`,
/// and `crates/cranelisp-types/src/module.rs` `SymbolTable` rustdoc.
pub type SymbolTables<C, L> = dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>;

/// A module-path-namespace alias entry — the resolved record of a single
/// `(import [(target-module local-alias) …])` (§8.3.4 alias-import) or
/// `(export [(target-module local-alias) …])` (§8.4.4 export-mount) form.
///
/// Aliases name **parts of a module path**, not value bindings; they live
/// in a parallel session-level table [`ModuleAliases`], NOT on
/// `SymbolTable.symbols`. The owning module of any alias entry is
/// **derived from the key** of the [`ModuleAliases`] DashMap (strip the
/// last dot-separated segment of the key; e.g. key `m.n.str` → owner
/// `m.n`); it is **not stored on `ModuleAliasEntry`**. See
/// `bounded-contexts.md` §7 — "Module aliases live at session level".
///
/// **Field set rationale.** Per spec §8.3.4 + §8.4.4 + §8.6.6, the
/// minimum-viable record to resolve a qualified name through an alias
/// (`current-module.str/split` → `core.string/split` in §8.4.4's worked
/// example) is:
///
/// - [`Self::target`] — the `ModuleFullPath` the alias resolves to. §8.6.6
///   step 5 substitutes the matched segment with this target before
///   restarting resolution.
/// - [`Self::visibility`] — `Visibility::Private` for `import`-form aliases
///   (§8.3.4); `Visibility::Public` for `export`-mount aliases (§8.4.4).
///   §8.6.6 consults this to decide whether downstream consumers (modules
///   importing from the alias's owner module) may traverse the alias.
///   Per-entry visibility per BC §7's "Visibility is per-entry"
///   convention — the same shape as `Binding.visibility`.
/// - [`Self::span`] — source span for diagnostics on conflict-detection
///   collisions (§8.6.4 mount collision; §8.6.4 mount-vs-submodule
///   cross-namespace collision).
///
/// **Why no `kind` field distinguishing import-alias from export-mount.**
/// The two cases differ at the parse-time installer (which form produces
/// which kind of alias and what diagnostics fire on collision), but at
/// resolution time they are uniform: `visibility` fully captures the
/// downstream-visibility difference, and `target` + the key fully capture
/// the resolution semantics. Per Principle 18 (enforce invariants
/// structurally), folding the kind into `visibility` removes a redundant
/// degree of freedom from the data model.
///
/// **`#[non_exhaustive]` per Principle 18 + workspace DTO convention** —
/// adding a field (e.g., a future per-alias docstring or provenance
/// marker) is non-breaking; consumers cannot exhaustively match across
/// crate boundaries.
///
/// See `bounded-contexts.md` §7, `spec/08-modules.md` §8.3.4 (alias
/// import), `spec/08-modules.md` §8.4.4 (module mounting on export),
/// `spec/08-modules.md` §8.6.6 (qualified name resolution order).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct ModuleAliasEntry {
    /// The fully-qualified module path the alias resolves to.
    ///
    /// For `(import [(core.string str) …])` in module `m`, this is
    /// `core.string`. For `(export [(core.option opt) …])` in module `m`,
    /// this is `core.option`. §8.6.6 step 5 substitutes the matched
    /// segment of the queried `module_path` with this target before
    /// restarting resolution.
    pub target: ModuleFullPath,

    /// Per-entry visibility (BC §7 "Visibility is per-entry").
    ///
    /// - `Visibility::Private` — the `(import [(target alias) …])` form
    ///   (§8.3.4). The alias is visible only to the owning module's own
    ///   qualified-name lookups; downstream consumers MUST NOT traverse
    ///   it.
    /// - `Visibility::Public` — the `(export [(target alias) …])` form
    ///   (§8.4.4 module mounting on export). The alias is part of the
    ///   owning module's public namespace; downstream consumers
    ///   importing from the owner module MAY write
    ///   `<owner>.<alias>/<name>` and have it resolve via §8.6.6.
    pub visibility: Visibility,

    /// Source span of the originating `import`/`export` form's
    /// alias-pair node — used by §8.6.4 conflict diagnostics (mount
    /// collision; mount-vs-submodule cross-namespace collision).
    pub span: Span,
}

impl ModuleAliasEntry {
    /// Construct an alias entry. Visibility selects between the two
    /// authoring forms: `Private` for §8.3.4 import-alias, `Public` for
    /// §8.4.4 export-mount.
    pub fn new(target: ModuleFullPath, visibility: Visibility, span: Span) -> Self {
        ModuleAliasEntry {
            target,
            visibility,
            span,
        }
    }
}

/// Session-level map of `ModuleFullPath → ModuleAliasEntry` — the
/// workspace's shared module-path-namespace alias table.
///
/// Lives in **parallel** to [`SymbolTables`]; keyed by the alias's
/// **full path** (e.g., key `m.n.str` for `(import [(core.string str)
/// …])` declared in `m.n`). [`crate::module_alias_key`] is the only key mint.
/// Resolution walks the requested path segment by segment: the leading probe
/// is scoped to the referring module and may traverse its private alias;
/// subsequent probes are scoped beneath the resolved prefix and require a
/// public mount. Every step is a keyed lookup; no alias-map scan occurs.
///
/// **Three keying domains, three newtypes, no conflation** (BC §7):
///
/// - [`ModuleFullPath`] — module / alias path (this table + `SymbolTables`)
/// - [`Symbol`] — in-module binding (`SymbolTable.symbols`)
/// - [`TypeName`] — receiver-pinned ADT lookup
///
/// **Insertion-time conflict enforcement** (spec §8.6.4):
///
/// - **Mount collision** (within this table) — two mounts at the same
///   alias inside the same owner module collide; different owner modules
///   mounting the same local alias name land at different
///   `ModuleFullPath` keys and do NOT collide. Structurally detected by a
///   second `module_aliases.insert(key, …)` for an already-occupied key.
/// - **Mount-vs-submodule cross-namespace collision** (this table vs
///   [`SymbolTables`]) — an alias path here clashes with a real loaded
///   module path in `SymbolTables`. NOT structural via the type system;
///   the parse-time installer MUST perform an atomic cross-table check
///   at insert time.
///
/// **Owner derivation.** Strip the last dot-separated segment of the
/// key to recover the alias's owner module. Example:
///
/// - key `m.n.str` → owner `m.n`, alias name `str`
/// - key `user.opt` → owner `user`, alias name `opt`
///
/// Single-segment keys (an alias at the root module) are valid; the
/// owner is then the root module `""` or the project root depending on
/// session configuration.
///
/// See `bounded-contexts.md` §7 ("Module aliases live at session
/// level"), `spec/08-modules.md` §8.3.4 (alias import), §8.4.4 (module
/// mounting on export), §8.6.6 (qualified name resolution order).
pub type ModuleAliases = dashmap::DashMap<ModuleFullPath, ModuleAliasEntry>;

/// Inherent constructor on the `()`-defaulted instantiation. Defined on
/// `SymbolTable<(), ()>` specifically (not on the generic `impl<C, L>`)
/// so that the call `SymbolTable::new(path)` — which appears throughout
/// the codebase without type annotations — resolves to this method
/// directly without requiring the type parameters to be specified or
/// inferred from context. Crates that need the parameterised flavour
/// (the integration layer with `C = Code`) construct the entry-set
/// differently (e.g., `cache-restore` populates a `SymbolTable<Code, _>`
/// from the deserialised `()` flavour by mapping entries; or use
/// `SymbolTable::<Code, ()>::new(path)` explicitly).
///
/// See the `cargo doc` discussion in Sprint 58 Wave 3a: Rust's default
/// type parameter inference does not propagate to associated function
/// calls (`SymbolTable::new(path)` would error with `type annotations
/// needed` if `new` were defined only on the generic `impl<C: CodeStore,
/// L: LinkerStore>`). The concrete-`()` inherent impl resolves the
/// ergonomic gap without sacrificing the parameterisation.
impl SymbolTable<(), ()> {
    pub fn new(path: ModuleFullPath) -> Self {
        SymbolTable {
            path,
            module_preamble: None,
            symbols: HashMap::new(),
            retired_slots: Vec::new(),
            next_seq: 0,
            got: std::sync::Arc::new(GotTable::new()),
            imports: Vec::new(),
            exports: Vec::new(),
            platforms: Vec::new(),
            submodules: Vec::new(),
            written_trait_impls: Vec::new(),
            lookup_dependencies: BTreeSet::new(),
            schema_version: 0,
            linker: None,
            transactions: TableTransactions::default(),
        }
    }
}

// Sprint 58 Wave 3b: Conversion `SymbolTable<()> → SymbolTable<C, L>` for
// the cache-restore path. The cache deserialises a `<()>`-flavoured table
// (because `code` is `#[serde(skip)]` and `linker` is `#[serde(skip)]`,
// the serialised form is parameter-independent); the integration layer
// needs to install it as a `<Code, ()>`-flavoured table for its session.
// This is a structural conversion (every entry's `code` becomes `None::<C>`
// and the `linker` field becomes `None::<L>`).
impl SymbolTable<(), ()> {
    /// Convert a `()`-flavoured `SymbolTable` to any other `<C, L>`
    /// instantiation by mapping each entry's `code: Option<()>` field to
    /// `None::<C>` and `linker: Option<()>` to `None::<L>`. Used by the
    /// cache-restore path: deserialise yields `<()>`, install needs
    /// `<Code, ()>` for the integration layer, and the structural
    /// fields (ast, scheme, callees, got_slot, etc.) are
    /// parameter-independent — they're carried over as-is.
    ///
    /// Sprint 58 Wave 3b (Decision 35).
    pub fn into_concrete<C: CodeStore, L: LinkerStore>(self) -> SymbolTable<C, L> {
        let mut symbols: HashMap<Symbol, SymbolEntry<C>> =
            HashMap::with_capacity(self.symbols.len());
        for (name, entry) in self.symbols {
            symbols.insert(name, entry.into_concrete::<C>());
        }
        SymbolTable {
            path: self.path,
            module_preamble: self.module_preamble,
            symbols,
            retired_slots: self.retired_slots,
            next_seq: self.next_seq,
            got: self.got,
            imports: self.imports,
            exports: self.exports,
            platforms: self.platforms,
            submodules: self.submodules,
            written_trait_impls: self.written_trait_impls,
            lookup_dependencies: self.lookup_dependencies,
            schema_version: self.schema_version,
            linker: None,
            transactions: TableTransactions::default(),
        }
    }
}

impl<C: CodeStore> SymbolTable<C, ()> {
    /// Atomically publish every binding and candidate exposure authored in an
    /// unpublished table for this module.
    ///
    /// Integration supplies exactly one decision for each key where both the
    /// prior and staged callable generations carry slots. All other slot moves
    /// are derived by the table. An explicit [`StagedPublicationDecision::ChangeAbi`]
    /// may also retire a slotted live callable whose key is wholly absent from
    /// staging; omission alone never removes a live binding. Staged lookup
    /// dependencies are unioned into the live set, which never loses a member.
    /// The transaction validates a cloned result before replacing live state,
    /// so every refusal leaves `self` unchanged.
    pub fn publish_staged(
        &mut self,
        staging: SymbolTable<C, ()>,
        decisions: &[StagedPublicationDecision],
    ) -> Result<Vec<PublicationRecord<C>>, LifecycleError> {
        let plan = self.plan_staged_publication(staging, decisions)?;
        Ok(self.apply_staged_publication(plan))
    }

    /// Atomically publish an owner-free staged module together with the exact
    /// compiled owners for its concrete backend bodies.
    ///
    /// The owner keys must equal the staged `Concrete`/`Body` key set. Every
    /// refusal leaves this table unchanged and returns the complete submitted
    /// owner map through [`CompiledPublicationRejection::into_parts`]. A live
    /// slotted callable may be retired without a replacement only through an
    /// explicit [`StagedPublicationDecision::ChangeAbi`]; omitted live keys are
    /// otherwise preserved. Staged lookup dependencies are unioned into the
    /// live set, as for [`Self::publish_staged`].
    pub fn publish_compiled_staged(
        &mut self,
        staging: SymbolTable<C, ()>,
        decisions: &[StagedPublicationDecision],
        compiled_owners: HashMap<CallableTarget, C>,
    ) -> Result<Vec<PublicationRecord<C>>, CompiledPublicationRejection<C>> {
        let mut plan = match self.plan_staged_publication(staging, decisions) {
            Ok(plan) => plan,
            Err(reason) => {
                return Err(CompiledPublicationRejection {
                    reason,
                    compiled_owners,
                });
            }
        };

        if let Err((reason, compiled_owners)) =
            attach_compiled_publication_owners(&mut plan, compiled_owners)
        {
            return Err(CompiledPublicationRejection {
                reason,
                compiled_owners,
            });
        }

        Ok(self.apply_staged_publication(plan))
    }

    fn plan_staged_publication(
        &self,
        staging: SymbolTable<C, ()>,
        decisions: &[StagedPublicationDecision],
    ) -> Result<StagedPublicationPlan<C>, LifecycleError> {
        if staging.path != self.path {
            return Err(LifecycleError::WrongModule {
                expected: self.path.clone(),
                actual: staging.path,
            });
        }
        staging.validate_lifecycle()?;

        if let Some(retired) = staging.retired_slots.first() {
            return Err(LifecycleError::WrongState {
                symbol: retired_slot_symbol(retired).clone(),
                expected: "unpublished staging without retired slots",
            });
        }

        for (name, binding) in staging.all_symbols() {
            validate_publication_binding(binding, name)?;
            if binding_has_compiled_owner(binding) {
                return Err(LifecycleError::WrongState {
                    symbol: name.clone(),
                    expected: "unpublished callable without a compiled owner",
                });
            }
            validate_publication_collision(self, name, self.get(name.as_ref()), binding)?;
        }

        let mut choices = BTreeSet::new();
        for (name, staged) in staging.all_symbols() {
            if self
                .get(name.as_ref())
                .is_some_and(binding_has_claimed_slot)
                && binding_has_claimed_slot(staged)
            {
                choices.insert(name.clone());
            }
        }

        let mut decision_by_symbol = BTreeMap::new();
        for decision in decisions {
            let (symbol, planned) = match decision {
                StagedPublicationDecision::PreserveAbi { symbol } => {
                    (symbol, PlannedAbiDecision::Preserve)
                }
                StagedPublicationDecision::ChangeAbi { symbol } => {
                    (symbol, PlannedAbiDecision::Change)
                }
            };
            if decision_by_symbol.insert(symbol.clone(), planned).is_some() {
                return Err(LifecycleError::WrongState {
                    symbol: symbol.clone(),
                    expected: "one unique publication decision",
                });
            }
        }

        if let Some(missing) = choices
            .iter()
            .find(|symbol| !decision_by_symbol.contains_key(*symbol))
        {
            return Err(LifecycleError::WrongState {
                symbol: missing.clone(),
                expected: "an explicit ABI publication decision",
            });
        }

        let mut absent_retirements = Vec::new();
        for (symbol, planned) in &decision_by_symbol {
            if choices.contains(symbol) {
                continue;
            }

            if matches!(planned, PlannedAbiDecision::Preserve) {
                return Err(LifecycleError::WrongState {
                    symbol: symbol.clone(),
                    expected: "PreserveAbi only at a two-slot ABI choice",
                });
            }
            if staging.symbols.contains_key(symbol) {
                return Err(LifecycleError::WrongState {
                    symbol: symbol.clone(),
                    expected: "ChangeAbi with a slotted replacement or a wholly absent staging key",
                });
            }
            let Some(entry) = self.symbols.get(symbol) else {
                return Err(LifecycleError::MissingBinding {
                    symbol: symbol.clone(),
                });
            };
            let Some(binding) = entry.binding.as_ref() else {
                return Err(LifecycleError::WrongState {
                    symbol: symbol.clone(),
                    expected: "a live slotted callable binding, not a candidate-only spelling",
                });
            };
            if !binding_is_callable(binding) {
                return Err(LifecycleError::NotCallable {
                    symbol: symbol.clone(),
                });
            }
            if !binding_has_claimed_slot(binding) {
                return Err(LifecycleError::WrongState {
                    symbol: symbol.clone(),
                    expected: "a live slotted callable",
                });
            }
            absent_retirements.push(symbol.clone());
        }
        absent_retirements.sort();

        let staged_next_seq = staging.next_seq;
        let staged_written_impls = staging.written_trait_impls;
        let staged_lookup_dependencies = staging.lookup_dependencies;
        let mut staged_entries: Vec<_> = staging.symbols.into_iter().collect();
        staged_entries.sort_by(|(left_name, left), (right_name, right)| {
            let left_slot = left.binding.as_ref().and_then(binding_first_claimed_slot);
            let right_slot = right.binding.as_ref().and_then(binding_first_claimed_slot);
            match (left_slot, right_slot) {
                (Some(left), Some(right)) => left
                    .index()
                    .cmp(&right.index())
                    .then_with(|| left_name.cmp(right_name)),
                (Some(_), None) => std::cmp::Ordering::Less,
                (None, Some(_)) => std::cmp::Ordering::Greater,
                (None, None) => left_name.cmp(right_name),
            }
        });

        let mut candidate = self.clone();
        let mut records = Vec::new();
        let mut mutated = Vec::new();
        let mut compiled_body_targets = Vec::new();
        let mut claimed = candidate.claimed_slots();
        for (name, mut staged_entry) in staged_entries {
            let mut live_entry = candidate
                .symbols
                .remove(&name)
                .unwrap_or_else(SymbolEntry::empty);
            if let Some(mut published) = staged_entry.binding.take() {
                let mut prior = live_entry.binding.take();
                let prior_was_callable = prior.as_ref().is_some_and(binding_is_callable);
                let bodies = reconcile_publication_binding(
                    &candidate.path,
                    &name,
                    prior.as_mut(),
                    &mut published,
                    decision_by_symbol.get(&name).copied(),
                    &mut claimed,
                    &mut candidate.retired_slots,
                )?;
                compiled_body_targets.extend(binding_compiled_body_targets(
                    &candidate.path,
                    &name,
                    &published,
                ));
                live_entry.binding = Some(published);
                records.push(PublicationRecord {
                    symbol: name.clone(),
                    prior_was_callable,
                    bodies,
                });
                mutated.push(name.clone());
            }

            live_entry.references.extend(staged_entry.references);
            canonicalize_and_dedup_name_candidates(&mut live_entry.references);
            if live_entry.binding.is_some() || !live_entry.references.is_empty() {
                candidate.symbols.insert(name.clone(), live_entry);
            }
            mutated.push(name);
        }

        for name in absent_retirements {
            let Some(mut live_entry) = candidate.symbols.remove(&name) else {
                return Err(LifecycleError::MissingBinding { symbol: name });
            };
            let Some(mut prior) = live_entry.binding.take() else {
                return Err(LifecycleError::WrongState {
                    symbol: name,
                    expected: "a live slotted callable binding, not a candidate-only spelling",
                });
            };
            if !binding_is_callable(&prior) {
                return Err(LifecycleError::NotCallable { symbol: name });
            }
            let bodies = retire_absent_binding(
                &candidate.path,
                &name,
                &mut prior,
                &mut candidate.retired_slots,
            );
            if !live_entry.references.is_empty() {
                candidate.symbols.insert(name.clone(), live_entry);
            }
            records.push(PublicationRecord {
                symbol: name.clone(),
                prior_was_callable: true,
                bodies,
            });
            mutated.push(name);
        }

        merge_written_trait_impls(&mut candidate, staged_written_impls)?;
        candidate
            .lookup_dependencies
            .extend(staged_lookup_dependencies);
        candidate.next_seq = candidate.next_seq.max(staged_next_seq);
        candidate.validate_lifecycle()?;

        compiled_body_targets.sort();
        mutated.sort();
        mutated.dedup();
        Ok(StagedPublicationPlan {
            candidate,
            records,
            mutated,
            compiled_body_targets,
        })
    }

    fn apply_staged_publication(
        &mut self,
        plan: StagedPublicationPlan<C>,
    ) -> Vec<PublicationRecord<C>> {
        self.symbols = plan.candidate.symbols;
        self.retired_slots = plan.candidate.retired_slots;
        self.written_trait_impls = plan.candidate.written_trait_impls;
        self.lookup_dependencies = plan.candidate.lookup_dependencies;
        self.next_seq = plan.candidate.next_seq;
        for name in plan.mutated {
            self.note_symbol_mutation(&name);
        }
        plan.records
    }
}

/// Module-local GOT exhaustion: the table's private slot allocator was called
/// when the claims-plus-tombstones scan found no free index in the module's
/// fixed [`GOT_TABLE_SIZE`]-slot slab.
///
/// Constructed only by the table's private allocator. It is never
/// serialised (GOT slot allocation is not persisted state — the slab is
/// re-derived per session), so a schema bump is not part of its lifecycle.
/// Callers map it into their own error carrier — a located compile error
/// naming the module — never a panic on user input.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct GotExhausted {
    /// The module whose GOT has no free slot.
    pub module: ModuleFullPath,
}

impl std::fmt::Display for GotExhausted {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "GOT slot table exhausted for module '{}' ({GOT_TABLE_SIZE} slots): \
             too many definitions and ABI-changing redefinitions in one session",
            self.module
        )
    }
}

impl std::error::Error for GotExhausted {}

// --- Callable-slot witness (S119 types-first slice; design/arch/total-concreteness.md §2) ---

/// A GOT slot index paired, at mint, with the concreteness check of the scheme
/// it serves — the witness half of the `slot ⇒ is_concrete()` invariant
/// (`design/arch/total-concreteness.md` §2 I-CONC; BC §7 "Callability is
/// structural").
///
/// The field is **private**: outside `cranelisp-types` a `CallableSlot` value
/// can only be obtained from a [`SymbolTable`] settlement funnel (fresh,
/// checked), [`CallableSlot::rebind`] (reuse, re-checked — the REPL
/// slot-carry-forward path), or deserialization. Because constructing a
/// slot-carrying kind variant requires a `CallableSlot` *value*, the enum
/// variants that will carry it need no field privatisation — the S119
/// former hand-mint spelling (raw allocation then a concrete-state literal)
/// is unavailable because allocation and publication are private funnel work.
///
/// **Trust-boundary obligation (R-29).** Serde bypasses the mint
/// (`#[serde(transparent)]` — the wire shape is the bare index, byte-identical
/// to the `usize` it replaces). The cache-load loop therefore re-checks every
/// restored slot-carrying entry: a restored slot whose scheme fails
/// `is_concrete()` is refused by `validate_lifecycle` as
/// `LifecycleError::NonConcreteSlot` (`design/arch/total-concreteness.md` §2),
/// never a trusted witness. Clone/copy can likewise move a slot beside a
/// different scheme in-process; the standing falsifier for that residual is
/// the NC-1 universal sweep (tier 5 of the §3.2 ladder).
///
/// **Rejected relocation — slot inside `MonoDefnVariant` (`codegen_view`),
/// ruled 2026-07-27** (`design/arch/symbol-table-lifecycle.md` §8). The
/// slot witnesses *scheme* concreteness for the whole slotted population —
/// including `Realization::ExternShim` primitives and platform-effect entries
/// whose bodies are Rust/DLL code that can never carry a view — and its
/// lifetime is the published ABI epoch (rebind carry-forward; the trap-stub
/// freeze retains the slot of an entry with NO body), while the view's
/// lifetime is one definition. The slot's home is the kind variant beside the
/// scheme; the view carries no slot.
///
/// **Rejected relocation — a `symbol → slot` register owned by/beside
/// `GotTable`, ruled 2026-07-27** (`design/arch/symbol-table-lifecycle.md` §8). A side map would single-home the *binding* while splitting the
/// *capability* from its determinant: the programme's invariant is
/// slotted ⟺ concrete, and the concreteness determinant is the kind
/// discriminator the slot sits beside (Principle 20, S84 — "is it concrete"
/// IS "does it have a slot"). The map re-opens the S83-closed illegal
/// pairing (a `Constrained` entry beside a live row), guarded only by
/// scrub-and-membership discipline — the S82 accessor stopgap generalised,
/// the fallback P20 records as superseded. Structurally it also cannot live
/// in `GotTable`: the slab is `#[serde(skip)]` + Clone-as-fresh, and staging
/// tables hold a fresh GOT `Arc`, so a register there loses every binding at
/// staging construction. The one thing the register would buy —
/// `redef_slots` subsumption — is bought inside the representation instead:
/// the D11 amendment carries the redefinition-reuse candidate on
/// `Life::Declared { prior }` (§3.11 ruling 2).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct CallableSlot(usize);

impl CallableSlot {
    /// The raw GOT slot index (for `SymbolTable.got` `store_slot`/`load_slot`
    /// and serde/storage sites). Read-only — there is no public inverse.
    pub fn index(&self) -> usize {
        self.0
    }

    /// Checked slot REUSE — the Decision-31 REPL-redefinition carry-forward:
    /// transfer this slot to a new scheme iff the scheme is concrete.
    ///
    /// Consumes the witness and re-issues it against `scheme`, so a slot
    /// cannot silently migrate from a concrete definition to a non-concrete
    /// redefinition (the redefinition path must instead take the slot-less
    /// template route and the old slot is retired/frozen per the session's
    /// retention rules). The error carries the first residual position
    /// ([`NotConcrete`]) for a located diagnostic.
    pub fn rebind(self, scheme: &Scheme) -> Result<CallableSlot, NotConcrete> {
        // `ConcreteType::from_type` is the witness-producing form of
        // `Type::is_concrete()` (identical acceptance set; the Err carries the
        // exact residual TypeId) — one predicate, one choke point (P7).
        ConcreteType::from_type(&scheme.ty)?;
        Ok(self)
    }
}

/// Why a [`SymbolTable`] settlement funnel refused to mint a slot.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum SlotMintError {
    /// The scheme is not fully concrete — a GOT slot is the value-capability
    /// of a CONCRETE callable (Principle 20 / I-CONC); the entry must take a
    /// slot-less [`Life::Template`] state instead.
    NotConcrete(NotConcrete),
    /// The module's fixed GOT slab has no free slot (the pre-existing
    /// [`GotExhausted`] failure, unchanged in meaning).
    Exhausted(GotExhausted),
}

impl std::fmt::Display for SlotMintError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SlotMintError::NotConcrete(nc) => write!(
                f,
                "cannot mint a callable GOT slot for a non-concrete scheme ({nc:?}): \
                 only a fully-concrete callable may hold a slot"
            ),
            SlotMintError::Exhausted(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for SlotMintError {}
/// [`Decl::ImplShell`] discovery shell that fresh registration placed
/// in the **trait's home** table (Decision 45 as amended S110 §1.1.1).
///
/// Serde-visible on the writer module's `.meta.json` via
/// `SymbolTable.written_trait_impls`; restoration re-enrols the shell from
/// this record through [`enrol_written_trait_impl`] — never from mangled-name
/// parsing, never from a foreign-table scan (both Principle-24 banned shapes).
/// The Principle-7 second-home justification (authority split by lifetime:
/// live-session discovery = the shell; cross-session persistence = this
/// record; ONE derivation, conflict-checked at the enrolment seam) is
/// `design/arch/trait-impl-cache-carrier.md` §7.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct WrittenTraitImpl {
    /// Canonical resolved trait identity (never re-derived at restore).
    pub trait_name: FQTraitName,
    /// Canonical resolved implementing-type identity.
    pub impl_type: FQTypeName,
    /// The writer's module — equal to the owning table's `path` (the load
    /// boundary validates this; a mismatched record is diagnosed cache-stale,
    /// never trusted into enrolment — R6, `safety-invariants.md` §4).
    pub impl_module: ModuleFullPath,
    /// Local method names (not mangled).
    pub methods: Vec<Symbol>,
    /// `Public` per spec §5.11.1.
    pub visibility: Visibility,
}

impl WrittenTraitImpl {
    /// Construct the single record shared by fresh registration's staged
    /// trait-home shell and its success-only writer-side upsert.
    pub fn new(
        trait_name: FQTraitName,
        impl_type: FQTypeName,
        impl_module: ModuleFullPath,
        methods: Vec<Symbol>,
        visibility: Visibility,
    ) -> Self {
        WrittenTraitImpl {
            trait_name,
            impl_type,
            impl_module,
            methods,
            visibility,
        }
    }
}

/// Outcome of [`enrol_written_trait_impl`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnrolOutcome {
    /// The discovery shell was absent and has been inserted.
    Enrolled,
    /// An identical shell was already present — no-op (idempotence under
    /// multi-path restore; carried by the helper, not caller bookkeeping).
    AlreadyEnrolled,
}

/// Opaque snapshot for rolling back an unpublished callable-checking batch.
///
/// The token is table-specific, non-cloneable and consumed by either
/// [`SymbolTable::rollback_callables`] or [`RetainedCallables::commit`].
#[must_use = "retained callable batches must be committed or rolled back"]
pub struct RetainedCallables<C: CodeStore = ()> {
    registry: Arc<Mutex<TransactionRegistry>>,
    entries: Vec<(Symbol, Option<SymbolEntry<C>>, u64)>,
    retired_slots: Vec<RetiredSlot>,
}

impl<C: CodeStore> RetainedCallables<C> {
    /// Accept the current callable batch and release its rollback reservation.
    pub fn commit(self) {}
}

impl<C: CodeStore> Drop for RetainedCallables<C> {
    fn drop(&mut self) {
        let mut registry = self
            .registry
            .lock()
            .expect("transaction registry mutex poisoned");
        for (name, _, _) in &self.entries {
            registry.retained_callables.remove(name);
        }
    }
}

/// Opaque fresh-registration token for one provisionally installed
/// trait-implementation shell.
///
/// Fresh registration may stage a divergent same-key re-impl while its methods
/// check. The token retains that predecessor for exact rollback; cache restore
/// never uses this path and remains strict through [`enrol_written_trait_impl`].
/// The token is table-specific, non-cloneable and consumed by either
/// [`SymbolTable::rollback_trait_impl_shell`] or [`StagedImplShell::commit`].
#[must_use = "staged trait implementation shells must be committed or rolled back"]
pub struct StagedImplShell<C: CodeStore = ()> {
    registry: Arc<Mutex<TransactionRegistry>>,
    key: Symbol,
    candidate: WrittenTraitImpl,
    prior: Option<SymbolEntry<C>>,
    revision: u64,
}

impl<C: CodeStore> StagedImplShell<C> {
    /// Accept the staged shell and release its rollback reservation.
    pub fn commit(self) {}
}

impl<C: CodeStore> Drop for StagedImplShell<C> {
    fn drop(&mut self) {
        self.registry
            .lock()
            .expect("transaction registry mutex poisoned")
            .staged_shells
            .remove(&self.key);
    }
}

/// The ONE strict idempotent cache-restore enrolment primitive over the
/// **trait home's** table (`trait-impl-cache-carrier.md` §4).
///
/// Restore and fresh registration share [`crate::trait_impl_key`] and the
/// `Decl::ImplShell` representation, but not conflict policy: restore calls
/// this function and rejects a divergent occupant; fresh registration uses
/// [`SymbolTable::stage_trait_impl_shell`] so a same-key re-impl can retain its
/// predecessor and roll back while methods are checked.
///
/// Semantics: mint the storage key via [`crate::trait_impl_key`]; probe
/// `table`; **absent** → insert the shell → [`EnrolOutcome::Enrolled`];
/// **present and payload-identical** → no-op →
/// [`EnrolOutcome::AlreadyEnrolled`]; **present and divergent** (different
/// payload, or a non-`TraitImpl` occupant) → hard `ModuleError` naming both —
/// deterministic conflict handling, never a silent pick.
///
/// A malformed record (empty method list — the R6 well-formedness floor this
/// crate can check without the sidecar context) is rejected before the probe;
/// the load boundary additionally validates `impl_module` against the owning
/// sidecar's module path (int/backend side, same R6 row).
#[allow(clippy::result_large_err)]
pub fn enrol_written_trait_impl<C, L>(
    table: &mut SymbolTable<C, L>,
    record: &WrittenTraitImpl,
) -> Result<EnrolOutcome, crate::CranelispError>
where
    C: CodeStore,
    L: LinkerStore,
{
    use crate::{CranelispError, ErrorLocation};

    if record.methods.is_empty() {
        return Err(CranelispError::ModuleError {
            message: format!(
                "malformed written-impl record: impl of {} for {} (writer {}) has an empty \
                 method list — rejecting enrolment (stale or corrupted cache metadata)",
                record.trait_name, record.impl_type, record.impl_module
            ),
            location: ErrorLocation::unknown(),
        });
    }

    let key = crate::trait_impl_key(&record.impl_type, &record.trait_name);
    match table.get(key.as_ref()) {
        None => {
            table
                .install_binding(
                    key,
                    Binding::new(
                        Decl::ImplShell(ImplShell {
                            trait_name: record.trait_name.clone(),
                            impl_type: record.impl_type.clone(),
                            impl_module: record.impl_module.clone(),
                            methods: record.methods.clone(),
                        }),
                        record.visibility,
                    ),
                )
                .map_err(|error| CranelispError::ModuleError {
                    message: error.to_string(),
                    location: ErrorLocation::unknown(),
                })?;
            Ok(EnrolOutcome::Enrolled)
        }
        Some(Binding {
            visibility,
            declaration: Decl::ImplShell(shell),
        }) if shell.trait_name == record.trait_name
            && shell.impl_type == record.impl_type
            && shell.impl_module == record.impl_module
            && shell.methods == record.methods
            && *visibility == record.visibility =>
        {
            Ok(EnrolOutcome::AlreadyEnrolled)
        }
        Some(existing) => {
            // `C` is not `Debug`-bounded; describe the occupant without it.
            let existing_desc = match existing {
                Binding {
                    visibility,
                    declaration: Decl::ImplShell(shell),
                } => format!(
                    "ImplShell {{ trait: {}, type: {}, writer: {}, methods: {:?}, \
                     visibility: {visibility:?} }}",
                    shell.trait_name, shell.impl_type, shell.impl_module, shell.methods
                ),
                _ => "a non-impl-shell binding".to_string(),
            };
            Err(crate::CranelispError::ModuleError {
                message: format!(
                    "divergent trait-impl enrolment at key `{key}` in module `{}`: the table \
                     holds {existing_desc} but the writer-side record is {record:?} — refusing \
                     to choose (recompile the writer module)",
                    table.path
                ),
                location: ErrorLocation::unknown(),
            })
        }
    }
}

impl<C: CodeStore, L: LinkerStore> SymbolTable<C, L> {
    /// Construct an empty `SymbolTable<C, L>` for a generic instantiation.
    ///
    /// Sprint 58 Wave 3b (Decision 35): the integration layer needs to
    /// construct `SymbolTable<Code, ()>` directly (to seed user/test
    /// modules into `SharedState.symbol_tables`). The `()`-flavoured
    /// inherent impl above (`SymbolTable::<(), ()>::new`) covers
    /// typecheck/frontend's use case where no type annotation is supplied;
    /// this generic version covers the integration layer's
    /// `SymbolTable::<Code, ()>::new(path)` call sites.
    ///
    /// Both produce identical structural state (empty maps, fresh GOT,
    /// `code: None` / `linker: None`); they differ only in the type
    /// parameters Rust infers.
    pub fn new_with_params(path: ModuleFullPath) -> Self {
        SymbolTable {
            path,
            module_preamble: None,
            symbols: HashMap::new(),
            retired_slots: Vec::new(),
            next_seq: 0,
            got: std::sync::Arc::new(GotTable::new()),
            imports: Vec::new(),
            exports: Vec::new(),
            platforms: Vec::new(),
            submodules: Vec::new(),
            written_trait_impls: Vec::new(),
            lookup_dependencies: BTreeSet::new(),
            schema_version: 0,
            linker: None,
            transactions: TableTransactions::default(),
        }
    }

    /// Modules whose tables answered a qualified reference while this module
    /// compiled, after module-alias substitution, in path order.
    ///
    /// These are cache-validity edges only, not a load obligation.
    pub fn lookup_dependencies(&self) -> impl Iterator<Item = &ModuleFullPath> {
        self.lookup_dependencies.iter()
    }

    /// Record one lookup dependency.
    ///
    /// Insert-only: duplicates collapse and this table's own path is ignored.
    /// Producers record into the cluster's staging table; staged publication
    /// unions the set into the live table.
    pub fn record_lookup_dependency(&mut self, module: ModuleFullPath) {
        if module != self.path {
            self.lookup_dependencies.insert(module);
        }
    }

    /// Allocate the next available module-local GOT slot.
    ///
    /// The GOT is a fixed [`GOT_TABLE_SIZE`]-slot slab. Allocation derives the
    /// first index absent from live claims and retired-slot tombstones; if none
    /// exists it fails with [`GotExhausted`]. No stored cursor is mutated, so
    /// exhaustion is stable and repeatable.
    /// This makes exhaustion a diagnosed compile error at the seam rather than
    /// release-mode UB at the eventual `store_slot`/`load_slot` (Phase H).
    ///
    /// This raw allocator is private and used only beneath
    /// `mint_callable_slot`, which pairs allocation with the concreteness
    /// check. That is the C1 realization of FIXME 0931; sprint administration
    /// retains and closes the marker after the downstream wash.
    fn allocate_got_slot_with_claims(
        &self,
        claimed: &HashSet<usize>,
    ) -> Result<usize, GotExhausted> {
        (0..GOT_TABLE_SIZE)
            .find(|slot| !claimed.contains(slot))
            .ok_or_else(|| GotExhausted {
                module: self.path.clone(),
            })
    }

    /// The ONE way to obtain a fresh [`CallableSlot`]: checks
    /// `scheme.ty.is_concrete()` and allocates from derived claims in one act.
    ///
    /// A refusal ([`SlotMintError::NotConcrete`]) means the entry must take a
    /// slot-less [`Life::Template`] state — there is no legal way to hold a
    /// callable slot over a non-concrete scheme. Refusals are stable and
    /// side-effect-free.
    ///
    /// The concreteness check runs through [`ConcreteType::from_type`] — the
    /// witness-producing form of `Type::is_concrete()` (identical acceptance
    /// set; the `Err` carries the exact residual `TypeId` for a located
    /// diagnostic).
    fn mint_callable_slot(&self, scheme: &Scheme) -> Result<CallableSlot, SlotMintError> {
        let mut claimed = self.claimed_slots();
        self.mint_callable_slot_with_claims(scheme, &mut claimed)
    }

    fn mint_callable_slot_with_claims(
        &self,
        scheme: &Scheme,
        claimed: &mut HashSet<usize>,
    ) -> Result<CallableSlot, SlotMintError> {
        if let Err(nc) = ConcreteType::from_type(&scheme.ty) {
            return Err(SlotMintError::NotConcrete(nc));
        }
        let slot = self
            .allocate_got_slot_with_claims(claimed)
            .map_err(SlotMintError::Exhausted)?;
        claimed.insert(slot);
        Ok(CallableSlot(slot))
    }

    // `append_structural_decl` + its `StructuralDeclEntry` carrier DELETED
    // (S119, FIXME 0918 — resolving the Decision-39 append-carrier question
    // ONE way): the helper had zero callers repo-wide and the carrier enum
    // was constructed nowhere. **The `pub` structural Vec fields ARE the
    // append contract**: writers (int's form handlers) push directly onto
    // `imports` / `exports` / `platforms` / `submodules` in source/authorship
    // order under the append-only, no-dedup discipline stated on each field.
    // There is no bulk-load method either — the once-cited
    // `write_structural_decls` never existed (the phantom is retracted here;
    // a stale mention survives in `cranelisp-frontend/src/module_extract.rs`
    // rustdoc for the frontend wash to sweep).

    /// Return the binding stored under `name` without following aliases.
    pub fn get(&self, name: &str) -> Option<&Binding<C>> {
        self.symbols
            .get(name)
            .and_then(|entry| entry.binding.as_ref())
    }

    fn replace_binding(&mut self, name: Symbol, binding: Binding<C>) -> Option<Binding<C>> {
        self.symbols
            .entry(name)
            .or_insert_with(SymbolEntry::empty)
            .binding
            .replace(binding)
    }

    fn remove_binding(&mut self, name: &Symbol) -> Option<Binding<C>> {
        let binding = self
            .symbols
            .get_mut(name)
            .and_then(|entry| entry.binding.take());
        if self
            .symbols
            .get(name)
            .is_some_and(|entry| entry.binding.is_none() && entry.references.is_empty())
        {
            self.symbols.remove(name);
        }
        binding
    }

    /// Replace the authoritative docstring of a local plain callable.
    ///
    /// Documentation is orthogonal to lifecycle state, so every lifecycle
    /// legal for [`CallableOrigin::Plain`] is accepted without changing the
    /// binding, lifecycle payload, candidates, slot, compiled owner or GOT.
    /// Candidate-only spellings are not mutable aliases: `name` must identify
    /// the canonical local binding. Successful replacement records one normal
    /// symbol mutation; every refusal leaves both data and revision unchanged.
    pub fn set_plain_callable_docstring(
        &mut self,
        name: &Symbol,
        docstring: String,
    ) -> Result<(), LifecycleError> {
        let entry = self
            .symbols
            .get_mut(name)
            .ok_or_else(|| LifecycleError::MissingBinding {
                symbol: name.clone(),
            })?;
        let binding = entry
            .binding
            .as_mut()
            .ok_or_else(|| LifecycleError::MissingBinding {
                symbol: name.clone(),
            })?;
        let callable = binding
            .callable_mut()
            .ok_or_else(|| LifecycleError::NotCallable {
                symbol: name.clone(),
            })?;
        if !matches!(callable.origin, CallableOrigin::Plain) {
            return Err(LifecycleError::WrongState {
                symbol: name.clone(),
                expected: "plain callable",
            });
        }
        callable.docstring = Some(docstring);
        self.note_symbol_mutation(name);
        Ok(())
    }

    /// Record whether a concrete callable is used as a first-class value
    /// without exposing mutable access to lifecycle state. Only a settled
    /// concrete callable accepts this fact.
    pub fn set_value_use(&mut self, name: &Symbol, mark: bool) -> Result<(), LifecycleError> {
        let callable = self.callable_mut_in_state(name, "Concrete")?;
        let Life::Concrete { value_use, .. } = &mut callable.arm.life else {
            return Err(LifecycleError::WrongState {
                symbol: name.clone(),
                expected: "Concrete",
            });
        };
        *value_use = mark;
        self.note_symbol_mutation(name);
        Ok(())
    }

    /// Install a non-callable binding. Callable state is created only through
    /// the lifecycle funnels below.
    pub fn install_binding(
        &mut self,
        name: Symbol,
        binding: Binding<C>,
    ) -> Result<Option<Binding<C>>, LifecycleError> {
        if matches!(
            binding.declaration,
            Decl::Callable(_) | Decl::Overloaded(_) | Decl::Macro(_) | Decl::TraitMethod(_)
        ) {
            return Err(LifecycleError::WrongState {
                symbol: name,
                expected: "non-callable binding outside the dedicated trait-method funnel",
            });
        }
        if self.get(name.as_ref()).is_some_and(|existing| {
            existing.callable().is_some()
                || existing.trait_method().is_some()
                || self.binding_owns_candidate_references(existing)
        }) {
            return Err(LifecycleError::WrongState {
                symbol: name,
                expected: "explicit callable or trait-method displacement",
            });
        }
        let previous = self.replace_binding(name.clone(), binding);
        self.note_symbol_mutation(&name);
        Ok(previous)
    }

    /// Install one complete overloaded declaration at an absent canonical binding.
    pub fn install_overloaded(
        &mut self,
        name: Symbol,
        docstring: Option<String>,
        seq: u64,
        arms: Vec<CallableArmDraft>,
        visibility: Visibility,
    ) -> Result<(), LifecycleError> {
        let mut claimed = self.claimed_slots();
        let arms = arms
            .into_iter()
            .map(|draft| self.settle_family_arm(draft, &mut claimed))
            .collect::<Result<Vec<_>, _>>()?;
        let declaration = OverloadedCallable::new(docstring, seq, arms)?;
        self.install_callable_family(name, Decl::Overloaded(declaration), visibility)
    }

    /// Install one complete macro declaration at an absent canonical binding.
    pub fn install_macro(
        &mut self,
        name: Symbol,
        docstring: Option<String>,
        seq: u64,
        macro_sexp: Sexp,
        clauses: Vec<MacroClauseDraft>,
        visibility: Visibility,
    ) -> Result<(), LifecycleError> {
        let mut claimed = self.claimed_slots();
        let clauses = clauses
            .into_iter()
            .enumerate()
            .map(|(ordinal, draft)| {
                let callable = self.settle_family_arm(draft.callable, &mut claimed)?;
                Ok(MacroClause::new(
                    CallableArmId::from_ordinal(ordinal)?,
                    draft.params,
                    draft.rest_param,
                    callable,
                ))
            })
            .collect::<Result<Vec<_>, LifecycleError>>()?;
        let declaration = MacroDeclaration::new(docstring, seq, macro_sexp, clauses)?;
        self.install_callable_family(name, Decl::Macro(declaration), visibility)
    }

    fn settle_family_arm(
        &self,
        draft: CallableArmDraft,
        claimed: &mut HashSet<usize>,
    ) -> Result<CallableArm<C>, LifecycleError> {
        let CallableArmDraft {
            scheme,
            param_names,
            settlement,
        } = draft;
        let life = match settlement {
            CallableArmSettlement::Template {
                body,
                kind,
                callees,
            } => {
                if ConcreteType::from_type(&scheme.ty).is_ok() {
                    return Err(LifecycleError::ConcreteTemplate {
                        symbol: Symbol::from("family arm"),
                    });
                }
                Life::Template {
                    body,
                    kind,
                    callees: canonical_callees(callees),
                }
            }
            CallableArmSettlement::ConcreteBody { ast, view, callees } => {
                let slot = self
                    .mint_callable_slot_with_claims(&scheme, claimed)
                    .map_err(LifecycleError::SlotMint)?;
                Life::Concrete {
                    slot,
                    realization: Realization::Body { view, code: None },
                    minted_from: None,
                    ast: Some(ast),
                    callees: canonical_callees(callees),
                    value_use: false,
                    mode_summary: None,
                }
            }
        };
        Ok(CallableArm::new(scheme, param_names, life))
    }

    fn install_callable_family(
        &mut self,
        name: Symbol,
        declaration: Decl<C>,
        visibility: Visibility,
    ) -> Result<(), LifecycleError> {
        if self.get(name.as_ref()).is_some() {
            return Err(LifecycleError::WrongState {
                symbol: name,
                expected: "vacant canonical family binding",
            });
        }
        self.replace_binding(name.clone(), Binding::new(declaration, visibility));
        if let Err(error) = self.validate_lifecycle() {
            self.remove_binding(&name);
            return Err(error);
        }
        self.note_symbol_mutation(&name);
        Ok(())
    }

    /// Install an unslotted trait-method declaration at its canonical
    /// `Trait.method` key and project its bare spelling into method scope.
    ///
    /// Both writes are validated before either lands. An identical retry is a
    /// no-op; a divergent canonical occupant or projection is refused.
    pub fn install_trait_method(
        &mut self,
        method: Symbol,
        record: TraitMethodRecord,
        visibility: Visibility,
    ) -> Result<(), LifecycleError> {
        if record.trait_name.module != self.path {
            return Err(LifecycleError::WrongState {
                symbol: method,
                expected: "trait method declared in its trait home",
            });
        }
        let canonical = crate::member_key(record.trait_name.name.as_ref(), method.as_ref());
        let source = FQSymbol {
            module: self.path.clone(),
            symbol: canonical.clone(),
        };
        let terminal_present = match self.get(canonical.as_ref()) {
            None => false,
            Some(binding)
                if binding.visibility == visibility
                    && binding
                        .trait_method()
                        .is_some_and(|existing| trait_method_records_equal(existing, &record)) =>
            {
                true
            }
            Some(_) => {
                return Err(LifecycleError::WrongState {
                    symbol: canonical,
                    expected: "vacant or identical canonical trait-method declaration",
                });
            }
        };

        let mut references = self
            .symbols
            .get(&method)
            .map(|entry| entry.references.clone())
            .unwrap_or_default();
        match references
            .iter()
            .find(|candidate| candidate.source == source)
        {
            Some(candidate) if candidate.visibility == visibility => {}
            Some(_) => {
                return Err(LifecycleError::WrongState {
                    symbol: method,
                    expected: "absent or identical local trait-method projection",
                });
            }
            None => {
                references.push(NameCandidate::new(source, visibility));
                canonicalize_name_candidates(&mut references);
            }
        }

        if !terminal_present {
            self.replace_binding(
                canonical.clone(),
                Binding::new(Decl::TraitMethod(record), visibility),
            );
            self.note_symbol_mutation(&canonical);
        }
        self.symbols
            .entry(method)
            .or_insert_with(SymbolEntry::empty)
            .references = references;
        Ok(())
    }

    /// Expose a terminal canonical declaration under a local spelling.
    ///
    /// Repeating one source deduplicates it, with public visibility dominating
    /// private visibility. Distinct canonical sources remain candidates.
    pub fn expose_candidate(
        &mut self,
        local_name: Symbol,
        source: FQSymbol,
        visibility: Visibility,
    ) -> Result<(), LifecycleError> {
        if source.module == self.path {
            let binding =
                self.get(source.symbol.as_ref())
                    .ok_or_else(|| LifecycleError::MissingBinding {
                        symbol: source.symbol.clone(),
                    })?;
            if source.symbol == local_name {
                if visibility == Visibility::Public && !binding.is_public() {
                    self.symbols
                        .get_mut(&local_name)
                        .and_then(|entry| entry.binding.as_mut())
                        .expect("binding checked above")
                        .visibility = Visibility::Public;
                    self.note_symbol_mutation(&local_name);
                }
                return Ok(());
            }
        }

        let references = &mut self
            .symbols
            .entry(local_name.clone())
            .or_insert_with(SymbolEntry::empty)
            .references;
        if let Some(existing) = references
            .iter_mut()
            .find(|candidate| candidate.source == source)
        {
            if visibility == Visibility::Public {
                existing.visibility = Visibility::Public;
            }
        } else {
            references.push(NameCandidate::new(source, visibility));
        }
        canonicalize_name_candidates(references);
        self.note_symbol_mutation(&local_name);
        Ok(())
    }

    /// Return every terminal candidate visible under one local spelling.
    pub fn name_candidates(&self, name: &Symbol) -> Vec<NameCandidate> {
        let Some(entry) = self.symbols.get(name) else {
            return Vec::new();
        };
        let mut candidates = entry.references.clone();
        if let Some(binding) = &entry.binding {
            candidates.push(NameCandidate::new(
                FQSymbol {
                    module: self.path.clone(),
                    symbol: name.clone(),
                },
                binding.visibility,
            ));
        }
        canonicalize_and_dedup_name_candidates(&mut candidates);
        candidates
    }

    /// Iterate every public terminal candidate exposed by this table.
    pub fn public_name_candidates(&self) -> impl Iterator<Item = (&Symbol, NameCandidate)> {
        self.all_name_candidates()
            .filter(|(_, candidate)| candidate.visibility == Visibility::Public)
    }

    /// Iterate every terminal candidate exposed by this table.
    pub fn all_name_candidates(&self) -> impl Iterator<Item = (&Symbol, NameCandidate)> {
        self.symbols.iter().flat_map(|(name, _)| {
            self.name_candidates(name)
                .into_iter()
                .map(move |candidate| (name, candidate))
        })
    }

    /// Iterate over bindings whose outer visibility is public.
    pub fn public_symbols(&self) -> impl Iterator<Item = (&Symbol, &Binding<C>)> {
        self.symbols.iter().filter_map(|(name, entry)| {
            entry
                .binding
                .as_ref()
                .filter(|binding| binding.is_public())
                .map(|binding| (name, binding))
        })
    }

    /// Iterate over all symbols (public and private).
    pub fn all_symbols(&self) -> impl Iterator<Item = (&Symbol, &Binding<C>)> {
        self.symbols
            .iter()
            .filter_map(|(name, entry)| entry.binding.as_ref().map(|binding| (name, binding)))
    }

    /// Resolve a typed execution target to the callable arm owned by this table.
    pub fn callable_target(&self, target: &CallableTarget) -> Option<&CallableArm<C>> {
        let (owner, family_id) = match target {
            CallableTarget::Binding(owner) => {
                if owner.module != self.path {
                    return None;
                }
                return self
                    .get(owner.symbol.as_ref())
                    .and_then(Binding::callable)
                    .map(|c| &c.arm);
            }
            CallableTarget::OverloadArm { owner, arm } => (owner, (*arm, false)),
            CallableTarget::MacroClause { owner, clause } => (owner, (*clause, true)),
        };
        if owner.module != self.path {
            return None;
        }
        match (&self.get(owner.symbol.as_ref())?.declaration, family_id) {
            (Decl::Overloaded(declaration), (id, false)) => declaration
                .arms
                .get(id.ordinal())
                .filter(|arm| arm.id == id)
                .map(|arm| &arm.callable),
            (Decl::Macro(declaration), (id, true)) => declaration
                .clauses
                .get(id.ordinal())
                .filter(|clause| clause.id == id)
                .map(|clause| &clause.callable),
            _ => None,
        }
    }

    /// Iterator over entries that codegen should compile.
    ///
    /// Shared codegen-compilable predicate — see Decision 22 in
    /// `design/arch/CLAUDE.md` and §9.5 of `design/typecheck/ast-annotation.md`.
    /// Both the backend's `compile_to_module` and the integration layer's
    /// priority worker enumerate codegen targets via this iterator so the
    /// filter lives in exactly one place.
    ///
    /// Direct callables, overload arms, and macro clauses are considered
    /// independently. Templates and other non-body lifecycle states are
    /// mono/dispatch sources, not codegen targets; only a concrete body
    /// realization appears in this projection.
    pub fn codegen_targets(&self) -> impl Iterator<Item = (CallableTarget, &CallableArm<C>)> {
        let module = self.path.clone();
        self.all_symbols().flat_map(move |(name, binding)| {
            let owner = FQSymbol {
                module: module.clone(),
                symbol: name.clone(),
            };
            let candidates: Vec<_> = match &binding.declaration {
                Decl::Callable(callable) => vec![(CallableTarget::Binding(owner), &callable.arm)],
                Decl::Overloaded(declaration) => declaration
                    .arms
                    .iter()
                    .map(|arm| {
                        (
                            CallableTarget::OverloadArm {
                                owner: owner.clone(),
                                arm: arm.id,
                            },
                            &arm.callable,
                        )
                    })
                    .collect(),
                Decl::Macro(declaration) => declaration
                    .clauses
                    .iter()
                    .map(|clause| {
                        (
                            CallableTarget::MacroClause {
                                owner: owner.clone(),
                                clause: clause.id,
                            },
                            &clause.callable,
                        )
                    })
                    .collect(),
                _ => Vec::new(),
            };
            candidates.into_iter().filter(|(_, arm)| {
                matches!(
                    arm.life,
                    Life::Concrete {
                        realization: Realization::Body { .. },
                        ..
                    }
                )
            })
        })
    }

    /// Register or redeclare a checked callable. Any displaced slot becomes
    /// the declaration's provisional prior claim until settlement decides
    /// whether to rebind or retire it.
    #[allow(clippy::too_many_arguments)]
    pub fn declare(
        &mut self,
        name: Symbol,
        scheme: Scheme,
        param_names: Vec<Symbol>,
        docstring: Option<String>,
        seq: u64,
        origin: CallableOrigin,
        visibility: Visibility,
    ) -> Result<(), LifecycleError> {
        let prior = match self.get(name.as_ref()) {
            None => None,
            Some(binding) => {
                let existing = binding
                    .callable()
                    .ok_or_else(|| LifecycleError::NotCallable {
                        symbol: name.clone(),
                    })?;
                if !same_redeclarable_origin(&existing.origin, &origin) {
                    return Err(LifecycleError::IllegalOriginState { symbol: name });
                }
                existing.arm.life.claimed_slot()
            }
        };
        let binding = Binding::new(
            Decl::Callable(Callable {
                docstring,
                seq,
                origin,
                arm: CallableArm::new(scheme, param_names, Life::Declared { prior }),
            }),
            visibility,
        );
        validate_origin_state(&name, binding.callable().expect("declaration is callable"))?;
        self.replace_binding(name.clone(), binding);
        self.note_symbol_mutation(&name);
        Ok(())
    }

    /// Replace the provisional scheme of a declared callable while
    /// preserving any displaced prior slot claim.
    pub fn update_declared_scheme(
        &mut self,
        name: &Symbol,
        scheme: Scheme,
    ) -> Result<(), LifecycleError> {
        let callable = self.callable_mut_in_state(name, "Declared")?;
        if !matches!(callable.arm.life, Life::Declared { .. }) {
            return Err(LifecycleError::WrongState {
                symbol: name.clone(),
                expected: "Declared",
            });
        }
        callable.arm.scheme = scheme;
        self.note_symbol_mutation(name);
        Ok(())
    }

    /// Settle a declared callable as a non-concrete template.
    pub fn settle_template(
        &mut self,
        name: &Symbol,
        body: TemplateBody,
        kind: TemplateKind,
        callees: Vec<FQSymbol>,
    ) -> Result<(), LifecycleError> {
        let candidate = {
            let callable = self
                .get(name.as_ref())
                .and_then(Binding::callable)
                .ok_or_else(|| LifecycleError::NotCallable {
                    symbol: name.clone(),
                })?;
            if !matches!(callable.arm.life, Life::Declared { .. }) {
                return Err(LifecycleError::WrongState {
                    symbol: name.clone(),
                    expected: "Declared",
                });
            }
            if ConcreteType::from_type(&callable.arm.scheme.ty).is_ok() {
                return Err(LifecycleError::ConcreteTemplate {
                    symbol: name.clone(),
                });
            }
            let mut candidate = callable.clone();
            candidate.arm.life = Life::Template {
                body: body.clone(),
                kind: kind.clone(),
                callees: callees.clone(),
            };
            candidate
        };
        validate_origin_state(name, &candidate)?;
        let prior = {
            let callable = self.callable_mut_in_state(name, "Declared")?;
            match &mut callable.arm.life {
                Life::Declared { prior } => prior.take(),
                _ => {
                    return Err(LifecycleError::WrongState {
                        symbol: name.clone(),
                        expected: "Declared",
                    });
                }
            }
        };
        if let Some(slot) = prior {
            self.retired_slots.push(RetiredSlot {
                slot,
                reason: RetireReason::TemplateFlip {
                    symbol: name.clone(),
                },
            });
        }
        self.callable_mut_in_state(name, "Declared")?.arm.life = Life::Template {
            body,
            kind,
            callees,
        };
        self.note_symbol_mutation(name);
        self.validate_lifecycle()
    }

    /// Settle a declaration as a concrete callable, atomically pairing its
    /// concrete scheme, codegen view and re-bound-or-fresh slot.
    pub fn settle_concrete(
        &mut self,
        name: &Symbol,
        realization: Realization<C>,
        ast: Option<DefnVariant>,
        callees: Vec<FQSymbol>,
    ) -> Result<CallableSlot, LifecycleError> {
        let (scheme, prior) = {
            let callable = self
                .get(name.as_ref())
                .and_then(Binding::callable)
                .ok_or_else(|| LifecycleError::NotCallable {
                    symbol: name.clone(),
                })?;
            let Life::Declared { prior } = callable.arm.life else {
                return Err(LifecycleError::WrongState {
                    symbol: name.clone(),
                    expected: "Declared",
                });
            };
            (callable.arm.scheme.clone(), prior)
        };
        let slot = match prior {
            Some(slot) => slot
                .rebind(&scheme)
                .map_err(|error| LifecycleError::SlotMint(SlotMintError::NotConcrete(error)))?,
            None => self.mint_callable_slot(&scheme)?,
        };
        let life = Life::Concrete {
            slot,
            realization,
            minted_from: None,
            ast,
            callees,
            value_use: false,
            mode_summary: None,
        };
        let mut candidate = self
            .get(name.as_ref())
            .and_then(Binding::callable)
            .expect("declared callable checked above")
            .clone();
        candidate.arm.life = life.clone();
        validate_origin_state(name, &candidate)?;
        self.callable_mut_in_state(name, "Declared")?.arm.life = life;
        self.note_symbol_mutation(name);
        self.validate_lifecycle()?;
        Ok(slot)
    }

    /// Atomically settle an AST-backed checked body as a non-concrete
    /// template, accepting the Pass-2/finalize states defined by the lifecycle
    /// contract.
    pub fn settle_checked_template(
        &mut self,
        name: &Symbol,
        scheme: Scheme,
        ast: DefnVariant,
        kind: TemplateKind,
        callees: Vec<FQSymbol>,
    ) -> Result<(), LifecycleError> {
        if ConcreteType::from_type(&scheme.ty).is_ok() {
            return Err(LifecycleError::ConcreteTemplate {
                symbol: name.clone(),
            });
        }
        let old_binding =
            self.get(name.as_ref())
                .cloned()
                .ok_or_else(|| LifecycleError::MissingBinding {
                    symbol: name.clone(),
                })?;
        let callable = old_binding
            .callable()
            .ok_or_else(|| LifecycleError::NotCallable {
                symbol: name.clone(),
            })?;
        let retired = match &callable.arm.life {
            Life::Declared { prior } => *prior,
            Life::Template {
                body: TemplateBody::Ast(_),
                ..
            } => None,
            Life::Concrete {
                slot,
                realization: Realization::Body { .. },
                minted_from: None,
                ..
            } => Some(*slot),
            _ => {
                return Err(LifecycleError::WrongState {
                    symbol: name.clone(),
                    expected: "Declared, AST Template, or ordinary Body Concrete",
                });
            }
        };
        let mut candidate = callable.clone();
        candidate.arm.scheme = scheme;
        candidate.arm.life = Life::Template {
            body: TemplateBody::Ast(ast),
            kind,
            callees: canonical_callees(callees),
        };
        validate_origin_state(name, &candidate)?;

        let old_tombstones = self.retired_slots.clone();
        self.replace_binding(
            name.clone(),
            Binding::new(Decl::Callable(candidate), old_binding.visibility),
        );
        if let Some(slot) = retired {
            self.retired_slots.push(RetiredSlot {
                slot,
                reason: RetireReason::TemplateFlip {
                    symbol: name.clone(),
                },
            });
        }
        if let Err(error) = self.validate_lifecycle() {
            self.replace_binding(name.clone(), old_binding);
            self.retired_slots = old_tombstones;
            return Err(error);
        }
        self.note_symbol_mutation(name);
        Ok(())
    }

    /// Atomically settle an AST-backed checked body as concrete, committing
    /// its final scheme, view, call edges and slot transition together.
    pub fn settle_checked_concrete(
        &mut self,
        name: &Symbol,
        scheme: Scheme,
        ast: DefnVariant,
        view: crate::MonoDefnVariant,
        callees: Vec<FQSymbol>,
    ) -> Result<CallableSlot, LifecycleError> {
        if view.name != *name {
            return Err(LifecycleError::WrongState {
                symbol: name.clone(),
                expected: "codegen view with matching symbol identity",
            });
        }
        ConcreteType::from_type(&scheme.ty)
            .map_err(|error| LifecycleError::SlotMint(SlotMintError::NotConcrete(error)))?;
        let old_binding =
            self.get(name.as_ref())
                .cloned()
                .ok_or_else(|| LifecycleError::MissingBinding {
                    symbol: name.clone(),
                })?;
        let callable = old_binding
            .callable()
            .ok_or_else(|| LifecycleError::NotCallable {
                symbol: name.clone(),
            })?;
        let existing_slot = match &callable.arm.life {
            Life::Declared { prior } => *prior,
            Life::Template {
                body: TemplateBody::Ast(_),
                ..
            } => None,
            Life::Concrete {
                slot,
                realization: Realization::Body { .. },
                minted_from: None,
                ..
            } => Some(*slot),
            _ => {
                return Err(LifecycleError::WrongState {
                    symbol: name.clone(),
                    expected: "Declared, AST Template, or ordinary Body Concrete",
                });
            }
        };
        let slot = match existing_slot {
            Some(slot) => slot
                .rebind(&scheme)
                .map_err(|error| LifecycleError::SlotMint(SlotMintError::NotConcrete(error)))?,
            None => self.mint_callable_slot(&scheme)?,
        };
        let mut candidate = callable.clone();
        candidate.arm.scheme = scheme;
        candidate.arm.life = Life::Concrete {
            slot,
            realization: Realization::Body { view, code: None },
            minted_from: None,
            ast: Some(ast),
            callees: canonical_callees(callees),
            value_use: false,
            mode_summary: None,
        };
        validate_origin_state(name, &candidate)?;

        self.replace_binding(
            name.clone(),
            Binding::new(Decl::Callable(candidate), old_binding.visibility),
        );
        if let Err(error) = self.validate_lifecycle() {
            self.replace_binding(name.clone(), old_binding);
            return Err(error);
        }
        self.note_symbol_mutation(name);
        Ok(slot)
    }

    /// Atomically replace an unpublished synthesized constructor or accessor
    /// with its non-concrete template form while preserving every name-candidate
    /// exposure which reaches the canonical binding.
    ///
    /// This authoring-time operation accepts only an existing synthetic
    /// [`Life::Concrete`] or [`Life::Broken`] entry with the same constructor or
    /// accessor identity. Its provisional slot must still contain a null GOT row
    /// and a concrete body must have no compiled owner. The replacement records
    /// no retired-slot tombstone; live publication and ABI retirement remain the
    /// responsibility of [`SymbolTable::publish_staged`]. Every refusal leaves
    /// the table unchanged.
    #[allow(clippy::too_many_arguments)]
    pub fn replace_unpublished_synthesized_template(
        &mut self,
        name: Symbol,
        scheme: Scheme,
        param_names: Vec<Symbol>,
        docstring: Option<String>,
        origin: CallableOrigin,
        synth: crate::SynthSpec,
        visibility: Visibility,
    ) -> Result<(), LifecycleError> {
        if ConcreteType::from_type(&scheme.ty).is_ok() {
            return Err(LifecycleError::ConcreteTemplate { symbol: name });
        }
        let (old_binding, _) = self.unpublished_synthesized_replacement_target(&name, &origin)?;
        let seq = old_binding
            .callable()
            .expect("replacement target checked as callable")
            .seq;
        let replacement = Binding::new(
            Decl::Callable(Callable {
                docstring,
                seq,
                origin,
                arm: CallableArm::new(
                    scheme,
                    param_names,
                    Life::Template {
                        body: TemplateBody::Synth(synth),
                        kind: TemplateKind::Parametric,
                        callees: Vec::new(),
                    },
                ),
            }),
            visibility,
        );
        self.replace_validated_unpublished_synthesized_binding(name, replacement)
    }

    /// Atomically replace an unpublished synthesized constructor or accessor
    /// with a concrete body and return its retained provisional callable slot.
    ///
    /// The supplied scheme must be concrete and `concrete_view` must carry the
    /// canonical `name`. The existing synthetic entry must identify the same
    /// constructor or accessor, own no compiled body, and still have a null GOT
    /// row. The checked slot is rebound rather than retired or freshly minted;
    /// the synthesized AST and concrete view enter [`Life::Concrete`] together
    /// with no compiled owner. Every refusal leaves the table unchanged.
    #[allow(clippy::too_many_arguments)]
    pub fn replace_unpublished_synthesized_concrete(
        &mut self,
        name: Symbol,
        scheme: Scheme,
        param_names: Vec<Symbol>,
        docstring: Option<String>,
        origin: CallableOrigin,
        synth: crate::SynthSpec,
        concrete_view: MonoDefnVariant,
        visibility: Visibility,
    ) -> Result<CallableSlot, LifecycleError> {
        if concrete_view.name != name {
            return Err(LifecycleError::WrongState {
                symbol: name,
                expected: "codegen view with matching symbol identity",
            });
        }
        ConcreteType::from_type(&scheme.ty)
            .map_err(|error| LifecycleError::SlotMint(SlotMintError::NotConcrete(error)))?;
        let (old_binding, old_slot) =
            self.unpublished_synthesized_replacement_target(&name, &origin)?;
        let slot = old_slot
            .rebind(&scheme)
            .map_err(|error| LifecycleError::SlotMint(SlotMintError::NotConcrete(error)))?;
        let seq = old_binding
            .callable()
            .expect("replacement target checked as callable")
            .seq;
        let replacement = Binding::new(
            Decl::Callable(Callable {
                docstring,
                seq,
                origin,
                arm: CallableArm::new(
                    scheme,
                    param_names,
                    Life::Concrete {
                        slot,
                        realization: Realization::Body {
                            view: concrete_view,
                            code: None,
                        },
                        minted_from: None,
                        ast: Some(synth.variant),
                        callees: Vec::new(),
                        value_use: false,
                        mode_summary: None,
                    },
                ),
            }),
            visibility,
        );
        self.replace_validated_unpublished_synthesized_binding(name, replacement)?;
        Ok(slot)
    }

    fn unpublished_synthesized_replacement_target(
        &self,
        name: &Symbol,
        replacement_origin: &CallableOrigin,
    ) -> Result<(Binding<C>, CallableSlot), LifecycleError> {
        self.validate_lifecycle()?;
        let binding =
            self.get(name.as_ref())
                .cloned()
                .ok_or_else(|| LifecycleError::MissingBinding {
                    symbol: name.clone(),
                })?;
        let callable = binding
            .callable()
            .ok_or_else(|| LifecycleError::NotCallable {
                symbol: name.clone(),
            })?;
        if !same_synthesized_origin(&callable.origin, replacement_origin) {
            return Err(LifecycleError::IllegalOriginState {
                symbol: name.clone(),
            });
        }
        let slot = match &callable.arm.life {
            Life::Concrete { slot, .. } | Life::Broken { slot, .. } => *slot,
            _ => {
                return Err(LifecycleError::WrongState {
                    symbol: name.clone(),
                    expected: "unpublished synthesized Concrete or Broken",
                });
            }
        };
        if binding_has_compiled_owner(&binding) {
            return Err(LifecycleError::WrongState {
                symbol: name.clone(),
                expected: "unpublished synthesized callable without compiled owner",
            });
        }
        if !self.got.load_slot(slot.index()).is_null() {
            return Err(LifecycleError::WrongState {
                symbol: name.clone(),
                expected: "unpublished synthesized callable with null GOT slot",
            });
        }
        Ok((binding, slot))
    }

    fn replace_validated_unpublished_synthesized_binding(
        &mut self,
        name: Symbol,
        replacement: Binding<C>,
    ) -> Result<(), LifecycleError> {
        let mut candidate_table = self.clone();
        candidate_table.replace_binding(name.clone(), replacement.clone());
        candidate_table.validate_lifecycle()?;
        self.replace_binding(name.clone(), replacement);
        self.note_symbol_mutation(&name);
        Ok(())
    }

    /// Replace and canonicalize call edges on a settled template or concrete
    /// callable without changing any other lifecycle payload.
    pub fn replace_callees(
        &mut self,
        name: &Symbol,
        callees: Vec<FQSymbol>,
    ) -> Result<(), LifecycleError> {
        let callees = canonical_callees(callees);
        let callable = self.callable_mut_in_state(name, "Template or Concrete")?;
        match &mut callable.arm.life {
            Life::Template {
                callees: current, ..
            }
            | Life::Concrete {
                callees: current, ..
            } => *current = callees,
            _ => {
                return Err(LifecycleError::WrongState {
                    symbol: name.clone(),
                    expected: "Template or Concrete",
                });
            }
        }
        self.note_symbol_mutation(name);
        Ok(())
    }

    /// Publish an ownership-annotated body view and its persisted summary as
    /// one atomic update on an uncompiled concrete body.
    pub fn publish_body_ownership(
        &mut self,
        target: &CallableTarget,
        summary: ModeSummary,
        mut view: crate::MonoDefnVariant,
    ) -> Result<(), LifecycleError> {
        let name = callable_target_owner(target).symbol.clone();
        let arm = self.callable_target_mut(target)?;
        let Life::Concrete {
            realization:
                Realization::Body {
                    view: current,
                    code,
                },
            mode_summary,
            ..
        } = &mut arm.life
        else {
            return Err(LifecycleError::WrongState {
                symbol: name.clone(),
                expected: "uncompiled Concrete Body",
            });
        };
        if code.is_some() {
            return Err(LifecycleError::WrongState {
                symbol: name.clone(),
                expected: "uncompiled Concrete Body",
            });
        }
        if view.name != current.name {
            return Err(LifecycleError::WrongState {
                symbol: name.clone(),
                expected: "ownership view with matching body identity",
            });
        }
        view.mode_summary = Some(summary.clone());
        *current = view;
        *mode_summary = Some(summary);
        self.note_symbol_mutation(&name);
        Ok(())
    }

    fn callable_target_mut(
        &mut self,
        target: &CallableTarget,
    ) -> Result<&mut CallableArm<C>, LifecycleError> {
        let owner = callable_target_owner(target);
        if owner.module != self.path {
            return Err(LifecycleError::WrongModule {
                expected: self.path.clone(),
                actual: owner.module.clone(),
            });
        }
        let binding = self
            .symbols
            .get_mut(&owner.symbol)
            .and_then(|entry| entry.binding.as_mut())
            .ok_or_else(|| LifecycleError::MissingBinding {
                symbol: owner.symbol.clone(),
            })?;
        match (target, &mut binding.declaration) {
            (CallableTarget::Binding(_), Decl::Callable(callable)) => Ok(&mut callable.arm),
            (CallableTarget::OverloadArm { arm, .. }, Decl::Overloaded(declaration)) => declaration
                .arms
                .get_mut(arm.ordinal())
                .filter(|candidate| candidate.id == *arm)
                .map(|candidate| &mut candidate.callable)
                .ok_or_else(|| LifecycleError::WrongState {
                    symbol: owner.symbol.clone(),
                    expected: "an existing overload arm target",
                }),
            (CallableTarget::MacroClause { clause, .. }, Decl::Macro(declaration)) => declaration
                .clauses
                .get_mut(clause.ordinal())
                .filter(|candidate| candidate.id == *clause)
                .map(|candidate| &mut candidate.callable)
                .ok_or_else(|| LifecycleError::WrongState {
                    symbol: owner.symbol.clone(),
                    expected: "an existing macro clause target",
                }),
            _ => Err(LifecycleError::NotCallable {
                symbol: owner.symbol.clone(),
            }),
        }
    }

    /// Attach a compiled body owner without exposing mutable lifecycle state.
    ///
    /// Only a concrete backend-body realization accepts an owner. Success
    /// returns the prior owner; refusal returns the submitted owner through
    /// [`CompiledOwnerRejection::into_parts`].
    pub fn publish_compiled_owner(
        &mut self,
        target: &CallableTarget,
        owner: C,
    ) -> Result<Option<C>, CompiledOwnerRejection<C>> {
        let name = callable_target_owner(target).symbol.clone();
        let displaced = {
            let arm = match self.callable_target_mut(target) {
                Ok(arm) => arm,
                Err(reason) => return Err(CompiledOwnerRejection { reason, owner }),
            };
            let Life::Concrete {
                realization: Realization::Body { code, .. },
                ..
            } = &mut arm.life
            else {
                return Err(CompiledOwnerRejection {
                    reason: LifecycleError::WrongState {
                        symbol: name.clone(),
                        expected: "Concrete Body",
                    },
                    owner,
                });
            };
            code.replace(owner)
        };
        self.note_symbol_mutation(&name);
        Ok(displaced)
    }

    /// Install a born-settled non-concrete template. Synthesized ADT members
    /// and uniform Rust templates use this funnel instead of entering a
    /// transient Declared state.
    #[allow(clippy::too_many_arguments)]
    pub fn install_template(
        &mut self,
        name: Symbol,
        scheme: Scheme,
        param_names: Vec<Symbol>,
        docstring: Option<String>,
        seq: u64,
        origin: CallableOrigin,
        body: TemplateBody,
        kind: TemplateKind,
        callees: Vec<FQSymbol>,
        visibility: Visibility,
    ) -> Result<(), LifecycleError> {
        if ConcreteType::from_type(&scheme.ty).is_ok() {
            return Err(LifecycleError::ConcreteTemplate { symbol: name });
        }
        self.install_settled_callable(
            name,
            Callable {
                docstring,
                seq,
                origin,
                arm: CallableArm::new(
                    scheme,
                    param_names,
                    Life::Template {
                        body,
                        kind,
                        callees,
                    },
                ),
            },
            visibility,
        )
    }

    /// Install a fresh, non-instance concrete callable through the same
    /// checked mint used by declaration settlement.
    #[allow(clippy::too_many_arguments)]
    pub fn install_concrete(
        &mut self,
        name: Symbol,
        scheme: Scheme,
        param_names: Vec<Symbol>,
        docstring: Option<String>,
        seq: u64,
        origin: CallableOrigin,
        realization: Realization<C>,
        ast: Option<DefnVariant>,
        callees: Vec<FQSymbol>,
        visibility: Visibility,
    ) -> Result<CallableSlot, LifecycleError> {
        let slot = self.mint_callable_slot(&scheme)?;
        self.install_settled_callable(
            name,
            Callable {
                docstring,
                seq,
                origin,
                arm: CallableArm::new(
                    scheme,
                    param_names,
                    Life::Concrete {
                        slot,
                        realization,
                        minted_from: None,
                        ast,
                        callees,
                        value_use: false,
                        mode_summary: None,
                    },
                ),
            },
            visibility,
        )?;
        Ok(slot)
    }

    /// Install a concrete monomorphised instance under the storage key
    /// derived from its typed template link.
    ///
    /// The returned symbol is the exact installed storage key. Keeping key
    /// derivation and back-link publication inside this funnel prevents a
    /// caller from installing a valid instance under a written alias or a
    /// differently mangled spelling.
    #[allow(clippy::too_many_arguments)]
    pub fn install_instance(
        &mut self,
        link: InstanceLink,
        scheme: Scheme,
        param_names: Vec<Symbol>,
        docstring: Option<String>,
        seq: u64,
        origin: CallableOrigin,
        realization: Realization<C>,
        ast: Option<DefnVariant>,
        callees: Vec<FQSymbol>,
        visibility: Visibility,
    ) -> Result<(Symbol, CallableSlot), LifecycleError> {
        let name = settled_instance_key(&link, &scheme)?;
        let slot = self.mint_callable_slot(&scheme)?;
        self.install_settled_callable(
            name.clone(),
            Callable {
                docstring,
                seq,
                origin,
                arm: CallableArm::new(
                    scheme,
                    param_names,
                    Life::Concrete {
                        slot,
                        realization,
                        minted_from: Some(link),
                        ast,
                        callees,
                        value_use: false,
                        mode_summary: None,
                    },
                ),
            },
            visibility,
        )?;
        Ok((name, slot))
    }

    /// Install a primitive extern shim as a born-settled callable.
    #[allow(clippy::too_many_arguments)]
    pub fn install_extern(
        &mut self,
        name: Symbol,
        scheme: Scheme,
        param_names: Vec<Symbol>,
        docstring: Option<String>,
        seq: u64,
        borrowed_sibling: Option<CallableSlot>,
        mode_summary: Option<ModeSummary>,
        visibility: Visibility,
    ) -> Result<CallableSlot, LifecycleError> {
        let slot = self.mint_callable_slot(&scheme)?;
        self.install_settled_callable(
            name,
            Callable {
                docstring,
                seq,
                origin: CallableOrigin::RustPrimitive,
                arm: CallableArm::new(
                    scheme,
                    param_names,
                    Life::Concrete {
                        slot,
                        realization: Realization::ExternShim { borrowed_sibling },
                        minted_from: None,
                        ast: None,
                        callees: Vec::new(),
                        value_use: false,
                        mode_summary,
                    },
                ),
            },
            visibility,
        )?;
        Ok(slot)
    }

    /// Install a slot-less inline primitive.
    pub fn install_inline(
        &mut self,
        name: Symbol,
        scheme: Scheme,
        param_names: Vec<Symbol>,
        docstring: Option<String>,
        seq: u64,
        mode_summary: Option<ModeSummary>,
        visibility: Visibility,
    ) -> Result<(), LifecycleError> {
        self.install_settled_callable(
            name,
            Callable {
                docstring,
                seq,
                origin: CallableOrigin::RustPrimitive,
                arm: CallableArm::new(scheme, param_names, Life::Inline { mode_summary }),
            },
            visibility,
        )
    }

    /// Install a slot-less by-name host-promised primitive.
    pub fn install_host_promised(
        &mut self,
        name: Symbol,
        scheme: Scheme,
        param_names: Vec<Symbol>,
        docstring: Option<String>,
        seq: u64,
        visibility: Visibility,
    ) -> Result<(), LifecycleError> {
        self.install_settled_callable(
            name,
            Callable {
                docstring,
                seq,
                origin: CallableOrigin::RustPrimitive,
                arm: CallableArm::new(scheme, param_names, Life::HostPromised),
            },
            visibility,
        )
    }

    /// Install a DLL effect at its manifest-owned slot.
    #[allow(clippy::too_many_arguments)]
    pub fn install_platform(
        &mut self,
        name: Symbol,
        scheme: Scheme,
        param_names: Vec<Symbol>,
        docstring: Option<String>,
        seq: u64,
        scheduling_class: SchedulingClass,
        poll_shape: bool,
        manifest_slot: usize,
        visibility: Visibility,
    ) -> Result<CallableSlot, LifecycleError> {
        ConcreteType::from_type(&scheme.ty)
            .map_err(|error| LifecycleError::SlotMint(SlotMintError::NotConcrete(error)))?;
        if manifest_slot >= GOT_TABLE_SIZE {
            return Err(LifecycleError::SlotOutOfRange {
                slot: manifest_slot,
            });
        }
        // Loading the same platform generation through cache/reload is an
        // idempotent declaration, not a second slot claim.  Validate the full
        // manifest-owned callable identity before accepting the retry.
        if let Some(existing) = self.get(name.as_ref()) {
            let same = existing.visibility == visibility
                && existing.callable().is_some_and(|callable| {
                    callable.docstring == docstring
                        && callable.seq == seq
                        && callable.arm.scheme.type_vars == scheme.type_vars
                        && callable.arm.scheme.constraints == scheme.constraints
                        && callable.arm.scheme.ty == scheme.ty
                        && callable.arm.param_names == param_names
                        && matches!(
                            (&callable.origin, &callable.arm.life),
                            (
                                CallableOrigin::PlatformEffect {
                                    scheduling_class: existing_class,
                                    poll_shape: existing_poll,
                                },
                                Life::Concrete {
                                    slot,
                                    realization: Realization::Dll,
                                    minted_from: None,
                                    ast: None,
                                    callees,
                                    value_use: false,
                                    mode_summary: None,
                                }
                            ) if *existing_class == scheduling_class
                                && *existing_poll == poll_shape
                                && slot.index() == manifest_slot
                                && callees.is_empty()
                        )
                });
            return if same {
                Ok(CallableSlot(manifest_slot))
            } else {
                Err(LifecycleError::WrongState {
                    symbol: name,
                    expected: "an absent or identical platform effect declaration",
                })
            };
        }
        if self.claimed_slots().contains(&manifest_slot) {
            return Err(LifecycleError::DuplicateSlot {
                slot: manifest_slot,
            });
        }
        let slot = CallableSlot(manifest_slot);
        self.install_settled_callable(
            name,
            Callable {
                docstring,
                seq,
                origin: CallableOrigin::PlatformEffect {
                    scheduling_class,
                    poll_shape,
                },
                arm: CallableArm::new(
                    scheme,
                    param_names,
                    Life::Concrete {
                        slot,
                        realization: Realization::Dll,
                        minted_from: None,
                        ast: None,
                        callees: Vec::new(),
                        value_use: false,
                        mode_summary: None,
                    },
                ),
            },
            visibility,
        )?;
        Ok(slot)
    }

    /// Move a concrete callable to its explicit broken state without losing
    /// the slot claim.
    pub fn mark_broken(
        &mut self,
        name: &Symbol,
        error: crate::BrokenProvenance,
    ) -> Result<BrokenTransition<C>, LifecycleError> {
        let mut candidate = self.clone();
        let _candidate_transition = apply_broken_transition(&mut candidate, name, error.clone())?;
        candidate.validate_lifecycle()?;

        let transition = apply_broken_transition(self, name, error)?;
        self.note_symbol_mutation(name);
        Ok(transition)
    }

    /// Remove a non-callable binding, refusing every callable lifecycle state.
    pub fn remove_non_callable(
        &mut self,
        name: &Symbol,
    ) -> Result<Option<Binding<C>>, LifecycleError> {
        if self.symbols.get(name).is_some_and(|entry| {
            entry.callable().is_some()
                || entry.trait_method().is_some()
                || entry
                    .binding
                    .as_ref()
                    .is_some_and(|binding| self.binding_owns_candidate_references(binding))
        }) {
            return Err(LifecycleError::WrongState {
                symbol: name.clone(),
                expected: "non-callable binding outside the dedicated trait-method funnel",
            });
        }
        let removed = self.remove_binding(name);
        if removed.is_some() {
            self.note_symbol_mutation(name);
        }
        Ok(removed)
    }

    /// Discard a provisional declaration only when it carries no displaced
    /// slot claim.
    pub fn discard_declared(&mut self, name: &Symbol) -> Result<(), LifecycleError> {
        let binding = self
            .symbols
            .get(name)
            .ok_or_else(|| LifecycleError::MissingBinding {
                symbol: name.clone(),
            })?;
        let Some(callable) = binding.callable() else {
            return Err(LifecycleError::NotCallable {
                symbol: name.clone(),
            });
        };
        if !matches!(callable.arm.life, Life::Declared { prior: None }) {
            return Err(LifecycleError::WrongState {
                symbol: name.clone(),
                expected: "Declared without prior slot",
            });
        }
        self.remove_binding(name);
        self.note_symbol_mutation(name);
        Ok(())
    }

    /// Retain callable entries and tombstones for one unpublished checking
    /// transaction.
    pub fn retain_callables(
        &self,
        names: &[Symbol],
    ) -> Result<RetainedCallables<C>, LifecycleError> {
        let mut unique = HashSet::with_capacity(names.len());
        for name in names {
            if !unique.insert(name.clone()) {
                return Err(LifecycleError::WrongState {
                    symbol: name.clone(),
                    expected: "unique retained callable name",
                });
            }
            if self
                .symbols
                .get(name)
                .is_some_and(|binding| binding.callable().is_none())
            {
                return Err(LifecycleError::NotCallable {
                    symbol: name.clone(),
                });
            }
        }

        let mut registry = self
            .transactions
            .0
            .lock()
            .expect("transaction registry mutex poisoned");
        if let Some(overlap) = names
            .iter()
            .find(|name| registry.retained_callables.contains(*name))
        {
            return Err(LifecycleError::WrongState {
                symbol: overlap.clone(),
                expected: "callable without an active retention token",
            });
        }
        let entries = names
            .iter()
            .map(|name| {
                (
                    name.clone(),
                    self.symbols.get(name).cloned(),
                    registry.revisions.get(name).copied().unwrap_or(0),
                )
            })
            .collect();
        registry.retained_callables.extend(names.iter().cloned());
        drop(registry);
        Ok(RetainedCallables {
            registry: Arc::clone(&self.transactions.0),
            entries,
            retired_slots: self.retired_slots.clone(),
        })
    }

    /// Restore an unpublished callable batch exactly, or refuse without any
    /// mutation if publication or an intervening table change is detected.
    pub fn rollback_callables(
        &mut self,
        retained: RetainedCallables<C>,
    ) -> Result<(), LifecycleError> {
        if !Arc::ptr_eq(&self.transactions.0, &retained.registry) {
            return Err(LifecycleError::WrongState {
                symbol: retained
                    .entries
                    .first()
                    .map(|(name, _, _)| name.clone())
                    .unwrap_or_else(|| Symbol::from("<batch>")),
                expected: "retention token from this symbol table",
            });
        }
        let names: HashSet<_> = retained
            .entries
            .iter()
            .map(|(name, _, _)| name.clone())
            .collect();
        let prior_unrelated: Vec<_> = retained
            .retired_slots
            .iter()
            .filter(|slot| !names.contains(retired_slot_symbol(slot)))
            .collect();
        let current_unrelated: Vec<_> = self
            .retired_slots
            .iter()
            .filter(|slot| !names.contains(retired_slot_symbol(slot)))
            .collect();
        if prior_unrelated != current_unrelated {
            return Err(LifecycleError::WrongState {
                symbol: retained
                    .entries
                    .first()
                    .map(|(name, _, _)| name.clone())
                    .unwrap_or_else(|| Symbol::from("<batch>")),
                expected: "unchanged unrelated tombstones",
            });
        }

        let registry = self
            .transactions
            .0
            .lock()
            .expect("transaction registry mutex poisoned");
        for (name, _, revision) in &retained.entries {
            let current_revision = registry.revisions.get(name).copied().unwrap_or(0);
            if current_revision == *revision {
                continue;
            }
            let Some(current) = self.symbols.get(name) else {
                continue;
            };
            if current.callable().is_none() {
                return Err(LifecycleError::NotCallable {
                    symbol: name.clone(),
                });
            }
        }
        drop(registry);

        let prior_slots: HashSet<_> = retained
            .entries
            .iter()
            .filter_map(|(_, binding, _)| {
                binding
                    .as_ref()
                    .and_then(SymbolEntry::callable)
                    .and_then(|callable| callable.arm.life.claimed_slot())
            })
            .chain(
                retained
                    .retired_slots
                    .iter()
                    .filter(|retired| names.contains(retired_slot_symbol(retired)))
                    .map(|retired| retired.slot),
            )
            .collect();
        let current_slots: HashSet<_> = retained
            .entries
            .iter()
            .filter_map(|(name, _, _)| {
                self.symbols
                    .get(name)
                    .and_then(SymbolEntry::callable)
                    .and_then(|callable| callable.arm.life.claimed_slot())
            })
            .chain(
                self.retired_slots
                    .iter()
                    .filter(|retired| names.contains(retired_slot_symbol(retired)))
                    .map(|retired| retired.slot),
            )
            .collect();
        let introduced_slots: HashSet<_> =
            current_slots.difference(&prior_slots).copied().collect();
        for (name, _, _) in &retained.entries {
            if let Some(callable) = self.symbols.get(name).and_then(SymbolEntry::callable)
                && callable
                    .arm
                    .life
                    .claimed_slot()
                    .is_some_and(|slot| introduced_slots.contains(&slot))
                && matches!(
                    &callable.arm.life,
                    Life::Concrete {
                        realization: Realization::Body { code: Some(_), .. },
                        ..
                    }
                )
            {
                return Err(LifecycleError::WrongState {
                    symbol: name.clone(),
                    expected: "unpublished callable body",
                });
            }
        }
        if let Some(slot) = introduced_slots
            .iter()
            .find(|slot| !self.got.load_slot(slot.index()).is_null())
        {
            let symbol = self
                .retired_slots
                .iter()
                .find(|retired| retired.slot == *slot)
                .map(retired_slot_symbol)
                .cloned()
                .unwrap_or_else(|| {
                    retained
                        .entries
                        .first()
                        .map(|(name, _, _)| name.clone())
                        .unwrap_or_else(|| Symbol::from("<batch>"))
                });
            return Err(LifecycleError::WrongState {
                symbol,
                expected: "unpublished null GOT slot",
            });
        }

        let mut candidate_symbols = self.symbols.clone();
        for (name, prior, _) in &retained.entries {
            match prior {
                Some(binding) => {
                    candidate_symbols.insert(name.clone(), binding.clone());
                }
                None => {
                    candidate_symbols.remove(name);
                }
            }
        }
        let current_symbols = std::mem::replace(&mut self.symbols, candidate_symbols);
        let current_tombstones =
            std::mem::replace(&mut self.retired_slots, retained.retired_slots.clone());
        if let Err(error) = self.validate_lifecycle() {
            self.symbols = current_symbols;
            self.retired_slots = current_tombstones;
            return Err(error);
        }
        for (name, _, _) in &retained.entries {
            self.note_symbol_mutation(name);
        }
        Ok(())
    }

    /// Fresh-registration-only: provisionally install a trait-implementation
    /// shell while retaining its same-key predecessor for exact rollback.
    /// Cache restoration uses [`enrol_written_trait_impl`] instead.
    #[allow(clippy::result_large_err)]
    pub fn stage_trait_impl_shell(
        &mut self,
        record: &WrittenTraitImpl,
    ) -> Result<StagedImplShell<C>, crate::CranelispError> {
        validate_written_trait_impl(record, None)?;
        if self.path != record.trait_name.module {
            return Err(module_error(format!(
                "cannot stage trait impl for {} in module `{}`: the shell belongs in trait home `{}`",
                record.trait_name, self.path, record.trait_name.module
            )));
        }
        let key = crate::trait_impl_key(&record.impl_type, &record.trait_name);
        let prior = self.symbols.get(&key).cloned();
        if prior
            .as_ref()
            .and_then(|entry| entry.binding.as_ref())
            .is_some_and(|binding| !matches!(binding.declaration, Decl::ImplShell(_)))
        {
            return Err(module_error(format!(
                "cannot stage trait impl at `{key}` in module `{}`: a non-impl-shell binding occupies the key",
                self.path
            )));
        }
        {
            let mut registry = self
                .transactions
                .0
                .lock()
                .expect("transaction registry mutex poisoned");
            if !registry.staged_shells.insert(key.clone()) {
                return Err(module_error(format!(
                    "trait impl key `{key}` already has an active staging token"
                )));
            }
        }
        self.replace_binding(key.clone(), written_trait_impl_binding(record));
        self.note_symbol_mutation(&key);
        let revision = self.symbol_revision(&key);
        Ok(StagedImplShell {
            registry: Arc::clone(&self.transactions.0),
            key,
            candidate: record.clone(),
            prior,
            revision,
        })
    }

    /// Roll back a provisionally installed trait-implementation shell after
    /// verifying that no intervening write replaced the staged candidate.
    #[allow(clippy::result_large_err)]
    pub fn rollback_trait_impl_shell(
        &mut self,
        staged: StagedImplShell<C>,
    ) -> Result<(), crate::CranelispError> {
        if !Arc::ptr_eq(&self.transactions.0, &staged.registry) {
            return Err(module_error(
                "staged impl-shell token belongs to another table",
            ));
        }
        if self.symbol_revision(&staged.key) != staged.revision {
            return Err(module_error(format!(
                "staged trait impl at `{}` changed before rollback",
                staged.key
            )));
        }
        let matches_candidate = self
            .symbols
            .get(&staged.key)
            .and_then(|entry| entry.binding.as_ref())
            .is_some_and(|binding| binding_matches_written_trait_impl(binding, &staged.candidate));
        if !matches_candidate {
            return Err(module_error(format!(
                "staged trait impl at `{}` changed before rollback",
                staged.key
            )));
        }
        match &staged.prior {
            Some(binding) => {
                self.symbols.insert(staged.key.clone(), binding.clone());
            }
            None => {
                self.symbols.remove(&staged.key);
            }
        }
        self.note_symbol_mutation(&staged.key);
        Ok(())
    }

    /// Complete the writer half of a successful fresh impl registration.
    ///
    /// Called only after every method settles and before the shell/method tokens
    /// commit. Validation failure is non-mutating; success inserts or replaces
    /// by canonical trait/type key while preserving registration order.
    #[allow(clippy::result_large_err)]
    pub fn upsert_written_trait_impl(
        &mut self,
        record: WrittenTraitImpl,
    ) -> Result<(), crate::CranelispError> {
        validate_written_trait_impl(&record, Some(&self.path))?;
        let mut seen = HashSet::new();
        let mut matching = None;
        for (index, existing) in self.written_trait_impls.iter().enumerate() {
            let key = crate::trait_impl_key(&existing.impl_type, &existing.trait_name);
            if !seen.insert(key.clone()) {
                return Err(module_error(format!(
                    "writer table `{}` contains duplicate trait-impl record key `{key}`",
                    self.path
                )));
            }
            if key == crate::trait_impl_key(&record.impl_type, &record.trait_name) {
                matching = Some(index);
            }
        }
        match matching {
            Some(index) => self.written_trait_impls[index] = record,
            None => self.written_trait_impls.push(record),
        }
        Ok(())
    }

    /// Remove an ABI-changing callable while retaining its old index as a
    /// permanent table-side tombstone.
    pub fn retire_abi_changing(&mut self, name: &Symbol) -> Result<Binding<C>, LifecycleError> {
        let binding = self
            .remove_binding(name)
            .ok_or_else(|| LifecycleError::MissingBinding {
                symbol: name.clone(),
            })?;
        let Some(slot) = binding
            .callable()
            .and_then(|callable| callable.arm.life.claimed_slot())
        else {
            self.replace_binding(name.clone(), binding);
            return Err(LifecycleError::WrongState {
                symbol: name.clone(),
                expected: "slot-carrying callable",
            });
        };
        self.retired_slots.push(RetiredSlot {
            slot,
            reason: RetireReason::AbiChanging {
                symbol: name.clone(),
            },
        });
        if let Err(error) = self.validate_lifecycle() {
            self.retired_slots.pop();
            self.replace_binding(name.clone(), binding);
            return Err(error);
        }
        self.note_symbol_mutation(name);
        Ok(binding)
    }

    /// Return the permanent tombstones that prevent published slot reuse.
    pub fn retired_slots(&self) -> &[RetiredSlot] {
        &self.retired_slots
    }

    /// Re-derive slot authority and validate a freshly-built, cloned or
    /// deserialized table before it becomes live.
    pub fn validate_lifecycle(&self) -> Result<(), LifecycleError> {
        self.validate_local_name_candidates()?;
        let mut seen = std::collections::HashSet::new();
        for retired in &self.retired_slots {
            validate_slot(retired.slot, &mut seen)?;
        }
        for (symbol, entry) in &self.symbols {
            let Some(binding) = entry.binding.as_ref() else {
                continue;
            };
            match &binding.declaration {
                Decl::Callable(callable) => {
                    validate_instance_key(symbol, callable)?;
                    validate_origin_state(symbol, callable)?;
                    validate_arm(symbol, &callable.arm, &mut seen)?;
                }
                Decl::Overloaded(declaration) => {
                    validate_family_ids(symbol, declaration.arms.iter().map(|arm| arm.id))?;
                    for arm in &declaration.arms {
                        validate_arm(symbol, &arm.callable, &mut seen)?;
                        validate_arm_template_target(symbol, &arm.callable)?;
                    }
                }
                Decl::Macro(declaration) => {
                    validate_family_ids(
                        symbol,
                        declaration.clauses.iter().map(|clause| clause.id),
                    )?;
                    for clause in &declaration.clauses {
                        validate_arm(symbol, &clause.callable, &mut seen)?;
                        validate_arm_template_target(symbol, &clause.callable)?;
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Validate this table's candidate references against direct canonical
    /// terminals after every dependency table has been restored.
    ///
    /// Local sources are deliberately checked against `self`, so a staging
    /// table never validates through an older live copy. Imported sources are
    /// direct-probed in `tables`; aliases are not accepted as terminals.
    pub fn validate_name_candidates(
        &self,
        tables: &SymbolTables<C, L>,
    ) -> Result<(), LifecycleError> {
        self.validate_lifecycle()?;
        for entry in self.symbols.values() {
            for candidate in &entry.references {
                if candidate.source.module == self.path {
                    continue;
                }
                let table = tables.get(&candidate.source.module).ok_or_else(|| {
                    LifecycleError::MissingBinding {
                        symbol: candidate.source.symbol.clone(),
                    }
                })?;
                if table.get(candidate.source.symbol.as_ref()).is_none() {
                    return Err(LifecycleError::WrongState {
                        symbol: candidate.source.symbol.clone(),
                        expected: "terminal name-candidate source",
                    });
                }
            }
        }
        Ok(())
    }

    fn install_settled_callable(
        &mut self,
        name: Symbol,
        callable: Callable<C>,
        visibility: Visibility,
    ) -> Result<(), LifecycleError> {
        if self.get(name.as_ref()).is_some() {
            return Err(LifecycleError::WrongState {
                symbol: name,
                expected: "vacant binding",
            });
        }
        validate_instance_key(&name, &callable)?;
        validate_origin_state(&name, &callable)?;
        self.replace_binding(
            name.clone(),
            Binding::new(Decl::Callable(callable), visibility),
        );
        if let Err(error) = self.validate_lifecycle() {
            self.remove_binding(&name);
            return Err(error);
        }
        self.note_symbol_mutation(&name);
        Ok(())
    }

    fn callable_mut_in_state(
        &mut self,
        name: &Symbol,
        _expected: &'static str,
    ) -> Result<&mut Callable<C>, LifecycleError> {
        self.symbols
            .get_mut(name)
            .and_then(SymbolEntry::callable_mut)
            .ok_or_else(|| LifecycleError::NotCallable {
                symbol: name.clone(),
            })
    }

    fn validate_local_name_candidates(&self) -> Result<(), LifecycleError> {
        for (local_name, entry) in &self.symbols {
            let mut prior: Option<&FQSymbol> = None;
            for candidate in &entry.references {
                if prior.is_some_and(|source| {
                    (&source.module, &source.symbol)
                        >= (&candidate.source.module, &candidate.source.symbol)
                }) {
                    return Err(LifecycleError::WrongState {
                        symbol: local_name.clone(),
                        expected: "sorted unique name-candidate sources",
                    });
                }
                prior = Some(&candidate.source);
                if candidate.source.module == self.path {
                    if self.get(candidate.source.symbol.as_ref()).is_none() {
                        return Err(LifecycleError::WrongState {
                            symbol: candidate.source.symbol.clone(),
                            expected: "terminal local name-candidate source",
                        });
                    }
                }
                if candidate.source.module == self.path && candidate.source.symbol == *local_name {
                    return Err(LifecycleError::WrongState {
                        symbol: local_name.clone(),
                        expected: "canonical binding represented as an implicit candidate",
                    });
                }
            }
        }

        for (canonical, binding) in &self.symbols {
            let Some(record) = binding.trait_method() else {
                continue;
            };
            let source = FQSymbol {
                module: self.path.clone(),
                symbol: canonical.clone(),
            };
            let method = trait_method_terminal_method(&source, record).ok_or_else(|| {
                LifecycleError::WrongState {
                    symbol: canonical.clone(),
                    expected: "canonical trait-method terminal in its trait home",
                }
            })?;
            let matches = self
                .symbols
                .get(&method)
                .into_iter()
                .flat_map(|entry| &entry.references)
                .filter(|candidate| candidate.source == source)
                .count();
            if matches != 1 {
                return Err(LifecycleError::WrongState {
                    symbol: canonical.clone(),
                    expected: "exactly one bare projection for a local trait-method terminal",
                });
            }
        }
        Ok(())
    }

    fn binding_owns_candidate_references(&self, binding: &Binding<C>) -> bool {
        let Decl::Trait(record) = &binding.declaration else {
            return false;
        };
        self.symbols
            .values()
            .flat_map(|entry| &entry.references)
            .any(|candidate| {
                candidate.source.module == self.path
                    && candidate
                        .source
                        .symbol
                        .as_ref()
                        .strip_prefix(record.info.name.as_ref())
                        .is_some_and(|suffix| suffix.starts_with('.') && suffix.len() > 1)
            })
    }

    fn note_symbol_mutation(&self, name: &Symbol) {
        let mut registry = self
            .transactions
            .0
            .lock()
            .expect("transaction registry mutex poisoned");
        let revision = registry.revisions.entry(name.clone()).or_default();
        *revision = revision.wrapping_add(1);
    }

    fn symbol_revision(&self, name: &Symbol) -> u64 {
        self.transactions
            .0
            .lock()
            .expect("transaction registry mutex poisoned")
            .revisions
            .get(name)
            .copied()
            .unwrap_or(0)
    }

    fn claimed_slots(&self) -> std::collections::HashSet<usize> {
        let mut claimed: std::collections::HashSet<_> = self
            .retired_slots
            .iter()
            .map(|retired| retired.slot.index())
            .collect();
        for entry in self.symbols.values() {
            let Some(binding) = entry.binding.as_ref() else {
                continue;
            };
            match &binding.declaration {
                Decl::Callable(callable) => {
                    if let Some(slot) = callable.arm.life.claimed_slot() {
                        claimed.insert(slot.index());
                    }
                }
                Decl::Overloaded(declaration) => {
                    claimed.extend(
                        declaration
                            .arms
                            .iter()
                            .filter_map(|arm| arm.callable.life.claimed_slot())
                            .map(|slot| slot.index()),
                    );
                }
                Decl::Macro(declaration) => {
                    claimed.extend(
                        declaration
                            .clauses
                            .iter()
                            .filter_map(|clause| clause.callable.life.claimed_slot())
                            .map(|slot| slot.index()),
                    );
                }
                _ => {}
            }
        }
        claimed
    }
}

fn validate_family_ids(
    symbol: &Symbol,
    ids: impl IntoIterator<Item = crate::CallableArmId>,
) -> Result<(), LifecycleError> {
    for (ordinal, id) in ids.into_iter().enumerate() {
        if id.ordinal() != ordinal {
            return Err(LifecycleError::WrongState {
                symbol: symbol.clone(),
                expected: "a unique contiguous callable-arm roster in declaration order",
            });
        }
    }
    Ok(())
}

fn validate_arm<C: CodeStore>(
    symbol: &Symbol,
    arm: &CallableArm<C>,
    seen: &mut HashSet<usize>,
) -> Result<(), LifecycleError> {
    if matches!(arm.life, Life::Concrete { .. } | Life::Broken { .. })
        && ConcreteType::from_type(&arm.scheme.ty).is_err()
    {
        return Err(LifecycleError::NonConcreteSlot {
            symbol: symbol.clone(),
        });
    }
    if matches!(arm.life, Life::Template { .. }) && ConcreteType::from_type(&arm.scheme.ty).is_ok()
    {
        return Err(LifecycleError::ConcreteTemplate {
            symbol: symbol.clone(),
        });
    }
    if let Some(slot) = arm.life.claimed_slot() {
        validate_slot(slot, seen)?;
    }
    Ok(())
}

fn validate_arm_template_target<C: CodeStore>(
    symbol: &Symbol,
    arm: &CallableArm<C>,
) -> Result<(), LifecycleError> {
    if matches!(
        &arm.life,
        Life::Concrete {
            minted_from: Some(InstanceLink {
                template: CallableTarget::MacroClause { .. },
                ..
            }),
            ..
        }
    ) {
        return Err(LifecycleError::WrongState {
            symbol: symbol.clone(),
            expected: "an instance template target that is not a macro clause",
        });
    }
    Ok(())
}

fn validate_publication_binding<C: CodeStore>(
    binding: &Binding<C>,
    name: &Symbol,
) -> Result<(), LifecycleError> {
    for arm in binding_callable_arm_refs(binding) {
        if matches!(arm.life, Life::Declared { .. } | Life::Broken { .. }) {
            return Err(LifecycleError::WrongState {
                symbol: name.clone(),
                expected: "a settled, non-broken staged callable",
            });
        }
    }
    Ok(())
}

fn binding_is_callable<C: CodeStore>(binding: &Binding<C>) -> bool {
    matches!(
        binding.declaration,
        Decl::Callable(_) | Decl::Overloaded(_) | Decl::Macro(_)
    )
}

fn binding_callable_arm_refs<C: CodeStore>(binding: &Binding<C>) -> Vec<&CallableArm<C>> {
    match &binding.declaration {
        Decl::Callable(callable) => vec![&callable.arm],
        Decl::Overloaded(declaration) => declaration.arms.iter().map(|arm| &arm.callable).collect(),
        Decl::Macro(declaration) => declaration
            .clauses
            .iter()
            .map(|clause| &clause.callable)
            .collect(),
        _ => Vec::new(),
    }
}

fn binding_callable_arms<'a, C: CodeStore>(
    module: &ModuleFullPath,
    name: &Symbol,
    binding: &'a Binding<C>,
) -> Vec<(CallableTarget, &'a CallableArm<C>)> {
    let owner = FQSymbol {
        module: module.clone(),
        symbol: name.clone(),
    };
    match &binding.declaration {
        Decl::Callable(callable) => vec![(CallableTarget::Binding(owner), &callable.arm)],
        Decl::Overloaded(declaration) => declaration
            .arms
            .iter()
            .map(|arm| {
                (
                    CallableTarget::OverloadArm {
                        owner: owner.clone(),
                        arm: arm.id,
                    },
                    &arm.callable,
                )
            })
            .collect(),
        Decl::Macro(declaration) => declaration
            .clauses
            .iter()
            .map(|clause| {
                (
                    CallableTarget::MacroClause {
                        owner: owner.clone(),
                        clause: clause.id,
                    },
                    &clause.callable,
                )
            })
            .collect(),
        _ => Vec::new(),
    }
}

fn binding_callable_arm_mut<'a, C: CodeStore>(
    binding: &'a mut Binding<C>,
    target: &CallableTarget,
) -> Option<&'a mut CallableArm<C>> {
    match (target, &mut binding.declaration) {
        (CallableTarget::Binding(_), Decl::Callable(callable)) => Some(&mut callable.arm),
        (CallableTarget::OverloadArm { arm, .. }, Decl::Overloaded(declaration)) => declaration
            .arms
            .get_mut(arm.ordinal())
            .filter(|candidate| candidate.id == *arm)
            .map(|candidate| &mut candidate.callable),
        (CallableTarget::MacroClause { clause, .. }, Decl::Macro(declaration)) => declaration
            .clauses
            .get_mut(clause.ordinal())
            .filter(|candidate| candidate.id == *clause)
            .map(|candidate| &mut candidate.callable),
        _ => None,
    }
}

fn binding_has_claimed_slot<C: CodeStore>(binding: &Binding<C>) -> bool {
    binding_callable_arm_refs(binding)
        .into_iter()
        .any(|arm| arm.life.claimed_slot().is_some())
}

fn binding_first_claimed_slot<C: CodeStore>(binding: &Binding<C>) -> Option<CallableSlot> {
    binding_callable_arm_refs(binding)
        .into_iter()
        .filter_map(|arm| arm.life.claimed_slot())
        .min_by_key(|slot| slot.index())
}

fn binding_has_compiled_owner<C: CodeStore>(binding: &Binding<C>) -> bool {
    binding_callable_arm_refs(binding).into_iter().any(|arm| {
        matches!(
            arm.life,
            Life::Concrete {
                realization: Realization::Body { code: Some(_), .. },
                ..
            }
        )
    })
}

#[derive(Clone)]
struct PublicationArmSnapshot {
    target: CallableTarget,
    scheme: Scheme,
    slot: Option<CallableSlot>,
}

fn publication_arm_snapshots<C: CodeStore>(
    module: &ModuleFullPath,
    name: &Symbol,
    binding: &Binding<C>,
) -> Vec<PublicationArmSnapshot> {
    binding_callable_arms(module, name, binding)
        .into_iter()
        .map(|(target, arm)| PublicationArmSnapshot {
            target,
            scheme: arm.scheme.clone(),
            slot: arm.life.claimed_slot(),
        })
        .collect()
}

fn publication_arm_pairs<C: CodeStore>(
    module: &ModuleFullPath,
    name: &Symbol,
    prior: Option<&Binding<C>>,
    published: &Binding<C>,
    decision: Option<PlannedAbiDecision>,
) -> Result<
    Vec<(
        Option<PublicationArmSnapshot>,
        Option<PublicationArmSnapshot>,
    )>,
    LifecycleError,
> {
    let old = prior
        .map(|binding| publication_arm_snapshots(module, name, binding))
        .unwrap_or_default();
    let new = publication_arm_snapshots(module, name, published);
    if matches!(decision, Some(PlannedAbiDecision::Change)) {
        return Ok(old
            .into_iter()
            .map(|arm| (Some(arm), None))
            .chain(new.into_iter().map(|arm| (None, Some(arm))))
            .collect());
    }
    let Some(prior) = prior else {
        return Ok(new.into_iter().map(|arm| (None, Some(arm))).collect());
    };

    match (&prior.declaration, &published.declaration) {
        (Decl::Callable(_), Decl::Callable(_)) => {
            Ok(vec![(old.into_iter().next(), new.into_iter().next())])
        }
        (Decl::Overloaded(_), Decl::Overloaded(_)) => {
            let mut unmatched_new: Vec<Option<PublicationArmSnapshot>> =
                new.into_iter().map(Some).collect();
            let mut pairs = Vec::new();
            for old_arm in old {
                let matched = unmatched_new.iter().position(|candidate| {
                    candidate.as_ref().is_some_and(|new_arm| {
                        schemes_alpha_equivalent(&old_arm.scheme, &new_arm.scheme)
                    })
                });
                if let Some(index) = matched {
                    pairs.push((Some(old_arm), unmatched_new[index].take()));
                } else {
                    pairs.push((Some(old_arm), None));
                }
            }
            pairs.extend(
                unmatched_new
                    .into_iter()
                    .flatten()
                    .map(|arm| (None, Some(arm))),
            );
            if matches!(decision, Some(PlannedAbiDecision::Preserve))
                && pairs
                    .iter()
                    .any(|(old, new)| old.is_none() || new.is_none())
            {
                return Err(LifecycleError::WrongState {
                    symbol: name.clone(),
                    expected: "PreserveAbi with an unchanged overload scheme roster",
                });
            }
            Ok(pairs)
        }
        (Decl::Macro(old_macro), Decl::Macro(new_macro)) => {
            let mut pairs = Vec::new();
            let common = old_macro.clauses.len().min(new_macro.clauses.len());
            for ordinal in 0..common {
                if macro_clause_patterns_equal(
                    &old_macro.clauses[ordinal],
                    &new_macro.clauses[ordinal],
                ) {
                    pairs.push((Some(old[ordinal].clone()), Some(new[ordinal].clone())));
                } else {
                    pairs.push((Some(old[ordinal].clone()), None));
                    pairs.push((None, Some(new[ordinal].clone())));
                }
            }
            pairs.extend(old.into_iter().skip(common).map(|arm| (Some(arm), None)));
            pairs.extend(new.into_iter().skip(common).map(|arm| (None, Some(arm))));
            Ok(pairs)
        }
        // A roster/single-body transition changes the callable's language type.
        // Preserve must not fall through to the retire-and-mint pairing below.
        (Decl::Callable(_), Decl::Overloaded(_)) | (Decl::Overloaded(_), Decl::Callable(_))
            if matches!(decision, Some(PlannedAbiDecision::Preserve)) =>
        {
            Err(LifecycleError::WrongState {
                symbol: name.clone(),
                expected: "ChangeAbi for an ordinary/overloaded callable transition",
            })
        }
        _ => Ok(old
            .into_iter()
            .map(|arm| (Some(arm), None))
            .chain(new.into_iter().map(|arm| (None, Some(arm))))
            .collect()),
    }
}

fn macro_clause_patterns_equal<C: CodeStore>(
    left: &MacroClause<C>,
    right: &MacroClause<C>,
) -> bool {
    left.rest_param == right.rest_param
        && left.params.len() == right.params.len()
        && left
            .params
            .iter()
            .zip(&right.params)
            .all(|(left, right)| match (left, right) {
                (crate::MacroParam::Name(left), crate::MacroParam::Name(right)) => left == right,
                (
                    crate::MacroParam::Bracket {
                        fixed: left_fixed,
                        rest: left_rest,
                    },
                    crate::MacroParam::Bracket {
                        fixed: right_fixed,
                        rest: right_rest,
                    },
                ) => left_fixed == right_fixed && left_rest == right_rest,
                _ => false,
            })
}

fn schemes_alpha_equivalent(left: &Scheme, right: &Scheme) -> bool {
    if left.type_vars.len() != right.type_vars.len() {
        return false;
    }
    let mut forward = HashMap::new();
    let mut reverse = HashMap::new();
    for (&left_id, &right_id) in left.type_vars.iter().zip(&right.type_vars) {
        if !bind_alpha_ids(left_id, right_id, &mut forward, &mut reverse) {
            return false;
        }
    }
    if !types_alpha_equivalent(&left.ty, &right.ty, &mut forward, &mut reverse) {
        return false;
    }
    if left.constraints.len() != right.constraints.len() {
        return false;
    }
    left.constraints.iter().all(|(left_id, left_traits)| {
        let Some(right_id) = forward.get(left_id) else {
            return false;
        };
        let Some(right_traits) = right.constraints.get(right_id) else {
            return false;
        };
        trait_sets_equal(left_traits, right_traits)
    })
}

fn bind_alpha_ids(
    left: TypeId,
    right: TypeId,
    forward: &mut HashMap<TypeId, TypeId>,
    reverse: &mut HashMap<TypeId, TypeId>,
) -> bool {
    match (forward.get(&left), reverse.get(&right)) {
        (Some(mapped), Some(back)) => *mapped == right && *back == left,
        (None, None) => {
            forward.insert(left, right);
            reverse.insert(right, left);
            true
        }
        _ => false,
    }
}

fn types_alpha_equivalent(
    left: &Type,
    right: &Type,
    forward: &mut HashMap<TypeId, TypeId>,
    reverse: &mut HashMap<TypeId, TypeId>,
) -> bool {
    match (left, right) {
        (Type::Int, Type::Int)
        | (Type::Bool, Type::Bool)
        | (Type::String, Type::String)
        | (Type::Float, Type::Float) => true,
        (Type::Var(left), Type::Var(right)) => bind_alpha_ids(*left, *right, forward, reverse),
        (Type::Fn(left_params, left_return), Type::Fn(right_params, right_return)) => {
            left_params.len() == right_params.len()
                && left_params
                    .iter()
                    .zip(right_params)
                    .all(|(left, right)| types_alpha_equivalent(left, right, forward, reverse))
                && types_alpha_equivalent(left_return, right_return, forward, reverse)
        }
        (Type::ADT(left_name, left_args), Type::ADT(right_name, right_args)) => {
            left_name == right_name
                && left_args.len() == right_args.len()
                && left_args
                    .iter()
                    .zip(right_args)
                    .all(|(left, right)| types_alpha_equivalent(left, right, forward, reverse))
        }
        (Type::TyConApp(left_head, left_args), Type::TyConApp(right_head, right_args)) => {
            bind_alpha_ids(*left_head, *right_head, forward, reverse)
                && left_args.len() == right_args.len()
                && left_args
                    .iter()
                    .zip(right_args)
                    .all(|(left, right)| types_alpha_equivalent(left, right, forward, reverse))
        }
        _ => false,
    }
}

fn trait_sets_equal(left: &[FQTraitName], right: &[FQTraitName]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .all(|item| right.iter().filter(|candidate| *candidate == item).count() == 1)
        && right
            .iter()
            .all(|item| left.iter().filter(|candidate| *candidate == item).count() == 1)
}

fn mint_publication_slot(
    module: &ModuleFullPath,
    scheme: &Scheme,
    claimed: &mut HashSet<usize>,
) -> Result<CallableSlot, LifecycleError> {
    if let Err(error) = ConcreteType::from_type(&scheme.ty) {
        return Err(LifecycleError::SlotMint(SlotMintError::NotConcrete(error)));
    }
    let index = (0..GOT_TABLE_SIZE)
        .find(|slot| !claimed.contains(slot))
        .ok_or_else(|| {
            LifecycleError::SlotMint(SlotMintError::Exhausted(GotExhausted {
                module: module.clone(),
            }))
        })?;
    claimed.insert(index);
    Ok(CallableSlot(index))
}

fn reconcile_publication_binding<C: CodeStore>(
    module: &ModuleFullPath,
    name: &Symbol,
    mut prior: Option<&mut Binding<C>>,
    published: &mut Binding<C>,
    decision: Option<PlannedAbiDecision>,
    claimed: &mut HashSet<usize>,
    retired_slots: &mut Vec<RetiredSlot>,
) -> Result<Vec<CallablePublicationRecord<C>>, LifecycleError> {
    let pairs = publication_arm_pairs(module, name, prior.as_deref(), published, decision)?;
    let mut records = Vec::with_capacity(pairs.len());
    for (prior_arm, published_arm) in pairs {
        let prior_slot = prior_arm.as_ref().and_then(|arm| arm.slot);
        let displaced_owner = prior_arm.as_ref().and_then(|snapshot| {
            prior
                .as_deref_mut()
                .and_then(|binding| binding_callable_arm_mut(binding, &snapshot.target))
                .and_then(take_compiled_owner_from_arm)
        });
        let mut published_slot = published_arm.as_ref().and_then(|arm| arm.slot);

        match (prior_slot, published_slot) {
            (Some(old_slot), Some(_)) => {
                if !matches!(decision, Some(PlannedAbiDecision::Preserve)) {
                    return Err(LifecycleError::WrongState {
                        symbol: name.clone(),
                        expected: "an explicit ABI publication decision",
                    });
                }
                let snapshot = published_arm.as_ref().expect("published slot has a target");
                let slot = old_slot
                    .rebind(&snapshot.scheme)
                    .map_err(|error| LifecycleError::SlotMint(SlotMintError::NotConcrete(error)))?;
                let arm =
                    binding_callable_arm_mut(published, &snapshot.target).ok_or_else(|| {
                        LifecycleError::WrongState {
                            symbol: name.clone(),
                            expected: "the validated published callable target",
                        }
                    })?;
                set_publication_arm_slot(arm, slot, name)?;
                published_slot = Some(slot);
            }
            (None, Some(_)) => {
                let snapshot = published_arm.as_ref().expect("published slot has a target");
                let slot = mint_publication_slot(module, &snapshot.scheme, claimed)?;
                let arm =
                    binding_callable_arm_mut(published, &snapshot.target).ok_or_else(|| {
                        LifecycleError::WrongState {
                            symbol: name.clone(),
                            expected: "the validated published callable target",
                        }
                    })?;
                set_publication_arm_slot(arm, slot, name)?;
                published_slot = Some(slot);
            }
            (Some(old_slot), None) => retired_slots.push(RetiredSlot {
                slot: old_slot,
                reason: if published_arm.is_some() {
                    RetireReason::TemplateFlip {
                        symbol: name.clone(),
                    }
                } else {
                    RetireReason::AbiChanging {
                        symbol: name.clone(),
                    }
                },
            }),
            (None, None) => {}
        }

        records.push(CallablePublicationRecord {
            prior_target: prior_arm.map(|arm| arm.target),
            published_target: published_arm.map(|arm| arm.target),
            prior_slot,
            published_slot,
            displaced_owner,
        });
    }
    Ok(records)
}

fn retire_absent_binding<C: CodeStore>(
    module: &ModuleFullPath,
    name: &Symbol,
    prior: &mut Binding<C>,
    retired_slots: &mut Vec<RetiredSlot>,
) -> Vec<CallablePublicationRecord<C>> {
    publication_arm_snapshots(module, name, prior)
        .into_iter()
        .map(|snapshot| {
            let displaced_owner = binding_callable_arm_mut(prior, &snapshot.target)
                .and_then(take_compiled_owner_from_arm);
            if let Some(slot) = snapshot.slot {
                retired_slots.push(RetiredSlot {
                    slot,
                    reason: RetireReason::AbiChanging {
                        symbol: name.clone(),
                    },
                });
            }
            CallablePublicationRecord {
                prior_target: Some(snapshot.target),
                published_target: None,
                prior_slot: snapshot.slot,
                published_slot: None,
                displaced_owner,
            }
        })
        .collect()
}

fn binding_compiled_body_targets<C: CodeStore>(
    module: &ModuleFullPath,
    name: &Symbol,
    binding: &Binding<C>,
) -> Vec<CallableTarget> {
    binding_callable_arms(module, name, binding)
        .into_iter()
        .filter_map(|(target, arm)| {
            matches!(
                arm.life,
                Life::Concrete {
                    realization: Realization::Body { .. },
                    ..
                }
            )
            .then_some(target)
        })
        .collect()
}

fn attach_compiled_publication_owners<C: CodeStore>(
    plan: &mut StagedPublicationPlan<C>,
    mut compiled_owners: HashMap<CallableTarget, C>,
) -> Result<(), (LifecycleError, HashMap<CallableTarget, C>)> {
    let expected: HashSet<_> = plan.compiled_body_targets.iter().cloned().collect();
    let mut unexpected: Vec<_> = compiled_owners
        .keys()
        .filter(|target| !expected.contains(*target))
        .cloned()
        .collect();
    unexpected.sort();
    if let Some(target) = unexpected.into_iter().next() {
        return Err((owner_set_error(&target), compiled_owners));
    }
    if let Some(target) = plan
        .compiled_body_targets
        .iter()
        .find(|target| !compiled_owners.contains_key(*target))
    {
        return Err((owner_set_error(target), compiled_owners));
    }

    let mut attached = Vec::with_capacity(plan.compiled_body_targets.len());
    for target in &plan.compiled_body_targets {
        let Some(owner) = compiled_owners.remove(target) else {
            return Err((
                owner_set_error(target),
                recover_attached_publication_owners(plan, compiled_owners, &attached),
            ));
        };
        match attach_compiled_owner_to_candidate(&mut plan.candidate, target, owner) {
            Ok(()) => attached.push(target.clone()),
            Err((reason, owner)) => {
                compiled_owners.insert(target.clone(), owner);
                return Err((
                    reason,
                    recover_attached_publication_owners(plan, compiled_owners, &attached),
                ));
            }
        }
    }
    Ok(())
}

fn owner_set_error(target: &CallableTarget) -> LifecycleError {
    LifecycleError::WrongState {
        symbol: callable_target_owner(target).symbol.clone(),
        expected: "one compiled owner for every staged Concrete Body target and no other target",
    }
}

fn attach_compiled_owner_to_candidate<C: CodeStore>(
    candidate: &mut SymbolTable<C, ()>,
    target: &CallableTarget,
    owner: C,
) -> Result<(), (LifecycleError, C)> {
    let name = callable_target_owner(target).symbol.clone();
    let arm = match candidate.callable_target_mut(target) {
        Ok(arm) => arm,
        Err(reason) => return Err((reason, owner)),
    };
    let Life::Concrete {
        realization: Realization::Body { code, .. },
        ..
    } = &mut arm.life
    else {
        return Err((
            LifecycleError::WrongState {
                symbol: name.clone(),
                expected: "Concrete Body",
            },
            owner,
        ));
    };
    if code.is_some() {
        return Err((
            LifecycleError::WrongState {
                symbol: name.clone(),
                expected: "uncompiled Concrete Body",
            },
            owner,
        ));
    }
    *code = Some(owner);
    Ok(())
}

fn recover_attached_publication_owners<C: CodeStore>(
    plan: &mut StagedPublicationPlan<C>,
    mut compiled_owners: HashMap<CallableTarget, C>,
    attached: &[CallableTarget],
) -> HashMap<CallableTarget, C> {
    for target in attached {
        if let Ok(arm) = plan.candidate.callable_target_mut(target)
            && let Some(owner) = take_compiled_owner_from_arm(arm)
        {
            compiled_owners.insert(target.clone(), owner);
        }
    }
    compiled_owners
}

fn take_compiled_owner_from_arm<C: CodeStore>(arm: &mut CallableArm<C>) -> Option<C> {
    let Life::Concrete {
        realization: Realization::Body { code, .. },
        ..
    } = &mut arm.life
    else {
        return None;
    };
    code.take()
}

fn apply_broken_transition<C: CodeStore, L: LinkerStore>(
    table: &mut SymbolTable<C, L>,
    name: &Symbol,
    error: crate::BrokenProvenance,
) -> Result<BrokenTransition<C>, LifecycleError> {
    let Some(entry) = table.symbols.get_mut(name) else {
        return Err(LifecycleError::MissingBinding {
            symbol: name.clone(),
        });
    };
    let Some(callable) = entry.callable_mut() else {
        return Err(LifecycleError::NotCallable {
            symbol: name.clone(),
        });
    };
    let (slot, displaced_owner) = match &mut callable.arm.life {
        Life::Concrete {
            slot, realization, ..
        } => {
            let displaced_owner = match realization {
                Realization::Body { code, .. } => code.take(),
                Realization::ExternShim { .. }
                | Realization::Dll
                | Realization::FacadeOf { .. } => None,
            };
            (*slot, displaced_owner)
        }
        _ => {
            return Err(LifecycleError::WrongState {
                symbol: name.clone(),
                expected: "Concrete",
            });
        }
    };
    callable.arm.life = Life::Broken { slot, error };
    Ok(BrokenTransition {
        slot,
        displaced_owner,
    })
}

fn set_publication_arm_slot<C: CodeStore>(
    arm: &mut CallableArm<C>,
    slot: CallableSlot,
    name: &Symbol,
) -> Result<(), LifecycleError> {
    let Life::Concrete {
        slot: current_slot, ..
    } = &mut arm.life
    else {
        return Err(LifecycleError::WrongState {
            symbol: name.clone(),
            expected: "a slotted staged concrete callable",
        });
    };
    *current_slot = slot;
    Ok(())
}

fn validate_publication_collision<C: CodeStore, L: LinkerStore>(
    table: &SymbolTable<C, L>,
    name: &Symbol,
    prior: Option<&Binding<C>>,
    staged: &Binding<C>,
) -> Result<(), LifecycleError> {
    let Some(prior) = prior else {
        return Ok(());
    };
    match (&prior.declaration, &staged.declaration) {
        (Decl::Callable(existing), Decl::Callable(replacement)) => {
            if existing.arm.life.claimed_slot().is_some()
                && matches!(
                    &replacement.arm.life,
                    Life::Inline { .. } | Life::HostPromised
                )
            {
                return Err(LifecycleError::WrongState {
                    symbol: name.clone(),
                    expected: "a slotted callable to become Template or remain slotted",
                });
            }
            if same_publishable_origin(&existing.origin, &replacement.origin) {
                Ok(())
            } else {
                Err(LifecycleError::IllegalOriginState {
                    symbol: name.clone(),
                })
            }
        }
        // Adding/removing signatures may change a plain defn's representation.
        // Semantic admission belongs to integration; slot and owner moves remain
        // in the ordinary publication transaction. Other origins cannot cross.
        (Decl::Overloaded(_), Decl::Callable(callable))
        | (Decl::Callable(callable), Decl::Overloaded(_))
            if matches!(callable.origin, CallableOrigin::Plain) =>
        {
            Ok(())
        }
        (Decl::Overloaded(_), Decl::Overloaded(_)) | (Decl::Macro(_), Decl::Macro(_)) => Ok(()),
        (Decl::TraitMethod(existing), Decl::TraitMethod(replacement))
            if prior.visibility == staged.visibility
                && trait_method_records_equal(existing, replacement) =>
        {
            Ok(())
        }
        (_, Decl::Callable(_) | Decl::Overloaded(_) | Decl::Macro(_)) => {
            Err(LifecycleError::NotCallable {
                symbol: name.clone(),
            })
        }
        (_, Decl::TraitMethod(_)) => Err(LifecycleError::WrongState {
            symbol: name.clone(),
            expected: "a vacant or identical canonical trait-method declaration",
        }),
        (Decl::Callable(_) | Decl::Overloaded(_) | Decl::Macro(_) | Decl::TraitMethod(_), _) => {
            Err(LifecycleError::WrongState {
                symbol: name.clone(),
                expected: "explicit callable or trait-method displacement",
            })
        }
        _ if table.binding_owns_candidate_references(prior) => Err(LifecycleError::WrongState {
            symbol: name.clone(),
            expected: "a binding without owned candidate references",
        }),
        _ => Ok(()),
    }
}

fn same_publishable_origin(existing: &CallableOrigin, replacement: &CallableOrigin) -> bool {
    match (existing, replacement) {
        (CallableOrigin::Plain, CallableOrigin::Plain)
        | (CallableOrigin::RustPrimitive, CallableOrigin::RustPrimitive) => true,
        (
            CallableOrigin::TraitMethod {
                shell: left_shell,
                trait_name: left_trait,
                impl_type: left_impl,
            },
            CallableOrigin::TraitMethod {
                shell: right_shell,
                trait_name: right_trait,
                impl_type: right_impl,
            },
        ) => left_shell == right_shell && left_trait == right_trait && left_impl == right_impl,
        (
            CallableOrigin::Ctor {
                type_name: left_type,
                tag: left_tag,
                field_count: left_fields,
                internal: left_internal,
                ..
            },
            CallableOrigin::Ctor {
                type_name: right_type,
                tag: right_tag,
                field_count: right_fields,
                internal: right_internal,
                ..
            },
        ) => {
            left_type == right_type
                && left_tag == right_tag
                && left_fields == right_fields
                && left_internal == right_internal
        }
        (
            CallableOrigin::Accessor {
                type_name: left_type,
                field: left_field,
            },
            CallableOrigin::Accessor {
                type_name: right_type,
                field: right_field,
            },
        ) => left_type == right_type && left_field == right_field,
        (
            CallableOrigin::PlatformEffect {
                scheduling_class: left_class,
                poll_shape: left_poll,
            },
            CallableOrigin::PlatformEffect {
                scheduling_class: right_class,
                poll_shape: right_poll,
            },
        ) => left_class == right_class && left_poll == right_poll,
        _ => false,
    }
}

fn same_synthesized_origin(existing: &CallableOrigin, replacement: &CallableOrigin) -> bool {
    matches!(
        existing,
        CallableOrigin::Ctor { .. } | CallableOrigin::Accessor { .. }
    ) && matches!(
        replacement,
        CallableOrigin::Ctor { .. } | CallableOrigin::Accessor { .. }
    ) && same_publishable_origin(existing, replacement)
}

fn merge_written_trait_impls<C: CodeStore, L: LinkerStore>(
    table: &mut SymbolTable<C, L>,
    staged: Vec<WrittenTraitImpl>,
) -> Result<(), LifecycleError> {
    let mut positions = HashMap::new();
    for (index, record) in table.written_trait_impls.iter().enumerate() {
        let key = crate::trait_impl_key(&record.impl_type, &record.trait_name);
        if positions.insert(key.clone(), index).is_some() {
            return Err(LifecycleError::WrongState {
                symbol: key,
                expected: "one written trait-implementation record per canonical key",
            });
        }
    }
    for record in staged {
        let key = crate::trait_impl_key(&record.impl_type, &record.trait_name);
        if validate_written_trait_impl(&record, Some(&table.path)).is_err() {
            return Err(LifecycleError::WrongState {
                symbol: key,
                expected: "a valid writer-owned trait-implementation record",
            });
        }
        match positions.get(&key).copied() {
            Some(index) => table.written_trait_impls[index] = record,
            None => {
                positions.insert(key, table.written_trait_impls.len());
                table.written_trait_impls.push(record);
            }
        }
    }
    Ok(())
}

fn validate_slot(
    slot: CallableSlot,
    seen: &mut std::collections::HashSet<usize>,
) -> Result<(), LifecycleError> {
    if slot.index() >= GOT_TABLE_SIZE {
        return Err(LifecycleError::SlotOutOfRange { slot: slot.index() });
    }
    if !seen.insert(slot.index()) {
        return Err(LifecycleError::DuplicateSlot { slot: slot.index() });
    }
    Ok(())
}

fn callable_target_owner(target: &CallableTarget) -> &FQSymbol {
    match target {
        CallableTarget::Binding(owner)
        | CallableTarget::OverloadArm { owner, .. }
        | CallableTarget::MacroClause { owner, .. } => owner,
    }
}

fn canonical_callees(mut callees: Vec<FQSymbol>) -> Vec<FQSymbol> {
    callees
        .sort_by(|left, right| (&left.module, &left.symbol).cmp(&(&right.module, &right.symbol)));
    callees.dedup();
    callees
}

fn canonicalize_name_candidates(candidates: &mut [NameCandidate]) {
    candidates.sort_by(|left, right| {
        (&left.source.module, &left.source.symbol)
            .cmp(&(&right.source.module, &right.source.symbol))
    });
}

fn canonicalize_and_dedup_name_candidates(candidates: &mut Vec<NameCandidate>) {
    canonicalize_name_candidates(candidates);
    let mut deduped: Vec<NameCandidate> = Vec::with_capacity(candidates.len());
    for candidate in candidates.drain(..) {
        if let Some(existing) = deduped
            .last_mut()
            .filter(|existing| existing.source == candidate.source)
        {
            if candidate.visibility == Visibility::Public {
                existing.visibility = Visibility::Public;
            }
        } else {
            deduped.push(candidate);
        }
    }
    *candidates = deduped;
}

fn trait_method_terminal_method(source: &FQSymbol, record: &TraitMethodRecord) -> Option<Symbol> {
    if record.trait_name.module != source.module {
        return None;
    }
    let (parent, method) = source.symbol.as_ref().rsplit_once('.')?;
    if parent != record.trait_name.name.as_ref()
        || method.is_empty()
        || crate::member_key(parent, method) != source.symbol
    {
        return None;
    }
    Some(Symbol::from(method))
}

fn trait_method_records_equal(left: &TraitMethodRecord, right: &TraitMethodRecord) -> bool {
    left.scheme.type_vars == right.scheme.type_vars
        && left.scheme.constraints == right.scheme.constraints
        && left.scheme.ty == right.scheme.ty
        && left.param_names == right.param_names
        && left.docstring == right.docstring
        && left.trait_name == right.trait_name
}

fn retired_slot_symbol(retired: &RetiredSlot) -> &Symbol {
    match &retired.reason {
        RetireReason::TemplateFlip { symbol } | RetireReason::AbiChanging { symbol } => symbol,
    }
}

fn module_error(message: impl Into<String>) -> crate::CranelispError {
    crate::CranelispError::ModuleError {
        message: message.into(),
        location: crate::ErrorLocation::unknown(),
    }
}

#[allow(clippy::result_large_err)]
fn validate_written_trait_impl(
    record: &WrittenTraitImpl,
    writer: Option<&ModuleFullPath>,
) -> Result<(), crate::CranelispError> {
    if record.methods.is_empty() {
        return Err(module_error(format!(
            "malformed written-impl record: impl of {} for {} has an empty method list",
            record.trait_name, record.impl_type
        )));
    }
    if let Some(writer) = writer
        && &record.impl_module != writer
    {
        return Err(module_error(format!(
            "written trait impl for {} and {} belongs to writer `{}`, not table `{writer}`",
            record.trait_name, record.impl_type, record.impl_module
        )));
    }
    Ok(())
}

fn written_trait_impl_binding<C: CodeStore>(record: &WrittenTraitImpl) -> Binding<C> {
    Binding::new(
        Decl::ImplShell(ImplShell {
            trait_name: record.trait_name.clone(),
            impl_type: record.impl_type.clone(),
            impl_module: record.impl_module.clone(),
            methods: record.methods.clone(),
        }),
        record.visibility,
    )
}

fn binding_matches_written_trait_impl<C: CodeStore>(
    binding: &Binding<C>,
    record: &WrittenTraitImpl,
) -> bool {
    matches!(
        binding,
        Binding {
            visibility,
            declaration: Decl::ImplShell(shell),
        } if *visibility == record.visibility
            && shell.trait_name == record.trait_name
            && shell.impl_type == record.impl_type
            && shell.impl_module == record.impl_module
            && shell.methods == record.methods
    )
}

// The instance scheme is authoritative here: its template may live in another
// table. Installation and restored-state validation share this exact projection.
fn settled_instance_key(link: &InstanceLink, scheme: &Scheme) -> Result<Symbol, LifecycleError> {
    let owner = crate::lifecycle::instance_owner(&link.template).map_err(|_| {
        LifecycleError::WrongState {
            symbol: match &link.template {
                CallableTarget::Binding(owner)
                | CallableTarget::OverloadArm { owner, .. }
                | CallableTarget::MacroClause { owner, .. } => owner.symbol.clone(),
            },
            expected: "an instance template target that is not a macro clause",
        }
    })?;
    let concrete = ConcreteType::from_type(&scheme.ty)
        .map_err(|error| LifecycleError::SlotMint(SlotMintError::NotConcrete(error)))?;
    crate::concrete_callable_key(owner, &concrete).map_err(|_| LifecycleError::WrongState {
        symbol: owner.symbol.clone(),
        expected: "a concrete function instance scheme",
    })
}

fn validate_instance_key<C: CodeStore>(
    symbol: &Symbol,
    callable: &Callable<C>,
) -> Result<(), LifecycleError> {
    let Life::Concrete {
        minted_from: Some(link),
        ..
    } = &callable.arm.life
    else {
        return Ok(());
    };
    let expected = settled_instance_key(link, &callable.arm.scheme)?;
    if *symbol != expected {
        return Err(LifecycleError::InstanceKeyMismatch {
            symbol: symbol.clone(),
            expected,
        });
    }
    Ok(())
}

fn validate_origin_state<C: CodeStore>(
    symbol: &Symbol,
    callable: &Callable<C>,
) -> Result<(), LifecycleError> {
    use CallableOrigin::{Accessor, Ctor, Plain, PlatformEffect, RustPrimitive, TraitMethod};

    let state_legal = matches!(
        (&callable.origin, &callable.arm.life),
        (PlatformEffect { .. }, Life::Concrete { .. })
            | (RustPrimitive, Life::Template { .. } | Life::Concrete { .. })
            | (RustPrimitive, Life::Inline { .. } | Life::HostPromised)
            | (
                Plain | TraitMethod { .. },
                Life::Declared { .. }
                    | Life::Template { .. }
                    | Life::Concrete { .. }
                    | Life::Broken { .. },
            )
            | (
                Ctor { .. } | Accessor { .. },
                Life::Template { .. } | Life::Concrete { .. } | Life::Broken { .. },
            )
    );
    if !state_legal {
        return Err(LifecycleError::IllegalOriginState {
            symbol: symbol.clone(),
        });
    }

    let payload_legal = match (&callable.origin, &callable.arm.life) {
        (
            RustPrimitive,
            Life::Template {
                body: TemplateBody::UniformRust { .. },
                kind: TemplateKind::Parametric,
                ..
            },
        ) => true,
        (
            Ctor { .. } | Accessor { .. },
            Life::Template {
                body: TemplateBody::Synth(_),
                ..
            },
        ) => true,
        (
            Plain | TraitMethod { .. },
            Life::Template {
                body: TemplateBody::Ast(_),
                ..
            },
        ) => true,
        (_, Life::Template { .. }) => false,
        (
            PlatformEffect { .. },
            Life::Concrete {
                realization: Realization::Dll,
                ..
            },
        ) => true,
        (
            RustPrimitive,
            Life::Concrete {
                realization: Realization::ExternShim { .. } | Realization::FacadeOf { .. },
                ..
            },
        ) => true,
        (
            Plain | TraitMethod { .. } | Ctor { .. } | Accessor { .. },
            Life::Concrete {
                realization: Realization::Body { .. },
                ..
            },
        ) => true,
        (_, Life::Concrete { .. }) => false,
        _ => true,
    };
    if !payload_legal {
        return Err(LifecycleError::IllegalRealization {
            symbol: symbol.clone(),
        });
    }
    Ok(())
}

fn same_redeclarable_origin(existing: &CallableOrigin, replacement: &CallableOrigin) -> bool {
    match (existing, replacement) {
        (CallableOrigin::Plain, CallableOrigin::Plain) => true,
        (
            CallableOrigin::TraitMethod {
                shell: left_shell,
                trait_name: left_trait,
                impl_type: left_impl,
            },
            CallableOrigin::TraitMethod {
                shell: right_shell,
                trait_name: right_trait,
                impl_type: right_impl,
            },
        ) => left_shell == right_shell && left_trait == right_trait && left_impl == right_impl,
        _ => false,
    }
}
/// A macro parameter: either a simple name or a bracket destructuring.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MacroParam {
    /// Simple name binding
    Name(Symbol),
    /// Bracket destructuring: `[fixed... & rest]`
    Bracket {
        fixed: Vec<Symbol>,
        rest: Option<Symbol>,
    },
}

// --- Import/Export (Ring 2) ---

/// What names to import from a module.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ImportNames {
    Specific(Vec<Symbol>),
    Glob,
    MemberGlob(Symbol),
    None,
}

/// An import declaration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImportSpec {
    pub module_path: ModuleFullPath,
    pub alias: Option<ModuleName>,
    pub names: ImportNames,
    pub span: Span,
}

/// An export declaration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExportSpec {
    pub module_path: ModuleFullPath,
    pub names: ImportNames,
    pub span: Span,
}

// `ImplSexp` DELETED (S119, FIXME 0918 — the S87 dead-surface class): a
// zero-consumer public type (not a field anywhere, in-crate included). Impl
// forms are processed directly; the persisted trait-impl record is
// `WrittenTraitImpl` (below) and the discovery shell is
// `Decl::ImplShell`.

// --- Platform Declarations ---

/// A `(platform <name>)` declaration extracted from top-level forms.
///
/// **Form-record** per Decision 33 — parallel to `ImportSpec` / `ExportSpec` /
/// `ModDecl`. Carries only what the user wrote in source order, for `.cl`
/// regeneration per `repl/spec.md` §15.4. Resolved data (manifest path,
/// loaded DLL handle) is NOT carried here.
///
/// **Spec grounding.** Per spec §2.2.9 grammar
/// (`platform_form = '(' 'platform' SYMBOL ')'`) the form takes a single
/// bare symbol — no alias is permitted. Per spec §10.9 the form is valid
/// only in the entry module; non-entry modules use
/// `(import [platform.<name> [*]])`. Per spec §8.9.3 the form registers a
/// synthetic module at `symbol_tables["platform.<name>"]`. (As stated above,
/// the loaded DLL handle is NOT carried on that module's `SymbolTable` —
/// it is retained int-side in `SharedState.kept_dlls`, `src/platform.rs`.)
///
/// **Standing target narrow (S69 Submission 21; re-affirmed S119, FIXME
/// 0919).** `name: String → name: ModuleName` per the newtype rule
/// (`design/arch/CLAUDE.md` §"String Newtypes"). **Trigger:** rides the
/// first change-set that touches the field's construction sites. The retired-shape fields
/// `manifest_path` and `alias` are NOT introduced — `manifest_path` is
/// resolved data (belongs elsewhere); `alias` is excluded by spec §2.2.9
/// grammar.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PlatformSpec {
    pub name: String,
    pub span: Span,
}

// --- Module Declarations ---

/// A parsed `(mod name)` or `(mod- name)` declaration.
///
/// **Lifecycle of `inline_body`** (forward reference for readers tracing
/// the spec §8.2.2 path):
///
/// - Frontend's `parse_mod_decl` populates `inline_body: Some(forms)` when
///   `(mod name forms…)` is parsed with body.
/// - Int's `worker::handle_mod` consumes the forms to write the backing
///   submodule file via `write_inline_mod_to_disk`.
/// - Int's source-rewriter (per `repl/spec.md` §15.4 regeneration path)
///   MUST emit `ModDecl` as `(mod name)` form regardless of `inline_body`
///   — closing spec §8.2.2 step 2 ("rewrite the parent file, replacing
///   `(mod name form1 form2 ...)` with `(mod name)`"). The rewrite is
///   currently unimplemented; tracked by
///   `design/arch/fixmes/0217-inline-module-spec-rewrite.md` targeting `/int`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModDecl {
    pub name: ModuleName,
    pub visibility: Visibility,
    pub inline_body: Option<Vec<Sexp>>,
    pub span: Span,
}

// `StructuralDeclEntry` DELETED (S119, FIXME 0918) — see the note at the
// former `append_structural_decl` site: the pub structural Vec fields are the
// append contract; the enum carrier was constructed nowhere.

// `use crate::JitSymbol;` retired (S69 Submission 36 — the `jit_name` field
// on the former primitive discriminator is gone; the symbol-table key IS the JIT linker
// name uniformly per `src/CLAUDE.md` §"JIT Symbol Names"). Re-introduce
// only when another use site needs JitSymbol within this file.

// --- Module map graph operations (Sprint 67 hack-back; FIXME 0192 + 0193) ---
//
// Atomic primitives over `DashMap<ModuleFullPath, SymbolTable<C, L>>` that
// previously lived as `pub` methods on `cranelisp-typecheck::TypeCheckEnv`.
// Relocated here per the disposition table — these are pure graph ops on
// the module store and rightly live with the storage they operate on, not
// in the inference engine that borrows it. Typecheck imports them back at
// internal use sites.

/// Outcome of an `ensure_module_exists` call.
///
/// Used by observability hooks to distinguish a fresh creation from an
/// already-present module (the latter being the common case once the
/// session has loaded the module map).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnsureOutcome {
    /// The module's symbol table was created (vacant → inserted).
    Created,
    /// The module's symbol table was already present (no change).
    AlreadyPresent,
}

/// Ensure a module's symbol table exists in `modules`, creating an empty
/// table if absent. Atomic check-then-insert via DashMap's `entry()`. No
/// seeding — per Principle 17 + FIXME 0193 amendment, modules start empty;
/// special-form metadata lives at root `""` and is never replicated.
///
/// Returns the outcome so callers (observability, the orchestrator) can
/// distinguish a fresh creation from an already-present module.
pub fn ensure_module_exists<C, L>(
    modules: &dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>,
    path: &ModuleFullPath,
) -> EnsureOutcome
where
    C: CodeStore,
    L: LinkerStore,
{
    use dashmap::mapref::entry::Entry;
    match modules.entry(path.clone()) {
        Entry::Occupied(_) => EnsureOutcome::AlreadyPresent,
        Entry::Vacant(slot) => {
            slot.insert(SymbolTable::<C, L>::new_with_params(path.clone()));
            EnsureOutcome::Created
        }
    }
}

/// The per-module GOT **data-symbol name** — the single source of truth for
/// the relocation-symbol naming scheme that addresses a module's `GotTable`
/// slab base.
///
/// Every module `M` exposes its GOT slab as a data symbol named
/// `__cranelisp_got_{flat}`, where `flat` is `M`'s dotted path with `.`
/// replaced by `_` (and the empty/entry path mapped to `_entry`). Backend
/// codegen emits a `Linkage::Import` `global_value` against this name for
/// cross-module GOT-indirect calls (Decision 23/36); int registers the slab
/// base under this name (JIT `symbol_lookup_fn` / cache-hit
/// `Linker::register_symbol` / `--link` relocation).
///
/// This naming scheme is consumed by **two crates** — `cranelisp-backend`
/// (codegen relocation) and `int` (JIT/cache/link symbol registration) — so
/// it lives here in `cranelisp-types`, the data-and-contract home, rather than
/// being duplicated or reached-into across the backend boundary. It is a pure
/// string function over `ModuleFullPath` with zero codegen dependency, a peer
/// of `ensure_module_exists`. Relocated DOWN from `cranelisp-backend`'s
/// former `pub(crate) compiler::got_data_symbol_name` at S76 per the /arch
/// Phase 2 review (single-source-of-truth, Principle 7); the backend keeps a
/// one-line forward fenced by a corpus-equality test.
///
/// **Injective escape (S119, FIXME 0748 — safety-register R4).** The former
/// bare `.`→`_` flatten was non-injective: `a.b` and `a_b` both minted
/// `__cranelisp_got_a_b` — two modules sharing ONE GOT slab data symbol, a
/// constructible cross-module wrong-slab dispatch. The flatten is now the
/// unambiguously-decodable escape recovered from the retired backend
/// `escape_symbol` scheme:
///
/// - `_` → `__`, `.` → `_d`, `-` → `_h`, any other non-alphanumeric
///   codepoint → `_u{cp:06x}`; alphanumerics pass through.
/// - **Purely-alphanumeric paths are fixed points** — load-bearing:
///   `__cranelisp_got_primitives` is an `export_name` LITERAL in
///   `cranelisp-primitives/src/lib.rs` that every `--link` binary links
///   against.
/// - The `_entry` sentinel for the empty path is **outside the escape
///   image** (an escaped path can begin `__`/`_d`/`_h`/`_u` but never `_e`).
/// - **The synthetic `platform.*` namespace is a carve-out** that keeps the
///   legacy `.`→`_` join verbatim: the platform GOT symbol is a RATIFIED
///   C-ABI literal minted by the DLL itself
///   (`#[export_name = concat!("__cranelisp_got_platform_", name)]`,
///   `cranelisp-platform/src/declare.rs` — `platform-interface.md` §1's
///   three-exports contract, linked directly by every `--link` binary and
///   `dlsym`'d by the host), so the host-side mint MUST reproduce it. This is
///   not a Principle-19 name privilege: `platform.<name>` is a synthetic
///   namespace *by construction* (spec §8.9.3 — only the `(platform …)` form
///   creates these modules), and the prefix here is the namespace's
///   definition, exactly like a synthetic-module construction site. Named
///   residual (recorded on the R4 register row): a platform whose name begins
///   `d`/`h`/`u`/`_` could collide with the escape image of a contrived
///   root-module spelling (`platform-x` vs a platform named `hx`); closing it
///   is loader-side platform-name validation, not a mint change.
///
/// Decoding is unambiguous (every `_` in the image starts exactly one legal
/// escape pair), so the mint is injective by construction over the
/// non-platform domain; the round-trip battery in `module/tests.rs` is the
/// standing witness. Changing this scheme renames every cached `.o`'s
/// relocations — a cache-invalidation event covered by the
/// `CACHE_SCHEMA_VERSION` window of the change-set that lands it (S119: the
/// 23→24 window).
pub fn got_data_symbol_name(module_path: &ModuleFullPath) -> String {
    let path: &str = module_path.as_ref();
    if path.is_empty() {
        return "__cranelisp_got__entry".to_string();
    }
    // Platform carve-out: the DLL's export_name literal is the authority.
    if path == "platform" || path.starts_with("platform.") {
        return format!("__cranelisp_got_{}", path.replace('.', "_"));
    }
    let mut flat = String::with_capacity(path.len());
    for ch in path.chars() {
        match ch {
            '_' => flat.push_str("__"),
            '.' => flat.push_str("_d"),
            '-' => flat.push_str("_h"),
            c if c.is_ascii_alphanumeric() => flat.push(c),
            c => {
                use std::fmt::Write as _;
                write!(flat, "_u{:06x}", c as u32).expect("String write");
            }
        }
    }
    format!("__cranelisp_got_{flat}")
}

/// Injective module-qualified linker identity for one complete concrete type.
///
/// Part of the **result-root grammar**: the program-result release symbol is
/// minted over `ConcreteType::result_root()` (the single IO-head-strip rule,
/// FIXME 0898) — backend's result-root glue enumeration and int's
/// `release_key` both derive the root through that method and the symbol
/// through this one.
pub fn drop_glue_symbol_name(module: &ModuleFullPath, ty: &ConcreteType) -> LinkerSymbol {
    let mut out = String::from("__cranelisp_drop_");
    encode_component(&mut out, module.as_ref());
    out.push('_');
    encode_concrete_type(&mut out, ty);
    LinkerSymbol::from(out)
}

fn encode_component(out: &mut String, value: &str) {
    use std::fmt::Write as _;
    write!(out, "{}_", value.len()).expect("String write");
    for byte in value.as_bytes() {
        write!(out, "{byte:02x}").expect("String write");
    }
}

fn encode_arity(out: &mut String, n: usize) {
    use std::fmt::Write as _;
    write!(out, "{n}_").expect("String write");
}

fn encode_concrete_type(out: &mut String, ty: &ConcreteType) {
    match ty {
        ConcreteType::Int => out.push('i'),
        ConcreteType::Bool => out.push('b'),
        ConcreteType::String => out.push('s'),
        ConcreteType::Float => out.push('f'),
        ConcreteType::Fn(params, ret) => {
            out.push('n');
            encode_arity(out, params.len());
            for param in params {
                encode_concrete_type(out, param);
            }
            encode_concrete_type(out, ret);
        }
        ConcreteType::ADT(name, args) => {
            out.push('a');
            encode_component(out, name.module.as_ref());
            encode_component(out, name.name.as_ref());
            encode_arity(out, args.len());
            for arg in args {
                encode_concrete_type(out, arg);
            }
        }
    }
}

/// Install a pre-built `SymbolTable` at `path`. Used by the cache-hit branch
/// of `CompilerSession::introduce_module` — the cached metadata is decoded
/// into a `SymbolTable` and installed atomically. Overwrites any existing
/// entry at `path` (consistent with the pre-S67 `restore_cached_module`
/// behaviour, which unconditionally inserted).
pub fn install_module<C, L>(
    modules: &dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>,
    path: ModuleFullPath,
    table: SymbolTable<C, L>,
) where
    C: CodeStore,
    L: LinkerStore,
{
    modules.insert(path, table);
}

// --- Chain-follow primitives (Sprint 67 hack-back — FIXME 0192 methods 1, 3, 5, 7) ---
//
// These free fns operate purely on the `&DashMap<ModuleFullPath, SymbolTable>`
// data home. They do NOT consult typecheck-owned cluster staging — they are
// the live-only chain walkers, intended for cross-crate read consumers
// (REPL display, introspection in `int`). Cluster-mode consumers (inside
// typecheck) keep the staging-aware methods on `TypeCheckEnv`.

/// Compatibility depth bound retained for module-routing chain consumers.
pub const CHAIN_FOLLOW_DEPTH_LIMIT: usize = 10;

/// Iterate the (name, entry) pairs of `module_path`'s symbol table.
///
/// Live-only variant of `TypeCheckEnv::for_each_in_module`. Used by the
/// relocated `get_impls_for_type_chain` / `get_implementing_types_chain`
/// free fns; cross-crate consumers (REPL display) probe live state only.
pub fn for_each_in_module<C, L, F>(
    modules: &dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_path: &ModuleFullPath,
    mut f: F,
) where
    C: CodeStore,
    L: LinkerStore,
    F: FnMut(&Symbol, &Binding<C>),
{
    if let Some(guard) = modules.get(module_path) {
        for (k, v) in guard.all_symbols() {
            f(k, v);
        }
    }
}

/// Resolve a uniquely exposed terminal candidate from a live module table.
pub fn resolve_terminal_entry_and_home<C, L>(
    modules: &dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_path: &ModuleFullPath,
    name: &str,
) -> Option<(Binding<C>, ModuleFullPath)>
where
    C: CodeStore,
    L: LinkerStore,
{
    resolve_terminal_entry_home_and_key(modules, module_path, name)
        .map(|(entry, home, _key)| (entry, home))
}

/// Keyed sibling retained privately while resolution callers migrate to
/// `Resolved::canonical`.
pub(crate) fn resolve_terminal_entry_home_and_key<C, L>(
    modules: &dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_path: &ModuleFullPath,
    name: &str,
) -> Option<(Binding<C>, ModuleFullPath, Symbol)>
where
    C: CodeStore,
    L: LinkerStore,
{
    let source = {
        let guard = modules.get(module_path)?;
        let candidates = guard.name_candidates(&Symbol::from(name));
        if candidates.len() != 1 {
            return None;
        }
        candidates.into_iter().next()?.source
    };
    let entry = modules
        .get(&source.module)?
        .get(source.symbol.as_ref())?
        .clone();
    Some((entry, source.module, source.symbol))
}

/// Look up a TypeDefInfo by chain-following `name` from `scope` (the access
/// root). Live-only free-fn variant of the relocated method 1
/// (`lookup_type_def_in_module` body). Returns `None` if absent or if the
/// chain terminates on a non-TypeDef entry.
pub fn lookup_type_def_chain<C, L>(
    modules: &dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>,
    scope: &ModuleFullPath,
    // FQTypeName exception 2 (context-supplied: scope IS the resolution context; returns FQ TypeDefInfo)
    name: &TypeName,
) -> Option<TypeDefInfo>
where
    C: CodeStore,
    L: LinkerStore,
{
    let (terminal, _home) = resolve_terminal_entry_and_home(modules, scope, name.as_ref())?;
    terminal.type_def_info().cloned()
}

/// Look up a `TraitDeclInfo` by chain-following `name` from `scope`. Live-only
/// free-fn variant of the relocated method 4's underlying primitive
/// (`lookup_trait_decl_in_module` body).
///
/// Returns the slimmed symbol-table payload `TraitDeclInfo` (S72 Phase B) —
/// the entry no longer embeds the full AST `TraitDecl`. Callers needing
/// `docstring`/`visibility` read them from the entry directly (e.g. via
/// `is_public()`); this primitive surfaces the structural trait metadata.
pub fn lookup_trait_decl_chain<C, L>(
    modules: &dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>,
    scope: &ModuleFullPath,
    // FQTypeName exception 2 (context-supplied: scope IS the resolution context; returns FQ TypeDefInfo)
    trait_name: &TraitName,
) -> Option<TraitDeclInfo>
where
    C: CodeStore,
    L: LinkerStore,
{
    let (terminal, _home) = resolve_terminal_entry_and_home(modules, scope, trait_name.as_ref())?;
    match terminal.declaration {
        Decl::Trait(record) => Some(record.info),
        _ => None,
    }
}

/// Return all trait names that have an impl registered for `type_name`,
/// reachable from `scope`. Sorted alphabetically. Live-only free-fn
/// variant of method 3 (`get_impls_for_type_in_module` body).
///
/// Per Decision 45 (Pattern B) — enumerate candidate traits in `scope`,
/// chain-follow each to its defining module, and probe each home for
/// impls of `type_name`. Each trait home is touched at most once.
pub fn get_impls_for_type_chain<C, L>(
    modules: &dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>,
    scope: &ModuleFullPath,
    type_name: &TypeName,
    // FQTypeName exception 1 (reverse-lookup-for-display: bare names projected off FQ entries for introspection enumeration within scope)
) -> Vec<TraitName>
where
    C: CodeStore,
    L: LinkerStore,
{
    let mut traits: Vec<TraitName> = Vec::new();
    let candidates: Vec<TraitName> = {
        let mut acc = Vec::new();
        if let Some(table) = modules.get(scope) {
            for name in table.symbols.keys() {
                acc.push(TraitName::from(name.as_ref()));
            }
        }
        acc
    };
    let mut visited_homes: std::collections::HashSet<ModuleFullPath> =
        std::collections::HashSet::new();
    for candidate in candidates {
        let trait_home = match resolve_terminal_entry_and_home(modules, scope, candidate.as_ref()) {
            Some((
                Binding {
                    declaration: Decl::Trait(_),
                    ..
                },
                home,
            )) => home,
            _ => continue,
        };
        if !visited_homes.insert(trait_home.clone()) {
            continue;
        }
        for_each_in_module(modules, &trait_home, |_key, entry| {
            if let Decl::ImplShell(shell) = &entry.declaration
                && &shell.impl_type.name == type_name
                && !traits.contains(&shell.trait_name.name)
            {
                traits.push(shell.trait_name.name.clone());
            }
        });
    }
    traits.sort();
    traits
}

/// Return all type names that implement `trait_name`, reachable from `scope`.
/// Sorted alphabetically. Live-only free-fn variant of method 5
/// (`get_implementing_types_in_module` body).
///
/// Per Decision 45 (Pattern B) — chain-follow the trait reference to its
/// defining module, then enumerate `Decl::ImplShell` entries in
/// that one module.
pub fn get_implementing_types_chain<C, L>(
    modules: &dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>,
    scope: &ModuleFullPath,
    trait_name: &TraitName,
    // FQTypeName exception 1 (reverse-lookup-for-display: bare names projected off FQ entries for introspection enumeration within scope)
) -> Vec<TypeName>
where
    C: CodeStore,
    L: LinkerStore,
{
    let mut types: Vec<TypeName> = Vec::new();
    let trait_home = match resolve_terminal_entry_and_home(modules, scope, trait_name.as_ref()) {
        Some((
            Binding {
                declaration: Decl::Trait(_),
                ..
            },
            home,
        )) => home,
        _ => return types,
    };
    for_each_in_module(modules, &trait_home, |_name, entry| {
        if let Decl::ImplShell(shell) = &entry.declaration
            && &shell.trait_name.name == trait_name
            && !types.contains(&shell.impl_type.name)
        {
            types.push(shell.impl_type.name.clone());
        }
    });
    types.sort();
    types
}

/// Resolve a module name to its `ModuleFullPath`, trying child-of-scope
/// first then root. Live-only free-fn variant of method 7
/// (`resolve_module_by_name` body).
pub fn resolve_module_by_name_chain<C, L>(
    modules: &dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>,
    scope: &ModuleFullPath,
    name: &str,
) -> Option<ModuleFullPath>
where
    C: CodeStore,
    L: LinkerStore,
{
    let child_path = ModuleFullPath::from(format!("{}.{}", scope, name));
    if modules.contains_key(&child_path) {
        return Some(child_path);
    }
    let root_path = ModuleFullPath::from(name);
    if modules.contains_key(&root_path) {
        return Some(root_path);
    }
    None
}

#[cfg(test)]
mod tests;
