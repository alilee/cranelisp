use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use crate::{
    DefnVariant, FQSymbol, FQTraitName, FQTypeName, GOT_TABLE_SIZE, GotTable, ModeSummary,
    ModuleFullPath, ModuleName, MonoDefnVariant, Scheme, SchedulingClass, Sexp, Span, Symbol,
    TraitDeclInfo, TraitName, Type, TypeDefInfo, TypeName, Visibility,
};

// --- CodeStore / LinkerStore marker traits (Sprint 58 Wave 3a; Decision 32) ---

/// Empty marker trait for the per-function compiled-code store carried on
/// `ModuleEntry::Def.code`.
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
/// The blanket `impl<T: Send + Sync + 'static> CodeStore for T` means any
/// `Send + Sync + 'static` type the integration layer wants to use as `C`
/// automatically satisfies the bound — no per-call-site `impl` line needed.
/// `()` trivially satisfies it (zero-sized, Send + Sync + 'static), which
/// is why it works as the default for crates that don't handle compiled
/// code (typecheck, frontend, the bulk of backend).
///
/// See `design/arch/CLAUDE.md` Decision 32 (canonical) and Decision 35
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
/// See `design/arch/CLAUDE.md` Decision 32 (canonical) and Decision 35
/// (`L = ()` rationale).
pub trait LinkerStore: Clone + Send + Sync + 'static {}
impl<T: Clone + Send + Sync + 'static> LinkerStore for T {}

// --- Symbol Table ---

/// Per-module symbol table.
///
/// Mostly pure data (types, schemes, docstrings) with a single runtime-only
/// field: `got` (the per-module Global Offset Table). The GOT holds code
/// pointers that codegen writes and JIT-emitted call sites read; it is
/// `#[serde(skip)]` so cache files stay pointer-free and re-initialise to a
/// fresh null table on deserialise.
///
/// Owned by `TypeChecker` (via `DashMap<ModuleFullPath, SymbolTable>`), read
/// by `Backend` for type information, and mutated atomically per-slot by
/// codegen workers through `got.store_slot`.
///
/// Structural declarations (`imports`, `exports`, `platforms`, `submodules`)
/// retain the *original specification* of the module's `(import …)` /
/// `(export …)` / `(platform …)` / `(mod …)` forms — the per-symbol
/// `ModuleEntry::Import` entries are the *resolved effects* of imports.
/// See Decision 33 in `design/arch/CLAUDE.md` (Sprint 58 Step 5a). The
/// `ModuleStructure` parallel store in `src/save.rs` (Sprint-57 transitional
/// shape) dissolves at Step 5a — its fields move 1:1 to these.
///
/// Generic over `C: CodeStore` (per-function compiled-code store carried on
/// `ModuleEntry::Def.code`) and `L: LinkerStore` (per-module linker store
/// carried on `linker`). Both default to `()` so crates that don't handle
/// compiled code (typecheck, frontend, the bulk of backend) work with
/// `SymbolTable` (i.e. `SymbolTable<(), ()>`) and never see the parameters
/// in their signatures. The integration layer instantiates
/// `SymbolTable<Code, ()>` (or similar) in `src/session_v4.rs` (per
/// Decision 35). See Decision 32 for the trait shape and the
/// `pipeline-v4.md` §9.1 normative shape.
///
/// **Serde discipline.** The `linker: Option<L>` field is `#[serde(skip)]`
/// (runtime state), and `code: Option<C>` on `ModuleEntry::Def` is also
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
    /// The module analogue of a per-definition docstring (the per-entry
    /// `ModuleEntry::Def.docstring`), but documenting the module **as a whole**
    /// rather than a named symbol — so it lives here on the per-module table,
    /// off the symbol axis entirely (a synthetic `ModuleEntry` was rejected:
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
    pub symbols: HashMap<Symbol, ModuleEntry<C>>,
    /// Next available GOT slot index for this module.
    /// Module-local: slot 0, 1, 2... independently per module.
    #[serde(default)]
    pub next_got_slot: usize,
    /// Monotonic per-entry sequence allocator. Every newly-inserted
    /// `ModuleEntry::Def` receives `seq = next_seq` and the field is bumped.
    /// Used by `regenerate_backing_file` to emit defns in authorship order
    /// per `repl/spec.md` §15.4(2). Redefinition does NOT reorder:
    /// `insert_or_update` (consumer-side, in `int`) preserves the existing
    /// entry's `seq` value alongside Decision 31's `code` carry-forward.
    /// Replaces the prior `defn_order: Vec<Symbol>` side-table (Decision 39
    /// design upgrade — eliminates side-table drift, matches the
    /// `next_got_slot` allocation pattern).
    ///
    /// Source-side this is plain `u64` mutated under the existing
    /// `&mut SymbolTable` discipline (mirrors `next_got_slot: usize`). The
    /// facade target is `AtomicU64` (peer of facade's `next_got_slot:
    /// AtomicUsize`); the conversion lands as part of the broader
    /// SymbolTable concurrency cascade (S-DRIFT-19/20/21), not in this
    /// change-set.
    ///
    /// `#[serde(default)]` so pre-existing caches deserialise as `0` and the
    /// loader re-derives the high-water mark from the maximum `seq` across
    /// loaded entries (consumer-side reconstruction).
    #[serde(default)]
    pub next_seq: u64,
    /// Per-module Global Offset Table. Created when the `SymbolTable` is
    /// constructed (at module registration). Base address is stable for
    /// the module's lifetime. Slot indices are assigned by
    /// `allocate_got_slot`; code pointers are written atomically by
    /// codegen workers and read by JIT-emitted call sites.
    ///
    /// Wrapped in `Arc` so codegen workers can hold a cheap handle to the
    /// GOT while the `DashMap` read guard is released. Cloning a
    /// `SymbolTable` shares the same underlying GOT via refcount bump — the
    /// GOT is runtime state, not copied data. Phase 2 bridge: `/int`'s
    /// Wave 2 may swap the `Arc` for a bare field once
    /// `compile_and_register_defn_shared` and its helpers are deleted.
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
    /// on per-symbol `ModuleEntry::Import` entries (`visibility` discriminates
    /// private `(import …)`-edge from public `(export [foreign-sym])`-edge
    /// — see `Import` variant in this enum
    /// variant docstring).
    /// Consumers that need the effective set (transitive impl-resolution;
    /// module-locality short-name lookups) walk both stores — see
    /// `transitive_import_closure` in `crates/cranelisp-typecheck/src/checker.rs`.
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
    /// enum + `L = ()` rationale), `interfaces.md` §"Symbol Table" for
    /// the field-shape contract.
    #[serde(skip)]
    pub linker: Option<L>,
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
/// - `cranelisp` (the `int` integration layer) — `SharedState.symbol_tables: SymbolTables<Code, ()>` (see `design/arch/facades/int.md` + Decision 0035); int's Pass-1 macro recognition also reads it via `cranelisp_types::resolve_macro_head`
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
/// **Drift note — no `Arc<…>` wrapper.** Earlier facade text declared
/// `pub type SymbolTables<C, L> = DashMap<ModuleFullPath, Arc<SymbolTable<C, L>>>;`
/// (with `Arc<…>`). The canonical form is **without** `Arc` — the
/// integration layer's `SharedState.symbol_tables: SymbolTables<Code, ()>`
/// holds the per-module `SymbolTable` values directly inside the DashMap
/// shards. The `Arc` was an editorial drift on the frontend facade
/// (self-classified in the S70 Phase B frontend audit memo at
/// `design/arch/facades/frontend-audit-s70.md`; the frontend facade
/// itself was retired in S70 Phase B group B3-C — its narrative folded
/// into the lib.rs //! preamble + BC §1); the sibling
/// `int::SharedState.symbol_tables` is the workspace-stable shape.
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
///   convention — the same shape as `ModuleEntry::*.visibility`.
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
        ModuleAliasEntry { target, visibility, span }
    }
}

/// Session-level map of `ModuleFullPath → ModuleAliasEntry` — the
/// workspace's shared module-path-namespace alias table.
///
/// Lives in **parallel** to [`SymbolTables`]; keyed by the alias's
/// **full path** (e.g., key `m.n.str` for `(import [(core.string str)
/// …])` declared in `m.n`). This keying lets §8.6.6 qualified-name
/// resolution do a single-table longest-prefix-match against the queried
/// `module_path` rather than segmenting and walking per-module alias
/// sub-tables.
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
            next_got_slot: 0,
            next_seq: 0,
            got: std::sync::Arc::new(GotTable::new()),
            imports: Vec::new(),
            exports: Vec::new(),
            platforms: Vec::new(),
            submodules: Vec::new(),
            schema_version: 0,
            linker: None,
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
        let mut symbols: HashMap<Symbol, ModuleEntry<C>> = HashMap::with_capacity(self.symbols.len());
        for (name, entry) in self.symbols {
            symbols.insert(name, entry.into_concrete::<C>());
        }
        SymbolTable {
            path: self.path,
            module_preamble: self.module_preamble,
            symbols,
            next_got_slot: self.next_got_slot,
            next_seq: self.next_seq,
            got: self.got,
            imports: self.imports,
            exports: self.exports,
            platforms: self.platforms,
            submodules: self.submodules,
            schema_version: self.schema_version,
            linker: None,
        }
    }
}

impl ModuleEntry<()> {
    /// Convert a `()`-flavoured `ModuleEntry` to any other `<C>`
    /// instantiation by setting `code` to `None::<C>` (the only field
    /// that depends on `C`). All other fields are parameter-independent.
    /// Sprint 58 Wave 3b (Decision 35).
    pub fn into_concrete<C: CodeStore>(self) -> ModuleEntry<C> {
        match self {
            ModuleEntry::Def {
                scheme, visibility, docstring, param_names, kind, callees, value_use,
                trait_origin, seq, ast, codegen_view, code: _,
            } => ModuleEntry::Def {
                scheme, visibility, docstring, param_names, kind, callees, value_use,
                trait_origin, seq, ast, codegen_view, code: None,
            },
            ModuleEntry::SpecialForm { scheme, param_names, docstring, description, visibility } => {
                ModuleEntry::SpecialForm { scheme, param_names, docstring, description, visibility }
            }
            ModuleEntry::Import { source, visibility } => ModuleEntry::Import { source, visibility },
            ModuleEntry::TypeDef { info, visibility, docstring } => {
                ModuleEntry::TypeDef { info, visibility, docstring }
            }
            ModuleEntry::IntrinsicType { ty, visibility, docstring } => {
                ModuleEntry::IntrinsicType { ty, visibility, docstring }
            }
            ModuleEntry::TraitDecl { info, visibility, docstring } => {
                ModuleEntry::TraitDecl { info, visibility, docstring }
            }
            // ModuleEntry::Constructor variant retired — constructors are now
            // ModuleEntry::Def entries with kind: DefKind::Constructor { .. }
            // and synthesised DefnVariant bodies whose body expression is
            // Expr::ConstrADT (S69 Submission 35 narrowed ast from Option<Defn>
            // to Option<DefnVariant>; see `DefKind::Constructor` rustdoc
            // and `design/arch/bounded-contexts.md` §7).
            // ModuleEntry::Macro variant retired (Submission 22) — macros are
            // now ModuleEntry::Def entries with kind: DefKind::Macro
            // { clauses_meta } (see `DefKind::Macro` rustdoc). Per-symbol
            // source / sexp / clif_ir / disasm / code_size live on the
            // integration-layer Introspection record (Decision 41), not on
            // the Def variant — symmetric across all DefKinds.
            // ModuleEntry::PlatformDecl variant retired (Submission 22) —
            // platforms register as synthetic modules at
            // symbol_tables["platform.<name>"] per spec §8.9.3; the DLL handle
            // lives on the platform module's own SymbolTable.dll
            // (see `design/arch/bounded-contexts.md` §7).
            ModuleEntry::TraitImpl { trait_name, impl_type, impl_module, methods, visibility } => {
                ModuleEntry::TraitImpl { trait_name, impl_type, impl_module, methods, visibility }
            }
            ModuleEntry::Ambiguous { visibility } => ModuleEntry::Ambiguous { visibility },
        }
    }
}

/// Module-local GOT exhaustion: [`SymbolTable::allocate_got_slot`] was called
/// when `next_got_slot` had already reached [`GOT_TABLE_SIZE`], so no free slot
/// remains in the module's fixed 1024-slot GOT slab.
///
/// Constructed ONLY by [`SymbolTable::allocate_got_slot`]. It is never
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
            next_got_slot: 0,
            next_seq: 0,
            got: std::sync::Arc::new(GotTable::new()),
            imports: Vec::new(),
            exports: Vec::new(),
            platforms: Vec::new(),
            submodules: Vec::new(),
            schema_version: 0,
            linker: None,
        }
    }

    /// Allocate the next available module-local GOT slot.
    ///
    /// The GOT is a fixed [`GOT_TABLE_SIZE`]-slot slab; once `next_got_slot`
    /// reaches that bound there is no free slot and allocation fails with
    /// [`GotExhausted`]. `next_got_slot` is **not** advanced on failure, so
    /// exhaustion is stable and repeatable (a second call fails identically).
    /// This makes exhaustion a diagnosed compile error at the seam rather than
    /// release-mode UB at the eventual `store_slot`/`load_slot` (Phase H).
    pub fn allocate_got_slot(&mut self) -> Result<usize, GotExhausted> {
        if self.next_got_slot >= GOT_TABLE_SIZE {
            return Err(GotExhausted {
                module: self.path.clone(),
            });
        }
        let slot = self.next_got_slot;
        self.next_got_slot += 1;
        Ok(slot)
    }

    /// REPL append path — extends the appropriate structural Vec with one new
    /// entry. Used for `(import …)` / `(export …)` / `(declare-platform …)` /
    /// `(mod …)` forms entered interactively at the REPL prompt. File-loaded
    /// modules use a bulk-load shape (`write_structural_decls`, facade-target —
    /// not present source-side yet) instead. Brief per-eval `&mut`
    /// window — one enum-carrier method, no parallel per-section append
    /// methods. Per `repl/spec.md` §15.4 and Decision 39 (S69 Phase 3 upgrade).
    pub fn append_structural_decl(&mut self, entry: StructuralDeclEntry) {
        match entry {
            StructuralDeclEntry::Import(spec) => self.imports.push(spec),
            StructuralDeclEntry::Export(spec) => self.exports.push(spec),
            StructuralDeclEntry::Platform(spec) => self.platforms.push(spec),
            StructuralDeclEntry::Mod(decl) => self.submodules.push(decl),
        }
    }

    pub fn get(&self, name: &str) -> Option<&ModuleEntry<C>> {
        self.symbols.get(name)
    }

    pub fn insert(&mut self, name: Symbol, entry: ModuleEntry<C>) {
        self.symbols.insert(name, entry);
    }

    pub fn public_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry<C>)> {
        self.symbols.iter().filter(|(_, e)| e.is_public())
    }

    /// Iterate over all symbols (public and private).
    pub fn all_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry<C>)> {
        self.symbols.iter()
    }

    /// Iterator over entries that codegen should compile.
    ///
    /// Filter: `ast.is_some() AND kind != Overloaded AND kind != UserFn { fn_state: Constrained(_) }`.
    ///
    /// Shared codegen-compilable predicate — see Decision 22 in
    /// `design/arch/CLAUDE.md` and §9.5 of `design/typecheck/ast-annotation.md`.
    /// Both the backend's `compile_to_module` and the integration layer's
    /// priority worker enumerate codegen targets via this iterator so the
    /// filter lives in exactly one place.
    ///
    /// Entries that carry `ast: None` are never compilable (pre-body-check,
    /// primitives, special forms, `Overloaded` base entries whose mangled
    /// variants carry the bodies, and constrained-fn templates whose mono
    /// specialisations carry the bodies).
    ///
    /// **`Polymorphic` is a mono SOURCE, NOT a codegen target — EXCLUDED like
    /// `Constrained` (S84 Phase 4B, FIXME 0381).** A generic-unconstrained def
    /// ([`UserFnState::Polymorphic`]) is a slot-less template body that must
    /// NEVER be a `compile_to_module` codegen target: the monomorphisation pass
    /// specialises it at every reachable concrete use, and those concrete
    /// instances (mangled `name$Args` entries) carry the bodies that codegen.
    /// Emitting the template body itself reached `HeapCategory::classify` at RC
    /// sites with scheme-quantified free vars (the 317× backstop fire,
    /// FIXME 0381). So — symmetric with `Constrained`, whose mono instances carry
    /// the bodies and whose template is excluded here — a `Polymorphic` entry is
    /// EXCLUDED (the filter excludes `Overloaded`, `Constrained`, and
    /// `Polymorphic`). Concrete (`is_concrete()`) generic instances retain their
    /// slot and codegen normally.
    pub fn defined_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry<C>)> {
        self.symbols.iter().filter(|(_, entry)| match entry {
            ModuleEntry::Def { ast: Some(_), kind, .. } => !matches!(
                kind.as_ref(),
                DefKind::Overloaded { .. }
                    | DefKind::UserFn { fn_state: UserFnState::Constrained(_) }
                    | DefKind::UserFn { fn_state: UserFnState::Polymorphic(_) }
            ),
            _ => false,
        })
    }
}

// --- Module Entries ---

/// An entry in a module's symbol table.
///
/// Generic over `C: CodeStore` per the parameterised `SymbolTable<C, L>`
/// shape (Decision 32). `C` defaults to `()` so crates that don't handle
/// compiled code work with `ModuleEntry` (i.e. `ModuleEntry<()>`). The
/// `code: Option<C>` field on the `Def` variant is the only place `C`
/// appears; every other variant is independent of the parameter (the
/// `PhantomData` slot is implicit via the `code: Option<C>` field).
///
/// **Serde discipline.** The `code: Option<C>` field is `#[serde(skip)]` —
/// it never round-trips through serde. The explicit `#[serde(bound = "")]`
/// on the derive suppresses the auto-generated `C: Serialize +
/// Deserialize` bounds that the derive would otherwise emit; without
/// `bound = ""`, the derive proactively requires bounds on `C` even for
/// skipped fields. The `Option<C>` field's `default` (i.e., `None`) does
/// not require `C: Default` because `Option::default()` returns `None`
/// for any `T`.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub enum ModuleEntry<C: CodeStore = ()> {
    /// A definition: function, primitive, or constructor.
    ///
    /// Special forms are NOT `Def` entries — they live in their own
    /// `ModuleEntry::SpecialForm` variant per S69 Submission 36 (a Def
    /// reads at most 4 of the ~11 fields below, so a dedicated variant
    /// fits the introspection use case cleanly — parallels Submission 30's
    /// `IntrinsicType` shape). See `ModuleEntry::SpecialForm` variant below
    /// for the manifestation.
    Def {
        scheme: Scheme,
        visibility: Visibility,
        docstring: Option<String>,
        param_names: Vec<Symbol>,
        kind: Box<DefKind>,
        /// Fully-qualified callees discovered during typechecking (Decision 21).
        /// Populated by `finalize_check_result()` for user-defined functions.
        /// Empty for primitives, special forms, and entries not yet body-checked.
        #[serde(default)]
        callees: Vec<FQSymbol>,
        /// **Value-use mark** (S102 CS-A;
        /// `design/typecheck/ownership-inference.md` §8.3): `true` iff this
        /// callable is referenced in non-callee position somewhere in the
        /// program (`(map f xs)`, stored, returned). Written by typecheck's
        /// ownership pass alongside the summary; read by backend wrapper
        /// emission — a value-used callable with a non-Decision-24 summary
        /// needs its synthesized Decision-24 adapter wrapper (spine §8.2),
        /// and this mark says so without the backend re-deriving it.
        /// `#[serde(default)]` = `false` = the pre-analysis point (wrapper
        /// decisions fall back to as-built behaviour). Like `callees`, a
        /// pass-written runtime fact — no builder setter.
        #[serde(default)]
        value_use: bool,
        // **No flat `got_slot` field (S83, FIXME 0356/0357, Principle 20;
        // amends Decision 0035).** The module-local GOT slot through which an
        // entry is invoked now lives on the callable `DefKind` variants
        // (`UserFn`'s `Concrete` `fn_state`, `Primitive`, `Constructor`) — not
        // as a flat `Def` field. This makes the once-illegal pairing (a
        // constrained-fn template holding a callable slot) structurally
        // unconstructable: a constrained template is
        // `kind: DefKind::UserFn { fn_state: UserFnState::Constrained(_) }`,
        // which carries no slot. Non-callable kinds (`Macro` parent,
        // `PlatformEffect`, `PrimitiveExtern`, `Overloaded` base) carry no slot
        // field at all; special forms / type defs / trait decls are separate
        // `ModuleEntry` variants with no `kind`. Read the callable address via
        // [`ModuleEntry::callable_got_slot`] (the single read-through point);
        // the GOT remains the single source of truth for the runtime *address*
        // (`SymbolTable.got.store_slot`/`.load_slot`), indexed by the slot the
        // kind variant carries. See BC §7 "Callability is structural" +
        // `design/arch/principles/20-model-invariants-by-representation.md`.
        /// If this Def is a trait method, which trait it belongs to.
        /// Replaces the `method_to_trait` reverse index on `TraitRegistry`.
        /// `None` for non-trait-method definitions.
        #[serde(default)]
        trait_origin: Option<FQTraitName>,
        /// Per-entry monotonic ordering token, allocated via
        /// `SymbolTable.next_seq` fetch-and-bump at first registration.
        /// Used by `regenerate_backing_file` to emit defns in authorship order
        /// per `repl/spec.md` §15.4(2). On redefinition, `insert_or_update`
        /// (consumer-side, in `int`) preserves the existing `seq` value
        /// alongside the `code` carry-forward per Decision 31 — a redefined
        /// defn keeps its original authorship position across REPL redef
        /// (principle of least surprise).
        ///
        /// Per Decision 39 design upgrade (S69 Phase 3): replaces the prior
        /// `SymbolTable.defn_order: Vec<Symbol>` side-table — eliminates
        /// side-table drift, matches the `got_slot` allocation pattern.
        #[serde(default)]
        seq: u64,
        /// Typechecked function body — the single meaningful payload `DefnVariant`
        /// (params + body + span). Written by typecheck after `check_form(CheckBody)`;
        /// read by codegen. `None` for primitives, special forms, and pre-body-check
        /// entries (the codegen-compilable predicate per Decision 22 reads
        /// `ast.is_some()` alongside the `kind` discriminant — see
        /// `defined_symbols()` above).
        ///
        /// **Narrowed from `Defn` to `DefnVariant` (S69 Submission 35).** Each
        /// `ModuleEntry::Def` represents one callable entry — by the time a Def
        /// reaches backend, multi-sig has already been **decomposed into per-
        /// mangled-name Defs** (`add$Int+Int`, `add$Float+Float`), each carrying a
        /// synthesised single-variant payload. The outer `Defn` wrapper carries
        /// only duplicate metadata at this layer:
        /// - `Defn.name` duplicated the symbol-table key,
        /// - `Defn.docstring` duplicated this entry's own `docstring` field,
        /// - `Defn.variants` was always `.len() == 1` post-decomposition (single-
        ///   element `Vec` wrapping the meaningful payload),
        /// - `Defn.visibility` duplicated this entry's own `visibility` field,
        /// - `Defn.span` was redundant with the variant's own `span`.
        ///
        /// The meaningful payload IS the single `DefnVariant`. Narrowing here
        /// honours **minimum mechanism** (carry only what consumers read) and
        /// **single source of truth (Principle 7)** — the entry's own
        /// `name` / `visibility` / `docstring` / `seq` fields are canonical for
        /// that metadata; the outer `Defn` wrapper retires from the runtime model.
        ///
        /// `Defn` continues to exist as the **frontend AST node** (parser output,
        /// pre-decomposition). Typecheck's multi-sig decomposition splits the
        /// frontend `Defn` into per-variant `DefnVariant`s, each landing in its
        /// own `ModuleEntry::Def`'s `ast` field; the outer `Defn` wrapper does
        /// not propagate past that decomposition boundary.
        ///
        /// **Decision 22's codegen-compilable predicate is preserved** —
        /// `ast.is_some()` discriminates "body available" from "body not yet
        /// available / never available"; the predicate is indifferent to the
        /// payload type. See `defined_symbols()` above for the call-site.
        #[serde(default)]
        ast: Option<DefnVariant>,
        /// The **concrete-boundary codegen view** of this entry's body — a
        /// [`MonoDefnVariant`] whose [`MonoExpr`](crate::MonoExpr) nodes carry
        /// [`ConcreteType`](crate::ConcreteType) **non-optionally**. This is the
        /// view the backend consumes for codegen (Phase 3 of the
        /// `design/arch/concrete-boundary-type.md` arc): it has **no `Type` on
        /// its read path and therefore no `Var`** — a representation-undetermined
        /// type is structurally unrepresentable here (Principle 18 / Principle 20).
        ///
        /// Populated alongside `ast` for every **codegen-bound** entry:
        /// - **Monomorphised instances** (the `name$Args` mangled concrete
        ///   instances) — built by the mono pass at the mono-population seam via
        ///   [`MonoExpr::from_expr`](crate::MonoExpr::from_expr) over the
        ///   fully-annotated, subst-resolved instance body (moving off the
        ///   transitional `CheckState.mono_variants` parallel `Vec`).
        /// - **Ordinary concrete (`is_concrete()`) defns** — every
        ///   `UserFnState::Concrete { got_slot }` entry — built by the same
        ///   `from_expr` over its annotated `Defn` body at body-check.
        ///
        /// `None` for entries that are NOT codegen targets: `ast: None` entries
        /// (primitives, special forms, pre-body-check), and the slot-less
        /// **template** kinds (`Constrained`/`Polymorphic` `UserFn`, `Overloaded`
        /// base) which are mono *sources*, never `compile_to_module` targets (see
        /// `defined_symbols()`). A codegen-bound entry whose `codegen_view` is
        /// `None` at the moment the backend reaches it is the single relocated
        /// backstop (a located `expect`) — the only guard replacing the four
        /// behavioural `Var`-guards the arc retires.
        ///
        /// **Transitional (Phase 2→3).** Carried ALONGSIDE `ast` rather than
        /// replacing it: the backend reads `ast` (the `inferred_type`-annotated
        /// `DefnVariant`) until /dev(backend) flips `compile_to_module` to consume
        /// `codegen_view`. Once the flip lands and the suite is green, `ast`'s
        /// codegen role retires (it may stay as the introspection/regen body
        /// source — that disposition is a follow-up, not part of this field's
        /// landing). Both fields are subst-resolved views of the same body;
        /// `from_expr` is non-destructive over `ast`.
        ///
        /// Serde: a plain `#[serde(default)]` participant in the cached
        /// `.meta.json` shape (it carries no `C`/pointer state) — its addition is
        /// the `CACHE_SCHEMA_VERSION` 7 → 8 bump.
        #[serde(default)]
        codegen_view: Option<MonoDefnVariant>,
        /// Compiled-code handle written by the backend after `compile_to_module`
        /// returns. Runtime-only state (Decision 25 in `design/arch/CLAUDE.md`):
        /// `#[serde(skip)]` so cache manifests stay pointer-free, and the field
        /// re-initialises to `None` on cache-hit load. Codegen repopulates it
        /// on demand.
        ///
        /// Generic over `C: CodeStore` (Wave 3a; Decision 32 + Decision 35).
        /// The integration layer instantiates `C = Code` (an enum unifying
        /// `Code::Jit { Arc<Jit>, ptr }` and `Code::Linker { Arc<Linker>,
        /// ptr }` per Decision 35); other crates default `C = ()` and read
        /// this as `Option<()>` (a structurally meaningless tag). Per
        /// Decision 31 Scenario 2, after Wave 3b lands the integration
        /// layer's concrete `Code::Jit` here, dropping the last
        /// `ModuleEntry::Def.code` referencing a given `Arc<Jit>` reaches
        /// refcount 0 and the custom `Drop` on the `Jit` wrapper calls
        /// `unsafe JITModule::free_memory()` — the per-redefinition reclaim
        /// primitive.
        #[serde(skip)]
        code: Option<C>,
    },
    /// A compiler-provided special form (`if`, `let`, `defn`, `match`, etc.).
    ///
    /// Per S69 Submission 36 — promoted from `DefKind::SpecialForm` to its
    /// own `ModuleEntry` variant. A special form reads at most 4 of `Def`'s
    /// ~11 fields (`scheme`, `param_names`, `docstring`, `description`);
    /// a dedicated variant fits the introspection use case cleanly and
    /// parallels Submission 30's `IntrinsicType` shape (compiler-provided
    /// construct that has no user-level definition).
    ///
    /// Introspection-only. NOT JIT-registered (special forms are pure
    /// syntax; no runtime address). NO `got_slot` field (never callable
    /// as a value). NO `code` field (no body to compile). NO `ast` field
    /// (no AST to codegen).
    ///
    /// Lives in the root module `""` per FIXME 0193 (special-form
    /// metadata lives at root and is never replicated). Resolved by
    /// chain-follow from the user module through the prelude's
    /// `(import [<root> [*]])` (or directly from root for unqualified
    /// resolution).
    ///
    /// See `design/arch/bounded-contexts.md` §7
    /// `ModuleEntry::SpecialForm`.
    SpecialForm {
        scheme: Scheme,
        param_names: Vec<Symbol>,
        docstring: Option<String>,
        description: String,
        visibility: Visibility,
    },
    /// An imported name from another module (Ring 2).
    ///
    /// **Covers both edge kinds.** `visibility` discriminates provenance (see
    /// `design/arch/bounded-contexts.md` §7 "Visibility is per-entry"):
    /// - `Visibility::Private` — the `(import …)`-form effect. The local
    ///   binding is reachable from this module's scope but does not escape via
    ///   the public surface. Spec §8.3.
    /// - `Visibility::Public` — the `(export [foreign-sym])`-form effect (the
    ///   prior `ModuleEntry::Reexport` variant, retired in the per-entry
    ///   visibility collapse). The local binding is reachable from this
    ///   module AND from downstream importers (re-export edge). Spec §8.4.
    ///
    /// Chain-follow per Decision 45 walks `Import` edges regardless of
    /// visibility — the variant collapse simplifies the pattern-match
    /// (`ModuleEntry::Import { source, .. }` covers both edges that were
    /// previously a two-arm match).
    Import {
        source: FQSymbol,
        visibility: Visibility,
    },
    /// A type definition (deftype).
    ///
    /// **Introspection lives elsewhere — symmetric across all
    /// introspection-bearing variants (Decision 41 operative).** The prior
    /// `sexp: Option<Sexp>` field was retired in S70 Phase 3 — every
    /// construction site wrote `None` (7 sites across
    /// `cranelisp-typecheck::builtins` + `cranelisp-typecheck::adt`); the
    /// only reader was a dead-arm pattern-match in `src/save.rs`'s
    /// `generate_types`. Per-symbol source / sexp / expanded / clif_ir /
    /// disasm / code_size for type definitions live on the per-`FQSymbol`
    /// `Introspection` record in the integration layer's
    /// `SharedState.introspection: Option<DashMap<FQSymbol, Introspection>>`
    /// (defined at `src/session_v4.rs:566`), written directly by frontend
    /// during expand and by backend during `compile_to_module` (gated by
    /// `Option<&DashMap<FQSymbol, Introspection>>` parameter — the
    /// `Option`'s `is_some()` IS the mode discriminator, Decision 38).
    /// Symmetric with `DefKind::Macro` (which shed the same shadow fields
    /// pre-S70) and with `DefKind::UserFn` / `DefKind::Constructor` (which
    /// never carried them). See the `DefKind::Macro` rustdoc below for the
    /// full Decision-41 settlement including the cache-hit residual gap.
    ///
    /// **`docstring` is a direct entry field (S72 Phase B).** The docstring
    /// previously lived nested inside `info.docstring` (`TypeDefInfo`); it is
    /// now a direct top-level field on the entry, matching `Def` /
    /// `SpecialForm`. `TypeDefInfo` no longer carries a docstring — single
    /// source of truth (Principle 7). The entry owns the docstring; the
    /// `info` payload carries only the type's structural metadata (name,
    /// type-parameter binders, constructor names).
    /// **`constructor_scheme` retired (S79 Option 3a).** A single-ctor
    /// **product** type no longer survives as a `TypeDef` entry that smuggled
    /// the ctor's function-type `Scheme` in a `constructor_scheme:
    /// Option<Scheme>` field. The product case now survives as a got-slotted
    /// ctor `Def` carrying a type facet (`DefKind::Constructor { type_def:
    /// Some(..) }`); the ctor's scheme lives canonically on that `Def`'s own
    /// `scheme`. `ModuleEntry::TypeDef` entries are therefore only ever the
    /// **sum/enum** case (type name distinct from every ctor name), and carry
    /// no constructor scheme — consumers read each ctor's scheme from its own
    /// `Def`. See `DefKind::Constructor.type_def` rustdoc + `bounded-contexts.md` §7.
    TypeDef {
        info: TypeDefInfo,
        visibility: Visibility,
        docstring: Option<String>,
    },
    /// Compiler-intrinsic scalar type (Int, Bool, Float, String).
    ///
    /// "Intrinsic" — the compiler provides this type directly; it has no
    /// user-level definition (no constructors, no fields, no type parameters).
    /// Spec §3.1 calls these "primitive types"; this variant uses the name
    /// "intrinsic" to distinguish from the broader `primitives` module that
    /// holds intrinsic types alongside primitive functions and builtin ADTs
    /// (Vec, IO, Option). Naming reflects the structural property (compiler-
    /// provided, no user-level definition) rather than the housing module.
    ///
    /// `ty` is the bare `Type` variant (`Type::Int`, etc.) for backend
    /// codegen efficiency; the fully-qualified form (`primitives/Int`)
    /// lives in the SymbolTable key. Resolution returns `ty.clone()`
    /// directly — no FQTypeName special-casing.
    ///
    /// Per spec §3.1 / §8.9.1 (S69 /spec fire sharpening) — bare-name
    /// access (`:Int`) requires prelude re-export or explicit `(import
    /// [primitives [Int]])`. Fully-qualified `:primitives/Int` always
    /// works. Without prelude / explicit import, bare `:Int` is a
    /// compile-time "unknown type" error.
    ///
    /// Registered by `cranelisp-typecheck::register_builtin_type_names`
    /// (in `builtins.rs`); resolved by `resolve_named` via uniform entry
    /// lookup. Supersedes the retired `Type::from_name` / `Type::type_name`
    /// reverse-lookup bridge (S69 Submission 30 — they made bare `:Int`
    /// always available regardless of imports, contradicting spec §3.1 /
    /// §8.9.1 / §8.11.4). The prior `register_primitives` registration flow
    /// was deleted in S72 (T1).
    ///
    /// **`docstring` is a direct entry field (S72 Phase B).** Intrinsic types
    /// (`Int`, `Bool`, `Float`, `String`) are introspectable like any other
    /// symbol; the field carries the compiler-provided documentation surfaced
    /// by `/doc` / `/info`. Direct top-level field, matching `Def` /
    /// `SpecialForm` / `TypeDef` — populated at registration (`None` when no
    /// documentation is provided).
    IntrinsicType {
        ty: Type,
        visibility: Visibility,
        docstring: Option<String>,
    },
    /// A trait declaration (deftrait, Ring 2).
    ///
    /// **Introspection lives elsewhere — symmetric across all
    /// introspection-bearing variants (Decision 41 operative).** The prior
    /// `sexp: Option<Sexp>` field was retired in S70 Phase 3 — both
    /// construction sites in `cranelisp-typecheck::traits` wrote `None`; the
    /// only reader was a dead-arm pattern-match in `src/save.rs`'s
    /// `generate_traits`. Per-symbol source / sexp / expanded / clif_ir /
    /// disasm / code_size for trait declarations live on the per-`FQSymbol`
    /// `Introspection` record in the integration layer's
    /// `SharedState.introspection: Option<DashMap<FQSymbol, Introspection>>`
    /// (defined at `src/session_v4.rs:566`), written directly by frontend
    /// during expand and by backend during `compile_to_module` (gated by
    /// `Option<&DashMap<FQSymbol, Introspection>>` parameter — the
    /// `Option`'s `is_some()` IS the mode discriminator, Decision 38).
    /// Symmetric with `ModuleEntry::TypeDef` and `DefKind::Macro` (which all
    /// shed the same shadow fields pre/at S70). See the `DefKind::Macro`
    /// rustdoc below for the full Decision-41 settlement including the
    /// cache-hit residual gap.
    ///
    /// **Slimmed payload + direct `docstring`/`visibility` (S72 Phase B).**
    /// The entry previously embedded the full frontend AST node
    /// `crate::ast::TraitDecl`, which duplicated `visibility` (the AST node
    /// carries its own `visibility`) and `docstring` (nested in `decl.docstring`),
    /// and dragged the parser `span` into the runtime symbol-table model.
    /// Following the `ModuleEntry::Def` precedent — `Def` does NOT embed the
    /// `Defn` AST node; it carries direct `scheme`/`visibility`/`docstring`/`seq`
    /// fields plus a slimmed `ast: Option<DefnVariant>`, with the outer `Defn`
    /// wrapper retiring from the runtime model — `TraitDecl` now carries direct
    /// `docstring` + `visibility` and a slimmed `info: TraitDeclInfo`
    /// (`name`, `type_params`, `methods`).
    ///
    /// Single source of truth (Principle 7): `docstring`/`visibility` live on
    /// the entry, NOT duplicated in the payload. The frontend AST `TraitDecl`
    /// (in `crate::ast`) keeps its own `visibility`/`docstring`/`span` — those
    /// record what the user wrote at the source layer and remain legitimate
    /// parser output; the symbol-table entry stops embedding/duplicating them.
    /// The `is_public()` uniform match (below) reads the entry's direct
    /// `visibility` exactly as for every other variant.
    TraitDecl {
        info: TraitDeclInfo,
        visibility: Visibility,
        docstring: Option<String>,
    },
    // ModuleEntry::Constructor variant retired. Constructors are now
    // ModuleEntry::Def entries with kind: DefKind::Constructor { type_name,
    // tag, field_count, internal } and synthesised DefnVariant bodies whose
    // body expression is Expr::ConstrADT (S69 Submission 35 narrowed ast from
    // Option<Defn> to Option<DefnVariant>; see `design/arch/bounded-contexts.md` §7
    // — the single store" §"DefKind" for the ctor-as-Def shape and rejected
    // alternatives). See crates/cranelisp-types/src/check.rs for the
    // retirement of ConstructorInfo struct and TypeDefInfo.constructors:
    // Vec<Symbol> shape.
    // ModuleEntry::Macro variant retired (Submission 22 — 2026-05-21).
    // Macros are now ModuleEntry::Def entries with
    // kind: DefKind::Macro { clauses_meta } (see `DefKind::Macro` rustdoc
    // in this file). Per-clause bodies are ordinary Def entries with mangled
    // names `{macro-name}$clause-{N}` parallel to multi-sig fn variants like
    // `add$Int+Int`. The session-level `MacroEnv` sidecar retires alongside
    // this variant (consumer cascade in /dev wave-3). The `MacroClauseInfo`
    // / `MacroParam` support types below continue to exist because
    // `DefKind::Macro` still references them; their own retirement (if any)
    // is a separate cascade item. Per-symbol source / sexp / clif_ir /
    // disasm / code_size live on the integration-layer Introspection record
    // (Decision 41), NOT on `DefKind::Macro` — symmetric with all other Def
    // variants.
    //
    // ModuleEntry::PlatformDecl variant retired (Submission 22 — 2026-05-21).
    // Per spec §8.9.3, `(platform <name>)` registers a synthetic module at
    // `symbol_tables["platform.<name>"]` — a normal module per the existing
    // module map. The DLL handle is retained on that platform module's own
    // `SymbolTable.dll: Option<D>` field (via the `D: DllStore` generic; see
    // `design/arch/bounded-contexts.md` §7).
    // The variant previously stored a per-platform DLL record AS AN ENTRY
    // WITHIN the declaring module, which contradicted spec §8.9.3 — platforms
    // are modules of their own, not entries within other modules. The
    // form-record `PlatformSpec` on the entry module's `SymbolTable.platforms`
    // continues to record what the user wrote (for `.cl` regeneration per
    // `repl/spec.md` §15.4).
    /// A trait implementation for a specific type (Ring 2).
    /// Keyed by synthetic name `impl$FQTypeName$FQTraitName` on the SymbolTable.
    /// Always public (spec §5.11: impls are visible wherever both trait and type are in scope).
    ///
    /// **Storage placement (Decision 0045 pattern (b), as amended S110 W0.1 —
    /// `design/arch/backend-keyed-consumer.md` §1.1.1).** An `(impl Trait Type
    /// method-defns…)` form written in module M splits across two placements:
    ///
    /// - **This shell entry — the DISCOVERY record — lands in the TRAIT's
    ///   defining module** (resolved by chain-following the trait reference
    ///   from M at write time; `impl_check.rs` `check_trait_impl`). Importers
    ///   discover the impl by the same per-symbol chain-follow (Principle 17
    ///   shape 1) back to the trait's home and an `O(1)` probe for the
    ///   synthetic key — no closure walk, no cycle detection.
    /// - **The method bodies — the COMPILATION record — land in M** (the
    ///   writer's module) as ordinary `ModuleEntry::Def` entries with mangled
    ///   names (`Trait.method$m/Type`, the S102 FQ-head grain). This is
    ///   structurally forced: the bodies compile in M's codegen batch, and
    ///   `compile_to_module` requires every compiled defn's entry + GOT slot
    ///   in the compiling module's OWN table. The `methods: Vec<Symbol>`
    ///   field lists the local names.
    ///
    /// The `impl_module: ModuleFullPath` field (S110 W0.1b,
    /// `backend-keyed-consumer.md` §1.1.1) is the pointer from the discovery
    /// record to the storage module — the impl-WRITER's module, whose table
    /// holds this impl's mangled method `Def`s and their GOT slots. Written
    /// from `state.current_module` at the shell construction
    /// (`impl_check.rs` `check_trait_impl`), so trait-method dispatch derives
    /// the selected method entry's home with one keyed probe — never a scan
    /// (resolves the callees.rs "Step 5" note; repairs the S101
    /// session-transaction reverse index for cross-module trait calls). It is
    /// a REQUIRED field (no `#[serde(default)]`): a defaulted `""` module is a
    /// representable-invalid state (Principle 20), and construction sites are
    /// forced to supply it (Principle 18).
    TraitImpl {
        trait_name: FQTraitName,
        impl_type: FQTypeName,
        /// The module whose table holds this impl's mangled method `Def`s and
        /// their GOT slots (the impl-writer's module). See the variant rustdoc
        /// above — the discovery→storage pointer for the amended Decision 45.
        impl_module: ModuleFullPath,
        /// Method names defined in this impl (local names, not mangled).
        methods: Vec<Symbol>,
        /// Always `Public` per spec §5.11.1 (impls are visible wherever both
        /// trait and type are in scope). The field is present so that every
        /// `ModuleEntry` variant carries `visibility` — the
        /// resolution-algorithm visibility filter is uniform (see
        /// `design/arch/bounded-contexts.md` §7). Marking
        /// `Public` on `TraitImpl` is lossless.
        visibility: Visibility,
    },
    /// A bare name that became ambiguous (two different sources registered it, Ring 2).
    ///
    /// Sentinel variant. Carries `visibility: Visibility` for variant
    /// uniformity (see `design/arch/bounded-contexts.md` §7);
    /// `Public` is the lossless mark (the sentinel itself never resolves to a
    /// payload, so visibility is informational only).
    Ambiguous {
        visibility: Visibility,
    },
}

// SAFETY: `ModuleEntry::Def` carries no raw pointer fields directly —
// the runtime address for an entry lives in the GOT slot referenced by
// `got_slot: Option<usize>` (the single source of truth for "where to call
// to invoke this entry"). `code: Option<C>` (Decision 25 + Decision 32) is
// parameterised over `C: CodeStore`, which itself requires `Send + Sync +
// 'static`. The safety of `code` is therefore delegated to whatever
// concrete type the integration layer chooses for `C` — for `C = ()` (the
// default for typecheck/frontend/backend), there is nothing to dereference;
// for `C = Code` (the integration layer's enum per Decision 35), `Code`
// carries its own `unsafe impl Send + Sync` with the `Arc<Jit>` /
// `Arc<Linker>` keeping the backing pages alive. The `CodeStore` bound
// guarantees `Send + Sync` propagates through `Option<C>`. The remaining
// fields are all owned data (no raw pointers, no shared interior
// mutability) and therefore Send + Sync via the auto traits, so this
// `unsafe impl` is informational only — it documents that the entry's
// thread-safety story now flows through `code` and the GOT (which is
// itself `Send + Sync` by virtue of holding `AtomicPtr`).
unsafe impl<C: CodeStore> Send for ModuleEntry<C> {}
unsafe impl<C: CodeStore> Sync for ModuleEntry<C> {}

impl<C: CodeStore> ModuleEntry<C> {
    /// Begin constructing a [`ModuleEntry::Def`] with the runtime-state
    /// fields defaulted.
    ///
    /// `ModuleEntry::Def` carries eleven fields, but six of them are always
    /// construction-time defaults at every static-table / mount call site:
    /// `callees: Vec::new()`, `value_use: false`, `trait_origin: None`,
    /// `seq: 0`, `ast: None`, `code: None`. Enum variants cannot use `..Default::default()`, so
    /// without a builder every construction spells out all of them even though
    /// it only cares about a few (`scheme`, `kind`, and usually `visibility`).
    /// This builder lets callers specify only what they care about.
    ///
    /// **The GOT slot rides on the `kind` (S83, FIXME 0356/0357, Principle
    /// 20).** There is no `got_slot` builder setter — the slot is no longer a
    /// flat `Def` field. A caller that wants a got-slotted callable passes the
    /// slot *inside* the kind it builds with:
    /// `ModuleEntry::def(scheme, DefKind::primitive(got_slot))` (or the
    /// explicit `DefKind::Primitive { body: PrimitiveBody::Extern { .. }, .. }`
    /// form — S102 FIXME 0476),
    /// `… DefKind::Constructor { got_slot, .. }`, or
    /// `… DefKind::UserFn { fn_state: UserFnState::Concrete { got_slot, .. } }`.
    /// To read a prior entry's concrete slot for REPL-redefinition reuse, call
    /// [`ModuleEntry::callable_got_slot`] on the existing entry.
    ///
    /// `visibility` defaults to [`Visibility::Public`] — the overwhelmingly
    /// common case for the production consumers (primitives, the int mount).
    /// Call [`DefBuilder::visibility`] to override.
    ///
    /// # Consumers
    ///
    /// This is the single Tier-1 production constructor for `Def` entries
    /// shared by every site that builds a symbol table by hand:
    /// `cranelisp-primitives` static-table assembly, the integration layer's
    /// synthetic-module mount (FIXME 0242), and the feature-gated
    /// `cranelisp_types::test_support` helpers (compiled only under the
    /// `test-support` feature). It is production surface (it enters
    /// `public-api.txt`).
    ///
    /// It realizes the `declare_def` helper deferred by FIXME 0241; the
    /// broader `declare_adt` / `declare_special_form` / `declare_trait`
    /// vocabulary remains deferred (minimum mechanism — only the `Def`
    /// constructor has two real consumers today).
    ///
    /// # Example
    ///
    /// ```ignore
    /// let entry: ModuleEntry = ModuleEntry::def(scheme, DefKind::primitive(slot))
    ///     .docstring("Add two integers")
    ///     .param_names(vec![Symbol::from("a"), Symbol::from("b")])
    ///     .build();
    /// ```
    pub fn def(scheme: Scheme, kind: DefKind) -> DefBuilder<C> {
        DefBuilder::new(scheme, kind)
    }

    /// Returns the callees for this entry, or an empty slice for variants without callees.
    ///
    /// Supports the `tc.symbol_table(module).get(name).callees()` dot-access pattern
    /// from the call graph design (Decision 21).
    pub fn callees(&self) -> &[FQSymbol] {
        match self {
            ModuleEntry::Def { callees, .. } => callees,
            // TraitImpl has no callees — it's an index/metadata entry.
            // The actual method Def entries carry their own callees.
            // (Per Submission 22, macro clause bodies are now Def entries
            // with mangled names, so their callees surface via the Def arm.)
            _ => &[],
        }
    }

    /// Returns true if this entry is publicly visible.
    ///
    /// Every `ModuleEntry` variant carries `visibility: Visibility` —
    /// public-ness consults that one field uniformly (see `design/arch/bounded-contexts.md` §7
    /// §"Symbol table — the single store"). The prior special-cases
    /// (`Import`/`Reexport`/`TraitImpl` always public, `Ambiguous` always
    /// false) collapse to the uniform `visibility` check.
    /// `TraitImpl` is constructed with `Visibility::Public` per spec §5.11.1;
    /// `Ambiguous` carries `Visibility::Public` as a lossless mark (the
    /// sentinel never resolves to a payload, so the visibility value is
    /// informational only).
    pub fn is_public(&self) -> bool {
        match self {
            ModuleEntry::Def { visibility, .. }
            | ModuleEntry::SpecialForm { visibility, .. }
            | ModuleEntry::TypeDef { visibility, .. }
            | ModuleEntry::IntrinsicType { visibility, .. }
            | ModuleEntry::TraitDecl { visibility, .. }
            | ModuleEntry::Import { visibility, .. }
            | ModuleEntry::TraitImpl { visibility, .. }
            | ModuleEntry::Ambiguous { visibility } => *visibility == Visibility::Public,
        }
    }

    /// The **concrete-boundary codegen view** of this entry's body, or `None`
    /// when the entry carries no codegen view.
    ///
    /// This is the backend's read-through for the body it codegens (Phase 3 of
    /// the `design/arch/concrete-boundary-type.md` arc): the returned
    /// [`MonoDefnVariant`] carries [`MonoExpr`](crate::MonoExpr) nodes whose
    /// `ty` is a [`ConcreteType`](crate::ConcreteType) — **no `Type`, no `Var`**
    /// on the read path. `compile_to_module` consults this rather than
    /// reconstructing a `Defn` from `ast` + reading `inferred_type` off `Expr`.
    ///
    /// `Some` for codegen-bound entries (concrete defns + mono instances) once
    /// the typecheck seam has populated it; `None` for non-codegen entries
    /// (template kinds, primitives, special forms, pre-body-check). A `None`
    /// here at a codegen-reached entry is the single relocated backstop (the
    /// backend's located `expect`). See the field rustdoc on `ModuleEntry::Def`.
    pub fn codegen_view(&self) -> Option<&MonoDefnVariant> {
        match self {
            ModuleEntry::Def { codegen_view, .. } => codegen_view.as_ref(),
            _ => None,
        }
    }

    /// Returns `true` iff this entry is a **constrained-fn template** — a
    /// `Def { kind: DefKind::UserFn { constrained_fn: Some(_) }, .. }`.
    ///
    /// A constrained template is the as-defined polymorphic body of a
    /// trait-bounded function (`(defn cmp [:Eq :Display a …] …)`). It is
    /// **never directly callable**: it cannot be compiled generically (it
    /// needs trait dictionaries resolved per call), so `defined_symbols()`
    /// excludes it from codegen and only its **monomorphised variants**
    /// (`cmp$Int+Int`, each carrying its own `got_slot`) are emitted and
    /// callable. See [`Self::callable_got_slot`].
    pub fn is_constrained_template(&self) -> bool {
        matches!(
            self,
            ModuleEntry::Def { kind, .. }
                if matches!(kind.as_ref(), DefKind::UserFn { fn_state: UserFnState::Constrained(_) })
        )
    }

    /// The GOT slot through which this entry may be **invoked**, or `None`
    /// when the entry has no directly-callable runtime address.
    ///
    /// This is the **single read-through point for "where to call to invoke
    /// this entry"** at call-target resolution — callers consult it rather
    /// than re-pattern-matching the `DefKind` variant set, so the callable /
    /// non-callable partition lives in exactly one place.
    ///
    /// **Trivial since S83 (FIXME 0356/0357, Principle 20).** With the slot
    /// carried on the callable `DefKind` variants (`UserFn`'s `Concrete`
    /// `fn_state`, `Primitive`, `Constructor`) and absent from the
    /// non-callable kinds, this accessor is a simple variant match — there is
    /// no longer an illegal `got_slot`+template pairing to "read around" (it
    /// is unconstructable). A constrained-fn template is
    /// `UserFnState::Constrained(_)`, which carries no slot, so it answers
    /// `None` structurally; the determined-parametric `UserFnState::Polymorphic`
    /// (S84 — non-concrete-but-unconstrained generic) likewise carries no slot
    /// and answers `None`; the Pass-1 interim `UserFnState::NotDetermined`
    /// also answers `None` (nothing may call an as-yet-undetermined fn). This
    /// retired the S82 stopgap's `mark_constrained_template()` flip-and-clear
    /// sole-writer and `assert_well_formed()` phantom-slot guard — there is no
    /// sibling field to clear or assert about. The GOT remains the single
    /// source of truth for the runtime *address*, indexed by the slot this
    /// accessor returns.
    ///
    /// Call-resolution sites (`cranelisp-backend::compiler::resolve_got_target`)
    /// consult this accessor; storage / serde / codegen sites that need the
    /// allocated index read it directly off the matched callable kind variant.
    /// See BC §7 "Callability is structural" and Principle 20
    /// (`design/arch/principles/20-*.md`).
    pub fn callable_got_slot(&self) -> Option<usize> {
        match self {
            ModuleEntry::Def { kind, .. } => match kind.as_ref() {
                DefKind::UserFn { fn_state: UserFnState::Concrete { got_slot, .. } } => {
                    Some(*got_slot)
                }
                // Only the Extern arm has a slot; an Inline primitive answers
                // `None` BY CONSTRUCTION (S102 FIXME 0476 — no consumer can
                // dispatch GOT-indirect through a body that cannot exist).
                DefKind::Primitive { body: PrimitiveBody::Extern { got_slot, .. }, .. } => {
                    Some(*got_slot)
                }
                DefKind::Primitive { body: PrimitiveBody::Inline, .. } => None,
                DefKind::Constructor { got_slot, .. } => Some(*got_slot),
                DefKind::PlatformEffect { got_slot, .. } => Some(*got_slot),
                // NotDetermined / Constrained / Polymorphic user fns, Macro
                // parent, PrimitiveExtern, Overloaded base — no slot.
                _ => None,
            },
            _ => None,
        }
    }

    /// `true` iff this entry is a **dispatchable call target** — either
    /// slot-dispatched ([`Self::callable_got_slot`] is `Some`) or an
    /// inline-dispatched primitive ([`PrimitiveBody::Inline`], whose body is
    /// backend inline emission with no slot by construction).
    ///
    /// This is the **resolution stop condition** (S102, FIXME 0476): name
    /// resolution walks (`resolve_driven`-family precedence) stop at the
    /// first entry that is a callable target, replacing the former
    /// `callable_got_slot().is_some()` predicate so that inline primitives
    /// participate in shadowing precedence identically to slot-carrying ones
    /// — callability is a kind fact, not a slot-presence proxy. Dispatch
    /// sites still read [`Self::callable_got_slot`] and must handle the
    /// `is_callable_target() ∧ slot-less` case by inline emission.
    pub fn is_callable_target(&self) -> bool {
        if self.callable_got_slot().is_some() {
            return true;
        }
        matches!(
            self,
            ModuleEntry::Def { kind, .. }
                if matches!(kind.as_ref(), DefKind::Primitive { body: PrimitiveBody::Inline, .. })
        )
    }

    /// The **type-def view** of this entry — `Some(&TypeDefInfo)` iff the
    /// entry answers *as a type*; the single "does this entry answer as a
    /// type" reader (Principle 7; the [`Self::callable_got_slot`] precedent
    /// applied to the type facet).
    ///
    /// A type name survives in the symbol table as one of two shapes (S79
    /// Option 3a — see the `DefKind::Constructor.type_def` rustdoc):
    ///
    /// - a [`ModuleEntry::TypeDef`] — the **sum/enum** case (type name
    ///   distinct from every ctor name); or
    /// - a `ModuleEntry::Def { kind: DefKind::Constructor { type_def:
    ///   Some(..), .. } }` — the **single-ctor product** case, where the
    ///   got-slotted ctor `Def` IS its own type and carries the type facet
    ///   (type-name == ctor-name).
    ///
    /// Every site that needs an entry *as a type* — resolution, arity
    /// validation, exhaustiveness, introspection, **persistence** — reads
    /// this accessor rather than matching `ModuleEntry::TypeDef` directly. A
    /// bare `TypeDef` match is exactly the FIXME-0573 defect class: the
    /// product `deftype` has no `TypeDef` entry, so a `TypeDef`-only reader
    /// silently skips it (int's `save.rs generate_types` skipped product
    /// types from backing-file persistence — silent data loss). Delegating
    /// consumers: typecheck's `type_def_view_of` (`checker.rs`) and int's
    /// `save.rs` type emission (both delegated in the S109 Phase-5 waves);
    /// [`crate::type_ctor_names`] is the ctor-name projection over the same
    /// two-shape switch.
    ///
    /// Read-side only — no serde/cache-schema impact.
    pub fn type_def_info(&self) -> Option<&TypeDefInfo> {
        match self {
            ModuleEntry::TypeDef { info, .. } => Some(info),
            ModuleEntry::Def { kind, .. } => match kind.as_ref() {
                DefKind::Constructor { type_def: Some(td), .. } => Some(td),
                _ => None,
            },
            _ => None,
        }
    }

    /// The entry's ownership summary ([`ModeSummary`]), or `None` when the
    /// entry carries none — the uniform read-through point for the
    /// typecheck→backend ownership contract (S102 CS-A; the
    /// [`Self::callable_got_slot`] precedent).
    ///
    /// `None` means the Decision-24 conservative point — both "not a
    /// summary-carrying kind" (non-callable kinds have no summary slot by
    /// construction) and "callable but not analysed / analysis off" read
    /// identically conservative (monotone soundness,
    /// `design/arch/ownership-inference.md` §6.1). For `DefKind::Primitive`
    /// the same slot carries the hand-declared fact table (spine §3.1(a),
    /// Principle 19 — one carrier, one read accessor).
    pub fn mode_summary(&self) -> Option<&ModeSummary> {
        match self {
            ModuleEntry::Def { kind, .. } => match kind.as_ref() {
                DefKind::UserFn { fn_state: UserFnState::Concrete { mode_summary, .. } } => {
                    mode_summary.as_ref()
                }
                DefKind::Primitive { mode_summary, .. } => mode_summary.as_ref(),
                DefKind::Constructor { mode_summary, .. } => mode_summary.as_ref(),
                DefKind::PlatformEffect { mode_summary, .. } => mode_summary.as_ref(),
                _ => None,
            },
            _ => None,
        }
    }

    /// Write this entry's ownership summary slot. Returns `true` iff the
    /// entry is a summary-carrying callable kind and the write landed;
    /// `false` (a did-not-write indicator, not an error) for every other
    /// shape — non-callable kinds have no summary slot by construction, so
    /// the caller (typecheck's publication walk, through
    /// `current_symbol_table_mut`) can treat `false` as "not a publication
    /// target" without pre-matching the kind.
    pub fn set_mode_summary(&mut self, summary: Option<ModeSummary>) -> bool {
        match self {
            ModuleEntry::Def { kind, .. } => match kind.as_mut() {
                DefKind::UserFn { fn_state: UserFnState::Concrete { mode_summary, .. } } => {
                    *mode_summary = summary;
                    true
                }
                DefKind::Primitive { mode_summary, .. } => {
                    *mode_summary = summary;
                    true
                }
                DefKind::Constructor { mode_summary, .. } => {
                    *mode_summary = summary;
                    true
                }
                DefKind::PlatformEffect { mode_summary, .. } => {
                    *mode_summary = summary;
                    true
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// The per-entry **value-use mark** (S102 CS-A;
    /// `design/typecheck/ownership-inference.md` §8.3) — `true` iff this
    /// callable is referenced in non-callee position somewhere in the
    /// program. `false` for non-`Def` entries and pre-analysis entries.
    pub fn value_use(&self) -> bool {
        match self {
            ModuleEntry::Def { value_use, .. } => *value_use,
            _ => false,
        }
    }

    /// Write the value-use mark. Returns `true` iff the entry is a `Def`
    /// (the only shape carrying the mark) and the write landed.
    pub fn set_value_use(&mut self, mark: bool) -> bool {
        match self {
            ModuleEntry::Def { value_use, .. } => {
                *value_use = mark;
                true
            }
            _ => false,
        }
    }
}

// --- Def builder (Tier-1 production constructor) ---

/// Chainable builder for [`ModuleEntry::Def`] — see [`ModuleEntry::def`].
///
/// Construct via [`ModuleEntry::def(scheme, kind)`](ModuleEntry::def), set the
/// fields you care about, and terminate with [`DefBuilder::build`] (or the
/// [`From<DefBuilder<C>>`] conversion). Every field defaults to its
/// construction-time value:
///
/// | Field | Default | Setter |
/// |---|---|---|
/// | `visibility` | [`Visibility::Public`] | [`Self::visibility`] |
/// | `docstring` | `None` | [`Self::docstring`] |
/// | `param_names` | `vec![]` | [`Self::param_names`] |
/// | `trait_origin` | `None` | [`Self::trait_origin`] |
/// | `seq` | `0` | [`Self::seq`] |
/// | `ast` | `None` | [`Self::ast`] |
/// | `callees` | `vec![]` | (no setter — populated by typecheck's `finalize_check_result`, never at construction) |
/// | `value_use` | `false` | (no setter — written by typecheck's ownership pass via [`ModuleEntry::set_value_use`], never at construction) |
/// | `code` | `None` | (no setter — runtime-only, written by backend after `compile_to_module`) |
///
/// `callees` and `code` deliberately have no setter: they are runtime-state
/// fields populated downstream (callees by typecheck, code by backend), never
/// at table-assembly time. Constraining the builder to construction-time
/// concerns keeps the runtime-state single-source-of-truth invariants
/// (Principle 7) intact.
#[derive(Debug, Clone)]
pub struct DefBuilder<C: CodeStore = ()> {
    scheme: Scheme,
    kind: DefKind,
    visibility: Visibility,
    docstring: Option<String>,
    param_names: Vec<Symbol>,
    trait_origin: Option<FQTraitName>,
    seq: u64,
    ast: Option<DefnVariant>,
    codegen_view: Option<MonoDefnVariant>,
    _code: std::marker::PhantomData<C>,
}

impl<C: CodeStore> DefBuilder<C> {
    /// Start a builder with `scheme` + `kind`; all other fields default
    /// (see [`DefBuilder`] for the default table). Prefer
    /// [`ModuleEntry::def`] as the entry point.
    pub fn new(scheme: Scheme, kind: DefKind) -> Self {
        DefBuilder {
            scheme,
            kind,
            visibility: Visibility::Public,
            docstring: None,
            param_names: Vec::new(),
            trait_origin: None,
            seq: 0,
            ast: None,
            codegen_view: None,
            _code: std::marker::PhantomData,
        }
    }

    /// Override the visibility (defaults to [`Visibility::Public`]).
    pub fn visibility(mut self, visibility: Visibility) -> Self {
        self.visibility = visibility;
        self
    }

    /// Set the docstring.
    pub fn docstring(mut self, docstring: impl Into<String>) -> Self {
        self.docstring = Some(docstring.into());
        self
    }

    /// Set the parameter names.
    pub fn param_names(mut self, param_names: Vec<Symbol>) -> Self {
        self.param_names = param_names;
        self
    }

    /// Set the trait this Def is a method of (normally defaulted to `None`).
    pub fn trait_origin(mut self, trait_origin: FQTraitName) -> Self {
        self.trait_origin = Some(trait_origin);
        self
    }

    /// Set the per-entry sequence token (normally defaulted to `0`; the
    /// authorship-order allocator lives on [`SymbolTable::next_seq`]).
    pub fn seq(mut self, seq: u64) -> Self {
        self.seq = seq;
        self
    }

    /// Set the typechecked body (normally defaulted to `None`; primitives,
    /// special forms, and pre-body-check entries carry `None`).
    pub fn ast(mut self, ast: DefnVariant) -> Self {
        self.ast = Some(ast);
        self
    }

    /// Set the concrete-boundary codegen view (the [`MonoDefnVariant`] whose
    /// nodes carry [`ConcreteType`](crate::ConcreteType)). Normally defaulted to
    /// `None`; populated for codegen-bound entries (concrete defns + mono
    /// instances) at the typecheck mono/body-check seam. See the
    /// `ModuleEntry::Def.codegen_view` field rustdoc.
    pub fn codegen_view(mut self, codegen_view: MonoDefnVariant) -> Self {
        self.codegen_view = Some(codegen_view);
        self
    }

    /// Materialize the [`ModuleEntry::Def`]. `callees` and `code` are always
    /// the construction-time defaults (`Vec::new()` / `None`).
    pub fn build(self) -> ModuleEntry<C> {
        ModuleEntry::Def {
            scheme: self.scheme,
            visibility: self.visibility,
            docstring: self.docstring,
            param_names: self.param_names,
            kind: Box::new(self.kind),
            callees: Vec::new(),
            value_use: false,
            trait_origin: self.trait_origin,
            seq: self.seq,
            ast: self.ast,
            codegen_view: self.codegen_view,
            code: None,
        }
    }
}

impl<C: CodeStore> From<DefBuilder<C>> for ModuleEntry<C> {
    fn from(builder: DefBuilder<C>) -> Self {
        builder.build()
    }
}

// --- Definition Classification ---

/// What kind of definition a symbol is.
///
/// **S69 Submission 36 settlement.**
/// - `SpecialForm` retired from `DefKind` — promoted to its own
///   `ModuleEntry::SpecialForm` variant (special forms read only 4 of
///   `Def`'s ~11 fields; dedicated variant fits the introspection use
///   case, parallels `ModuleEntry::IntrinsicType` per Submission 30).
/// - `Primitive` collapsed to a payload-free discriminator — the prior
///   `PrimitiveKind { Inline, Extern, PlatformEffect }` sub-discriminator
///   and the `jit_name: Option<JitSymbol>` sibling field are both
///   retired. The discriminator alone signals "bundled compiler-provided
///   body" (lives in `cranelisp-primitives`); inline-eligibility was
///   never read from `PrimitiveKind` in production (only test assertions
///   — verified by grep at submission time) and is encoded per-call-site
///   in `ResolvedCall::BuiltinFn { name }` (set by typecheck), not in a
///   `PrimitiveKind::Inline` discriminator. The retired `jit_name`
///   field's value is the symbol-table key uniformly per `src/CLAUDE.md`
///   §"JIT Symbol Names" — every symbol addressable as `module/symbol`
///   (or the appropriate mangled form for trait methods / multi-sig
///   variants); the key IS the JIT linker name. No separate `jit_name`
///   field is needed.
/// - `PlatformEffect { scheduling_class }` promoted from a sub-variant
///   of `PrimitiveKind` to a sibling variant of `DefKind`. The
///   `scheduling_class` is the cross-crate-load-bearing payload — read
///   by `src/worker.rs` for JIT-symbol-table registration of DLL-routed
///   effects, and carried in IO trampoline records per Decision 26.
///   PlatformEffect's body location (DLL) is structurally distinct from
///   bundled-primitive provenance — sibling variants under `DefKind`
///   reflect that (provenance discriminator is on `DefKind`, not nested
///   one level deeper).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DefKind {
    /// A built-in primitive bundled in `cranelisp-primitives`.
    ///
    /// No payload — the discriminator alone signals "bundled
    /// compiler-provided body". The symbol-table key IS the JIT linker
    /// name uniformly per `src/CLAUDE.md` §"JIT Symbol Names"; no
    /// separate `jit_name` field. Inline-eligibility for arithmetic /
    /// vec / sexp ops is encoded per-call-site in
    /// `ResolvedCall::BuiltinFn { name }` (set by typecheck), not on
    /// this discriminator.
    ///
    /// See `DefKind::Primitive` rustdoc and
    /// Decision 48 (primitives uniform module + bundled provenance).
    ///
    /// **Body/dispatch discriminator (S102, FIXME 0476 — Principle 20 applied
    /// one level down from the S83 kind⇔slot reshape).** How a primitive's
    /// body is reached lives on [`PrimitiveBody`]: an **`Extern`** primitive
    /// carries its mandatory GOT slot (an extern shim body is stored there at
    /// registration; the operator-as-value path `(let [f +] (f 1 2))`
    /// indirects through it), while an **`Inline`** primitive carries NO slot
    /// **by construction** — its only body is backend inline emission keyed
    /// by canonical bare name, so "resolvable but not slot-callable" is a
    /// *kind*, not a name-list, and
    /// [`ModuleEntry::callable_got_slot`] answers `None` for it structurally
    /// (no consumer can dispatch GOT-indirect through a body that cannot
    /// exist — the allocated-but-NULL-slot defect class is unrepresentable).
    /// Resolution stop conditions use [`ModuleEntry::is_callable_target`],
    /// which covers both arms.
    ///
    /// **`mode_summary` is the hand-declared primitive fact table** (spine
    /// `design/arch/ownership-inference.md` §3.1(a); typecheck proposal §9) —
    /// declared constants seeding the ownership fixpoint at the leaves,
    /// populated at static registration (`cranelisp-primitives`). The SAME
    /// carrier inferred summaries ride (Principle 19 — the pass cannot tell a
    /// declared leaf from an inferred summary except by `DefKind`). Analysis
    /// inputs only: the extern consuming convention is unchanged. `None` ⇒
    /// the Decision-24 conservative point.
    Primitive {
        body: PrimitiveBody,
        #[serde(default)]
        mode_summary: Option<ModeSummary>,
    },
    /// A DLL-routed platform effect.
    ///
    /// `scheduling_class` is the cross-crate-load-bearing payload — read
    /// by `src/worker.rs` for JIT-symbol-table registration of DLL-routed
    /// effects, and carried in IO trampoline records per Decision 26.
    /// PlatformEffect's body lives in a platform DLL (loaded into the
    /// platform module's `SymbolTable.dll`); contrast `DefKind::Primitive`
    /// whose body is bundled in `cranelisp-primitives`.
    ///
    /// See `DefKind::PlatformEffect` rustdoc and
    /// Decision 26 (scheduling-class lives on the platform-effect variant
    /// so ill-formed states — "a user fn with a scheduling class" — are
    /// unrepresentable).
    ///
    /// **S94 R1 — the poll-shape discriminator (`poll_shape`, FIXME 0457).**
    /// The effect-concurrency seam (`effect-concurrency.md` §13 "S94 R1") keys
    /// the backend's two emission arms on whether the effect is a poll-shape
    /// async leaf vs a v6 blocking effect. That bit cannot be recovered from
    /// `scheduling_class` (`ConcurrencyDescriptor::from_scheduling_class` maps
    /// **all three** classes to `blocking == 1`), so it rides here as its own
    /// orthogonal field. `scheduling_class` is the *conflict-domain* axis
    /// (token/cardinality semantics for the three classes); `poll_shape` is the
    /// orthogonal *dispatch* axis (reactor poll-leaf vs blocking call) — exactly
    /// the orthogonality `ConcurrencyDescriptor` documents between
    /// `{token,cardinality}` and `blocking`. The full `ConcurrencyDescriptor` is
    /// **not** carried here because that type is `#[cfg(feature="concurrency")]`
    /// (a dormant C-ABI contract, off the frozen `public-api.txt` edge) while
    /// `DefKind` is core/ungated; graduating it onto the symbol table is a later,
    /// deliberate step gated on lifting that dormancy (a native cardinality-N
    /// pool + `global_budget` — both slice-≥4 / unbuilt — are the only surface
    /// `{scheduling_class, poll_shape}` does not already cover).
    PlatformEffect {
        scheduling_class: SchedulingClass,
        /// `true` ⇒ a poll-shape async leaf (the loader lifted
        /// `ConcurrencyDescriptor.blocking == 0` from the unified
        /// `PlatformFn::concurrency`); backend emits the poll-construction arm
        /// (`IO_TAG_EFFECT_POLL` + host-built state-closure). `false` ⇒ a
        /// blocking effect; backend emits the unchanged blocking call. Polarity
        /// is inverted from the C-ABI `blocking` field so that the serde default
        /// (`false`) is the byte-identical blocking world — a cached pre-S94
        /// `PlatformEffect` (no field in its JSON) deserializes as a blocking
        /// effect, exactly as before. (FIXME 0457; `effect-concurrency.md`
        /// §13 "S94 R1" + Appendix B "ratified backend↔intrinsics seam".)
        #[serde(default)]
        poll_shape: bool,
        /// The GOT slot through which this platform effect is invoked
        /// (manifest index, §5.3). A platform effect is a GOT-addressable
        /// callable — backend dispatches it GOT-indirect and the platform DLL
        /// loader writes its runtime pointer into `SymbolTable.got` at this
        /// slot, so the slot is **mandatory** (not `Option`), same as
        /// [`DefKind::Primitive`]. (S83, FIXME 0358 — PlatformEffect was
        /// incorrectly placed in the slot-less set by the Option-A reshape;
        /// pending `/arch` ratification.) `poll_shape` does not affect slotting:
        /// poll-shape and blocking effects are both GOT-addressable callables.
        got_slot: usize,
        /// Ownership summary slot ([`ModeSummary`]) — carried for uniformity
        /// with the other callable kinds (the summary rides where the slot
        /// rides, `design/arch/ownership-inference.md` §3.3), but **stays
        /// `None` throughout increment I**: platform calls are a pinned
        /// Decision-24 boundary (mode vectors do NOT join the platform
        /// manifest — spine §3.1 boundary pins).
        #[serde(default)]
        mode_summary: Option<ModeSummary>,
    },
    /// A host-promised extern primitive.
    ///
    /// Like `DefKind::PlatformEffect`, this is a host-promised callable whose
    /// body lives **outside** `cranelisp-primitives` — but the body is supplied
    /// by the integration layer (`int`) at JIT-finalize via
    /// `Jit::define_symbol`, not loaded from a platform DLL. The motivating
    /// member is `discover-tests`: its body must read int's live typed session
    /// state (the per-module `SymbolTable` + GOT) to enumerate eligible
    /// `test-*` functions, which `cranelisp-intrinsics` cannot do because it
    /// cannot name `Code` (Principle 18 / Decision 0048).
    ///
    /// **No payload — unit variant** (Principle 6, minimum mechanism). The
    /// contract is carried entirely by the kind discriminant plus the field
    /// invariants common to host-promised slot-less kinds:
    /// - **The symbol-table key IS the ABI name** (`src/CLAUDE.md` §"JIT Symbol
    ///   Names"); there is no separate `jit_name`. Backend lowers a call to a
    ///   `PrimitiveExtern` callee as a `Linkage::Import` against the key.
    /// - **No GOT slot** — `got_slot: None`. The entry joins the slot-less
    ///   classes enumerated in the `got_slot` rustdoc on `ModuleEntry::Def`:
    ///   a `PrimitiveExtern` is never invoked GOT-indirect and is never used as
    ///   an operator-as-value, so it has no module-local callable address. (A
    ///   call to it resolves to the host-promised symbol, not to a GOT slot —
    ///   the discovered wrappers it *returns* are the GOT-indirect callables.)
    /// - **`code: None`** — the body is promised by the publisher, not held on
    ///   the entry; primitive-ness/provenance reads from `kind`.
    ///
    /// `DefKind::PlatformEffect` is the direct structural precedent (a
    /// host-promised callable whose body lives elsewhere, registered by walking
    /// the kind at JIT setup). `PrimitiveExtern` is the same shape with the body
    /// promised by `int` via `Jit::define_symbol` rather than loaded from a DLL,
    /// and with no `scheduling_class` (it is not an IO effect).
    ///
    /// See `design/arch/test-discovery.md` §6 "`DefKind::PrimitiveExtern`" + §7
    /// (the entry shape) and the `got_slot` slot-less-kinds rustdoc note on
    /// `ModuleEntry::Def`.
    PrimitiveExtern,
    /// A user-defined function.
    ///
    /// **Callability is structural (S83, FIXME 0356/0357, Principle 20; amends
    /// Decision 0035).** The GOT slot through which a user fn is invoked lives
    /// *here*, on the kind's [`UserFnState`] payload — not on a flat
    /// `ModuleEntry::Def.got_slot` field (which is retired). This makes the
    /// once-illegal pairing — a constrained *template* (never directly callable;
    /// only its monomorphised variants are) holding a callable slot —
    /// **structurally unconstructable**: only the [`UserFnState::Concrete`]
    /// variant carries a slot, and a constrained fn is [`UserFnState::Constrained`]
    /// which has no slot field. The three legal states are exactly the three
    /// `UserFnState` variants; the illegal fourth (constrained + slot) has no
    /// representation. See [`UserFnState`] and BC §7 "Callability is structural".
    UserFn {
        fn_state: UserFnState,
    },
    /// Multi-sig overloaded function base name (Ring 2).
    Overloaded {
        variants: Vec<OverloadVariant>,
    },
    /// An ADT constructor (see `design/arch/bounded-contexts.md` §7
    /// "Multi-legged authoring" for the ctor-as-Def shape and rejected alternatives).
    ///
    /// The Def's `ast` field carries a synthesised `DefnVariant` whose body
    /// expression is `Expr::ConstrADT { type_name, tag, fields, span }` (S69
    /// Submission 35 narrowed `ast: Option<Defn>` to `ast: Option<DefnVariant>`;
    /// constructors synthesise the single meaningful payload directly). The metadata on
    /// this variant (`type_name`, `tag`, `field_count`, `internal`) is read by
    /// pattern matching (`Pattern::Constructor` → consult `DefKind::Constructor.tag`)
    /// and by REPL introspection (`/info` displays the owning ADT + constructor
    /// metadata). Backend codegen lowers the synthesised body's `Expr::ConstrADT`
    /// node — it never reads this variant's metadata for code emission.
    ///
    /// `internal: true` for compiler-internal constructors that users cannot
    /// directly construct or pattern-match (e.g., `IO.Bind` is constructed only
    /// by `bind`).
    ///
    /// **Product-type dual facet — `type_def` (S79 Option 3a).** A
    /// **single-ctor product type** (`(deftype Rectangle [:Int w :Int h])`)
    /// has type-name == ctor-name, so the type and its constructor collide on
    /// one symbol-table key (`"Rectangle"`). Rather than let a
    /// `ModuleEntry::TypeDef` overwrite the got-slotted ctor `Def` (the prior
    /// model — which dropped the ctor's `param_names` field names and broke
    /// product-ctor-as-first-class-value, a §4.2.1 spec violation propped up
    /// by six bespoke `constructor_scheme` fallback legs), the surviving
    /// `"Rectangle"` entry is the **got-slotted ctor `Def`** (exactly like a
    /// sum ctor) carrying a **type facet** so it ALSO answers as its own type.
    ///
    /// - `type_def: Some(..)` ⟺ **this constructor IS its own type** — the
    ///   single-ctor product case (type-name == ctor-name). The carried
    ///   `TypeDefInfo` (`name` / `type_params` / `constructors`) is the
    ///   type-def view a consumer reads when it needs the entry *as a type*
    ///   (resolution, introspection, schema). Field names are NOT duplicated
    ///   here — they stay on the ctor `Def`'s `param_names`, the single source
    ///   (Principle 7); `TypeDefInfo` deliberately carries no `field_names`
    ///   list.
    /// - `type_def: None` ⟺ an **ordinary sum/enum constructor** whose type is
    ///   a *separate* `ModuleEntry::TypeDef` entry under a distinct key
    ///   (`Option` vs `Some`/`None`). The ctor answers only as a value/callable.
    ///
    /// In short: product ctors are got-slotted `Def`s that carry their type
    /// facet — they are NOT absorbed into a `ModuleEntry::TypeDef`. The prior
    /// `ModuleEntry::TypeDef.constructor_scheme: Option<Scheme>` smuggling
    /// field (the seam the six fallback legs keyed on) is retired; the ctor's
    /// function-type signature lives canonically on the `Def`'s own `scheme`.
    /// See `design/arch/bounded-contexts.md` §7 "Multi-legged authoring".
    Constructor {
        /// Module-local GOT slot through which the constructor is invoked
        /// (the operator-as-value path `(map Some xs)` indirects through it).
        ///
        /// **Carries its `got_slot` (S83, FIXME 0356/0357, Principle 20).** A
        /// constructor is an addressable callable, born concrete at synthesis
        /// (it is never constrained), so the slot is **mandatory** — it moved
        /// here off the retired flat `ModuleEntry::Def.got_slot` field.
        got_slot: usize,
        type_name: FQTypeName,
        tag: usize,
        field_count: usize,
        #[serde(default)]
        internal: bool,
        /// The type facet for a single-ctor **product** type (type-name ==
        /// ctor-name). `Some(TypeDefInfo)` iff this constructor IS its own
        /// type — the entry answers both as a got-slotted ctor `Def` AND as
        /// its type. `None` for ordinary sum/enum ctors whose type is a
        /// separate `ModuleEntry::TypeDef` entry. Boxed to keep the common
        /// (`None`) variant small. Field names are NOT stored here — they live
        /// on the Def's `param_names` (single source, Principle 7).
        #[serde(default)]
        type_def: Option<Box<TypeDefInfo>>,
        /// Ownership summary slot ([`ModeSummary`]) — carried for uniformity
        /// with the other callable kinds (the summary rides where the slot
        /// rides, `design/arch/ownership-inference.md` §3.3). Constructors
        /// are a Decision-24-by-construction boundary pin (field-store
        /// consumes; always `Owned` per param — spine §3.1), so this stays
        /// `None` in increment I; the classifier hardwires ctor behaviour
        /// rather than reading a summary.
        #[serde(default)]
        mode_summary: Option<ModeSummary>,
    },
    /// A multi-clause macro parent entry (S69 Submission 13 macro-unification).
    ///
    /// **Storage shape.** The parent `ModuleEntry::Def { kind: DefKind::Macro
    /// { clauses_meta }, .. }` carries dispatch metadata only — per-clause
    /// compiled bodies live as **separate** `ModuleEntry::Def` entries under
    /// mangled names `{macro-name}$clause-{N}` with `kind: DefKind::UserFn`,
    /// `got_slot: Some(_)`, `ast: Some(DefnVariant)`, and `code: Some(_)`
    /// populated. The mangled-variant shape parallels multi-sig fn variants
    /// (`add$Int+Int` etc.) per `bounded-contexts.md` §7 "Macros are Defs".
    ///
    /// **Parent metadata-only.** This parent entry has no callable runtime
    /// address — `got_slot` is `None` (see the `got_slot` rustdoc on `Def`,
    /// which names `Def { kind: DefKind::Macro }` parent entries among the
    /// slot-less classes). Invocation dispatches to a clause-body Def via
    /// `clauses_meta` walk + GOT-lookup on the matched variant's mangled name.
    ///
    /// **Fields.**
    /// - `clauses_meta` carries per-clause `MacroClauseInfo` (`params` with
    ///   bracket destructuring shape via `MacroParam`, `rest_param`) for the
    ///   dispatcher's pattern-match. The dispatch order is authorship-order —
    ///   `clauses_meta[0]` is tried first, then `[1]`, etc., per the
    ///   multi-clause `defmacro` spec. `MacroClauseInfo` has no parallel on
    ///   any other `DefKind` variant — it is the macro-specific dispatcher
    ///   lookup table and the sole reason this variant exists distinct from
    ///   `DefKind::UserFn`.
    ///
    /// **Introspection vs compile — the D1 split (S80, reverses Decision 41
    /// for macro `sexp` only).** Two distinct readers consumed the per-symbol
    /// "original form" data, and they have **different homes** after D1:
    ///
    /// - **Compile-path reader → symbol table (`macro_sexp`, above).** The
    ///   on-demand macro-clause recompile (`worker::resolve_macro_sexp_from` →
    ///   `parse_defmacro` → `compile_macro_with_state`) is a *compile* need —
    ///   it rebuilds clause code during FQ-autoload and cache-restore. Per the
    ///   S80 user ruling ("any data the COMPILE pipeline reads MUST live in the
    ///   symbol table, not introspection — it's in the name"), the macro's
    ///   source form lives on this variant's `macro_sexp` field.
    /// - **REPL-introspection readers → int-layer `Introspection` record.**
    ///   `source`, `expanded`, `clif_ir`, `disasm`, `code_size` (and the
    ///   `sexp` *display* used by `/sexp`) for ALL Def variants — macros
    ///   included — live on the per-`FQSymbol` `Introspection` record in
    ///   `SharedState.introspection` (`src/session_v4.rs`). These back the
    ///   REPL slash-commands ONLY and are populated ONLY in REPL mode. The
    ///   compile pipeline never reads them; the mode signal is no longer
    ///   `introspection.is_some()` (see BC §6 — int carries an explicit
    ///   `CompileMode`/run-mode on `SharedState`, set from `main.rs`'s
    ///   `Action`). `design/arch/bounded-contexts.md` §int places introspection
    ///   in the integration layer ("development tooling: tracing,
    ///   observability, introspection").
    ///
    /// **Why D41's symmetry still holds for every *other* kind.** Decision 41
    /// retired the per-entry `sexp` field for symmetry — no other `DefKind`
    /// carries a `sexp`, and REPL display reads a uniform per-FQSymbol store.
    /// That symmetry is preserved for the *introspection* readers. Macros are
    /// the one kind whose *compile* path needs the original form, and they are
    /// the one kind with no `ast: Option<DefnVariant>` to carry a compile
    /// payload (the macro parent's clause bodies are separate mangled-name
    /// Defs). `macro_sexp` is therefore scoped to this variant — NOT a
    /// reintroduced generic `Def.sexp` — so `DefKind::UserFn`,
    /// `DefKind::Constructor`, etc. stay symmetric with each other and unchanged.
    ///
    /// **Cache-restore is solved by serialization (D1), not by introspection
    /// rehydration.** Because `macro_sexp` serializes (no `#[serde(skip)]`), a
    /// cache-restored macro entry carries its source form and the recompile
    /// path works directly off the entry. The earlier "cache-hit residual gap"
    /// (introspection not rehydrated on cache load) no longer blocks the
    /// *compile* path — that path reads `macro_sexp`, not introspection. A
    /// residual REPL-tooling gap remains for the *introspection* readers
    /// (`/source` of a cache-loaded symbol): `Introspection` is REPL-only +
    /// non-Serde, so REPL-editing a cache-loaded module still cannot trigger
    /// `.cl` regeneration for symbols whose introspection entries are absent.
    /// The future fix for THAT is lazy re-read of the backing source file on
    /// demand; serializing the whole `Introspection` record into the cache
    /// is NOT the answer (mixes REPL concerns into the cache). Note: macro
    /// `.cl` regeneration (`save::generate_module_source`) can now read
    /// `macro_sexp` off the symbol table as a fallback when the introspection
    /// record is absent — see BC §6.
    ///
    /// **Retired storage.** The prior `ModuleEntry::Macro` sibling variant was
    /// retired in Submission 22 (deleted from source 2026-05-21). The
    /// session-level `MacroEnv` sidecar retires alongside — clause bodies live
    /// in the symbol table under mangled names rather than in a separate
    /// dispatch map. See the `ModuleEntry::Macro retired` comment between the
    /// `Constructor` and `TraitImpl` variants for the cross-reference trail.
    ///
    /// See `crates/cranelisp-frontend/src/expand.rs` rustdoc for the
    /// dispatcher behaviour (post-S70 B3-C the canonical home; the
    /// per-crate `facades/frontend.md` document was retired);
    /// `design/arch/bounded-contexts.md` §7 for the bounded-context
    /// invariants (macros are Defs; the clause-walk dispatch story).
    Macro {
        clauses_meta: Vec<MacroClauseInfo>,
        /// The macro's original definition s-expression — the parsed
        /// `(defmacro name …)` form. **Compile-path data** (D1 reversal of
        /// Decision 41, S80): the on-demand macro-clause recompile path
        /// (`worker::resolve_macro_sexp_from` → `parse_defmacro` →
        /// `compile_macro_with_state`) needs the source form to rebuild a
        /// macro's clause code when its GOT slot is empty (FQ-autoload of a
        /// cross-module macro; cache-restore where the clause `.o` was not
        /// linked inline). Because this is data the **compile pipeline reads**
        /// — not REPL slash-command introspection — it lives on the symbol-
        /// table entry, never on `SharedState.introspection` ("it's in the
        /// name": introspection is REPL-command-only).
        ///
        /// **Serde / cache.** Serialized like `clauses_meta` (no
        /// `#[serde(skip)]`): the field round-trips through the disk cache, so
        /// a cache-restored macro entry carries its `macro_sexp` and the
        /// recompile path works without any rehydration step. `Sexp` already
        /// derives `Serialize`/`Deserialize` and is the canonical macro-clause
        /// metadata's sibling — adding it here is the same serialization
        /// discipline `clauses_meta` already follows. The serialized cost is a
        /// single parsed form per macro Def, bounded by the source size; this
        /// is acceptable for the compile-necessary payload (contrast the
        /// rejected option of serializing the whole `Introspection` record,
        /// which mixes REPL-only fields into the cache).
        ///
        /// **Why on `DefKind::Macro` and not a generic `Def.sexp`.** Decision
        /// 41 retired the per-entry `sexp` field for *symmetry* — no other
        /// `DefKind` carries a `sexp`, and the introspection store was the
        /// uniform home for `source`/`sexp`/`expanded` across all Def kinds for
        /// REPL display. That symmetry holds for the *introspection* readers
        /// (`/source`, `/sexp`, `/expand` — still served from the int-layer
        /// `Introspection` record). Macros are the *one* kind whose **compile**
        /// path needs the original form (other kinds carry their compile
        /// payload as `ast: Option<DefnVariant>` — a macro parent has no `ast`
        /// because its clause bodies are separate mangled-name Defs, so the
        /// recompile source has nowhere else to live). Scoping the field to
        /// the macro variant — rather than reintroducing a generic
        /// `Def.sexp` — preserves D41's symmetry for every other kind while
        /// giving the macro compile path its required input on the symbol
        /// table.
        macro_sexp: Sexp,
    },
}

impl DefKind {
    /// Convenience constructor for the common extern-shimmed primitive shape:
    /// `Primitive { body: Extern { got_slot, no sibling }, no declared facts }`.
    ///
    /// The registration sites that declare ownership facts or a borrowed
    /// sibling (`cranelisp-primitives`) construct the variant literally; every
    /// other site (typecheck bootstrap seeding, tests) uses this.
    pub fn primitive(got_slot: usize) -> DefKind {
        DefKind::Primitive {
            body: PrimitiveBody::Extern { got_slot, borrowed_sibling_slot: None },
            mode_summary: None,
        }
    }
}

/// How a [`DefKind::Primitive`]'s body is reached — the body/dispatch
/// discriminator (S102, FIXME 0476; Principle 20 applied one level down from
/// the S83 kind⇔slot reshape).
///
/// The defect class this makes unrepresentable: an entry whose *kind* says
/// "slot-carrying callable" while its slot is allocated-but-NULL (no extern
/// body can exist — the vec-query-family SIGSEGV, third instance of the
/// phantom-slot class). With the discriminator, "resolvable but not
/// slot-callable" is a *kind*, not a name-list:
/// [`ModuleEntry::callable_got_slot`] answers `None` for [`Self::Inline`] by
/// construction, and resolution stop conditions read
/// [`ModuleEntry::is_callable_target`] (covering both arms) so shadowing
/// precedence is unchanged.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PrimitiveBody {
    /// An extern-shimmed primitive: a Rust body is stored in the GOT at
    /// registration and the entry is GOT-indirect dispatchable (both at
    /// statically-resolved sites and on the operator-as-value path).
    Extern {
        /// Module-local GOT slot holding the extern shim — **mandatory** (an
        /// extern primitive always has an address).
        got_slot: usize,
        /// GOT slot of the optional **borrowed-convention sibling** export
        /// (`<name>$borrowed` — `design/backend/ownership-codegen.md` §9.1):
        /// a second entry point sharing the consuming export's core but
        /// emitting no consuming dec, targeted by the backend at extern call
        /// sites where the declared facts + site borrow-classification allow
        /// (§9.3 four-leg gate). `None` ⇒ no sibling registered ⇒ every call
        /// takes the consuming export (the Decision-24 path). Rides the
        /// `Extern` arm only: an inline primitive has no extern body, so an
        /// inline-with-sibling state is unrepresentable (Principle 20).
        #[serde(default)]
        borrowed_sibling_slot: Option<usize>,
    },
    /// An inline-lowered primitive (the vec query family): the ONLY body is
    /// backend inline emission keyed by canonical bare name — no GOT slot, no
    /// extern shim, **by construction**. Value-use paths (fn-as-value,
    /// auto-curry) must synthesize inline-emitting wrappers rather than
    /// dispatch through a slot.
    Inline,
}

/// The determined-or-not callability state of a [`DefKind::UserFn`] entry
/// (S83, FIXME 0356/0357, Principle 20; amends Decision 0035).
///
/// This is the structural realisation of the "callability is a kind property"
/// invariant: a user fn's GOT slot is correlated with whether the fn is a
/// directly-callable concrete function or a constrained template (only the
/// former is invokable through a slot). Modelling the correlation as a sum type
/// — one variant per legal state, each carrying exactly the data valid in that
/// state — makes the illegal pairing (a constrained template holding a callable
/// slot) **unconstructable** (Principle 20 "parse, don't validate"). The S82
/// stopgap (`callable_got_slot()` reading around a flat `got_slot` field +
/// `mark_constrained_template()` sole-writer) is retired by this shape.
///
/// **The S84 generalisation (FIXME 0377, user-ratified 2026-06-16).** The
/// correlated invariant the sum type encodes is the GENERAL one: **a def has a
/// GOT slot ⟺ its type is fully concrete (`Type::is_concrete()` — no
/// `Type::Var`), NOT merely ⟺ it is unconstrained.** A constrained template is
/// one species of non-concrete def (vars pinned per-call by trait dictionaries);
/// a plain generic def (`id : ∀a. a→a`, a `(Box a)`-result HOF) is *equally*
/// non-concrete and *equally* slot-less, yet carries no trait constraints. The
/// slot-eligibility gate is therefore `is_concrete()`, not
/// `constraints.is_empty()`; the determined-but-non-concrete unconstrained def
/// gets its own slot-less [`UserFnState::Polymorphic`] arm so that
/// `Concrete { got_slot } ∧ non-concrete-type` stays unconstructable.
///
/// **The four legal states**, and where each is constructed:
///
/// 1. [`UserFnState::NotDetermined`] — the **Pass-1 interim**. Typecheck
///    `register_defn_signature` registers a user fn's scheme/signature *before*
///    Pass-2 constraint detection runs, so callability is not yet known. The
///    entry has no slot — which is correct, because nothing may call it before
///    its callability is determined. This is the absence of a determined
///    callable payload, **NOT** a separate `Pending` enum arm (gating decision 3):
///    the `UserFn` discriminator already names the kind; this variant names the
///    not-yet-determined sub-state without adding `ModuleEntry`-level surface.
/// 2. [`UserFnState::Concrete`] — a **determined unconstrained callable**.
///    Carries `got_slot: usize` (mandatory, not `Option`): an unconstrained fn
///    always has a module-local callable address. Constructed at the
///    determination point (end of Pass-2 when no constraints were found), and
///    for every mangled mono / multi-sig / macro-clause variant (`cmp$Int+Int`,
///    `add$Int+Int`, `m$clause-0`), each owning its own slot.
/// 3. [`UserFnState::Constrained`] — a **determined constrained template**.
///    Carries the [`ConstrainedFn`] body and **no slot**: a template is never
///    directly callable (only its mono variants, which are `Concrete` entries,
///    are), so it structurally cannot hold a callable address.
/// 4. [`UserFnState::Polymorphic`] — a **determined generic / parametric
///    template** (S84). Carries the [`ParametricFn`] body and **no slot**:
///    non-concrete (residual `Type::Var`) but trait-unconstrained. Slot-less for
///    the same reason as `Constrained` (only its concrete mono instances are
///    callable); a *sibling* to it, differing only in *why* the vars are
///    unpinned (no constraints vs trait dictionaries).
///
/// **Timing-wall resolution (gating decision 3): defer, don't mark.** The slot
/// is allocated at the *determination* point (constructing `Concrete`), not in
/// Pass-1. The interim `NotDetermined` state is honest rather than a flat field
/// that is "sometimes meaningful". On REPL redefinition the prior concrete
/// entry's slot is *reused* (read via [`ModuleEntry::callable_got_slot`]) when
/// the redefinition is again concrete — the use-after-free guard the S82
/// `existing_slot` carry-forward provided is preserved at the determination
/// point. See `design/arch/principles/20-model-invariants-by-representation.md`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum UserFnState {
    /// Pass-1 interim — signature registered, callability not yet determined.
    /// Slot-less by construction (nothing may call an as-yet-undetermined fn).
    NotDetermined,
    /// Determined unconstrained concrete callable. Carries the mandatory
    /// module-local GOT slot through which it is invoked.
    Concrete {
        got_slot: usize,
        /// The callable's ownership summary ([`ModeSummary`]) — written by
        /// typecheck's `pass5_ownership` after body analysis, read by backend
        /// emission and the R3 summary-diff gate. Rides the `Concrete` arm
        /// because the mode vector correlates with callable-ness exactly as
        /// the slot does (templates carry per-INSTANCE summaries on their
        /// mono variants' own `Concrete` entries, never on themselves —
        /// `design/arch/ownership-inference.md` §3.3). `None` ⇒ the
        /// Decision-24 conservative point (absent ⇒ ⊤; old caches
        /// deserialise to today's behaviour).
        #[serde(default)]
        mode_summary: Option<ModeSummary>,
    },
    /// Determined constrained-fn template — slot-less. Only the monomorphised
    /// variants (`Concrete` entries under mangled names) are callable.
    Constrained(Box<ConstrainedFn>),
    /// Determined **generic / parametric** template — slot-less. A def whose
    /// finalised type is **non-concrete** (carries a `Type::Var`) yet has **no
    /// trait constraints** (`id : ∀a. a→a`, or a HOF whose result is `(Box a)`).
    ///
    /// **The S84 generalisation of Principle 20 (user-ratified 2026-06-16).** A
    /// GOT slot is the value-capability of a CONCRETE callable: a def has a slot
    /// ⟺ its type is fully concrete (`Type::is_concrete()`). Both `Constrained`
    /// and `Polymorphic` are slot-less; they differ only in *why* their vars are
    /// unpinned — trait dictionaries (`Constrained`) vs nothing at all
    /// (`Polymorphic`). Reusing `NotDetermined` (which means "Pass-2 has not run")
    /// would conflate interim with determined; reusing `Constrained` would force
    /// a misleading empty-constraint `ConstrainedFn` and collapse the *why*
    /// distinction BC §7 + Principle 20 make explicit. So a third determined,
    /// slot-less state.
    ///
    /// **Slot-less ⇒ a mono SOURCE, EXCLUDED from codegen like `Constrained`
    /// (S84 Phase 4B, FIXME 0381).** Only the monomorphised concrete instances
    /// (`id$Int`, `(Box Int)`) are slotted and callable. The instance-minting pass
    /// (`pass4_monomorphise`) MUST specialise a `Polymorphic` def at every
    /// reachable concrete use — and those concrete instances carry the bodies that
    /// codegen. The template body itself is NEVER a codegen target: emitting it
    /// reached `HeapCategory::classify` with scheme-quantified free vars (the
    /// FIXME-0381 backstop fire), so the eligible-for-codegen filter
    /// ([`SymbolTable::defined_symbols`]) EXCLUDES `Polymorphic`, symmetric with
    /// `Constrained` (whose mono instances likewise carry the bodies). A
    /// `Polymorphic` def that is never instantiated concretely is dead for codegen
    /// and correctly emits no instance.
    ///
    /// Carries a [`ParametricFn`] body — the `DefnVariant` + `Scheme`
    /// `monomorphise_call` needs to re-check the body at concrete types,
    /// mirroring [`ConstrainedFn`] minus the trait-dictionary semantics.
    /// `callable_got_slot()` answers `None` for this arm structurally (same
    /// fall-through as `Constrained` / `NotDetermined`). See
    /// `design/arch/principles/20-model-invariants-by-representation.md`,
    /// `design/typecheck/monomorphisation.md` §2.3, and BC §7.
    Polymorphic(Box<ParametricFn>),
}

// `PrimitiveKind` enum retired (S69 Submission 36).
//
// Prior shape:
//   pub enum PrimitiveKind { Inline, Extern, PlatformEffect { scheduling_class } }
//
// Rationale for retirement:
// - **Inline/Extern variants were vestigial.** No production consumer read
//   them — verified by grep at submission time (only test assertions). Backend
//   dispatches all bundled primitives uniformly via GOT slot per Decision 48;
//   inline-eligibility for arithmetic / vec / sexp ops is encoded per-call-site
//   in `ResolvedCall::BuiltinFn { name }` (set by typecheck), not in a
//   `PrimitiveKind::Inline` discriminator.
// - **PlatformEffect was structurally distinct from bundled-primitive
//   provenance.** Its body location (DLL) is not a sub-classification of
//   "primitive" — it's a sibling provenance class. Promoted to its own
//   `DefKind::PlatformEffect { scheduling_class }` variant; the
//   `scheduling_class` payload (the cross-crate-load-bearing data — consumed
//   by `src/worker.rs` for JIT-symbol-table registration; carried in IO
//   trampoline records per Decision 26) moves with it.
// - **No replacement enum.** The provenance discriminator IS `DefKind`'s
//   variant set; nesting `{ Primitive { primitive_kind: PrimitiveKind } }`
//   was one level deeper than needed.
//
// See `DefKind` rustdoc and `types-audit-s69.md`
// §"Finding S-DRIFT-17" closure for the full settlement rationale.

/// One variant of an overloaded (multi-sig) function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OverloadVariant {
    pub param_types: Vec<Type>,
    pub ret_type: Type,
    pub mangled_name: Symbol,
}

/// A constrained polymorphic function awaiting monomorphisation (Ring 2).
///
/// **Single-variant invariant — one clause, one template.** The `variant:
/// DefnVariant` field carries the body of exactly ONE constrained clause.
/// This holds for multi-sig defns too — multi-sig × constrained-poly is
/// SUPPORTED (S112, user-ruled 2026-07-18): each trait-constrained (or
/// genuinely-polymorphic) clause of a multi-sig defn is registered as its
/// OWN one-variant template under the clause's normalized mangle (e.g.
/// `g$Var`), referenced from the base entry's
/// `OverloadVariant.mangled_name`; dispatch reads the referenced entry's
/// *kind* and routes a `Constrained` clause through per-call-site
/// monomorphisation exactly as a standalone constrained fn (no
/// `OverloadVariant` field addition — the kind lives on the entry,
/// Principle 7). A multi-variant `ConstrainedFn` is never constructed,
/// because the multi-sig decomposition into per-clause `__vN` entries
/// (`cranelisp-typecheck::program::finalize`, the
/// `collect_single_sig_defns` seam) happens BEFORE template detection —
/// `detect_constrained_fns` only ever sees single-clause bodies. See
/// `design/typecheck/monomorphisation.md` §11.4.
///
/// (History: pre-S112 the invariant held on different grounds — an
/// `is_multi_sig` filter made the constrained and multi-sig paths
/// mutually exclusive, rejecting the combination outright. The former
/// "Future-state note" here anticipated a `Vec<DefnVariant>` expansion if
/// the cell became supported; it did NOT materialize — per-clause
/// templates preserve the single-variant shape.)
///
/// **Symmetry with `ModuleEntry::Def.ast`.** S69 Submission 35 narrowed
/// `ModuleEntry::Def.ast: Option<Defn>` → `Option<DefnVariant>` on the
/// observation that the outer `Defn` wrapper carries only metadata that
/// duplicates the parent `Def` (name, docstring, variants, visibility,
/// span — all canonical on the parent `Def`). S35 did not cascade to
/// `ConstrainedFn.defn`, leaving the asymmetry: one of the two sibling
/// sites holding "function body" payload narrowed; the other didn't. S70
/// Phase 3 closes the asymmetry — `ConstrainedFn.variant: DefnVariant`
/// matches `Def.ast: Option<DefnVariant>` in shape and Decision-grounding.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstrainedFn {
    pub variant: DefnVariant,
    pub scheme: Scheme,
}

/// A **generic / parametric** (trait-unconstrained but non-concrete) function
/// awaiting monomorphisation (S84, FIXME 0377).
///
/// The body payload of [`UserFnState::Polymorphic`]. Mirrors [`ConstrainedFn`]'s
/// shape — `variant: DefnVariant` (the single-signature body) + `scheme: Scheme`
/// (the generalised polymorphic type) — because the monomorphisation core
/// (`cranelisp-typecheck::traits::monomorphise_call`) reads exactly those two
/// fields to instantiate at concrete arg-types, re-check the body in the right
/// scope, and register a concrete (slotted) mono instance.
///
/// **Why a distinct struct from `ConstrainedFn` rather than a reuse.** A
/// separate, accurately-named payload keeps the *why*-distinction legible at
/// every reader: `ConstrainedFn` names a trait-bounded body whose vars are
/// pinned per-call by dictionaries; `ParametricFn` names a body whose vars carry
/// **no** trait bounds at all (`scheme.constraints` is empty). Reusing the
/// `Constrained`-named struct as the `Polymorphic` payload would re-conflate the
/// distinction the new variant exists to make explicit (Principle 20; BC §7).
/// The single-variant invariant `ConstrainedFn` documents holds here on the
/// same grounds (S112): a multi-sig defn is decomposed into per-clause
/// `__vN` entries before template detection, and a genuinely-polymorphic
/// clause becomes its OWN one-variant template — `variant` is always the
/// one `DefnVariant`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParametricFn {
    pub variant: DefnVariant,
    pub scheme: Scheme,
}

// --- Macro Support Types ---

/// Information about a single macro clause (for multi-clause defmacro, Ring 3).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MacroClauseInfo {
    pub params: Vec<MacroParam>,
    pub rest_param: Option<Symbol>,
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

/// Stored impl S-expression for deferred processing.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImplSexp {
    pub trait_name: TraitName,
    pub target: TypeName,
    pub sexp: Sexp,
}

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
/// synthetic module at `symbol_tables["platform.<name>"]` whose
/// `SymbolTable.dll` retains the loaded DLL handle (see
/// `design/arch/bounded-contexts.md` §7).
///
/// **Target narrow (Submission 21).** `name: String → name: ModuleName`
/// per the newtype rule (`design/arch/CLAUDE.md` §"String Newtypes"). The
/// retired-shape fields `manifest_path` and `alias` are NOT introduced —
/// `manifest_path` is resolved data (belongs elsewhere); `alias` is
/// excluded by spec §2.2.9 grammar. Source migration in the /dev
/// wave-3 concurrency-cluster brief.
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

/// REPL append-path carrier — one variant per structural Vec field on
/// `SymbolTable`. Consumed by `SymbolTable::append_structural_decl`. Per
/// `repl/spec.md` §15.4: structural forms entered at the REPL prompt extend
/// the corresponding section in authorship order (no dedup, mirroring the
/// file-load discipline). Per Decision 39 (S69 Phase 3 upgrade) — one
/// enum-carrier replaces four parallel `append_*` methods.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum StructuralDeclEntry {
    Import(ImportSpec),
    Export(ExportSpec),
    Platform(PlatformSpec),
    Mod(ModDecl),
}

// `use crate::JitSymbol;` retired (S69 Submission 36 — the `jit_name` field
// on `DefKind::Primitive` is gone; the symbol-table key IS the JIT linker
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
/// Phase 2 review (single-source-of-truth, Principle 7).
pub fn got_data_symbol_name(module_path: &ModuleFullPath) -> String {
    let flat = module_path.as_ref().replace('.', "_");
    format!(
        "__cranelisp_got_{}",
        if flat.is_empty() { "_entry" } else { &flat }
    )
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

/// Maximum chain depth for `Import` follow. Mirrors the
/// typecheck-internal limit (spec §8.6.2). Pathological cycles terminate
/// in `None`.
///
/// `Import` covers both edge kinds (the prior `Reexport` variant retired —
/// see `Import` variant in this enum
/// docstring); chain-follow walks `Import` edges regardless of visibility.
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
    F: FnMut(&Symbol, &ModuleEntry<C>),
{
    if let Some(guard) = modules.get(module_path) {
        for (k, v) in guard.all_symbols() {
            f(k, v);
        }
    }
}

/// Chain-follow `name` starting from `module_path` to its canonical home,
/// returning `(terminal_entry, terminal_module)`. Live-only variant of
/// `TypeCheckEnv::resolve_terminal_entry_and_home` (Decision 45 Pattern B).
///
/// Walks per-symbol `ModuleEntry::Import` bindings one edge at a time
/// along `source.module` references until a canonical entry is reached or
/// the depth limit is hit. `Import` covers both private (`(import …)`-form
/// effect) and public (`(export [foreign-sym])`-form effect) edges (see
/// `Import` variant in this enum
/// docstring); chain-follow proceeds regardless of `visibility` (the prior
/// `Reexport` variant retired).
pub fn resolve_terminal_entry_and_home<C, L>(
    modules: &dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_path: &ModuleFullPath,
    name: &str,
) -> Option<(ModuleEntry<C>, ModuleFullPath)>
where
    C: CodeStore,
    L: LinkerStore,
{
    resolve_terminal_entry_home_and_key(modules, module_path, name)
        .map(|(entry, home, _key)| (entry, home))
}

/// Keyed sibling of [`resolve_terminal_entry_and_home`]: additionally returns
/// the terminal **storage key** — the exact symbol-table key under which the
/// terminal (non-`Import`) entry sits in `home`'s table. For an unaliased name
/// this equals `name`; across a member alias (`v` → `Box.v`), a renamed
/// import/export (`[(foo bar)]`), or any `Import`/`Reexport` chain whose edges
/// rename, it is the LAST followed edge's `source.symbol` — the only place the
/// storage identity is knowable (a `ModuleEntry` does not carry its own key).
/// Feeds `Resolved.storage_key` (resolve.rs) — the FIXME-0620 carrier
/// identity; see `design/arch/backend-keyed-consumer.md` §1.1.
pub(crate) fn resolve_terminal_entry_home_and_key<C, L>(
    modules: &dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_path: &ModuleFullPath,
    name: &str,
) -> Option<(ModuleEntry<C>, ModuleFullPath, Symbol)>
where
    C: CodeStore,
    L: LinkerStore,
{
    let entry = {
        let guard = modules.get(module_path)?;
        guard.get(name).cloned()?
    };
    chain_follow_to_home(modules, entry, module_path.clone(), Symbol::from(name), 0)
}

fn chain_follow_to_home<C, L>(
    modules: &dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>,
    entry: ModuleEntry<C>,
    home: ModuleFullPath,
    key: Symbol,
    depth: usize,
) -> Option<(ModuleEntry<C>, ModuleFullPath, Symbol)>
where
    C: CodeStore,
    L: LinkerStore,
{
    if depth > CHAIN_FOLLOW_DEPTH_LIMIT {
        return None;
    }
    match &entry {
        ModuleEntry::Import { source, .. } => {
            let next_home = source.module.clone();
            let next_key = source.symbol.clone();
            let next_entry = {
                let guard = modules.get(&source.module)?;
                guard.get(next_key.as_ref()).cloned()?
            };
            chain_follow_to_home(modules, next_entry, next_home, next_key, depth + 1)
        }
        _ => Some((entry, home, key)),
    }
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
    match terminal {
        ModuleEntry::TypeDef { info, .. } => Some(info),
        _ => None,
    }
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
    let (terminal, _home) =
        resolve_terminal_entry_and_home(modules, scope, trait_name.as_ref())?;
    match terminal {
        ModuleEntry::TraitDecl { info, .. } => Some(info),
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
        for_each_in_module(modules, scope, |name, entry| match entry {
            ModuleEntry::TraitDecl { .. } | ModuleEntry::Import { .. } => {
                acc.push(TraitName::from(name.as_ref()));
            }
            _ => {}
        });
        acc
    };
    let mut visited_homes: std::collections::HashSet<ModuleFullPath> =
        std::collections::HashSet::new();
    for candidate in candidates {
        let trait_home = match resolve_terminal_entry_and_home(modules, scope, candidate.as_ref()) {
            Some((ModuleEntry::TraitDecl { .. }, home)) => home,
            _ => continue,
        };
        if !visited_homes.insert(trait_home.clone()) {
            continue;
        }
        for_each_in_module(modules, &trait_home, |_key, entry| {
            if let ModuleEntry::TraitImpl { trait_name, impl_type, .. } = entry
                && &impl_type.name == type_name
                && !traits.contains(&trait_name.name)
            {
                traits.push(trait_name.name.clone());
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
/// defining module, then enumerate `ModuleEntry::TraitImpl` entries in
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
        Some((ModuleEntry::TraitDecl { .. }, home)) => home,
        _ => return types,
    };
    for_each_in_module(modules, &trait_home, |_name, entry| {
        if let ModuleEntry::TraitImpl { trait_name: tn, impl_type, .. } = entry
            && &tn.name == trait_name
            && !types.contains(&impl_type.name)
        {
            types.push(impl_type.name.clone());
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
