use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use crate::{
    Defn, DefnVariant, FQSymbol, FQTraitName, FQTypeName, GotTable, ModuleFullPath,
    ModuleName, Scheme, SchedulingClass, Sexp, Span, Symbol, TraitDecl, TraitName, Type,
    TypeDefInfo, TypeName, Visibility,
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
                scheme, visibility, docstring, param_names, kind, callees,
                got_slot, trait_origin, seq, ast, code: _,
            } => ModuleEntry::Def {
                scheme, visibility, docstring, param_names, kind, callees,
                got_slot, trait_origin, seq, ast, code: None,
            },
            ModuleEntry::SpecialForm { scheme, param_names, docstring, description, visibility } => {
                ModuleEntry::SpecialForm { scheme, param_names, docstring, description, visibility }
            }
            ModuleEntry::Import { source, visibility } => ModuleEntry::Import { source, visibility },
            ModuleEntry::TypeDef { info, visibility, constructor_scheme, sexp } => {
                ModuleEntry::TypeDef { info, visibility, constructor_scheme, sexp }
            }
            ModuleEntry::IntrinsicType { ty, visibility } => {
                ModuleEntry::IntrinsicType { ty, visibility }
            }
            ModuleEntry::TraitDecl { decl, visibility, sexp } => {
                ModuleEntry::TraitDecl { decl, visibility, sexp }
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
            ModuleEntry::TraitImpl { trait_name, impl_type, methods, visibility } => {
                ModuleEntry::TraitImpl { trait_name, impl_type, methods, visibility }
            }
            ModuleEntry::Ambiguous { visibility } => ModuleEntry::Ambiguous { visibility },
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
    pub fn allocate_got_slot(&mut self) -> usize {
        let slot = self.next_got_slot;
        self.next_got_slot += 1;
        slot
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
    /// Filter: `ast.is_some() AND kind != Overloaded AND kind != UserFn { constrained_fn: Some(_) }`.
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
    pub fn defined_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry<C>)> {
        self.symbols.iter().filter(|(_, entry)| match entry {
            ModuleEntry::Def { ast: Some(_), kind, .. } => !matches!(
                kind.as_ref(),
                DefKind::Overloaded { .. }
                    | DefKind::UserFn { constrained_fn: Some(_) }
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
        /// Module-local GOT slot index. The slot is the **single source of
        /// truth** for the entry's runtime code address: the GOT is owned by
        /// the module's `SymbolTable.got` and reads/writes go through
        /// `SymbolTable.got.store_slot(slot, ptr)` / `.load_slot(slot)`. No
        /// duplicate `fn_ptr` field exists on `ModuleEntry::Def` (Sprint 66
        /// Wave 0 amendment — the prior `fn_ptr: Option<*const u8>` field was
        /// redundant with the GOT and has been removed).
        ///
        /// A slot is allocated at registration time for any **addressable
        /// callable** — any entry that may be invoked, including via the
        /// operator-as-value path (`(let [f +] (f 1 2))` indirects through the
        /// GOT slot allocated for `+`). This covers user functions, primitives
        /// (when used as values), and platform DLL fns.
        ///
        /// The slot is `None` only for entries that are **never** called or
        /// referenced as values: special forms (`if`, `let`, `defn` — pure
        /// syntax, no runtime address), `Overloaded` base entries (the
        /// mangled variants carry the slots), `TypeDef`/`TraitDecl` and
        /// `Def { kind: DefKind::Macro }` parent entries (no callable
        /// position; per-clause variant Defs carry the slots), and
        /// constrained-fn templates whose mono specialisations carry the
        /// slots.
        ///
        /// Direct-call inlining at known call sites does not require a GOT
        /// lookup, but having a slot does not preclude a direct call — the
        /// slot is for the operator-as-value path.
        #[serde(default)]
        got_slot: Option<usize>,
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
    TypeDef {
        info: TypeDefInfo,
        visibility: Visibility,
        constructor_scheme: Option<Scheme>,
        sexp: Option<Sexp>,
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
    /// Registered by `cranelisp-typecheck::register_primitives` (wave-3
    /// cascade); resolved by `resolve_named` via uniform entry lookup.
    /// Supersedes the retired `Type::from_name` / `Type::type_name`
    /// reverse-lookup bridge (S69 Submission 30 — they made bare `:Int`
    /// always available regardless of imports, contradicting spec §3.1 /
    /// §8.9.1 / §8.11.4).
    IntrinsicType {
        ty: Type,
        visibility: Visibility,
    },
    /// A trait declaration (deftrait, Ring 2).
    TraitDecl {
        decl: TraitDecl,
        visibility: Visibility,
        sexp: Option<Sexp>,
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
    /// **Storage placement (Decision 0045).** `(impl Trait Type method-defns…)`
    /// written in module M lands HERE — in M's symbol table. The trait's
    /// defining module and the type's defining module are NOT mutated by the
    /// impl write; only M is. Discovery from the importer side is via an
    /// import-chain walk (Principle 17): readers searching for an impl walk
    /// the current module's transitive import closure and probe each named
    /// module's table for the synthetic key. This keeps typecheck writes
    /// local (Principle 1) and the canonical store single-sourced
    /// (Principle 7); cluster atomicity (Decision 44) follows because the
    /// staging table for cluster mode is M's table, the same one
    /// `ctx.current_symbol_table_mut()` already targets.
    ///
    /// The associated method bodies are written to M as ordinary
    /// `ModuleEntry::Def` entries with mangled names (e.g.,
    /// `Display.show$Option$Int`); the `methods: Vec<Symbol>` field below
    /// lists the local names so importers can dereference back to the bodies
    /// in M.
    TraitImpl {
        trait_name: FQTraitName,
        impl_type: FQTypeName,
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
    Primitive,
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
    PlatformEffect {
        scheduling_class: SchedulingClass,
    },
    /// A user-defined function.
    UserFn {
        constrained_fn: Option<Box<ConstrainedFn>>,
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
    Constructor {
        type_name: FQTypeName,
        tag: usize,
        field_count: usize,
        #[serde(default)]
        internal: bool,
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
    /// **Introspection lives elsewhere — symmetric across all DefKind
    /// variants (Decision 41 operative).** `source`, `sexp`, `expanded`,
    /// `clif_ir`, `disasm`, `code_size` for ALL Def variants — macros
    /// included — live on the per-`FQSymbol` `Introspection` record in the
    /// integration layer's `SharedState.introspection: Option<DashMap<FQSymbol,
    /// Introspection>>`. The struct is defined at `src/session_v4.rs:566`.
    /// Backend writes those fields directly during `compile_to_module` via
    /// its `introspection: Option<&DashMap<FQSymbol, Introspection>>`
    /// parameter — the `Option`'s `is_some()` IS the mode discriminator
    /// (Decision 38; the same discriminator that gates Introspection
    /// population in JIT mode and skips it in `--link` object mode). See
    /// `design/arch/sequences/exec-flow-compilation.mmd` line 111 (frontend
    /// populates `Introspection { source, sexp, .. }` per-symbol after
    /// expand) and lines 211-221 (backend writes
    /// `Introspection { clif_ir, disasm, code_size, .. }` directly per Decision
    /// 41 — int does no post-processing); `design/arch/sequences/exec-flow-repl.mmd`
    /// line 132 (the `compile_to_module` invocation shape).
    /// `design/arch/bounded-contexts.md` §int places introspection in the
    /// integration layer ("development tooling: tracing, observability,
    /// introspection").
    ///
    /// **Why no `sexp` / `source` field here.** Macros are not architecturally
    /// special for introspection purposes. A future reader looking up
    /// `/source <macro-name>` / `/sexp <macro-name>` / `/expand <macro-name>`
    /// hits the same per-FQSymbol `Introspection` record that backs
    /// `/source <fn-name>` for any other Def — indexed by `FQSymbol`,
    /// mode-gated by the `Option`. Carrying `sexp` / `source` on
    /// `DefKind::Macro` would duplicate the canonical store asymmetrically
    /// (no other `DefKind` variant carries them — `DefKind::UserFn`,
    /// `DefKind::Constructor`, etc. all rely on the integration-layer
    /// `Introspection` map). This variant predates Decision 41's settlement;
    /// the prior `sexp` / `source` fields were pre-D41 shadows carried
    /// forward from S69 Submission 13's narrative and have been removed.
    ///
    /// **Cache-hit residual gap (architectural debt).** `Introspection` is
    /// `#[derive(Default)]` (non-Serde; REPL-only per its own rustdoc) and
    /// lives on `SharedState` per BC §int — when a module loads from cache,
    /// the `Introspection` DashMap is NOT rehydrated. REPL editing of a
    /// cache-loaded module therefore cannot today trigger `.cl` regeneration
    /// for symbols whose Introspection entries are absent. Serializing the
    /// full `Introspection` structure into the cache is NOT the answer
    /// (mixes concerns, bloats the cache, raises invalidation questions);
    /// the future fix is lazy re-read of the backing source file on demand
    /// — re-parse the file region and populate Introspection for the
    /// queried symbols only. Tracked as architectural debt; restoring
    /// D41-violating shadow fields on `DefKind::Macro` (or any other Def
    /// variant) is NOT the answer. See `design/arch/fixmes/` —
    /// "int cache-hit source rehydration on demand" — for the open design
    /// question (WHEN to re-read; HOW to map FQSymbol back to file region).
    ///
    /// **Retired storage.** The prior `ModuleEntry::Macro` sibling variant was
    /// retired in Submission 22 (deleted from source 2026-05-21). The
    /// session-level `MacroEnv` sidecar retires alongside — clause bodies live
    /// in the symbol table under mangled names rather than in a separate
    /// dispatch map. See the `ModuleEntry::Macro retired` comment between the
    /// `Constructor` and `TraitImpl` variants for the cross-reference trail.
    ///
    /// See `facades/frontend.md` §"expand" for the dispatcher behaviour;
    /// `design/arch/bounded-contexts.md` §7 for the bounded-context invariants
    /// (macros are Defs; the clause-walk dispatch story).
    Macro {
        clauses_meta: Vec<MacroClauseInfo>,
    },
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
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstrainedFn {
    pub defn: Defn,
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
    let entry = {
        let guard = modules.get(module_path)?;
        guard.get(name).cloned()?
    };
    chain_follow_to_home(modules, entry, module_path.clone(), 0)
}

fn chain_follow_to_home<C, L>(
    modules: &dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>,
    entry: ModuleEntry<C>,
    home: ModuleFullPath,
    depth: usize,
) -> Option<(ModuleEntry<C>, ModuleFullPath)>
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
            let next_entry = {
                let guard = modules.get(&source.module)?;
                guard.get(source.symbol.as_ref()).cloned()?
            };
            chain_follow_to_home(modules, next_entry, next_home, depth + 1)
        }
        _ => Some((entry, home)),
    }
}

/// Look up a TypeDefInfo by chain-following `name` from `scope` (the access
/// root). Live-only free-fn variant of the relocated method 1
/// (`lookup_type_def_in_module` body). Returns `None` if absent or if the
/// chain terminates on a non-TypeDef entry.
pub fn lookup_type_def_chain<C, L>(
    modules: &dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>,
    scope: &ModuleFullPath,
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

/// Look up a `TraitDecl` by chain-following `name` from `scope`. Live-only
/// free-fn variant of the relocated method 4's underlying primitive
/// (`lookup_trait_decl_in_module` body).
pub fn lookup_trait_decl_chain<C, L>(
    modules: &dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>,
    scope: &ModuleFullPath,
    trait_name: &TraitName,
) -> Option<TraitDecl>
where
    C: CodeStore,
    L: LinkerStore,
{
    let (terminal, _home) =
        resolve_terminal_entry_and_home(modules, scope, trait_name.as_ref())?;
    match terminal {
        ModuleEntry::TraitDecl { decl, .. } => Some(decl),
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
mod tests {
    use super::*;
    use crate::{
        Defn, DefnVariant, Expr, FQSymbol, FQTypeName, ModuleName, Scheme, Span, Symbol, Type,
        TypeDefInfo, TypeName, Visibility,
    };
    use std::collections::HashMap;

    // ---- Sprint 56 Wave 0 §9.5 — defined_symbols filter predicate ----

    /// Build a minimal `ModuleEntry::Def` for test fixtures.
    fn mk_def(
        kind: DefKind,
        ast: Option<DefnVariant>,
    ) -> ModuleEntry {
        ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Int,
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(kind),
            callees: Vec::new(),
            got_slot: None,
            trait_origin: None,
            seq: 0,
            ast,
            code: None,
        }
    }

    /// A trivial `DefnVariant` used as an `ast` payload for tests (S69 Submission 35
    /// narrowed `ModuleEntry::Def.ast` from `Option<Defn>` to `Option<DefnVariant>`).
    /// The `_name` parameter is retained at call sites for readability but no longer
    /// threads into the payload (the entry's own symbol-table key carries the name).
    fn trivial_variant(_name: &str) -> DefnVariant {
        DefnVariant {
            params: vec![],
            body: Expr::IntLit {
                value: 0,
                span: Span::SYNTHETIC,
                inferred_type: Some(Box::new(Type::Int)),
            },
            span: Span::SYNTHETIC,
        }
    }

    /// A trivial one-variant `Defn` used where a full frontend `Defn` is still
    /// required (e.g., `ConstrainedFn { defn: Defn, .. }` continues to carry the
    /// frontend AST node — the typecheck-side decomposition into per-variant
    /// Defs operates on the frontend form).
    fn trivial_defn(name: &str) -> Defn {
        Defn {
            name: Symbol::from(name),
            docstring: None,
            variants: vec![trivial_variant(name)],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }
    }

    // spec: design/typecheck/ast-annotation.md §9.5 — defined_symbols filter predicate
    #[test]
    fn wave0_defined_symbols_filter_is_correct() {
        let mut st = SymbolTable::new(ModuleFullPath::from("user"));

        // (a) Regular UserFn with ast: Some(_) — SHOULD appear.
        st.insert(
            Symbol::from("regular"),
            mk_def(
                DefKind::UserFn { constrained_fn: None },
                Some(trivial_variant("regular")),
            ),
        );

        // (b) Overloaded base with ast: None — MUST NOT appear.
        st.insert(
            Symbol::from("overloaded_base"),
            mk_def(
                DefKind::Overloaded { variants: vec![] },
                None,
            ),
        );

        // (c) UserFn template with constrained_fn: Some(_) — MUST NOT appear,
        // even if ast happens to be Some(_) (§9.5 filter excludes templates by kind).
        let template_cf = ConstrainedFn {
            defn: trivial_defn("template"),
            scheme: Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Int,
            },
        };
        st.insert(
            Symbol::from("template"),
            mk_def(
                DefKind::UserFn { constrained_fn: Some(Box::new(template_cf)) },
                Some(trivial_variant("template")),
            ),
        );

        // (d) TypeDef — not a Def variant at all; MUST NOT appear.
        st.insert(
            Symbol::from("MyType"),
            ModuleEntry::TypeDef {
                info: TypeDefInfo {
                    name: FQTypeName::new(
                        ModuleFullPath::from("user"),
                        TypeName::from("MyType"),
                    ),
                    type_params: vec![],
                    constructors: vec![],
                    docstring: None,
                },
                visibility: Visibility::Public,
                constructor_scheme: None,
                sexp: None,
            },
        );

        // (e) Import — not a Def variant; MUST NOT appear.
        st.insert(
            Symbol::from("imported"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: ModuleFullPath::from("primitives"),
                    symbol: Symbol::from("some-prim"),
                },
                visibility: Visibility::Private,
            },
        );

        // (f) Mangled multi-sig variant with ast: Some(_) — SHOULD appear.
        st.insert(
            Symbol::from("add$Int+Int"),
            mk_def(
                DefKind::UserFn { constrained_fn: None },
                Some(trivial_variant("add$Int+Int")),
            ),
        );

        let names: std::collections::HashSet<String> = st
            .defined_symbols()
            .map(|(s, _)| s.as_ref().to_string())
            .collect();

        assert!(
            names.contains("regular"),
            "regular UserFn with ast: Some(..) must appear; got {:?}",
            names
        );
        assert!(
            names.contains("add$Int+Int"),
            "mangled multi-sig variant with ast: Some(..) must appear; got {:?}",
            names
        );
        assert!(
            !names.contains("overloaded_base"),
            "Overloaded base must NOT appear; got {:?}",
            names
        );
        assert!(
            !names.contains("template"),
            "constrained-fn template must NOT appear; got {:?}",
            names
        );
        assert!(
            !names.contains("MyType"),
            "TypeDef must NOT appear; got {:?}",
            names
        );
        assert!(
            !names.contains("imported"),
            "Import must NOT appear; got {:?}",
            names
        );
    }

    // ---- Sprint 56 Wave 0 §9.8 — GotTable on SymbolTable ----

    // spec: design/typecheck/ast-annotation.md §9.8 — GotTable on SymbolTable: presence + serde roundtrip
    #[test]
    fn wave0_symbol_table_got_present_and_serde_skipped() {
        // Build a SymbolTable and verify `got` is live and addressable.
        let mut st = SymbolTable::new(ModuleFullPath::from("user"));

        // base_ptr() is non-null and stable across reads.
        let p1 = st.got.base_ptr();
        let p2 = st.got.base_ptr();
        assert!(!p1.is_null(), "fresh SymbolTable's GOT base pointer must be non-null");
        assert_eq!(p1, p2, "GOT base_ptr() must be stable across reads");

        // Slot bookkeeping before and after allocation.
        assert_eq!(st.next_got_slot, 0);
        let s0 = st.allocate_got_slot();
        let s1 = st.allocate_got_slot();
        assert_eq!(s0, 0);
        assert_eq!(s1, 1);
        assert_eq!(st.next_got_slot, 2);

        // Allocation does not move the GOT array in memory.
        assert_eq!(st.got.base_ptr(), p1);

        // Insert one entry to prove serde roundtrip preserves symbol data.
        st.insert(
            Symbol::from("entry"),
            mk_def(
                DefKind::UserFn { constrained_fn: None },
                Some(trivial_variant("entry")),
            ),
        );

        // Write a known pointer through the GOT and read it back (round-trip
        // of the runtime pointer must NOT survive serde — verified below).
        let fake_ptr = 0xDEAD_BEEFusize as *const u8;
        st.got.store_slot(s0, fake_ptr);
        assert_eq!(st.got.load_slot(s0), fake_ptr);

        // Serialize and deserialize. The `got` field is `#[serde(skip)]` so it
        // must NOT round-trip the runtime pointer; a fresh null GOT is expected.
        let json = serde_json::to_string(&st).expect("SymbolTable must serialize");
        assert!(
            !json.contains("DEADBEEF") && !json.contains("deadbeef"),
            "serialized form must not contain runtime pointer values: {}",
            json
        );
        let rt: SymbolTable =
            serde_json::from_str(&json).expect("SymbolTable must deserialize");

        // next_got_slot bookkeeping is preserved across the roundtrip.
        assert_eq!(
            rt.next_got_slot, 2,
            "next_got_slot must round-trip via serde"
        );

        // The deserialized GOT exists (#[serde(default)] reconstructs it), has a
        // valid base pointer, and all slots start null (runtime state NOT
        // round-tripped — §9.8.3 Serde semantics).
        let rt_base = rt.got.base_ptr();
        assert!(
            !rt_base.is_null(),
            "deserialized SymbolTable must have a live GOT (non-null base_ptr)"
        );
        assert!(
            rt.got.load_slot(s0).is_null(),
            "deserialized GOT must reset slot pointers to null"
        );
        assert!(
            rt.got.load_slot(s1).is_null(),
            "deserialized GOT must reset every slot to null"
        );

        // Symbol payload (non-runtime) survives the roundtrip.
        assert!(rt.get("entry").is_some(), "entry must round-trip");
    }

    // ---- Sprint 57 Wave 2 Step 1 — Decision 25: `code` field on ModuleEntry::Def ----

    // spec: design/arch/CLAUDE.md Decision 25 / design/typecheck/ast-annotation.md §10.1 —
    //       `code: Option<Code>` present and defaults to None on fresh construction.
    #[test]
    fn module_entry_def_has_code_field_none_by_default() {
        let entry = mk_def(
            DefKind::UserFn { constrained_fn: None },
            Some(trivial_variant("fresh")),
        );
        match entry {
            ModuleEntry::Def { code, .. } => {
                assert!(
                    code.is_none(),
                    "freshly constructed ModuleEntry::Def must have code: None; got {:?}",
                    code
                );
            }
            other => panic!("expected ModuleEntry::Def, got {:?}", other),
        }
    }

    // spec: design/arch/CLAUDE.md Decision 25 + Sprint 58 Wave 3b (Decision 35) —
    //       #[serde(skip)] on the `code: Option<C>` field; runtime-only, never
    //       round-trips through the cache manifest. Wave 3b note: the old
    //       `cranelisp_types::Code` pointer-only struct is gone; the field is
    //       now generic over `C: CodeStore`. This test exercises the `()`
    //       default flavour (typecheck-side view); the integration-layer
    //       enum-flavour serde is exercised in `src/code.rs::tests`.
    #[test]
    fn code_serialise_round_trip_skips_field() {
        let entry: ModuleEntry<()> = ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Int,
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(DefKind::UserFn { constrained_fn: None }),
            callees: Vec::new(),
            got_slot: None,
            trait_origin: None,
            seq: 0,
            ast: Some(trivial_variant("with_code")),
            // `()` flavour — Some/None of the unit type. Serde discipline
            // is the same regardless of `C`.
            code: Some(()),
        };

        let json = serde_json::to_string(&entry).expect("entry must serialize");
        // Field must not appear in the serialised form.
        assert!(
            !json.contains("\"code\""),
            "serialised form must not contain the `code` field (it is #[serde(skip)]): {}",
            json
        );

        let rt: ModuleEntry = serde_json::from_str(&json).expect("entry must deserialize");
        match rt {
            ModuleEntry::Def { code, ast, .. } => {
                assert!(
                    code.is_none(),
                    "deserialised ModuleEntry::Def must have code: None (serde(skip)); got {:?}",
                    code
                );
                assert!(
                    ast.is_some(),
                    "ast must survive the roundtrip so codegen can repopulate code from it"
                );
            }
            other => panic!("expected ModuleEntry::Def, got {:?}", other),
        }
    }

    // ---- Sprint 66 Wave 0 amendment — fn_ptr removed; GOT is the single source of truth ----

    // spec: design/arch/CLAUDE.md Sprint 66 Wave 0 amendment — the prior
    //       `fn_ptr: Option<*const u8>` field on `ModuleEntry::Def` has been
    //       deleted. The runtime address for an addressable callable lives
    //       in the module's GOT slot referenced by `got_slot: Option<usize>`.
    //       A freshly constructed entry has `got_slot: None` (no slot
    //       allocated yet); registration sites that mark an entry callable
    //       allocate a slot via `SymbolTable::allocate_got_slot`.
    #[test]
    fn fresh_module_entry_def_has_no_got_slot() {
        let entry = mk_def(
            DefKind::UserFn { constrained_fn: None },
            Some(trivial_variant("fresh")),
        );
        match entry {
            ModuleEntry::Def { got_slot, .. } => {
                assert!(
                    got_slot.is_none(),
                    "freshly constructed ModuleEntry::Def must have got_slot: None; got {:?}",
                    got_slot
                );
            }
            other => panic!("expected ModuleEntry::Def, got {:?}", other),
        }
    }

    // spec: design/arch/CLAUDE.md Decision 26 (Option B — variant-internal) —
    //       DefKind::PlatformEffect { scheduling_class } carries the class on
    //       the variant itself, not as a sibling field on ModuleEntry::Def.
    //       S69 Submission 36 promoted PlatformEffect from PrimitiveKind
    //       sub-discriminator to its own DefKind variant; the substantive
    //       Decision-26 invariant (variant-internal scheduling_class) is
    //       preserved, restated at the DefKind level.
    #[test]
    fn def_kind_platform_effect_carries_scheduling_class() {
        // Build a platform-effect entry.
        let entry = mk_def(
            DefKind::PlatformEffect {
                scheduling_class: crate::SchedulingClass::Commutative,
            },
            None,
        );

        match entry {
            ModuleEntry::Def { kind, .. } => match *kind {
                DefKind::PlatformEffect { scheduling_class } => {
                    assert_eq!(
                        scheduling_class,
                        crate::SchedulingClass::Commutative,
                        "scheduling_class must be readable from the variant directly"
                    );
                }
                other => panic!(
                    "expected DefKind::PlatformEffect {{ .. }}, got {:?}",
                    other
                ),
            },
            other => panic!("expected ModuleEntry::Def, got {:?}", other),
        }
    }

    // spec: design/arch/CLAUDE.md Sprint 66 Wave 0 amendment — `fn_ptr` field
    //       removed from `ModuleEntry::Def`; `scheduling_class` inside
    //       `DefKind::PlatformEffect` (S69 Submission 36 — promoted from
    //       PrimitiveKind sub-variant) continues to round-trip via serde
    //       (it is static manifest data, not a runtime pointer).
    #[test]
    fn platform_effect_scheduling_class_round_trips() {
        // Explicit `<()>` annotation: `code: None` is polymorphic in `C`, so
        // the inferred `C` would be ambiguous without context.
        let entry: ModuleEntry = ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Int,
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(DefKind::PlatformEffect {
                scheduling_class: crate::SchedulingClass::ResourceSerial,
            }),
            callees: Vec::new(),
            got_slot: None,
            trait_origin: None,
            seq: 0,
            ast: None,
            code: None,
        };

        let json = serde_json::to_string(&entry).expect("entry must serialize");

        // No leaked runtime pointer field of any name.
        assert!(
            !json.contains("fn_ptr"),
            "serialised form must not contain any `fn_ptr` field (the field has been removed entirely): {}",
            json
        );
        // jit_name retired per S69 Submission 36 — symbol-table key IS the
        // JIT linker name uniformly per src/CLAUDE.md §"JIT Symbol Names".
        assert!(
            !json.contains("jit_name"),
            "serialised form must not contain `jit_name` (retired S69 Submission 36): {}",
            json
        );

        let rt: ModuleEntry =
            serde_json::from_str(&json).expect("entry must deserialize");
        match rt {
            ModuleEntry::Def { kind, .. } => {
                // scheduling_class (on the variant) MUST round-trip — it is static
                // manifest data, not a runtime pointer.
                match *kind {
                    DefKind::PlatformEffect { scheduling_class } => {
                        assert_eq!(
                            scheduling_class,
                            crate::SchedulingClass::ResourceSerial,
                            "scheduling_class inside DefKind::PlatformEffect must survive serde roundtrip"
                        );
                    }
                    other => panic!(
                        "expected DefKind::PlatformEffect, got {:?}",
                        other
                    ),
                }
            }
            other => panic!("expected ModuleEntry::Def, got {:?}", other),
        }
    }

    // ---- Sprint 58 Wave 2 Step 5a — Decision 33: structural-decl fields on SymbolTable ----

    /// Build an `ImportSpec` with a unique span (used to verify source-order
    /// preservation in the no-deduplication and ordering tests).
    fn mk_import(module_path: &str, names: &[&str], span_start: u32) -> ImportSpec {
        ImportSpec {
            module_path: ModuleFullPath::from(module_path),
            alias: None,
            names: ImportNames::Specific(names.iter().map(|s| Symbol::from(*s)).collect()),
            span: Span::new(span_start, span_start + 8),
        }
    }

    /// Build an `ExportSpec` with a unique span.
    fn mk_export(module_path: &str, names: &[&str], span_start: u32) -> ExportSpec {
        ExportSpec {
            module_path: ModuleFullPath::from(module_path),
            names: ImportNames::Specific(names.iter().map(|s| Symbol::from(*s)).collect()),
            span: Span::new(span_start, span_start + 8),
        }
    }

    /// Build a `PlatformSpec` with a unique span.
    fn mk_platform(name: &str, span_start: u32) -> PlatformSpec {
        PlatformSpec {
            name: name.to_string(),
            span: Span::new(span_start, span_start + 8),
        }
    }

    /// Build a `ModDecl` with a unique span.
    fn mk_mod(name: &str, visibility: Visibility, span_start: u32) -> ModDecl {
        ModDecl {
            name: ModuleName::from(name),
            visibility,
            inline_body: None,
            span: Span::new(span_start, span_start + 8),
        }
    }

    // spec: design/typecheck/ast-annotation.md §11.3 invariant 1 — source-order preservation
    //       (importing `[a [x]]` then `[b [y]]` records both in declaration order).
    #[test]
    fn symbol_table_imports_preserves_source_order() {
        let mut st = SymbolTable::new(ModuleFullPath::from("user"));

        // Push three imports in source order; spans are strictly increasing.
        st.imports.push(mk_import("a", &["x"], 10));
        st.imports.push(mk_import("b", &["y"], 30));
        st.imports.push(mk_import("c", &["z"], 50));

        assert_eq!(st.imports.len(), 3, "all three imports must be recorded");

        // First-class structural shape: module paths in source order.
        assert_eq!(
            st.imports[0].module_path.as_ref(),
            "a",
            "imports[0] must be the first form pushed"
        );
        assert_eq!(st.imports[1].module_path.as_ref(), "b");
        assert_eq!(st.imports[2].module_path.as_ref(), "c");

        // Span ordering: insertion order matches source order.
        assert!(
            st.imports[0].span.start < st.imports[1].span.start,
            "source-order invariant: imports[0].span.start < imports[1].span.start"
        );
        assert!(
            st.imports[1].span.start < st.imports[2].span.start,
            "source-order invariant: imports[1].span.start < imports[2].span.start"
        );
    }

    // spec: design/typecheck/ast-annotation.md §11.3 invariant 2 — no deduplication
    //       (importing `[a [x y]]` then `[a [x]]` records both; writer MUST NOT dedup).
    #[test]
    fn symbol_table_imports_no_deduplication() {
        let mut st = SymbolTable::new(ModuleFullPath::from("user"));

        // Two imports from the same module, different name lists, distinct spans.
        st.imports.push(mk_import("a", &["x", "y"], 10));
        st.imports.push(mk_import("a", &["x"], 30));

        assert_eq!(
            st.imports.len(),
            2,
            "duplicate imports MUST NOT collapse — both spans needed for resolver diagnostics"
        );

        // Both retain their distinct spans (not collapsed to one).
        assert_eq!(st.imports[0].span.start, 10);
        assert_eq!(st.imports[1].span.start, 30);

        // Same shape applies to structurally-identical pushes (different spans).
        let mut st2 = SymbolTable::new(ModuleFullPath::from("user"));
        st2.imports.push(mk_import("a", &["x"], 10));
        st2.imports.push(mk_import("a", &["x"], 30));
        assert_eq!(
            st2.imports.len(),
            2,
            "structurally-identical imports with distinct spans MUST NOT collapse"
        );
    }

    // spec: design/typecheck/ast-annotation.md §11.3 invariant 3 — no cross-module mixing
    //       (module A's `imports` does not contain B's imports).
    #[test]
    fn symbol_table_no_cross_module_mixing() {
        // Two distinct symbol tables for modules A and B.
        let mut a = SymbolTable::new(ModuleFullPath::from("user.a"));
        let mut b = SymbolTable::new(ModuleFullPath::from("user.b"));

        // Push to A only.
        a.imports.push(mk_import("primitives", &["foo"], 10));
        a.exports.push(mk_export("user.a", &["bar"], 20));
        a.platforms.push(mk_platform("io", 30));
        a.submodules.push(mk_mod("inner", Visibility::Public, 40));

        // B is untouched.
        assert_eq!(b.imports.len(), 0, "B's imports MUST be empty — A's writes do not leak");
        assert_eq!(b.exports.len(), 0, "B's exports MUST be empty");
        assert_eq!(b.platforms.len(), 0, "B's platforms MUST be empty");
        assert_eq!(b.submodules.len(), 0, "B's submodules MUST be empty");

        // Now push to B; A is unchanged.
        b.imports.push(mk_import("primitives", &["baz"], 100));
        assert_eq!(a.imports.len(), 1, "A's imports unchanged after B's write");
        assert_eq!(b.imports.len(), 1);

        // Distinct content across modules.
        assert_ne!(
            a.imports[0].span.start, b.imports[0].span.start,
            "A and B carry independent records"
        );
    }

    // spec: design/typecheck/ast-annotation.md §11.3 invariant 4 — coherence with
    //       ModuleEntry::Import chains is one-way (positive direction):
    //       every imports entry's specific names have a corresponding ModuleEntry::Import.
    //       The reverse is NOT required (implicit prelude injection is /int's call).
    #[test]
    fn symbol_table_imports_have_corresponding_module_entries_positive() {
        let mut st = SymbolTable::new(ModuleFullPath::from("user"));

        // Structural record: import [primitives [foo bar]].
        st.imports.push(mk_import("primitives", &["foo", "bar"], 10));

        // Resolved effects: per-symbol Import entries from the same module.
        st.insert(
            Symbol::from("foo"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: ModuleFullPath::from("primitives"),
                    symbol: Symbol::from("foo"),
                },
                visibility: Visibility::Private,
            },
        );
        st.insert(
            Symbol::from("bar"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: ModuleFullPath::from("primitives"),
                    symbol: Symbol::from("bar"),
                },
                visibility: Visibility::Private,
            },
        );

        // For every name in every Specific imports entry, a corresponding
        // ModuleEntry::Import must exist whose source matches.
        for spec in &st.imports {
            if let ImportNames::Specific(syms) = &spec.names {
                for sym in syms {
                    let entry = st.get(sym.as_ref()).unwrap_or_else(|| {
                        panic!(
                            "import [{} [{}]] has no corresponding ModuleEntry::Import for `{}`",
                            spec.module_path.as_ref(),
                            sym.as_ref(),
                            sym.as_ref()
                        )
                    });
                    match entry {
                        ModuleEntry::Import { source, .. } => {
                            assert_eq!(
                                source.module, spec.module_path,
                                "ModuleEntry::Import source module must match imports entry"
                            );
                            assert_eq!(
                                source.symbol.as_ref(),
                                sym.as_ref(),
                                "ModuleEntry::Import source symbol must match imports entry"
                            );
                        }
                        other => panic!(
                            "expected ModuleEntry::Import for `{}`, got {:?}",
                            sym.as_ref(),
                            other
                        ),
                    }
                }
            }
        }

        // Reverse direction (every ModuleEntry::Import has an imports entry)
        // is /int's Wave 2b design call per §11.3 invariant 4 — NOT enforced
        // here. Implicit prelude injection produces ModuleEntry::Import chains
        // without a structural imports entry, and that may be the chosen
        // behaviour. /int picks based on resolver-diagnostic quality.
    }

    // spec: design/typecheck/ast-annotation.md §11.3 invariant 5 — read-only after
    //       typecheck completes. There is no setter API for these fields; they are
    //       written via direct field access by the worker (per §11.2). This test
    //       is the documented-sense check: SymbolTable exposes no `set_imports`
    //       /`add_import` / `clear_imports`-style mutator method that would imply
    //       a public mutation protocol post-typecheck.
    #[test]
    fn symbol_table_structural_fields_have_no_setter_api() {
        // Compile-time enforcement: this test compiles only because no such
        // methods exist. The presence of any of the following inherent methods
        // would indicate an unintended mutation API and SHOULD break the build:
        //
        //   st.set_imports(...)
        //   st.add_import(...)
        //   st.clear_imports()
        //   st.set_exports(...)
        //   st.set_platforms(...)
        //   st.set_submodules(...)
        //
        // The fields are `pub`, so the worker writes via `st.imports.push(spec)`
        // directly — that is the documented writer protocol (§11.2). No setter
        // method abstraction is introduced because doing so would imply the
        // mutation is part of the type's public API; the actual contract is
        // "writer-only during the form-by-form classification pass, frozen
        // after `tc.check_program(...)` returns" (§11.3 invariant 5), which
        // is enforced at the call-site discipline level (in `/int`'s
        // `src/worker.rs`), not at the type level.
        //
        // Assert nothing additional here — the test passes by compilation.
        // Constructor returns empty fields, confirming the only mutation path
        // is direct field-access by the writer.
        let st = SymbolTable::new(ModuleFullPath::from("user"));
        assert!(st.imports.is_empty(), "fresh SymbolTable starts with empty imports");
        assert!(st.exports.is_empty(), "fresh SymbolTable starts with empty exports");
        assert!(st.platforms.is_empty(), "fresh SymbolTable starts with empty platforms");
        assert!(st.submodules.is_empty(), "fresh SymbolTable starts with empty submodules");
    }

    // spec: design/typecheck/ast-annotation.md §11.3 invariant 6 — serde round-trip
    //       identity. A SymbolTable serialised → deserialised yields structurally
    //       identical fields modulo runtime-only fields (`got`, `code`,
    //       `linker`).
    #[test]
    fn symbol_table_serde_round_trip_with_structural_decls() {
        let mut st = SymbolTable::new(ModuleFullPath::from("user.module"));
        st.schema_version = 1;

        // Populate all four structural fields with non-trivial content.
        st.imports.push(mk_import("primitives", &["foo", "bar"], 10));
        st.imports.push(mk_import("user.helper", &["baz"], 30));

        st.exports.push(mk_export("user.module", &["public_fn"], 50));

        st.platforms.push(mk_platform("stdio", 70));
        st.platforms.push(mk_platform("test_capture", 90));

        st.submodules.push(mk_mod("public_child", Visibility::Public, 110));
        st.submodules.push(mk_mod("private_child", Visibility::Private, 130));

        // Also add one Def entry to confirm symbols round-trip alongside.
        st.insert(
            Symbol::from("entry"),
            mk_def(
                DefKind::UserFn { constrained_fn: None },
                Some(trivial_variant("entry")),
            ),
        );

        // Round-trip via serde-JSON.
        let json = serde_json::to_string(&st).expect("SymbolTable must serialize");
        let rt: SymbolTable =
            serde_json::from_str(&json).expect("SymbolTable must deserialize");

        // Structural identity on the four new fields.
        assert_eq!(rt.imports.len(), 2, "imports.len() must round-trip");
        assert_eq!(rt.imports[0].module_path.as_ref(), "primitives");
        assert_eq!(rt.imports[0].span.start, 10);
        assert_eq!(rt.imports[1].module_path.as_ref(), "user.helper");
        assert_eq!(rt.imports[1].span.start, 30);

        assert_eq!(rt.exports.len(), 1, "exports.len() must round-trip");
        assert_eq!(rt.exports[0].module_path.as_ref(), "user.module");
        assert_eq!(rt.exports[0].span.start, 50);

        assert_eq!(rt.platforms.len(), 2, "platforms.len() must round-trip");
        assert_eq!(rt.platforms[0].name, "stdio");
        assert_eq!(rt.platforms[1].name, "test_capture");
        assert_eq!(rt.platforms[0].span.start, 70);

        assert_eq!(rt.submodules.len(), 2, "submodules.len() must round-trip");
        assert_eq!(rt.submodules[0].name.as_ref(), "public_child");
        assert_eq!(
            rt.submodules[0].visibility,
            Visibility::Public,
            "visibility must round-trip (Public)"
        );
        assert_eq!(rt.submodules[1].name.as_ref(), "private_child");
        assert_eq!(
            rt.submodules[1].visibility,
            Visibility::Private,
            "visibility must round-trip (Private)"
        );

        // Schema version round-trips.
        assert_eq!(rt.schema_version, 1, "schema_version must round-trip");

        // Symbols round-trip (sanity check that adding new fields didn't
        // disturb the existing serde shape).
        assert!(rt.get("entry").is_some(), "Def entry must round-trip");

        // Source ordering invariant survives the round-trip.
        assert!(
            rt.imports[0].span.start < rt.imports[1].span.start,
            "source-order invariant survives serde round-trip"
        );
    }

    // spec: design/arch/CLAUDE.md Decision 34 — `schema_version` defaults to 0
    //       when deserialising from a Sprint-57-era cache (which lacks the field).
    //       The cache loader compares the deserialised value to the current
    //       `CACHE_SCHEMA_VERSION` constant (owned by /backend) and rejects
    //       mismatches as cache-stale.
    #[test]
    fn symbol_table_schema_version_defaults_to_zero_for_legacy_cache() {
        // Synthesise a JSON shape that matches a Sprint-57-era serialised
        // SymbolTable: lacks `schema_version`. The four structural-decl fields
        // also lack values (Sprint 57 had no `imports`/`exports`/`platforms`/
        // `submodules` on SymbolTable), and they too carry `#[serde(default)]`
        // so the legacy cache deserialises cleanly to empty Vecs and the
        // schema_version mismatch is surfaced to the loader.
        //
        // This is the exact shape Decision 34 promises will trigger
        // version-mismatch handling: deserialise succeeds with `schema_version
        // = 0`, the loader compares to `CACHE_SCHEMA_VERSION = 1` (owned by
        // /backend), and the cache entry is rejected as stale (same path as
        // dep-hash mismatch).
        let legacy_json = r#"{
            "path": "user",
            "symbols": {},
            "next_got_slot": 0
        }"#;

        let rt: SymbolTable = serde_json::from_str(legacy_json)
            .expect("legacy Sprint-57-era SymbolTable JSON must deserialize cleanly");

        assert_eq!(
            rt.schema_version, 0,
            "schema_version MUST default to 0 for legacy caches lacking the field — \
             cache loader uses this to detect Sprint-57-era caches and reject as stale"
        );

        // The four structural-decl fields default to empty when absent — also
        // load-bearing for legacy-cache compatibility (the cache loader
        // version-checks BEFORE attempting to use these fields, but the
        // deserialise step must succeed first).
        assert!(rt.imports.is_empty(), "missing `imports` field defaults to empty Vec");
        assert!(rt.exports.is_empty(), "missing `exports` field defaults to empty Vec");
        assert!(rt.platforms.is_empty(), "missing `platforms` field defaults to empty Vec");
        assert!(rt.submodules.is_empty(), "missing `submodules` field defaults to empty Vec");
    }

    // spec: design/typecheck/ast-annotation.md §11.3 invariant 2 — no deduplication
    //       (same shape applies to exports as to imports).
    #[test]
    fn symbol_table_exports_no_deduplication() {
        let mut st = SymbolTable::new(ModuleFullPath::from("user"));

        st.exports.push(mk_export("user", &["foo"], 10));
        st.exports.push(mk_export("user", &["foo"], 30));

        assert_eq!(
            st.exports.len(),
            2,
            "duplicate exports MUST NOT collapse (parallel to imports invariant)"
        );
        assert_eq!(st.exports[0].span.start, 10);
        assert_eq!(st.exports[1].span.start, 30);
    }

    // ---- Sprint 58 Wave 3a — Decision 32: CodeStore / LinkerStore marker traits ----

    // spec: design/typecheck/ast-annotation.md §12.1 + Decision 32 —
    //       SymbolTable<C: CodeStore = (), L: LinkerStore = ()> defaults
    //       resolve to SymbolTable<(), ()> when constructed without args.
    //       Confirms the "default-(): propagation" invariant: typecheck-side
    //       call sites that name `SymbolTable` (no args) get the unit
    //       parameterisation and the `code: Option<()>` / `linker: Option<()>`
    //       shape compiles cleanly.
    #[test]
    fn symbol_table_default_generics_resolve_to_unit() {
        // Construct via the inherent `SymbolTable<(), ()>::new(...)` path
        // (the only one defined; see the inherent-impl rationale on
        // `impl SymbolTable<(), ()>` for why `::new` lives there rather
        // than on the generic impl).
        let st = SymbolTable::new(ModuleFullPath::from("user"));

        // Annotate explicitly to assert the inferred parameterisation is
        // <(), ()>. The `:` binds a fresh local with the spelled type;
        // the assignment from `st` would fail to compile if the parameters
        // were anything other than <(), ()>.
        let _typed: SymbolTable<(), ()> = st;

        // The four Vec<…> fields and the linker / schema_version fields
        // are all populated with their defaults by `::new`. The `linker`
        // field is `Option<()>` (a meaningless tag from typecheck's POV);
        // confirm it starts as None.
        let st: SymbolTable<(), ()> = SymbolTable::new(ModuleFullPath::from("user"));
        assert!(
            st.linker.is_none(),
            "fresh SymbolTable<(), ()> must have linker: None (Wave 3a default)"
        );
        // Sanity: the structural-decl Vec<…> fields are empty too (Step 5a
        // invariant; reasserted here to prove parameterisation didn't
        // disturb the existing field set).
        assert!(st.imports.is_empty());
        assert!(st.exports.is_empty());
        assert!(st.platforms.is_empty());
        assert!(st.submodules.is_empty());
        // `code` field shape exists on every Def entry; it is Option<()>
        // for typecheck-side fixtures and would be Option<Code> for
        // integration-layer fixtures (Wave 3b instantiates `C = Code`).
    }

    // spec: design/typecheck/ast-annotation.md §12.2 + Decision 32 —
    //       The blanket `impl<T: Send + Sync + 'static> CodeStore for T` /
    //       `impl<T: Send + Sync + 'static> LinkerStore for T` makes both
    //       traits trivially satisfied by `()` (zero-sized, Send + Sync +
    //       'static) and by other common types the integration layer
    //       might choose. Confirms the "no per-call-site impl line"
    //       ergonomic property of the empty-marker design (Decision 32
    //       rationale).
    #[test]
    fn code_store_and_linker_store_blanket_impl_holds() {
        // Compile-time check: the function below requires its parameter
        // type to satisfy `CodeStore`. The fact that this compiles is the
        // assertion — calling it with `()` and several other plausible
        // integration-layer concrete types proves the blanket impl
        // applies.
        fn _requires_code_store<T: CodeStore>() {}
        fn _requires_linker_store<T: LinkerStore>() {}

        _requires_code_store::<()>();
        _requires_linker_store::<()>();

        // Common Arc-wrapped shapes that the integration layer may use
        // for `C` (per Decision 35: `Arc<Jit>`-or-`Code`-enum) and `L`
        // (per Decision 35: `Arc<Linker>` if `L` is reactivated). Use
        // `Arc<()>` and `Arc<u64>` as stand-ins for the integration
        // layer's concrete shapes — they must satisfy the bound for the
        // Wave 3b instantiation to compile. `i64` exercises the simplest
        // primitive case (the §G.12 unit test for `module_entry_def_code_field_is_optional_c`
        // uses `i64` synthetically).
        _requires_code_store::<std::sync::Arc<()>>();
        _requires_code_store::<std::sync::Arc<u64>>();
        _requires_code_store::<i64>();
        _requires_code_store::<u64>();
        _requires_linker_store::<std::sync::Arc<()>>();
        _requires_linker_store::<std::sync::Arc<u64>>();

        // (Sprint 58 Wave 3b: the previous `_requires_code_store::<crate::Code>()`
        // assertion targeted the now-dissolved `cranelisp_types::Code` struct.
        // The replacement test lives in `src/code.rs::tests` —
        // `session_symbol_table_concrete_type_choice` — and asserts
        // `_requires_code_store::<src::code::Code>()` against the integration
        // layer's enum, the actual concrete type for `C`. This module's
        // tests stay strictly within `cranelisp-types`'s scope and exercise
        // only synthetic / `()`-flavoured shapes.)
    }

    // spec: design/typecheck/ast-annotation.md §12.4 + Decision 32 + §G.12
    //       (`module_entry_def_code_field_is_optional_c`) —
    //       `ModuleEntry<C>` parameterises the `code: Option<C>` field over
    //       the `C: CodeStore` parameter. With a synthetic `C = i64`,
    //       constructing `Def { code: Some(42i64), .. }` must compile and
    //       round-trip via serde with `code` skipped (the serialised JSON
    //       contains no `code` field; deserialise produces `code: None`
    //       regardless of the source `C`).
    #[test]
    fn module_entry_def_code_field_is_optional_c() {
        // Synthetic `C = i64`: any `Send + Sync + 'static` type satisfies
        // CodeStore via the blanket impl. The point of this test is to
        // exercise the `Option<C>` parameterisation with a `C` that is
        // NOT `Code` and NOT `()` — proving the field is genuinely
        // generic over the parameter, not specialised to either default.
        let entry: ModuleEntry<i64> = ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Int,
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(DefKind::UserFn { constrained_fn: None }),
            callees: Vec::new(),
            got_slot: None,
            trait_origin: None,
            seq: 0,
            ast: Some(trivial_variant("synthetic")),
            code: Some(42i64),
        };

        // The `code` field carries the synthetic `C = i64` value.
        match &entry {
            ModuleEntry::Def { code, .. } => {
                assert_eq!(*code, Some(42i64), "code field must hold the constructed Some(42i64)");
            }
            other => panic!("expected ModuleEntry::Def, got {:?}", other),
        }

        // Serde discipline: `code` is `#[serde(skip)]`, so the serialised
        // shape MUST NOT contain a `code` field, and the deserialised
        // entry MUST have `code: None` regardless of the source `C`. Use
        // the `()` flavour for the deserialise target (typecheck-side
        // view) to confirm cross-flavour serde compatibility — the
        // serialised shape is identical because `code` never appears in
        // the JSON.
        let json = serde_json::to_string(&entry).expect("ModuleEntry<i64> must serialize");
        assert!(
            !json.contains("\"code\""),
            "serialised form must not contain the `code` field (it is #[serde(skip)]): {}",
            json
        );

        let rt: ModuleEntry<()> = serde_json::from_str(&json)
            .expect("ModuleEntry<()> must deserialize from ModuleEntry<i64>'s JSON");
        match rt {
            ModuleEntry::Def { code, ast, .. } => {
                // The deserialised `code` is `None::<()>` — the source
                // `Some(42i64)` did not survive (correctly) because the
                // field is skipped.
                assert!(
                    code.is_none(),
                    "deserialised ModuleEntry<()>::Def must have code: None (serde(skip)); got {:?}",
                    code
                );
                // ast survives the round-trip — only the `code` field is
                // skipped (the prior `fn_ptr` field has been removed entirely
                // per the Sprint 66 Wave 0 amendment).
                assert!(ast.is_some(), "ast must survive the round-trip");
            }
            other => panic!("expected ModuleEntry::Def, got {:?}", other),
        }
    }
}
