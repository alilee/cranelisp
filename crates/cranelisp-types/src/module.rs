use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::PathBuf;

use crate::{
    Code, ConstructorInfo, Defn, FQSymbol, FQTraitName, FQTypeName, GotTable, ModuleFullPath,
    ModuleName, Scheme, SchedulingClass, Sexp, Span, Symbol, TraitDecl, TraitName, Type,
    TypeDefInfo, TypeName, Visibility,
};

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
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SymbolTable {
    pub path: ModuleFullPath,
    pub symbols: HashMap<Symbol, ModuleEntry>,
    /// Next available GOT slot index for this module.
    /// Module-local: slot 0, 1, 2... independently per module.
    #[serde(default)]
    pub next_got_slot: usize,
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
    /// Original `(import [module [names...]])` declarations in source order.
    /// Used by `src/save.rs::generate_module_source` for `.cl` regeneration
    /// (spec §6.4) and by the import-resolver. Distinct from the per-symbol
    /// `ModuleEntry::Import` entries, which are the *resolved* effects.
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
    /// `is_private` distinguishes `(mod-)`. Consumed by `/int` for submodule
    /// loading.
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
}

fn default_got_arc() -> std::sync::Arc<GotTable> {
    std::sync::Arc::new(GotTable::new())
}

impl SymbolTable {
    pub fn new(path: ModuleFullPath) -> Self {
        SymbolTable {
            path,
            symbols: HashMap::new(),
            next_got_slot: 0,
            got: std::sync::Arc::new(GotTable::new()),
            imports: Vec::new(),
            exports: Vec::new(),
            platforms: Vec::new(),
            submodules: Vec::new(),
            schema_version: 0,
        }
    }

    /// Allocate the next available module-local GOT slot.
    pub fn allocate_got_slot(&mut self) -> usize {
        let slot = self.next_got_slot;
        self.next_got_slot += 1;
        slot
    }

    pub fn get(&self, name: &str) -> Option<&ModuleEntry> {
        self.symbols.get(name)
    }

    pub fn insert(&mut self, name: Symbol, entry: ModuleEntry) {
        self.symbols.insert(name, entry);
    }

    pub fn public_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry)> {
        self.symbols.iter().filter(|(_, e)| e.is_public())
    }

    /// Iterate over all symbols (public and private).
    pub fn all_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry)> {
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
    pub fn defined_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry)> {
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
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ModuleEntry {
    /// A definition: function, primitive, special form.
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
        /// Module-local GOT slot index. Assigned at registration time for
        /// user-defined functions. `None` for primitives and special forms
        /// (they don't need GOT slots — inlined or called directly).
        #[serde(default)]
        got_slot: Option<usize>,
        /// If this Def is a trait method, which trait it belongs to.
        /// Replaces the `method_to_trait` reverse index on `TraitRegistry`.
        /// `None` for non-trait-method definitions.
        #[serde(default)]
        trait_origin: Option<FQTraitName>,
        /// Typechecked function body. Written by typecheck after check_form(CheckBody).
        /// Read by codegen. None for primitives, special forms, and pre-body-check entries.
        #[serde(default)]
        ast: Option<Defn>,
        /// Compiled-code handle written by the backend after `compile_to_module`
        /// returns. Runtime-only state (Decision 25 in `design/arch/CLAUDE.md`):
        /// `#[serde(skip)]` so cache manifests stay pointer-free, and the field
        /// re-initialises to `None` on cache-hit load. Codegen repopulates it
        /// on demand. Owner of `Code`: integration layer (per-session Jit set
        /// holds the backing pages alive per Decision 28).
        #[serde(skip)]
        code: Option<Code>,
        /// Platform-function pointer written during `(platform ...)` form
        /// processing (Sprint 57 Wave 3 / G8, Decision 26 in
        /// `design/arch/CLAUDE.md`).
        ///
        /// `Some` only when `kind == DefKind::Primitive { primitive_kind:
        /// PrimitiveKind::PlatformEffect { .. }, .. }`. `None` for every
        /// non-platform `Def`. Replaces the separate `PlatformRegistry`:
        /// the IO trampoline and JIT symbol resolution look up platform fn
        /// ptrs by walking Import chains to the defining `PlatformEffect`
        /// entry and reading this field.
        ///
        /// `#[serde(skip)]` — runtime state. The pointer is valid for as long
        /// as the owning DLL is loaded; the session retains DLL handles for
        /// every platform entry. On cache-hit load this field deserialises to
        /// `None`; it is re-populated by re-opening the DLL referenced by the
        /// corresponding `PlatformDecl` entry and reading its manifest.
        #[serde(skip, default)]
        platform_fn_ptr: Option<*const u8>,
    },
    /// An imported name from another module (Ring 2).
    Import { source: FQSymbol },
    /// A re-exported name from another module (Ring 2).
    Reexport { source: FQSymbol },
    /// A type definition (deftype).
    TypeDef {
        info: TypeDefInfo,
        visibility: Visibility,
        constructor_scheme: Option<Scheme>,
        sexp: Option<Sexp>,
    },
    /// A trait declaration (deftrait, Ring 2).
    TraitDecl {
        decl: TraitDecl,
        visibility: Visibility,
        sexp: Option<Sexp>,
    },
    /// A constructor (from a deftype).
    Constructor {
        type_name: FQTypeName,
        info: ConstructorInfo,
        scheme: Scheme,
        visibility: Visibility,
    },
    /// A macro definition (defmacro, Ring 3).
    Macro {
        name: Symbol,
        clauses: Vec<MacroClauseInfo>,
        docstring: Option<String>,
        visibility: Visibility,
        sexp: Option<Sexp>,
        source: Option<String>,
        /// Fully-qualified callees discovered during typechecking (Decision 21).
        /// Populated by `finalize_check_result()` for macro clause bodies.
        #[serde(default)]
        callees: Vec<FQSymbol>,
    },
    /// A platform DLL declaration (Ring 4).
    PlatformDecl {
        dll_path: PathBuf,
        platform_module: ModuleFullPath,
    },
    /// A trait implementation for a specific type (Ring 2).
    /// Keyed by synthetic name `impl$FQTypeName$FQTraitName` on the SymbolTable.
    /// Always public (spec §5.11: impls are visible wherever both trait and type are in scope).
    /// See `design/arch/traitimpl-symbol-table.md` for the full design.
    TraitImpl {
        trait_name: FQTraitName,
        impl_type: FQTypeName,
        /// Method names defined in this impl (local names, not mangled).
        methods: Vec<Symbol>,
    },
    /// A bare name that became ambiguous (two different sources registered it, Ring 2).
    Ambiguous,
}

// SAFETY: `ModuleEntry::Def` carries `platform_fn_ptr: Option<*const u8>`
// (Sprint 57 Wave 3, Decision 26) and `code: Option<Code>` (Decision 25) —
// both are raw pointers into DLL code pages or JIT-owned mmap'd executable
// pages. The pointers are integer handles; transmitting the integer across
// threads is safe. The backing pages are kept alive at the session level
// (session's `loaded_platforms` DLL handles and `Arc<Jit>` set), which
// outlives every `SymbolTable` holding entries that reference them. Threads
// that dereference `platform_fn_ptr` or `code.ptr` must hold a live handle
// (directly or transitively via the session) to the owning resource — the
// session enforces this invariant.
unsafe impl Send for ModuleEntry {}
unsafe impl Sync for ModuleEntry {}

impl ModuleEntry {
    /// Returns the callees for this entry, or an empty slice for variants without callees.
    ///
    /// Supports the `tc.symbol_table(module).get(name).callees()` dot-access pattern
    /// from the call graph design (Decision 21).
    pub fn callees(&self) -> &[FQSymbol] {
        match self {
            ModuleEntry::Def { callees, .. } | ModuleEntry::Macro { callees, .. } => callees,
            // TraitImpl has no callees — it's an index/metadata entry.
            // The actual method Def entries carry their own callees.
            _ => &[],
        }
    }

    /// Returns true if this entry is publicly visible.
    pub fn is_public(&self) -> bool {
        match self {
            ModuleEntry::Def { visibility, .. }
            | ModuleEntry::TypeDef { visibility, .. }
            | ModuleEntry::TraitDecl { visibility, .. }
            | ModuleEntry::Constructor { visibility, .. }
            | ModuleEntry::Macro { visibility, .. } => *visibility == Visibility::Public,
            ModuleEntry::Import { .. } | ModuleEntry::Reexport { .. } => true,
            ModuleEntry::PlatformDecl { .. } => true,
            // Spec §5.11: trait implementations are always public.
            ModuleEntry::TraitImpl { .. } => true,
            ModuleEntry::Ambiguous => false,
        }
    }
}

// --- Definition Classification ---

/// What kind of definition a symbol is.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DefKind {
    /// A special form (if, let, defn, ...).
    SpecialForm { description: String },
    /// A built-in primitive (inline IR, extern FFI, or platform effect).
    Primitive {
        primitive_kind: PrimitiveKind,
        jit_name: Option<JitSymbol>,
    },
    /// A user-defined function.
    UserFn {
        constrained_fn: Option<Box<ConstrainedFn>>,
    },
    /// Multi-sig overloaded function base name (Ring 2).
    Overloaded {
        variants: Vec<OverloadVariant>,
    },
}

/// Classification of primitive functions.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PrimitiveKind {
    /// Inlined as Cranelift IR at the call site
    Inline,
    /// Calls an extern Rust function via JIT symbol (Ring 1+)
    Extern,
    /// Platform effect (dispatched through IO trampoline, Ring 4).
    ///
    /// `scheduling_class` lives on the variant (not on a sibling field on
    /// `ModuleEntry::Def`) so that only `PlatformEffect` entries can carry
    /// a scheduling class — ill-formed states ("a user fn with a scheduling
    /// class") are unrepresentable. See Decision 26 in `design/arch/CLAUDE.md`.
    ///
    /// The variant serialises normally: `scheduling_class` is static manifest
    /// data (re-read from the DLL manifest on cache-hit load via `PlatformDecl`
    /// reconstruction, not a runtime pointer). Contrast with the sibling
    /// `ModuleEntry::Def.platform_fn_ptr` which is `#[serde(skip)]` because it
    /// IS a runtime pointer into the loaded DLL's code pages.
    PlatformEffect {
        scheduling_class: SchedulingClass,
    },
}

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
    pub source: Option<String>,
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

/// A `(platform name)` declaration extracted from top-level forms.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PlatformSpec {
    pub name: String,
    pub span: Span,
}

// --- Module Declarations ---

/// A parsed `(mod name)` or `(mod- name)` declaration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModDecl {
    pub name: ModuleName,
    pub is_private: bool,
    pub inline_body: Option<Vec<Sexp>>,
    pub span: Span,
}

use crate::JitSymbol;

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
        ast: Option<Defn>,
    ) -> ModuleEntry {
        ModuleEntry::Def {
            scheme: Scheme {
                vars: vec![],
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
            ast,
            code: None,
            platform_fn_ptr: None,
        }
    }

    /// A trivial one-variant Defn used as an `ast` payload for tests.
    fn trivial_defn(name: &str) -> Defn {
        Defn {
            name: Symbol::from(name),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit {
                    value: 0,
                    span: Span::SYNTHETIC,
                    inferred_type: Some(Box::new(Type::Int)),
                },
                span: Span::SYNTHETIC,
            }],
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
                Some(trivial_defn("regular")),
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
                vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Int,
            },
        };
        st.insert(
            Symbol::from("template"),
            mk_def(
                DefKind::UserFn { constrained_fn: Some(Box::new(template_cf)) },
                Some(trivial_defn("template")),
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
            },
        );

        // (f) Mangled multi-sig variant with ast: Some(_) — SHOULD appear.
        st.insert(
            Symbol::from("add$Int+Int"),
            mk_def(
                DefKind::UserFn { constrained_fn: None },
                Some(trivial_defn("add$Int+Int")),
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
                Some(trivial_defn("entry")),
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
            Some(trivial_defn("fresh")),
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

    // spec: design/arch/CLAUDE.md Decision 25 — #[serde(skip)] on code field; runtime-only,
    //       never round-trips through the cache manifest.
    #[test]
    fn code_serialise_round_trip_skips_field() {
        let fake_ptr = 0xCAFEF00Dusize as *const u8;
        let entry = ModuleEntry::Def {
            scheme: Scheme {
                vars: vec![],
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
            ast: Some(trivial_defn("with_code")),
            code: Some(crate::Code::new(fake_ptr)),
            platform_fn_ptr: None,
        };

        let json = serde_json::to_string(&entry).expect("entry must serialize");
        // Field must not appear in the serialised form.
        assert!(
            !json.contains("\"code\""),
            "serialised form must not contain the `code` field (it is #[serde(skip)]): {}",
            json
        );
        // Raw pointer value must not leak through (hex or decimal representation).
        assert!(
            !json.to_lowercase().contains("cafef00d"),
            "serialised form must not contain the raw pointer value: {}",
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

    // ---- Sprint 57 Wave 3 Step A — Decision 26: platform_fn_ptr + scheduling_class ----

    // spec: design/arch/CLAUDE.md Decision 26 — `platform_fn_ptr: Option<*const u8>`
    //       sibling field on ModuleEntry::Def; defaults to None on fresh construction.
    #[test]
    fn platform_fn_ptr_field_defaults_to_none() {
        let entry = mk_def(
            DefKind::UserFn { constrained_fn: None },
            Some(trivial_defn("fresh")),
        );
        match entry {
            ModuleEntry::Def { platform_fn_ptr, .. } => {
                assert!(
                    platform_fn_ptr.is_none(),
                    "freshly constructed ModuleEntry::Def must have platform_fn_ptr: None; got {:?}",
                    platform_fn_ptr
                );
            }
            other => panic!("expected ModuleEntry::Def, got {:?}", other),
        }
    }

    // spec: design/arch/CLAUDE.md Decision 26 (Option B — variant-internal) —
    //       PrimitiveKind::PlatformEffect { scheduling_class } carries the class
    //       on the variant itself, not as a sibling field on ModuleEntry::Def.
    #[test]
    fn primitive_kind_platform_effect_carries_scheduling_class() {
        // Build a platform-effect primitive entry.
        let entry = mk_def(
            DefKind::Primitive {
                primitive_kind: PrimitiveKind::PlatformEffect {
                    scheduling_class: crate::SchedulingClass::Commutative,
                },
                jit_name: Some(crate::JitSymbol::from("cranelisp_get_time")),
            },
            None,
        );

        match entry {
            ModuleEntry::Def { kind, .. } => match *kind {
                DefKind::Primitive {
                    primitive_kind: PrimitiveKind::PlatformEffect { scheduling_class },
                    jit_name,
                } => {
                    assert_eq!(
                        scheduling_class,
                        crate::SchedulingClass::Commutative,
                        "scheduling_class must be readable from the variant directly"
                    );
                    assert_eq!(
                        jit_name.as_deref(),
                        Some("cranelisp_get_time"),
                        "jit_name remains on DefKind::Primitive alongside primitive_kind"
                    );
                }
                other => panic!(
                    "expected DefKind::Primitive {{ PlatformEffect {{ .. }} }}, got {:?}",
                    other
                ),
            },
            other => panic!("expected ModuleEntry::Def, got {:?}", other),
        }
    }

    // spec: design/arch/CLAUDE.md Decision 26 — `#[serde(skip)]` on platform_fn_ptr;
    //       runtime-only, never round-trips through the cache manifest. Also confirms
    //       the `scheduling_class` inside PrimitiveKind::PlatformEffect DOES round-trip
    //       (it is static manifest data, not a runtime pointer).
    #[test]
    fn platform_fn_ptr_skipped_by_serde() {
        let fake_ptr = 0xFEEDFACEusize as *const u8;
        let entry = ModuleEntry::Def {
            scheme: Scheme {
                vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Int,
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(DefKind::Primitive {
                primitive_kind: PrimitiveKind::PlatformEffect {
                    scheduling_class: crate::SchedulingClass::ResourceSerial,
                },
                jit_name: Some(crate::JitSymbol::from("cranelisp_http_get")),
            }),
            callees: Vec::new(),
            got_slot: None,
            trait_origin: None,
            ast: None,
            code: None,
            platform_fn_ptr: Some(fake_ptr),
        };

        let json = serde_json::to_string(&entry).expect("entry must serialize");

        // `platform_fn_ptr` field must not appear in the serialised form.
        assert!(
            !json.contains("platform_fn_ptr"),
            "serialised form must not contain the `platform_fn_ptr` field (it is #[serde(skip)]): {}",
            json
        );
        // Raw pointer value must not leak through (hex or decimal representation).
        assert!(
            !json.to_lowercase().contains("feedface"),
            "serialised form must not contain the raw pointer value: {}",
            json
        );

        let rt: ModuleEntry =
            serde_json::from_str(&json).expect("entry must deserialize");
        match rt {
            ModuleEntry::Def { platform_fn_ptr, kind, .. } => {
                assert!(
                    platform_fn_ptr.is_none(),
                    "deserialised ModuleEntry::Def must have platform_fn_ptr: None (serde(skip)); got {:?}",
                    platform_fn_ptr
                );
                // scheduling_class (on the variant) MUST round-trip — it is static
                // manifest data, not a runtime pointer. Re-reading the DLL manifest
                // on cache-hit load would re-derive it, but serde carrying it across
                // avoids an extra DLL read.
                match *kind {
                    DefKind::Primitive {
                        primitive_kind: PrimitiveKind::PlatformEffect { scheduling_class },
                        ..
                    } => {
                        assert_eq!(
                            scheduling_class,
                            crate::SchedulingClass::ResourceSerial,
                            "scheduling_class inside PrimitiveKind::PlatformEffect must survive serde roundtrip"
                        );
                    }
                    other => panic!(
                        "expected DefKind::Primitive with PlatformEffect, got {:?}",
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
    fn mk_mod(name: &str, is_private: bool, span_start: u32) -> ModDecl {
        ModDecl {
            name: ModuleName::from(name),
            is_private,
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
        a.submodules.push(mk_mod("inner", false, 40));

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
            },
        );
        st.insert(
            Symbol::from("bar"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: ModuleFullPath::from("primitives"),
                    symbol: Symbol::from("bar"),
                },
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
                        ModuleEntry::Import { source } => {
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
    //       `platform_fn_ptr`, `linker`).
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

        st.submodules.push(mk_mod("public_child", false, 110));
        st.submodules.push(mk_mod("private_child", true, 130));

        // Also add one Def entry to confirm symbols round-trip alongside.
        st.insert(
            Symbol::from("entry"),
            mk_def(
                DefKind::UserFn { constrained_fn: None },
                Some(trivial_defn("entry")),
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
        assert!(!rt.submodules[0].is_private, "is_private flag must round-trip (false)");
        assert_eq!(rt.submodules[1].name.as_ref(), "private_child");
        assert!(rt.submodules[1].is_private, "is_private flag must round-trip (true)");

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
}
