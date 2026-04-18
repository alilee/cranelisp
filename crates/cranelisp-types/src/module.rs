use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::PathBuf;

use crate::{
    ConstructorInfo, Defn, FQSymbol, FQTraitName, FQTypeName, GotTable, ModuleFullPath,
    ModuleName, Scheme, Sexp, Span, Symbol, TraitDecl, TraitName, Type, TypeDefInfo, TypeName,
    Visibility,
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
    /// Platform effect (dispatched through IO trampoline, Ring 4)
    PlatformEffect,
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
        Defn, DefnVariant, Expr, FQSymbol, FQTypeName, Scheme, Span, Symbol, Type, TypeDefInfo,
        TypeName, Visibility,
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
}
