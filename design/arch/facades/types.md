# Facade spec — `crates/cranelisp-types/`

**Bounded context citation.** Cross-crate boundary types and traits. The single home for any type that crosses a crate boundary. See `bounded-contexts.md` §7 — Cross-crate types.

This spec is **target-stating**. It describes the as-designed public surface; drift between as-designed and as-built is detected by `cargo-public-api` (M4-pending) and `/review`'s per-PR audit, not by this document.

---

## Public surface (as-designed)

Organised by concern. All boundary types live here so the dependency edge is one-directional: every other crate depends on `cranelisp-types`; `cranelisp-types` depends on no other workspace crate (Principle 3).

### Identifier newtypes

```rust
// String newtypes — hard rule per src/CLAUDE.md: never pass bare String where any of these is expected.
pub struct Symbol(String);              // local identifier — fn / var / operator / constructor name
pub struct ModuleName(String);          // single component, no dots — "core", "option"
pub struct ModuleFullPath(String);      // dotted path — "core.option", "user"
pub struct TypeName(String);            // type name (uppercase) — "Int", "Option"
pub struct TraitName(String);           // trait name (uppercase) — "Num", "Display"
pub struct LinkerSymbol(String);        // mangled name in the cache `Linker`'s symbol table — "add$Int+Int"
```

Each is generated via the `string_newtype!` macro: derives the standard trait set, implements `Deref<Target = str>`, `From<String>`, `From<&str>`, `AsRef<str>`, `Display`. `Serialize`/`Deserialize` for cache participation.

### Fully-qualified references

```rust
#[non_exhaustive]
pub struct FQSymbol {
    pub module: ModuleFullPath,
    pub symbol: Symbol,
}

#[non_exhaustive]
pub struct FQTypeName {
    pub module: ModuleFullPath,
    pub name: TypeName,
}

#[non_exhaustive]
pub struct FQTraitName {
    pub module: ModuleFullPath,
    pub name: TraitName,
}
```

Used wherever a value, type, or trait reference crosses a module boundary. The diagram-surfaced `process_form`, `wait_for_typecheck_symbol`, `wait_for_typecheck_type`, `priority_boost_jit`, `notify_symbol_typechecked`, `notify_inmem_codegen_complete`, `enqueue_jit` all take these.

### Source-level constructs (read by frontend, threaded through typecheck/backend)

```rust
#[non_exhaustive]
pub struct Span { pub start: u32, pub end: u32 }      // byte offsets — every error / warning carries one
pub const SYNTHETIC: Span;                            // for compiler-generated forms

pub enum Sexp { /* atom / list / bracket variants — preserves source spans */ }
```

### AST (built by frontend, annotated by typecheck, lowered by backend)

```rust
pub enum Expr { /* let / fn / if / match / apply / literal / var / do / quote / quasiquote — annotated with Type after check_form */ }

pub enum Pattern { /* literal / var / wildcard / constructor / nested */ }

#[non_exhaustive]
pub struct MatchArm { pub pattern: Pattern, pub guard: Option<Expr>, pub body: Expr }

pub enum TypeExpr { /* SYNTACTIC type expression (TypeName | applied | function | type-var) — distinct from Type */ }

pub enum Visibility { Public, Private }

#[non_exhaustive]
pub struct Defn { pub name: Symbol, pub variants: Vec<DefnVariant>, pub visibility: Visibility, pub docstring: Option<String>, pub span: Span }

#[non_exhaustive]
pub struct DefnVariant { pub params: Vec<(Symbol, TypeExpr)>, pub return_type: TypeExpr, pub body: Expr, pub span: Span }

#[non_exhaustive]
pub struct ConstructorDef { pub name: Symbol, pub fields: Vec<FieldDef>, pub span: Span }

#[non_exhaustive]
pub struct FieldDef { pub name: Option<Symbol>, pub ty: TypeExpr, pub span: Span }

#[non_exhaustive]
pub struct TraitDecl { pub name: TraitName, pub type_params: Vec<TypeName>, pub methods: Vec<TraitMethodSig>, pub visibility: Visibility, pub docstring: Option<String>, pub span: Span }

#[non_exhaustive]
pub struct TraitMethodSig { pub name: Symbol, pub params: Vec<TypeExpr>, pub return_type: TypeExpr, pub default_body: Option<Expr> }

#[non_exhaustive]
pub struct TraitImpl { pub trait_name: FQTraitName, pub target: TypeExpr, pub methods: Vec<Defn>, pub span: Span }

pub enum TopLevel { Defn(Defn), DeftypeAdt(/* … */), Deftrait(TraitDecl), Impl(TraitImpl), Defmacro(/* … */), Import(ImportSpec), Export(ExportSpec), Mod(ModDecl), Platform(PlatformSpec), Expr(Expr) }

#[non_exhaustive]
pub struct Program { pub forms: Vec<TopLevel> }

pub fn free_vars_expr(expr: &Expr) -> HashSet<Symbol>;
```

### `ParsedEntry` — the parse-time-only transient (per FIXME 0156 resolution)

`ParsedEntry` is the transient handoff from `cranelisp_frontend::build_form` to `cranelisp_typecheck::check_form`. It carries only what the parser knows; resolved-stage fields (type, scheme, callees, code, got_slot) are populated by `check_form` downstream and end up on `ModuleEntry`. **`ParsedEntry` NEVER lands in `SymbolTable`** — its lifecycle is bounded by one orchestrator iteration: `parse → ParsedEntry → check_form → Vec<(Symbol, ModuleEntry)> → SymbolTable.insert`. The SymbolTable invariant ("if it's in the table, it's checked") is preserved.

```rust
#[non_exhaustive]
pub enum ParsedEntry {
    /// Parsed `(defn name (params) body)` form. Pre-typecheck — types are `TypeExpr`, no `Scheme`.
    Def {
        name: Symbol,
        variants: Vec<DefnVariant>,
        visibility: Visibility,
        docstring: Option<String>,
        span: Span,
    },
    /// Parsed `(deftype Name … | (Variant fields...))` form. Yields the type itself plus per-constructor entries downstream.
    TypeDef {
        name: TypeName,
        type_params: Vec<TypeName>,
        constructors: Vec<ConstructorDef>,
        visibility: Visibility,
        docstring: Option<String>,
        span: Span,
    },
    /// Parsed `(deftrait Name … (method sig)*)` form.
    TraitDecl {
        decl: TraitDecl,                                   // re-uses the same shape as in `TopLevel::Deftrait`
    },
    /// Parsed `(impl Trait Type method-defns…)` form.
    TraitImpl {
        impl_: TraitImpl,
    },
    /// Parsed `(defmacro name clauses…)` form. Each clause downstream becomes a `ModuleEntry::Macro` clause.
    Macro {
        info: DefmacroInfo,
    },
    /// Synthetic per-constructor entry — emitted by `build_form` for each constructor of a `TypeDef`.
    /// Pre-typecheck shape; `check_form` lifts to a `ModuleEntry::Def` with primitive-kind constructor metadata.
    Constructor {
        name: Symbol,
        of_type: TypeName,
        fields: Vec<FieldDef>,
        span: Span,
    },
}

#[non_exhaustive]
pub struct DefmacroInfo {
    pub name: Symbol,
    pub clauses: Vec<MacroClauseInfo>,
    pub visibility: Visibility,
    pub docstring: Option<String>,
    pub span: Span,
}
```

`DefmacroInfo` moves from `cranelisp-frontend` to `cranelisp-types` (per FIXME 0156 resolution) so that `check_form`'s consumer (`int`) can name the type uniformly. The frontend's `parse_defmacro` becomes `pub(crate)` inside the `build_form` dispatcher.

`#[non_exhaustive]` on both `ParsedEntry` and `DefmacroInfo`. Derived traits: `Debug, Clone`. Not `Serialize/Deserialize` — `ParsedEntry` is transient; never persisted to cache.

### Resolved type system (output of typecheck, consumed by backend)

**`FQTypeName` is binding** as the cross-crate boundary type for resolved-stage type identifiers. Every API past frontend's resolution stage that names a type uses `FQTypeName`; bare `TypeName` is reserved for syntactic-stage uses inside the frontend (parser output, AST surface, `TypeExpr` shape). This commitment was lifted from aspirational to binding in Sprint 65 W2 — see `sprint-65-reshape-phase-2-review.md` §4.1 for the lift's rationale and the grep-and-classify pass that landed it.

`TypeName` and `FQTypeName` partition cleanly across the parse → resolve boundary:

- **`TypeName`** (syntactic stage) appears in positions produced by the frontend before module context is known: `TypeExpr::Named(TypeName)`, `TypeExpr::Applied`, `TraitImpl.target_type`, `TraitDecl.type_params`. The bare identifier is correct here; resolution has not happened yet. Frontend-internal constructs and AST nodes that the frontend emits are the only home for bare `TypeName`.
- **`FQTypeName`** (resolved stage) appears in positions produced by typecheck after resolution against `&symbol_tables`: `Type::ADT(FQTypeName, …)`, `TypeDefInfo.name`, `MethodResolutions.impl_type`, `ResolutionGap::Type(FQTypeName)`, `int::wait_for_typecheck_type(fqt: &FQTypeName)`. Every cross-crate API that names a type by identity uses `FQTypeName` — module ambiguity is resolved by the time the boundary is crossed.

The `TypeName → FQTypeName` lift happens inside `check_form` when a `TypeExpr::Named(name)` is resolved by looking up `name` in the current scope plus imported modules. This is the architectural reason the two newtypes exist as distinct types.

**Producer/consumer responsibility.** Frontend produces `TypeExpr` carrying bare `TypeName` (no resolution). Typecheck consumes `TypeExpr`, performs the lift, and produces `Type` / `TypeDefInfo` / `MethodResolutions` / `CheckResult` shapes carrying `FQTypeName`. Backend, intrinsics, primitives, platform, and int consume only `FQTypeName` at their public surface — no consumer past typecheck ever sees a bare `TypeName` in a boundary type. Two narrow exceptions, documented as principled and not extendable without `/arch` review:

1. **Reverse-lookup helpers on `Type`** — `from_name(&TypeName)` for primitive recognition and `type_name(&Type) -> Option<TypeName>` for primitive emission, which operate on the small set of built-in non-ADT types where the unqualified name IS unique.
2. **Receiver-pinned lookups** — APIs whose receiver itself supplies the module context. `SymbolTable::get_type(&TypeName)` is keyed by bare `TypeName` because the `&self` receiver IS the module; wrapping the local-to-this-table key in `FQTypeName` would re-encode information already pinned by the receiver. The fully-qualified identity is reconstructible by the caller as `FQTypeName::new(module_of(&self), name.clone())` if needed downstream. This exception is structural, not aspirational: it applies wherever the receiver's type pins the module context.

```rust
pub type TypeId = u32;

pub enum Type {
    Int,
    Bool,
    String,
    Float,
    Fn(Vec<Type>, Box<Type>),                                 // params, return
    ADT(FQTypeName, Vec<Type>),                               // module context embedded — module ambiguity resolved at typecheck
    Var(TypeId),                                              // unification variable; resolved to a concrete Type before codegen
    TyConApp(TypeId, Vec<Type>),                              // higher-kinded: a TypeId-bound type constructor applied to args (Ring 2+)
    /* IO is not a separate variant — represented as Type::ADT(FQTypeName { module: "primitives", name: "IO" }, [inner]) */
}

impl Type {
    pub fn adt(module: ModuleFullPath, name: TypeName, args: Vec<Type>) -> Type;     // construction helper — wraps FQTypeName::new internally

    pub fn from_name(name: &TypeName) -> Option<Type>;        // primitive TypeName → Type — TypeName::new("Int") → Type::Int. Returns None for non-primitives — caller falls back to SymbolTable::get_type for ADTs (Decision 6 — centralised mapping)
    pub fn type_name(&self) -> Option<TypeName>;              // Type → primitive TypeName — Type::Int → TypeName::new("Int"). Returns None for ADTs / fns / vars — those have FQTypeName or no single name

    pub fn is_io(&self) -> bool;                              // true iff Type::ADT(fqtn, _) where fqtn.module == "primitives" && fqtn.name == "IO"
    pub fn unwrap_io(&self) -> &Type;                         // T from IO T — returns self if not IO
    /* … */
}

#[non_exhaustive]
pub struct Scheme {
    pub type_vars: Vec<TypeId>,
    pub constraints: HashMap<TypeId, Vec<TraitName>>,        // bound trait constraints per var
    pub ty: Type,
}

pub type Subst = HashMap<TypeId, Type>;

pub fn apply(subst: &Subst, ty: &Type) -> Type;
pub fn free_vars(ty: &Type) -> HashSet<TypeId>;
pub fn max_type_var_id(ty: &Type) -> Option<TypeId>;
pub fn format_type_display(ty: &Type) -> String;
pub fn format_type_with_vars(ty: &Type, vars: &HashMap<TypeId, String>) -> String;
pub fn type_var_names(ty: &Type) -> HashMap<TypeId, String>;
```

### Symbol table — the single store

Per Decisions 25, 31, 32, 33: `SymbolTable<C: CodeStore, L: LinkerStore>` is THE per-module store. All per-symbol metadata lives on `ModuleEntry`. Structural decls (imports, exports, platforms, submodules) live as fields on `SymbolTable` (Decision 33).

```rust
#[non_exhaustive]
pub struct SymbolTable<C: CodeStore = (), L: LinkerStore = ()> {
    // populated form-by-form during typecheck — per-entry mutation via inner DashMap
    pub symbols: DashMap<Symbol, ModuleEntry<C>>,
    pub got: Arc<GotTable>,
    pub next_got_slot: AtomicUsize,

    // structural decls (Decision 33) — written by write_structural_decls at parse-time
    pub imports: Vec<ImportSpec>,
    pub exports: Vec<ExportSpec>,
    pub platforms: Vec<PlatformSpec>,
    pub submodules: Vec<ModDecl>,

    /// Canonical defn ordering for source regeneration — appended at first registration
    /// of each symbol; redefinition does NOT reorder. Used by `regenerate_backing_file`
    /// to emit defns in their original source order. Populated alongside structural decls
    /// at Phase 0 (parse-time write_structural_decls) for file-based modules; appended
    /// per REPL eval that introduces a new defn. Per Decision 39.
    pub defn_order: Vec<Symbol>,

    pub path: ModuleFullPath,
    pub schema_version: u32,                  // Decision 34 — bumped on serialised-shape change
    _phantom_l: PhantomData<L>,
}

impl SymbolTable {
    pub fn new(path: ModuleFullPath) -> Self;                                                      // SymbolTable<(), ()>
}

impl<C: CodeStore, L: LinkerStore> SymbolTable<C, L> {
    // ────── Phase 0 — brief [&mut SymbolTable] window at parse-time ──────
    /// Called once per module at parse-time, while the integration layer holds
    /// a brief RefMut from `Sess.symbol_tables.entry(m).or_default()`. Populates
    /// imports / exports / platforms / submodules + seeds defn_order with the
    /// declaration-order list of defn names extracted by the parser. After this
    /// returns, the RefMut drops and the SymbolTable is reachable only via shared
    /// `.get(m)` shard-read locks.
    pub fn write_structural_decls(&mut self, decls: StructuralDecls);

    /// REPL append path — extends `defn_order` with a single new defn. Brief
    /// per-eval RefMut hold (microseconds). For file-based modules, defn_order is
    /// fully populated at Phase 0 and this method is unused.
    pub fn append_defn_order(&mut self, sym: Symbol);

    /// Adds bare-name Import-variant entries to the inner symbols DashMap so that
    /// resolved-import names can be looked up via `get(sym)`. Per the per-symbol
    /// mutability discipline this is `&self` — writes go through the inner
    /// DashMap's per-entry write locks. Imports are installed during the form
    /// loop (when each `(import …)` form is processed by check_form), NOT at
    /// Phase 0.
    pub fn install_import_bindings(&self, from: &ModuleFullPath, names: ImportNames);

    // ────── Per-entry mutation — [&self] under inner DashMap per-key locks ──────
    pub fn get(&self, sym: &Symbol) -> Option<Ref<'_, Symbol, ModuleEntry<C>>>;
    pub fn insert_or_update(&self, sym: Symbol, entry: ModuleEntry<C>);                             // Decision 31 — carry-forward `code` from existing entry
    pub fn write_code(&self, sym: &Symbol, code: C);                                                // Decision 31 — atomic GOT swap on update
    pub fn allocate_got_slot(&self) -> usize;                                                       // monotonic, atomic

    // ────── Read-only iteration ──────
    pub fn public_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry<C>)>;
    pub fn defined_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry<C>)>;              // Decision 22 — codegen-compilable predicate
    pub fn all_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry<C>)>;
    pub fn get_type(&self, name: &TypeName) -> Option<&TypeDef>;                                    // receiver-pinned exception — &self IS the module context (see §"Resolved type system" exception 2)

    // ────── Defn order — read-only (regeneration walks this) ──────
    pub fn defn_order(&self) -> &[Symbol];
}

#[non_exhaustive]
pub struct StructuralDecls {
    pub imports: Vec<ImportSpec>,
    pub exports: Vec<ExportSpec>,
    pub platforms: Vec<PlatformSpec>,
    pub submodules: Vec<ModDecl>,
}

#[non_exhaustive]
pub enum ModuleEntry<C: CodeStore = ()> {
    Def {
        name: Symbol,
        kind: DefKind,
        scheme: Option<Scheme>,
        ast: Option<Expr>,                           // Decision 22 — codegen-compilable iff Some
        callees: Vec<FQSymbol>,                      // Decision 21 — TC-sourced call graph
        got_slot: usize,
        visibility: Visibility,
        docstring: Option<String>,
        /// Unified fn pointer — single source of truth for "where to call to invoke this entry."
        /// Origin is encoded by `kind: DefKind`, NOT by which optional field is set:
        ///   - `DefKind::Function | UserFn { … }` — user fn; ptr written by backend at codegen
        ///     (JIT path) or by `load_object` (linker-loaded cache path); paired with
        ///     `code = Some(Code::Jit(_))` or `Some(Code::Linker(_))`.
        ///   - `DefKind::Primitive { primitive_kind: Builtin | Inline | … }` — primitive;
        ///     ptr written at static-init by `cranelisp-primitives::PRIMITIVES_TABLE`;
        ///     `code = None` (primitives have process lifetime; no per-entry lifecycle owner).
        ///   - `DefKind::Primitive { primitive_kind: PlatformEffect { … } }` — platform DLL fn;
        ///     ptr resolved at platform-load time from `OwnedPlatformFnDescriptor.ptr`;
        ///     `code = None` (DLL handle held in `SharedState.kept_dlls`; DLL pages are not
        ///     unmapped while the session lives).
        /// serde-skip — runtime state, never persisted.
        ///
        /// Use `fn_ptr` directly for ptr extraction; do NOT match on `Code` variants for ptr access
        /// (`Code` carries lifecycle ownership only — see `code` field below and `facades/backend.md`).
        fn_ptr: Option<*const u8>,                   // unified — serde-skip
        /// Lifecycle owner only — `Code::Jit(Arc<Jit>)` for JIT-compiled user fns (Decision 31
        /// Scenario 2 — per-redefinition reclaim fires when the last `Arc<Jit>` clone drops),
        /// `Code::Linker(Arc<Linker>)` for cache-hit user fns. `None` for primitives (process
        /// lifetime) and platform DLL fns (DLL handle held elsewhere). The fn ptr lives on
        /// `fn_ptr`, NOT inside the `Code` variant. Decision 25 + Decision 41.
        #[serde(skip)] code: Option<C>,
    },
    Macro { name: Symbol, clauses: Vec<MacroClauseInfo>, callees: Vec<FQSymbol>, got_slot: usize, visibility: Visibility, docstring: Option<String>, #[serde(skip)] code: Option<C> },
    TypeDef { /* … per Decision 22 */ },
    Trait { /* … */ },
    TraitImpl { /* … */ },
    Import { /* bare-name binding installed by install_import_bindings */ },
    PlatformDecl { /* serde-persistent record of which DLL provides this fn */ },
}

#[non_exhaustive]
pub enum DefKind {
    UserFn { constrained_fn: Option<ConstrainedFn> },
    Macro { /* macro-specific */ },
    TypeDef { /* ADT shape */ },
    Trait { /* trait shape */ },
    Primitive { primitive_kind: PrimitiveKind },
    Overloaded { variants: Vec<OverloadVariant> },           // Decision multi-sig
}

#[non_exhaustive]
pub enum PrimitiveKind {
    Builtin,                                                  // intrinsic — Cranelift IR emitted directly
    PlatformEffect { scheduling_class: SchedulingClass },     // Decision 26 — class lives in the variant
}

#[non_exhaustive] pub struct ConstrainedFn { /* polymorphic defn awaiting monomorphisation */ }
#[non_exhaustive] pub struct OverloadVariant { /* one resolved monomorphic variant of a multi-sig defn */ }
#[non_exhaustive] pub struct MacroClauseInfo { /* per-clause macro shape */ }
#[non_exhaustive] pub struct MacroParam { /* macro parameter — Name | Bracket { fixed, rest } */ }
```

### Cross-module structural specs (read at parse-time, persisted in `SymbolTable`)

```rust
#[non_exhaustive]
pub struct ImportSpec {
    pub module_path: ModuleFullPath,
    pub alias: Option<ModuleName>,
    pub names: ImportNames,
    pub visibility: Visibility,
    pub span: Span,                                                         // whole import form — for "module not found" / unused-import errors
}

#[non_exhaustive]
pub enum ImportNames {
    Glob,
    Specific(Vec<NamedImport>),                                             // per-name spans — see NamedImport
    AliasOnly,
}

#[non_exhaustive]
pub struct NamedImport {
    pub name: Symbol,
    pub span: Span,                                                         // per-name span — for "name X not exported by m2" pointing at the specific name
}

#[non_exhaustive]
pub struct ExportSpec {
    pub names: Vec<NamedExport>,                                            // per-name spans — for "exported name X not defined" pointing at the specific name
    pub span: Span,                                                         // whole export form — for "export form has no names" / "duplicate export form" errors
}

#[non_exhaustive]
pub struct NamedExport {
    pub name: Symbol,
    pub span: Span,
}

#[non_exhaustive]
pub struct ModDecl {
    pub name: ModuleName,
    pub visibility: Visibility,
    pub span: Span,                                                         // for "submodule file not found" errors
}

#[non_exhaustive]
pub struct PlatformSpec {
    pub manifest_path: PathBuf,
    pub alias: Option<ModuleName>,
    pub span: Span,                                                         // for DLL load failure / ABI mismatch errors
}
```

### Typecheck output (consumed by backend)

```rust
#[non_exhaustive]
pub struct CheckResult {
    pub annotated_ast: Expr,
    pub scheme: Option<Scheme>,
    pub callees: Vec<FQSymbol>,
    pub method_resolutions: MethodResolutions,
    pub type_defs: Vec<TypeDefInfo>,
    pub mono_defns: Vec<MonoDefn>,
    /* … */
}

#[non_exhaustive]
pub enum CheckError {
    Gap(ResolutionGap),                          // surfaces a dependency to int's process_form orchestrator — caller dispatches via handle_gap and retries
    TypeError { /* … */, span: Span },           // genuine type error — non-recoverable
    /* … */
}

/// Dependency-not-yet-ready signal produced by frontend::expand and typecheck::check_form.
/// The orchestrator (int::process_form) catches and dispatches to the scheduler, then retries.
/// Per the gap-return pattern — frontend and typecheck stay pure (no Sess / scheduler dependency)
/// and surface dependencies as values.
#[non_exhaustive]
pub enum ResolutionGap {
    SymbolTypechecked(FQSymbol),                 // need entry's type/scheme — check_form value refs (typecheck only; macros are already expanded by the time check_form runs)
    MacroInMem(FQSymbol),                        // expand: make this FQ as ready as it needs to be for macro expansion. Orchestrator does ensure_registered + wait_for_typecheck_symbol, then peeks at the entry — if it's a Macro with code missing, additionally priority_boost + wait_for_inmem; otherwise just retry. One retry round-trip regardless of macro-vs-fn.
    Type(FQTypeName),                            // need type's typecheck — check_form FQ type refs
}

#[non_exhaustive] pub struct TypeDefInfo { /* registered ADT/type metadata */ }
#[non_exhaustive] pub struct ConstructorInfo { /* per-constructor info */ }
#[non_exhaustive] pub struct FieldInfo { /* per-field info */ }
#[non_exhaustive] pub struct MethodResolutions { pub resolved_calls: HashMap<Span, ResolvedCall> }
#[non_exhaustive] pub enum ResolvedCall { TraitMethod { /* … */ }, SigDispatch { /* … */ }, AutoCurry { /* … */ } }
#[non_exhaustive] pub struct MonoDefn { /* monomorphic specialisation of a constrained polymorphic fn */ }
#[non_exhaustive] pub struct DisplayInfo { /* REPL display metadata */ }
#[non_exhaustive] pub struct ReplSnapshot { /* TC snapshot for REPL eval rollback on error — pipeline-v4 §6.2 */ }
```

`ProcessedForm` is `int`'s shape, not `cranelisp-types`'s — `int` composes a `CheckResult` plus codegen-readiness info per the diagram. (See `facades/int.md`.)

### Sealed marker traits (Decision 32)

```rust
pub trait CodeStore: Send + Sync + Clone + 'static {}
impl<T: Send + Sync + Clone + 'static> CodeStore for T {}

pub trait LinkerStore: Send + Sync + Clone + 'static {}
impl<T: Send + Sync + Clone + 'static> LinkerStore for T {}
```

Empty marker traits with blanket impls. The `Clone` super-bound is load-bearing per Decision 32 — needed for DashMap iteration semantics and the `register_defn_signature` carry-forward invariant. Crates that don't handle compiled code work with `SymbolTable<(), ()>` and never see the parameters.

### GOT — the cross-thread publication primitive

```rust
#[non_exhaustive]
pub struct GotTable {
    slots: Vec<AtomicPtr<()>>,                    // single-writer per slot, atomic-readable by many
}

impl GotTable {
    pub fn new(capacity: usize) -> Self;
    pub fn load_slot(&self, slot: usize) -> *const u8;        // Ordering::Acquire
    pub fn store_slot(&self, slot: usize, ptr: *const u8);    // Ordering::Release — Decision 31 atomic swap
    pub fn base_ptr(&self) -> *const u8;                      // backend reads this for __cranelisp_got_{module} resolution
}

pub const GOT_TABLE_SIZE: usize;
```

### Heap layout (consumed by backend codegen)

```rust
pub enum HeapCategory { NeverHeap, AlwaysHeap, Mixed }    // codegen drives RC discipline by category
#[non_exhaustive] pub struct HeapHeader { /* total_size: u64 | rc: AtomicI64 — base-pointer convention per src/CLAUDE.md */ }
pub const NULLARY_TAG_THRESHOLD: i64;                     // ADT discriminant boundary for nullary vs data ctors
```

### Pipeline / orchestration types

```rust
#[non_exhaustive] pub enum CodegenBehaviour { InMemoryAndObject, ObjectOnly }   // settings.codegen_behaviour — controls Run vs Link
#[non_exhaustive] pub enum ModuleStrategy { Initial, Replace, Additive }        // register_module / re_register / append_form discrimination
#[non_exhaustive] pub struct CompileContext { /* per-batch context — passed by int into backend::compile_to_module */ }
#[non_exhaustive] pub struct CompileResult { /* per-batch result — JIT or object */ }
#[non_exhaustive] pub struct CallGraph { /* rich within-module call graph for codegen */ }
#[non_exhaustive] pub struct CallEdge { pub caller: Symbol, pub callee: FQSymbol, pub tail: bool, pub span: Span }
#[non_exhaustive] pub struct CallInfo { /* per-call resolution info */ }
```

### Operator / primitive registry (consumed by backend for Cranelift lowering)

```rust
#[non_exhaustive]
pub struct PrimitiveDef {
    pub name: Symbol,                                                      // user-visible name (kebab-case per src/CLAUDE.md JIT symbol naming)
    pub ty: Type,                                                          // monomorphic scheme registered by typecheck
    pub cranelift_op: &'static str,                                        // backend matches on this to emit inline Cranelift IR
    pub param_names: Vec<Symbol>,                                          // for /sig display
}

pub fn primitives() -> &'static [PrimitiveDef];                            // the single authoritative primitive registry — typechecker registers, backend matches on cranelift_op
```

### Marshaling tags (consumed by backend + runtime for Sexp ABI)

```rust
pub const TAG_SNIL: i64;
pub const TAG_SCONS: i64;
pub const TAG_SEXP_INT: i64;
pub const TAG_SEXP_FLOAT: i64;
pub const TAG_SEXP_BOOL: i64;
pub const TAG_SEXP_STR: i64;
pub const TAG_SEXP_SYM: i64;
pub const TAG_SEXP_LIST: i64;
pub const TAG_SEXP_BRACKET: i64;
```

### Scheduling — for IO trampoline + Effect dispatch

Plain manifest data attached to platform DLL functions. Governs two things: (a) how `bind!` chains are compiled — sequential-chain vs parallel-safe; (b) how the IO trampoline schedules nodes during IO forcing. Lives in `cranelisp-types` (rather than `cranelisp-platform`) so it can appear on both `PrimitiveKind::PlatformEffect` and `cranelisp_platform::PlatformFn` without forcing a `cranelisp-types → cranelisp-platform` dependency edge (which Principle 3 forbids).

```rust
#[repr(u32)]
pub enum SchedulingClass {
    /// Always execute in order relative to other effects — global shared resource (stdin, stdout, a global log). Never placed in a Par node.
    Sequential = 0,                                                              // default
    /// Fully independent — no shared state between calls. Always safe to parallelise with other Commutative effects (HTTP requests, time queries, `open`).
    Commutative = 1,
    /// Parallel across different resource tokens; sequential within the same token. The platform fn sets the token via `CLIO::effect_on_resource(token, …)`.
    ResourceSerial = 2,
}

impl SchedulingClass {
    pub fn from_u32(v: u32) -> Self;                                             // unknown discriminants default to Sequential — for forward-compat across DLLs built against newer ABI
}
```

NOT `#[non_exhaustive]` because it crosses the platform-DLL C ABI as a `#[repr(u32)]` discriminant — `from_u32` exists precisely to handle ABI-version drift. Adding a variant requires bumping `cranelisp_platform::ABI_VERSION`.

### Errors and warnings

Per Decision 39, errors carry an `ErrorLocation` — coordinates as data, formatting downstream. Producer captures what it has at error-construction time; the formatter (in `int`) decides what to display based on what's populated. Production batch displays `file:line:col`; REPL/trace mode resolves `fq` against `shared.introspection[fq].source` for inline snippets; parse errors carry their own `context` snippet inline (parser holds the file `Arc<str>` at error time).

```rust
/// 1-based line + column, derived from byte offsets when source is in hand.
#[non_exhaustive]
pub struct LineCol {
    pub line: u32,
    pub col: u32,
}

#[non_exhaustive]
pub struct LineColRange {
    pub start: LineCol,
    pub end: LineCol,
}

/// Permissive error-location carrier. Producers populate the fields they have on
/// hand; the formatter selects display strategy based on what's present.
#[non_exhaustive]
pub struct ErrorLocation {
    /// Byte offsets into the relevant source coordinate system (file-global for
    /// parse errors, per-defn-local for typecheck/codegen errors per Decision 39).
    /// Always populated.
    pub span: Span,

    /// Source file path when known (file-based modules); `None` for REPL evals or
    /// synthetic forms.
    pub file: Option<PathBuf>,

    /// Owning defn for post-parse errors. The formatter resolves this against
    /// `shared.introspection[fq].source` to produce inline snippets in REPL/trace
    /// mode. `None` for parse errors (no defn registered yet) and for module-level
    /// errors (e.g. import not found).
    pub fq: Option<FQSymbol>,

    /// Pre-resolved line/col coordinates. Populated when source was available at
    /// error-construction time (parser path always; typecheck/codegen path when
    /// per-defn source is in hand). Lets the formatter display `file:line:col`
    /// without needing to re-resolve byte offsets at display time.
    pub line_col: Option<LineColRange>,

    /// Inline source-context snippet captured at error time. Populated by the
    /// parser (a few surrounding lines) so parse errors are self-contained even
    /// after the file `Arc<str>` is dropped. Typecheck/codegen errors typically
    /// leave this `None` and rely on `fq` + introspection resolution at display
    /// time, but may populate it for production-mode standalone display.
    pub context: Option<String>,
}

#[non_exhaustive]
pub enum CranelispError {
    ParseError    { message: String, location: ErrorLocation },
    TypeError     { message: String, location: ErrorLocation },
    ModuleError   { message: String, location: ErrorLocation },
    CodegenError  { message: String, location: ErrorLocation },
    LinkError     { message: String },                                          // process-level — no location
    CacheError    { message: String },                                          // process-level — no location
    RuntimeError  { message: String, location: Option<ErrorLocation> },         // location optional — runtime panics may originate from synthetic call sites
    Platform(PlatformError),                                                    // per Decision 42 — structured platform-origin failures with location
    /* … */
}

impl CranelispError {
    /// Single accessor used by the integration-layer formatter — returns the
    /// error's location if it carries one. `LinkError` and `CacheError` return None.
    pub fn location(&self) -> Option<&ErrorLocation>;
}

#[non_exhaustive]
pub struct Warning {
    pub kind: WarningKind,
    pub message: String,
    pub location: ErrorLocation,                                                // same shape as errors — uniform formatting
}

#[non_exhaustive]
pub enum WarningKind { UnusedDefn, UnusedImport, ShadowedName, /* … */ }

/// Per-call linker error — surfaced by `Linker::get_symbol` and other
/// per-symbol cache-load operations. Distinct from `CranelispError::LinkError`
/// (process-level link failure). Per §2.6 — facade embeds logic in types:
/// asking for a symbol that's not there is a typed result, not a bare `Option`.
/// Per FIXME 0154 resolution — the two-variant baseline is the minimum surface
/// acceptable at S66 close; additional variants extend as evidence accrues
/// (re-shape may be triggered during /review of a future FIXME).
#[non_exhaustive]
pub enum LinkerError {
    /// The cache `Linker`'s symbol table does not contain the requested name.
    /// Usually indicates either: (a) the `.o` was produced from a different
    /// source state than the symbol-table consumer expects (cache mismatch);
    /// (b) the symbol's `Linkage::Local` bare name doesn't match what the
    /// caller asked for (Decision 36 contract violation).
    SymbolNotFound { name: LinkerSymbol },
    /// Object relocation pass produced an error during `load_object` or
    /// per-symbol resolution. Signals corruption, ABI mismatch, or
    /// unresolved external reference.
    RelocationFailed { name: LinkerSymbol, cause: String },
}

/// Cross-cutting "this dependency isn't ready yet" signal. Carried by both
/// `ExpansionError::Gap` (frontend `expand`) and `CheckError::Gap` (typecheck
/// `check_form`). The integration layer's `process_form` pattern-matches on
/// the variant to decide what to wait on (typecheck for symbol typing, JIT
/// for in-mem macro code, typecheck for an opaque type ref). Per FIXMEs 0092
/// + 0093.
#[non_exhaustive]
pub enum ResolutionGap {
    /// Symbol's typecheck not yet complete — wait for `notify_symbol_typechecked(fq)`.
    SymbolTypechecked(FQSymbol),
    /// Macro target needs in-mem JIT — typecheck first, then `priority_boost_jit(fq)` + `wait_for_inmem(fq)`.
    MacroInMem(FQSymbol),
    /// Type reference needs typecheck — wait for `notify_type_resolved(fq)`.
    Type(FQTypeName),
}

/// Typecheck-side error type for `cranelisp_typecheck::check_form`. Mirrors
/// the frontend-side `ExpansionError`'s shape — both carry `ResolutionGap`
/// for the dependency-not-ready case, both surface domain errors with
/// `ErrorLocation` per Decision 39. Per FIXME 0093.
#[non_exhaustive]
pub enum CheckError {
    /// Dependency not yet ready — caller dispatches via int::process_form's handle_gap and retries.
    Gap(ResolutionGap),
    /// Type-inference or constraint failure — substantive typecheck rejection.
    TypeError { message: String, location: ErrorLocation },
}

/// Platform-origin failures — DLL load, manifest parse, ABI mismatch, dispatch.
/// Per Decision 42 — coordinates as data; `int`'s `Sess::format_error` consumes
/// via `CranelispError::Platform(PlatformError)` and selects display strategy
/// via Decision 39's mode-conditional source resolution.
#[non_exhaustive]
pub enum PlatformError {
    /// DLL could not be loaded from the search path.
    LoadFailed { dll: PathBuf, cause: String, location: ErrorLocation },
    /// DLL was found but its manifest is missing or unreadable.
    ManifestNotFound { dll: PathBuf, location: ErrorLocation },
    /// DLL's declared ABI version does not match the runtime's expected version.
    AbiVersionMismatch { dll: PathBuf, expected: u32, found: u32, location: ErrorLocation },
    /// A platform-fn dispatch failed at runtime (e.g., null fn ptr, panic in callee).
    DispatchError { fn_name: Symbol, cause: String, location: ErrorLocation },
}
```

**Producer-side policy** (consequence of the design, not part of the facade):

| Producer | `span` | `file` | `fq` | `line_col` | `context` |
|---|---|---|---|---|---|
| Parser (file `Arc<str>` in hand) | ✓ file-global | ✓ if file-based | — | ✓ (cheap) | ✓ (a few surrounding lines, captured before the file string drops) |
| Typecheck / codegen (per-defn source on Introspection) | ✓ per-defn-local | ✓ if file-based | ✓ owning defn | ✓ when introspection enabled | typically — (formatter resolves via introspection) |
| Production batch (introspection = None) | ✓ | ✓ | ✓ | ✓ | — (no source retained; formatter shows `file:line:col` only) |

**Formatter-side policy** lives in `int` (display layer, not `cranelisp-types`). The facade gives the formatter all permissions; what to display where is `int`'s call.

---

## Re-exports

`cranelisp-types` does not re-export from anywhere — it has no workspace dependencies (Principle 3). It depends only on `serde`, `dashmap`, and `std`.

---

## Consumed surface

None. `cranelisp-types` is the bottom of the workspace dependency DAG.

---

## Sealed traits

`CodeStore` and `LinkerStore` are sealed in the empty-marker sense per Decision 32 — no methods, blanket impl over `Send + Sync + Clone + 'static`. Crates implement them by virtue of their concrete `C` and `L` types satisfying the bounds; there is no method surface to extend. `/arch` does not need to approve new impls because the blanket impl admits any type satisfying the bounds.

---

## `#[non_exhaustive]` policy

Every public struct and enum in `cranelisp-types` MUST be `#[non_exhaustive]`. Adding a variant or field is non-breaking; consumers cannot exhaustively match or destructure across crate boundaries.

The newtypes (`Symbol`, `ModuleFullPath`, etc.) are an exception — they wrap a single `String` and are constructed via `From`/`From<&str>`. The wrapper is opaque; field access is not exposed. (No `#[non_exhaustive]` needed because there's nothing to add.)

---

## Notable items NOT in `cranelisp-types`

These types are referenced from the diagrams but live elsewhere because including them here would invert the dependency edge (Principle 3):

- **`Code` enum** — the per-entry retention root for compiled code (`Code::Jit { jit: Arc<Jit>, ptr } | Code::Linker { linker: Arc<Linker>, ptr }`). Lives in `int` (`src/code.rs`) per Decision 35. References `cranelisp_backend::jit::Jit` and `cranelisp_backend::cache::Linker` — neither of which `cranelisp-types` may name.
- **`JitArtefact`, `LinkerArtefact`, `ObjectArtefact`** — backend's compile_to_module / load_object / compile_to_object return shapes. Live in `cranelisp-backend`. Reference Cranelift types.
- **`PriorityWork`, `NiceWork`, `CompileScheduler`** — work item enums and the scheduler itself. Live in `int` (`src/scheduler.rs`).
- **`ProcessedForm`** — the shared `process_form` return shape. Lives in `int`. Composes a `CheckResult` (from `cranelisp-types`) with codegen-readiness info.
- **`ObjectCache`, `CacheLookupResult`, `CacheError`** — cache facade. Lives in `int` (`src/cache.rs`).
- **`EvalResult`, `EvalValue`, `CommandResult`, `SlashCommand`, `SymbolInfo`, `SymbolDescription`, `FileChangeEvent`** — REPL-side types. Live in `int`.
- **`CLType`, `CLInt`, `CLString`, `CLBool`, `CLFloat`, `CLIO<T>`, `CLHeap`, `CLOwned`, `HostContext`, `HostCallbacks`, `PlatformFn`, `OwnedPlatformFnDescriptor`, `PlatformManifest`** — platform ABI. Live in `cranelisp-platform`.

---

## Bounded-context invariants

These hold across sprints — the contract `cranelisp-types` makes with the rest of the workspace:

1. **No logic.** Every item here is a data definition or a thin function over data (apply, free_vars, type_var_names). No business logic; no side effects. Provider crates implement the behaviour.
2. **Boundary-only.** A type lives here if and only if it crosses a crate boundary. Per-crate internal types live in their owning crate.
3. **Never depends on other workspace crates.** Forward dependency edges only — `cranelisp-types → ∅` is the design intent. Cranelift types, JIT handles, runtime allocator handles, and similar concrete-implementation types are confined to their owning crate (per Decision 35's `Code` placement).
4. **All identifier fields use newtypes.** Per `src/CLAUDE.md` — no bare `String` for anything that names something in the language.
5. **Every error carries an `ErrorLocation` (Decision 39).** Even if synthetic. `ErrorLocation.span` is always populated (even for synthetic forms — using `SYNTHETIC`). Other fields (`file`, `fq`, `line_col`, `context`) are populated by the producer based on what's available at error-construction time. The integration layer formatter resolves location data into displayable form, with REPL/trace mode using `shared.introspection[fq].source` for inline snippets and production batch falling back to `file:line:col` style.
6. **Warnings are data.** `Vec<Warning>` accumulated and returned, never `eprintln!` — the integration layer formats and displays.
7. **Cache shape is versioned.** Per Decision 34 — `SymbolTable.schema_version: u32` is the canonical version field; cache load checks it before accepting deserialised state.
