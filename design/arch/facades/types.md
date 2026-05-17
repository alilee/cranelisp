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
pub struct JitSymbol(String);           // JIT-time mangled name — pre-cache; "Display.show$Option$Int" etc.
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

**Trait-method addressing convention (S66 Wave 3a — user-arbitrated 2026-05-13).** Trait methods are addressed by composite `Symbol` within the trait's defining module. For a trait method `Display.show` declared in module `core`:

- The canonical `ModuleEntry::Def` for the method lives in `core` keyed by `Symbol::from("Display.show")`.
- Per-method `ModuleEntry::Import` bindings injected by the prelude into user modules carry `source: FQSymbol { module: ModuleFullPath::from("core"), symbol: Symbol::from("Display.show") }`.
- Bare-name use sites (`(show 42)`) install the local Import binding under the bare `Symbol::from("show")` — keyed by the user-visible name, with `source` pointing at the composite `Display.show` in the trait's home module.

The trait is **not** a distinct module namespace — `core/Display/show` is NOT a valid path. Two options were considered and rejected:

- (A) `module: "core/Display", symbol: "show"` — breaks Principle 17's module-path semantics (`/` in `ModuleFullPath` would imply nested-module lookup, which `chain-follow` would then try to navigate against a path that has no `SymbolTable`).
- (C) `module: "core", trait: Some("Display"), symbol: "show"` — promotes traits to a first-class third component of `FQSymbol`. Rejected as gratuitous structural cost; the dot-composite spelling is already the REPL's convention (`/list` Trait.method format) and matches what users type when disambiguating.

Option B (composite `Symbol`) keeps `FQSymbol` two-component, keeps `ModuleFullPath` strictly module-pathed, and keeps the per-symbol-chain-follow primitive of Principle 17 unchanged — a trait-method Import binding chains exactly like any other Import binding, with the symbol part happening to contain a `.`. Backend mangling for trait-method bodies (`Display.show$Option$Int`, etc., per `facades/types.md` §"`SymbolTable` — the single store" `TraitImpl` notes) is unaffected: the `$`-mangled local Symbol IS the body name; the dot-composite is the trait-method canonical name. The two coexist because they identify different things (the body vs. the trait-method binding).

This is binding for `Wave 3a-α/β` and forward: any `FQSymbol` whose `symbol` field contains a `.` is a trait-method reference, addressable in the trait's defining module.

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

### `ParsedEntry` — the parse-time-only transient (per FIXME 0156 resolution; passed as `Vec<ParsedEntry>` to `check_forms` per Decision 44's 2026-05-13 third amendment)

`ParsedEntry` is the transient handoff from `cranelisp_frontend::build_form` to the single-call typecheck surface (`cranelisp_typecheck::check_forms`). It carries only what the parser knows; resolved-stage fields (type, scheme, callees, code, got_slot) are populated by `check_forms` downstream and end up on `ModuleEntry`. **`ParsedEntry` NEVER lands in `SymbolTable`** — its lifecycle is bounded by one orchestrator-cluster iteration: `parse → ParsedEntry → orchestrator accumulates Vec<ParsedEntry> → check_forms(Vec<ParsedEntry>) (internal Pass 1 then Pass 2) → staging carries typed entries → orchestrator commits staging into live SymbolTable`. The SymbolTable invariant ("if it's in the live table, it's checked AND committed") is preserved by the cluster-atomic commit.

**Persistence across passes**. The orchestrator (`int::process_cluster`) accumulates the `Vec<ParsedEntry>` for the cluster and hands the whole list to one `check_forms` call. The internal Pass 1 / Pass 2 ordering reads the same vector twice. `ParsedEntry` derives `Clone` so the orchestrator can rebuild the vector on Gap-retry (whole-cluster retry against a fresh staging frame); the parser never produces a `ParsedEntry` that would invalidate between cluster attempts.

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

### `View<'a, C, L>` — the cluster read surface (per Decision 44, amended FIXME 0167)

`View<'a, C, L>` is a thin newtype that wraps two `&SymbolTable<C, L>` references — staging (orchestrator-local, transient) and live — and routes lookups staging-first then live. It is the read surface the typecheck cluster surface (`check_forms`) sees for the current cluster's per-module read. Typecheck does not know whether a given lookup hits staging, live, or unioned content; it just calls `view.lookup(name)`.

**Construction site**. `View` is not constructed at the typecheck call site directly; it is produced inside `ClusterContext::current_symbol_table()` (in `cranelisp-typecheck`). In `ClusterContext::Cluster` mode the accessor returns `View::union(staging, live)`; in `ClusterContext::Live` mode the accessor returns `View::single(live)` — a single-source view over the live module. This indirection means the two-pass typecheck signature does not change shape across cluster-vs-committed mode — typecheck always reads through `ctx.current_symbol_table()`, and the staging-vs-live distinction is absorbed by `ClusterContext`'s accessor surgery. `View` itself remains the read-side abstraction and lives in `cranelisp-types` (multi-consumer at the boundary type level — frontend + typecheck both consume it via `ClusterContext`'s API surface).

```rust
pub struct View<'a, C: CodeStore = (), L: LinkerStore = ()> {
    staging: &'a SymbolTable<C, L>,
    live: &'a SymbolTable<C, L>,
}

impl<'a, C: CodeStore, L: LinkerStore> View<'a, C, L> {
    /// Construct a composite read view. Lookups dispatch staging-first, then live.
    /// Both refs must outlive `'a`; lifetime bound on the returned `View`.
    pub fn union(staging: &'a SymbolTable<C, L>, live: &'a SymbolTable<C, L>) -> Self;

    /// Construct a single-source read view over `live` alone. Used by
    /// `ClusterContext::Live` (REPL introspection, fine-grained-test paths,
    /// any caller reading committed state directly). Lookups dispatch
    /// directly to `live`; no staging side. Adds no allocation; the newtype
    /// stores the single reference. Selected over a static empty-sentinel
    /// sentinel (`View::union(&EMPTY, live)`) for cleaner surface — the API
    /// names what each mode does rather than embedding a sentinel idiom.
    pub fn single(live: &'a SymbolTable<C, L>) -> Self;

    /// Read-through lookup. Staging entries shadow live entries (Pass 1 sig
    /// shells masking any partially-existing live placeholder that should
    /// not happen — both passes assume cluster atomicity). `single`-mode
    /// dispatches directly to live.
    pub fn lookup(&self, name: &Symbol) -> Option<&ModuleEntry<C>>;

    /// Iterate the union, staging-first; live entries shadowed by staging
    /// keys are skipped. Order within each table is iteration order of the
    /// underlying DashMap. Used by typecheck passes that need to enumerate
    /// (e.g., `defined_symbols()`-style passes).
    pub fn iter(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry<C>)> + '_;
}
```

**Properties**:
- No allocation per lookup — the newtype holds two references and dispatches.
- Read-only — `View` exposes no write methods; staging is mutated only through the orchestrator's direct `&mut SymbolTable` handle outside the typecheck call.
- Lifetime-bounded — the `View` borrows both tables for `'a`; it cannot outlive either.

**Why a newtype rather than a trait or a method on `SymbolTable`**. The orchestrator passes a 2-level composite read view today. A trait abstraction (`SymbolTableView`) would generalise to N-level staging or alternate read shapes, but adds a trait surface to support a single production caller pattern. A method on `SymbolTable` returning a `View` is fine but the construction call (`View::union`) reads cleaner at the orchestrator site. If future needs require N-level staging or other compositions, a trait can be introduced then; the current shape is the minimum surface that satisfies cluster-atomic Pass 1 / Pass 2 visibility.

`#[non_exhaustive]`. Derived traits: `Debug` (best-effort — delegates to underlying tables). Not `Clone` (a `View` is constructed at the call site; cloning the borrow has no value). Not `Serialize/Deserialize` — never persisted; the `'a` lifetime makes this physically impossible at the boundary.

### Resolved type system (output of typecheck, consumed by backend)

**`FQTypeName` is binding** as the cross-crate boundary type for resolved-stage type identifiers. Every API past frontend's resolution stage that names a type uses `FQTypeName`; bare `TypeName` is reserved for syntactic-stage uses inside the frontend (parser output, AST surface, `TypeExpr` shape). This commitment was lifted from aspirational to binding in Sprint 65 W2 — see `sprint-65-reshape-phase-2-review.md` §4.1 for the lift's rationale and the grep-and-classify pass that landed it.

`TypeName` and `FQTypeName` partition cleanly across the parse → resolve boundary:

- **`TypeName`** (syntactic stage) appears in positions produced by the frontend before module context is known: `TypeExpr::Named(TypeName)`, `TypeExpr::Applied`, `TraitImpl.target_type`, `TraitDecl.type_params`. The bare identifier is correct here; resolution has not happened yet. Frontend-internal constructs and AST nodes that the frontend emits are the only home for bare `TypeName`.
- **`FQTypeName`** (resolved stage) appears in positions produced by typecheck after resolution against `&symbol_tables`: `Type::ADT(FQTypeName, …)`, `TypeDefInfo.name`, `MethodResolutions.impl_type`, `ResolutionGap::Type(FQTypeName)`, `int::wait_for_typecheck_type(fqt: &FQTypeName)`. Every cross-crate API that names a type by identity uses `FQTypeName` — module ambiguity is resolved by the time the boundary is crossed.

The `TypeName → FQTypeName` lift happens inside `check_form` when a `TypeExpr::Named(name)` is resolved by looking up `name` in the current scope plus imported modules. This is the architectural reason the two newtypes exist as distinct types.

**Producer/consumer responsibility.** Frontend produces `TypeExpr` carrying bare `TypeName` (no resolution). Typecheck consumes `TypeExpr`, performs the lift, and produces `Type` / `TypeDefInfo` / `MethodResolutions` / `CheckResult` shapes carrying `FQTypeName`. Backend, intrinsics, primitives, platform, and int consume only `FQTypeName` at their public surface — no consumer past typecheck ever sees a bare `TypeName` in a boundary type. Two narrow exceptions, documented as principled and not extendable without `/arch` review:

1. **Reverse-lookup helpers on `Type`** — `from_name(&TypeName)` for primitive recognition and `type_name(&Type) -> Option<TypeName>` for primitive emission, which operate on the small set of built-in non-ADT types where the unqualified name IS unique.
2. **Receiver-pinned lookups** — APIs whose receiver itself supplies the module context. `SymbolTable::get_type(&TypeName)` is keyed by bare `TypeName` because the `&self` receiver IS the module; wrapping the local-to-this-table key in `FQTypeName` would re-encode information already pinned by the receiver. The fully-qualified identity is reconstructible by the caller as `FQTypeName::new(module_of(&self), name.clone())` if needed downstream. This exception is structural, not aspirational: it applies wherever the receiver's type pins the module context.

## FQTypeName migration plan (Sprint 67)

Per Sprint 67 second-challenge scope amendment (`sprints/SPRINT.md` §"Second user challenge applied"), FQTypeName binding migration (FIXME 0151) is edge drift, not interior. The facade above commits to `FQTypeName` at every resolved-stage boundary; source has not been migrated since the binding lift in S65 W2. /dev (per crate) executes the conversions in Wave 3 per the table below; /dev (typecheck) carries the largest share.

Direction discipline:
- **PIF — convert to `FQTypeName`**: API is a resolved-stage boundary and no exception applies. Wave 3 conversion.
- **Keep — frontend syntactic**: inside frontend AST/parser surface (`TypeExpr::Named(TypeName)` and friends). No conversion.
- **Keep — receiver-pinned**: `SymbolTable::get_type(&TypeName)` and any hit where `&self` IS the module-owning receiver. Exception 2.
- **Keep — reverse-lookup**: `Type::from_name(&TypeName)` and `type_name(&Type) -> Option<TypeName>`. Exception 1.

### typecheck

Largest concentration; bulk of /dev (typecheck) Wave 3 burden.

| API | File:line | Direction | Owning /dev task |
|---|---|---|---|
| `TypeCheckEnv::lookup_type_def(&self, &TypeName)` | `crates/cranelisp-typecheck/src/checker.rs:571,2497` | **Keep — receiver-pinned** | (none — exception 2; receiver IS the module-owning env) |
| `TypeCheckEnv::lookup_type_def_in_module(&self, &ModuleFullPath, &TypeName)` | `crates/cranelisp-typecheck/src/checker.rs:584,2510` | PIF | /dev (typecheck) Wave 3 — pair of args collapses to `&FQTypeName` |
| `TypeCheckEnv::lookup_constructor_type(&self, &str) -> Option<TypeName>` | `crates/cranelisp-typecheck/src/checker.rs:627,2516` | PIF return | /dev (typecheck) Wave 3 — return becomes `Option<FQTypeName>` |
| `TypeCheckEnv::all_type_defs(&self) -> Vec<(TypeName, TypeDefInfo)>` | `crates/cranelisp-typecheck/src/checker.rs:699` | PIF return | /dev (typecheck) Wave 3 — Vec element becomes `(FQTypeName, TypeDefInfo)`; REPL introspection callers update |
| `TypeCheckEnv::all_type_defs_map(&self) -> HashMap<TypeName, TypeDefInfo>` | `crates/cranelisp-typecheck/src/checker.rs:748` | PIF return | /dev (typecheck) Wave 3 |
| `TypeCheckEnv::snapshot_type_defs(&self) -> (HashMap<TypeName, …>, HashMap<Symbol, TypeName>)` | `crates/cranelisp-typecheck/src/checker.rs:764` | PIF | /dev (typecheck) Wave 3 — both halves lift |
| `TypeCheckEnv::register_type_def(&mut self, type_name: &TypeName, ...)` | `crates/cranelisp-typecheck/src/checker.rs:1675,2524` | Conditional: **keep** if called only post-cluster-context-set, **PIF** otherwise | /dev (typecheck) Wave 3 — audit call sites; if a receiver-pinned cluster context names the module, treat as exception 2 |
| `TypeCheckEnv::check_exhaustiveness(&mut self, type_name: &TypeName, …)` | `crates/cranelisp-typecheck/src/checker.rs:1733,2542` | PIF | /dev (typecheck) Wave 3 — match-arm checks are post-resolution; `FQTypeName` |
| `cranelisp_typecheck::adt::register_type_def(name: &TypeName, …)` | `crates/cranelisp-typecheck/src/adt.rs:31,107,188,209,244,260,328,346` | Conditional per call | /dev (typecheck) Wave 3 — within-module ADT registration is receiver-pinned; cross-module ADT references via `TypeExpr::Named` lift at boundary |
| `cranelisp_typecheck::resolve::*(name: &TypeName, …)` | `crates/cranelisp-typecheck/src/resolve.rs:58,83` | **Keep — syntactic lift site** | Same call IS the lift; bare `TypeName` enters, `FQTypeName` exits |
| `cranelisp_typecheck::traits::fqtn_for_bare_type_name(&self, state, &TypeName)` | `crates/cranelisp-typecheck/src/traits.rs:589` | **Keep — syntactic lift site** | The function's existence IS the lift; same as resolve |
| `cranelisp_typecheck::builtins::*(... &TypeName::from("Sexp") ...)` | `crates/cranelisp-typecheck/src/builtins.rs:552,604,664,729,929,1082,…` | **Keep — receiver-pinned with module known** | Builtins-init paths construct `&TypeName::from(...)` to register into a known-module `SymbolTable`. Receiver-pinned per exception 2. |

### backend

Smaller surface; mostly already migrated. Outstanding hits in inline-substitution table only.

| API | File:line | Direction | Owning /dev task |
|---|---|---|---|
| `primitives_inline::*(impl_type: &TypeName, …)` | `crates/cranelisp-backend/src/primitives_inline.rs:348` | PIF | /dev (backend) Wave 3 — boundary helper takes the trait-method-resolution target type; lift to `&FQTypeName` |
| `primitives_inline::*(... &TypeName::from("Int|Float|Bool|String|Color"))` (test helpers) | `crates/cranelisp-backend/src/primitives_inline.rs:425,436,449,461,472,483,494,505,516,527,538,549,560` | **Keep — reverse-lookup callsites** | All hits are test-side `TypeName::from("Int")` constructions. Test code is exempt from the resolved-stage rule (synthetic test inputs aren't products of typecheck resolution); leave as-is. |
| `cranelisp_backend::lib.rs:1200,1201,1205-1206` | `crates/cranelisp-backend/src/lib.rs:1200-1206` | **Keep — test code** | Test-internal `TypeName::from("Option")` constructions for codegen tests |

### intrinsics

No hits at the public surface (verified by grep). FQTypeName migration is a no-op for intrinsics.

### primitives

No hits at the public surface (verified by grep). FQTypeName migration is a no-op for primitives.

### platform

| API | File:line | Direction | Owning /dev task |
|---|---|---|---|
| `cranelisp_types::TypeName::from("IO")` | `src/platform.rs:426` | **Keep — reverse-lookup at primitive emission site** | Per exception 1 — `IO` is the primitive marker name; emission helpers name it directly. /dev (platform) Wave 3 verifies this is the only hit; if other primitive markers appear, same exception applies. |

### int

Mixed: REPL introspection paths (receiver-pinned; keep) and one synthetic-module init helper.

| API | File:line | Direction | Owning /dev task |
|---|---|---|---|
| `pretty.rs:128` doc comment | `src/pretty.rs:128` | n/a (comment) | none |
| `session_v4.rs:3582 — TypeName::from(type_name.name.as_ref())` | `src/session_v4.rs:3582` | **Keep — REPL introspection within known module context** | REPL `/info <type>` resolves against current module; receiver-pinned (exception 2). |
| `session_v4.rs:3671,3712 — let tn = TypeName::from(type_name)` | `src/session_v4.rs:3671,3712` | **Keep — REPL introspection** | Same as above |
| `worker.rs:173-176 — let type_params_tn: Vec<TypeName> = ...` | `src/worker.rs:173-176` | **Keep — syntactic conversion at parser boundary** | `worker::check_program_compat` converts `Vec<String>` type params from the parser into `Vec<TypeName>` — pre-resolution conversion |
| `exe.rs:544,588 — TypeName::from("IO")` | `src/exe.rs:544,588` | **Keep — reverse-lookup at exe-startup primitive registration** | Synthesises the IO type marker during startup-object generation; exception 1. |
| `pipeline.rs:345 — TypeName::from("IO")` | `src/pipeline.rs:345` | **Keep — reverse-lookup at pipeline init** | Same — synthesises IO marker during initial primitive registration |

### Summary by crate

| Crate | Convert (PIF) | Keep — frontend syntactic | Keep — receiver-pinned | Keep — reverse-lookup | Notes |
|---|---|---|---|---|---|
| typecheck | ~7 APIs | 3 (resolve, fqtn_for_bare_type_name, builtins) | ~5 (TypeCheckEnv pinned methods) | 0 | Largest /dev (typecheck) Wave 3 burden |
| backend | 1 API | 0 | 0 | ~13 (all test code) | /dev (backend) Wave 3 — single boundary helper |
| intrinsics | 0 | 0 | 0 | 0 | No-op |
| primitives | 0 | 0 | 0 | 0 | No-op |
| platform | 0 | 0 | 0 | 1 | No-op (single keep) |
| int | 0 | 1 (worker.rs parse-time) | 3 (REPL introspection) | 3 (IO marker emission) | No-op (all keeps justified by exceptions) |

Acceptance criterion (Wave 5 /review checkpoint): every API at a resolved-stage boundary uses `FQTypeName`; remaining bare `TypeName` hits MUST cite an exception by name in a code comment, e.g. `// FQTypeName exception 2 (receiver-pinned: &self IS module N)`.

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
        /// Module-local GOT slot index — **single source of truth** for the
        /// entry's runtime call address (S66 post-rollback `1dc57ae`). The
        /// GOT is owned by the module's `SymbolTable.got` and reads/writes
        /// go through `SymbolTable.got().store_slot(slot, ptr)` /
        /// `.load_slot(slot)`. No sibling `fn_ptr` / `platform_fn_ptr` /
        /// `primitive_fn_ptr` field exists — those workarounds were
        /// considered (Wave B `primitive_fn_ptr`; commit `b09ec76`'s unified
        /// `fn_ptr`) and rejected/rolled back as redundant with the GOT.
        ///
        /// A slot is allocated at registration for any **addressable
        /// callable** — user fns (JIT-built or linker-loaded), primitives
        /// (when used as values), and platform DLL fns. Origin is encoded
        /// by `kind: DefKind`:
        ///   - `DefKind::UserFn { .. }` — slot written by backend's
        ///     `compile_to_module` (JIT) or `load_object` (cache-hit `.o`);
        ///     paired with `code = Some(Code::Jit(_))` or
        ///     `Some(Code::Linker(_))`.
        ///   - `DefKind::Primitive { primitive_kind: Inline | Extern }` —
        ///     slot populated at static-init by
        ///     `cranelisp-primitives::PRIMITIVES_TABLE`; `code = None`.
        ///   - `DefKind::Primitive { primitive_kind: PlatformEffect { .. } }`
        ///     — slot populated at platform-load time from
        ///     `OwnedPlatformFnDescriptor.ptr`; `code = None` (DLL handle
        ///     held in `SharedState.kept_dlls`).
        ///
        /// `got_slot: None` indicates **non-callable, non-addressable**
        /// entries: special forms (pure syntax, no runtime address);
        /// `Overloaded` base entries (the mangled variants carry slots);
        /// `TypeDef` / `TraitDecl` / `Macro` (no callable position);
        /// constrained-fn templates (their mono specialisations carry
        /// slots).
        got_slot: Option<usize>,
        visibility: Visibility,
        docstring: Option<String>,
        /// Lifecycle owner only — `Code::Jit(Arc<Jit>)` for JIT-compiled user fns (Decision 31
        /// Scenario 2 — per-redefinition reclaim fires when the last `Arc<Jit>` clone drops),
        /// `Code::Linker(Arc<Linker>)` for cache-hit user fns. `None` for primitives (process
        /// lifetime) and platform DLL fns (DLL handle held elsewhere). **The call address is in
        /// the GOT (read via `got_slot`), not in the `Code` variant.** Decision 25 + Decision 41
        /// + Decision 35 (S66 amendment, slimmed variants).
        #[serde(skip)] code: Option<C>,
    },
    Macro { name: Symbol, clauses: Vec<MacroClauseInfo>, callees: Vec<FQSymbol>, got_slot: usize, visibility: Visibility, docstring: Option<String>, #[serde(skip)] code: Option<C> },
    TypeDef { /* … per Decision 22 */ },
    Trait { /* … */ },
    /// `(impl Trait Type method-defns…)` lands in the **trait's defining
    /// module** — keyed by the synthetic name `impl$FQTypeName$FQTraitName`.
    /// Per Decision 0045 (TraitImpl placement is the trait's defining module):
    /// neither the writer's module nor the type's defining module are mutated
    /// by the impl write; only the trait's home is. This keeps the canonical
    /// store single-sourced (Principle 7) and reduces lookup to a per-symbol
    /// chain-follow (Principle 17 — Module locality in typecheck).
    ///
    /// **Discovery.** Importers locate impls by **chain-following the trait
    /// reference** back to its defining module (per Principle 17): from the
    /// current module N's view, look up the trait — if the entry is
    /// `ModuleEntry::Import { source, … }` or `ModuleEntry::Reexport { source, … }`,
    /// follow `source.module` one edge at a time until a `ModuleEntry::Trait`
    /// entry is reached. That terminating module IS the trait's home; probe
    /// its symbol table for `impl$FQTypeName$FQTraitName`. No closure walk; no
    /// cycle detection; per-symbol point-to-point navigation only. The impl
    /// is reachable from N iff the trait is reachable from N (encoded
    /// structurally by the chain-follow's termination at the trait's home).
    ///
    /// **Always public** (spec §5.11.1: impls are visible wherever both trait
    /// and type are in scope). The `methods: Vec<Symbol>` field carries the
    /// local names of the impl's method bodies, which live as ordinary
    /// `ModuleEntry::Def` entries with mangled names (e.g.,
    /// `Display.show$Option$Int`) in the **same module** as the `TraitImpl`
    /// entry — i.e., the trait's defining module.
    TraitImpl { /* trait_name: FQTraitName, impl_type: FQTypeName, methods: Vec<Symbol> */ },
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

// `LinkerError` was previously defined here. Per Sprint 67 REV-4 it has moved
// to `cranelisp-backend` (single-consumer per Principle 15 — backend
// constructs, `int` matches; no multi-consumer pull justifies hoisting to
// types). See `facades/backend.md` §"Errors" for the canonical definition.

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

- **`Code` enum** — the per-entry lifecycle owner for compiled code (`Code::Jit(Arc<Jit>) | Code::Linker(Arc<Linker>)` per S66 — variants carry lifecycle ownership only; the per-entry call address lives **in the per-module `GotTable`**, indexed by `ModuleEntry::Def.got_slot`. The S66 unification briefly placed the address on a sibling `ModuleEntry::Def.fn_ptr` field; the `1dc57ae` rollback removed that field as redundant with the GOT — see "Symbol table — the single store" §`got_slot` doc and `crates/cranelisp-types/src/got.rs`). Lives in `cranelisp-backend/src/code.rs` (moved from `src/code.rs` per Decision 41). References `cranelisp_backend::jit::Jit` and `cranelisp_backend::cache::Linker` — neither of which `cranelisp-types` may name.
- **`JitArtefact`, `LinkerArtefact`, `ObjectArtefact`** — backend's compile_to_module / load_object / compile_to_object return shapes. Live in `cranelisp-backend`. Reference Cranelift types.
- **`PriorityWork`, `NiceWork`, `CompileScheduler`** — work item enums and the scheduler itself. Live in `int` (`src/scheduler.rs`).
- **`ProcessedForm`** — the shared `process_form` return shape. Lives in `int`. Composes a `CheckResult` (from `cranelisp-types`) with codegen-readiness info.
- **`ObjectCache`, `CacheLookupResult`, `CacheError`** — cache facade. Lives in `int` (`src/cache.rs`).
- **`EvalResult`, `EvalValue`, `CommandResult`, `SlashCommand`, `SymbolInfo`, `SymbolDescription`, `FileChangeEvent`** — REPL-side types. Live in `int`.
- **`CLType`, `CLInt`, `CLString`, `CLBool`, `CLFloat`, `CLIO<T>`, `CLHeap`, `CLOwned`, `HostContext`, `HostCallbacks`, `PlatformFn`, `OwnedPlatformFnDescriptor`, `PlatformManifest`** — platform ABI. Live in `cranelisp-platform`.

---

## Item-by-item disposition (S67 Wave 1 facade-compliance baseline)

Sprint 67 Wave 0 (`/qa`) introduced `tests/facade_compliance.rs` as the mechanical drift detector between `crates/cranelisp-types/public-api.txt` (as-built) and this facade (as-designed). Wave 1 (`/design (cranelisp-types)`) closes the orphan delta by naming every pub-api leaf below — either expanding a `/* … */` summary in the §"Public surface" blocks above, or recording the disposition here.

The facade above intentionally keeps **shape summaries** in code blocks (e.g., `pub enum Expr { /* let / fn / if / match / … */ }`) rather than enumerating every variant + field, because the variant-level surface is internal-but-exposed: consumers pattern-match on `Expr` exhaustively only inside the crates that own the lowering (typecheck, backend) and the `#[non_exhaustive]` attribute disallows cross-crate exhaustive match anyway. This section names the leaves that the compliance grep extracts so the test passes — they remain internal-but-exposed under the shape summaries above unless promoted to top-level surface by a future facade change.

### Enum variants (internal-but-exposed under shape summaries)

The variant-level surface is internal-but-exposed: every variant of every `#[non_exhaustive] pub enum` listed in §"AST", §"Resolved type system", §"Typecheck output", §"Errors and warnings", §"Source-level constructs", §"View", and §"Symbol table" is part of the public surface for pattern matching by consumer crates, but the canonical shape statement is the summary in the parent code block.

| Variant | Parent enum | Rationale |
|---|---|---|
| `Expr::Annotate`, `Expr::Apply`, `Expr::BoolLit`, `Expr::IntLit`, `Expr::FloatLit`, `Expr::StringLit`, `Expr::VecLit`, `Expr::Lambda`, `Expr::Match`, `Expr::If`, `Expr::ParBind`, `Expr::Trace` | `Expr` | Under §"AST" `pub enum Expr { /* let / fn / if / match / apply / literal / var / do / quote / quasiquote / annotate / par-bind / trace / vec-literal */ }`. Lowering crates (typecheck, backend) match on every variant; new variants are added only via /arch review. |
| `Pattern::Wildcard` (and all sibling variants) | `Pattern` | Under §"AST" `pub enum Pattern { /* literal / var / wildcard / constructor / nested */ }`. |
| `TypeExpr::SelfType` (and siblings) | `TypeExpr` | Under §"AST" `pub enum TypeExpr { /* … */ }`. `SelfType` is the `:Self` syntactic marker (resolved to the impl target type by typecheck). |
| `DefKind::SpecialForm` | `DefKind` | Under §"Symbol table" `pub enum DefKind { /* … */ }`. The `SpecialForm { description: String }` variant exists alongside `UserFn`/`Macro`/`TypeDef`/`Trait`/`Primitive`/`Overloaded` and is registered for special-form introspection (`/info`, `/list`); `description` is the user-facing one-liner. |
| `ResolvedCall::BuiltinFn` | `ResolvedCall` | Under §"Typecheck output" `pub enum ResolvedCall { TraitMethod / SigDispatch / AutoCurry / BuiltinFn }`. `BuiltinFn` is the resolved-call shape for primitive ops (`+`, `-`, `vec-push`, etc.) — pre-typecheck the call site is bare `Apply`, typecheck rewrites to `BuiltinFn` with the primitive's `cranelift_op` carrier. |
| `ResolvedCall::TraitMethod::{method_name, mangled_name, trait_resolution}`, `ResolvedCall::SigDispatch::mangled_name`, `ResolvedCall::AutoCurry::{target_name, applied_count, total_count, trait_resolution}` | `ResolvedCall` variants' fields | Per-variant payload — backend reads `mangled_name: JitSymbol` to emit the call. `trait_resolution: Option<Box<ResolvedCall>>` chains AutoCurry → TraitMethod when a curried call's underlying body is a trait method. |
| `ModuleEntry::Ambiguous` | `ModuleEntry` | Under §"Symbol table". Sentinel for the bare-name-resolves-to-multiple-imports case; typecheck emits a `TypeError` if a use site hits an `Ambiguous` entry. |
| `CranelispError::MacroError` | `CranelispError` | Under §"Errors and warnings". Emitted by `int`'s macro-expansion driver when a macro invocation fails. Same `{message, location}` shape as `ParseError`/`TypeError`/`ModuleError`/`CodegenError` per Decision 39. (Facade text §"Errors and warnings" notes `LinkError`/`CacheError`/`RuntimeError` aspirationally; source has `MacroError` instead — covered here, /arch follow-up may reconcile facade body if the divergence is structural.) |
| `LinkerError::SymbolNotFound`, `LinkerError::RelocationFailed` | `LinkerError` | **Transient — slated for removal.** Per Sprint 67 REV-4 (sprints/SPRINT.md row 5), `LinkerError` relocates to `cranelisp-backend`; see `facades/backend.md` §"Errors" for the canonical definition. The variants remain in `cranelisp-types::error` until `/dev (cranelisp-types)` removes the export sites in S67 Wave 4. After the relocation, this row deletes. |
| `WarningKind::UnusedBinding`, `WarningKind::UnreachableArm` (and siblings) | `WarningKind` | Under §"Errors and warnings" `pub enum WarningKind { UnusedDefn, UnusedImport, ShadowedName, /* … */ }`. Concrete variant set is internal-but-exposed; new variants added as detectors are implemented. |
| `View::Single`, `View::Union` | `View` | **Surface drift — substantive.** Source defines `View` as an **enum** with `Single { live }` and `Union { staging, live }` variants; the facade §"View" describes it as a `struct` with `union(…)` and `single(…)` constructors. The two shapes agree on the read surface (both expose `lookup`/`iter`/`single`/`union` as constructors), but the structural shape differs. **PIF candidate** — /arch follow-up to reconcile (either widen facade text to describe the enum, or PIF the source to a struct with internal enum). Tracked here for the compliance test; FIXME filing deferred until /arch decides direction. |

### Struct fields (internal-but-exposed under shape summaries)

The struct definitions in §"AST", §"Resolved type system", §"Symbol table", and §"Errors and warnings" include `/* … */` placeholders for fields that are not material to the cross-crate contract (e.g., per-variant payloads of enum struct-variants, internal annotation cache fields). The fields are reachable on the public surface (consumers can construct via builder methods or `Default`) but exhaustive field-by-field documentation lives in `rustdoc` on the source types. The compliance grep treats every field as a candidate name; the table below names them under the structures already cited.

| Field | Parent struct/variant | Rationale |
|---|---|---|
| `inferred_type` (on `Expr::Annotate`, `Expr::Apply`, `Expr::BoolLit`, `Expr::FloatLit`, `Expr::If`, `Expr::IntLit`, `Expr::Lambda`, `Expr::Match`, `Expr::StringLit`, `Expr::VecLit`, `Expr::Trace`, …) | `Expr` variants | Per-variant annotation cache populated by typecheck Pass 2. `Option<Box<Type>>` — `None` pre-typecheck, `Some` after `check_form`. Per Decision 22 (AST annotation) — every `Expr` variant carries this. |
| `annotation` | `Expr::Annotate` | The user-written `:Type` annotation; the syntactic counterpart to `inferred_type` (which is the resolved Type). |
| `arms`, `scrutinee`, `compiler_generated` | `Expr::Match` | `scrutinee: Box<Expr>` (matched expression), `arms: Vec<MatchArm>` (clauses), `compiler_generated: bool` (distinguishes `let`-desugaring from user `match`). |
| `then_branch`, `else_branch` | `Expr::If` | Standard if/else carriers — `Box<Expr>` each. |
| `elements` | `Expr::VecLit` | `Vec<Expr>` of the literal's elements. |
| `param_annotations` (on `Expr::Lambda`, `DefnVariant`) | `Expr::Lambda`, `DefnVariant` | Per-param optional `:Type` annotation — `Vec<Option<TypeExpr>>`. |
| `type_args`, `type_constraints` | `TraitImpl` | Polymorphic impl shape — `Vec<Symbol>` (type vars introduced by `(impl Trait (TypeCtor a b) …)`) + `Vec<(Symbol, TraitName)>` (constraints — `:Display a` etc.). |
| `type_expr` | `FieldDef` | `TypeExpr` of the constructor field (syntactic; resolved to `Type` by typecheck). |
| `default_param_names`, `hkt_param_index`, `ret_type` | `TraitMethodSig` | `default_param_names: Vec<Symbol>` (param names for use in default body); `hkt_param_index: Option<usize>` (which param is the higher-kinded "Self" for HKT traits); `ret_type: TypeExpr` (syntactic return type). |
| `body_sexp`, `fixed_params`, `rest_param` | `MacroClause`, `MacroClauseInfo` | Per-clause shape — `body_sexp: Sexp` (template), `fixed_params: Vec<MacroParam>` (positional), `rest_param: Option<Symbol>` (`&rest`-splice). |
| `is_private` | `ModDecl`, `DefmacroInfo` | Visibility flag — synonym for `visibility: Visibility::Private`; the field name reflects the underlying serialisation. |
| `inline_body` | `ModDecl` | `Option<Vec<Sexp>>` — `Some` for `(mod name forms…)` inline declarations, `None` for `(mod name)` external file references. |
| `dll_path`, `platform_module` | `ModuleEntry::PlatformDecl` | DLL path + the platform-module's `ModuleFullPath` — written at parse-time when a `(platform …)` form binds to a DLL. |
| `description` | `DefKind::SpecialForm` | One-line description for `/info` / `/list` REPL introspection (e.g., "let-binding form"). |
| `trait_origin` | `ModuleEntry::Def` | `Option<FQTraitName>` — `Some(trait_fqn)` when the entry is a method-body emitted by a `(impl Trait Type …)` form; `None` for ordinary defns. |
| `constructor_scheme` | `ModuleEntry::TypeDef` | `Option<Scheme>` — the polymorphic constructor's scheme (for parameterized ADTs like `Option a`); `None` for monomorphic ADTs. |
| `sexp` (on `ModuleEntry::Macro`, `ModuleEntry::TraitDecl`, `ModuleEntry::TypeDef`) | various `ModuleEntry` variants | `Option<Sexp>` — the original source form, retained for REPL `/sexp`, `/expand`, and source regeneration (Decision 39). |
| `jit_name` | `DefKind::Primitive` | `Option<JitSymbol>` — the mangled name a primitive registers under in the JIT's symbol table when it's used as a value (i.e., addressable). `None` for inline-only primitives. |
| `mangled_name`, `param_types`, `ret_type` | `OverloadVariant` | Resolved per-variant shape for multi-sig defns — `mangled_name: Symbol` (e.g., `foo$Int+Bool`), `param_types: Vec<Type>`, `ret_type: Type`. |
| `expr_types` | `MonoDefn` | `HashMap<Span, Type>` — the per-span annotation map for the monomorphic specialisation. Backend reads this to emit type-specialised code. |
| `target_name`, `applied_count`, `total_count`, `trait_resolution` | `ResolvedCall::AutoCurry` | Auto-curry shape — `target_name: Symbol` (which fn is being curried), `applied_count`/`total_count: usize` (arity progress), `trait_resolution: Option<Box<ResolvedCall>>` (nested resolution when the curried target is itself a trait method). |
| `codegen_names` | `CompileResult` | `Vec<Symbol>` of the symbols this batch produced code for — `int` matches against staging to know what to commit. |
| `tail_position` | `CallEdge` | `bool` — TCO discrimination on the call edge per Principle 22 (TCO over self-recursive tails). |

### Newtypes (string identifiers)

| Item | Disposition |
|---|---|
| `JitSymbol` | **PIF — promote.** `JitSymbol` is generated by `string_newtype!` alongside `Symbol`, `ModuleName`, `ModuleFullPath`, `TypeName`, `TraitName`, `LinkerSymbol`. It carries JIT-time mangled names (e.g., `Display.show$Option$Int`) before they're handed to the cache linker (where they become `LinkerSymbol`). Hoisted to §"Identifier newtypes" — see addition below. |

The §"Identifier newtypes" code block is amended to include `pub struct JitSymbol(String); // JIT-time mangled name — pre-cache; "Display.show$Option$Int" etc.` immediately above `LinkerSymbol`.

### Modules (top-level `pub mod`)

| Item | Disposition |
|---|---|
| `marshal` | **Internal-but-exposed module.** `cranelisp_types::marshal` hosts the Sexp ABI marshaling tags (`TAG_SNIL`, `TAG_SCONS`, `TAG_SEXP_INT`, …) already enumerated in §"Marshaling tags". The module is a namespace for those constants; no top-level surface promotion needed. |
| `parsed` | **Internal-but-exposed module.** `cranelisp_types::parsed` hosts `ParsedEntry` + `DefmacroInfo` + `MacroClause` (the parse-time-only transient per FIXME 0156). Already enumerated in §"`ParsedEntry`". The module is a namespace for those types. |

### Constants (offsets, sizes)

| Item | Disposition |
|---|---|
| `HeapHeader::RC_OFFSET`, `HeapHeader::ALLOC_SIZE_OFFSET`, `HeapHeader.alloc_size` | **Internal-but-exposed under §"Heap layout".** The `pub struct HeapHeader { /* total_size: u64 | rc: AtomicI64 — base-pointer convention per src/CLAUDE.md */ }` summary holds; the associated constants `RC_OFFSET` and `ALLOC_SIZE_OFFSET` are backend codegen's compile-time offset constants for emitting RC inc/dec loads. The `alloc_size` field is the heap header's own size record (used by `free` to know the original allocation size for unsized-Vec deallocation). All three are surface-stable per the base-pointer ABI (Decision 10) and consumed by `cranelisp-backend`'s codegen + `cranelisp-intrinsics`' RC primitives. |

### Free functions

| Item | Disposition |
|---|---|
| `ring0_primitives()`, `ring1_primitives()`, `ring3_primitives()` | **Internal-but-exposed under §"Operator / primitive registry".** The `pub fn primitives() -> &'static [PrimitiveDef]` in the facade text is the authoritative single registry; the three `ringN_primitives()` accessors return the per-ring subsets used by the type-checker's incremental builtins-init paths (Ring 0 = bool/int arith, Ring 1 = float + string, Ring 3 = Sexp / marshal). All three return `Vec<PrimitiveDef>` (built from the same source-of-truth list) and are consumed by `cranelisp-typecheck`'s `register_builtins` at startup. The facade's `primitives()` is the union; the per-ring accessors are conveniences. |
| `ensure_module_exists`, `install_module`, `EnsureOutcome` | **Module-lifecycle primitives** (S67 hack-back FIXME 0192). Operate on `&DashMap<ModuleFullPath, SymbolTable<C, L>>` — the data home for symbol tables. `ensure_module_exists` is the atomic check-then-insert (returns `EnsureOutcome::AlreadyPresent` or `::Created`). `install_module` is the cache-hit branch's atomic overwrite. Composed by `CompilerSession::introduce_module` (int) and `worker::try_cache_hit_load`. Replaces the pre-S67 `TypeCheckEnv::ensure_module_exists` / `restore_cached_module` methods — the data-home location of these primitives is the architectural intent (Principle 17). |
| `lookup_type_def_chain`, `lookup_trait_decl_chain`, `get_impls_for_type_chain`, `get_implementing_types_chain`, `resolve_module_by_name_chain`, `for_each_in_module`, `resolve_terminal_entry_and_home`, `CHAIN_FOLLOW_DEPTH_LIMIT` | **Chain-follow primitives** (S67 hack-back FIXME 0192 methods 1, 3, 4, 5, 7). Live-only free fns that walk `Import`/`Reexport` chains on `&DashMap<ModuleFullPath, SymbolTable<C, L>>` plus an explicit `scope: &ModuleFullPath` access root. Used by cross-crate read consumers (REPL display, `int` introspection paths). Cluster-mode consumers inside typecheck retain the staging-aware `TypeCheckEnv` methods (`lookup_type_def_in_module`, `get_impls_for_type_in_module`, etc.). The chain-follow primitives uniformly cap depth at `CHAIN_FOLLOW_DEPTH_LIMIT = 10` (spec §8.6.2). |

### Misc structs

| Item | Disposition |
|---|---|
| `ImplSexp` | **Internal-but-exposed under §"Symbol table — ModuleEntry::TraitImpl".** `pub struct ImplSexp { sexp: Sexp }` is the parse-time wrapper carrying the original `(impl Trait Type …)` source form (separate from the constructed `TraitImpl` AST). Stored alongside `ModuleEntry::TraitImpl` for source regeneration + `/sexp` introspection. Cited here for compliance; full shape lives in source rustdoc. |

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
