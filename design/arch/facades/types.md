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

### Fully-qualified references (resolved stage)

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

Used wherever a value, type, or trait reference crosses a module boundary **post-resolution**. The diagram-surfaced `process_form`, `wait_for_typecheck_symbol`, `wait_for_typecheck_type`, `priority_boost_jit`, `notify_symbol_typechecked`, `notify_inmem_codegen_complete`, `enqueue_jit` all take these.

### Syntactic-stage references (S69 Submission 27)

```rust
#[non_exhaustive]
pub struct TraitRef {
    pub module: Option<ModuleFullPath>,
    pub name: TraitName,
}

#[non_exhaustive]
pub struct TypeRef {
    pub module: Option<ModuleFullPath>,
    pub name: TypeName,
}
```

`TraitRef` and `TypeRef` are the **syntactic-stage counterparts** to `FQTraitName` and `FQTypeName`. Same structural shape (module + name) but with `Option<ModuleFullPath>` because the syntactic stage captures **what the user wrote** — including the unqualified case:

- `(impl Display ...)` / `(Option Int)` → `module: None` (resolution looks up `name` against current scope + imports at the lift site inside `check_form`)
- `(impl fmt/Display ...)` / `(option/Option Int)` → `module: Some("fmt")` / `Some("option")` (import alias; resolution dereferences the alias through the module-aliases session table to its canonical defining-module path)
- `(impl core.fmt/Display ...)` / `(core.option/Option Int)` → `module: Some("core.fmt")` / `Some("core.option")` (full path; no alias dereference needed)

Per spec §2.3.4 + §4.2.2 qualified references like `module/name` resolve via the module system; the optional `module` on `TraitRef`/`TypeRef` is the structural capture of the leading-module part of that grammar.

**Why two separate types vs. one shared shape.** `TraitRef` and `TypeRef` are not interchangeable — a `TraitRef` is the reference type used in trait-position (as the head of an `impl_form` or as a constraint), and a `TypeRef` is used in type-position (inside `TypeExpr::Named` / `TypeExpr::Applied`). The two encode the same shape but the typesystem prevents accidental cross-use. Both derive `Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize`. `Display` formats as `name` when `module: None`, `module/name` when `Some`.

**Resolution lift.** The `TraitRef → FQTraitName` and `TypeRef → FQTypeName` lifts happen inside `check_form` at the same site (the resolver consults `ref.module` to decide between alias-dereference vs. scope-lookup vs. full-path use). The lift is the consumer's responsibility, not the producer's — see §"Resolved type system" for the producer/consumer split.

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
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Span {
    pub start: u32,                                   // byte offsets — every error / warning carries one
    pub end: u32,
}

impl Span {
    pub const SYNTHETIC: Span = Span { start: 0, end: 0 };  // for compiler-generated forms
    pub fn new(start: u32, end: u32) -> Self;
    pub fn merge(self, other: Span) -> Span;
}

// `Span::default()` produces `Span { start: 0, end: 0 }` — structurally equivalent to
// `Span::SYNTHETIC` but the two roles are distinct: `SYNTHETIC` is the explicit marker
// for compiler-generated forms (read at error-formatting and trace sites); `default()`
// is for `#[serde(default)]` cache-compatibility on newly-added span fields (e.g.
// `FieldDef::span`, Submission 25 — pre-existing caches deserialise the field as the
// `Default`-derived zero span). Same value; different semantic intent.

pub enum Sexp { /* 8 variants: 5 atom kinds (Symbol/Int/Float/Bool/Str), List, Bracket, Comment — each carries Span */ }

impl Sexp {
    pub fn span(&self) -> Span;
    pub fn format_flat(&self) -> String;
    pub fn format_indented(&self, indent: usize) -> String;
}
impl Display for Sexp { /* uses format_indented(0) */ }
```

Cross-crate consumers (frontend `expand.rs`, macros, etc.) pattern-match variants directly per Principle 15 ("facade types live with their behavior"); the facade summary names the variants but leaves payload destructuring (the `(payload, Span)` tuple shape of each variant) to source rustdoc in `crates/cranelisp-types/src/sexp.rs`. The opacity policy is intentional — full variant shape is read alongside the parser/expander code that consumes it.

### AST (built by frontend, annotated by typecheck, lowered by backend)

```rust
pub enum Expr {
    // Literals (spec §4.1) — value + span + inferred_type cache (None pre-typecheck; Some after check_form).
    IntLit    { value: i64,    span: Span, inferred_type: Option<Box<Type>> },
    FloatLit  { value: f64,    span: Span, inferred_type: Option<Box<Type>> },
    BoolLit   { value: bool,   span: Span, inferred_type: Option<Box<Type>> },
    StringLit { value: String, span: Span, inferred_type: Option<Box<Type>> },

    // Variable reference (spec §4.2).
    Var { name: Symbol, span: Span, inferred_type: Option<Box<Type>> },

    // Let binding (spec §4.3) — `bindings` is the sequence of `(name, value-expr)`
    // pairs of a single `(let [n1 v1 n2 v2 …] body)` form (Cranelisp `let` is
    // sequential; later bindings see earlier ones). `body` is the let body.
    Let { bindings: Vec<(Symbol, Expr)>, body: Box<Expr>, span: Span, inferred_type: Option<Box<Type>> },

    // If (spec §4.4).
    If { cond: Box<Expr>, then_branch: Box<Expr>, else_branch: Box<Expr>, span: Span, inferred_type: Option<Box<Type>> },

    // Lambda (spec §4.5) — per spec §2.3.5 `fn_expr` the parameter list uses
    // the same syntax as `defn` (spec §2.5 `annotated_param = annotation
    // SYMBOL | SYMBOL`); each parameter carries its own optional `:Type`
    // annotation independently. Lambda's parallel-vec layout migrated to the
    // fused tuple shape in S69 Submission 24 per Principle 18 (enforce
    // invariants structurally — the lockstep invariant `params.len() ==
    // param_annotations.len()` is folded into the type) + Principle 7
    // (single source of truth — mirror of `DefnVariant`'s Submission 23
    // migration; the same semantic concept has one structural form).
    Lambda { params: Vec<(Symbol, Option<TypeExpr>)>, body: Box<Expr>, span: Span, inferred_type: Option<Box<Type>> },

    // Function application (spec §4.6). `resolved_call` is populated by typecheck
    // dispatch (None pre-typecheck; Some(Box<ResolvedCall>) after body checking).
    // Boxed to avoid bloating the Expr enum — see Decision 22 / per-crate
    // typecheck design `ast-annotation`.
    Apply { callee: Box<Expr>, args: Vec<Expr>, resolved_call: Option<Box<ResolvedCall>>, span: Span, inferred_type: Option<Box<Type>> },

    // Match (spec §4.8 + patterns spec §6). `compiler_generated` distinguishes
    // typechecker-synthesised matches (e.g., desugaring `let`/destructuring)
    // from user-written `(match …)` forms — error reporting uses this to skip
    // synthesised arms.
    Match { scrutinee: Box<Expr>, arms: Vec<MatchArm>, compiler_generated: bool, span: Span, inferred_type: Option<Box<Type>> },

    // Type annotation (spec §4.9) — `annotation` is the syntactic `:Type` form;
    // `inferred_type` carries the typechecker's resolved Type. Field order
    // matches source (annotation before expr).
    Annotate { annotation: TypeExpr, expr: Box<Expr>, span: Span, inferred_type: Option<Box<Type>> },

    // Vec literal (spec §4.10).
    VecLit { elements: Vec<Expr>, span: Span, inferred_type: Option<Box<Type>> },

    // Trace — REPL/`--run`-only implementation extension per spec §12 (runtime model).
    // `modules` is the list of module names the trace form scopes over;
    // `body` is the wrapped expression. Per Decision 40 the form is rejected
    // at compile time in `--link` mode (lives in `int`, never reaches batch lowering).
    Trace { modules: Vec<Symbol>, body: Box<Expr>, span: Span, inferred_type: Option<Box<Type>> },

    // Parallel-bind chain — produced by the bind! independence-analysis pass.
    // Semantically identical to a sequential `Let` for typecheck (bindings are
    // independent — no binding references another in the chain), but codegen
    // emits parallel IO dispatch via `IO_TAG_PAR`. Spec §10.12 (Automatic IO
    // Scheduling).
    ParBind { bindings: Vec<(Symbol, Expr)>, body: Box<Expr>, span: Span, inferred_type: Option<Box<Type>> },

    // ADT construction — language-level operation synthesised by the deftype expander.
    // See following ConstrADT doc-block for full rationale + dispatch story.
    ConstrADT { type_name: FQTypeName, tag: usize, fields: Vec<Expr>, span: Span, inferred_type: Option<Box<Type>> },
}

/// ADT construction — a language-level operation. Synthesised by the
/// deftype expander as the body expression of each constructor's `Defn`
/// (which is the `ast` of a `ModuleEntry::Def` with `kind:
/// DefKind::Constructor { .. }`; see §"Symbol table — the single store"
/// for the ctor-as-Def shape and rejected alternatives). NOT user syntax —
/// users write `(Some 42)` (an `Apply` against the constructor's name),
/// which resolves to the synthesised ctor Def whose body is this node.
///
/// Backend lowers `ConstrADT` however it chooses (inline alloc+tag+stores,
/// libcall to a runtime helper, hybrid) — backend implementation detail,
/// opaque to typecheck and to downstream AST readers.

/// Pattern in a match expression. Per spec §6.2.
///
/// Spec §6.6 explicitly excludes: literal patterns (§6.6.2), nested patterns
/// (§6.6.1), or-patterns (§6.6.3), and guarded patterns (§6.6.4). The enum
/// has three variants — `Constructor` (covering both the data §6.2.1 and
/// nullary §6.2.2 forms; nullary uses empty `bindings`), `Wildcard` (§6.2.3),
/// and `Var` (§6.2.4). The §6.2.4 disambiguation rule (bare symbol → wildcard
/// if `_`; nullary constructor if registered as such; else variable) is
/// resolved at AST-builder time.
pub enum Pattern {
    /// Constructor pattern (§6.2.1 + §6.2.2). Data form: `(Some x)`,
    /// `(Cons h t)` with non-empty bindings. Nullary form: `None`, `Red`
    /// with empty bindings. Typecheck binds each binding name to the
    /// corresponding constructor field type (exhaustiveness per §6.5);
    /// backend emits heap-cell loads at match lowering.
    Constructor { name: Symbol, bindings: Vec<Symbol>, span: Span },
    /// Wildcard `_` (§6.2.3) — matches anything; binds nothing.
    Wildcard { span: Span },
    /// Variable pattern (§6.2.4) — matches anything; binds scrutinee to `name`.
    Var { name: Symbol, span: Span },
}

/// One arm of a `match` expression — pattern + body + span. Per spec §6.1.
///
/// Spec §6.6.4 explicitly excludes guarded arms (no `when`/`if` condition
/// attached to the pattern). The body is evaluated only if the pattern
/// matches; runtime conditionals belong inside `body` via `if`. Adjacent
/// §6.6 exclusions (no nested / no literal / no or-patterns) apply to the
/// `Pattern` enum — see the `Pattern` docstring.
#[non_exhaustive]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Expr,
    pub span: Span,
}

// SYNTACTIC type expression — distinct from `Type` (the resolved-stage variant).
//
// The `Named` / `Applied` variants carry a `TypeRef` (S69 Submission 27) —
// `(Option<ModuleFullPath>, TypeName)` — capturing **as-written** qualification
// structurally (e.g. bare `Int` → `module: None`; `option/Option` →
// `module: Some("option")`). The cascade from bare `TypeName` payloads to
// `TypeRef` payloads sharpens Decision 47's producer/consumer split: the
// syntactic stage carries the qualification structurally rather than letting
// a "bare name slip through" the AST. Typecheck resolves `TypeRef.module`
// (an alias OR full path) via the import graph at the `TypeName → FQTypeName`
// lift site inside `check_form`. `head_ref(&self) -> Option<&TypeRef>` is
// a uniform accessor for the head reference on `Named` and `Applied` (`None`
// for `TypeVar`, `SelfType`, `FnType`).
pub enum TypeExpr {
    Named(TypeRef),
    Applied(TypeRef, Vec<TypeExpr>),
    TypeVar(Symbol),
    SelfType,
    FnType(Vec<TypeExpr>, Box<TypeExpr>),
}
impl TypeExpr { pub fn head_ref(&self) -> Option<&TypeRef>; }

pub enum Visibility { Public, Private }

#[non_exhaustive]
pub struct Defn { pub name: Symbol, pub variants: Vec<DefnVariant>, pub visibility: Visibility, pub docstring: Option<String>, pub span: Span }

// Fused per-param shape — each parameter carries its own `Option<TypeExpr>`
// annotation independently. Replaces the prior parallel-vec layout
// (`Vec<Symbol>` + `Vec<Option<TypeExpr>>`); the parallel-vec form carried an
// unenforced lockstep invariant (`params.len() == param_annotations.len()`)
// which Principle 18 (enforce invariants structurally) directs us to fold
// into the type. Per spec §5.1.1 EBNF (`annotated_param = colon_prefix
// symbol | symbol`) the annotation is independently optional per-param. Per
// spec §5.1 (L41) "The return type is always inferred; there is no return
// type annotation syntax" — `return_type` is deliberately absent.
#[non_exhaustive]
pub struct DefnVariant { pub params: Vec<(Symbol, Option<TypeExpr>)>, pub body: Expr, pub span: Span }

#[non_exhaustive]
pub struct ConstructorDef { pub name: Symbol, pub fields: Vec<FieldDef>, pub span: Span }

// `FieldDef` — constructor field. Per spec §2.2.6 + spec §5.2
// (`field_def = annotation SYMBOL | SYMBOL`) the field name is always present:
// both grammar productions terminate in a required `SYMBOL`. The type
// annotation is independently optional — a bare field (`SYMBOL`-only) gets
// a synthesised `TypeExpr::TypeVar` at parse time so `type_expr: TypeExpr` is
// unconditional (ADT type-resolution consumers always have a syntactic type
// to resolve; the synthesised `TypeVar` directs inference). Per Principle 7
// the producer-side name `type_expr` (vs. the prior facade text `ty`) is the
// single source of truth. Per Decision 39 (per-defn source coordinate
// system — substance manifested in §"Symbol table" of this facade and in
// `repl/spec.md` §15.4) each field carries its own `span` for "field has
// wrong type" diagnostics. Submission 25 closure on S-DRIFT-12.
#[non_exhaustive]
pub struct FieldDef { pub name: Symbol, pub type_expr: TypeExpr, pub span: Span }

#[non_exhaustive]
pub struct TraitDecl { pub name: TraitName, pub type_params: Vec<TypeName>, pub methods: Vec<TraitMethodSig>, pub visibility: Visibility, pub docstring: Option<String>, pub span: Span }

// `TraitMethodSig` — trait method signature. Per spec §5.3 EBNF
// (`required_method = '(' name docstring? '[' param+ ']' type_expr ')'`,
// `default_method  = '(' name docstring? '[' param+ ']' body ')'`,
// `param = ':' type_expr symbol | symbol`) **every** method has named
// parameters — the `param` production always terminates in a `symbol`. The
// type annotation is independently optional per-param. Per spec §5.3.1
// bare parameter names default to the implementing type; the parser
// synthesises `TypeExpr::SelfType` for bare params at parse time so
// `params: Vec<(Symbol, TypeExpr)>` is unconditional (consumers always have
// a name + a syntactic type per param). This mirrors the
// `Vec<(Symbol, Option<TypeExpr>)>` shape on `DefnVariant` (S69 Submission 23)
// and `Expr::Lambda` (S69 Submission 24); for traits the synthesised-`SelfType`
// convention collapses the `Option` — the second tuple element is always
// some `TypeExpr` (either the user-written annotation or synthesised `SelfType`).
// Per Principle 18 (enforce invariants structurally) name + annotation
// belong together on each param rather than across parallel vectors —
// the prior `default_param_names` sibling vector carried an unenforced
// lockstep invariant (`default_param_names.is_empty() == default_body.is_none()`)
// folded into the type. Names belong with the params, not with the default
// body. Per Principle 7 (single source of truth) `ret_type` (not the prior
// facade `return_type`) is canonical. `default_body: Option<Expr>` is the
// target form (vindication against source's pre-Submission-26 `Option<Sexp>`)
// — AST building catches structural errors in special forms at trait-decl
// time, per spec §5.4.5 name resolution + typecheck remain deferred (the
// trait declaration clones the `Expr` into each impl's typecheck context
// to validate against the instantiated signature). `hkt_param_index:
// Option<usize>` identifies the HKT constructor parameter per spec §5.3.2;
// HKT traits forbid default-method implementations (spec §5.3.2 + parser
// guard in `build_method_sig`). `span: Span` per Decision 39 — substance
// manifested here in §"Symbol table" + `repl/spec.md` §15.4.
#[non_exhaustive]
pub struct TraitMethodSig { pub name: Symbol, pub docstring: Option<String>, pub params: Vec<(Symbol, TypeExpr)>, pub ret_type: TypeExpr, pub span: Span, pub hkt_param_index: Option<usize>, pub default_body: Option<Expr> }

// `TraitImpl` — syntactic-stage shape (S69 Submission 27).
//
// Per spec §5.4 EBNF `impl_form` treats `target_type` as one grammatical unit
// (`target_type = qualified_symbol | '(' qualified_symbol type_arg+ ')'`).
// The unified `target: TypeExpr` field captures that unit directly — bare
// target → `TypeExpr::Named(TypeRef)`; polymorphic target → `TypeExpr::Applied`.
// The prior 6-field source-side shape (`target_type: TypeName + type_args:
// Vec<Symbol>`) split a single grammatical unit; no Decision-level grounding
// supported the split. `type_args` is no longer a separate field — type-var
// bindings introduced by the impl live structurally inside `target` (any
// `TypeExpr::TypeVar` reachable from `target` is a polymorphic-impl type var).
//
// `trait_name: TraitRef` (S69 Submission 27 — was `FQTraitName` pre-S69-S27)
// captures **as-written** qualification: `(impl Display ...)` → `module: None`;
// `(impl fmt/Display ...)` → `module: Some("fmt")`. Per spec §4.2.2 + §2.3.4
// qualified references resolve via the module system; typecheck resolves
// aliases through the import graph at the lift site, producing `FQTraitName`
// at the resolved-stage boundary per Decision 47. Same applies to `TypeRef`s
// inside `target`. `type_constraints: Vec<(Symbol, TraitRef)>` allows
// qualified trait references in constraints — `:(fmt/Display a)` — same
// `TraitRef`-uniform treatment. The resolved-stage counterpart of this
// struct is `ModuleEntry::TraitImpl { trait_name: FQTraitName, impl_type:
// FQTypeName, methods, visibility }` stored on the trait's defining module
// per Decision 45 — distinct type, FQ names throughout, post-resolution.
//
// The syntactic→resolved lift is the architectural reason both forms exist
// as distinct types; the facade names both (the AST form here under §"AST"
// and the resolved form under §"Symbol table — the single store").
#[non_exhaustive]
pub struct TraitImpl {
    pub trait_name: TraitRef,
    pub target: TypeExpr,
    pub type_constraints: Vec<(Symbol, TraitRef)>,
    pub methods: Vec<Defn>,
    pub span: Span,
}

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
    /// Parsed `(defmacro name clauses…)` form. Downstream becomes a parent
    /// `Def { kind: DefKind::Macro { clauses_meta, sexp, source } }` metadata
    /// entry plus N clause-body `Def { kind: UserFn, … }` entries under
    /// mangled names `{macro-name}$clause-{N}` — see §"Symbol table — the
    /// single store" §"DefKind" `DefKind::Macro` for the unified shape; the
    /// prior sibling `ModuleEntry::Macro` variant retired (Submission 13).
    Macro {
        info: DefmacroInfo,
    },
    /// Synthetic per-constructor entry — emitted by `build_form` for each constructor of a `TypeDef`.
    /// Pre-typecheck transient. `check_forms` lifts this into a `ModuleEntry::Def`
    /// with `kind: DefKind::Constructor { type_name, tag, field_count, internal }` and a synthesised
    /// `Defn` whose body expression is `Expr::ConstrADT { type_name, tag, fields, span }`
    /// (see §"Symbol table — the single store" for the ctor-as-Def shape).
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

**Syntactic vs. resolved partition (post-S69 Submission 27).** The syntactic stage carries as-written qualification structurally via `TypeRef` / `TraitRef`; the resolved stage carries canonical-module qualification via `FQTypeName` / `FQTraitName`. The two pairs partition cleanly across the parse → resolve boundary:

- **`TypeRef`** (syntactic stage — was bare `TypeName` pre-S69-S27) appears in positions produced by the frontend before module context is resolved: `TypeExpr::Named(TypeRef)`, `TypeExpr::Applied(TypeRef, …)`, `TraitImpl.target: TypeExpr` (and therefore any `TypeRef` reachable from it), constraint heads on impl polymorphic forms (`:(Display a)`). `TypeRef.module: Option<ModuleFullPath>` captures **what the user wrote** — unqualified (`Int`), aliased (`option/Option`), or fully-qualified (`core.option/Option`). The syntactic stage no longer carries "bare name slips through"; it carries the qualification structurally.
- **`TraitRef`** (syntactic stage — was bare `TraitName` pre-S69-S27) is the trait counterpart: `TraitImpl.trait_name: TraitRef`, `TraitImpl.type_constraints: Vec<(Symbol, TraitRef)>`. Same `Option<ModuleFullPath>` shape, same as-written capture.
- **`FQTypeName`** (resolved stage) appears in positions produced by typecheck after resolution against `&symbol_tables`: `Type::ADT(FQTypeName, …)`, `TypeDefInfo.name`, `MethodResolutions.impl_type`, `ResolutionGap::Type(FQTypeName)`, `int::wait_for_typecheck_type(fqt: &FQTypeName)`. Every cross-crate API past typecheck that names a type by identity uses `FQTypeName`.
- **`FQTraitName`** (resolved stage) — the trait counterpart: `ResolvedCall::TraitMethod { trait_name: FQTraitName, … }`, `Scheme.constraints: HashMap<TypeId, Vec<FQTraitName>>`, `ModuleEntry::TraitImpl { trait_name: FQTraitName, … }`.

The lift from `TypeRef → FQTypeName` (and `TraitRef → FQTraitName`) happens inside `check_form` when a `TypeExpr::Named(typeref)` (or the head of `TypeExpr::Applied`, or `TraitImpl.trait_name`) is resolved by consulting `typeref.module` against the import graph + current scope:

- `typeref.module == None` → resolve by name lookup against current-scope-plus-imports, find the defining module → `FQTypeName { module: <defining>, name: typeref.name }`.
- `typeref.module == Some(alias_or_path)` → resolve the alias (if any) through the session-level module-aliases table to its canonical `ModuleFullPath`, or use the full path directly → `FQTypeName { module: <canonical>, name: typeref.name }`.

This is the architectural reason the four newtypes exist as two distinct pairs: the producer (frontend) emits the syntactic pair; the consumer (typecheck onward) emits the resolved pair. The lift is the consumer's responsibility, not the producer's.

**Producer/consumer responsibility (post-S69 Submission 27).** Frontend produces `TypeExpr` carrying `TypeRef` (and `TraitImpl` carrying `TraitRef`) — the as-written qualification structurally. Typecheck consumes `TypeExpr` / `TraitImpl`, performs the lift, and produces `Type` / `TypeDefInfo` / `MethodResolutions` / `CheckResult` shapes carrying `FQTypeName` / `FQTraitName`. Backend, intrinsics, primitives, platform, and int consume only `FQTypeName` / `FQTraitName` at their public surface — no consumer past typecheck ever sees a `TypeRef` or `TraitRef` in a boundary type. Two narrow exceptions for `TypeName` (not `TypeRef`) remain, documented as principled and not extendable without `/arch` review:

1. **Reverse-lookup helpers on `Type`** — `from_name(&TypeName)` for primitive recognition and `type_name(&Type) -> Option<TypeName>` for primitive emission, which operate on the small set of built-in non-ADT types where the unqualified name IS unique.
2. **Receiver-pinned lookups** — APIs whose receiver itself supplies the module context. `SymbolTable::get_type(&TypeName)` is keyed by bare `TypeName` because the `&self` receiver IS the module; wrapping the local-to-this-table key in `FQTypeName` would re-encode information already pinned by the receiver. The fully-qualified identity is reconstructible by the caller as `FQTypeName::new(module_of(&self), name.clone())` if needed downstream. This exception is structural, not aspirational: it applies wherever the receiver's type pins the module context.

## FQTypeName migration plan (Sprint 67)

Per Sprint 67 second-challenge scope amendment (`sprints/SPRINT.md` §"Second user challenge applied"), FQTypeName binding migration (FIXME 0151) is edge drift, not interior. The facade above commits to `FQTypeName` at every resolved-stage boundary; source has not been migrated since the binding lift in S65 W2. /dev (per crate) executes the conversions in Wave 3 per the table below; /dev (typecheck) carries the largest share.

Direction discipline:
- **PIF — convert to `FQTypeName`**: API is a resolved-stage boundary and no exception applies. Wave 3 conversion.
- **Keep — frontend syntactic**: inside frontend AST/parser surface (`TypeExpr::Named(TypeRef)` and friends — post-S69 Submission 27 the AST carries `TypeRef`, not bare `TypeName`). No conversion.
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
| `cranelisp_typecheck::adt::register_type_def(name: &TypeName, …)` | `crates/cranelisp-typecheck/src/adt.rs:31,107,188,209,244,260,328,346` | Conditional per call | /dev (typecheck) Wave 3 — within-module ADT registration is receiver-pinned; cross-module ADT references via `TypeExpr::Named(TypeRef)` lift at boundary (post-S69 Submission 27 the AST carries `TypeRef`; the lift consults `typeref.module`) |
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

No hits at the public surface (verified by grep — `cranelisp-platform` crate has zero `TypeName`/`FQTypeName` references in source). FQTypeName migration is a no-op for platform.

### int

Mixed: REPL introspection paths (receiver-pinned; keep) and synthetic-module init helpers.

| API | File:line | Direction | Owning /dev task |
|---|---|---|---|
| `pretty.rs:128` doc comment | `src/pretty.rs:128` | n/a (comment) | none |
| `session_v4.rs:3582 — TypeName::from(type_name.name.as_ref())` | `src/session_v4.rs:3582` | **Keep — REPL introspection within known module context** | REPL `/info <type>` resolves against current module; receiver-pinned (exception 2). |
| `session_v4.rs:3671,3712 — let tn = TypeName::from(type_name)` | `src/session_v4.rs:3671,3712` | **Keep — REPL introspection** | Same as above |
| `worker.rs:173-176 — let type_params_tn: Vec<TypeName> = ...` | `src/worker.rs:173-176` | **Keep — syntactic conversion at parser boundary** | `worker::check_program_compat` converts `Vec<String>` type params from the parser into `Vec<TypeName>` — pre-resolution conversion |
| `exe.rs:544,588 — TypeName::from("IO")` | `src/exe.rs:544,588` | **Keep — reverse-lookup at exe-startup primitive registration** | Synthesises the IO type marker during startup-object generation; exception 1. |
| `pipeline.rs:345 — TypeName::from("IO")` | `src/pipeline.rs:345` | **Keep — reverse-lookup at pipeline init** | Same — synthesises IO marker during initial primitive registration |
| `platform.rs:426 — TypeName::from("IO")` | `src/platform.rs:426` | **Keep — reverse-lookup at primitive emission site** | Synthesises the IO type marker; exception 1. (Lives in the `src/` int binary, not in `crates/cranelisp-platform/`.) |

### Summary by crate

| Crate | Convert (PIF) | Keep — frontend syntactic | Keep — receiver-pinned | Keep — reverse-lookup | Notes |
|---|---|---|---|---|---|
| typecheck | ~7 APIs | 3 (resolve, fqtn_for_bare_type_name, builtins) | ~5 (TypeCheckEnv pinned methods) | 0 | Largest /dev (typecheck) Wave 3 burden |
| backend | 1 API | 0 | 0 | ~13 (all test code) | /dev (backend) Wave 3 — single boundary helper |
| intrinsics | 0 | 0 | 0 | 0 | No-op |
| primitives | 0 | 0 | 0 | 0 | No-op |
| platform | 0 | 0 | 0 | 0 | No-op (zero hits) |
| int | 0 | 1 (worker.rs parse-time) | 3 (REPL introspection) | 4 (IO marker emission) | No-op (all keeps justified by exceptions) |

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

    /// Arity of a function type. Returns `Some(params.len())` for
    /// `Type::Fn(params, _)`; `None` for all other variants
    /// (primitives, ADTs, Var, TyConApp). Self-contained on `Type`
    /// data — no other inputs.
    ///
    /// This is the data-owning accessor for "how many arguments does this
    /// callable take?" — `Type` (more precisely `Type::Fn`'s `params` Vec)
    /// is the canonical home for arity information at the resolved-stage
    /// boundary. Consumers that previously read a separately-stored arity
    /// count (e.g., a name-list on the entry whose `.len()` was the only
    /// thing read) MUST migrate to this accessor; see
    /// `ModuleEntry::arity()` below for the entry-level delegation.
    pub fn fn_arity(&self) -> Option<usize>;
    /* … */
}

#[non_exhaustive]
pub struct Scheme {
    pub type_vars: Vec<TypeId>,
    pub constraints: HashMap<TypeId, Vec<FQTraitName>>,       // bound trait constraints per var (Decision 47: FQ at resolved-stage boundaries)
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

**Module aliases live at session level, not on `SymbolTable`.** `SymbolTable` holds a single per-key store — `symbols: DashMap<Symbol, ModuleEntry<C>>` for value/type/trait bindings. The module-path-namespace aliases introduced by §8.3.4 (import alias) and §8.4.4 (export mount) live in a **parallel session-level table** `ModuleAliases = DashMap<ModuleFullPath, ModuleAliasEntry>`, keyed by the alias's **full path** (e.g., key `m.n.str` for an alias named `str` declared inside module `m.n`). This shape replaces an earlier per-module-segment `SymbolTable.aliases: DashMap<ModuleName, ModuleAliasEntry>` field that was authored and retracted in the same sprint: aliases are not symbols (they name parts of a module path, not value bindings), and keying by full path lets §8.6.6 resolution do a single-table longest-prefix-match against the queried `module_path` rather than segmenting and walking per-module alias sub-tables. The owning module of any alias entry is **derived from the key** (strip the last dot-separated segment, e.g., key `m.n.str` → owner `m.n`); it is not stored on `ModuleAliasEntry`. Newtype discipline at the API surface: both `SymbolTables` and `ModuleAliases` are keyed by `ModuleFullPath`; the `symbols` DashMap inside each `SymbolTable` is keyed by `Symbol`. Three keying domains — `ModuleFullPath` (module / alias path), `Symbol` (in-module binding), `TypeName` (receiver-pinned ADT lookup) — three newtypes, no conflation.

**Qualified-name resolution algorithm per `spec/08-modules.md` §8.6.6.** A qualified name has the form `module_path/local_name` with exactly one `/` (per §1.4.3); `module_path` is dot-separated. Resolution walks the dot-separated segments of `module_path`, generating the sequence of prefixes from longest to shortest, and queries both session-level tables for each prefix in parallel:

```rust
for prefix in path.prefixes_descending() {
    if let Some(st)  = symbol_tables.get(prefix)  { /* hit module → proceed */ }
    if let Some(ent) = module_aliases.get(prefix) { /* hit alias → substitute */ }
}
```

The first hit wins. If it's an alias entry:
- Derive owner = prefix - last segment (e.g., key `m.n.str` → owner `m.n`).
- Visibility filter: if `entry.visibility == Private` AND `owner != current_module`, treat as miss and continue the prefix walk (private import aliases per §8.3.4 are not visible to external resolutions).
- Otherwise substitute `entry.target` for the matched prefix + remaining tail, restart with the rewritten `module_path`.

If it's a module entry: proceed to symbol lookup (single `/` boundary reached; `local_name` looked up against the resolved module's `symbol_table.symbols`).

**Per-entry visibility filter on cross-module slot resolution.** Every `ModuleEntry` variant carries `visibility: Visibility` (visibility is an orthogonal axis to entry kind — see §"Visibility" enum below + §"Rejected alternatives — per-entry visibility" further down). On slot hit during cross-module resolution (i.e., looking up `local_name` against another module's `symbols`):

```
if entry.visibility == Private AND lookup_origin != entry_module {
    treat as miss; continue
}
// else proceed: chain-follow for Import; symbol payload otherwise
```

Same-module lookup skips the visibility check (passes trivially). The `/exports M` REPL command = filter `SymbolTables[M].symbols` for `entry.visibility == Public`; no separate exports-set iteration. The check applies uniformly across `Def` (including `DefKind::Macro` parent entries and their `{macro}$clause-{N}` mangled-variant `UserFn` Def bodies), `TypeDef`, `TraitDecl`, `Import`, `TraitImpl`, `Ambiguous` — `TraitImpl` is constructed `Public` per §5.11.1 (lossless mark); `Ambiguous` is `Public` as a sentinel.

Chain-follow depth limit per §8.6.2 (`CHAIN_FOLLOW_DEPTH_LIMIT = 10`). Newtype boundary preserved at the API surface: `symbol_tables` keyed by `ModuleFullPath`; alias entries keyed by `ModuleFullPath` (same newtype); the `symbols` DashMap inside each `SymbolTable` keyed by `Symbol`. Three keying domains, three newtypes, no conflation.

**In-sprint /dev brief — session-level table cascade.** The concurrency-cluster /dev brief that lands the source side of this facade move now includes:

- **Construction.** A `module_aliases: ModuleAliases` field is added to `SharedState` (`facades/int.md` §"SharedState") alongside `symbol_tables: SymbolTables<Code, ()>`. Constructed empty at session init; lives for the session lifetime, interior-mutable like the symbol-tables map.
- **Parse-time write — import alias.** When an `ImportSpec` carries `alias.is_some()`, the parse-time installer writes a `ModuleAliasEntry` into `session.module_aliases` at key `owner_path + "." + alias_name` with `visibility = Visibility::Private` per §8.3.4.
- **Parse-time write — export mount.** When an `ExportSpec` carries `alias.is_some()`, the parse-time installer writes a `ModuleAliasEntry` into `session.module_aliases` at the same key shape with `visibility = Visibility::Public` per §8.4.4.
- **Resolver.** Qualified-name resolution per §8.6.6 walks `module_path` prefixes from longest to shortest, querying both `symbol_tables` and `module_aliases` in parallel; first hit wins; visibility filter applied on alias substitution; chain-follow depth capped at `CHAIN_FOLLOW_DEPTH_LIMIT`.
- **Cross-table mount-vs-submodule conflict check.** Atomic at insert time: writing into either table queries the other for the same `ModuleFullPath` key and rejects if present (invariant 8 third bullet below).

```rust
/// Marker trait for the `D` (DLL handle) parameter on `SymbolTable`.
/// Parallel to `CodeStore` and `LinkerStore`. The unit type is the
/// default — `SymbolTable<C, L>` (with `D = ()`) for crates that never
/// load platforms (frontend, typecheck, the bulk of backend). The
/// integration layer instantiates `SymbolTable<Code, (), Dll>` on the
/// platform-module slot specifically (per spec §8.9.3 — `(platform
/// stdio)` registers a synthetic module at `symbol_tables["platform.stdio"]`
/// whose own SymbolTable retains the loaded DLL).
pub trait DllStore: Send + Sync + 'static {}
impl DllStore for () {}

#[non_exhaustive]
pub struct SymbolTable<C: CodeStore = (), L: LinkerStore = (), D: DllStore = ()> {
    // populated form-by-form during typecheck — per-entry mutation via inner DashMap.
    // Module aliases (§8.3.4 / §8.4.4) live at session level in the parallel
    // `ModuleAliases` table (see typedef below), keyed by the alias's full path.
    // They are NOT a SymbolTable field — aliases name parts of a module path,
    // not value/type/trait bindings.
    pub symbols: DashMap<Symbol, ModuleEntry<C>>,
    pub got: Arc<GotTable>,
    pub next_got_slot: AtomicUsize,
    /// Monotonic per-entry sequence allocator — every newly-inserted `ModuleEntry::Def`
    /// receives `seq = next_seq.fetch_add(1)`. Used by `regenerate_backing_file` to
    /// emit defns in authorship order per `repl/spec.md` §15.4(2). Redefinition does
    /// NOT reorder: `insert_or_update` preserves the existing entry's `seq` value
    /// (alongside Decision 41's `code` carry-forward), so a defn keeps its original
    /// position across REPL redef. Replaces the prior `defn_order: Vec<Symbol>`
    /// side-table — peer of `next_got_slot`, same allocation discipline.
    pub next_seq: AtomicU64,

    // structural decls (Decision 33) — written by write_structural_decls at
    // parse-time; REPL appends via append_structural_decl. `regenerate_backing_file`
    // emits the four sections at the top of the regenerated file in the fixed
    // order required by `repl/spec.md` §15.4(4): platforms, submodules, exports,
    // imports — then defns follow, sorted by `seq` per §15.4(2).
    pub imports: Vec<ImportSpec>,
    pub exports: Vec<ExportSpec>,
    pub platforms: Vec<PlatformSpec>,
    pub submodules: Vec<ModDecl>,

    pub path: ModuleFullPath,
    pub schema_version: u32,                  // Decision 34 — bumped on serialised-shape change
    /// DLL handle for platform-module SymbolTables. Spec §8.9.3:
    /// `(platform stdio)` registers a synthetic module named
    /// `platform.stdio`; the loaded DLL handle lives on **that
    /// SymbolTable's own** `dll` field — co-located with the platform
    /// module's `symbols` (which carry `platform_fn_ptr` populated
    /// from `dlsym` at load time). `None` for all non-platform modules
    /// (the bulk of `symbol_tables`); `Some(dll)` only for entries
    /// keyed `platform.<name>`. Drop semantics: when this SymbolTable
    /// is dropped, the DLL handle drops with it — so every
    /// `platform_fn_ptr` on a Def in `symbols` is valid for exactly
    /// the SymbolTable's lifetime.
    ///
    /// Parallel to `linker: Option<L>` (whose docstring lives on
    /// `SymbolTable<C, L>`'s pre-existing `LinkerStore` field): both
    /// are lifecycle-owner slots for runtime state attached to one
    /// module's address space. `#[serde(skip)]` — runtime state, not
    /// part of the cached module shape; re-populated on cache-hit by
    /// re-loading the platform DLL.
    ///
    /// `ModuleEntry::PlatformDecl` is retired — see the `PlatformDecl`
    /// retirement note on `ModuleEntry` below. The DLL handle is no
    /// longer carried as a per-entry record inside another module's
    /// table; it lives here, on the platform module's own SymbolTable,
    /// per spec §8.9.3 (platforms are modules of their own, not
    /// entries within other modules).
    #[serde(skip)]
    pub dll: Option<D>,
    _phantom_l: PhantomData<L>,
}

impl SymbolTable {
    pub fn new(path: ModuleFullPath) -> Self;                                                      // SymbolTable<(), (), ()>
}

impl<C: CodeStore, L: LinkerStore, D: DllStore> SymbolTable<C, L, D> {
    // ────── Phase 0 — brief [&mut SymbolTable] window at parse-time ──────
    /// Called once per module at parse-time, when the module is initialised from
    /// a file source. The integration layer holds a brief RefMut from
    /// `Sess.symbol_tables.entry(m).or_default()` and populates the four
    /// structural Vec fields (`imports` / `exports` / `platforms` / `submodules`)
    /// in one shot. After this returns, the RefMut drops and the SymbolTable is
    /// reachable only via shared `.get(m)` shard-read locks.
    ///
    /// File-modules-only initialisation. REPL-entered structural forms
    /// (`(import …)` / `(export …)` / `(declare-platform …)` / `(mod …)`
    /// typed at the prompt) use `append_structural_decl` instead — this
    /// method is the bulk-load shape for parsed file contents.
    pub fn write_structural_decls(&mut self, decls: StructuralDecls);

    /// REPL append path — extends the appropriate structural Vec with one new
    /// entry. Used for `(import …)` / `(export …)` / `(declare-platform …)` /
    /// `(mod …)` forms entered interactively. File-loaded modules use
    /// `write_structural_decls` instead. Brief per-eval RefMut hold
    /// (microseconds). One enum-carrier method — no parallel per-section
    /// append methods.
    pub fn append_structural_decl(&mut self, entry: StructuralDeclEntry);

    // ────── Per-entry mutation — [&self] under inner DashMap per-key locks ──────
    pub fn get(&self, sym: &Symbol) -> Option<Ref<'_, Symbol, ModuleEntry<C>>>;
    /// Insert a new entry or update an existing one for `sym`. On update,
    /// preserves the existing entry's `seq` value (alongside the `code`
    /// carry-forward per Decision 41) — a redefined defn keeps its original
    /// authorship position in regenerated source. On insert, the caller is
    /// expected to have allocated `seq` via `next_seq.fetch_add(1)` before
    /// constructing the `ModuleEntry::Def`.
    pub fn insert_or_update(&self, sym: Symbol, entry: ModuleEntry<C>);                             // Decision 41 — `code` carry-forward; `repl/spec.md` §15.4(2) — `seq` carry-forward (defn keeps original authorship position across redef)
    pub fn write_code(&self, sym: &Symbol, code: C);                                                // Decision 41 — atomic GOT swap on update
    pub fn allocate_got_slot(&self) -> usize;                                                       // monotonic, atomic
    /// Adds bare-name Import-variant entries to the inner symbols DashMap so that
    /// resolved-import names can be looked up via `get(sym)`. Per the per-symbol
    /// mutability discipline this is `&self` — writes go through the inner
    /// DashMap's per-entry write locks. Imports are installed during the form
    /// loop (when each `(import …)` form is processed by check_form), NOT at
    /// Phase 0.
    pub fn install_import_bindings(&self, from: &ModuleFullPath, names: ImportNames);

    // ────── Read-only iteration ──────
    pub fn public_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry<C>)>;
    pub fn defined_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry<C>)>;              // Decision 22 — codegen-compilable predicate
    pub fn all_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry<C>)>;
    pub fn get_type(&self, name: &TypeName) -> Option<Ref<'_, Symbol, ModuleEntry<C>>>;             // receiver-pinned exception — &self IS the module context (see §"Resolved type system" exception 2). Same return shape as `get()` — type-keyed (TypeName not Symbol) + variant-filtered (Some only when entry is `ModuleEntry::TypeDef { … }`). `TypeDefInfo` is not promoted to facade-tier; callers extract via `if let ModuleEntry::TypeDef { info, .. } = &*entry { … }`, same idiom as other variants.

    // Module-alias access has been REMOVED from `SymbolTable`. Aliases live
    // in the session-level `ModuleAliases` table (see typedef below) and are
    // looked up directly against it by full path. See §"Symbol table — the
    // single store" narrative above + the cross-table conflict rules in
    // bounded-context invariant 8.
}

/// Session-level per-module SymbolTable storage. Parallel to `ModuleAliases`;
/// see the qualified-name resolution algorithm in §"Symbol table — the single
/// store" above. Materialised here (not just spelled out at every use site)
/// per the S69 audit F-1 disposition (`facades/cranelisp-typecheck-audit-s69.md`):
/// pub-api projection names the alias mechanically and the facade-compliance
/// test can grep-match against it. The integration layer's `SharedState`
/// (see `facades/int.md` §"SharedState") instantiates this as
/// `SymbolTables<Code, ()>`; tests / fine-grained drivers use
/// `SymbolTables<(), ()>`.
pub type SymbolTables<C, L, D = ()> = DashMap<ModuleFullPath, SymbolTable<C, L, D>>;

/// Session-level module-alias storage — parallel to `SymbolTables<C, L>`,
/// keyed by `ModuleFullPath` so resolution per `spec/08-modules.md` §8.6.6
/// uses single-table longest-prefix-match. Both `m.n.aliases.get(a)` and
/// `session.module_aliases.get(m.n.a)` would conceptually return the same
/// entry; this is the storage shape that wins on resolver simplicity (no
/// per-module segmentation needed during the prefix walk).
///
/// Owning module for any alias entry at key `K` is derived as `K` minus its
/// last dot-separated segment (e.g., key `m.n.str` → owner `m.n`). The
/// owner field is NOT stored on `ModuleAliasEntry` to avoid representation
/// redundancy. Visibility filtering for external consumers (per §8.4.4
/// public mounts vs §8.3.4 private import aliases) compares the derived
/// owner against the resolution's `current_module`.
pub type ModuleAliases = DashMap<ModuleFullPath, ModuleAliasEntry>;

/// One row in the session-level `ModuleAliases` table. Written at parse-time
/// when an `ImportSpec` or `ExportSpec` carries `alias.is_some()` — see
/// §"Cross-module structural specs" below for the form-record → alias-table
/// flow. The entry is keyed in `ModuleAliases` by the alias's **full path**
/// (`owner_path + "." + alias_name`); the owning module is derived from the
/// key by stripping the last dot-separated segment and is NOT stored on this
/// struct. Per spec §8.3.4 + §8.4.4 + §8.6.6.
#[non_exhaustive]
pub struct ModuleAliasEntry {
    /// §8.3.4 / §8.4.4 — the module this alias points at. Resolution per §8.6.6
    /// substitutes this `ModuleFullPath` for the matched alias prefix in
    /// `module_path`, then restarts resolution on the rewritten path.
    pub target: ModuleFullPath,
    /// `Private` for §8.3.4 import-side alias (local to the importing module —
    /// does not escape via the public surface); `Public` for §8.4.4 export-side
    /// mount (visible to downstream importers whose §8.6.6 resolution probes
    /// the session-level `ModuleAliases` for keys under another module's owner).
    /// The visibility filter compares the derived owner (key minus last
    /// dot-separated segment) against the resolution's `current_module`.
    pub visibility: Visibility,
    /// Span of the `(module alias)` pair in source, for diagnostics + source
    /// regeneration. The form-record on `SymbolTable.imports` / `.exports`
    /// retains the authoritative source shape; the `span` here pins the
    /// per-entry source location for "duplicate mount alias" /
    /// "mount-vs-submodule collision" error pointing per §8.6.4.
    pub span: Span,
}

/// Per-entry visibility carrier — appears on every `ModuleEntry` variant,
/// on `ModuleAliasEntry`, and on form-level constructs (`Defn`, `TraitDecl`,
/// `ModDecl`, `ImportSpec`, `ExportSpec`). (The retired `PlatformDecl`
/// variant was always-discoverable-by-construction and had no visibility
/// field; it no longer exists — see retirement note on `ModuleEntry` and
/// the platform-module shape on `SymbolTable.dll`.)
///
/// **Source**: `crates/cranelisp-types/src/ast.rs:263`.
/// **Derives**: `Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize`.
/// Notably NOT `Hash` — visibility never appears as a map key; consumers
/// compare by equality.
///
/// **Consumers**: `ModuleEntry.visibility` on every variant (the cross-module
/// resolution visibility-filter); `ModuleAliasEntry.visibility` (the
/// alias-substitution visibility-filter per §8.6.6); `ImportSpec.visibility`
/// and `ExportSpec.visibility` form-records (source-level provenance for
/// `.cl` regeneration); the `is_public()` accessor on `ModuleEntry`; the
/// `/exports M` REPL command (filter `Public` entries on a module's
/// `symbols`).
///
/// Visibility is an orthogonal axis to entry kind (one field, not a sibling
/// variant); see §"Rejected alternatives — per-entry visibility" below.
pub enum Visibility { Public, Private }
```

**Rejected alternatives — session-level path-keyed `ModuleAliases` table** (load-bearing for future re-litigation of the `ModuleAliasEntry` storage shape):

- **Per-module `aliases: DashMap<ModuleName, ModuleAliasEntry>` field on `SymbolTable`** — initially landed in this facade during the S69 walk-through, then retracted. Rejected on: (1) module aliases are not symbols and not module-name-keyed-within-module — they name parts of a module path; the per-module shape violated newtype discipline by mixing `Symbol`/`ModuleName` keying domains within one struct; (2) resolver becomes a per-module-segmentation walk instead of a single-table prefix walk against `ModuleAliases`.
- **Bundled `ModuleSpace<C, L>` struct holding both tables, single parameter through APIs.** Rejected on: (1) bigger migration churn — every consumer's signature changes shape rather than gains a parameter; (2) violates Principle 2 narrowness — consumers that don't resolve qualified names (e.g., backend's `defined_symbols` iteration) acquire alias-resolution capability they don't use; (3) doesn't close audit F-1 cleanly — the `&SymbolTables<C, L>` typedef adoption is an in-flight migration that naturally absorbs the parallel `&ModuleAliases` typedef.
- **Explicit `owner: ModuleFullPath` field on `ModuleAliasEntry`.** Rejected per Principle 7 — derivable data should not be persisted alongside its derivation source; risks drift between the stored field and the key. Recovery via deterministic strip-last-segment is O(1) and matches spec §8.3.4 / §8.4.4 grammar (alias names are always single segments).
- **Unified `module_nodes: DashMap<ModuleFullPath, ModuleNode>` where `ModuleNode = Module(SymbolTable) | Alias(entry)`.** Rejected on: (1) every iteration that wants "all modules" filters on the variant — cost on hot paths; (2) breaks the `SymbolTables<C, L>` typedef pattern in flight per audit F-1; (3) variance with generic parameters becomes more entangled (`ModuleNode<C, L>` carries C/L but only the Module variant needs them).

**Rejected alternatives — per-entry visibility on `ModuleEntry`** (load-bearing for future re-litigation of the `Import`/`Reexport` collapse + the per-entry `visibility` field):

- **Narrow disposition — keep `Reexport` as a sibling variant.** The original U2 disposition in `types-audit-s69.md`. Rejected on: encodes visibility via variant proliferation rather than as an orthogonal axis; misses the symmetry with `ModuleAliasEntry.visibility` and `DefKind::Constructor` (both expressing kind-discriminators-on-an-entry rather than sibling-variants); leaves exports-set duplication in place where it exists. The variant collapse simplifies cross-module resolution (one `Import` arm regardless of edge provenance) without losing the public/private distinction (now on `visibility`).
- **`Visibility` as wrapper at the slot — `DashMap<Symbol, (Visibility, ModuleEntry<C>)>`.** Adds a layer at lookup; less DRY than per-entry field; doesn't match the per-entry pattern on `ModuleAliasEntry`. Rejected on Principle 2 / Principle 7 grounds.
- **Keep exports-set on SymbolTable; no per-entry visibility field.** Two sources of truth (entry kind + exports set); doesn't generalise to `ModuleAliasEntry`, which already needs per-entry visibility. Rejected on Principle 7.
- **Promote visibility per-entry but keep `Reexport` variant.** Internally inconsistent — visibility on the entry would duplicate what the variant name encodes. Rejected on Principle 7.

**Two complementary stores, two purposes** — the form-record on `SymbolTable.{imports,exports}` is NOT the same thing as per-entry `visibility` on `ModuleEntry`:

- **`SymbolTable.imports: Vec<ImportSpec>` and `SymbolTable.exports: Vec<ExportSpec>`** are **form-records**: append-only, source-order, only user-authored forms. They are the source-of-truth for `.cl` regeneration (`repl/spec.md` §15.4), duplicate-form warnings, and form-by-form parse-time classification. The form-record records *what the user wrote*.
- **Per-entry `visibility: Visibility` on `ModuleEntry`** is the source-of-truth for visibility decisions: used by cross-module resolution's visibility-filter step and by the `/exports M` REPL command. Per-entry visibility records *the effect on each symbol* — one symbol per `ModuleEntry` slot, with its own visibility.

Both are load-bearing; neither retires the other. A `(export [a b c])` form persists one `ExportSpec` row in the form-record and toggles `visibility = Public` on the three corresponding `ModuleEntry` slots; a `(import …)` form similarly persists an `ImportSpec` row and installs per-entry `Import { visibility: Private, .. }` bindings. The two stores stay structurally consistent by parse-time installer convention — the form-record drives `.cl` regeneration; per-entry visibility drives resolution.

```rust
#[non_exhaustive]
pub struct StructuralDecls {
    pub imports: Vec<ImportSpec>,
    pub exports: Vec<ExportSpec>,
    pub platforms: Vec<PlatformSpec>,
    pub submodules: Vec<ModDecl>,
}

/// REPL append-path carrier — one variant per structural Vec on `SymbolTable`.
/// Consumed by `append_structural_decl`. Per `repl/spec.md` §15.4: structural
/// forms entered at the prompt extend the corresponding section in authorship
/// order (no dedup, mirroring `write_structural_decls`'s file-load discipline).
#[non_exhaustive]
pub enum StructuralDeclEntry {
    Import(ImportSpec),
    Export(ExportSpec),
    Platform(PlatformSpec),
    Mod(ModDecl),
}

```

#### Multi-legged authoring

**Multi-legged authoring forms.** Some declarations author multiple `Def` entries from a single source form. The parent metadata `Def` carries the authored form; synthesized sub-entries derive from it.

| Source form | Parent metadata `Def` | Synthesized sub-entries |
|---|---|---|
| `(defn name ([sig-1] body-1) ([sig-2] body-2))` (multi-sig) | `Def { kind: Overloaded { variants, sexp, source } }` | One `Def { kind: UserFn, ast, code }` per variant, mangled name (e.g., `add$Int+Int`) |
| `(defmacro name [pat-0] body-0 [pat-1] body-1)` | `Def { kind: Macro { clauses_meta, sexp, source } }` | One `Def { kind: UserFn, ast, code }` per clause body, mangled name `{name}$clause-{N}` |
| `(deftype (Name a) Ctor-0 Ctor-1)` | `Def { kind: TypeDef { …, sexp, source } }` *(target — pending sibling-variant unification, parallel to D49 + Macro)* | One `Def { kind: Constructor, ast, code }` per constructor (D49) |
| `(deftrait Name methods…)` | `Def { kind: Trait { methods, sexp, source } }` *(target — pending sibling-variant unification)* | Methods stored per D45 (TraitImpl placement) |

**`sexp` + `source` live on the parent metadata `DefKind` variant; not on synthesized sub-entries.** The authoring unit is the whole form, even when storage emits multiple entries. REPL `/source name` resolves through the parent metadata if a sub-entry is named (e.g., `/source thread-first$clause-0` resolves to the parent `thread-first`'s form); `/sexp` and `/expand` likewise. `ast` and `code` are sub-entry concerns — each clause body, constructor body, or multi-sig variant body has its own.

For single-legged forms (`(defn add [x y] …)` → one `Def { kind: UserFn }`), the parent IS the only entry; whether it carries `sexp` + `source` at the metadata level (vs. relying on the REPL `DefEntry` sidecar) is open — addressed when a `/source`-style consumer requires it.

```rust
#[non_exhaustive]
pub enum ModuleEntry<C: CodeStore = ()> {
    Def {
        name: Symbol,
        kind: DefKind,
        scheme: Option<Scheme>,
        ast: Option<Expr>,                           // Decision 22 — codegen-compilable iff Some
        callees: Vec<FQSymbol>,                      // Decision 21 — TC-sourced call graph
        /// Per-entry monotonic ordering token, allocated via
        /// `SymbolTable::next_seq.fetch_add(1)` at first registration. Used by
        /// `regenerate_backing_file` to emit defns in authorship order per
        /// `repl/spec.md` §15.4(2). On redefinition, `insert_or_update`
        /// preserves the existing `seq` value (alongside the `code`
        /// carry-forward per Decision 41), so a defn keeps its original
        /// authorship position across REPL redef — principle of least surprise.
        seq: u64,
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
        ///     `cranelisp-primitives::PRIMITIVES_TABLE`;
        ///     `code = Some(Code::Primitive)` (marker variant per Decision
        ///     0048 (A2, revised 2026-05-17) — no payload; lifecycle is
        ///     process-static, owned by the `LazyLock`).
        ///   - `DefKind::Primitive { primitive_kind: PlatformEffect { .. } }`
        ///     — slot populated at platform-load time from
        ///     `OwnedPlatformFnDescriptor.ptr`; `code = None` (DLL handle
        ///     held in `SharedState.kept_dlls`).
        ///
        /// `got_slot: None` indicates **non-callable, non-addressable**
        /// entries: special forms (pure syntax, no runtime address);
        /// `Overloaded` base entries (the mangled variants carry slots);
        /// `TypeDef` / `TraitDecl` / `Macro` parent entries (no own
        /// callable position — `DefKind::Macro` parent metadata has no
        /// body; its per-clause mangled-variant `UserFn` Defs carry the
        /// slots); constrained-fn templates (their mono specialisations
        /// carry slots).
        got_slot: Option<usize>,
        visibility: Visibility,
        docstring: Option<String>,
        /// Lifecycle owner only — `Code::Jit(Arc<Jit>)` for JIT-compiled user fns (Decision 41 —
        /// per-symbol-immediate redefinition reclaim fires when the last `Arc<Jit>` clone drops;
        /// formerly Decision 31 Scenario 2, retired with substance amended into D41),
        /// `Code::Linker(Arc<Linker>)` for cache-hit user fns, `Code::Primitive` for primitives
        /// (marker variant; no payload; lifecycle is process-static, owned by the `LazyLock`
        /// in `cranelisp-primitives` — Decision 0048 (A2, revised S68 Phase 3)). `None` for
        /// platform DLL fns (DLL handle held elsewhere). **The call address is in the GOT
        /// (read via `got_slot`), not in the `Code` variant.** Decision 25 + Decision 41 +
        /// Decision 35 (S66 amendment, slimmed variants) + Decision 0048 (S68 Phase 3 revision).
        #[serde(skip)] code: Option<C>,
    },
    // **Storage detail (Def).** Source currently carries an additional
    // `param_names: Vec<Symbol>` on `Def` for historical reasons; only
    // `.len()` and `.is_empty()` are read by the two active consumers
    // (backend cross-module arity lookup at
    // `crates/cranelisp-backend/src/compiler/mod.rs:153` `arity_in_module`;
    // zero-arg `test-*` discovery filter at `src/session_v4.rs:4787`). The
    // accessor `ModuleEntry::arity()` (impl block below) encapsulates this
    // — consumers never reach into the field. The field is marked for
    // cleanup in the in-sprint `/dev` concurrency-cluster wave-3 brief
    // (delete after consumer migration; arity derives from `scheme.ty`
    // via `Type::fn_arity()`).
    // `ModuleEntry::Macro` variant retired — macros are now
    // `Def { kind: DefKind::Macro { clauses_meta, sexp, source } }`,
    // parallel to D49's `Def { kind: Constructor }` migration and the
    // multi-sig fn `Def { kind: Overloaded }` pattern. See `DefKind::Macro`
    // below (§"DefKind") for the full shape, the per-clause-body storage
    // discipline (`{macro-name}$clause-{N}` mangled-variant Defs), and
    // the dispatch story (expansion-time walk over `clauses_meta` → GOT
    // dispatch on the matched clause's variant Def). `MacroEnv` sidecar
    // retires alongside this variant.
    /// Pending sibling-variant unification into `Def { kind: TypeDef { … } }` —
    /// see §"Multi-legged authoring" for the target binding shape (parallel to
    /// `DefKind::Macro` and the D49 `Constructor` migration).
    TypeDef { /* … per Decision 22 */ },
    /// Pending sibling-variant unification into `Def { kind: Trait { … } }` —
    /// see §"Multi-legged authoring" for the target binding shape.
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
    /// `ModuleEntry::Import { source, .. }` (covering both private and public
    /// edges via per-entry `visibility`; the prior `ModuleEntry::Reexport`
    /// variant retired — see the `Import` variant docstring below),
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
    TraitImpl { /* trait_name: FQTraitName, impl_type: FQTypeName, methods: Vec<Symbol>, visibility: Visibility (always Public per spec §5.11.1) */ },
    /// Bare-name binding installed by `install_import_bindings`. **Covers both
    /// edge kinds** — `visibility` discriminates provenance (visibility is an
    /// orthogonal axis to entry kind; see §"Rejected alternatives — per-entry
    /// visibility" below):
    ///   - `Visibility::Private` — parse-time effect of `(import …)` (per
    ///     spec §8.3). Local binding reachable from this module only.
    ///   - `Visibility::Public` — parse-time effect of `(export
    ///     [foreign-sym])` (per spec §8.4); was the now-retired
    ///     `ModuleEntry::Reexport` variant. Local binding reachable from
    ///     this module AND from downstream importers.
    /// Chain-follow (see TraitImpl docstring) walks `Import` edges regardless
    /// of visibility — the variant collapse simplifies the pattern-match.
    Import { /* source: FQSymbol, visibility: Visibility */ },
    // `ModuleEntry::PlatformDecl` variant retired — platforms register as
    // synthetic modules at `symbol_tables["platform.<name>"]` per spec
    // §8.9.3; the DLL handle lives on the platform module's own
    // SymbolTable via the `D: DllStore` generic (see `dll: Option<D>`
    // field on SymbolTable above). The variant previously stored a
    // per-platform DLL record AS AN ENTRY WITHIN the declaring module,
    // which contradicted spec §8.9.3 — platforms are modules of their
    // own, not entries within other modules. The form-record
    // `PlatformSpec` on the entry module's `SymbolTable.platforms`
    // continues to record what the user wrote (for `.cl` regeneration
    // per `repl/spec.md` §15.4); the substantive runtime state (DLL
    // loaded; platform module's `symbols` populated with per-fn Defs)
    // is structurally captured by the existence + contents of
    // `symbol_tables["platform.<name>"]`. Idempotent load: the
    // `symbol_tables` DashMap is keyed by `ModuleFullPath`, so
    // `platform.<name>` can exist only once; existing
    // `ensure_module_exists` / `install_module` machinery handles dedup.
    // Source removal happens in /dev wave-3 concurrency-cluster brief.
    /// Sentinel for the bare-name-resolves-to-multiple-imports case. Carries
    /// `visibility: Visibility` for variant uniformity; `Public` is the
    /// lossless mark (sentinel never resolves to a payload).
    Ambiguous { /* visibility: Visibility */ },
    // `ModuleEntry::Constructor` variant retired — ADT constructors are now
    // `ModuleEntry::Def` with `kind: DefKind::Constructor { .. }` and
    // synthesised `Defn` bodies whose body expression is `Expr::ConstrADT`
    // (see §"DefKind" Rejected alternatives for the migration rationale).
    //
    // `ModuleEntry::Reexport` variant retired — public-edge re-exports now
    // land as `Import { source, visibility: Public }`; the variant collapse
    // aligns with the per-entry visibility pattern on `ModuleAliasEntry`
    // (see Import-variant docstring and §"Rejected alternatives — per-entry
    // visibility" below).
}

impl<C: CodeStore> ModuleEntry<C> {
    /// Arity of this entry as a callable, if it has a single well-defined
    /// arity at this entry.
    ///
    /// Returns:
    /// - `Some(n)` for `Def { scheme, .. }` where `scheme.ty` is
    ///   `Type::Fn(params, _)` with `n = params.len()` — `UserFn`,
    ///   `Constructor` (whose `scheme` is `Fn`-shaped per D49).
    /// - `None` for non-Def variants (`Import`, `Ambiguous`,
    ///   `TraitImpl`). (The retired `PlatformDecl` variant no longer
    ///   exists.)
    /// - `None` for multi-legged parent Defs (`Overloaded`, `Macro`) —
    ///   their parent `scheme.ty` is not `Fn`-shaped; query variants
    ///   /clauses individually via `.arity()` on each leaf sub-entry
    ///   `Def` (sub-entries live in `SymbolTable.symbols` under mangled
    ///   names like `add$Int+Int` or `{macro-name}$clause-{N}`).
    /// - `None` for declarative DefKinds (`TypeDef`, `Trait`,
    ///   `SpecialForm`).
    ///
    /// Implementation: delegates to `scheme.ty.fn_arity()` for `Def`
    /// variants. No `DefKind`-level method exists — `DefKind` does not
    /// own arity data; threading `scheme` into a `DefKind::arity(scheme)`
    /// method would signal the wrong receiver. The data owner is `Type`
    /// (via `scheme.ty`); `ModuleEntry::arity()` delegates without
    /// threading; the manifestation-site discipline puts the accessor at
    /// the data owner (`Type::fn_arity`) and a thin entry-level delegate
    /// at the entry owner (this method).
    pub fn arity(&self) -> Option<usize>;
}

#[non_exhaustive]
pub enum DefKind {
    UserFn { constrained_fn: Option<ConstrainedFn> },
    /// Multi-clause macro metadata entry. See §"Multi-legged authoring"
    /// above for the parent-metadata + mangled-variant-Defs storage pattern
    /// (`{macro-name}$clause-{N}` per clause body, uniform with `Overloaded`
    /// and `Constructor`).
    ///
    /// **Dispatch story.** The expansion-time macro expander looks up
    /// `{macro-name}` → finds `Def { kind: Macro { clauses_meta, … }, … }`
    /// → walks `clauses_meta` to pattern-match the call sexp against
    /// each clause's pattern shape → GOT-dispatches to the matched
    /// clause's mangled-variant Def. The expander's clause-walk-and-
    /// match logic is unchanged from the prior `MacroEnv`-sidecar shape;
    /// only the STORAGE of clause bodies moves — from the per-session
    /// `MacroEnv` (per-clause `func_ptr` indexed by macro+clause-index)
    /// into the normal `SymbolTable.symbols` namespace, dispatched via
    /// the same GOT mechanism as any other fn.
    ///
    /// **Sidecar retirement.** `MacroEnv` retires — clause-body lookup
    /// is now the same GOT-dispatch path as any other callable. Macros
    /// become "just Defs with a special kind" exactly like Constructors
    /// did under D49.
    ///
    /// **Rejected alternatives** (load-bearing for future re-litigation):
    /// - **Keep `ModuleEntry::Macro` as sibling variant; treat as
    ///   substantively distinct.** Macros ARE expansion-time-called
    ///   rather than runtime-called; that's a real lifecycle difference.
    ///   Rejected on: D49 precedent (discriminator over sibling variant);
    ///   the facade already hinted at unified shape via the `DefKind::Macro`
    ///   placeholder; the substantive difference (expansion vs runtime)
    ///   is a property of HOW the entry is invoked, not WHAT it is — the
    ///   storage shape doesn't need to encode the invocation timing.
    /// - **Unify, but keep entry-level GOT dispatch via a generated
    ///   clause-dispatch trampoline.** Each macro entry has `got_slot +
    ///   code`; the code is a compiled trampoline that pattern-matches
    ///   the call sexp and routes to the matched clause body. Rejected
    ///   on: redundancy with the multi-sig pattern (the trampoline IS
    ///   what the expander's clause-walk already does, but moved into
    ///   compiled code unnecessarily); adds backend complexity
    ///   (generating sexp-pattern-match trampolines as compiled
    ///   functions); fails Principle 2 (narrow surfaces) — embeds
    ///   expander logic into the backend.
    /// - **Unify but keep `sexp` + `source` at `ModuleEntry::Def` level
    ///   (not inside `DefKind::Macro`).** Every Def carries these fields,
    ///   with `None` for non-macros. Rejected on: violates the
    ///   DefKind-specific-data principle (these fields only make sense
    ///   for macros; `UserFn` doesn't need them); inflates the Def
    ///   shape with macro-specific noise that doesn't apply to the vast
    ///   majority of entries.
    Macro {
        clauses_meta: Vec<MacroClauseInfo>,                       // pattern shapes; expander walks for match — Name/Bracket/rest per `MacroParam`. The struct name `MacroClauseInfo` is retained from the prior sibling-variant shape; its `params` / `rest_param` / `source` fields carry the per-clause pattern metadata. Note: any prior `func_ptr`-shaped field would be redundant under the unified shape (clause-body addresses live in the GOT via each `{macro}$clause-{N}` mangled-variant Def's `got_slot`) — flag for /dev concurrency-cluster wave when migrating the source-side struct.
        sexp: Option<Sexp>,                                       // original parsed form — REPL `/sexp`, `/expand`
        source: Option<String>,                                   // original source text — REPL `/source` + macro-redefinition regen per `repl/spec.md` §15.4
    },
    TypeDef { /* ADT shape */ },
    Trait { /* trait shape */ },
    /// ADT constructor. Constructors are `ModuleEntry::Def` entries with this
    /// `DefKind`; the Def's `ast` field carries a synthesised `Defn` whose body
    /// expression is `Expr::ConstrADT { type_name, tag, fields, span }` (see
    /// §"AST"). Read by pattern matching (`Pattern::Constructor` consults
    /// `tag`) and by REPL introspection. Backend codegen does NOT read this
    /// variant — it lowers the synthesised body's `Expr::ConstrADT` node.
    ///
    /// `internal: true` for compiler-internal constructors users cannot
    /// directly construct or pattern-match (e.g., `IO.Bind` is constructed only
    /// by `bind`).
    ///
    /// **Rejected alternatives** (load-bearing for future re-litigation):
    /// - **Keep `ast: None` on ctor Defs and add a backend special case.**
    ///   Smaller change but the AST tells the truth nowhere: `ast: None` says
    ///   "no AST" while pattern matching still wants the tag. Three backend
    ///   special cases stay. Rejected per "AST tells the truth about
    ///   language-level operations" — `Expr::ConstrADT` is a language-level
    ///   node.
    /// - **Synthesise the body via `Apply` against an internal `alloc-adt-K`
    ///   primitive family.** Same dispatch unification but introduces a
    ///   primitive-by-string-name dependency between the deftype expander and
    ///   backend; typos compile silently; widens primitive surface for
    ///   compiler-internal use. Rejected per "intrinsics are backend
    ///   implementation detail; AST should not couple to string identifiers
    ///   for compiler-synthesised operations".
    /// - **Keep `ModuleEntry::Constructor` as a metadata-only variant
    ///   (no `code`/`got_slot`).** Resolves the `ConstructorInfo` duplication
    ///   but leaves backend with three special paths for callable ctors —
    ///   halfway move; improves the data model without simplifying backend
    ///   dispatch. Rejected against the uniform-dispatch model in §"Symbol
    ///   table" and the per-symbol JIT cardinality discipline.
    Constructor { type_name: FQTypeName, tag: usize, field_count: usize, internal: bool },
    Primitive { primitive_kind: PrimitiveKind },
    /// See §"Multi-legged authoring" for the parent-metadata + mangled-variant-Defs
    /// storage pattern; `Overloaded` carries `sexp` + `source` of the whole
    /// multi-clause `(defn …)` form at this metadata entry; variants are separate
    /// `DefKind::UserFn` Defs.
    Overloaded { variants: Vec<OverloadVariant>, sexp: Option<Sexp>, source: Option<String> },           // Decision multi-sig
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

#### Module lifecycle primitives

Free functions over `&DashMap<ModuleFullPath, SymbolTable<C, L>>` (i.e., the `SymbolTables<C, L>` typedef above) — the atomic write-side primitives for installing per-module symbol tables into the session-level map. Per S67 hack-back (FIXME 0192) these replace the pre-S67 `TypeCheckEnv::ensure_module_exists` / `restore_cached_module` methods: the data-home location of these primitives is the architectural intent (Principle 17 — primitives live with the data they operate on, not in a borrower).

Two primitives, two purposes — `ensure_module_exists` is the atomic check-then-insert (signalling outcome via `EnsureOutcome` for observability dispatch); `install_module` is the atomic unconditional overwrite used by the cache-hit branch of `CompilerSession::introduce_module` (the int layer composes both into a higher-level orchestration outcome internal to int).

```rust
/// Outcome of an `ensure_module_exists` call. Distinguishes fresh creation
/// from already-present (consumed by observability hooks in
/// `cranelisp-typecheck`'s trace dispatch).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnsureOutcome {
    Created,        // vacant slot → SymbolTable inserted
    AlreadyPresent, // occupied slot → no change
}

/// Atomic check-then-insert. Returns `EnsureOutcome` so observability
/// dispatch can distinguish the two outcomes. No seeding — modules start
/// empty per Principle 17 + FIXME 0193 amendment.
pub fn ensure_module_exists<C: CodeStore, L: LinkerStore>(
    modules: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    path: &ModuleFullPath,
) -> EnsureOutcome;

/// Atomic overwrite — the cache-hit branch's install primitive. Distinct
/// from `ensure_module_exists` (which is check-then-insert); `install_module`
/// unconditionally inserts, replacing any existing entry. Used by the
/// `int` layer's cache-load path (consistent with the pre-S67
/// `restore_cached_module` behaviour).
pub fn install_module<C: CodeStore, L: LinkerStore>(
    modules: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    path: ModuleFullPath,
    table: SymbolTable<C, L>,
);
```

### Cross-module structural specs (read at parse-time, persisted in `SymbolTable`)

```rust
// Per `spec/08-modules.md` §8.3 + §8.4: imports and exports share the
// `names_list` grammar, the `module_spec` grammar, and the alias mechanisms.
// `ImportSpec` and `ExportSpec` are structurally identical — the only
// difference is that names brought in via an `ExportSpec` are ALSO part of
// the current module's public API. Both stored on `SymbolTable` (in
// `imports: Vec<ImportSpec>` and `exports: Vec<ExportSpec>` fields) for
// source regeneration + introspection.
//
// **Alias-table flow.** When `alias.is_some()` on an `ImportSpec` or
// `ExportSpec`, parse-time processing of the form (`(import [(mod a) …])`
// or `(export [(mod a) …])`) ALSO writes a `ModuleAliasEntry` into the
// session-level `ModuleAliases` table, keyed by the alias's **full path**:
// `owner_module_path + "." + alias_name` (e.g., inside module `m.n` an
// alias `str` lands at key `m.n.str`). The entry's `visibility` is
// `Private` for import aliases (per §8.3.4) and `Public` for export mounts
// (per §8.4.4). The form-record (the `ImportSpec` / `ExportSpec` itself,
// persisted on `SymbolTable.imports` / `.exports`) retains the alias for
// source regeneration; the `ModuleAliases` entry is the resolution-layer
// artefact consumed by §8.6.6 qualified-name resolution. The two stores
// stay in sync — the form-record is the source of truth for regeneration;
// the alias-table entry is the resolution-time projection.
//
// **Cross-table mount-vs-submodule check at insert time.** When inserting
// `m.n.str` into `ModuleAliases`, the parse-time installer ALSO checks
// whether `m.n.str` is a key in `SymbolTables` (i.e., is a real loaded
// module at that path). If yes, this is a §8.6.4 mount-vs-submodule
// collision and the installer surfaces a typecheck error. Symmetric check
// when registering a module at `m.n.str` — the installer queries
// `ModuleAliases` for the same key before committing the `SymbolTable`
// insert. See bounded-context invariant 8 below for the rule statement.
//
// **Name-rename flow.** When a `NamedImport.rename.is_some()` (per §8.3.5
// / §8.4.5 symbol-alias form), parse-time processing inserts the bare-name
// `Import` entry into `SymbolTable.symbols` keyed by the local `Symbol`
// (`rename.as_ref().unwrap_or(&name)`); the source `name` is carried on
// the `ModuleEntry::Import { source, … }` row for chain-follow per §8.6.2.
// Renames write to `symbols` (the Symbol-keyed namespace, inside one
// module's `SymbolTable`); module aliases write to the session-level
// `ModuleAliases` (the `ModuleFullPath`-keyed namespace). The two
// namespaces have distinct keying domains and never collide.

#[non_exhaustive]
pub struct ImportSpec {
    pub module_path: ModuleFullPath,                                        // source module being imported from
    pub alias: Option<ModuleName>,                                          // §8.3.4 (import) / §8.4.4 (export — mount) — local alias for the source module; on imports, private to this module; on exports, becomes a public mount alias at `current/alias/...`
    pub names: ImportNames,                                                 // shared grammar with §8.3 / §8.4
    pub visibility: Visibility,
    pub span: Span,                                                         // whole import/export form — for "module not found" / unused-import errors
}

#[non_exhaustive]
pub enum ImportNames {
    Specific(Vec<NamedImport>),                                             // §8.3.1 / §8.4.1 — each entry independently classified per §8.3.11 (bare symbol → bare-name; dotted_symbol → selective member; (source local) → renamed bare; (Type.Member local) → renamed selective member). Parent type NOT brought into scope by dotted/member-rename entries.
    Glob,                                                                   // §8.3.2 / §8.4.2 — `[*]` — all public top-level exports as bare names
    MemberGlob(NamedImport),                                                // §8.3.3 — `[Type.*]` — all members of Type as bare names (parent Type NOT in scope); NamedImport carries parent name + its span for "Type not found" diagnostic. Rename does NOT apply to member-glob entries.
    AliasOnly,                                                              // §8.3.6 (import) — `[]` paired with `alias.is_some()` — loads module for alias resolution; brings nothing as bare. On exports per §8.4.4, the mount-only form: `(export [(m a) []])` mounts m at current/a without re-exporting names.
    Null,                                                                   // §8.3.7 (import) — `[]` paired with `alias.is_none()` — does not load or resolve; used to suppress implicit prelude. On exports, vacuous form `(export [m []])` — implementation-defined per §8.4.4 (no-op or parse error).
}

#[non_exhaustive]
pub struct NamedImport {
    pub name: Symbol,                                                       // source name in the source module — bare (`Some`) or dotted (`Option.None`) per §1.4.4 + §8.3.11
    pub rename: Option<Symbol>,                                             // §8.3.5 / §8.4.5 — Some(local) when explicit rename `(source local)`; None when no rename. Resolver uses `rename.as_ref().unwrap_or(&name)` as the DashMap key (local-name); the `name` field carries the source for chain-follow per §8.6.2.
    pub span: Span,                                                         // per-name span — for "name X not exported by m2" pointing (`repl/spec.md` §5.1 + §5.3)
}

// ExportSpec is structurally identical to ImportSpec — see the block comment
// above. We keep two type names for semantic clarity at use sites; the SymbolTable
// stores them in distinct fields (`imports` / `exports`), and the contextual
// distinction (private alias / mount alias; private names / public names) flows
// from which field holds the spec.

#[non_exhaustive]
pub struct ExportSpec {
    pub module_path: ModuleFullPath,                                        // §8.4.1–§8.4.3 — source module being re-exported from
    pub alias: Option<ModuleName>,                                          // §8.4.4 — Some(name) creates a public mount alias at `current/name/...` reaching the source module via full transparent forwarding; None = no mount
    pub names: ImportNames,                                                 // §8.4 grammar shares with §8.3 — same 5 variants. Exports MUST NOT carry `AliasOnly` with `alias.is_none()` and SHOULD treat `Null` per §8.4.4 implementation-defined disposition.
    pub span: Span,                                                         // whole export form
}

#[non_exhaustive]
pub struct ModDecl {
    pub name: ModuleName,
    pub visibility: Visibility,
    pub span: Span,                                                         // for "submodule file not found" errors
}

#[non_exhaustive]
pub struct PlatformSpec {
    /// The bare symbol the user wrote in `(platform <name>)` per spec
    /// §2.2.9 grammar — `platform_form = '(' 'platform' SYMBOL ')'`.
    /// Spec §10.9: `(platform name)` is only valid in the entry module;
    /// non-entry modules use `(import [platform.<name> [*]])`. The
    /// registered synthetic module name is `platform.<name>` per spec
    /// §8.9.3; this `PlatformSpec` is the form-record carrying only what
    /// the user wrote (parallel to `ImportSpec` / `ExportSpec` / `ModDecl`
    /// per Decision 33). Resolved data (manifest path, loaded DLL handle)
    /// is NOT carried on this form-record — see SymbolTable shape above
    /// for the DLL handle's home (`platform.<name>` SymbolTable's `dll`
    /// field via the `D: DllStore` generic). The retired `alias` field
    /// is excluded by spec §2.2.9 grammar (no alias permitted on the
    /// `platform` form).
    pub name: ModuleName,
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

#[non_exhaustive] pub struct TypeDefInfo {
    pub name: FQTypeName,
    pub type_params: Vec<Symbol>,
    pub constructors: Vec<Symbol>,       // names only; per-ctor metadata on each ctor's Def — see §"Symbol table — the single store" §"DefKind"
    pub docstring: Option<String>,
}
// `ConstructorInfo` retired — see §"Symbol table — the single store" §"DefKind" for the migration map.
//   .name           → ModuleEntry::Def.name
//   .tag            → DefKind::Constructor.tag
//   .fields[i].name → encoded in the synthesised `Defn`'s variant params (see §"AST" / §"Multi-legged authoring"); not a separate field on `Def`. (Cleanup: the historical `param_names: Vec<Symbol>` carrier on `Def` is private storage, accessed via `ModuleEntry::arity()` not by name indexing — see §"Storage detail (Def)" comment + invariant 11.)
//   .fields[i].type_expr → folded into Def.scheme (constructor's polymorphic function-type signature)
//   .fields[i].span     → preserved as FieldDef.span on the synthesised Defn's variant params metadata (Decision 39 per-field span; Submission 25)
//   .docstring      → Def.docstring
//   .internal       → DefKind::Constructor.internal
#[non_exhaustive] pub struct FieldInfo { /* per-field info — { name: Symbol, ty: Type } pair; consumed by HeapCategory::classify */ }
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
    pub fn store_slot(&self, slot: usize, ptr: *const u8);    // Ordering::Release — Decision 41 atomic swap
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
#[non_exhaustive] pub struct CompileContext { /* per-call context — passed by int into backend::compile_to_module (per-symbol arity for JIT mode, per-module for object mode — Decision 41) */ }
#[non_exhaustive] pub struct CompileResult { /* per-call result — JIT (per-symbol) or object (per-module) per Decision 41 cardinality */ }
#[non_exhaustive] pub struct CallGraph { /* rich within-module call graph for codegen */ }
#[non_exhaustive] pub struct CallEdge { pub caller: Symbol, pub callee: FQSymbol, pub tail: bool, pub span: Span }
#[non_exhaustive] pub struct CallInfo { /* per-call resolution info */ }
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
| `Pattern::Constructor`, `Pattern::Wildcard`, `Pattern::Var` | `Pattern` | Under §"AST" — three-variant enum per spec §6.2 (Constructor covers both §6.2.1 data form and §6.2.2 nullary form via empty `bindings`; Wildcard is §6.2.3; Var is §6.2.4). Spec §6.6 explicitly excludes literal/nested/or/guarded patterns — the enum closes over the spec's full pattern surface. |
| `TypeExpr::SelfType` (and siblings) | `TypeExpr` | Under §"AST" `pub enum TypeExpr { /* … */ }`. `SelfType` is the `:Self` syntactic marker (resolved to the impl target type by typecheck). |
| `DefKind::SpecialForm` | `DefKind` | Under §"Symbol table" `pub enum DefKind { /* … */ }`. The `SpecialForm { description: String }` variant exists alongside `UserFn`/`Macro`/`TypeDef`/`Trait`/`Primitive`/`Overloaded` and is registered for special-form introspection (`/info`, `/list`); `description` is the user-facing one-liner. |
| `ResolvedCall::BuiltinFn` | `ResolvedCall` | Under §"Typecheck output" `pub enum ResolvedCall { TraitMethod / SigDispatch / AutoCurry / BuiltinFn }`. `BuiltinFn` is the resolved-call shape for primitive ops (`+`, `-`, `vec-push`, etc.) — pre-typecheck the call site is bare `Apply`, typecheck rewrites to `BuiltinFn` with the primitive's `cranelift_op` carrier. |
| `ResolvedCall::TraitMethod::{method_name, mangled_name, trait_resolution}`, `ResolvedCall::SigDispatch::mangled_name`, `ResolvedCall::AutoCurry::{target_name, applied_count, total_count, trait_resolution}` | `ResolvedCall` variants' fields | Per-variant payload — backend reads `mangled_name: JitSymbol` to emit the call. `trait_resolution: Option<Box<ResolvedCall>>` chains AutoCurry → TraitMethod when a curried call's underlying body is a trait method. |
| `ModuleEntry::Ambiguous { visibility }` | `ModuleEntry` | Under §"Symbol table". Sentinel for the bare-name-resolves-to-multiple-imports case; typecheck emits a `TypeError` if a use site hits an `Ambiguous` entry. Carries `visibility: Visibility` for variant uniformity; constructed `Public` as the lossless mark (sentinel never resolves to a payload). |
| `ModuleEntry::Import { source, visibility }` | `ModuleEntry` | Under §"Symbol table". Covers BOTH edge kinds: `visibility = Private` is the `(import …)`-form effect (spec §8.3); `visibility = Public` is the `(export [foreign-sym])`-form effect (spec §8.4 — the prior `ModuleEntry::Reexport` variant retired). Chain-follow walks `Import` edges regardless of visibility. |
| `ModuleEntry::TraitImpl { trait_name, impl_type, methods, visibility }` | `ModuleEntry` | Under §"Symbol table". Gains `visibility: Visibility` for variant uniformity; constructed `Public` per spec §5.11.1 (impls are visible wherever both trait and type are in scope — lossless mark). |
| `Visibility { Public, Private }` | top-level enum | Under §"Symbol table — the single store" (canonical home; re-exported from `cranelisp_types::ast`). Per-entry visibility carrier — appears on every `ModuleEntry` variant, on `ModuleAliasEntry`, and on form-level constructs (`Defn`, `TraitDecl`, `ModDecl`, `ImportSpec`, `ExportSpec`, `NamedImport.rename` flow). Single source of truth: visibility lives once, on the entry. |
| `CranelispError::MacroError` | `CranelispError` | Under §"Errors and warnings". Emitted by `int`'s macro-expansion driver when a macro invocation fails. Same `{message, location}` shape as `ParseError`/`TypeError`/`ModuleError`/`CodegenError` per Decision 39. (Facade text §"Errors and warnings" notes `LinkError`/`CacheError`/`RuntimeError` aspirationally; source has `MacroError` instead — covered here, /arch follow-up may reconcile facade body if the divergence is structural.) |
| `LinkerError::SymbolNotFound`, `LinkerError::RelocationFailed` | `LinkerError` | **Transient — slated for removal.** Per Sprint 67 REV-4 (sprints/SPRINT.md row 5), `LinkerError` relocates to `cranelisp-backend`; see `facades/backend.md` §"Errors" for the canonical definition. The variants remain in `cranelisp-types::error` until `/dev (cranelisp-types)` removes the export sites in S67 Wave 4. After the relocation, this row deletes. |
| `WarningKind::UnusedBinding`, `WarningKind::UnreachableArm` (and siblings) | `WarningKind` | Under §"Errors and warnings" `pub enum WarningKind { UnusedDefn, UnusedImport, ShadowedName, /* … */ }`. Concrete variant set is internal-but-exposed; new variants added as detectors are implemented. |
| `View::Single`, `View::Union` | `View` | **Surface drift — substantive.** Source defines `View` as an **enum** with `Single { live }` and `Union { staging, live }` variants; the facade §"View" describes it as a `struct` with `union(…)` and `single(…)` constructors. The two shapes agree on the read surface (both expose `lookup`/`iter`/`single`/`union` as constructors), but the structural shape differs. **PIF candidate** — /arch follow-up to reconcile (either widen facade text to describe the enum, or PIF the source to a struct with internal enum). Tracked here for the compliance test; FIXME filing deferred until /arch decides direction. |

### Struct fields (internal-but-exposed under shape summaries)

The struct definitions in §"AST", §"Resolved type system", §"Symbol table", and §"Errors and warnings" include `/* … */` placeholders for fields that are not material to the cross-crate contract (e.g., per-variant payloads of enum struct-variants, internal annotation cache fields). The fields are reachable on the public surface (consumers can construct via builder methods or `Default`) but exhaustive field-by-field documentation lives in `rustdoc` on the source types. The compliance grep treats every field as a candidate name; the table below names them under the structures already cited.

| Field | Parent struct/variant | Rationale |
|---|---|---|
| `inferred_type` | every `Expr` variant | Per-variant annotation cache populated by typecheck Pass 2. `Option<Box<Type>>` — `None` pre-typecheck, `Some` after `check_form`. Per Decision 22 (AST annotation) — every `Expr` variant carries this field; see §"AST" for the full variant set. |
| `annotation` | `Expr::Annotate` | The user-written `:Type` annotation; the syntactic counterpart to `inferred_type` (which is the resolved Type). |
| `arms`, `scrutinee`, `compiler_generated` | `Expr::Match` | `scrutinee: Box<Expr>` (matched expression), `arms: Vec<MatchArm>` (clauses), `compiler_generated: bool` (distinguishes `let`-desugaring from user `match`). |
| `then_branch`, `else_branch` | `Expr::If` | Standard if/else carriers — `Box<Expr>` each. |
| `elements` | `Expr::VecLit` | `Vec<Expr>` of the literal's elements. |
| `params` tuple `.1: Option<TypeExpr>` (on `DefnVariant` and `Expr::Lambda`) | `DefnVariant`, `Expr::Lambda` | Per-param optional `:Type` annotation, fused into the `params: Vec<(Symbol, Option<TypeExpr>)>` tuple shape (S69 Submission 23 for `DefnVariant`; S69 Submission 24 for `Expr::Lambda` — replaces the prior parallel-vec `params` + `param_annotations` form per Principle 18 / spec §5.1.1 EBNF for `defn` / spec §2.3.5 + §2.5 EBNF for `fn_expr`). `None` for an unannotated parameter; `Some(TypeExpr)` for `:Type name` or `:Trait name`. `DefnVariant` carries no `return_type` field — spec §5.1 (L41) — return type is always inferred (the same applies to `fn_expr` per spec §2.3.5: "no return type annotation"). Per Principle 7 (single source of truth) the two hosts share one structural form for the same semantic concept. |
| `target`, `type_constraints`, `trait_name` | `TraitImpl` | S69 Submission 27 5-field target. `target: TypeExpr` is the unified grammatical unit per spec §5.4 EBNF (`target_type = qualified_symbol | '(' qualified_symbol type_arg+ ')'`) — simple targets lower to `TypeExpr::Named(TypeRef)`; polymorphic targets to `TypeExpr::Applied(TypeRef, …)` with type-var bindings reachable structurally as `TypeExpr::TypeVar` inside `target`. The prior separate `type_args: Vec<Symbol>` field is **deleted** (subsumed structurally — the spec treats target as one unit). `type_constraints: Vec<(Symbol, TraitRef)>` allows qualified trait references in constraints (`:(fmt/Display a)`) — `TraitRef` uniform with `TraitImpl.trait_name`. `trait_name: TraitRef` (was `TraitName` / `FQTraitName` pre-S69-S27) captures as-written qualification structurally per Decision 47's sharpened producer/consumer split (syntactic stage carries the qualification; typecheck does the lift to `FQTraitName`). |
| `type_expr` | `FieldDef` | `TypeExpr` of the constructor field (syntactic; resolved to `Type` by typecheck). Unconditional `TypeExpr` per the bare-field synthesised-`TypeVar` convention (spec §2.2.6 + §5.2 — name always present, annotation independently optional; parser synthesises `TypeExpr::TypeVar` for bare fields so consumers always have a syntactic type). Submission 25 reconfirmed `TypeExpr` (not `Option<TypeExpr>`) per Principle 7 / single source of truth — `Option<TypeExpr>` consistency-with-`DefnVariant`/`Lambda` was the alternative considered and rejected. |
| `span` | `FieldDef` | Per-field `Span` for "field has wrong type" diagnostics — Decision 39 grounding (per-defn source coordinate system; substance in §"Symbol table" and `repl/spec.md` §15.4). Added Submission 25. `#[serde(default)]` for cache compatibility; pre-existing caches deserialise the field as `Span::SYNTHETIC`-equivalent. |
| `params` tuple `.0: Symbol`, `.1: TypeExpr`, `hkt_param_index`, `ret_type`, `default_body` | `TraitMethodSig` | `params: Vec<(Symbol, TypeExpr)>` — per-param `(name, type)` tuple per spec §5.3 EBNF (every method has named params; `param = ':' type_expr symbol | symbol` always terminates in a `symbol`). The second tuple element is **unconditional `TypeExpr`** (not `Option<TypeExpr>`) per the spec §5.3.1 synthesised-`TypeExpr::SelfType`-for-bare convention — bare params default to the implementing type; the parser synthesises `SelfType` at parse time. Per Principle 18 the prior `default_param_names: Vec<Symbol>` sibling vector retired (S69 Submission 26 — names belong with the params, not with the default body; lockstep invariant `default_param_names.is_empty() == default_body.is_none()` folded structurally). `hkt_param_index: Option<usize>` identifies the HKT constructor parameter per spec §5.3.2. `ret_type: TypeExpr` (Principle 7 — producer-side naming canonical over the prior facade `return_type`). `default_body: Option<Expr>` — parsed AST of the default body when present (S69 Submission 26 — vindication against pre-Submission-26 source `Option<Sexp>`; AST-build catches structural errors at trait-decl time; per spec §5.4.5 the trait declaration clones the `Expr` into each impl's typecheck context for instantiated typecheck). |
| `body_sexp`, `fixed_params`, `rest_param` | `MacroClause`, `MacroClauseInfo` | Per-clause shape — `body_sexp: Sexp` (template), `fixed_params: Vec<MacroParam>` (positional), `rest_param: Option<Symbol>` (`&rest`-splice). |
| `is_private` | `ModDecl`, `DefmacroInfo` | Visibility flag — synonym for `visibility: Visibility::Private`; the field name reflects the underlying serialisation. |
| `inline_body` | `ModDecl` | `Option<Vec<Sexp>>` — `Some` for `(mod name forms…)` inline declarations, `None` for `(mod name)` external file references. |
| `dll` | `SymbolTable` | `Option<D>` (where `D: DllStore`) — the loaded DLL handle on the platform module's own `SymbolTable` per spec §8.9.3. `None` for non-platform modules; `Some(dll)` for synthetic `platform.<name>` modules. `#[serde(skip)]` — runtime state; re-populated on cache-hit by re-loading the platform DLL. Replaces the retired `ModuleEntry::PlatformDecl { dll_path, platform_module }` (see retirement note above) — DLL handle is no longer a per-entry record inside another module; it lives on the platform module's own SymbolTable. |
| `description` | `DefKind::SpecialForm` | One-line description for `/info` / `/list` REPL introspection (e.g., "let-binding form"). |
| `trait_origin` | `ModuleEntry::Def` | `Option<FQTraitName>` — `Some(trait_fqn)` when the entry is a method-body emitted by a `(impl Trait Type …)` form; `None` for ordinary defns. |
| `seq` | `ModuleEntry::Def` | `u64` — per-entry authorship-order token, allocated via `SymbolTable::next_seq.fetch_add(1)` at first registration; preserved across redef by `insert_or_update`. Consumed by `regenerate_backing_file` per `repl/spec.md` §15.4(2). |
| `constructor_scheme` | `ModuleEntry::TypeDef` | `Option<Scheme>` — the polymorphic constructor's scheme (for parameterized ADTs like `Option a`); `None` for monomorphic ADTs. |
| `sexp` (on `DefKind::Macro`, `ModuleEntry::TraitDecl`, `ModuleEntry::TypeDef`) | various entry variants | `Option<Sexp>` — the original source form, retained for REPL `/sexp`, `/expand`, and source regeneration (Decision 39). For macros, the `sexp` field lives inside `DefKind::Macro` (per §"DefKind") — the prior sibling `ModuleEntry::Macro` variant retired (Submission 13). |
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
| **Module-lifecycle primitives** | These free functions + the `EnsureOutcome` enum (canonical statement in §"Symbol table — the single store" §"Module lifecycle primitives") operate on `&DashMap<ModuleFullPath, SymbolTable<C, L>>` — the data home for symbol tables. Per the S67 hack-back (FIXME 0192), they replace the pre-S67 `TypeCheckEnv::ensure_module_exists` / `restore_cached_module` methods — the data-home location of these primitives is the architectural intent (Principle 17). |
| `lookup_type_def_chain`, `lookup_trait_decl_chain`, `get_impls_for_type_chain`, `get_implementing_types_chain`, `resolve_module_by_name_chain`, `for_each_in_module`, `resolve_terminal_entry_and_home`, `CHAIN_FOLLOW_DEPTH_LIMIT` | **Chain-follow primitives** (S67 hack-back FIXME 0192 methods 1, 3, 4, 5, 7). Live-only free fns that walk `Import` chains on `&DashMap<ModuleFullPath, SymbolTable<C, L>>` plus an explicit `scope: &ModuleFullPath` access root. `Import` covers both private and public edges (visibility-discriminated; see §"Symbol table — the single store" `Import` variant docstring); chain-follow proceeds regardless of visibility. Used by cross-crate read consumers (REPL display, `int` introspection paths). Cluster-mode consumers inside typecheck retain the staging-aware `TypeCheckEnv` methods (`lookup_type_def_in_module`, `get_impls_for_type_in_module`, etc.). The chain-follow primitives uniformly cap depth at `CHAIN_FOLLOW_DEPTH_LIMIT = 10` (spec §8.6.2). |

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
8. **Per-namespace insertion-time conflict enforcement (`spec/08-modules.md` §8.6.4).** Three conflict cases — two within-table, one cross-table:
   - **Rename collision** (within `SymbolTable.symbols`) — two import/export entries producing the same local `Symbol` collide on insertion. Structural: a second `symbols.insert(sym, …)` for an already-occupied key is the detection site; the parse-time installer surfaces the duplicate as a typecheck error.
   - **Mount collision** (within session-level `ModuleAliases`) — two mounts at the same alias **inside the same owner module** collide on insertion into `ModuleAliases`. Different owner modules mounting the same local alias name land at different `ModuleFullPath` keys (`m.n.a` vs `p.q.a`) and do not collide. Same-owner-twice mount at the same alias name collides on the second `module_aliases.insert(K, …)` for an already-occupied `K`. Structural via the DashMap insertion-time check.
   - **Mount-vs-submodule cross-namespace collision** (cross-table — `ModuleAliases` vs `SymbolTables`) — an alias path in `ModuleAliases` clashes with a real loaded module path in `SymbolTables`. NOT structural via the type system (the two stores are independent DashMaps even though both key by `ModuleFullPath`); the parse-time installer MUST perform an atomic cross-table check at insert time. When inserting `m.n.str` into `ModuleAliases`, query `SymbolTables` for `m.n.str` and reject if present; symmetrically, when registering a module at `m.n.str` in `SymbolTables`, query `ModuleAliases` for `m.n.str` and reject if present. Surfaced as a typecheck error per §8.6.4.
9. **Visibility lives on the entry.** Every `ModuleEntry` variant carries `visibility: Visibility`; visibility is an orthogonal axis to entry kind (see §"Visibility" enum + §"Rejected alternatives — per-entry visibility"). There is no parallel exports-set sidecar — see also §"Two complementary stores, two purposes" for the form-record-vs-visibility distinction. Cross-module slot lookups consult `entry.visibility` directly: a `Private` entry is invisible to any `lookup_origin != entry_module`. Same-module lookups skip the check. `/exports M` REPL = filter `SymbolTables[M].symbols` for `entry.visibility == Public`. `Import` covers both private (`(import …)`-edge) and public (`(export [foreign-sym])`-edge) edges via this field — the prior `ModuleEntry::Reexport` variant retired. `TraitImpl` is constructed `Public` per §5.11.1 (lossless mark); `Ambiguous` is `Public` as a sentinel.

10. **Macros are Defs.** Macro clause bodies are stored as `Def { kind: UserFn { … } }` entries with mangled names `{macro-name}$clause-{N}`, dispatched via the normal GOT mechanism — uniform with multi-sig fn variants (`add$Int+Int`). Macro entries themselves are `Def { kind: Macro { clauses_meta, sexp, source } }` and carry **metadata only** — no own body (`ast: None`, `code: None`), `got_slot` unused at this parent entry (present for variant uniformity). Expansion-time dispatch walks `clauses_meta` to pattern-match the call sexp, then GOT-dispatches to the matched clause's mangled-variant Def. Parallel to `Def { kind: Overloaded }` for multi-sig fns and `Def { kind: Constructor }` for ADT constructors (per D49). **No sidecar `MacroEnv` table exists in target shape** — clause-body lookup is the same GOT-dispatch path as any other callable. The prior `ModuleEntry::Macro` sibling variant retired (Submission 13).

11. **Field-level access on state types is discouraged outside the types crate.** State types (`ModuleEntry`, `DefKind`, `SymbolTable`, etc.) expose method-level accessors as their public contract — e.g., `ModuleEntry::arity()` (delegating to `Type::fn_arity()` on `scheme.ty`), `SymbolTable::get` / `get_type` / `defined_symbols` / `public_symbols`, the structural-decl read accessors. Storage shape is implementation detail and may evolve without breaking consumers. Direct field access remains permitted on **data-record DTOs** (`NamedImport`, `ImportSpec`, `ExportSpec`, `ModDecl`, `PlatformSpec`, `Span`, `FQSymbol`, `FQTypeName`, `FQTraitName`, `TypeDefInfo`, `MethodResolutions`, etc.) where the field set IS the contract and serde round-trips structurally. The audit-time disposition heuristic for "source has field X, facade doesn't list it": if the host is a state type, the facade SHOULD name the accessor method (not the field); if the host is a DTO, the facade SHOULD list the field as part of its public surface. See `facades/types-audit-s69.md` §"Calibration" for the audit-time framing.
