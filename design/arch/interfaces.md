# Interfaces — v2 Boundary Type Definitions

**Author:** `/arch`
**Date:** 2026-03-25
**Status:** Proposed — awaiting user review
**Supersedes:** `design/arch/v1/interfaces.md`

Complete Rust type signatures for every type that crosses a crate boundary. These are the contracts that all compiler skills implement against. All types live in `cranelisp-types` unless otherwise noted.

Types are organized by pipeline stage, following the pipeline-v4 data flow:
source text -> Sexp -> (ModuleDecls, Sexp) -> Sexp (expanded) -> TopLevel -> annotated AST on `SymbolTable` -> executable code.

**Sprint 55/56 update:** `CheckResult` is no longer a cross-crate boundary type. Typecheck deposits its outputs directly onto `SymbolTable` entries (annotated `ast`, `scheme`, `got_slot`, `callees`, mangled multi-sig / mono variants) and returns a slim transient value to its caller. The backend reads from `SymbolTable` via `SymbolTable::defined_symbols()`; it no longer receives `CheckResult`. See §"TypeChecker Internal State (was: CheckResult Boundary)" and §"Backend Compilation Entry Point" below, and `design/backend/compile-to-module.md` §2.1.

**Architectural invariants** (Principles 11, 12, 13):
- No structurally identical types at any pipeline boundary.
- No adapter functions between boundary types.
- Every pipeline stage has exactly one entry point per crate.
- Mode differences are parameters, not separate types or functions.

---

## Foundation Types

### Source Location

```rust
/// Byte range in source text. Carried on every AST node and every error.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub const SYNTHETIC: Span = Span { start: 0, end: 0 };

    pub fn new(start: u32, end: u32) -> Self {
        Span { start, end }
    }

    pub fn merge(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}
```

### String Newtypes

All identifiers use newtypes to prevent accidental mixing. Generated via `string_newtype!` which derives `Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize` and implements `Deref<Target=str>`, `From<String>`, `From<&str>`, `AsRef<str>`, `Display`.

```rust
string_newtype!(Symbol);           // local name: "foo", "+", "Option"
string_newtype!(ModuleFullPath);   // dotted path: "core.option", "user"
string_newtype!(TraitName);        // trait name: "Num", "Display"
string_newtype!(TypeName);         // type name: "Int", "Option"
string_newtype!(ModuleName);       // single component: "option", "core"
string_newtype!(JitSymbol);        // JIT symbol name (mangled): "add$Int+Int"
string_newtype!(LinkerSymbol);     // linker-level symbol name

/// Fully qualified symbol: module path + local name.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FQSymbol {
    pub module: ModuleFullPath,
    pub symbol: Symbol,
}
```

### Errors

```rust
/// All errors carry a Span for source location.
#[derive(Debug)]
pub enum CranelispError {
    ParseError {
        message: String,
        span: Span,
    },
    TypeError {
        message: String,
        span: Span,
    },
    CodegenError {
        message: String,
        span: Span,
    },
    ModuleError {
        message: String,
        file: Option<PathBuf>,
        span: Span,
    },
}

/// Classification of non-fatal diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum WarningKind {
    UnusedBinding,
    UnreachableArm,
    ShadowedName,
    /// Non-tail self-recursion detected (from call graph analysis).
    NonTailRecursion,
    Other,
}

/// Non-fatal diagnostic accumulated during compilation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Warning {
    pub kind: WarningKind,
    pub message: String,
    pub span: Span,
}
```

---

## Reader Output (Stage 1: source text -> Sexp)

Produced by `cranelisp-frontend`, consumed by `cranelisp-frontend` (AST builder) and stored for introspection.

```rust
/// S-expression: the reader's structural output.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Sexp {
    Symbol(String, Span),
    Int(i64, Span),
    Float(f64, Span),
    Bool(bool, Span),
    Str(String, Span),
    List(Vec<Sexp>, Span),
    Bracket(Vec<Sexp>, Span),
    /// `:Type <form>` folded during reading. Both halves remain raw syntax;
    /// type-expression validation belongs to the AST builder.
    Annotated {
        /// The raw annotation form, with the colon introducer stripped.
        annotation: Box<Sexp>,
        /// The immediately following form to which the annotation applies.
        subject: Box<Sexp>,
        /// Colon-introducer start through subject end.
        span: Span,
    },
    Comment(String, Span),
}

impl Sexp {
    pub fn span(&self) -> Span { ... }
}
```

`Sexp::Annotated` is the one Rust carrier for read-time annotation folding.
Its named, same-typed slots prevent annotation/subject transposition at
construction sites, and `span()` returns the outer binding span while each
boxed child retains its own source span. The macro-visible `macros/Sexp` ADT
appends `SexpAnnotated` at tag 7 (`TAG_SEXP_ANNOTATED`); tags 0–6 remain stable.
The complete folding, printing, quasiquote, and persistence consequences are
elaborated in `annotated-sexp-node.md`; that document does not define a second
carrier.

### Reader-quote structural predicate (S121, user-approved 2026-09-01; resolves FIXME 0789's home question)

The ONE structural classifier for the reader-quote family lives beside `Sexp`
— a purely syntactic shape test (bare-symbol head + `len() == 2`, consulting
neither shadow sets nor any resolver), which is exactly why it belongs with
the datum rather than in either consumer (Principle 15; Principle 7):

```rust
// cranelisp-types, `crates/cranelisp-types/src/sexp.rs` — additive; no
// serde presence (a classification, never persisted).
//
/// The reader-quote family head of a `Sexp::List`'s children, or `None`.
/// CLOSED sum — exhaustive consumer matches are the safety feature (the
/// `crates/cranelisp-types/CLAUDE.md` §Public-surface-mechanics exception
/// class): a new quote head is a language change, and every walker must
/// take an arm for it.
pub enum QuoteHead { Quote, Quasiquote, Unquote, UnquoteSplicing }

/// Structural recognition: `children.len() == 2` and `children[0]` is the
/// bare symbol `quote` / `quasiquote` / `unquote` / `unquote-splicing`.
pub fn quote_head(children: &[Sexp]) -> Option<QuoteHead>;
```

**Consumers (the three copies collapse to one):** the frontend quasiquote
fold (`quasiquote.rs` — its crate-private `is_*` predicates delegate or
retire), and int's two scope-aware walks through `src/expander.rs::quote_head`
(the expander shield + the qualify shield, S115/FIXME 0718), which becomes a
thin projection (int's local three-arm `QuoteHead` may merge
`Unquote`/`UnquoteSplicing`; the types-level sum distinguishes them because
the fold does). If the fold's and the shields' notion of "is a quote" ever
diverge, a quoted subtree is double-desugared or mis-qualified
(`design/int/quote-shield.md` §5) — single-sourcing the shape test is the
structural close. **No parser redesign**: the reader still lowers `'x`/`` `x ``
/`~x`/`~@x` to the list forms; this predicate only classifies them.
`public-api.txt` delta: `cranelisp-types` +2 items, riding the one S121
C1 regeneration (the S121 lifecycle migration, retained in Git history); no frontend baseline delta
(the predicates were never frontend surface).

---

## Module Declarations (Stage 2: extraction)

Produced by `cranelisp-frontend::extract_module_decls`, consumed by the binary crate for module graph construction.

```rust
/// Import name selection.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ImportNames {
    Specific(Vec<Symbol>),
    Glob,
    MemberGlob(Symbol),
    None,
}

/// An import declaration. spec: §5.9
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImportSpec {
    pub module_path: ModuleFullPath,
    pub alias: Option<ModuleName>,
    pub names: ImportNames,
    pub span: Span,
}

/// An export declaration. spec: §5.9
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExportSpec {
    pub module_path: ModuleFullPath,
    pub names: ImportNames,
    pub span: Span,
}

/// Inline module declaration extracted during discovery. spec: §8.2.2
pub struct InlineModuleDecl {
    pub name: ModuleName,
    pub body: Vec<Sexp>,
    pub span: Span,
}

/// Extracted module-level declarations. spec: §5.8–5.10
///
/// These forms are handled before macro expansion and AST building.
/// They are NOT AST nodes.
pub struct ModuleDecls {
    pub mod_names: Vec<(ModuleName, Span)>,
    pub inline_mods: Vec<InlineModuleDecl>,
    pub imports: Vec<ImportSpec>,
    pub exports: Vec<ExportSpec>,
    pub platforms: Vec<(String, Option<String>, Span)>,
    /// Remaining sexps (passed to Stage 3: expansion).
    pub remaining: Vec<Sexp>,
}

// `ImplSexp` DELETED at S119 (FIXME 0918) — zero-consumer dead surface;
// impl forms are processed directly and the persisted trait-impl record is
// `WrittenTraitImpl` (see §"Written-impl cache carrier").
```

No changes from v1 (except the S119 `ImplSexp` deletion noted above).

---

## AST (Stage 4: Sexp -> typed AST)

Produced by `cranelisp-frontend`, consumed by `cranelisp-typecheck` and `cranelisp-backend`.

### Type Expressions

```rust
/// Type expression in annotations and trait signatures.
/// spec: §3 (Types), used in §5.1 (defn annotations), §5.3 (trait sigs)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TypeExpr {
    Named(TypeName),
    SelfType,
    FnType(Vec<TypeExpr>, Box<TypeExpr>),
    TypeVar(Symbol),
    Applied(TypeName, Vec<TypeExpr>),
    Bounds(Vec<TraitRef>),
}
```

**`Bounds` — the constrained-type-variable annotation (FIXME 0346, S82).** A
parameter annotation is *either* a concrete type *or* a set of trait bounds,
never both: you cannot write a concrete type and then also constrain it. The
param slot is one `Option<TypeExpr>` per binder
(`Vec<(Symbol, Option<TypeExpr>)>` on `Lambda` / `DefnVariant`), and
`TypeExpr::Bounds(Vec<TraitRef>)` is the variant that slot takes when the
binder carries a run of stacked `:Trait` annotations (`[:Eq :Display a]`, spec
§3.9.2). Holding **one-of-{concrete type, bounds set}** in the single
`Option<TypeExpr>` slot encodes the mutual exclusion *by construction* — the
ruled alternative (a sidecar struct carrying both `ty` and `bounds`) would model
a state that cannot exist. The `TraitRef`s carry as-written qualification
(`:fmt/Display`); typecheck resolves them and accumulates the bounds onto the
type variable's `Scheme.constraints` (spec §3.9.3 try-type-then-trait). This is
the same `TraitRef` reference type used by `TraitImpl::type_constraints:
Vec<(Symbol, TraitRef)>`. The param-tuple shape is **unchanged** by this
addition — zero call-site churn (minimum-mechanism). Frontend emits `Bounds`
from the accumulated annotation run; typecheck consumes it at the param-resolve
site (`program.rs:1856`). *(Note: the surrounding `TypeExpr` block above is a
historical v1 sketch — the live source carries `Named(TypeRef)` / `Applied(TypeRef, …)`
per S69 Submission 27; the `Bounds` payload `Vec<TraitRef>` is exact to source.)*

### Patterns

```rust
/// Pattern in a match expression. spec: §6
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Pattern {
    Constructor {
        name: Symbol,
        bindings: Vec<Symbol>,
        span: Span,
    },
    Wildcard { span: Span },
    Var { name: Symbol, span: Span },
}

/// One arm of a match expression.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Expr,
    pub span: Span,
}
```

### Expressions

```rust
/// Expression AST node. Every variant carries a Span.
///
/// spec: §4 (Expressions)
///   IntLit, FloatLit, BoolLit, StringLit — §4.1
///   Var — §4.2
///   Let — §4.3
///   If — §4.4
///   Lambda — §4.5
///   Apply — §4.6
///   Match — §4.8
///   Annotate — §4.9
///   VecLit — §4.10
///   Trace — §12
///   RunTests — REPL-only special form
///   ParBind — §10.12
///   LaunchContinue — §10.12.7
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Expr {
    IntLit { value: i64, span: Span },
    FloatLit { value: f64, span: Span },
    BoolLit { value: bool, span: Span },
    StringLit { value: String, span: Span },
    Var { name: Symbol, span: Span },
    Let {
        bindings: Vec<(Symbol, Expr)>,
        body: Box<Expr>,
        span: Span,
    },
    If {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
        span: Span,
    },
    Lambda {
        params: Vec<Symbol>,
        param_annotations: Vec<Option<TypeExpr>>,
        body: Box<Expr>,
        span: Span,
    },
    Apply {
        callee: Box<Expr>,
        args: Vec<Expr>,
        span: Span,
    },
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
        span: Span,
        compiler_generated: bool,
    },
    VecLit { elements: Vec<Expr>, span: Span },
    Annotate {
        annotation: TypeExpr,
        expr: Box<Expr>,
        span: Span,
    },
    Trace {
        modules: Vec<Symbol>,
        body: Box<Expr>,
        span: Span,
    },
    RunTests {
        modules: Vec<Symbol>,
        init: Box<Expr>,
        pass_fn: Box<Expr>,
        fail_fn: Box<Expr>,
        span: Span,
    },
    ParBind {
        bindings: Vec<(Symbol, Expr)>,
        body: Box<Expr>,
        span: Span,
    },
    // Launch-and-continue (spec §10.12.7) — the *detached* peer of `ParBind`.
    // Produced by the SAME `/int` bind-chain independence analysis (the shared
    // token-disjointness core, Principle 7), consumed by the SAME backend
    // IO-node-construction family (lowers to the `IO_TAG_LAUNCH` runtime node,
    // `design/backend/io-trampoline.md §15`). `launched` is the detached effect
    // sub-tree (result discarded, supervised strand); `continuation` runs
    // without awaiting it and produces the node's value. A dedicated variant
    // (not a `detached` flag on `ParBind`) keeps structured-join vs detached
    // representationally distinct per Principle 20 — the marker match selects
    // the runtime node by the variant, so a join site cannot be mis-lowered as
    // detached. Mirrored on `MonoExpr::LaunchContinue` (the codegen twin).
    LaunchContinue {
        launched: Box<Expr>,
        continuation: Box<Expr>,
        span: Span,
    },
}

impl Expr {
    pub fn span(&self) -> Span { ... }
}
```

No changes from v1.

### Top-Level Definitions

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Visibility {
    Public,
    Private,
}

/// One variant of a function definition. spec: §5.1.2
///
/// Contains the parameter list, annotations, and body for one signature.
/// A single-signature function (§5.1.1) has exactly one variant.
/// A multi-signature function (§5.1.2) has multiple variants.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DefnVariant {
    pub params: Vec<Symbol>,
    pub param_annotations: Vec<Option<TypeExpr>>,
    pub body: Expr,
    pub span: Span,
}

/// Function definition. spec: §5.1
///
/// Covers both single-signature (§5.1.1) and multi-signature (§5.1.2)
/// functions. A single-signature function has exactly one variant.
/// The spec uses the same `defn` keyword for both forms — the AST
/// makes no structural distinction.
///
/// Also used for trait method implementations (TraitImpl.methods),
/// where exactly one variant is always present.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Defn {
    pub name: Symbol,
    pub docstring: Option<String>,
    pub variants: Vec<DefnVariant>,
    pub visibility: Visibility,
    pub span: Span,
}

impl Defn {
    /// Returns true if this is a multi-signature function (more than one variant).
    pub fn is_multi_sig(&self) -> bool {
        self.variants.len() > 1
    }

    /// Convenience: params of the single variant. Panics if multi-sig.
    pub fn params(&self) -> &[Symbol] {
        assert!(!self.is_multi_sig(), "use variants for multi-sig defns");
        &self.variants[0].params
    }

    /// Convenience: body of the single variant. Panics if multi-sig.
    pub fn body(&self) -> &Expr {
        assert!(!self.is_multi_sig(), "use variants for multi-sig defns");
        &self.variants[0].body
    }

    /// Convenience: param_annotations of the single variant. Panics if multi-sig.
    pub fn param_annotations(&self) -> &[Option<TypeExpr>] {
        assert!(!self.is_multi_sig(), "use variants for multi-sig defns");
        &self.variants[0].param_annotations
    }
}

/// Field in a data constructor. spec: §5.2
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FieldDef {
    pub name: Symbol,
    pub type_expr: TypeExpr,
}

/// Data constructor definition. spec: §5.2
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstructorDef {
    pub name: Symbol,
    pub docstring: Option<String>,
    pub fields: Vec<FieldDef>,
    pub span: Span,
}

/// Frontend-stage trait method with one unclassified trailing form.
/// `tail` retains its own exact source span, including `Sexp::Annotated`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UnresolvedTraitMethodSig {
    pub name: Symbol,
    pub docstring: Option<String>,
    pub params: Vec<(Symbol, TypeExpr)>,
    pub tail: Sexp,
    pub span: Span,
    pub hkt_param_index: Option<usize>,
}

/// The one settled required-vs-default authority.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TraitMethodKind {
    Required { ret_type: TypeExpr },
    Default {
        body: Expr,
        result_constraint: Option<TypeExpr>,
    },
}

/// Typecheck-classified trait method stored in `TraitDeclInfo`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitMethodSig {
    pub name: Symbol,
    pub docstring: Option<String>,
    pub params: Vec<(Symbol, TypeExpr)>,
    pub kind: TraitMethodKind,
    pub span: Span,
    pub hkt_param_index: Option<usize>,
}

/// Trait declaration. spec: §5.3
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitDecl {
    pub name: TraitName,
    pub docstring: Option<String>,
    pub type_params: Vec<Symbol>,
    pub methods: Vec<UnresolvedTraitMethodSig>,
    pub visibility: Visibility,
    pub span: Span,
}

/// Trait implementation. spec: §5.4; impl-form grammar §7.3/§7.3.4.
///
/// As-built shape (S69 Submission 27 unified `target: TypeExpr`, replacing
/// the 6-field `target_type + type_args`; S112 b0 added `head_con_var`):
/// `head_con_var` carries the WRITTEN slot-1 head shape of the settled
/// echo-the-head impl form — `None` = bare head `(impl Display …)`,
/// `Some(con_var)` = parenthesized echoed head `(impl (Functor f) …)`,
/// spelling verbatim. The parser records the shape bit only (no kind
/// classification — Principle 24, one classifier); the sole consumer is
/// typecheck's §7.3.5 Case-3 seam (`design/typecheck/hkt.md` §5.4 step 3),
/// which validates shape + spelling against the trait's declaration.
/// `#[serde(default)]` — pre-b0 serialized forms deserialize as `None`,
/// equal to the fresh-parse bare-head value (schema-bump-exempt class).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitImpl {
    pub trait_name: TraitRef,
    #[serde(default)]
    pub head_con_var: Option<Symbol>,
    pub target: TypeExpr,
    pub type_constraints: Vec<(Symbol, TraitRef)>,
    pub methods: Vec<Defn>,
    pub span: Span,
}
```

The method-tail boundary is deliberately phase-separated. Frontend constructs
`UnresolvedTraitMethodSig` and preserves the sole trailing form verbatim; its
exact tail span is available through `Sexp::span()`, including the outer and
child spans of `Sexp::Annotated`. Typecheck is the only classifier. It must
complete the transactional type-resolution probe before replacing the
unresolved declaration with `TraitMethodSig` in `TraitDeclInfo`; an unresolved
method is never published to the symbol table.

`TraitMethodKind` is the one authoritative closed sum. The former parallel
`ret_type: TypeExpr` plus `default_body: Option<Expr>` representation is removed
in the same coordinated change. For an annotated default, typecheck builds
`body` from the annotation's subject and stores the annotation exactly once as
`result_constraint`; it must not also retain an outer `Expr::Annotate` carrying
the same constraint. `TraitDecl.methods` is therefore the frontend-stage
`Vec<UnresolvedTraitMethodSig>`, while `TraitDeclInfo.methods` remains the
classified `Vec<TraitMethodSig>`.

This carrier change coalesces with `Sexp::Annotated` in the already approved
cache schema 22→23 window. The required public-API baseline change is exactly
`crates/cranelisp-types/public-api.txt`. Frontend and typecheck baselines are
regenerated only as zero-diff verification: neither crate adds a public entry
point, re-export, or carrier of its own.

### TopLevel (CHANGED from v1)

```rust
/// Top-level form: the unit of compilation.
///
/// Every form the spec defines at the top level that survives to type
/// checking. Forms handled earlier (mod, import, export, platform,
/// defmacro, const, def) are NOT represented here.
///
/// Architectural invariant: this is the SOLE input type for
/// TypeChecker::check(). There is no parallel type. (Principle 11)
///
/// spec: §5 (Definitions), §4 (Expressions)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TopLevel {
    /// Function definition (single or multi-signature). spec: §5.1
    Defn(Defn),

    /// Algebraic data type definition. spec: §5.2
    TypeDef {
        name: TypeName,
        docstring: Option<String>,
        type_params: Vec<Symbol>,
        constructors: Vec<ConstructorDef>,
        visibility: Visibility,
        span: Span,
    },

    /// Trait declaration. spec: §5.3
    TraitDecl(TraitDecl),

    /// Trait implementation. spec: §5.4
    TraitImpl(TraitImpl),

    /// Bare expression (REPL input or module-level effect). spec: §4
    Expr(Expr),
}

/// A complete compilation unit: all top-level forms from one module.
pub type Program = Vec<TopLevel>;
```

**v1 diff:**
- `Defn` struct merged with `DefnMulti`: `Defn` now has `variants: Vec<DefnVariant>` instead of direct `params`/`body`. Single-sig functions have one variant, multi-sig have multiple. `TopLevel::DefnMulti` variant eliminated — 5 variants instead of 6.
- Added `Expr(Expr)` variant.
- `ReplInput` deleted — this is the sole top-level input type.
- Convenience methods `params()`, `body()`, `param_annotations()` on `Defn` provide ergonomic access for single-variant code; they panic on multi-sig as a safety check.

---

## Type System

```rust
pub type TypeId = u32;

/// Concrete type. All variants exist from Ring 0.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Type {
    Int,
    Bool,
    String,
    Float,
    Fn(Vec<Type>, Box<Type>),
    ADT(FQTypeName, Vec<Type>),   // module-qualified at construction (Decision 47)
    Var(TypeId),
    TyConApp(TypeId, Vec<Type>),
}

impl Type {
    pub fn adt(module: ModuleFullPath, name: TypeName, args: Vec<Type>) -> Type { ... }
    pub fn is_io(&self) -> bool { ... }   // `ADT(primitives/IO, _)` only; a user `IO` type never matches
    pub fn from_name(name: &str) -> Option<Type> { ... }
    pub fn type_name(&self) -> Option<&'static str> { ... }
    pub fn is_heap(&self) -> bool { ... }
}

/// Polymorphic type scheme.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Scheme {
    pub vars: Vec<TypeId>,
    pub constraints: HashMap<TypeId, Vec<FQTraitName>>,
    pub ty: Type,
}

pub type Subst = HashMap<TypeId, Type>;
pub fn apply(subst: &Subst, ty: &Type) -> Type { ... }
pub fn free_vars(ty: &Type) -> HashSet<TypeId> { ... }

/// The single parameterized walk over `Type`, beside its `Display` impl
/// (S87, FIXME 0420). Every workspace renderer delegates here; the two
/// `#[non_exhaustive]` config enums select output convention without forking
/// the walk. See `bounded-contexts.md` §7 "Type rendering".
pub fn render_type(ty: &Type, prim: PrimitiveNaming, vars: VarNaming<'_>) -> String { ... }
pub enum PrimitiveNaming { Bare, Qualified }            // bare `Int` vs FQ `primitives/Int`
pub enum VarNaming<'a> { Numbered, Lettered(&'a HashMap<TypeId, String>) } // `t{id}` vs lettered
pub fn type_var_names(...) -> HashMap<TypeId, String> { ... } // supplies the lettered map
```

The `Type`-representation core is unchanged from v1; S87 added the single
`render_type` walk + `PrimitiveNaming`/`VarNaming` config and **removed** the
dead `format_type_display` / `format_type_with_vars` free fns (their lettered
capability preserved as `VarNaming::Lettered`).

**Resolved-stage type identity is module-qualified (Decision 47).** Every API
past the frontend's resolution stage names a type or trait as `FQTypeName` /
`FQTraitName` (`crates/cranelisp-types/src/newtype.rs`); bare `TypeName` /
`TraitName` are syntactic-stage values (parser output, `TypeExpr`, the
pre-resolution `ImplSexp.target`). The lift happens once, in
`cranelisp_typecheck::resolve`, and unification compares the whole
`FQTypeName`, so a `Point` defined in two modules yields two distinct types. There are
exactly two exceptions, neither extendable without `arch` review: (1) the
reverse-lookup helpers `Type::from_name` / `Type::type_name`, which operate
only on the built-in non-ADT variants; (2) receiver-pinned lookups such as
`SymbolTable::get_type(&TypeName)`, where `&self` already supplies the module.
Two consequences are load-bearing: the primitive types keep dedicated `Type`
variants (`Int`, `Bool`, `String`, `Float`) rather than becoming
`ADT(primitives/Int)` — they need no tag, constructor or heap layout, and
`primitives/Int` is a rendering convention (`PrimitiveNaming::Qualified`), not
a type-system fact; and no derived name→module map exists anywhere — a
`Type::ADT` carries its module, so display and codegen never reverse-look it
up. Constructor names stay `Symbol` because the symbol table that holds them is
already module-pinned.

---

## Pipeline Configuration

### CompileMode (unchanged from v1)

```rust
/// Controls codegen strategy.
///
/// There is no CheckMode — the typecheck pipeline is always multi-pass
/// (register all signatures, then check all bodies). This works identically
/// on any input size: a batch program (many forms), a module (many forms),
/// or a REPL line (one or few forms). See pipeline-v2.md §5 for rationale.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompileMode {
    /// GOT-indirect calls for hot-reload. REPL + multi-module batch + caching.
    Interactive,
    /// Direct function calls, no GOT. Single-file test execution.
    Batch,
    /// Whole-program optimisation. Phase H.
    Release,
}
```

> **`CompileMode` is NOT the run-mode signal (D1, S80).** `CompileMode` is the
> *codegen-strategy* axis (GOT-indirect vs direct vs whole-program). The
> REPL-vs-`--run`-vs-`--link` *session* axis — which gates REPL-only introspection
> population and the platform layout-hash refuse-vs-warn behavior — is the separate
> **`RunMode`** enum (`Repl`/`Run`/`Link`), an **int-internal** type on
> `SharedState` set from `main.rs`'s `Action`. The two are orthogonal and MUST NOT
> be conflated. See `design/arch/d1-introspection-repl-only.md` and `bounded-contexts.md` §6.

### ModuleStrategy (NEW)

```rust
/// Whether a compilation unit replaces or extends the target module.
/// See pipeline-v2.md §14 for design rationale.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleStrategy {
    /// File load / hot-reload: these forms ARE the module.
    /// Clear existing definitions before registering new ones.
    Replace,
    /// REPL line: add to existing module state.
    /// Existing definitions preserved; re-definitions overwrite.
    Additive,
}
```

### CompileContext (NEW)

```rust
/// Compilation context: makes module target, strategy, and codegen mode explicit.
///
/// Constructed by the binary crate before invoking the pipeline.
/// Passed to check() and codegen() as an immutable parameter.
/// Replaces the implicit set_current_module()/current_module_path()
/// mutable state pattern from v1. See pipeline-v2.md §14.
#[derive(Debug, Clone)]
pub struct CompileContext {
    /// The module that definitions from this compilation unit are registered into.
    pub module: ModuleFullPath,

    /// Whether this compilation unit defines the module's complete contents
    /// (Replace) or adds to existing state (Additive).
    pub strategy: ModuleStrategy,

    /// Controls codegen strategy (GOT-indirect vs direct calls).
    pub compile_mode: CompileMode,
}
```

---

## TypeChecker Internal State (was: CheckResult Boundary)

**Sprint 55/56 change:** `CheckResult` is no longer a boundary contract between `cranelisp-typecheck` and `cranelisp-backend`. It was formerly the "SOLE boundary type between typecheck and backend"; it is now typecheck-internal transient state carrying only diagnostics and REPL display.

The codegen payload the backend used to consume from `CheckResult` has been redistributed onto `SymbolTable` entries by Sprint 55 (Phase 1 — AST annotation) and Sprint 56 (Phase 2 — shared codegen-compilable predicate):

| Former `CheckResult` field | New location (source of truth for codegen) |
|---|---|
| `method_resolutions: MethodResolutions` | `Expr::Apply.resolved_call` (call position) and `Expr::Var.resolved_call` (value position — a trait method bound/passed as a value, e.g. `(let [f =] (f x y))`) on AST nodes (`ModuleEntry::Def.ast`). The two carriers are the call-position and value-position channels for the same `MethodResolutions` map; the value-position carrier (S77, FIXME 0300) closes the gap where a trait method escaping the call site had a type but no resolution. |
| `expr_types: HashMap<Span, Type>` | `Expr.inferred_type` on every AST node. |
| `mono_defns: Vec<MonoDefn>` | Registered eagerly by `register_mono_entry` as mangled `ModuleEntry::Def` entries with `ast: Some(_)` carrying fully-concrete annotations. **Phase 3 (concrete-boundary arc, FIXME 0392):** each also carries `codegen_view: Some(MonoDefnVariant)` (the `MonoExpr` view the backend consumes), moving off the transitional `CheckState.mono_variants` parallel `Vec` onto the entry. |
| `default_method_defns: Vec<Defn>` | Registered by `register_mangled_method` as mangled `ModuleEntry::Def` entries with `ast: Some(_)`. |
| `constrained_fn_names: HashSet<Symbol>` | Derivable by scanning `SymbolTable` for `ModuleEntry::Def { kind: UserFn { constrained_fn: Some(_) }, .. }` — negation of `defined_symbols()` within `UserFn`. |
| `type_defs`, `constructor_to_type` | Already on `SymbolTable` as `ModuleEntry::TypeDef` / `ModuleEntry::Constructor`. |
| `call_graph` | The public `CallGraph` type was DELETED at S119 (FIXME 0918 — zero consumers); any within-module TCO/analysis bookkeeping is typecheck-internal. Persistent per-symbol `callees: Vec<FQSymbol>` lives on `ModuleEntry::Def` per Decision 21. |

**Callability is structural — GOT slot on the callable `DefKind` variants (FIXME 0356/0357, Principle 20; amends Decision 35; S83 target).** The row above notes a constrained template is the *negation of `defined_symbols()` within `UserFn`* — i.e. it is **not** codegen-compilable. The dual fact at the call-resolution seam is that it is **not directly callable**, and the S83 target makes this a property of the *shape* rather than an accessor convention. The S82 stopgap (`callable_got_slot()` reading around an illegal `got_slot`+template pairing, `mark_constrained_template()` flip-and-clear sole-writer, `assert_well_formed()` debug guard) is superseded: the `got_slot` migrates **off the flat `ModuleEntry::Def` field and onto the callable `DefKind` variants** (`UserFn`'s concrete-callable form, `Primitive`, `Constructor`, `PlatformEffect` — the four GOT-indirect-dispatched callable kinds; `PlatformEffect` ratified into this set S83 per FIXME 0358, correcting the Phase-2 gating-decision-2 omission); non-callable / non-GOT-dispatched kinds (the constrained-template form of `UserFn`, `Macro` parent, `PrimitiveExtern` — which dispatches by-name via `Linkage::Import`, FIXME 0360 — and the `Overloaded` base) carry no slot field, so `Def{slot}+template` is **unconstructable**. The timing wall (Pass-1 slot allocation preceded Pass-2 constraint detection) resolves by **deferring slot allocation past Pass-2 detection** — the entry has no slot until its callability is determined, which is correct because nothing may call it before then; no `Pending` interstage variant is needed. `callable_got_slot()` survives as the single read-through point (so callers do not re-pattern the kind set) but becomes a trivial present-or-absent read on the matched variant; `mark_constrained_template()` and the phantom-slot assertion retire. Backend call-target resolution (`resolve_got_target`) reads through `callable_got_slot()` exactly as before — its body changes, its contract does not. Mono variants (`cmp$Int+Int`) are ordinary concrete `UserFn` entries owning their own slot — the home for the S83 cross-module-mono feature (FIXME 0355). See BC §7 "Callability is structural" + Principle 20.

**S84 generalisation (user-ratified 2026-06-16; FIXME 0374; BC §7 + Principle 20).** The S83 statement above — "a constrained template has no slot" — is the constrained-template *species* of the general invariant **"a def has a GOT slot ⟺ its type is fully concrete (`Type::is_concrete()`, no `Type::Var`)."** A *plain parametric/generic* def (`id : ∀a. a→a`, a `(Box a)`-result HOF) carries **no trait constraints** yet is **not** concrete, so it too must be slot-less; only its monomorphised instances (`id$Int`, `(Box Int)`) are slotted. The slot-allocation gate therefore tests **`is_concrete()`, not `constraints.is_empty()`** — the as-built S83 gate (`program.rs:947` single-sig / `:1143` multi-sig, with the reuse legs at `:919`/`:1129`/`:1312`) tested the latter and leaked a `Concrete { got_slot }` for a generic-unconstrained def carrying a `Type::Var`, which reached `classify(Type::Var)` → SIGSEGV (S84 Wave-0 `mono_tier2_generic_adt_field_through_hof_no_crash`). `Concrete { got_slot }` is constructed only when `is_concrete()`; the determined-but-non-concrete unconstrained generic def gets a slot-less `fn_state` sibling to `Constrained`. `Type::is_concrete()` is a `cranelisp-types` public item (the GOT-slot-eligibility predicate; one additive `public-api.txt` line). This is the typecheck-side structural complement of monomorphisation-from-roots (FIXME 0374) and 0375's codegen-side backstop. **The slot-less arm landed (S84 Wave 1, FIXME 0377):** a distinct `UserFnState::Polymorphic(Box<ParametricFn>)` variant, sibling to `Constrained`, carrying `ParametricFn { variant: DefnVariant, scheme: Scheme }` (the body `monomorphise_call` re-checks at concrete types — the same payload `ConstrainedFn` carries, minus the trait-dictionary semantics; a dedicated struct rather than a `ConstrainedFn` reuse so the *why*-distinction stays legible at every exhaustive matcher). `callable_got_slot()` answers `None` structurally; `defined_symbols()` includes it as a mono target (unlike `Constrained`, which is skipped). Both are additive `public-api.txt` lines; `UserFnState`/`DefKind`'s serde shape changing forces a `CACHE_SCHEMA_VERSION` 5→6 bump (`cranelisp-backend/src/cache/mod.rs`) in the same change-set.

**S119 scoping of the S84 ⟺, re-ruled to target-universal (`/arch`, 2026-07-27; re-ruled 2026-07-28, user-directed).** At HEAD the biconditional holds only for **`DefKind::UserFn`**: generic-ADT `Constructor` entries (incl. the `IO.Bind` existential) and the one polymorphic `Primitive{Extern}` (`vec-len`) hold slots over non-concrete schemes under transitional licences (ctor representation-parametricity per I-CT′; the hand-written body's declared contract), and phrasing the invariant universally while those exceptions stood left it unassertable — the shadow in which the S119-censused `adt.rs`/`impl_check.rs` hand-mints hid. (Factual correction of the first ruling's text: `bind` and `catch-runtime-error` are slot-less `DefKind::PrimitiveExtern`, not slotted primitives.) **The target state eliminates the exceptions rather than partitioning the invariant**: the S84 ⟺ becomes universal and kind-free (`slot ⇒ is_concrete()`, whole-table) once the ctor tranche — re-staged 2026-09-01 as an arm of the S121 C1-led unified-lifecycle wash — retires the non-concrete ctor template slot (instances mint per instantiation under the ONE canonical mangler) and `vec-len` de-slots; the surviving polymorphic callables are the closed slot-less by-name ABI roster. Canonical statement + census + route: `design/arch/total-concreteness.md`; transitional record: BC §7 "S119 step-back ruling" + its re-ruling paragraph; register: `safety-invariants.md` §4 R11.

**Mono-instance linker identity is lossless by construction — a single-sourced, total mangler (S102, FIXME 0516; Principle 7 + Principle 20).** A monomorphic instance's slot (above) is one of its two structural identities; the other is its **mangled name** — the symbol-table key under which `register_mono_entry` inserts it and the `LinkerSymbol` the backend emits. That name MUST be a **total, collision-free function of the three distinguishing facts: the DEFINING module (`ModuleFullPath` — `home` when the fn is imported per FIXME 0355, else the current module), the bare fn name, and the recursively-mangled fully-concrete param signature.** The grammar is `{home}/{bare}${recursive-concrete-sig}` where the sig mangler recurses into every concrete `Type` variant (ADT type-args, `Fn` arg+return, `TyConApp`) so no distinguishing type-structure is dropped. **Collision-freedom is by representation (Principle 20): two instantiations that differ in any of the three facts mint different names; the illegal "two distinct instantiations, one name" state is unrepresentable.** The invariant was VIOLATED as-built along two axes — ADT type-args erased (`apply2@(Vec Int)` and `apply2@(Vec String)` both `apply2$Vec+Int` → the 0483 SIGBUS: two instantiations collapse to one body/slot, the surviving String-typed heap elem-dec runs on Int payloads) and home erased (two same-named imported generics `a/iden2`, `b/iden2` both `iden2$Int` → 0508 silent wrong-dispatch). Both are one bug: `build_mangled_name`/`concrete_type_name` dropping distinguishing information. The cure is **one canonical mangler, single-sourced (Principle 7)** — the three as-built stringly sites (`monomorphise.rs::build_mangled_name`/`concrete_type_name`, `program.rs::mangle_type`/`mangle_sig`, and the hand-rolled `seen`-dedup key at `program.rs:~3469`) unify onto it; `mangle_type` already recurses ADT args correctly and is the closer-to-canonical mirror. The name is an **opaque `String`/`LinkerSymbol` at every crate boundary** (produced in typecheck, consumed by name only through GOT-slot dispatch and the linker), so the grammar change is NOT a `public-api.txt` move — but the mangled name is the on-disk `.meta.json` entry identity, so it IS a `CACHE_SCHEMA_VERSION` bump in the same change-set. Any backend-side name that embeds a concrete signature MUST mangle that sig by the same total grammar, else it re-opens the mirror one level down. *(Corrected 2026-09-01: the `__inlwrap_{bare}_{sig}__` family previously cited here as the instance never existed in source — the live fn-as-value wrapper family is the span-keyed `__wrap_{name}_{disc}{start}_{end}__`, which embeds no signature, so the obligation currently binds zero backend names; it binds any future sig-keyed wrapper identity — e.g. `ownership-codegen.md` §13.3 Ruling 1's planned scheme — the moment one is introduced. `total-concreteness.md` §3.2.)*

**The gate is TOTAL — no `monomorphisable-from-params` carve-out; test fns are mono roots (S84 Wave 1b, user-ratified 2026-06-16; FIXME 0378 issue 3; /arch + /int).** The slot⟺`is_concrete()` invariant is *unconditional*. The Wave-1 landing carried a pragmatic carve-out (`fn_type_is_monomorphisable_from_params`, `program.rs:181`) that kept a **result-only-polymorphic** def (`test-* : (Fn [] (Option a))`) `Concrete`-with-a-slot — because such a def has no call-site parameter to monomorphise *from*, and the `/run-tests` names-only discovery reader (`discover_test_names`, `src/session_v4.rs:2533`) found tests via `callable_got_slot()`, so a slot-less test fn would be stranded. The ruling retires this carve-out by making **discovery-driven entry points (test functions) explicit monomorphisation ROOTS**, the same way `main` is the program root: the root carries the discovery contract's expected entry type `(Fn [] (Option String))` (`test_scheme_is_eligible`, `src/session_v4.rs:2816`), and `pass4_monomorphise` mints a concrete `Concrete{slot}` instance from the polymorphic original at that type. This is no new boundary type — the minted instance is an ordinary `MonoDefn`/`Defn` `Concrete` `UserFn` entry, found through the existing symbol-table lookup + `callable_got_slot()` chokepoint. The cross-crate seam is **mechanism-only** (typecheck registers the root; int's names-only reader resolves to the concrete instance's name instead of the original's now-absent slot — preferred shape: the concretised entry registers under the bare name so the reader stays byte-identical). **No `cranelisp-types` change, no `public-api.txt` move, no cache bump** — the `Polymorphic` variant from FIXME 0377 already supplies the slot-less state the now-slot-less result-only-polymorphic def lands in. Full statement: BC §2 "The slot gate is TOTAL" + the mono-root rule + the discovery-seam paragraphs.

**`Type::is_representation_undetermined()` — RETIRING (gated on /dev; the WRONG predicate under the tightened §3.11.1, commit `2290aa9`).** This predicate embodies the now-REJECTED *representation-determinacy* notion: it returns `false` for `(Vec a)`/`(Fn a)` ("uniformly heap — admit the unpinned var"), which the tightened §3.11.1 now **rejects** (the strictness is full concreteness — no `Var` — with NO representation-based exemption). It is NOT the §3.11.1 verdict; the correct verdict is `!is_concrete()` (`ConcreteType::from_type(ty).is_err()`), which rejects ANY residual free var. **Retirement from `cranelisp-types` is gated on /dev switching the §3.11.1 call site** (`cranelisp-typecheck::program::is_codegen_ambiguous_type`) off it (FIXME 0386); kept-but-deprecated until then (removing it now breaks the typecheck build, which still calls it). On retirement: one `public-api.txt` removal line. The backend `heap.rs` references are comments only (the FIXME-0375/0381 backstop is deferred). See `design/arch/concrete-boundary-type.md` §1.4/§3.1. The original (now-superseded) narrative follows for the interim-state record:

**(SUPERSEDED) The shared codegen-ambiguity predicate (S84 Wave 2, user-ratified 2026-06-16; FIXME 0379).** A second `cranelisp-types` public item on `Type` (one additive `public-api.txt` line: `pub fn cranelisp_types::Type::is_representation_undetermined(&self) -> bool`; no cache bump — a pure `&self -> bool` adds no serde shape). It is **THE single source of truth** for "does this `Type` carry a representation-undetermined free `Type::Var` at a codegen/RC site," shared by two consumers so typecheck and backend **agree by construction** (Principle 7 + Principle 18): the typecheck-side position-complete §3.11.1 ambiguity check (FIXME 0379, /dev) uses it **directly** as the ambiguity verdict at every codegen-reaching value position; the backend-side RC backstop (FIXME 0375, /dev) gates it **behind its own `classify == Mixed`** verdict (`panic iff classify == Mixed && is_representation_undetermined()`). **TRUE** for a bare `Type::Var`, a `Type::TyConApp` (HKT head var), and a non-`Vec` `Type::ADT` carrying a free var (the `Mixed`-family case the bare-`Var` panic missed); **FALSE** for `Type::Fn` and `(Vec a)` (uniformly heap, `classify`→`AlwaysHeap` regardless of the free var), any fully concrete type, and a `Type::ADT` with no free var (the legitimate type-known nullary-tag `Mixed` case). It is **table-free and structural** — it captures the "carries a free var in a representation-bearing position" half; the backend supplies the "is `Mixed`-shaped" half from the symbol tables, which is what excludes a table-determined `NeverHeap`/`AlwaysHeap` ADT carrying a free var from the backend panic. Distinct from `is_concrete()`: `is_concrete()` is the **GOT-slot-eligibility** predicate (does this def get a slot?); `is_representation_undetermined()` is the **codegen-RC-ambiguity** predicate (is this value's machine shape decidable at an RC site?) — and they differ precisely on the uniformly-heap shapes, which are non-concrete (no slot) yet representation-determined (`(Vec a)`, `Fn`). Full statement: BC §3 invariant 9 "belt-and-braces" + `crates/cranelisp-types/src/types.rs` rustdoc.

**`ConcreteType` — the concrete-only codegen-boundary type (S84 user ruling 2026-06-16; Phase-1 scaffold landed; `design/arch/concrete-boundary-type.md`; FIXME 0383).** The user re-direction: generics should not be *representable* at the backend boundary at all. `ConcreteType` (`crates/cranelisp-types/src/concrete.rs`) is the concrete subset of `Type` — Int/Bool/String/Float, concrete `Fn`, concrete `ADT(FQTypeName, Vec<ConcreteType>)` — with **NO `Var` and NO `TyConApp` variant** (recursion on `ConcreteType`, so concreteness is total at every depth; derives `Eq+Hash`, which `Type` cannot). The **single fallible conversion** `ConcreteType::from_type(&Type) -> Result<ConcreteType, NotConcrete>` succeeds iff fully concrete; its `Err(NotConcrete::Var | HktHead)` IS the unified ambiguity/could-not-monomorphise error that today scatters across three guards (the §3.11.1 check, mono-failure, `classify(Var)` panic). This is Principle 18 applied to the boundary type itself — the fullest expression of Principle 20: where the slot gate made *callability* structural, `ConcreteType` makes *value-representation* structural. **Disposition vs the two predicates above:** once the arc's Phase 3 lands (`HeapCategory::classify` takes `ConcreteType`), `is_representation_undetermined()` and the §3.11.1 standalone scan are **subsumed by the conversion** and retired; `is_concrete()` survives, re-expressed as `from_type(..).is_ok()`, still the typecheck slot-gate predicate (it operates on `Type` *before* conversion). The boundary backstops (FIXME 0375/0381) are **deleted, not re-armed** — a `Type::Var` becomes inexpressible at the seam. **Phase-1 scaffold (landed):** the type + conversion + `NotConcrete`, additive `public-api.txt` (27 lines), no cache bump, dead code until Phase 2 (mono produces it) + Phase 3 (backend consumes it). Full arc + honest per-phase sizing: `design/arch/concrete-boundary-type.md`.

**`MonoExpr` — the post-monomorphisation codegen AST (S84 concrete-boundary arc Phase 2a, landed; `design/arch/concrete-boundary-type.md` §2.4; FIXME 0383).** A parallel codegen view of `Expr` (`crates/cranelisp-types/src/mono_expr.rs`) whose every node carries `ty: ConcreteType` **non-optionally** in place of `Expr`'s `inferred_type: Option<Box<Type>>` — a generic / `Type::Var` is *structurally unrepresentable* on a codegen node (there is no `Type` field on `MonoExpr` at all; the fullest expression of the user ruling — generics "shouldn't even be REPRESENTABLE there"). `MonoExpr` mirrors `Expr`'s 14 non-`Annotate` variants; the `Annotate` node is **erased** (collapsed to its inner node at build); `Lambda` param `TypeExpr` annotations are erased (the concrete param types ride in the lambda's `ConcreteType::Fn`); match arms are carried by a sibling `MonoMatchArm { pattern: Pattern, body: MonoExpr, span }` (pattern reused verbatim — it carries no type annotation; S109 §10 later adds `resolved_ctor: Option<FQSymbol>`); `Apply`/`Var` carry `resolved_call: Option<Box<ResolvedCall>>` and every node carries `span: Span` (S110 0583 moved the resolved STORAGE identity onto the nodes as `resolved_target: Option<FQSymbol>`; the S114 carrier flip retyped it as the non-optional `Var.resolution: VarRef` / `Apply.dispatch: ApplyRef` — see §Method Resolutions). The mono-defn wrapper is `MonoDefnVariant { name: Symbol, params: Vec<Symbol>, body: MonoExpr, span }` (the typecheck mono pass builds it at the Phase-2b seam — `monomorphise_call`, immediately after `apply_subst_to_defn`). The **fallible builder** `MonoExpr::from_expr(&Expr, ..) -> Result<MonoExpr, ViewBuildError>` (the signature carries three REQUIRED span-keyed sidecar parameters — `pattern_ctors` + the typed `var_refs`/`apply_refs` since S114; the lenient counterpart `lenient_from_expr` and the all-local `synthetic_local_from_expr` live beside it — §Method Resolutions) walks an `inferred_type`-annotated `Expr`, converting each node via `ConcreteType::from_type`, and **fails at the first non-concrete node** (`ViewBuildError::NotConcrete` wrapping `NotConcrete::Var`/`HktHead`; an un-annotated node is the `NotConcrete::Var(0)` sentinel) **or resolution-verdict miss** (`ViewBuildError::Unresolved{span,name}` — the located phase-boundary gate) — the `NotConcrete` failure is the unified ambiguity/could-not-monomorphise error. Derives `Debug, Clone, Serialize, Deserialize` (no `PartialEq`/`Eq` — `Expr` cannot, carrying `f64`); accessors `span()`/`ty()`. **Phase 2a (landed):** the representation + builder + 10 unit tests, additive `public-api.txt`, **`CACHE_SCHEMA_VERSION` bumped 6 → 7** (the mono serde shape participates in the cached `.meta.json` surface). Produces-but-unused for codegen — the backend still reads `Expr.inferred_type` until Phase 3; the typecheck mono pass wires `from_expr` in Phase 2b (/dev(typecheck)).

**`ModuleEntry::Def.codegen_view` — the concrete-boundary threading field (S84 concrete-boundary arc Phase 3, threading shape LANDED; `design/arch/concrete-boundary-type.md` §3.0/§4 Phase 3).** The threading decision — how `MonoExpr` reaches the backend per codegen-bound entry — is ruled **option (a), additive field**: `ModuleEntry::Def` gains `codegen_view: Option<MonoDefnVariant>` (`crates/cranelisp-types/src/module.rs`) **alongside** the existing `ast: Option<DefnVariant>`. The backend's Phase-3 read path consumes `codegen_view`'s `MonoDefnVariant.body: MonoExpr` — `ty: ConcreteType` on every node, so **no `Type`/`Var` on the read path by construction** (Principle 18/20). Read through `ModuleEntry::codegen_view(&self) -> Option<&MonoDefnVariant>` (`None` for non-`Def` and non-codegen entries); populated via `DefBuilder::codegen_view(self, MonoDefnVariant) -> Self`. **NOT a type-swap of `ast`** (`Option<DefnVariant>` → `Option<MonoDefnVariant>` would break ~26 literal-construction sites + the `Defn`-reconstruction path at once — a non-green cascade); the additive field defaults `None`, keeping the build green and letting /dev migrate the read path incrementally. **NOT a separate structure `compile_to_module` takes** (rejected — that re-introduces the transitional parallel-`Vec` shape at the crate boundary; the view belongs ON the entry, the symbol table being the per-symbol codegen-input carrier, Principle 7). **Populated for BOTH codegen-bound cases:** monomorphised instances (the mono-population seam moves the already-built `MonoDefnVariant` off the transitional `CheckState.mono_variants` parallel `Vec` onto the entry — `register_mono_entry`), AND ordinary concrete (`UserFnState::Concrete`) defns (the same `MonoExpr::from_expr` over the annotated body at the body-check `.ast(...)` sites). Template kinds / primitives / special forms get `None` — correctly not codegen targets. **Landed:** the field + accessor + setter (+3 additive `public-api.txt` lines), `CACHE_SCHEMA_VERSION` **7 → 8** (the serialized `ModuleEntry::Def` shape changed; `#[serde(default)]` field, no pointer/`C` state). The backend's consumption (classify-becomes-total, the ~13 `inferred_type` read sites → `MonoExpr.ty()`, `compile_to_module` reads `codegen_view`, the single relocated `expect` backstop) is /dev(backend) — FIXME 0391; the typecheck population move is /dev(typecheck) — FIXME 0392.

**The callable-slot witness — `CallableSlot` + `SymbolTable::mint_callable_slot` (S119 types-first slice, landed; `design/arch/concreteness-types-first.md` §3).** The slot⟺concrete invariant's mint side becomes vocabulary: `CallableSlot` is an opaque `#[serde(transparent)]` newtype whose field is private — outside `cranelisp-types` a value is obtainable ONLY from the fallible `SymbolTable::mint_callable_slot(scheme)` (checks `scheme.ty.is_concrete()` via the witness-producing `ConcreteType::from_type` AND allocates from `next_got_slot` in one act; refusals are cursor-stable), from `CallableSlot::rebind(scheme)` (the Decision-31 REPL slot-reuse path, re-checked), or from deserialization (which is why the cache load boundary re-checks restored slot-carrying entries — the backend-wash `CacheStale::NonConcreteSlot` arm). `SlotMintError { NotConcrete, Exhausted }` carries the located refusal. The kind-field retypes onto `CallableSlot` — and `DefKind::Constructor`'s flip onto the landed-DORMANT `CtorState { Template, Concrete { got_slot: CallableSlot } }` sum (wire shape pinned by `module/tests.rs::ctor_state_serde_shape_pin`) — were the pinned per-kind wash (FIXME 0931), **superseded 2026-09-01 by the adopted unified lifecycle machine** (`symbol-table-lifecycle.md`; §"Module System" banner above): the slot lands on `Life::Concrete` via the same witness mint, the dormant `CtorState` deletes unwired, and `allocate_got_slot` retires into the settlement funnel in the S121 C1-led wash. Companion projections landed with it: `heap::ctor_field_types_at(table, ctor_key, args)` (the instantiation-substituting ctor-field derivation — concrete-or-refuse via `CtorFieldsAtError`, never fabricating; the backend's `unwrap_or(Type::Int)` walk retires onto it, R-13) and `ConcreteType::result_root()` (the ONE single-hop IO-head-strip rule, FIXME 0898 — at HEAD the rule has **three** encodings, not two: the method itself, which has zero production callers until the collapse, plus the two literal twins — backend `compile_to_module`'s `result_roots` map (S121 C4 bundle B6) and int's `src/result_owner.rs::strip_io_head`, sole caller `release_key` (S121 C6 bundle N6b) — both re-express over the method and delete; the filing deletes only when both are collapsed).

**Written-impl cache carrier — `WrittenTraitImpl` + `enrol_written_trait_impl` + `trait_impl_key` (S119, FIXME 0869; canonical: `design/arch/trait-impl-cache-carrier.md`).** The writer-side persistence projection of the Decision-45 discovery shell: `SymbolTable.written_trait_impls: Vec<WrittenTraitImpl>` (serde-visible, **no `#[serde(default)]`** — a pre-carrier sidecar is a hard parse error, wholesale invalidation), upserted by typecheck at the successful `register_trait_impl` registration seam (`traits/impl_check.rs:94`, invoked from `program/register.rs:66`; the formerly-cited `check_trait_impl` was a phantom — no such symbol exists; corrected S121 Phase 3), consumed at restore through the ONE idempotent enrolment primitive `enrol_written_trait_impl` (Enrolled / AlreadyEnrolled / hard-error-on-divergence — never a silent pick) over the trait home's table. Fresh registration stages the shell with an opaque retain-prior token, rolls it back with method entries on failure, and upserts the writer record only after every method settles; restore never uses that provisional path. `trait_impl_key(&FQTypeName, &FQTraitName)` is the hoisted ONE mint of the `impl$` storage key (the `member_key` pattern; the two hand-rolled typecheck format sites re-point in the wash), discharging the R4 census for that family. The `CACHE_SCHEMA_VERSION` 23→24 window rode the introducing change-set — the ONE S119 bump, which the injective `got_data_symbol_name` escape (FIXME 0748 — cached `.o` relocation names change) and the in-sprint downstream waves shared. **S121 status:** C3 owns the producer/transaction completion and C6 N3 the restore enrolment, with no further schema increment (`trait-impl-cache-carrier.md` §9 — the C6 H1 blocker's discharge).

**Ownership-inference carriers — `Mode`/`ModeSummary` + the `PrimitiveBody` reshape (S102 CS-A, landed; `design/arch/ownership-inference.md` §3.3; typecheck needs-list `design/typecheck/ownership-inference.md` §13.1; FIXME 0476).** The single increment-I `cranelisp-types` change-set (one `CACHE_SCHEMA_VERSION` bump, 11 → 12). New module `crates/cranelisp-types/src/ownership.rs`: the mode lattice **`Mode { Copy, Borrowed, Owned }`** (Owned = default = the Decision-24 ⊤ point), **`ResultMode { Fresh, ProjectionOf(i), AliasOf(i) }`**, **`ParamFlow { Consumed, IntoResult, Retained }`**, and the per-callable **`ModeSummary`** — ABI-bearing half (`param_modes`, `result`; compared by `abi_eq`/`abi_eq_opt`, the ONE definition serving the R3 summary-diff gate) + advisory half (`param_flow`, `spark_ops`, `result_unique`; sound to ignore). Full `Eq` (fixpoint change detection); every field `#[serde(default)]`; **⊤-on-absence lives in ONE home** — the conservative-read accessors `param_mode(i)`→`Owned`, `param_flow(i)`→`Retained`, `spark_op(i)`→`true`; no consumer indexes the vectors directly. The summary rides the **callable `DefKind` variants** (the S83 slot precedent: `UserFnState::Concrete`, `Primitive`, `Constructor`, `PlatformEffect` — non-callable kinds carry no summary field by construction) read/written via `ModuleEntry::mode_summary()` / `set_mode_summary()` (did-write bool), plus `MonoDefnVariant.mode_summary` as the compile-in-hand carrier; `DefKind::Primitive`'s slot doubles as the **hand-declared fact table** (spine §3.1(a), Principle 19 — same carrier, no separate type). Advisory **site facts** ride `MonoExpr` alloc/capture nodes (`escapes`/`confined`/`unique_static` on `StringLit`/`Lambda`/`Apply`/`VecLit`/`ConstrADT`, `provenance: Option<Symbol>` on `Apply` + `MonoMatchArm`; all `#[serde(default)]` = `None` = conservative); the per-entry **`value_use: bool` mark** rides `ModuleEntry::Def` (accessors `value_use()`/`set_value_use()`). The **FIXME-0476 representation cure rides the same bump**: `DefKind::Primitive { got_slot }` reshapes to `Primitive { body: PrimitiveBody, mode_summary }` with `PrimitiveBody::Extern { got_slot, borrowed_sibling_slot: Option<usize> }` (the §3.1(b) borrowed-convention sibling carrier — Extern-arm-only, so inline-with-sibling is unrepresentable) vs `PrimitiveBody::Inline` (slot-less **by construction** — `callable_got_slot()` answers `None` structurally; the allocated-but-NULL phantom-slot class is unrepresentable one level down from S83); the new **`ModuleEntry::is_callable_target()`** (slot-dispatched ∪ inline-dispatched) is the resolution stop condition replacing `callable_got_slot().is_some()`, with `DefKind::primitive(slot)` as the common-shape convenience ctor. The read-once **`CRANELISP_NO_OWNERSHIP`** gate relocated here as `ownership_analysis_off()` (needs-list item 12: typecheck's pass entry and backend's manifest key + emission gates read ONE polarity through ONE function — Principle 7; `cranelisp-backend::cache::manifest::no_ownership_enabled` now delegates). CS-A is **carrier-only**: as of the landing, `PrimitiveBody::Inline` has zero constructors and `mode_summary`/site facts are written by nothing — the S102 B1-be change-set (backend+primitives) flips the vec trio to `Inline` and retires the S101 name-list resolver; typecheck CS-1..4 produce summaries. `public-api.txt` regenerated (cranelisp-types only; the six consumer baselines verified unchanged).

**`ResultMode::MayAliasOf(usize)` — PINNED S111 Phase 3; lands in the S111 Phase-5 schema-20 ownership wave, NOT before (`design/arch/ownership-inference.md` §3.7 — the COW result-mode ruling; completeness matrix §3.7.1).** The exact enum diff:

```rust
// crates/cranelisp-types/src/ownership.rs — ONE added variant, nothing else moves
pub enum ResultMode {
    #[default]
    Fresh,
    ProjectionOf(usize),
    AliasOf(usize),
    /// The result EITHER is a fresh value OR reaches into param *i* — the
    /// param itself or a view rooted in it — decided at runtime (the COW
    /// pair: copy arm vs rc==1 in-place arm; a conditional projection).
    /// The consumer must never elide protection on it, and must never
    /// assume it reaches the param. `AliasOf`/`ProjectionOf` are reserved
    /// for provable UNCONDITIONAL claims. (§3.7/§3.7.1; S111.)
    MayAliasOf(usize),
}
```

Same-change-set cascade (why it does NOT land at Phase 3): the variant is serde-visible on persisted summaries ⇒ **`CACHE_SCHEMA_VERSION` 19→20** in `cranelisp-backend/src/cache/mod.rs`; the **0621 `callees` → `storage_fq()` rider shares the ONE bump window** (two persisted-meaning changes, one schema flip — a cache written between two separate bumps would carry schema-20 with alias `callees`); types `public-api.txt` +1 line; the truthful `ownership_facts.rs` declarations (`vec-set`/`vec-push` → `MayAliasOf(0)`) and the prelude-fallback-aware ownership envs land with it (a1 without a2 has no producer; a2 without a3 is dead code — §3.7). Consumer census, pinned 2026-07-17: **one compiler-forced exhaustive match** — `cranelisp-typecheck/src/ownership/transfer.rs:592–609` gains the `MayAliasOf(k)` arm (join of `Fresh` with `arg_origins[k]`; a param-reaching arg yields `Origin::MayParam`, never collapses to `Fresh` — the 0520 rule) — and **exactly two grep escapes** that compile silently and are each safe-direction for the new variant: backend `return_is_fresh_by_summary` (`fn_compiler.rs:1722`, `== Fresh` ⇒ `protect_return_value` KEPT) and `ModeSummary::is_abi_conservative` (`ownership.rs:201`, `== Fresh` ⇒ `MayAliasOf` classifies non-conservative). `abi_eq` (`ownership.rs:194`) compares two carried values variant-agnostically — safe by construction (`MayAliasOf(0) ≠ Fresh` is an R3 ABI-changing redefinition, which is correct). Sweep confirmed **no third escape** (`uniqueness.rs` hits are comments; `transfer.rs:546` matches `Origin`, not `ResultMode`); `/review` re-runs the grep on the landing change-set. The producer flip rides the same wave: `origin_to_result_mode` (`transfer.rs:237–252`) publishes `MayAliasOf(idx)` for **BOTH** `MayParam` body origins — `projection:false` (was hard `AliasOf`) **and** `projection:true` (was hard `ProjectionOf`; S111 Phase-3 `/arch` ruling on the `/design`(typecheck) proposal — a may-projection is a conditional claim, and §3.7's reservation clause already restricts `AliasOf`/`ProjectionOf` to provable unconditional claims). The unconditional arms stay: `Origin::Root → AliasOf`, `Origin::Projection → ProjectionOf` (the flagship bare-accessor precision is untouched). The collapse is honest under the variant claim above (identity-or-view) and retain-side-only: both consumer reads are indifferent to the identity-vs-view distinction at the May point (the transfer join yields a protected `MayParam` origin; the backend read is binary `== Fresh` ⇒ protect kept). The mode enums' deliberate **no-`#[non_exhaustive]` exception** is recorded in `ownership.rs`'s module rustdoc §"Exhaustiveness discipline" + the types `CLAUDE.md` exception list (S111 Phase 3).

**`ResultMode::MayAliasAny` — the result axis's ⊤; types half LANDED S121, consumers pending in the same wave (`design/arch/ownership-inference.md` §6.1; interior design `design/typecheck/ownership-inference.md` §19).** The variant FIXME 0521 deferred "until a reader arrives" — the reader turned out to be the producer itself. Before it, "the result reaches SOME parameter, which one undetermined" had no representation, so `origin_to_result_mode`'s lowest-index representative had no join target: a parameter-permuting self-call (`(defn f [i b] (if (eq-i64 i 0) b (f b i)))`) walked the involution `r ↦ 1 − r` forever, hit the visit cap, and "recovered" by publishing `fixpoint::top()` — whose `result: Fresh` is the axis's STRONGEST claim, not its ⊤ — for every callable in the module. The callee then elided its return protect on a body that returns a parameter (`return_is_fresh_by_summary`), releasing the accumulator at scope exit and returning a freed pointer: the S121 f4 SIGSEGV and the v23 garbage values. The exact enum diff, one added variant, nothing else moved:

```rust
// crates/cranelisp-types/src/ownership.rs — ONE added variant
pub enum ResultMode {
    #[default]
    Fresh,
    ProjectionOf(usize),
    AliasOf(usize),
    MayAliasOf(usize),
    /// The result EITHER is a fresh value OR reaches into SOME parameter —
    /// which one is not determined (the join of may-alias claims on distinct
    /// parameters). The ⊤ of the result axis: the consumer must keep
    /// protection and must not assume any particular parameter is reached.
    /// Carries no index, so the cache's persisted-index (`k < arity`) check
    /// does not apply to it. (§19.2; S121.)
    MayAliasAny,
}
```

Named `MayAliasAny` rather than 0521's recorded `AliasOfAny` because it is the join of *conditional* claims, and the `AliasOf` prefix is reserved for provable unconditional ones (§3.7's reservation clause). **`Default`, `abi_eq`, `abi_eq_opt` and `is_abi_conservative` are unchanged** — `MayAliasAny ≠ Fresh` makes it non-conservative and ABI-distinct by construction, exactly as `MayAliasOf` landed, so a `MayAliasOf(k) → MayAliasAny` redefinition is correctly an R3 ABI change. Generated baseline effect: **exactly +1 line, 0 removals**, `pub cranelisp_types::ResultMode::MayAliasAny`, sorted between `Fresh` and `MayAliasOf(usize)`; no other crate's baseline moves (`result_mode_param_index` is `pub(crate)`, typecheck's readers are private). Types unit pin: `ownership/tests.rs::may_alias_any_is_top_indexless_non_conservative_and_serde_stable` (⊤-ness, index-lessness, non-conservative at both `== Fresh` reads, persisted unit-variant spelling, ABI-distinctness from `Fresh` and from every `MayAliasOf(k)`), proven to detect against two planted faults — `is_abi_conservative` admitting `MayAliasAny`, and a serde rename — with the negative leg green.

**Consumer census, verified at source 2026-09-07 — the wave is types → typecheck → backend cache, and the tree does NOT compile between the reservations by design** (`ResultMode` carries no `#[non_exhaustive]`, so the variant is what forces each consumer match to be revisited). **Two compiler-forced exhaustive matches**, both outside this reservation: `cranelisp-typecheck/src/ownership/transfer.rs` (`walk_apply`'s conditional-result arm + `origin_to_result_mode`/`join_origin`'s reach-set join — §19.3/§19.4) and `cranelisp-backend/src/cache/serialize.rs::result_mode_param_index` (`MayAliasAny => None`, no index ⇒ no arity check, plus its R6 negative cell). One further forced match is a backend **test** helper, `compiler/rc_emission/return_ownership_tests.rs::forwarded_result_clif` (arms `Fresh` / `ProjectionOf(_)` / `AliasOf(_) | MayAliasOf(_)`, no `_` arm). **Exactly two silent grep escapes**, both safe-direction and unchanged: backend `return_is_fresh_by_summary` (`fn_compiler.rs:3353`, `== Fresh` ⇒ `protect_return_value` KEPT) and `ModeSummary::is_abi_conservative` (`ownership.rs`, `== Fresh` ⇒ `MayAliasAny` classifies non-conservative). The S121 re-run of the standing `_ =>`/`== Fresh` escape grep confirmed **no third binary read** (`src/redefine.rs::format_ownership_abi` uses `{:?}` — a display, not a decision; `cranelisp-primitives/src/ownership_facts.rs` only constructs, and no leaf declares the new point). Platform ABI, DLL manifest and `ABI_VERSION` have no `ModeSummary` contact at all. **Schema:** the variant is serde-visible on persisted summaries ⇒ **`CACHE_SCHEMA_VERSION` 26→27** with its version-log entry, owned by the backend-cache reservation — also a soundness invalidation, because a sidecar written by the pre-fix tree may carry the unsafe present-`Fresh` ⊤ for a permuting body.

### Residual `CheckResult` — typecheck-internal only

```rust
/// Transient typecheck output. NOT a boundary type. Owned by
/// `cranelisp-typecheck`; never serialised, never passed into the
/// backend.
///
/// Its remaining role is to carry diagnostics and the optional REPL
/// display payload out of `TypeChecker::check` to its immediate caller
/// (the integration layer in `src/`). All durable typecheck output is
/// deposited onto `SymbolTable` entries before `check` returns.
#[derive(Debug)]
pub struct CheckResult {
    /// Non-fatal warnings accumulated during checking.
    pub warnings: Vec<Warning>,

    /// Display information for the REPL (last Expr or Defn in the input).
    /// `None` in batch / module-load mode.
    pub display: Option<DisplayInfo>,
}

/// REPL display payload.
#[derive(Debug, Clone)]
pub struct DisplayInfo {
    /// Inferred type of the expression or definition.
    pub ty: Type,
    /// Generalized scheme (for defn). None for bare expressions.
    pub scheme: Option<Scheme>,
}
```

**Current status**: the struct definition in `crates/cranelisp-types/src/check.rs` still carries the legacy fields as typecheck-internal working state during the Phase 1 -> Phase 2 transition. A FIXME filed by `/typecheck` on that file tracks Phase 5 slimming to exactly `warnings + display`. The legacy fields are not a backend contract — `compile_to_module` no longer takes `CheckResult`. (Principle 2 — narrow interfaces; Principle 13 — `interfaces.md` is auditable.)

**No adapter functions.** `build_check_for_backend()` and `ReplCheckResult` remain deleted. No function converts `CheckResult` into a backend input — the backend input is `SymbolTable::defined_symbols()` (see below).

### Method Resolutions

```rust
/// Typecheck's span-keyed resolution sidecars. A `#[non_exhaustive]` newtype
/// struct since S69 (the v1 `type MethodResolutions = HashMap<Span, ResolvedCall>`
/// alias is retired — S-DRIFT-8); `pattern_ctors` added S70 (finding #4,
/// Decision 47); `resolved_targets` added S110 (FIXME 0583), split into the
/// TOTAL typed `var_refs` + `apply_refs` at the S114 carrier flip.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[non_exhaustive]
pub struct MethodResolutions {
    /// Per-`Apply`-span resolution: how typecheck resolved each call site.
    pub resolved_calls: HashMap<Span, ResolvedCall>,
    /// Per-`Pattern::Constructor`-span FQ resolution (Decision 47).
    pub pattern_ctors: HashMap<Span, FQSymbol>,
    /// Per-`Var`-span typed verdict — TOTAL over the check-run's Vars
    /// (S114 carrier flip). See the carrier narrative below.
    pub var_refs: HashMap<Span, VarRef>,
    /// Per-`Apply`-span typed dispatch verdict — TOTAL over the check-run's
    /// Applys (`Dispatch` or the POSITIVE `ViaCallee`).
    pub apply_refs: HashMap<Span, ApplyRef>,
}

/// How a function call was resolved by the typechecker.
/// (`FQTraitName`/`FQTypeName` per Decision 47; `JitSymbol` per the newtype table.)
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ResolvedCall {
    TraitMethod {
        trait_name: FQTraitName,
        method_name: Symbol,
        impl_type: FQTypeName,
        mangled_name: JitSymbol,
        /// The module whose table stores the selected mangled method `Def`
        /// (the impl-WRITER's module — S110 W0.1b; amended Decision 45).
        /// REQUIRED (no `#[serde(default)]`, Principles 18/20).
        impl_module: ModuleFullPath,
    },
    SigDispatch { mangled_name: JitSymbol },
    AutoCurry {
        target_name: Symbol,
        applied_count: usize,
        total_count: usize,
        trait_resolution: Option<Box<ResolvedCall>>,
    },
    BuiltinFn { name: Symbol },
}
```

**`VarRef` / `ApplyRef` — the typed keyed-consumer carrier (S110 0583 `resolved_targets` → S114 FIXME 0653 prong-3 flip, LANDED types-side in the S114 Phase-5 carrier wave; `design/arch/typed-resolution-carrier.md`; corollary at `principles/24-resolve-once.md`).** The one carrier behind the backend-as-pure-keyed-lookup-consumer contract (Principle 24 "Resolve once"; BC §3 invariant 10 is the consumer statement, BC §2 the producer obligation — this paragraph narrates the types surface, not those). The S110 `Option<FQSymbol>` shape conflated "local by design" with "unresolved by producer bug" under one `None` (the S113 check-gate-leak class); the S114 flip closes the dichotomy IN THE TYPE with two CLOSED sums constructed only by typecheck — `VarRef::Local { binder, binding_span } | VarRef::Global(FQSymbol)` (binder identity carried — the bound name + the binding FORM's span; frame/slot mapping stays backend-side) and `ApplyRef::Dispatch(FQSymbol) | ApplyRef::ViaCallee` (the Apply's third legal state gets its own constructor; `ViaCallee` is a POSITIVE verdict — typecheck asserts there is no Apply-level dispatch selection). **"Unresolved" has no constructor.** Both sums are deliberately NOT `#[non_exhaustive]` (closed sum = the contract; the ownership-mode-vocabulary exception class), and neither node field carries `#[serde(default)]` — absence is unrepresentable, in the cache as in the code. Three pieces, one identity:

- **The sidecars** — `var_refs: HashMap<Span, VarRef>` (keyed by `Expr::Var.span`) + `apply_refs: HashMap<Span, ApplyRef>` (keyed by `Expr::Apply.span`), both TOTAL over the paired check-run's references: locals record `VarRef::Local`, dispatch-less applies record `ApplyRef::ViaCallee` — the old "no entry means local" convention is retired, and the split retires the latent Var-span/Apply-span collision hazard of the shared map.
- **The mono-view fields** — `MonoExpr::Var.resolution: VarRef` / `MonoExpr::Apply.dispatch: ApplyRef` (`mono_expr.rs`, non-optional), populated at view-build. The backend matches exhaustively: `Local` → scope-stack read (a miss is a hard invariant failure carrying the binder identity), `Global`/`Dispatch` → ONE `entry_at` keyed fetch, `ViaCallee` → the callee's own carrier governs. It never re-resolves a name.
- **The gate + the unforgettable parameters** — `MonoExpr::from_expr(expr, pattern_ctors, var_refs, apply_refs) -> Result<MonoExpr, ViewBuildError>` where `ViewBuildError { NotConcrete(NotConcrete), Unresolved { span, name } }`: a real-span reference with no verdict is the LOCATED `Unresolved` typecheck-phase error (read BEFORE the node type, so a resolution miss can never slip into the `NotConcrete` lenient fallback); `NotConcrete` keeps the legitimate type-tolerance fallback route. `lenient_from_expr` (same parameters, infallible) tolerates TYPES only — its real-span resolution miss is an always-on tier-3 seam panic (`safety-invariants.md` §2), never a manufactured `Local`. Synthetic bodies (`Span::SYNTHETIC` on every node) are structurally outside span-keyed transport: they go through the sanctioned all-local builder `synthetic_local_from_expr(expr, pattern_ctors)` (FIXME 0685 — no resolution-map parameters, always-on synthetic-span assert), realized as the SYNTHETIC carve-out of the ONE shared walk (a synthetic-span miss takes `VarRef::Local { binding_span: SYNTHETIC }` / `ApplyRef::ViaCallee`; a map entry under the SYNTHETIC key still wins). View construction has ONE home in `cranelisp-types`; typecheck is the sole mono-view producer.
- **The pure-TYPE probe** — `is_strict_type_concrete(&Expr) -> bool` (`mono_expr.rs`, exported beside the gate; FIXME 0689 / the S114-W2-review mirror fence): the TYPE half of the `from_expr` gate DECOUPLED from the resolution gate — `Annotate` erased, every other node's `inferred_type` must convert via `ConcreteType::from_type`, per-arm child coverage pinned to `from_expr` by same-file exhaustive matches (a new `Expr` variant breaks both in one compile). Exists because the flip coupled type + resolution inside `from_expr` (empty maps ⇒ `Unresolved` on any real-span reference), so `from_expr` can no longer answer the pure type question. Sole out-of-crate consumer today: the ownership fixpoint's W0.b universe pin (`cranelisp-typecheck::ownership::fixpoint::collect_universe` — pre-flip strict-universe membership: mono instances + genuine concrete defns in; ctor/accessor synthesis + lenient-fallback bodies out).

**Semantics — "whichever storage key HIT" (§1.1).** The `FQSymbol` inside `Global`/`Dispatch` is the *storage* identity: module + the exact symbol-table key the typecheck resolution terminated at (bare `m/f`; canonical `m/Type.Ctor` for sum ctors and accessors; mangled `m/f$Int+Int` / `m/Trait.method$Type` for mono/dispatch instances; `primitives/add-i64` for a primitive). It is NOT the written name and NOT a display name. The binding **value-source rule** (§1.1.2, the FIXME-0620 close): every insert comes from exactly one of *walk-resolved* (`Resolved::storage_fq()` — see "The two identities on `Resolved`" under §"Resolution primitive" below; `Resolved.fq` composes the WRITTEN spelling, which is an alias for member-canonical keys and renamed imports), *mint-resolved* (the exact probe/registration key in hand at the seam), or *transport* (copying an existing carrier entry to a new span). A value composed from a written spelling is the 0620 defect class. The per-kind carrier-value matrix, the recorder census, and the map-provenance (check-run pairing) rule live in `backend-keyed-consumer.md` §1.1.2–§1.1.3 — not duplicated here; per-field authority is the `check.rs` / `mono_expr.rs` rustdoc. Cache: the S110 carrier fields rode `CACHE_SCHEMA_VERSION` 18→19; the S114 typed reshape rides 21→22 — ONE window shared with the B-2 escape-fact correction (`cache/mod.rs` version log).

`resolved_calls` stays supplementary dispatch metadata (inline-builtin intercepts, auto-curry counts, trait resolution for the as-value wrapper) — the backend never reads it as the keyed-lookup carrier; `var_refs`/`apply_refs` are the ONE carrier pair.

**`ResolvedCall::TraitMethod.impl_module` — the dispatch-leg storage module (S110 W0.1b `144828d1`; `backend-keyed-consumer.md` §1.1.1).** The resolution PRODUCT half of the amended Decision 45 (see §Module Entries below for the `ModuleEntry::TraitImpl.impl_module` twin): a trait-leg's selected mangled method `Def` lives in the impl-WRITER's module, not the trait's home and not the caller's. `try_resolve_trait_method` reads the module off the `TraitImpl` shell that grounds the selected mangle and records it here, where the resolution happens; downstream consumers (`dispatch_target_fq`, the `callees` edge) READ the field, never re-derive — deriving it as `current_module` was the W0.1 gap (wrong for every cross-module trait call, e.g. a prelude-written impl called from `user`). REQUIRED field, no `#[serde(default)]` (Principles 18/20). Landed inside the schema-19 window — no new `CACHE_SCHEMA_VERSION` bump.

### Monomorphised Definitions

```rust
/// A monomorphised function definition — a thin wrapper over a fully-annotated `Defn`.
#[derive(Debug, Clone)]
pub struct MonoDefn {
    pub defn: Defn,
}
```

**S81 W-G (FIXME 0033): side maps dropped.** `MonoDefn` previously carried
`resolutions: MethodResolutions` and `expr_types: HashMap<Span, Type>` — Span-keyed
side maps. After the Phase-1 AST-annotation migration these are redundant:
`monomorphise_call` (in `cranelisp-typecheck::traits`) annotates `defn` in place
(`annotate_defn_from_maps` + `apply_subst_to_defn`), so every typed expression carries
its `inferred_type` and every call site its `resolved_call` directly on the AST. No
consumer read the side maps for information not already on the annotated `defn`
(backend reads `mono.defn`; `register_mono_entry` reads `mono.defn`); the maps were
produced-but-never-read. Dropping them makes `MonoDefn` a single-field wrapper —
single source of truth (Principle 7): resolved-stage data lives on the AST.

---

## Call Graph — DELETED types; the live mechanism is `ModuleEntry::Def.callees`

The `CallEdge` / `CallInfo` / `CallGraph` cluster this section once specified
was **deleted at S119 (FIXME 0918)** — it was zero-consumer dead surface (the
S87 Finding-2 class): nothing in the workspace constructed or read it, and its
`sccs()` was a `todo!()` that never arrived. The **live** call-graph mechanism
is the one Decision 21 actually landed: the per-symbol
`callees: Vec<FQSymbol>` field on `ModuleEntry::Def`, populated by typecheck's
`finalize_check_result()`, persisted with the entry, and queryable via
`tc.symbol_table(module).get(name).callees()` — the same edges the S101
session-transaction reverse index and the ownership fixpoint walk. A future
rich-edge need (tail-position spans etc.) starts from the spec in git history,
not from a dormant type.

### `ParsedEntry` — the parse-time-only transient (Sprint 66, FIXME 0156)

**`ParsedEntry` is a transient boundary type, hosted in `cranelisp-types`,
that bridges `cranelisp-frontend::build_form` to
`cranelisp-typecheck::check_form`.** It carries only what the parser
knows; resolved-stage fields (type, scheme, callees, code, got_slot) are
populated by `check_form` downstream. **`ParsedEntry` NEVER lands in
`SymbolTable`** — its lifecycle is bounded by one orchestrator iteration:

```
parse → ParsedEntry → check_form → Vec<(Symbol, ModuleEntry)>
                                         → SymbolTable.insert (caller)
```

The SymbolTable invariant ("if it's in the table, it's checked") is
preserved because the orchestrator inserts only on `check_form`'s `Ok`
return.

`build_form` returns `Vec<ParsedEntry>` because some shapes yield more
than one entry per source form: a multi-clause `defmacro` yields one
`ParsedEntry::Macro` per clause (each clause typechecks independently);
a `deftype` yields the type entry plus per-constructor entries. The
caller drives `check_form` once per `ParsedEntry`. See
`crates/cranelisp-types/src/parsed.rs` rustdoc for the full enum shape,
`crates/cranelisp-frontend/src/lib.rs` //! preamble (post-S70 B3-C the
canonical home for the frontend public surface; `facades/frontend.md`
retired) + `crates/cranelisp-typecheck/src/lib.rs` rustdoc (post-S72 W5
the canonical home for the typecheck surface; `facades/typecheck.md`
retired) for the producer/consumer signatures.

`#[non_exhaustive]`. Derived: `Debug, Clone`. NOT
`Serialize/Deserialize` — never persisted.

**`DefmacroInfo` location move (FIXME 0156).** `DefmacroInfo` was
previously hosted in `cranelisp-frontend/src/defmacro.rs`. Per FIXME
0156 resolution it moves to `cranelisp-types` so that `int`'s
post-`build_form` consumption path can name the type uniformly.
`MacroClauseInfo` and `MacroParam` already live in `cranelisp-types`;
`DefmacroInfo` joins them. Frontend's `parse_defmacro` becomes
`pub(crate)` inside the `build_form` dispatcher; the public surface is
`build_form` returning `Vec<ParsedEntry>` carrying
`ParsedEntry::Macro { info: DefmacroInfo, .. }`.

### `check_forms` (Sprint 66; Decision 44 amended 2026-05-13 and 2026-09-03)

The 2026-09-03 macro-checkpoint amendment narrows “cluster” in this section to
the fully expanded **non-macro** HM entry set. A source-ordered `defmacro`
publishes its parent, clauses, and defining-module generated-realization rows
as a complete module-local checkpoint after the full expansion-time dependency
and generated-realization closure has typechecked and codegenerated
successfully. A later failure, including the §18 dependent cure, does not roll
it back.
Dependency modules publish independently. This does not split the non-macro
forward-reference scope and adds no typecheck or types facade item. A macro
replacement with fewer clauses supplies explicit absent-key `ChangeAbi`
decisions in that same publication. The existing decision means retirement of
the live prior ABI generation: a staged slotted replacement receives a fresh
slot, while a key wholly absent from staging removes the binding with no
replacement. Omission alone never deletes. The removed row returns its owner
and prior slot through the existing `PublicationRecord`, keeps the old GOT
pointer frozen behind an ABI-changing tombstone, and is excluded from the new
compiled-owner set. This is a semantic extension of the existing facade with
no new item, signature, re-export, baseline line or serialized shape.

The pre-S66 `check_form` mutated the symbol table in-place and was
merged via a typecheck-internal `merge_form_result()` helper. FIXME
0160 first purified it to a single-call pure function. Wave 3a
implementation surfaced a structural conflict with spec §5.13.1's
mandated two-pass typecheck (Pass 1 Registration; Pass 2 Checking) for
forward references / mutual recursion at top level — a single per-form
pure call cannot satisfy this because when checking `(defn f [] (g 1))`'s
body, `g`'s signature must already be in scope, but a per-form caller has
no opportunity to register `g`'s signature first. Decision 44 first split
the single call into two passes; the intermediate two-function shape
(`check_form_signatures` + `check_form_body`) exposed implementation
phasing across the facade and created a state-threading hole
(Pass-1-to-Pass-2 working state had no public home). The 2026-05-13
third amendment collapses the two-function split into a single
`check_forms` function that consumes the whole cluster and runs both
passes internally; Pass-1-to-Pass-2 working state lives inside the call
frame and never crosses the facade:

```rust
pub fn check_forms<C, L>(
    parsed: Vec<ParsedEntry>,             // whole cluster
    ctx: &mut SymbolTableAccess<'_, C, L>,    // staging-or-live access via accessor
    symbol_tables: &SymbolTables<C, L>,    // for cross-module reads
) -> Result<(), CheckError>;
```

`check_forms` is pure with respect to **live state** — it does not
mutate the live `SymbolTable` nor any state visible outside the cluster.
It MAY mutate the orchestrator-handed staging `SymbolTable` via
`ctx.current_symbol_table_mut()` — the same accessor API used in
committed-mode. Typecheck cannot distinguish staging from live because
the accessor abstracts the difference. The caller
(`int::process_cluster`) constructs `SymbolTableAccess::Cluster { modules,
staging: &mut empty_staging, current_module }` for the duration of one
cluster's processing, threads `&mut ctx` to one `check_forms` call,
and commits staging into the live `SymbolTable` atomically via
`int::insert_cluster` only on whole-cluster success. On `Err(Gap |
TypeError)`, no live mutation has occurred — the orchestrator either
drops the staging frame and retries the whole `check_forms` call
against a fresh staging frame (Gap) or drops staging on the floor when
the function frame returns (TypeError); the live table is
byte-identical to its pre-cluster state.

Per Decision 44 (amended FIXME 0167; third amendment 2026-05-13), cluster
atomicity is preserved because staging is orchestrator-local and is
committed (drained into live) only on whole-cluster `check_forms`
success. The transient-vs-durable distinction matters: the canonical
store has ONE durable write surface (live, committed via cluster atomic
drain); staging is a transient orchestrator-local frame, never published.
The Principle 7 objection "two write surfaces on the canonical store"
does not apply because
staging is not the canonical store — it is a per-cluster frame with the
same shape as the canonical store, used to absorb cross-pass write-side
intent before atomic commit. `ReplSnapshot` covers type-var-pool
rollback inside `CheckState` between calls.

**Cluster atomicity**. The orchestrator drives Pass 1 across every non-macro
`ParsedEntry` in a cluster, then Pass 2 across every `ParsedEntry` in
the cluster, then commits staging into live on success. A cluster is one
non-macro form (non-`begin` REPL input), the non-macro contents of
`(begin form₁ … formN)` (REPL explicit cluster), or a file's fully expanded
non-structural, non-macro forms (batch). Macro checkpoints encountered while
forming that set are outside its rollback domain. See
`bounded-contexts.md` §6 (int) + `design/int/s78-entry-module.md` +
`src/cluster.rs` rustdoc for the orchestrator side (the `facades/int.md`
facade retired S81 W-Retire → BC §6 + `design/int/` + source rustdoc),
`crates/cranelisp-types/src/view.rs` rustdoc for the read-surface newtype,
and `decisions/0044-*.md` for the rationale + rejected alternatives.

The pre-S66 `FormCheckResult` carrier and its `merge_form_result()`
helper are retired by this purification. Annotations onto AST nodes
(`Expr.inferred_type`, `Expr::Apply.resolved_call`) are now part of the
returned `ModuleEntry::Def.ast`; call-graph edges land in
`ModuleEntry::Def.callees` of the returned entries; mangled multi-sig
variants and mono specializations come back as additional entries in
the returned `Vec<(Symbol, ModuleEntry)>`. The orchestrator commits
the whole vector atomically on `Ok`.

### FormCheckResult (typecheck-internal — pre-S66 shape, retained for reference)

Per-form typecheck output produced internally by typecheck before
collation into the `Vec<(Symbol, ModuleEntry)>` returned by
`check_form`. **Not a boundary type** — typecheck-internal scratch
state. Pre-FIXME-0160, this was returned by `check_form` itself and
merged via a `merge_form_result()` helper that mutated the symbol
table in place. Post-FIXME-0160 (Sprint 66), the merge happens inside
`check_form` and the function returns a pure `Vec<(Symbol,
ModuleEntry)>` to the caller — the merge no longer crosses a crate
boundary. The struct shape below is preserved for reference; it is
purely an internal accumulator now.

```rust
/// Per-form typecheck result. Typecheck-internal.
#[derive(Debug)]
pub struct FormCheckResult {
    /// Method resolutions for this form's call sites (written onto
    /// `Expr::Apply.resolved_call` during merge).
    pub method_resolutions: MethodResolutions,
    /// Expression types for this form (written onto `Expr.inferred_type`
    /// during merge).
    pub expr_types: HashMap<Span, Type>,
    /// Constraints discovered for this form's symbols.
    pub constrained_fn_names: HashSet<Symbol>,
    /// Warnings produced during checking this form.
    pub warnings: Vec<Warning>,
    /// Call graph edges: (local caller, fully qualified callee).
    /// `finalize_check_result()` groups these by caller and writes
    /// `callees: Vec<FQSymbol>` to each caller's `ModuleEntry`.
    /// See Decision 21.
    pub call_graph_edges: Vec<(Symbol, FQSymbol)>,
}
```

---

## ADT Support Types

```rust
/// Information about a user-defined type. Symbol-table-stage structural
/// metadata only — `docstring` lives directly on `ModuleEntry::TypeDef`
/// (S72 Phase B; single source of truth, Principle 7), NOT here.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeDefInfo {
    pub name: FQTypeName,
    pub type_params: Vec<Symbol>,
    pub constructors: Vec<Symbol>,
}

/// Symbol-table-stage trait metadata — the slimmed payload of
/// `ModuleEntry::TraitDecl` (S72 Phase B). `docstring` + `visibility` live
/// directly on the entry, NOT here (single source of truth, Principle 7);
/// the entry no longer embeds the full frontend AST `TraitDecl`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitDeclInfo {
    pub name: TraitName,
    pub type_params: Vec<Symbol>,
    pub methods: Vec<TraitMethodSig>,
}

/// Information about a single data constructor.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstructorInfo {
    pub name: Symbol,
    pub tag: usize,
    pub fields: Vec<FieldInfo>,
    pub docstring: Option<String>,
    #[serde(default)]
    pub internal: bool,
}

/// Information about a constructor field.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FieldInfo {
    pub name: Symbol,
    pub ty: Type,
}
```

No changes from v1.

### ADT recipes — `AdtCtorSpec` + `build_adt_entries`

`build_adt_entries` is the ONE pure derivation shared by user `deftype`
registration and synthetic bootstrap seeds
(`crates/cranelisp-types/src/adt_build.rs`; Principle 24). It returns slotless
recipes: allocation and callable publication belong exclusively to the
`SymbolTable` settlement funnels defined by `symbol-table-lifecycle.md` §4.4.

```rust
#[non_exhaustive]
pub struct AdtCtorSpec {
    pub name: Symbol,
    pub fields: Vec<FieldInfo>,
    pub docstring: Option<String>,
    pub internal: bool,
}

#[non_exhaustive]
pub struct AdtCallableSpec {
    pub scheme: Scheme,
    pub param_names: Vec<Symbol>,
    pub docstring: Option<String>,
    pub origin: CallableOrigin,
    pub synth: SynthSpec,
    pub visibility: Visibility,
}

pub enum AdtEntrySpec<C: CodeStore = ()> {
    Callable(AdtCallableSpec),
    Binding(Binding<C>),
}

pub fn build_adt_entries<C: CodeStore>(
    fqtn: &FQTypeName,
    type_params: &[Symbol],
    type_var_ids: &[TypeId],
    adt_docstring: Option<&str>,
    ctors: &[AdtCtorSpec],
    visibility: Visibility,
) -> Vec<(Symbol, AdtEntrySpec<C>)>
```

The builder owns the product/sum split, constructor schemes, synthesised
`DefnVariant` bodies, positional tags, `CallableOrigin::Ctor`, canonical
`member_key(Type, Ctor)` keys, bare-name `NameCandidate` exposures, product
docstring fallback, and the single `TypeDefInfo` derivation. A product yields
one callable recipe whose origin carries the type facet; a sum yields each
canonical callable recipe followed by its bare alias and ends with its
`Decl::Type` binding.

Callers keep only stateful policy: resolve field types before building specs,
submit each `Callable` recipe to `install_template` or `install_concrete`, run
the §8.6.5 contest policy for bare aliases, and perform typecheck-only
recursive pre-seeding and product-accessor synthesis. No raw slot crosses this
boundary, and the builder never constructs a callable `Binding`. The generic
constructor control is
`adt_build/tests.rs::generic_constructor_recipe_has_no_slot_or_lifecycle_state`.
The result envelope is generic over the target table's `CodeStore`, so its
non-callable `Binding<C>` values install directly; consumers must not unwrap
and reconstruct bindings or depend on a types-private conversion. This is a
public-signature correction within C1's existing `cranelisp-types` baseline
regeneration, with no cache-schema or platform-ABI effect.

---

## Module System

> **S121 unified lifecycle boundary (architecture, candidate facade and A1 publication approved).**
> The user approved the `Binding -> Decl -> Callable -> Life` representation,
> table-owned enforcement of lifecycle/slot transitions, and module-atomic
> staged/live publication on 2026-09-02. The user also approved one symbol map
> whose per-spelling entry contains its canonical binding and visible candidate
> references; the parallel trait-method map is rejected. Integration chooses
> semantic commit policy; the table validates and applies all binding/slot moves
> together and returns displaced compiled-code owners. Packet B's exact
> per-spelling candidate carriers and resolution facade were approved on
> 2026-09-02. The same-day realization correction explicitly approved
> `all_name_candidates`, primitive installer ownership arguments, and
> `Life::Inline { mode_summary }`. Packet A1's exact publication methods and
> owner-conservation carriers were accepted and baselined on 2026-09-02.

### Symbol table and binding tree

```rust
pub struct SymbolTable<C: CodeStore = (), L: LinkerStore = ()> {
    pub path: ModuleFullPath,
    pub module_preamble: Option<String>,
    symbols: HashMap<Symbol, SymbolEntry<C>>, // private; writes use funnels
    retired_slots: Vec<RetiredSlot>,       // private persistent tombstones
    pub next_seq: u64,
    pub got: Arc<GotTable>,                // serde-skip runtime slab
    pub imports: Vec<ImportSpec>,
    pub exports: Vec<ExportSpec>,
    pub platforms: Vec<PlatformSpec>,
    pub submodules: Vec<ModDecl>,
    pub written_trait_impls: Vec<WrittenTraitImpl>,
    pub schema_version: u32,
    pub linker: Option<L>,                 // serde-skip
}

// Private implementation shape; approved 2026-09-02.
struct SymbolEntry<C = ()> {
    binding: Option<Binding<C>>,
    references: Vec<NameCandidate>,
}

#[non_exhaustive]
pub struct NameCandidate {
    pub source: FQSymbol,
    pub visibility: Visibility,
}

#[non_exhaustive]
pub struct Binding<C = ()> {
    pub visibility: Visibility,
    pub declaration: Decl<C>,
}

pub enum Decl<C = ()> {
    Callable(Callable<C>),
    TraitMethod(TraitMethodRecord),
    Group(Group),
    Type(TypeRecord),
    Trait(TraitRecord),
    ImplShell(ImplShell),
    SpecialForm(SpecialFormRecord),
}

pub struct Callable<C = ()> {
    pub scheme: Scheme,
    pub param_names: Vec<Symbol>,
    pub docstring: Option<String>,
    pub seq: u64,
    pub origin: CallableOrigin,
    pub life: Life<C>,
}
```

`SymbolTables<C, L>` remains
`DashMap<ModuleFullPath, SymbolTable<C, L>>`: the session collection uses
concurrent keyed access, while each shard value owns a private ordinary
`HashMap<Symbol, Binding<C>>` mutated under its `&mut SymbolTable` guard.
This distinction is load-bearing; there is no per-symbol `DashMap` and no
`Arc<SymbolTable>` wrapper.

Visibility is stored once on `Binding`. Declaration metadata lives on the
facet which owns it: executable callable metadata on `Callable`, unslotted
trait-method dispatch metadata on `TraitMethodRecord`, group metadata on
`Group`, type metadata on `TypeRecord`, trait metadata on `TraitRecord`, and
special-form metadata on `SpecialFormRecord`. A product constructor's
type facet remains `CallableOrigin::Ctor { type_def: Some(..) }`;
`Binding::type_def_info()` is the single read-through over that facet and
`Decl::Type(TypeRecord::Defined)`.

The readable surface is `get`, `public_symbols`, `all_symbols`,
`defined_symbols`, and the typed `Binding` projections. There is no public
raw-map iterator with write capability. `defined_symbols` is exactly the
`Life::Concrete { realization: Realization::Body { .. }, .. }` projection.
`Binding::is_callable_target` includes executable callable states and
`Decl::TraitMethod`; `callable_got_slot` remains executable-slot-only.

### Lifecycle authoring facade — proposal, exact API unapproved

The production-consumer census retains checked source settlement but finds no
cross-crate production consumer for the lower-level `settle_template` and
`settle_concrete`; that pair becomes types-private in the next API proposal.
Born-settled ordinary callables currently use
`install_template`, `install_concrete`, `install_extern`,
`install_inline`, `install_host_promised`, and `install_platform`.
`mark_broken` owns the concrete-to-broken transition and must return any
displaced compiled owner for integration retention. `install_binding`
accepts aliases, ambiguity sentinels, and non-callable declarations only.
All callable installation, slot mint/rebind, displacement, and retirement
stays inside `SymbolTable`; no public raw allocator or callable insertion
surface exists.

Live publication is a separate module-atomic capability. Integration supplies
the complete semantic decision set for an owned staging table; `SymbolTable`
validates the candidate, publishes every binding and slot move or none, records
retired slots, and returns displaced runtime-only `C` owners. Integration
retains those owners and consumes the publication report for redefinition
processing. The exact decision/report carriers and method signature remain at
the user public-API gate.

The executing C3 consumer adds no raw mutation escape. Pass 2 and finalize use
the controlling contract's narrow facade:

```rust
pub fn update_declared_scheme(
    &mut self, name: &Symbol, scheme: Scheme,
) -> Result<(), LifecycleError>
pub fn settle_checked_template(
    &mut self, name: &Symbol, scheme: Scheme, ast: DefnVariant,
    kind: TemplateKind, callees: Vec<FQSymbol>,
) -> Result<(), LifecycleError>
pub fn settle_checked_concrete(
    &mut self, name: &Symbol, scheme: Scheme, ast: DefnVariant,
    view: MonoDefnVariant, callees: Vec<FQSymbol>,
) -> Result<CallableSlot, LifecycleError>
pub fn replace_callees(
    &mut self, name: &Symbol, callees: Vec<FQSymbol>,
) -> Result<(), LifecycleError>
pub fn publish_body_ownership(
    &mut self, name: &Symbol, summary: ModeSummary, view: MonoDefnVariant,
) -> Result<(), LifecycleError>
pub fn set_value_use(
    &mut self, name: &Symbol, mark: bool,
) -> Result<(), LifecycleError>
pub fn remove_non_callable(
    &mut self, name: &Symbol,
) -> Result<Option<Binding<C>>, LifecycleError>
pub fn discard_declared(
    &mut self, name: &Symbol,
) -> Result<(), LifecycleError>
```

Checked settlement is atomic across final scheme, AST, view, callees and slot
transition; it accepts only checked AST-backed ordinary bodies. Callee
replacement canonicalizes its input. Ownership publication accepts an
annotated complete view and stamps its summary together with the lifecycle
summary; the one-sided public `set_mode_summary` is retired. Non-callable
removal and prior-free Declared discard are the only cleanup surfaces.
Multi-sig bodies stay local until their canonical key is known; no callable
rename/removal or caller-side provisional slot mint is published.

Trait-method declarations use a separate non-executable facet:

```rust
#[non_exhaustive]
pub struct TraitMethodRecord {
    pub scheme: Scheme,
    pub param_names: Vec<Symbol>,
    pub docstring: Option<String>,
    pub trait_name: FQTraitName,
}

TraitMethodRecord::new(scheme, param_names, docstring, trait_name)
    -> TraitMethodRecord
Binding::trait_method(&self) -> Option<&TraitMethodRecord>
SymbolTable::install_trait_method(method, record, visibility)
    -> Result<(), LifecycleError>
// General candidate projection/read operations remain at the API gate.
```

`install_trait_method` stores the record only at canonical
`member_key(Trait, method)` and adds a general candidate reference under the
bare spelling in the same `symbols` map. An accessor reference and method
reference can therefore coexist in one per-spelling entry without giving
either declaration two storage identities. The record remains a callable
resolution/type-inference terminal carrying canonical reverse trait identity;
it never enters `Life`, owns a slot/view, or appears in `defined_symbols`.

Candidate references are canonical-source deduplicated and deterministic for
diagnostics; same-source public visibility wins. `View` unions staging/live
entries using the same general carrier. Load validation direct-probes every
candidate's canonical terminal after dependencies are restored. There is no
trait-specific candidate DTO, read path, serialized map or cleanup API. The
Packet B removes `BindingBody`: import/re-export edges become terminal
`NameCandidate` exposures and ambiguity becomes a use-site
`ResolveError::Ambiguous` carrying the surviving canonical identities.
The approved read surface includes `all_name_candidates` for private+public
cache dependency discovery; `public_name_candidates` filters that iterator for
import/export exposure. Primitive birth funnels accept an optional declared
ownership summary immediately before visibility. Extern stores it in
`Life::Concrete`; inline stores it in `Life::Inline { mode_summary }`, and the
one `Binding::mode_summary` projection reads both.

The public declaration records remain `#[non_exhaustive]` and are authored
cross-crate only through the role-specific constructors:

```rust
Group::overload(scheme, param_names, docstring, seq, members) -> Group
Group::macro_group(scheme, param_names, docstring, seq,
                   clauses_meta, macro_sexp) -> Group
TraitRecord::new(info, docstring) -> TraitRecord
TraitMethodRecord::new(scheme, param_names, docstring, trait_name)
    -> TraitMethodRecord
SpecialFormRecord::new(scheme, param_names, docstring, description)
    -> SpecialFormRecord
SynthSpec::new(variant) -> SynthSpec
ConstrainedMeta::new(constraints) -> ConstrainedMeta
BrokenProvenance::new(broken_by, message) -> BrokenProvenance
```

Typecheck authors the lifecycle recipe/metadata families (`Group`,
`TraitRecord`, `TraitMethodRecord`, `SynthSpec`, `ConstrainedMeta`), primitives
authors `SpecialFormRecord`, and int authors `BrokenProvenance`. There is
no general `Group::new`, public `Callable` constructor, or public
`RetiredSlot` constructor. `ImplShell` is authored inside types by
`enrol_written_trait_impl`.

An external-consumer integration test in `cranelisp-types/tests/` must
exercise all eight construction paths above and the enclosing
`Decl`, `TemplateBody`, `TemplateKind`, and broken-state paths. This
compile-pass is required because an in-crate test cannot detect E0639 from a
missing constructor on a public `#[non_exhaustive]` record.

### Checked-registration transaction facade — proposal, exact API unapproved

```rust
#[must_use]
pub struct RetainedCallables<C: CodeStore = ()> { /* private */ }
SymbolTable::retain_callables(&self, names: &[Symbol])
    -> Result<RetainedCallables<C>, LifecycleError>
SymbolTable::rollback_callables(&mut self, retained: RetainedCallables<C>)
    -> Result<(), LifecycleError>
RetainedCallables::commit(self)

#[must_use]
pub struct StagedImplShell<C: CodeStore = ()> { /* private */ }
SymbolTable::stage_trait_impl_shell(&mut self, record: &WrittenTraitImpl)
    -> Result<StagedImplShell<C>, CranelispError>
SymbolTable::rollback_trait_impl_shell(&mut self, staged: StagedImplShell<C>)
    -> Result<(), CranelispError>
StagedImplShell::commit(self)

SymbolTable::upsert_written_trait_impl(&mut self, record: WrittenTraitImpl)
    -> Result<(), CranelispError>
```

Both tokens are opaque, non-`Clone` and non-serde. Callable rollback restores
or removes the named unpublished method entries and their prior claim/
tombstone state atomically; it refuses to reclaim a fresh non-null GOT row or
code-bearing body. Shell rollback verifies the staged occupant before
restoring/removing it. Fresh registration may stage a divergent same-key
re-impl; cache restore still uses `enrol_written_trait_impl`, whose divergent
case is a hard error.

C3 constructs one `WrittenTraitImpl`, retains method entries, stages the
trait-home shell, and checks methods. A failure rolls back methods then shell.
After all methods settle, the writer record is upserted as the final fallible
table act and the tokens commit. The previous writer record therefore remains
untouched until success; there is no record to remove on failure, while every
cluster commit still has exactly one matching record and shell per key.

### Instance identity funnel

`InstanceLink` and `MonoDemand` carry `template: CallableTarget` and
`type_args: Vec<ConcreteType>`. The target identifies the selected template binding or overload arm;
macro-clause demands are rejected. The vector records one concrete substitution per
generalized variable, including result-only variables, in first structural
occurrence order in the template scheme (parameters before result, repeated
variables once, higher-kinded heads before their arguments). This is neither
value-parameter order nor numeric inference-variable order. Derivation and
replay use the same authoritative scheme, including the exact checked-body
scheme while a cluster is unpublished.

The public constructors are `InstanceLink::from_type_args(template, type_args)`
and `MonoDemand::from_type_args(template, type_args, site)`. `site` is diagnostic;
`MonoDemand::instance_link()` projects it away. The approved S122
`instance_key(&Scheme) -> Result<Symbol, InstanceKeyError>` methods apply these
substitutions to the selected template scheme and delegate to the types-owned
`concrete_callable_key(&FQSymbol, &ConcreteType)` encoder. This encodes the
authored owner and complete concrete function signature, including result, with
no arm ordinal. Collection, deduplication, minting and installation preserve
that same link. The exact approved contract and source migration are in
[s122-overload-reorder-publication.md](s122-overload-reorder-publication.md). Typecheck derives it only after the full use type
settles, reconstructs the concrete signature from it and checks constraints.
Replay requires no expression map and checks vector length against the selected
scheme's generalized variables. The producer and replay contract lives in
[bounded-contexts.md](bounded-contexts.md) §2.

The ordinary `settle_concrete` and `install_concrete` surfaces do not take
`minted_from`; they always create non-instance concrete callables. A
concrete monomorphised instance uses the dedicated surface:

```rust
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
) -> Result<(Symbol, CallableSlot), LifecycleError>
```

The table derives the storage key from the actual settled instance scheme and
the authored owner in the link through `concrete_callable_key`, stores
`minted_from: Some(link)`, and returns the derived key and slot. A single
private validator compares every concrete binding's actual key with the
same settled-signature derivation; it runs before install mutation and from
`validate_lifecycle()` after clone/deserialisation. A mismatch is
`LifecycleError::InstanceKeyMismatch { symbol, expected }`, and cache load
maps it to cache-stale. Required evidence is: a positive instance-funnel pin;
an install-time mismatch plant proving no mutation; a tampered restored-key
plant; and an external-consumer compile-pass using `install_instance`.
S122 changes key meaning without changing carrier fields and requires the
coordinated backend semantic cache-version bump before integrated completion.
There is no ordinal/substitution-key compatibility
constructor or serde alias. Platform ABI and calling conventions are unchanged.

### Slot and cache authority

Slots occur only in `Life::Concrete`, `Life::Broken`,
`Life::Declared.prior`, and private `retired_slots`. Allocation derives
its unavailable set from live claims plus tombstones; `next_got_slot` is not
stored. The per-module `GotTable` remains the runtime pointer source of
truth and is reconstructed on restore. `validate_lifecycle()` checks slot
range/uniqueness, concrete schemes, legal origin/state and realization
pairings, and instance-key identity.

The `Binding`/`Decl`/`Callable`/`Life` serde reshape is cache schema
24→25: pre-25 sidecars are rejected and rebuilt. The constructor and instance
facade completion above changes APIs and validation but not the persisted
shape, so it does not take another schema bump. `CodeStore` and
`LinkerStore` remain `Clone + Send + Sync + 'static` boundary traits; the
backend-owned concrete code carrier and platform ABI are unchanged.

### Module aliases

`ModuleAliases = DashMap<ModuleFullPath, ModuleAliasEntry>` is a separate
session-level namespace. Keys are minted only by
`module_alias_key(owner, alias)`. `substitute_module_alias` performs the
referring-module-scoped segment walk: the leading segment may use the
referring module's private alias; later segments require public mounts.
Every step is a keyed probe, never a global scan or longest-prefix iteration.
See `module-alias-scoped-lookup.md` for conflict and visibility rules.

### Macro Support Types

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MacroClauseInfo {
    pub params: Vec<MacroParam>,
    pub source: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MacroParam {
    Name(Symbol),
    Bracket {
        fixed: Vec<Symbol>,
        rest: Option<Symbol>,
    },
}
```

No changes from v1.

---

## REPL Snapshot

`ReplSnapshot` was deleted as dead code in S73 (purge Wave 3) — superseded by the cluster-atomic staging-drop rollback mechanism (BC §2 invariant 7). The v1 sketch that lived here is retired; there is no `ReplSnapshot` type.

## Resolution primitive — `ResolutionScope`

`ResolutionScope` is the landed public query boundary: one lookup with the
prelude decision fixed at scope construction and no public fallback-less
free function. It owns the referring-module context required by the scoped
module-alias walk. See `design/arch/prelude-import-convergence.md` and
`design/arch/module-alias-scoped-lookup.md`.

```rust
// crates/cranelisp-types/src/resolve.rs
#[non_exhaustive]
pub struct Resolved<C: CodeStore = ()> {
    pub entry: Binding<C>,
    pub home: ModuleFullPath,
    pub fq: FQSymbol,          // reference identity: home + canonical WRITTEN spelling
    pub storage_key: Symbol,   // storage identity: the terminal table key (S110 W1.1, FIXME 0620)
}
impl<C: CodeStore> Resolved<C> {
    pub fn storage_fq(&self) -> FQSymbol;   // { home, storage_key } — the keyed-consumer carrier value
}

pub struct ResolutionScope<'a, C: CodeStore = (), L: LinkerStore = ()> { /* private */ }

impl<'a, C: CodeStore, L: LinkerStore> ResolutionScope<'a, C, L> {
    pub fn new(
        symbol_tables: &'a SymbolTables<C, L>,
        module_aliases: &'a ModuleAliases,
        first_hop: &'a View<'a, C, L>,
        current_module: &'a ModuleFullPath,
        prelude: Option<&'a ModuleFullPath>,
    ) -> Self;
    pub fn resolve(&self, name: &str, span: Span)
        -> Result<Resolved<C>, ResolveError>;
    pub fn resolve_macro_head(&self, name: &str, span: Span)
        -> Result<Option<FQSymbol>, ResolveError>;
}

#[non_exhaustive]
pub enum ResolveError {
    TraitNotFound { name, from_module, span },
    TypeNotFound { name, from_module, span },
    ConstructorNotFound { name, from_module, span },
    QualifiedModuleUnknown { module, name, span },
    PrivateInaccessible { name, defining_module, from_module, visibility_found, span },
}
```

**The two identities on `Resolved` (S110 W1.1, FIXME 0620).** `fq` is the *reference* identity — `home` + the canonical **written** spelling — consumed by display, error attribution, macro-head dispatch, §8.6.4 remedies, and `callees`. It does NOT in general address the entry: across a member alias (`v` → `Box.v`, `Pure` → `IO.Pure`), a renamed import/export (`[(foo bar)]`), or a renaming re-export, the written spelling is an `Alias`-edge name, not the table key. `storage_key` / `storage_fq()` is the *storage* identity — the exact key the chain-follow terminated at, captured by the walk itself (the only actor that knows it; a `Binding` does not carry its own key). Keyed consumers — the `var_refs`/`apply_refs` carrier (`VarRef::Global` / `ApplyRef::Dispatch` values) feeding the backend's `entry_at` direct read (`design/arch/backend-keyed-consumer.md` §1.1) — record `storage_fq()`, never `fq`. Composing a storage identity from a written spelling is the 0620 defect class.

The single types-owned query that turns a name into a resolved symbol-table entry — following imports/reexports, §8.6.6 module-path aliases, visibility, and Principle-17 chain-following. **Resolving a name is a query over the symbol-table data structure** (no inference, no unification, no substitution), so by Principle 15 (behaviour lives with the type) and Principle 7 (single source) it belongs in `cranelisp-types`, extending the `ensure_module_exists` + `got_data_symbol_name` + chain-follow precedent. It is pure over `symbol_tables` + `module_aliases` (both types-owned), generic over `<C, L>`, and carries **no `CheckState`** — which is what keeps it in the data-only crate.

**The primitive-vs-view line.** The *search primitive* is types-owned: "in this table set, resolve `name` from `current_module` following imports/aliases/visibility/chain." The *choice of which view to search stays with the caller*, supplied as the first-hop `View` over the current module:

- **int's Pass-1 macro recognition** searches the **committed** tables — `View::single(live)` over the live current module. No staging exists during Pass 1 (the expand phase precedes `check_forms`).
- **typecheck's Pass-2/3 body resolution** searches the **staging ∪ live union** — its `SymbolTableAccess` hands a `View::union(staging, live)`.

Same primitive, different first-hop view. Cross-module hops (chain-following an `Import` edge, or the alias-resolved FQ target) always land in *other, already-committed* modules — staging only ever holds the *current* cluster's module (Principle 17 + Decision 44) — so the view parameterises only the entry point, not the whole walk.

**Consolidation (retires two scattered copies).** `resolve_macro_head` replaces int's `SymbolTableMacroResolver::resolve_macro` chain-walk (`src/worker.rs`) — recognition is now a `cranelisp-types` query with **zero int→typecheck dependency**. typecheck's `resolve_trait` / `resolve_type` / `resolve_constructor` / `resolve_qualified` family (`crates/cranelisp-typecheck/src/checker.rs`, S72) becomes a set of thin callers of `resolve`, each projecting the generic `Resolved` / `ResolveError` to its kind-specific success/error. `ResolveError` moved here with the primitive (it was typecheck-local only because the resolver was); its `From<ResolveError> for CheckError` projection stays in `cranelisp-typecheck` because `CheckError` is typecheck-owned (the types-side projection target is the neutral `CranelispError`). **No DAG impact** — `cranelisp-types` has no dependencies; the primitive adds none.

Per Principle 6 (minimum surface), `ResolutionScope::resolve` is the one
general public query and `ResolutionScope::resolve_macro_head` is its typed
macro projection; typecheck's kind-specific resolvers remain crate-side
projections. See `bounded-contexts.md` §§2, 6, and 7.
**`substitute_module_alias` is public (FIXME 0798 ruling; canonical:
`design/arch/module-alias-scoped-lookup.md`).** Its landed signature is
`substitute_module_alias(module_aliases, referring_module, module_path)`.
It walks dot segments with keyed `module_alias_key(owner, alias)` probes: the
leading segment uses the referring module's namespace at either visibility;
later segments traverse Public mounts only; the shared chain-depth cap bounds
the walk. The int FQ-autoload boundary and qualified resolution call this one
primitive. No caller scans the alias map or performs longest-prefix matching.
`ModuleAliases` is session-live and unserialized, so the signature change has
no cache-schema effect.

**Qualified-split guard — a bare `/` operator is not a qualified name (S81 / FIXME 0331, ratified).** The two private split helpers inside `resolve.rs` — `split_qualified(name)` (resolve.rs:493, the `module/symbol` splitter) and `canonical_symbol(name)` (resolve.rs:591, the post-last-`/` local-symbol extractor) — both require a **non-empty remainder** before splitting on `/`. `split_qualified` filters `split_once('/')` on `!m.is_empty() && !s.is_empty()`; `canonical_symbol` filters `rsplit_once('/')` on a non-empty symbol part. A name whose split would yield an empty part — a bare punctuation operator (`/`, `//`) or a leading/trailing `foo/` / `/bar` — is treated as a literal bare name routed to the unqualified short-name path, never to `resolve_qualified` against an empty root module. This is the structural realization of **Principle 16** (a bare punctuation operator is not special) at the resolution layer: `/` resolves identically to `+` or any other operator. The guard fixes the FIXME-0328 regression (the `resolve_with_fallback` migration made bare `/` resolve as "undefined variable: /") and matches pre-S81-migration literal-lookup behaviour; both helpers are PRIVATE (`fn`, not `pub`) so the fix carries **zero `public-api.txt` delta** (verified — not present in the baseline; `public_api_relocations` passes unchanged).

### `ResolutionScope` — the one lookup, prelude fallback intrinsic (S108 Wave G; supersedes the S81 `resolve_with_fallback` shape)

> **Ruling home: `design/arch/prelude-import-convergence.md`.** This section is
> the facade-side record of the approved `cranelisp-types` surface (the crate
> has no `facades/{crate}.md`). The S81 free-fn `resolve_with_fallback` shape
> that previously occupied this section (landed FIXME 0316c) is superseded:
> per-call opt-in fallback (`fallback_on: bool` threaded at every site) proved
> forgettable — the [S108 matrix in Git](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/tests/plan/PLAN.md)
> found six `_or_prelude` variants and four RED silent-accept/skip
> sites, each a per-site re-decision of the fallback question. Git history
> preserves the S81 section text. **LANDED S108 Inc3** (baseline
> regenerated; `/review` structural grep CLEAR).

The prelude is `(import [prelude [*]])` (spec §8.8.1); "outer scope" is a
resolution *mechanism*, not a language concept. The fallback therefore becomes
**intrinsic to a resolution scope constructed once per module context** —
never decided at a call site, and with **no public fallback-less resolution
entry point** (Principles 18/20 — the forgettable decision is unrepresentable):

```rust
// crates/cranelisp-types/src/resolve.rs  (approved S108 target)

pub struct ResolutionScope<'a, C: CodeStore, L: LinkerStore> { /* private */ }

impl<'a, C: CodeStore, L: LinkerStore> ResolutionScope<'a, C, L> {
    /// `prelude`: `Some(path)` iff the module's `prelude_fallback` bit is ON
    /// and `current_module != prelude` — the caller-side role datum
    /// (Principle 19), resolved ONCE at construction. `None` ⇒ this scope
    /// never falls back (suppressed-prelude module; the prelude itself;
    /// platform sig checks).
    pub fn new(
        symbol_tables: &'a SymbolTables<C, L>,
        module_aliases: &'a ModuleAliases,
        first_hop: &'a View<'a, C, L>,     // caller-chosen view (staging∪live or single)
        current_module: &'a ModuleFullPath,
        prelude: Option<&'a ModuleFullPath>,
    ) -> Self;

    /// THE reference lookup: inner walk; on a not-found-class miss of an
    /// UNQUALIFIED name, prelude retry gated by the I-1 public filter on the
    /// prelude HEAD binding (§8.8.1 provides the prelude's public *names*;
    /// terminal-side public check kept as defence in depth — FIXME 0567);
    /// chain-follow; §8.7.3 visibility; §8.6.6 aliases. Qualified `mod/sym`
    /// never retries (it names its module).
    pub fn resolve(&self, name: &str, span: Span) -> Result<Resolved<C>, ResolveError>;

    /// Macro-head projection (int Pass-1 recognition) — same walk, kind filter.
    pub fn resolve_macro_head(&self, name: &str, span: Span)
        -> Result<Option<FQSymbol>, ResolveError>;
}

/// The ONE §8.6.4 definition seam (multi-consumer: typecheck Pass-1 register
/// + int defmacro registration). Resolves `name` in the scope; home ==
/// current ⇒ own redefinition, allowed; otherwise classifies provenance
/// (inner Import/Export head, else Prelude) and delegates to
/// `check_binding_addition`. Synthetic names (`$`, `__`) skip.
pub fn reject_def_over_binding<C: CodeStore, L: LinkerStore>(
    scope: &ResolutionScope<'_, C, L>,
    name: &Symbol,
    span: Span,
) -> Result<(), CranelispError>;
```

- The former free `pub fn resolve` and `pub fn resolve_with_fallback` become
  private internals of `ResolutionScope::resolve` (I-1 public-only prelude
  filter, miss-class-only retry, never-self-fallback, prelude-absent ⇒ miss
  stands, and the Principle-16 `split_qualified`/`canonical_symbol` guards
  all move inside unchanged). `resolve_macro_head` moves onto the scope.
- **Staging-view selection stays caller-side** (the `first_hop` argument);
  the primitive still does not know about staging. The `prelude_fallback`
  bit stays typecheck/int-side (data-only crate — the scope receives the
  already-resolved `Option<&ModuleFullPath>`, never the companion map).
- Scope constructors are the ONLY places the bit is consulted for
  resolution: typecheck's construct-and-resolve seams (landed as
  `TypeCheckEnv::scope_resolve` / `scope_resolve_in`, checker.rs — one bit
  consult + view selection, subsuming `prelude_fallback_target` as their
  private helper) and int's committed-view seams (macro recognition, the
  defmacro definition gate). The int DISPLAY gate
  (`repl.rs::lookup_with_prelude_fallback{,_opt}`) is deliberately NOT a
  scope consumer — a raw-head + resolving-module display operation with a
  root special-form tier; settled deviation + the I-1 display-divergence
  ruling: `prelude-import-convergence.md` §3.5.
- The typecheck `_or_prelude` variant family and the fallback-less
  `lookup_{trait_decl,type_def}_with_state` lookalikes delete per the
  collapse map in `prelude-import-convergence.md` §3.3; the only surviving
  fallback-less probe is the same-module idempotent re-registration check
  (a raw table probe — a different question from name-freedom).

**Net `cranelisp-types/public-api.txt` baseline delta (S108 Wave G,
`/arch`-pre-approved; LANDED with the typecheck consumer collapse in one
change-set, baseline regenerated):** + `ResolutionScope` (+3
methods) + `pub fn reject_def_over_binding`; − `pub fn resolve`,
− `pub fn resolve_with_fallback`, − free `pub fn resolve_macro_head`
(reshaped onto the scope). `Resolved` / `ResolveError` / `BindingProvenance`
/ `check_binding_addition` / `substitute_module_alias` unchanged.
`resolve_terminal_entry_and_home` stays `pub` (module.rs; consumed by
`resolve.rs` internals and int's §8.6.5 install-time comparator). No serde
shape change ⇒ no `CACHE_SCHEMA_VERSION` bump.
**S109 Phase-3 amendments (landed, one `/arch` change-set).**

- **I-1 filter corrected to the prelude HEAD (FIXME 0567, closed).** The
  prelude-retry filter inside `ResolutionScope::resolve` gated on the
  chain-followed TERMINAL's visibility; spec §8.8.1 provides the prelude's
  **public names**, i.e. the binding in the prelude's own table. A private
  `(import …)` edge inside the prelude chaining to a public `Def` elsewhere
  leaked as a bare name in every fallback-ON module (latent — the stock
  prelude is a pure public re-export shell). The retry now requires the
  prelude head entry `is_public()` (the terminal check stays as defence in
  depth), aligning resolution with the head-side precedents
  (`find_trait_method_decl`, `prelude_implicit_names`, the §3.5.2 display
  gate). The current direct types control
  `resolve/tests.rs::prelude_fallback_remains_public_head_only` is the public
  leg; consumer tests cover private terminal bindings and public re-exports,
  but no C1 types test preserves the discriminating private-head →
  public-terminal chain. Internal walk body only — **zero `public-api.txt`
  delta, no cache impact**.
- **`pub fn member_key(&TypeName, &str) -> Symbol` (+1 baseline line,
  additive).** The ONE mint point for the canonical `Type.member`
  symbol-table key of the §8.5.2 inverted member model — `Box.v` field
  accessors today; `Maybe.Some` constructor keys when the S109 dotted-ctor
  registration lands. Kills the hand-rolled `format!("{}.{}", …)` copies
  (typecheck `adt.rs` accessor registration, `checker.rs` canonical-key
  probe; the ctor registration is the third site) so the key grammar cannot
  drift per site (Principle 7). Lives beside the resolution primitives
  because the dotted member key is the local-key half of the reference
  grammar the resolver splits (`/` = module separator, `.` = member
  separator).
- **`pub fn bare_member_name(&str) -> &str` (+1 baseline line, additive; S109
  W1 review follow-up).** The projection INVERSE of `member_key` — the ONE
  terminal-segment grammar (`Maybe.Some`→`Some`, `macros/SCons`→`SCons`,
  `m/Type.Ctor`→`Ctor`; Principle-16 non-empty guards keep punctuation
  operators and empty-part shapes literal) for every site that compares a
  written form or storage key against a bare display name: typecheck's
  exhaustiveness covered-set normaliser (the S109 BR-1 `.`-strip) and backend
  sparkability's ctor-exclusion comparison (the S109 I-1 finding — the two
  sides of that comparison each hand-rolled half the grammar and drifted:
  `collect_module_constructors` yields storage keys, `is_worth_sparking`
  compares source-written callee names). Pins: `resolve/tests.rs::
  bare_member_name_*`.
- **Same-module alias-chain depth cap (S109 W1 review MINOR, zero API
  delta).** `chain_follow_committed`'s same-module VIEW hop (the S109
  staging-aware arm) now bottoms out at `CHAIN_FOLLOW_DEPTH_LIMIT`, mirroring
  `resolve_terminal_entry_and_home`'s cap — a degenerate same-module alias
  cycle reads as a not-found miss, never a stack overflow. The scoped
  module-alias walker shares the cap and is pinned by
  `resolve/tests.rs::alias_walk_refuses_more_than_the_shared_depth_limit`; the
  same-module chain-follow arm has no dedicated C1 unit pin.

---

## Macro execution callback — `MacroExpander` (S76 W-Macro, FIXME 0175 resolution)

```rust
// crates/cranelisp-types/src/macro_expander.rs
pub trait MacroExpander: Send + Sync {
    fn invoke(
        &self,
        fq: &FQSymbol,
        args: &[Sexp],
        call_span: Span,
    ) -> Result<Sexp, MacroInvokeError>;
}

#[non_exhaustive]
pub enum MacroInvokeError {
    Aborted   { fq: FQSymbol, message: String, span: Span },
    Malformed { fq: FQSymbol, message: String, span: Span },
}
```

The injected capability by which `cranelisp-typecheck` executes one JIT-compiled macro invocation without depending on the integration layer. Macro **recognition** is typecheck's (it already resolves every head against the symbol-table view); macro **execution** (marshal `Sexp`↔heap, the signal-protected `extern "C" fn(i64) -> i64` call) is int's, behind this trait — int implements it over `src/expander.rs`'s invocation core + `src/marshal.rs`. typecheck holds `&dyn MacroExpander` for the duration of a `check_forms` call; the result is a raw `Sexp` that typecheck re-classifies (nested-macro fixpoint + structural-form re-entry). The trait lives in `cranelisp-types` because it crosses the typecheck ↔ int boundary, and adds **no** dependency edge (typecheck stays `cranelisp-types`-only; the int→typecheck call edge already exists and now carries the `&dyn MacroExpander` argument). `Send + Sync` because concurrent typecheck workers may invoke macros in parallel (Decision 38). Replaces the REJECTED `cranelisp-marshal` bridge crate (FIXME 0175). The stale v1 `MacroExpander` sketch (frontend-side, `&mut self` + `is_macro`) is retired by this — there is no frontend macro trait. See `design/arch/macro-expansion-ownership.md`.

---

## Backend Types (in `cranelisp-backend`)

These types live in `cranelisp-backend`, not in `cranelisp-types`, because they contain runtime state.

```rust
/// Per-module codegen state. Owns GOT and code artifacts.
pub struct ModuleCodegenState {
    pub got_table: Option<Box<[*const u8; GOT_TABLE_SIZE]>>,
    pub next_got_slot: usize,
    pub def_codegen: HashMap<Symbol, DefCodegen>,
}

/// Codegen artifacts for a single definition.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct DefCodegen {
    pub got_slot: Option<usize>,
    #[serde(skip)]
    pub code_ptr: Option<*const u8>,
    pub source: Option<String>,
    pub sexp: Option<Sexp>,
    pub defn: Option<Defn>,
    pub clif_ir: Option<String>,
    pub disasm: Option<String>,
    pub code_size: Option<usize>,
    #[serde(skip)]
    pub compile_duration: Option<std::time::Duration>,
    pub param_count: Option<usize>,
}

/// Cache metadata for a compiled module.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CacheMetadata {
    pub content_hash: Option<String>,
    #[serde(skip)]
    pub cache_method_resolutions: MethodResolutions,
    #[serde(skip)]
    pub cache_expr_types: HashMap<Span, Type>,
}

pub const GOT_TABLE_SIZE: usize = 1024;
pub const NULLARY_TAG_THRESHOLD: usize = 1024;
```

No changes from v1.

### Per-Module GOT Registry (new — see `design/backend/per-module-got.md`)

```rust
/// Identifies a function's GOT location: which module's GOT and which slot.
///
/// Used in CodegenItem/CodegenPacket and cache metadata to communicate
/// GOT assignments from the integration layer to codegen workers.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FnSlotEntry {
    /// The module that owns the GOT containing this function's slot.
    pub module: ModuleFullPath,
    /// Slot index within that module's GOT.
    pub slot_index: usize,
}

/// Registry of per-module GOT tables for the JIT path.
///
/// Each module gets its own `ModuleCodegenState` with its own `GotTable`.
/// Slot indices are local to each module — slot 0 in module A is
/// independent of slot 0 in module B.
///
/// Lives on `InMemWorkerState` (replaces the flat `got_state` field).
pub struct ModuleGotRegistry {
    module_gots: HashMap<ModuleFullPath, ModuleCodegenState>,
}
```

`InMemWorkerState.got_state: ModuleCodegenState` becomes `InMemWorkerState.got_registry: ModuleGotRegistry`.

### GOT as persistent session state

Each `ModuleCodegenState` is persistent session state for one module. GOT slot assignments live in `def_codegen: HashMap<Symbol, DefCodegen>` and are assigned when functions are first registered. Slot indices are **local to the module** — slot 0 in module A and slot 0 in module B are in different `GotTable` allocations.

The `ensure_slot_for(name)` method reuses existing slots and allocates new ones at the end. Slots never move. This stability invariant enables both parallel codegen (each module's GOT is independent, no contention) and incremental recompilation (recompiled function gets the same slot, new code pointer written in, all GOT-indirect callers see it automatically).

### Cross-module GOT references

When compiling module B that imports function `f` from module A, the compiler needs `(got_base_ptr_of_A, slot_index_of_f_in_A)`. This is provided via `CrossModuleGot`:

```rust
/// Cross-module GOT mapping: (defining_module, function_name) -> (got_base_ptr, slot_index).
pub type CrossModuleGot = HashMap<(ModuleFullPath, Symbol), (i64, usize)>;
```

This type already exists in `compiler/mod.rs` and is already handled by `CompileContext.cross_module_got` and `resolve_got_entry()` in `apply.rs`. The per-module GOT change populates it (currently always `None`).

### `CodegenPacket` GOT fields (updated)

```rust
pub struct CodegenPacket {
    // ... other fields unchanged ...

    /// GOT slot map for this module's own functions.
    /// Maps function name -> slot index within this module's GOT.
    pub local_got_slots: HashMap<Symbol, usize>,

    /// GOT base pointer for this module's own GOT table.
    pub local_got_base: i64,

    /// Cross-module GOT for imported functions.
    pub cross_module_got: CrossModuleGot,

    /// Shared GOT table for THIS MODULE's atomic code pointer writes.
    pub shared_got: Option<Arc<GotTable>>,

    // REMOVED: got_slot_map: HashMap<Symbol, usize>  (was flat across all modules)
}
```

**Thread safety for parallel codegen:** Each codegen worker receives its module's `Arc<GotTable>` and writes code pointers atomically to its own module's slots. No contention between workers compiling different modules. The `DashMap<ModuleFullPath, SymbolTable>` passed into `compile_to_module` is read-only from the worker's perspective during a compile, and `SymbolTable` / `ModuleEntry` / `Defn` / `Expr` are `Send + Sync`. Each worker creates its own `Jit` instance. See `design/backend/per-module-got.md` for full design.

---

## Module Graph (in binary crate)

```rust
/// Information about a discovered module before compilation.
pub struct ModuleInfo {
    pub id: ModuleFullPath,
    pub file_path: PathBuf,
    pub source: String,
    pub sexps: Vec<Sexp>,
    pub child_mod_names: Vec<(ModuleName, Span)>,
    pub dependencies: Vec<ModuleFullPath>,
    pub imports: Vec<ImportSpec>,
    pub exports: Vec<ExportSpec>,
    pub platforms: Vec<(String, Option<String>, Span)>,
    pub is_lib: bool,
}

/// The complete module dependency graph with compilation order.
pub struct ModuleGraph {
    pub modules: HashMap<ModuleFullPath, ModuleInfo>,
    pub compile_order: Vec<ModuleFullPath>,
}
```

No changes from v1.

---

## Heap Classification

```rust
/// Whether a type requires heap allocation at runtime.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HeapCategory {
    NeverHeap,
    AlwaysHeap,
    Mixed,
}

impl HeapCategory {
    pub fn classify(ty: &Type) -> HeapCategory { ... }
}
```

No changes from v1.

---

## Heap Object Layouts

### HeapHeader (in `cranelisp-types`)

```rust
/// Universal header for all heap-allocated values.
#[repr(C)]
pub struct HeapHeader {
    pub alloc_size: i64,
    pub rc: i64,
}

impl HeapHeader {
    pub const SIZE: usize = 16;
    pub const ALLOC_SIZE_OFFSET: i32 = 0;
    pub const RC_OFFSET: i32 = 8;
}
```

### R5 value-representation flattening

The types-owned layout predicate is shared by typecheck's Copy/uniqueness
classification and backend's value lowering. A disagreement could bit-copy a
heap pointer without retaining it, so neither consumer derives eligibility
independently. Exact signatures and lookup obligations live in
[`heap.rs` rustdoc](../../crates/cranelisp-types/src/heap.rs).

- `Some(ValueLayout)` identifies a scalar or a single-constructor ADT with
  exactly one transitively value-eligible field, within `VALUE_LAYOUT_MAX_WORDS`.
  Multiple constructors, heap collections and fields whose stored types are
  not concrete are ineligible. This walk performs no generic substitution;
  `ctor_field_types_at` is the distinct substituting projection.
- `value_layout` adapts published tables to `value_layout_with_lookup`. The
  latter accepts exact keyed owned-binding lookup; the caller supplies a coherent
  declaration view and releases guards before returning each binding. The walk
  releases metadata before recursion and retains no callback or binding.
- Typecheck supplies its staging-first lookup to both classifiers. A present
  staged binding wins even when ineligible; only an absent key falls through.
  Backend uses the same algorithm with its codegen tables.
- The shared constructor projection preserves canonical member-key preference
  and the product-type facet. Cycles return no value layout.

The staging-aware input changed declaration access, not layout rules, calling
conventions or persisted field meanings. Approval and measured delivery history
remain in the closed S121 record and Git.

### Resource scheduling — the `ctx` vtable handle model (ABI v9, S97, supersedes FIXME 0482)

**Scheduling state never rides on a value** (`platform-interface.md` §6.8.0b;
`effect-concurrency.md` §4.1.1 — superseding the descriptor cut, which proposed a
value-header `ResourceDesc` slot and was retired at the Wave-2 DLL-mint blocker). There
is **no resource-descriptor heap-header slot, no `ResourceDesc` type, no resource-handle
layout marking, no `PollFn.desc_out`**. A resource handle (`web/Connection`) is an ordinary
ADT carrying the platform's own `r`/`fd` in a genuine field. It is **tramp-opaque, not
user-opaque**: the trampoline never introspects it (only the platform reads `r` back out),
but the **user program may read its fields by ordinary destructuring** — it is their
connection's genuine data, not a sealed value (`(match c [(Connection fd) fd])` typechecks
and yields the real fd; there is no "no user destructuring path" mechanism). All runtime
scheduling flows through a trampoline-owned **`ctx` vtable** (the generalized `HostCtx`) the
platform's poll-fns call — none of it on the value.

The v9 ABI surface is two additions — no value-side types:

```rust
// cranelisp-types — the new compile-time fact + acquire result.
//
/// Per-EFFECT static leaf role — a manifest compile-time fact (grounds inference E2,
/// documents the leaf). The trampoline does NOT branch on it at runtime. `#[repr(u8)]`,
/// governed by cranelisp_platform::ABI_VERSION.
#[repr(u8)]
pub enum ResourceRole { None = 0, Produce = 1, Consume = 2, Retire = 3 }

/// C-ABI result of a token-permit acquisition. `#[repr(i32)]`.
#[repr(i32)]
pub enum Acquire { Acquired = 0, Parked = 1 }

// `ConcurrencyDescriptor` gains `role: ResourceRole` (consuming one byte of its
// `_reserved: [u8; 3]` tail — existing field offsets + size unchanged).
// `PollFn` is UNCHANGED: poll(state, *HostCtx, *Waker) -> Poll  (no desc_out).
```

```rust
// cranelisp-platform — HostCtx (the `ctx` vtable) gains the token-permit half.
#[repr(C)]
pub struct HostCtx {
    pub register_readable: unsafe extern "C" fn(host: *const c_void, fd: i32, waker: *const Waker),
    pub register_writable: unsafe extern "C" fn(host: *const c_void, fd: i32, waker: *const Waker),
    pub register_timer:    unsafe extern "C" fn(host: *const c_void, deadline_nanos: u64, waker: *const Waker),
    // NEW v9 — token-permit pool ops the platform poll-fn calls:
    pub acquire: unsafe extern "C" fn(host: *const c_void, token: u64, capacity: u32, waker: *const Waker) -> Acquire,
    pub retire:  unsafe extern "C" fn(host: *const c_void, token: u64),
    pub host: *const c_void,
    // NO `release` — release is trampoline-owned (on Ready/cancel).
}
```

The poll-fn calls `acquire`/`register_*`/`retire` through the `*HostCtx` it already
receives; the host releases permits automatically on the effect's `Ready` or cancel (keyed
by effect identity). `acquire` takes the **waker** so a `Parked` return can enqueue the
strand for re-poll, and is idempotent per in-flight effect. These land in the v9 cutover
change-set (atomic `ABI_VERSION` 8 → 9; `cranelisp-types` + `cranelisp-platform`
`public-api.txt` regen) — a **simpler** bump than the descriptor cut. Canonical:
`platform-interface.md` §6.8.0b.

### HeapString (in `cranelisp-intrinsics`)

```rust
#[repr(C)]
pub struct HeapString {
    pub header: HeapHeader,
    pub len: i64,
}

impl HeapString {
    pub const LEN_OFFSET: i32 = 16;
    pub const DATA_OFFSET: i32 = 24;
}
```

### HeapAdt (in `cranelisp-backend`)

```rust
#[repr(C)]
pub struct HeapAdt {
    pub header: HeapHeader,
    pub tag: i64,
}

impl HeapAdt {
    pub const TAG_OFFSET: i32 = 16;
    pub const FIELDS_START: usize = 24;
    pub const fn field_offset(i: usize) -> i32 { ... }
}
```

### HeapClosure (in `cranelisp-backend`)

```rust
#[repr(C)]
pub struct HeapClosure {
    pub header: HeapHeader,
    pub code_ptr: i64,
    pub drop_glue_ptr: i64,
}

impl HeapClosure {
    pub const CODE_PTR_OFFSET: i32 = 16;
    pub const DROP_GLUE_PTR_OFFSET: i32 = 24;
    pub const CAPTURES_START: usize = 32;
    pub const fn capture_offset(i: usize) -> i32 { ... }
}
```

### HeapVec (in `cranelisp-backend`)

```rust
#[repr(C)]
pub struct HeapVec {
    pub header: HeapHeader,
    pub len: i64,
    pub capacity: i64,
    pub data_ptr: i64,
}

impl HeapVec {
    pub const LEN_OFFSET: i32 = 16;
    pub const CAPACITY_OFFSET: i32 = 24;
    pub const DATA_PTR_OFFSET: i32 = 32;
}
```

No changes from v1 for any heap layouts.

---

## IO Tag Constants (in `cranelisp-platform`)

```rust
pub const IO_TAG_PURE: i64 = 0;
pub const IO_TAG_EFFECT: i64 = 1;
pub const IO_TAG_BIND: i64 = 2;
pub const IO_TAG_PAR: i64 = 3;
// + IO_TAG_EFFECT_POLL = 4, IO_TAG_LAUNCH = 5, IO_TAG_SELECT = 6 (S94–S96).
```

**S121 — the `Pure` payload-glue word (FIXME 0934, ruled; canonical:
`total-concreteness.md` §3.4, as amended by the S121 Phase-3 ownership-witness
re-ruling).** The `Pure` node gains a hidden second field:
`[header | tag@16 | payload@24 | payload_glue@32]` — the canonical `drop<T>`
glue address for the payload's concrete type, stamped by the backend at every
(post-mono concrete) construction site, or the sentinel `0` for a non-heap
payload. The word is the **single ownership/force state** after publication:
`0 = Scalar`, `1 = Claimed`, every other value = `Owned(glue)`. The run lane
and `free_io_node` both atomically exchange it to `Claimed` with `AcqRel`;
only the claimant that observes `Scalar` or `Owned(glue)` may read/transfer
field 0, and teardown calls through only an observed `Owned(glue)`. A second
force observes `Claimed`, raises the standard runtime-error outcome before
reading the payload, and creates no second owner. `1` is reserved and is never
a backend/platform stamp or a call target. Construction and platform adoption
initialise the fresh unpublished node non-atomically; every intrinsics access
after publication is atomic. Existing node-publication, RC and structured-join
edges remain the lifetime boundary (complete rule and evidence:
`total-concreteness.md` §3.4). Every other IO node's layout is unchanged. The IO-node family is a layout contract governed
by `cranelisp_platform::ABI_VERSION` (Principle 14): this change bumps
**9 → 10**, executed in the S121 platform stream together with the platform
test-fixture rebuilds.

**S121 — platform-return stamps are tag-dispatched (`/arch`, 2026-09-01;
canonical: `total-concreteness.md` §3.4 "the platform-return seam").** At the
backend's one platform-call chokepoint, the post-call stamp is selected by the
**returned node's tag**, never by the callee's kind alone: `IO_TAG_EFFECT` ⇒
the FQ fn-name pointer into the Effect node's field-3 (base+40);
`IO_TAG_PURE` ⇒ the payload's canonical `drop<T>` (or the sentinel `0`) into
the payload-glue word (base+32, valid at ABI ≥ 10 only); any other tag ⇒ **no
write** (degrades exactly as a null fn-name handle does). The pre-S121
kind-keyed unconditional field-3 store was an out-of-bounds heap write for a
`Pure`-returning platform fn at both v9 and v10 (latent — no shipped platform
fn returns `Pure`). Authority split at the crossing: the DLL's only legal
glue-word write is the sentinel `0`; the backend is the sole stamp authority;
intrinsics is the sole post-publication state owner (run-lane claim plus
teardown claim). Lands in C4 bundle B5 and C5 I0b; register rows R19/R20.

---

## Typecheck Entry Point

The single entry point for type checking. Defined in `cranelisp-typecheck`.

```rust
impl TypeChecker {
    /// Check a compilation unit.
    ///
    /// Architectural invariant: this is the SOLE entry point for type checking.
    /// There is no check_repl_input or other parallel function. (Principle 11)
    ///
    /// The `ctx` parameter specifies the target module and strategy:
    /// - `ctx.module`: definitions are registered into this module.
    /// - `ctx.strategy`: Replace clears existing module state first;
    ///   Additive extends it. See pipeline-v2.md §14.
    ///
    /// Always multi-pass: register all signatures (Pass 1), check all bodies
    /// (Pass 2), detect constrained fns, monomorphise, resolve auto-curry.
    /// Works identically on a batch program (many forms) or a REPL line (one form).
    ///
    /// Side effects: all durable output is deposited onto the relevant
    /// `SymbolTable` entries before returning — annotated `ast: Some(Defn)`,
    /// `scheme`, `callees`, `got_slot`, and mangled multi-sig / mono variant
    /// entries. See `design/typecheck/ast-annotation.md` for the full
    /// symbol-table contract.
    ///
    /// Returns: `CheckResult { warnings, display }` only. Not a boundary
    /// contract — the backend does not receive this value; it reads the
    /// symbol table directly.
    pub fn check(
        &mut self,
        ctx: &CompileContext,
        program: &[TopLevel],
    ) -> Result<CheckResult, CranelispError>;
}
```

---

## Backend Compilation Entry Point

The single entry point for codegen. Defined in `cranelisp-backend`. This is the sole compilation function; there is no `compile_program`, no `compile_expr_with_got_and_symbols`, and no separate object-file compilation path (Principle 11).

```rust
/// Compile the named symbols of `module_path` into `module`.
///
/// Normative signature — four parameters. See
/// `design/backend/compile-to-module.md` §2.1 for the full contract.
///
/// Preconditions:
/// - For every name in `names`, `symbol_tables[module_path].get(name)`
///   returns a `ModuleEntry::Def` with `ast: Some(_)` carrying fully
///   annotated AST nodes (`inferred_type` and `resolved_call` populated).
///   A `None` body is a typecheck bug — `compile_to_module` returns
///   `CranelispError::CodegenError` naming the offending symbol.
/// - `names` should be obtained via `SymbolTable::defined_symbols()`
///   (shared predicate — see below). Callers that pass a subset must
///   ensure every element satisfies the same predicate.
///
/// Generic over the Cranelift `Module` impl so one function serves both
/// the JIT (`JITModule`) and object (`ObjectModule`) paths.
pub fn compile_to_module<M: Module>(
    module_path: ModuleFullPath,
    names: &[Symbol],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
    module: &mut M,
) -> Result<CompilationResult, CranelispError>;

/// Declare the intrinsic imports that `compile_to_module` may call into.
/// Call once per module creation, before `compile_to_module`.
pub fn declare_intrinsics<M: Module>(module: &mut M) -> IntrinsicIds;
```

### CompilationResult (NEW)

Returned by `compile_to_module`. Module-type-agnostic: the caller extracts what it needs (entry point for JIT; full map for object emission).

```rust
/// Result of compiling a set of named symbols into a Cranelift module.
///
/// Backend -> caller boundary. Replaces legacy `CompiledProgram` and
/// `CompiledModuleInfo`. See `design/backend/compile-to-module.md` §8.
#[derive(Debug)]
pub struct CompilationResult {
    /// FuncIds for all compiled functions, keyed by the same `Symbol` that
    /// appeared in `names` (mangled where the symbol table entry is mangled).
    pub func_ids: HashMap<Symbol, FuncId>,

    /// Per-symbol introspection artifacts (CLIF IR, disassembly, code size).
    /// Empty when capture is disabled (e.g., `--run` or object emission).
    /// The caller routes these onto `SharedState.introspection` if desired;
    /// the backend never touches `introspection` directly.
    pub artifacts: HashMap<Symbol, FunctionArtifacts>,

    /// FuncId of the entry function (last zero-arg defn), if any.
    /// JIT batch mode uses this to obtain the entry point; object mode
    /// ignores it.
    pub entry_func_id: Option<FuncId>,

    /// Arities for all compiled functions (used by closure wrapper generation).
    pub func_arities: HashMap<Symbol, usize>,

    /// Warnings accumulated during codegen (backend-phase warnings only).
    pub warnings: Vec<Warning>,
}

/// Per-symbol codegen byproducts. Captured during the same `FnCompiler`
/// pass that defines the function — no recompilation.
#[derive(Debug, Clone)]
pub struct FunctionArtifacts {
    pub clif_ir: String,
    pub disasm: String,
    pub code_size: u32,
}
```

### `SymbolTable::defined_symbols()` — shared codegen-compilable predicate

Both int's priority worker and the backend compile loop consume the one
types-owned predicate. In the unified lifecycle it is structural:

```rust
pub fn defined_symbols(&self)
    -> impl Iterator<Item = (&Symbol, &Binding<C>)>
{
    self.symbols.iter().filter(|(_, binding)| {
        matches!(
            binding.callable().map(|callable| &callable.life),
            Some(Life::Concrete {
                realization: Realization::Body { .. },
                ..
            })
        )
    })
}
```

A codegen-enumerated binding therefore has a slot and concrete body view by
construction. Groups, templates, inline/by-name callables, extern/DLL/facade
realizations, and broken entries are excluded by their lifecycle shape rather
than an `ast.is_some()` plus kind-exclusion list. The GOT remains the runtime
address source; `Realization::Body.code` is the serde-skipped lifecycle owner.

---

## Summary of Changes from v1

### Types deleted
- `ReplInput` — replaced by `TopLevel` with `Expr` variant
- `ReplCheckResult` — replaced by `CheckResult` with `display: Option<DisplayInfo>`
- `CheckResult` as a **boundary type** — demoted to typecheck-internal (Sprint 55/56). The struct still exists transiently in `cranelisp-types/src/check.rs` carrying `warnings + display` plus legacy working fields pending Phase 5 slimming (FIXME filed by `/typecheck`). It is no longer a parameter of any backend function.
- `ModuleStructure` (in `src/save.rs`) — dissolved at Sprint 58 Step 5a; fields move 1:1 to `SymbolTable.{imports, exports, platforms, submodules}`. The `SharedState.module_structures` parallel store is deleted. See Decision 33.

### Types added
- `TopLevel::Expr(Expr)` variant
- `DisplayInfo` — REPL display payload
- `CallGraph`, `CallEdge`, `CallInfo` — transient within-module call graph (rich, with tail-position/span) *(DELETED S119, FIXME 0918 — never consumed)*
- `FormCheckResult` — per-form typecheck output with `call_graph_edges: Vec<(Symbol, FQSymbol)>` (typecheck-internal)
- `ModuleEntry::Def.callees`, `ModuleEntry::Macro.callees` — persistent per-symbol `Vec<FQSymbol>` for cross-module call graph queries (Decision 21)
- `ModuleEntry::Def.ast: Option<Defn>` — annotated AST body deposited by typecheck; consumed by `compile_to_module` (Sprint 55 Phase 1). Authoritative table in `design/typecheck/ast-annotation.md` §6.
- `WarningKind::NonTailRecursion` — new warning category
- `CompileContext` — explicit compilation context (module target, strategy, compile mode)
- `ModuleStrategy` — additive vs replacement module compilation
- ~~`GotSlotMap`~~ — removed. GOT slot assignments are persistent session state in `ModuleCodegenState`, not a pipeline output. See `pipeline-v2.md` §12.5.
- `FnSlotEntry { module: ModuleFullPath, slot_index: usize }` — identifies a function's GOT location (which module's GOT, which slot). See `design/backend/per-module-got.md`.
- `ModuleGotRegistry` — per-module GOT table registry, replaces flat `InMemWorkerState.got_state`. Lives in `cranelisp-backend`.
- `CompilationResult` + `FunctionArtifacts` — backend output of `compile_to_module` (Sprint 56 Phase 2). Replaces `CompiledProgram` and `CompiledModuleInfo`.
- `CodeStore` + `LinkerStore` marker traits (Sprint 58 Step 5c, Decision 32) — generic boundary on `SymbolTable<C, L>` and the `Binding<C>` lifecycle tree. Both default to `()`. See `pipeline-v4.md` §9.1.
- `SymbolTable.imports`, `.exports`, `.platforms`, `.submodules` (Sprint 58 Step 5a, Decision 33) — structural declarations as fields, not a parallel store. Reuse existing `cranelisp-types::{ImportSpec, ExportSpec, PlatformSpec, ModDecl}`.
- `SymbolTable.linker: Option<L>` (Sprint 58 Step 5c) — per-module linker store for cache-hit `.o` mapping. `#[serde(skip)]`.
- `SymbolTable.schema_version: u32` (Sprint 58 Step 5b, Decision 34) — explicit cache schema version; mismatch invalidates the cache as if dependencies changed.
- `Code` enum (Sprint 58 Phase 3a, Decision 35; Sprint 64 location move per Decision 41; **Sprint 66 variant slimming preserved through the same-day fn_ptr-unification rollback**) — concrete `C` for `SymbolTable<Code, ()>`. Variants `Code::Jit(Arc<Jit>)` + `Code::Linker(Arc<Linker>)` — lifecycle owner ONLY post-S66; the per-entry call address lives in `SymbolTable.got()` (the post-rollback single source of truth — see `crates/cranelisp-types/src/got.rs`), indexed by `ModuleEntry::Def.got_slot`. Lives in `cranelisp-backend/src/code.rs` (moved from `src/code.rs` per Decision 41), NOT in `cranelisp-types` (Principle 3). The CP1 Layer-2-Option-B return-tuple pattern retracts: `compile_to_module` writes the resulting fn pointer to the entry's GOT slot via `symbol_table.got().store_slot(slot, ptr)` (D41 #2) and returns `Result<CompilationArtifacts, CompilationError>` (S70 Phase B). The **caller** composes `Code::Jit(Arc<Jit>)` / `Code::Linker(Arc<Linker>)` and submits it through the accepted types-owned `SymbolTable::publish_compiled_owner` capability (D41 #1 — the caller's, not backend's, per S75 W2 Finding-A; backend only borrows `&mut M`). `write_code` was an unimplemented design spelling, not an approved API. Documented at this boundary so every consumer of `SymbolTable<Code, ()>` references the same ownership split.
- `ModuleEntry` callable slot (HISTORICAL flat-field framing — since S83 the slot rides the callable `DefKind` variants, read via `callable_got_slot()`; this row records the pre-S83 shape) — single source of truth for "where to call to invoke this entry" (Sprint 56 G7; reaffirmed Sprint 66 post-rollback per `1dc57ae`). Indexes into `SymbolTable.got()`; the runtime address is `got().load_slot(slot)`. The S66 unification briefly placed the address on a sibling `ModuleEntry::Def.fn_ptr` field (commit `b09ec76`); the same-day rollback `1dc57ae` removed that field as redundant with the GOT. No per-entry pointer field exists post-rollback. Origin encoded by `kind: DefKind` (UserFn → JIT/linker; Primitive { Inline | Extern } → primitive; Primitive { PlatformEffect } → platform DLL). See `crates/cranelisp-types/src/module.rs` `ModuleEntry::Def.got_slot` rustdoc + Decision 41 S66 amendment + rollback.
- `ParsedEntry` enum (Sprint 66, FIXME 0156) — parse-time-only transient produced by `cranelisp_frontend::build_form` and consumed (as `Vec<ParsedEntry>`) by `cranelisp_typecheck::check_forms`'s single-call cluster surface (per Decision 44's 2026-05-13 third amendment; internal two-pass discipline). NEVER lands in `SymbolTable`. Orchestrator accumulates the vector across the cluster's forms and hands it to one `check_forms` call. `#[non_exhaustive]`; not `Serialize/Deserialize`; derives `Clone` so the orchestrator can rebuild the vector for Gap-retry. See `crates/cranelisp-types/src/parsed.rs` rustdoc + `crates/cranelisp-frontend/src/lib.rs` //! preamble (post-S70 B3-C frontend canonical) + `crates/cranelisp-typecheck/src/lib.rs` rustdoc (post-S72 W5 typecheck canonical; `facades/typecheck.md` retired).
- `DefmacroInfo` struct (Sprint 66, FIXME 0156) — moved from `cranelisp-frontend/src/defmacro.rs` to `cranelisp-types` so `int`'s post-`build_form` consumption path can name the type uniformly. Frontend's `parse_defmacro` becomes `pub(crate)` inside the `build_form` dispatcher.
- `View<'a, C, L>` newtype (Sprint 66, Decision 44 amended FIXME 0167) — composite read surface `(staging, live)` that wraps two `&SymbolTable` refs and routes lookups staging-first then live. Constructed inside `SymbolTableAccess::current_symbol_table()` (in `cranelisp-typecheck`); in `Cluster` mode returns `View::union(staging, live)`, in `Live` mode returns a single-source view. Typecheck reads through `ctx.current_symbol_table()` whenever it would have read `&SymbolTable` directly. No allocation per lookup; lifetime-bounded; read-only. See `crates/cranelisp-types/src/view.rs` rustdoc.

- `SymbolTableAccess<'a, C, L>` enum (Sprint 66, Decision 44 amended FIXME 0167; 2026-05-13 third amendment) — staging-vs-live abstraction that absorbs the surgery point for cluster-atomic typecheck under Approach B. Lives in `cranelisp-typecheck` (single-consumer pair: typecheck owns the structural shape; `int` constructs and threads instances). Two variants: `Live { modules }` for committed-mode access, `Cluster { modules, staging: &mut SymbolTable, current_module }` for cluster processing. Two accessors: `current_symbol_table() -> View<'_, C, L>` (read), `current_symbol_table_mut() -> &mut SymbolTable<C, L>` (write). The 91 register-call sites and 51 read access sites in `crates/cranelisp-typecheck/src/program.rs` flow through these accessors unchanged — staging-vs-live distinction is invisible to typecheck. See `crates/cranelisp-typecheck/src/lib.rs` rustdoc (post-S72 W5 canonical; `facades/typecheck.md` retired — cross-surface narrative in `bounded-contexts.md` §2).

### Types NOT added
- ~~`CheckMode`~~ — eliminated during design review. The multi-pass pipeline works identically on any input size. See `pipeline-v2.md` §5.

### Functions deleted
- `check_repl_input()` — replaced by `check()` (no mode parameter)
- `build_check_for_backend()` — both copies
- `toplevel_to_repl_input()` — no conversion needed
- `build_repl_input()` — no separate builder needed
- `compile_program`, `compile_expr_with_got_and_symbols`, `compile_module_to_object` — replaced by the single `compile_to_module<M: Module>` (Sprint 56).

### Functions changed
- `TypeChecker::check(&mut self, ctx: &CompileContext, program: &[TopLevel])` — single typecheck entry point, now takes explicit context; `CheckResult` is no longer a backend input.
- `compile_to_module<M: Module>(scope, names, symbol_tables, module_aliases, module)` — normative signature (Sprint 56 Phase 2; `module_aliases` added S75 W2). No `CheckResult`, no `Program`, no intrinsic IDs, no GOT map, no arities parameter. **Per Decision 41 (Sprint 64) + S66 amendment + rollback + S70 Phase B amendment + S75 W2 Finding-A correction**: returns `Result<CompilationArtifacts, CompilationError>`; backend writes the resulting fn pointer to the entry's GOT slot via `symbol_table.got().store_slot(entry.got_slot.unwrap(), ptr)` directly (D41 #2 — the GOT is the post-rollback single source of truth for callable addresses; the briefly-considered sibling `fn_ptr` field landed in `b09ec76` and was rolled back the same day in `1dc57ae`). The **caller** composes `Code::Jit(Arc<Jit>)` / `Code::Linker(Arc<Linker>)` and submits it through the accepted `SymbolTable::publish_compiled_owner` capability (D41 #1 — the caller's; backend only borrows `&mut M`, never owns the `Arc<Jit>`). On-demand disassembly is the separate `produce_disasm(fq, code_size, symbol_tables)` (caller-supplied `code_size` + capstone; S75 W2 Finding-C). See `bounded-contexts.md` §3 (backend) + the `crates/cranelisp-backend/src/lib.rs` rustdoc (`facades/backend.md` retired S75 W5b → BC §3 + source rustdoc) and `design/backend/compile-to-module.md`.
- `cranelisp_frontend::build_form(sexp: &Sexp) -> Result<Vec<ParsedEntry>, CranelispError>` (Sprint 66, FIXME 0156) — replaces the prior `build_ast` shape at the frontend's per-form boundary. Returns a `Vec` because some shapes yield more than one entry per source form (multi-clause `defmacro`, `deftype` with constructors). See `crates/cranelisp-frontend/src/lib.rs` //! preamble (post-S70 B3-C the frontend canonical surface contract).
- `cranelisp_typecheck::check_form` collapses to a **single `check_forms` free function** (Sprint 66, FIXME 0160 + Decision 44 amended FIXME 0167 + 2026-05-13 third amendment): `check_forms(parsed: Vec<ParsedEntry>, ctx: &mut SymbolTableAccess<'_, C, L>, symbol_tables: &SymbolTables<C, L>) -> Result<(), CheckError>`. Pre-S66 the legacy `check_form` mutated the table in-place via a typecheck-internal `merge_form_result()`; FIXME 0160 first purified it to a single-call pure function; Decision 44 then split that single call into a two-function Pass 1 (signatures) + Pass 2 (bodies) shape so spec §5.13.1's two-pass mandate (forward references / mutual recursion) survives the orchestrator-side cluster. The two-function shape exposed implementation phasing across the facade and created a state-threading hole; the third amendment collapses it back into a single `check_forms` call that runs both passes internally. Pass-1-to-Pass-2 working state lives inside `check_forms`'s frame and never crosses the facade. FIXME 0167's Approach B + SymbolTableAccess discipline is preserved: staging is empty at cluster start; reads via `View::union(staging, live)`; writes go to staging via the same `current_symbol_table_mut` accessor used in committed-mode. `check_forms` is pure with respect to live state; it does not mutate the live `SymbolTable`. The 91 register-call sites in `program.rs` do not change individually — staging-vs-live is absorbed inside `SymbolTableAccess::current_symbol_table{,_mut}` accessors. The caller (`int::process_cluster`) constructs `SymbolTableAccess::Cluster` with a transient orchestrator-local staging table and commits staging into the live table atomically via `int::insert_cluster` only on whole-cluster success; on `Err(Gap)`, the orchestrator drops the staging frame and retries the whole `check_forms` call against a fresh staging frame; on `Err(TypeError)`, staging dissolves with the function frame (live table byte-identical). See `crates/cranelisp-typecheck/src/lib.rs` rustdoc (post-S72 W5 canonical; `facades/typecheck.md` retired — cross-surface narrative in `bounded-contexts.md` §2), `bounded-contexts.md` §6 (int) + `src/cluster.rs` rustdoc for the `process_cluster` orchestrator side (`facades/int.md` retired S81 W-Retire → BC §6 + `design/int/` + source rustdoc), and the `check_forms` section above.

### Functions added
- `CallGraph::add_edge()`, `reverse_index()`, `sccs()`, `non_tail_self_recursion()` *(DELETED S119 with the type, FIXME 0918)*
- `SymbolTable::defined_symbols() -> impl Iterator<Item = (&Symbol, &Binding<C>)>` — shared `Concrete × Realization::Body` codegen predicate (Decision 22, reshaped S121 C1).
- ~~`declare_all_got_slots()`~~ — removed. GOT slots are assigned incrementally by `ModuleCodegenState::ensure_slot_for()` during function registration, not in a separate phase. See `pipeline-v2.md` §12.5.

### Coherence checklist
- [x] No structurally identical types at any pipeline boundary
- [x] No adapter functions between boundary types
- [x] Every pipeline stage has exactly one entry point per crate
- [x] Mode differences expressed as parameters, not separate types
- [x] All spec-required TopLevel variants present (§5.1–5.4, §4)
- [x] `Serialize`/`Deserialize` on all boundary types that need caching
- [x] Module context is an explicit parameter (`CompileContext`), not implicit mutable state
