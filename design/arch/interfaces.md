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
/// S-expression: the reader's output. 8 variants covering all syntactic forms.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Sexp {
    Symbol(String, Span),
    Int(i64, Span),
    Float(f64, Span),
    Bool(bool, Span),
    Str(String, Span),
    List(Vec<Sexp>, Span),
    Bracket(Vec<Sexp>, Span),
    Comment(String, Span),
}

impl Sexp {
    pub fn span(&self) -> Span { ... }
}
```

No changes from v1.

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

/// Stored impl S-expression for deferred processing.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImplSexp {
    pub trait_name: TraitName,
    pub target: TypeName,
    pub sexp: Sexp,
}
```

No changes from v1.

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

/// Trait method signature. spec: §5.3
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitMethodSig {
    pub name: Symbol,
    pub docstring: Option<String>,
    pub params: Vec<TypeExpr>,
    pub ret_type: TypeExpr,
    pub span: Span,
    pub hkt_param_index: Option<usize>,
    pub default_param_names: Vec<Symbol>,
    pub default_body: Option<Sexp>,
}

/// Trait declaration. spec: §5.3
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitDecl {
    pub name: TraitName,
    pub docstring: Option<String>,
    pub type_params: Vec<Symbol>,
    pub methods: Vec<TraitMethodSig>,
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
    ADT(TypeName, Vec<Type>),
    Var(TypeId),
    TyConApp(TypeId, Vec<Type>),
}

impl Type {
    pub fn from_name(name: &str) -> Option<Type> { ... }
    pub fn type_name(&self) -> Option<&'static str> { ... }
    pub fn is_heap(&self) -> bool { ... }
}

/// Polymorphic type scheme.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Scheme {
    pub vars: Vec<TypeId>,
    pub constraints: HashMap<TypeId, Vec<TraitName>>,
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
| `call_graph: CallGraph` | Transient within-module graph still produced during typecheck for TCO / analysis (see §"Call Graph"); persistent per-symbol `callees: Vec<FQSymbol>` lives on `ModuleEntry::Def` / `ModuleEntry::Macro` per Decision 21. |

**Callability is structural — GOT slot on the callable `DefKind` variants (FIXME 0356/0357, Principle 20; amends Decision 35; S83 target).** The row above notes a constrained template is the *negation of `defined_symbols()` within `UserFn`* — i.e. it is **not** codegen-compilable. The dual fact at the call-resolution seam is that it is **not directly callable**, and the S83 target makes this a property of the *shape* rather than an accessor convention. The S82 stopgap (`callable_got_slot()` reading around an illegal `got_slot`+template pairing, `mark_constrained_template()` flip-and-clear sole-writer, `assert_well_formed()` debug guard) is superseded: the `got_slot` migrates **off the flat `ModuleEntry::Def` field and onto the callable `DefKind` variants** (`UserFn`'s concrete-callable form, `Primitive`, `Constructor`, `PlatformEffect` — the four GOT-indirect-dispatched callable kinds; `PlatformEffect` ratified into this set S83 per FIXME 0358, correcting the Phase-2 gating-decision-2 omission); non-callable / non-GOT-dispatched kinds (the constrained-template form of `UserFn`, `Macro` parent, `PrimitiveExtern` — which dispatches by-name via `Linkage::Import`, FIXME 0360 — and the `Overloaded` base) carry no slot field, so `Def{slot}+template` is **unconstructable**. The timing wall (Pass-1 slot allocation preceded Pass-2 constraint detection) resolves by **deferring slot allocation past Pass-2 detection** — the entry has no slot until its callability is determined, which is correct because nothing may call it before then; no `Pending` interstage variant is needed. `callable_got_slot()` survives as the single read-through point (so callers do not re-pattern the kind set) but becomes a trivial present-or-absent read on the matched variant; `mark_constrained_template()` and the phantom-slot assertion retire. Backend call-target resolution (`resolve_got_target`) reads through `callable_got_slot()` exactly as before — its body changes, its contract does not. Mono variants (`cmp$Int+Int`) are ordinary concrete `UserFn` entries owning their own slot — the home for the S83 cross-module-mono feature (FIXME 0355). See BC §7 "Callability is structural" + Principle 20.

**S84 generalisation (user-ratified 2026-06-16; FIXME 0374; BC §7 + Principle 20).** The S83 statement above — "a constrained template has no slot" — is the constrained-template *species* of the general invariant **"a def has a GOT slot ⟺ its type is fully concrete (`Type::is_concrete()`, no `Type::Var`)."** A *plain parametric/generic* def (`id : ∀a. a→a`, a `(Box a)`-result HOF) carries **no trait constraints** yet is **not** concrete, so it too must be slot-less; only its monomorphised instances (`id$Int`, `(Box Int)`) are slotted. The slot-allocation gate therefore tests **`is_concrete()`, not `constraints.is_empty()`** — the as-built S83 gate (`program.rs:947` single-sig / `:1143` multi-sig, with the reuse legs at `:919`/`:1129`/`:1312`) tested the latter and leaked a `Concrete { got_slot }` for a generic-unconstrained def carrying a `Type::Var`, which reached `classify(Type::Var)` → SIGSEGV (S84 Wave-0 `mono_tier2_generic_adt_field_through_hof_no_crash`). `Concrete { got_slot }` is constructed only when `is_concrete()`; the determined-but-non-concrete unconstrained generic def gets a slot-less `fn_state` sibling to `Constrained`. `Type::is_concrete()` is a `cranelisp-types` public item (the GOT-slot-eligibility predicate; one additive `public-api.txt` line). This is the typecheck-side structural complement of monomorphisation-from-roots (FIXME 0374) and 0375's codegen-side backstop. **The slot-less arm landed (S84 Wave 1, FIXME 0377):** a distinct `UserFnState::Polymorphic(Box<ParametricFn>)` variant, sibling to `Constrained`, carrying `ParametricFn { variant: DefnVariant, scheme: Scheme }` (the body `monomorphise_call` re-checks at concrete types — the same payload `ConstrainedFn` carries, minus the trait-dictionary semantics; a dedicated struct rather than a `ConstrainedFn` reuse so the *why*-distinction stays legible at every exhaustive matcher). `callable_got_slot()` answers `None` structurally; `defined_symbols()` includes it as a mono target (unlike `Constrained`, which is skipped). Both are additive `public-api.txt` lines; `UserFnState`/`DefKind`'s serde shape changing forces a `CACHE_SCHEMA_VERSION` 5→6 bump (`cranelisp-backend/src/cache/mod.rs`) in the same change-set.

**Mono-instance linker identity is lossless by construction — a single-sourced, total mangler (S102, FIXME 0516; Principle 7 + Principle 20).** A monomorphic instance's slot (above) is one of its two structural identities; the other is its **mangled name** — the symbol-table key under which `register_mono_entry` inserts it and the `LinkerSymbol` the backend emits. That name MUST be a **total, collision-free function of the three distinguishing facts: the DEFINING module (`ModuleFullPath` — `home` when the fn is imported per FIXME 0355, else the current module), the bare fn name, and the recursively-mangled fully-concrete param signature.** The grammar is `{home}/{bare}${recursive-concrete-sig}` where the sig mangler recurses into every concrete `Type` variant (ADT type-args, `Fn` arg+return, `TyConApp`) so no distinguishing type-structure is dropped. **Collision-freedom is by representation (Principle 20): two instantiations that differ in any of the three facts mint different names; the illegal "two distinct instantiations, one name" state is unrepresentable.** The invariant was VIOLATED as-built along two axes — ADT type-args erased (`apply2@(Vec Int)` and `apply2@(Vec String)` both `apply2$Vec+Int` → the 0483 SIGBUS: two instantiations collapse to one body/slot, the surviving String-typed heap elem-dec runs on Int payloads) and home erased (two same-named imported generics `a/iden2`, `b/iden2` both `iden2$Int` → 0508 silent wrong-dispatch). Both are one bug: `build_mangled_name`/`concrete_type_name` dropping distinguishing information. The cure is **one canonical mangler, single-sourced (Principle 7)** — the three as-built stringly sites (`monomorphise.rs::build_mangled_name`/`concrete_type_name`, `program.rs::mangle_type`/`mangle_sig`, and the hand-rolled `seen`-dedup key at `program.rs:~3469`) unify onto it; `mangle_type` already recurses ADT args correctly and is the closer-to-canonical mirror. The name is an **opaque `String`/`LinkerSymbol` at every crate boundary** (produced in typecheck, consumed by name only through GOT-slot dispatch and the linker), so the grammar change is NOT a `public-api.txt` move — but the mangled name is the on-disk `.meta.json` entry identity, so it IS a `CACHE_SCHEMA_VERSION` bump in the same change-set. Any backend-side name that embeds a concrete signature (the `__inlwrap_{bare}_{sig}__` wrapper family, `ownership-codegen.md` §13.3 Ruling 1) MUST mangle that sig by the same total grammar, else it re-opens the mirror one level down.

**The gate is TOTAL — no `monomorphisable-from-params` carve-out; test fns are mono roots (S84 Wave 1b, user-ratified 2026-06-16; FIXME 0378 issue 3; /arch + /int).** The slot⟺`is_concrete()` invariant is *unconditional*. The Wave-1 landing carried a pragmatic carve-out (`fn_type_is_monomorphisable_from_params`, `program.rs:181`) that kept a **result-only-polymorphic** def (`test-* : (Fn [] (Option a))`) `Concrete`-with-a-slot — because such a def has no call-site parameter to monomorphise *from*, and the `/run-tests` names-only discovery reader (`discover_test_names`, `src/session_v4.rs:2533`) found tests via `callable_got_slot()`, so a slot-less test fn would be stranded. The ruling retires this carve-out by making **discovery-driven entry points (test functions) explicit monomorphisation ROOTS**, the same way `main` is the program root: the root carries the discovery contract's expected entry type `(Fn [] (Option String))` (`test_scheme_is_eligible`, `src/session_v4.rs:2816`), and `pass4_monomorphise` mints a concrete `Concrete{slot}` instance from the polymorphic original at that type. This is no new boundary type — the minted instance is an ordinary `MonoDefn`/`Defn` `Concrete` `UserFn` entry, found through the existing symbol-table lookup + `callable_got_slot()` chokepoint. The cross-crate seam is **mechanism-only** (typecheck registers the root; int's names-only reader resolves to the concrete instance's name instead of the original's now-absent slot — preferred shape: the concretised entry registers under the bare name so the reader stays byte-identical). **No `cranelisp-types` change, no `public-api.txt` move, no cache bump** — the `Polymorphic` variant from FIXME 0377 already supplies the slot-less state the now-slot-less result-only-polymorphic def lands in. Full statement: BC §2 "The slot gate is TOTAL" + the mono-root rule + the discovery-seam paragraphs.

**`Type::is_representation_undetermined()` — RETIRING (gated on /dev; the WRONG predicate under the tightened §3.11.1, commit `2290aa9`).** This predicate embodies the now-REJECTED *representation-determinacy* notion: it returns `false` for `(Vec a)`/`(Fn a)` ("uniformly heap — admit the unpinned var"), which the tightened §3.11.1 now **rejects** (the strictness is full concreteness — no `Var` — with NO representation-based exemption). It is NOT the §3.11.1 verdict; the correct verdict is `!is_concrete()` (`ConcreteType::from_type(ty).is_err()`), which rejects ANY residual free var. **Retirement from `cranelisp-types` is gated on /dev switching the §3.11.1 call site** (`cranelisp-typecheck::program::is_codegen_ambiguous_type`) off it (FIXME 0386); kept-but-deprecated until then (removing it now breaks the typecheck build, which still calls it). On retirement: one `public-api.txt` removal line. The backend `heap.rs` references are comments only (the FIXME-0375/0381 backstop is deferred). See `design/arch/concrete-boundary-type.md` §1.4/§3.1. The original (now-superseded) narrative follows for the interim-state record:

**(SUPERSEDED) The shared codegen-ambiguity predicate (S84 Wave 2, user-ratified 2026-06-16; FIXME 0379).** A second `cranelisp-types` public item on `Type` (one additive `public-api.txt` line: `pub fn cranelisp_types::Type::is_representation_undetermined(&self) -> bool`; no cache bump — a pure `&self -> bool` adds no serde shape). It is **THE single source of truth** for "does this `Type` carry a representation-undetermined free `Type::Var` at a codegen/RC site," shared by two consumers so typecheck and backend **agree by construction** (Principle 7 + Principle 18): the typecheck-side position-complete §3.11.1 ambiguity check (FIXME 0379, /dev) uses it **directly** as the ambiguity verdict at every codegen-reaching value position; the backend-side RC backstop (FIXME 0375, /dev) gates it **behind its own `classify == Mixed`** verdict (`panic iff classify == Mixed && is_representation_undetermined()`). **TRUE** for a bare `Type::Var`, a `Type::TyConApp` (HKT head var), and a non-`Vec` `Type::ADT` carrying a free var (the `Mixed`-family case the bare-`Var` panic missed); **FALSE** for `Type::Fn` and `(Vec a)` (uniformly heap, `classify`→`AlwaysHeap` regardless of the free var), any fully concrete type, and a `Type::ADT` with no free var (the legitimate type-known nullary-tag `Mixed` case). It is **table-free and structural** — it captures the "carries a free var in a representation-bearing position" half; the backend supplies the "is `Mixed`-shaped" half from the symbol tables, which is what excludes a table-determined `NeverHeap`/`AlwaysHeap` ADT carrying a free var from the backend panic. Distinct from `is_concrete()`: `is_concrete()` is the **GOT-slot-eligibility** predicate (does this def get a slot?); `is_representation_undetermined()` is the **codegen-RC-ambiguity** predicate (is this value's machine shape decidable at an RC site?) — and they differ precisely on the uniformly-heap shapes, which are non-concrete (no slot) yet representation-determined (`(Vec a)`, `Fn`). Full statement: BC §3 invariant 9 "belt-and-braces" + `crates/cranelisp-types/src/types.rs` rustdoc.

**`ConcreteType` — the concrete-only codegen-boundary type (S84 user ruling 2026-06-16; Phase-1 scaffold landed; `design/arch/concrete-boundary-type.md`; FIXME 0383).** The user re-direction: generics should not be *representable* at the backend boundary at all. `ConcreteType` (`crates/cranelisp-types/src/concrete.rs`) is the concrete subset of `Type` — Int/Bool/String/Float, concrete `Fn`, concrete `ADT(FQTypeName, Vec<ConcreteType>)` — with **NO `Var` and NO `TyConApp` variant** (recursion on `ConcreteType`, so concreteness is total at every depth; derives `Eq+Hash`, which `Type` cannot). The **single fallible conversion** `ConcreteType::from_type(&Type) -> Result<ConcreteType, NotConcrete>` succeeds iff fully concrete; its `Err(NotConcrete::Var | HktHead)` IS the unified ambiguity/could-not-monomorphise error that today scatters across three guards (the §3.11.1 check, mono-failure, `classify(Var)` panic). This is Principle 18 applied to the boundary type itself — the fullest expression of Principle 20: where the slot gate made *callability* structural, `ConcreteType` makes *value-representation* structural. **Disposition vs the two predicates above:** once the arc's Phase 3 lands (`HeapCategory::classify` takes `ConcreteType`), `is_representation_undetermined()` and the §3.11.1 standalone scan are **subsumed by the conversion** and retired; `is_concrete()` survives, re-expressed as `from_type(..).is_ok()`, still the typecheck slot-gate predicate (it operates on `Type` *before* conversion). The boundary backstops (FIXME 0375/0381) are **deleted, not re-armed** — a `Type::Var` becomes inexpressible at the seam. **Phase-1 scaffold (landed):** the type + conversion + `NotConcrete`, additive `public-api.txt` (27 lines), no cache bump, dead code until Phase 2 (mono produces it) + Phase 3 (backend consumes it). Full arc + honest per-phase sizing: `design/arch/concrete-boundary-type.md`.

**`MonoExpr` — the post-monomorphisation codegen AST (S84 concrete-boundary arc Phase 2a, landed; `design/arch/concrete-boundary-type.md` §2.4; FIXME 0383).** A parallel codegen view of `Expr` (`crates/cranelisp-types/src/mono_expr.rs`) whose every node carries `ty: ConcreteType` **non-optionally** in place of `Expr`'s `inferred_type: Option<Box<Type>>` — a generic / `Type::Var` is *structurally unrepresentable* on a codegen node (there is no `Type` field on `MonoExpr` at all; the fullest expression of the user ruling — generics "shouldn't even be REPRESENTABLE there"). `MonoExpr` mirrors `Expr`'s 14 non-`Annotate` variants; the `Annotate` node is **erased** (collapsed to its inner node at build); `Lambda` param `TypeExpr` annotations are erased (the concrete param types ride in the lambda's `ConcreteType::Fn`); match arms are carried by a sibling `MonoMatchArm { pattern: Pattern, body: MonoExpr, span }` (pattern reused verbatim — it carries no type annotation; S109 §10 later adds `resolved_ctor: Option<FQSymbol>`); `Apply`/`Var` carry `resolved_call: Option<Box<ResolvedCall>>` and every node carries `span: Span` (S110 0583 moved the resolved STORAGE identity onto the nodes as `resolved_target: Option<FQSymbol>`; the S114 carrier flip retyped it as the non-optional `Var.resolution: VarRef` / `Apply.dispatch: ApplyRef` — see §Method Resolutions). The mono-defn wrapper is `MonoDefnVariant { name: Symbol, params: Vec<Symbol>, body: MonoExpr, span }` (the typecheck mono pass builds it at the Phase-2b seam — `monomorphise_call`, immediately after `apply_subst_to_defn`). The **fallible builder** `MonoExpr::from_expr(&Expr, ..) -> Result<MonoExpr, ViewBuildError>` (the signature carries three REQUIRED span-keyed sidecar parameters — `pattern_ctors` + the typed `var_refs`/`apply_refs` since S114; the lenient counterpart `lenient_from_expr` and the all-local `synthetic_local_from_expr` live beside it — §Method Resolutions) walks an `inferred_type`-annotated `Expr`, converting each node via `ConcreteType::from_type`, and **fails at the first non-concrete node** (`ViewBuildError::NotConcrete` wrapping `NotConcrete::Var`/`HktHead`; an un-annotated node is the `NotConcrete::Var(0)` sentinel) **or resolution-verdict miss** (`ViewBuildError::Unresolved{span,name}` — the located phase-boundary gate) — the `NotConcrete` failure is the unified ambiguity/could-not-monomorphise error. Derives `Debug, Clone, Serialize, Deserialize` (no `PartialEq`/`Eq` — `Expr` cannot, carrying `f64`); accessors `span()`/`ty()`. **Phase 2a (landed):** the representation + builder + 10 unit tests, additive `public-api.txt`, **`CACHE_SCHEMA_VERSION` bumped 6 → 7** (the mono serde shape participates in the cached `.meta.json` surface). Produces-but-unused for codegen — the backend still reads `Expr.inferred_type` until Phase 3; the typecheck mono pass wires `from_expr` in Phase 2b (/dev(typecheck)).

**`ModuleEntry::Def.codegen_view` — the concrete-boundary threading field (S84 concrete-boundary arc Phase 3, threading shape LANDED; `design/arch/concrete-boundary-type.md` §3.0/§4 Phase 3).** The threading decision — how `MonoExpr` reaches the backend per codegen-bound entry — is ruled **option (a), additive field**: `ModuleEntry::Def` gains `codegen_view: Option<MonoDefnVariant>` (`crates/cranelisp-types/src/module.rs`) **alongside** the existing `ast: Option<DefnVariant>`. The backend's Phase-3 read path consumes `codegen_view`'s `MonoDefnVariant.body: MonoExpr` — `ty: ConcreteType` on every node, so **no `Type`/`Var` on the read path by construction** (Principle 18/20). Read through `ModuleEntry::codegen_view(&self) -> Option<&MonoDefnVariant>` (`None` for non-`Def` and non-codegen entries); populated via `DefBuilder::codegen_view(self, MonoDefnVariant) -> Self`. **NOT a type-swap of `ast`** (`Option<DefnVariant>` → `Option<MonoDefnVariant>` would break ~26 literal-construction sites + the `Defn`-reconstruction path at once — a non-green cascade); the additive field defaults `None`, keeping the build green and letting /dev migrate the read path incrementally. **NOT a separate structure `compile_to_module` takes** (rejected — that re-introduces the transitional parallel-`Vec` shape at the crate boundary; the view belongs ON the entry, the symbol table being the per-symbol codegen-input carrier, Principle 7). **Populated for BOTH codegen-bound cases:** monomorphised instances (the mono-population seam moves the already-built `MonoDefnVariant` off the transitional `CheckState.mono_variants` parallel `Vec` onto the entry — `register_mono_entry`), AND ordinary concrete (`UserFnState::Concrete`) defns (the same `MonoExpr::from_expr` over the annotated body at the body-check `.ast(...)` sites). Template kinds / primitives / special forms get `None` — correctly not codegen targets. **Landed:** the field + accessor + setter (+3 additive `public-api.txt` lines), `CACHE_SCHEMA_VERSION` **7 → 8** (the serialized `ModuleEntry::Def` shape changed; `#[serde(default)]` field, no pointer/`C` state). The backend's consumption (classify-becomes-total, the ~13 `inferred_type` read sites → `MonoExpr.ty()`, `compile_to_module` reads `codegen_view`, the single relocated `expect` backstop) is /dev(backend) — FIXME 0391; the typecheck population move is /dev(typecheck) — FIXME 0392.

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

## Call Graph (NEW)

Cross-cutting data structure populated during typecheck, consumed by analysis passes, codegen, and the binary crate.

```rust
/// An edge in the call graph.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CallEdge {
    /// The callee being called.
    pub callee: Symbol,
    /// Whether this call is in tail position.
    pub tail_position: bool,
    /// Source location of the call.
    pub span: Span,
}

/// Per-function call information.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CallInfo {
    /// Functions this function calls.
    pub callees: Vec<CallEdge>,
}

/// Transient within-module call graph. Adjacency list representation.
/// Rich edges with tail-position and span for codegen/analysis.
///
/// Populated during typecheck (Stage 5). Held as typecheck-internal
/// state during checking; not a cross-crate boundary value.
/// Consumed by:
/// - Analysis passes (SCC detection, recursion warnings — typecheck-internal)
/// - Codegen (tail call optimization decisions — read indirectly via
///   `ModuleEntry.callees` and AST annotations, not via `CheckResult`)
///
/// For cross-module / persistent call graph queries, use the per-symbol
/// `callees: Vec<FQSymbol>` on `ModuleEntry::Def` and `ModuleEntry::Macro`.
/// That representation is populated by `finalize_check_result()` and
/// queryable via `tc.symbol_table(module).get(name)`. See Decision 21.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CallGraph {
    /// Forward edges: caller -> list of callees.
    pub edges: HashMap<Symbol, CallInfo>,
}

impl CallGraph {
    /// Record a call from caller to callee.
    pub fn add_edge(
        &mut self,
        caller: &Symbol,
        callee: Symbol,
        tail_position: bool,
        span: Span,
    ) { ... }

    /// Build reverse index: callee -> set of callers.
    pub fn reverse_index(&self) -> HashMap<Symbol, HashSet<Symbol>> { ... }

    /// Find strongly connected components (Tarjan's algorithm).
    pub fn sccs(&self) -> Vec<Vec<Symbol>> {
        todo!("implemented when mutual recursion support arrives")
    }

    /// Find self-recursive calls not in tail position.
    pub fn non_tail_self_recursion(&self) -> Vec<(Symbol, Span)> { ... }
}
```

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

### `check_forms` (Sprint 66, FIXME 0160 + Decision 44 amended FIXME 0167 + 2026-05-13 third amendment)

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

**Cluster atomicity**. The orchestrator drives Pass 1 across every
`ParsedEntry` in a cluster, then Pass 2 across every `ParsedEntry` in
the cluster, then commits staging into live on success. A cluster is one
form (non-`begin` REPL input), the contents of `(begin form₁ … formN)`
(REPL explicit cluster), or a file's non-structural forms (batch). See
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

### ADT-entry builder — `AdtCtorSpec` + `build_adt_entries` (S110 R-2)

The ONE derivation of the symbol-table entry set an ADT registration produces
(`crates/cranelisp-types/src/adt_build.rs`; Principle 24 "Resolve once" —
instance R-2 of the registration-mirror class). Two writers previously
maintained the shape as a near-line-for-line mirror — typecheck
`adt.rs::register_type_def_with_ctor_infos` (user `deftype`) and int
`src/bootstrap.rs::register_synth_adt` (synthetic seeds: `Option`, `Pair`,
`Result`, `IO`, `SList`/`Sexp`, `Trace`) — and S109's canonical-key change had
to be hand-applied to BOTH (the `src/` audit R-2 finding). Now both are thin
callers.

```rust
/// One constructor of an ADT registration: caller-RESOLVED field types
/// (FieldInfo), pre-allocated got_slot (the builder is pure — slot
/// allocation is table state), ctor docstring, internal flag. Tag is
/// positional, assigned by build_adt_entries.
#[non_exhaustive]
pub struct AdtCtorSpec {
    pub name: Symbol,
    pub fields: Vec<FieldInfo>,
    pub docstring: Option<String>,
    pub internal: bool,
    pub got_slot: usize,
}
impl AdtCtorSpec { pub fn new(..) -> Self }

/// Pure: ADT description → ordered (key, entry) list.
pub fn build_adt_entries<C: CodeStore>(
    fqtn: &FQTypeName,
    type_params: &[Symbol],
    type_var_ids: &[TypeId],
    adt_docstring: Option<&str>,
    ctors: &[AdtCtorSpec],
    visibility: Visibility,
) -> Vec<(Symbol, ModuleEntry<C>)>
```

The builder owns: the product/sum split (S79 Option 3a — single ctor named as
the type ⇒ one dual-facet `Def` with `type_def: Some(..)`, no alias, no
`TypeDef`), ctor schemes (`forall vars. (Fn [fields] ADT)` / bare `ADT` for
nullary), the synthesised `DefnVariant` body wrapping `Expr::ConstrADT`,
canonical `member_key(Type, Ctor)` keying + the bare-name `Import` alias edge
per sum ctor (S109 dotted-ctor keying), the product docstring fallback, and
the `TypeDefInfo` computed ONCE. Callers keep: GOT-slot allocation (rides in
on the spec), insertion policy (bootstrap inserts verbatim; typecheck runs its
§8.6.5 contest classification on the returned `Import` alias pairs — the only
`Import` shape the builder emits, so structurally discriminable), the
recursive-field pre-seed, and product field-accessor synthesis
(typecheck-only). Ordering contract: per ctor in tag order, canonical `Def`
before its bare alias; sum `TypeDef` last — a sequential inserter preserves
as-built semantics. No serde-shape change (existing entry shapes only; no
`CACHE_SCHEMA_VERSION` impact). Caller wiring is the S110 Phase-5 coordinated
`/dev` change-set (`design/arch/backend-keyed-consumer.md` §6).

---

## Module System

### Symbol Table

```rust
/// Per-module symbol table. Pure data. Generic over the per-function code
/// store `C` and per-module linker store `L` per `pipeline-v4.md` §9.1.
///
/// Both `C` and `L` default to `()` so that crates that do not handle
/// compiled code (typecheck, frontend, the bulk of backend) work with
/// `SymbolTable` (i.e. `SymbolTable<(), ()>`) and never see the parameters
/// in their signatures. The integration layer instantiates
/// `SymbolTable<Code, Linker>` where `Code` and `Linker` are concrete types
/// chosen in `src/session_v4.rs`. See Decision 32 for the trait shape.
///
/// Structural declarations (`imports`, `exports`, `platforms`, `submodules`)
/// retain the *original specification* of the module's `(import …)` /
/// `(export …)` / `(platform …)` / `(mod …)` forms — the per-symbol
/// `ModuleEntry::Import` entries are the *resolved effects* of imports.
/// See Decision 33 (Step 5a). The `ModuleStructure` parallel store in
/// `src/save.rs` (Sprint-57 transitional shape) dissolves at Step 5a.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SymbolTable<C: CodeStore = (), L: LinkerStore = ()> {
    pub path: ModuleFullPath,
    pub symbols: HashMap<Symbol, ModuleEntry<C>>,

    // --- GOT (runtime memory for code pointers) ---
    /// Next available GOT slot index for this module (module-local).
    pub next_got_slot: usize,
    /// Per-module Global Offset Table. Created at module registration;
    /// base address stable for the module's lifetime. `Arc` for cheap
    /// codegen-worker handles.
    #[serde(skip, default = "default_got_arc")]
    pub got: std::sync::Arc<GotTable>,

    // --- Structural declarations (Step 5a; Decision 33) ---
    /// Original `(import [module [names...]])` declarations in source order.
    /// Used by `src/save.rs` for `.cl` regeneration (§6.4) and by the
    /// import-resolver. Cf. per-symbol `ModuleEntry::Import` entries which
    /// are the *resolved* effects.
    pub imports: Vec<ImportSpec>,
    /// Original `(export [names...])` declarations in source order.
    pub exports: Vec<ExportSpec>,
    /// Original `(platform "name")` declarations in source order.
    pub platforms: Vec<PlatformSpec>,
    /// Original `(mod child)` declarations in source order; `is_private`
    /// distinguishes `(mod- child)`.
    pub submodules: Vec<ModDecl>,

    // --- Cache schema version (Step 5b; Decision 34) ---
    /// Schema version of the serialised symbol table. Bumped on every
    /// shape-changing field addition / deletion / type change.
    /// Defaults to 0 on legacy caches (no field) → triggers cache-stale.
    #[serde(default)]
    pub schema_version: u32,

    // --- Cached object code (module-level .o loading) ---
    /// Mapped `.o` code for cache-hit modules. `#[serde(skip)]` — runtime
    /// state, re-derived on cache-hit load. `L = ()` for crates that don't
    /// handle linker state.
    #[serde(skip)]
    pub linker: Option<L>,
}

/// Empty marker trait for the per-function code store. Defined in
/// `cranelisp-types` so `SymbolTable` can be generic without pulling
/// Cranelift types into the contract surface (Decision 32).
///
/// `()` implements both `CodeStore` and `LinkerStore` via the blanket
/// `impl<T: Send + Sync + 'static>`. Concrete types live in the
/// integration layer or `cranelisp-backend` — methods that compile,
/// evict, or reclaim code go on those types, not on the trait.
pub trait CodeStore: Send + Sync + 'static {}
impl<T: Send + Sync + 'static> CodeStore for T {}

/// Empty marker trait for the per-module linker store. Same shape as
/// `CodeStore` but kept distinct so `SymbolTable<C, L>` has two
/// independent type parameters (per-function reclaim and per-module
/// reclaim are separate concerns; cache-restore can supply a `Linker`
/// without supplying a `Code` shape).
pub trait LinkerStore: Send + Sync + 'static {}
impl<T: Send + Sync + 'static> LinkerStore for T {}

fn default_got_arc() -> std::sync::Arc<GotTable> {
    std::sync::Arc::new(GotTable::new())
}

impl<C: CodeStore, L: LinkerStore> SymbolTable<C, L> {
    pub fn get(&self, name: &str) -> Option<&ModuleEntry<C>> { ... }
    pub fn insert(&mut self, name: Symbol, entry: ModuleEntry<C>) { ... }
    pub fn public_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry<C>)> { ... }
    pub fn allocate_got_slot(&mut self) -> usize { ... }
    pub fn defined_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry<C>)> { ... }
}
```

The Sprint-57 `ModuleStructure` struct in `src/save.rs` is **deleted** at Step 5a — its `import_specs` / `export_specs` / `mod_decls` / `platform_specs` fields move 1:1 to the corresponding `SymbolTable` fields above. `SharedState.module_structures: DashMap<ModuleFullPath, ModuleStructure>` dissolves; `src/save.rs::generate_module_source` reads from the `SymbolTable` it already holds. See Decision 33.

**`allocate_got_slot` becomes fallible — PINNED S111 Phase 3 (backend-audit R7: s107 R7 + s110 R7, 4th consecutive naming; release-mode UB today); lands early on the S111 backend-drain track.** As-built, `allocate_got_slot` (`module.rs:609`) is an unchecked monotone bump over a fixed `GOT_TABLE_SIZE = 1024` slot slab whose `store_slot`/`load_slot` only `debug_assert!` the bound — in release, slot 1024 is UB. One session-side guard exists (`src/redefine.rs::allocate_live_got_slot`, S101) but covers only the redefinition chokepoint; every other allocation path is unguarded. The pinned diff moves the check to the seam itself:

```rust
// crates/cranelisp-types/src/module.rs — beside the allocator
/// Module-local GOT exhaustion: `next_got_slot` reached `GOT_TABLE_SIZE`.
/// Constructed only by `allocate_got_slot`; callers map it into their own
/// error carrier (a located compile error — never a panic on user input).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct GotExhausted {
    /// The module whose GOT has no free slot.
    pub module: ModuleFullPath,
}
// + impl Display (names the module and GOT_TABLE_SIZE) + impl std::error::Error

pub fn allocate_got_slot(&mut self) -> Result<usize, GotExhausted> {
    if self.next_got_slot >= GOT_TABLE_SIZE {
        return Err(GotExhausted { module: self.path.clone() });
    }
    let slot = self.next_got_slot;
    self.next_got_slot += 1;
    Ok(slot)
}
```

`next_got_slot` is NOT bumped on failure — exhaustion is stable and repeatable. **Schema-INDEPENDENT, say it plainly: no serde shape or meaning changes (`next_got_slot: usize` untouched; `GotExhausted` is never persisted), so NO `CACHE_SCHEMA_VERSION` bump** — this change-set is deliberately decoupled from the schema-20 ownership wave and can land any time on the backend-drain track (S111 ordering constraint 3). Cascade: types `public-api.txt` (one changed signature line + the `GotExhausted` lines); typecheck/backend baselines unchanged (all callers internal). Caller census (verified 2026-07-17; **corrects the Phase-2 table, which missed `program/register.rs` ×2**, under-scoped the builtins bootstrap set, and mis-classed `extern_call.rs:151` as a production backend site — it is a `#[cfg(test)]` fixture):

- **typecheck, fallible → `CheckError` (10 production sites):** `adt.rs:173`, `adt.rs:614`, `traits/impl_check.rs:667`, `program/register.rs:376`, `program/register.rs:948`, `program/body.rs:278`, `program/body.rs:517`, `program/finalize.rs:233`, `program/finalize.rs:328`, `traits/monomorphise.rs:611`. **ONE typecheck-side mapping helper** (Principle 7 — a located compile error naming the module; variant choice is `/design`(typecheck)'s), never ten hand-rolled `map_err`s. The five `reuse.unwrap_or_else(|| st.allocate_got_slot())` shapes become `match reuse { Some(s) => s, None => helper(...)? }`.
- **typecheck, fresh-table bootstrap (3 sites, `unreachable!` convention):** `builtins.rs:694`, `builtins.rs:1021`, `builtins.rs:1098` — all seed a fresh primitives table; a fresh table cannot exhaust (`unreachable!("invariant: bootstrap seeding cannot exhaust a fresh GOT")`).
- **backend: ZERO production allocation sites** (verified S111 Phase 3, correcting BOTH the Phase-2 table and this census's first draft: `compiler/extern_call.rs:151` sits under `#[cfg(test)]` — a fixture). Allocation is entirely typecheck's + the bootstrap seeds; the backend only READS/WRITES already-allocated slots (`store_slot`, e.g. `lib.rs:994`) with indices carried on entries.
- **primitives, static bootstrap (2, `unreachable!` convention):** `lib.rs:230`, `lib.rs:348` — the statically-constructed primitives table.
- **int (3):** `src/redefine.rs:254` — the existing `allocate_live_got_slot` guard **collapses onto the `Result`** (delete the manual `next_got_slot >= GOT_TABLE_SIZE` pre-check; map `Err(GotExhausted)` into the existing `CranelispError::CodegenError` message, whose "restart the session to reclaim frozen slots" remedy text stays int-side); `src/bootstrap.rs:155` + `src/bootstrap.rs:773` — fresh synthetic-module tables, `unreachable!` convention.
- **test code (mechanical `.unwrap()`):** backend `got.rs` unit tests, backend `test_support.rs:938`, backend `compiler/extern_call.rs:151` (`#[cfg(test)]` fixture), `src/redefine.rs:1896` (`#[cfg(test)]`), types `module/tests.rs`.

**`store_slot`/`load_slot` backstop — RULED S111 Phase 3 (on the `/design`(backend) question; same change-set as the fallible allocator):** the bounds checks in `GotTable::store_slot`/`load_slot` (`got.rs:135/:146`) are promoted **`debug_assert!` → always-on `assert!`** — signatures UNCHANGED. With the allocation seam fallible, an out-of-bounds index in-process is an invariant breach (a compiler defect), and the honest Phase-H posture for an invariant breach is a located hard-fail, not release UB — `/design`(backend)'s "debug_assert is the wrong Phase-H final state" read is confirmed. The **`Result<_, CodegenError>`-shaped `store_slot` is REJECTED**: it would launder an invariant violation into a routine recoverable error and force a caller sweep with no user-reachable trigger (Principles 18/20; P6 budget). The check is per-definition-frequency (JIT-emitted code reads GOT memory via the base pointer, never through `load_slot`), so always-on costs nothing measurable. **The one genuine untrusted index source gets the diagnosed error instead: cache deserialization** — `.meta.json` `got_slot` values enter from disk unvalidated, and a corrupted/hand-edited cache is the only path to an out-of-range index once allocation is checked. The companion obligation (routed `/design`(backend), same R7 track): the cache-load seam validates each restored entry's `got_slot < GOT_TABLE_SIZE` and treats a violation as **cache-stale → recompile** (a diagnosed recovery, never a panic on disk content).

**Boundary-test obligation (types tier, `crates/cranelisp-types/src/module/tests.rs`):** 1024 consecutive allocations return `Ok(0)..=Ok(1023)`; the next call returns `Err(GotExhausted)` carrying the module path; `next_got_slot` is unchanged by the failure (a second call fails identically). Plus one session-surfaced caller test (e2e-or-unit — `/qa`'s row) proving exhaustion is a diagnosed error, not UB, on a real path. Currency sweep in the same change-set: the "UNCHECKED" prose at backend `got.rs:22–27`, the `src/worker.rs:419` doc-table row, and `src/redefine.rs:230–237` rustdoc all describe the pre-fix state and are updated. `GotTable`'s `debug_assert!` bounds checks stay as defence-in-depth. Sequence-diagram lockstep: `sequences/exec-flow-redefine.mmd:31` names the current infallible arrow (`SymbolTable::allocate_got_slot() -> fresh slot for f`) — the implementing change-set updates it to the `Result` shape and regenerates the `.svg` (`/arch` executes; the diagram is `/arch`-owned).

#### Two-GOT model — SymbolTable GOT vs `.o` data section GOT

Decision 23 (updated Sprint 58 Wave 2) records that every CLIF reference to `__cranelisp_got_{M}` resolves to a base address; the runtime memory the base addresses depends on the `Module` implementation used at finalize time. The two GOTs are distinct artefacts with different owners, lifetimes, mutability, and purposes — but they share the same name and the same per-slot semantics so that the backend can emit byte-identical CLIF in both modes.

| GOT | Backing | Owner / location | Lifetime | When read | Mutable? |
|---|---|---|---|---|---|
| **SymbolTable GOT** | `pub got: Arc<GotTable>` field on `SymbolTable` (above, line 870) — in-process memory | runtime / `cranelisp-types` | session — created at module registration, lives until session teardown | JIT (`--run`, REPL) — `JITBuilder::symbol_lookup_fn` (registered by the integration layer in `src/session_v4.rs`) returns `symbol_tables[M].got.base_ptr()` when Cranelift resolves the `Linkage::Import` data symbol at finalize | YES — REPL redefinition writes a new fn ptr into the existing slot via the Decision-31 atomic swap; the swap is the redefinition mechanism that makes existing callers see the new code |
| **`.o` data section GOT** | `Linkage::Export` data symbol named `__cranelisp_got_{M}` defined inside `M`'s own `.o`, with relocation initializers against the local function symbols (Decision 36) | object-file artefact emitted by `compile_to_module<ObjectModule>` | one per `.o` file on disk; in-memory only after `Linker::load_object` mmaps the `.o` | `--link` mode — system linker (`ld`) patches relocations against the defined data symbol when producing the executable; or our cache `Linker` in `--run`/REPL after cache-hit, when reading the `.o` to resolve cross-`.o` references | NO — initialised by the linker / loader once at load time, never mutated thereafter |

**Why two GOTs.** The SymbolTable GOT is for runtime — JIT calls index into it; REPL redefinition mutates it; it is the live store that user code reaches through. The `.o` data section GOT is for the on-disk artefact — the system linker in `--link` mode needs a defined data symbol to patch relocations against; without it, the system linker reports `__cranelisp_got_{M}` undefined (Bug B in `design/int/symbol-table-cache.md` §"Investigation findings"). The two are not stepping stones for each other — they serve different masters at different lifecycle phases.

**Same data symbol, different resolvers.** The CLIF emitted by `compile_to_module` declares `__cranelisp_got_{M}` as `Linkage::Import` from the caller's POV uniformly (the FnCompiler does not know which Module impl resolves it). The `.o` definition (`Linkage::Export`) appears only in the *defining* module's own `.o`, emitted via `compile_to_module<ObjectModule>`'s data-section emission step. JIT mode never reads the `.o` definition — `JITBuilder::symbol_lookup_fn` short-circuits the import resolution to the SymbolTable GOT base. `--link` mode never touches the SymbolTable GOT (the binary runs standalone and never instantiates a session).

**Mode dispatch is the Module impl, not the CLIF.** This is the canonical illustration of Principle 11 (single pipeline, mode parameters): one CLIF, two resolvers. Adding a third mode (e.g. AOT to a static archive) would add a third resolver behind a third Module impl — the CLIF would not change.

**Single-source GOT data-symbol name.** The `__cranelisp_got_{M}` naming scheme is produced by one function — `cranelisp_types::got_data_symbol_name(module_path) -> String` (`crates/cranelisp-types/src/module.rs`). It lives in `cranelisp-types` because **two** crates consume it: `cranelisp-backend` (emits the `Linkage::Import`/`Export` relocation symbol during codegen) and `int` (registers the SymbolTable-GOT slab base under this name for the JIT `symbol_lookup_fn`, the cache-hit `Linker::register_symbol`, and the `--link` startup `.o`). It was relocated DOWN from backend's former `pub(crate) compiler::got_data_symbol_name` at S76 (per the /arch S76 Phase 2 review) so the scheme is single-source rather than reached-into across the backend boundary or duplicated in int. It is pure string formatting over `ModuleFullPath`, a peer of `ensure_module_exists`.

Cross-references: Decision 23 (two-GOT framing); Decision 31 (the SymbolTable GOT slot is the redefinition atomic-swap target — the `--run` GOT MUST be mutable for redefinition to work); Decision 36 (function symbol naming + linkage policy — bare-Local is correct because the `.o` data section GOT's relocation initializers are intra-`.o`); Decision 37 (cache-hit codegen-phase order independence is established by the SymbolTable GOT slot LAYOUT being pinned at typecheck time).

### Module Entries

```rust
/// An entry in a module's symbol table.
///
/// Generic over `C: CodeStore` per the parameterised `SymbolTable<C, L>`
/// shape (Decision 32). `C` defaults to `()` so crates that don't handle
/// compiled code work with `ModuleEntry` (i.e. `ModuleEntry<()>`).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ModuleEntry<C: CodeStore = ()> {
    Def {
        scheme: Scheme,
        visibility: Visibility,
        docstring: Option<String>,
        param_names: Vec<Symbol>,
        kind: Box<DefKind>,
        /// Fully qualified callees, populated by finalize_check_result()
        /// from TC-sourced call graph edges. Used by scheduler for
        /// transitive macro dep discovery. See Decision 21.
        callees: Vec<FQSymbol>,
        /// Module-local GOT slot index — **single source of truth** for the
        /// entry's runtime call address (Sprint 56 Wave 0 §9.8 G7; reaffirmed
        /// Sprint 66 post-rollback per `1dc57ae`). Assigned at registration
        /// time for any **addressable callable** — user fns (JIT-built or
        /// linker-loaded), primitives (when used as values), and platform
        /// DLL fns. The address lives in `SymbolTable.got()` (a `GotTable`
        /// per module) and is read/written via
        /// `got().load_slot(slot)` / `got().store_slot(slot, ptr)`. No
        /// sibling `fn_ptr` / `platform_fn_ptr` / `primitive_fn_ptr` field
        /// exists — those workarounds were considered (Wave B
        /// `primitive_fn_ptr`; commit `b09ec76`'s unified `fn_ptr`) and
        /// rejected/rolled back as redundant with the GOT.
        ///
        /// `got_slot: None` indicates non-callable, non-addressable entries
        /// (special forms, `Overloaded` base entries, `TypeDef` /
        /// `TraitDecl` / `Macro`, constrained-fn templates, and
        /// `DefKind::PrimitiveExtern` host-promised externs — the key IS the
        /// ABI name a host promises at JIT-finalize via `Jit::define_symbol`;
        /// a call resolves `Linkage::Import`, never GOT-indirect).
        ///
        /// **S83 target (FIXME 0356/0357, Principle 20; amends Decision 35):**
        /// this flat field RELOCATES onto the callable `DefKind` variants
        /// (`UserFn` concrete-callable / `Primitive` / `Constructor`); the
        /// non-callable kinds carry no slot field, making `Def{slot}+template`
        /// unconstructable. The list of `None` cases above becomes the set of
        /// kinds with no slot field at all. See BC §7 "Callability is
        /// structural" + the callable-address paragraph above. (This
        /// illustrative block predates the reshape; the authoritative surface
        /// is BC §7 + `module.rs` source rustdoc.)
        got_slot: Option<usize>,
        /// Trait-method origin (Sprint 56 Decision 21). `Some(trait)` when
        /// this `Def` is a trait-method impl — replaces the
        /// `method_to_trait` reverse index on `TraitRegistry`. `None` for
        /// regular user functions.
        trait_origin: Option<FQTraitName>,
        /// Typechecked function body. Written by typecheck after
        /// `check_form(CheckBody)`, read by codegen. `None` for
        /// primitives, special forms, `Overloaded` base entries (their
        /// variants carry the bodies), constrained-fn templates (their
        /// mono specialisations carry the bodies), and pre-body-check
        /// entries. Authoritative per-category table:
        /// `design/typecheck/ast-annotation.md` §6. (Phase 1.)
        ast: Option<Defn>,
        /// Lifecycle owner for compiled code (Phase 3 Step 3b — G6;
        /// parameterised over `C` at Phase 5 Step 5c; **slimmed in Sprint 66
        /// — variants now carry lifecycle ownership only**).
        /// Written by the priority worker after `compile_to_module` returns
        /// (or by `load_object` on cache-hit). `None` until codegen completes,
        /// and `None` for entries whose lifecycle owner lives elsewhere
        /// (primitives — process-static `LazyLock<SymbolTable>` in
        /// `cranelisp-primitives`; platform DLL fns — DLL handle held in
        /// `SharedState.kept_dlls`). The integration layer chooses
        /// `C = Code` (re-exported from `cranelisp-backend`); the variants
        /// carry **lifecycle ownership only** — the call address lives in
        /// the per-module `GotTable` (the post-rollback single source of
        /// truth — see `got_slot` doc below and
        /// `crates/cranelisp-types/src/got.rs`), not inside the variant.
        ///
        /// **Variant shape post-Sprint 66 (slimmed)**:
        /// `Code::Jit(Arc<Jit>)` for JIT-built user fns;
        /// `Code::Linker(Arc<Linker>)` for cache-hit user fns. The previous
        /// `Code::Jit { jit, ptr }` / `Code::Linker { linker, ptr }` shapes
        /// are retired — the per-entry ptr is in the GOT (commit `b09ec76`
        /// briefly placed it on a sibling `fn_ptr` field; commit `1dc57ae`
        /// rolled that back as redundant with the GOT). The
        /// variant-uniform `Code::ptr()` accessor is retired with the
        /// embedded ptr; consumers read the address via
        /// `symbol_table.got().load_slot(entry.got_slot.unwrap())`.
        ///
        /// **Lifetime / reclaim (Decision 31, Scenario 2 — preserved
        /// post-S66)**: the `Arc<Jit>` *living directly on this field* is
        /// the reachability primitive that fires per-redefinition reclaim.
        /// While any entry holds an `Arc<Jit>` clone alive, the JIT's
        /// executable pages stay mapped. When every entry referencing the
        /// JIT is evicted or redefined, the Arc refcount reaches zero and
        /// the custom `Drop` on our `Jit` wrapper calls
        /// `unsafe JITModule::free_memory()` — this is the ONLY way to
        /// reclaim JIT pages in Cranelift 0.116 (the default drop path
        /// leaks on purpose; see archived `pipeline-v4.md` §9.4 for
        /// evidence). The safety invariant is maintained by: (a) the GOT
        /// slot's stored ptr becomes invalid the instant
        /// `JITModule::free_memory()` runs; (b) GOT slots are atomically
        /// swapped to new code before the old Arc can drop (Decision 41
        /// per-symbol JIT cardinality means redefine → new
        /// `Code::Jit(Arc<Jit>)` written to entry → old Arc clone drops
        /// as the entry is replaced); (c) user-returned `fn` values are
        /// heap closures calling through the GOT, not raw code pointers.
        ///
        /// **Pre-Phase-5 transitional shape (Sprint 57; superseded at
        /// Step 5c)**: `Arc<Jit>` lived in `SharedState.kept_jits` rather
        /// than directly on this field, because `SymbolTable<C, L>` was
        /// not yet activated. Per-redefinition reclaim therefore deferred
        /// to session teardown. Step 5c activates the generics and
        /// dissolves `kept_jits`.
        ///
        /// `#[serde(skip)]` — runtime state. Cache re-derives it from
        /// `ast` on cache-hit load (constructs `Code::Linker(Arc<Linker>)`
        /// per `load_object`). See Decision 25 (canonical placement)
        /// + Decision 31 (reclaim primitive; S66 amendment preserves
        /// semantics) + Decision 32 (`CodeStore` trait shape) + Decision
        /// 41 (per-symbol JIT cardinality + S66 amendment + rollback —
        /// call address lives in the GOT, not on a sibling field).
        #[serde(skip)]
        code: Option<C>,
        // Note: there is **no** `fn_ptr` / `platform_fn_ptr` /
        // `primitive_fn_ptr` field on `ModuleEntry::Def`. The S66 work
        // briefly added a unified `fn_ptr: Option<*const u8>` (commit
        // `b09ec76`) as the relocation target for the per-entry call
        // address removed from the `Code` variants; `1dc57ae` rolled
        // that back the same day after identifying it as redundant with
        // the per-module `GotTable`. The runtime call address lives at
        // `symbol_table.got().load_slot(slot)`, indexed by `got_slot`
        // (above). Origin (JIT / linker / primitive / platform DLL) is
        // encoded by `kind: DefKind`. See `got_slot` doc above and
        // `crates/cranelisp-types/src/got.rs`.
    },
    Import { source: FQSymbol },
    Reexport { source: FQSymbol },
    TypeDef {
        info: TypeDefInfo,
        visibility: Visibility,
        docstring: Option<String>,   // S72 Phase B — direct field; un-nested from TypeDefInfo
        // S79 Option 3a (FIXME 0319): `constructor_scheme: Option<Scheme>` RETIRED.
        // A single-ctor product type (type-name == ctor-name) no longer survives
        // as a TypeDef that smuggled the ctor's Scheme here; it survives as a
        // got-slotted ctor Def carrying a type facet
        // (DefKind::Constructor { type_def: Some(TypeDefInfo) }), and the ctor
        // scheme lives on that Def's own `scheme`. TypeDef entries are now only
        // ever the sum/enum case.
    },
    TraitDecl {
        info: TraitDeclInfo,         // S72 Phase B — slimmed payload; no longer embeds AST TraitDecl
        visibility: Visibility,
        docstring: Option<String>,   // S72 Phase B — direct field; un-nested from embedded decl
    },
    Constructor {
        type_name: Symbol,
        info: ConstructorInfo,
        scheme: Scheme,
        visibility: Visibility,
    },
    Macro {
        name: Symbol,
        clauses: Vec<MacroClauseInfo>,
        docstring: Option<String>,
        visibility: Visibility,
        sexp: Option<Sexp>,
        source: Option<String>,
        /// Fully qualified callees, populated by finalize_check_result()
        /// from TC-sourced call graph edges. Used by scheduler for
        /// transitive macro dep discovery. See Decision 21.
        callees: Vec<FQSymbol>,
    },
    PlatformDecl {
        dll_path: PathBuf,
        platform_module: ModuleFullPath,
    },
    /// A trait implementation — the DISCOVERY shell, keyed
    /// `impl$FQTypeName$FQTraitName` in the TRAIT's defining module
    /// (Decision 45 pattern (b), as amended S110 W0.1 — see narrative below).
    TraitImpl {
        trait_name: FQTraitName,
        impl_type: FQTypeName,
        /// The module whose table holds this impl's mangled method `Def`s and
        /// their GOT slots (the impl-writer's module) — the discovery→storage
        /// pointer. REQUIRED (no `#[serde(default)]`, Principles 18/20).
        impl_module: ModuleFullPath,
        /// Method names defined in this impl (local names, not mangled).
        methods: Vec<Symbol>,
        /// Always `Public` (spec §5.11.1); present for variant uniformity.
        visibility: Visibility,
    },
    Ambiguous,
}

impl ModuleEntry {
    pub fn is_public(&self) -> bool { ... }
}
```

**`ModuleEntry::type_def_info() -> Option<&TypeDefInfo>` — the single "answers as a type" reader (S109 Phase 3, additive).** A type name survives in the table as one of two shapes (S79 Option 3a dual facet): a `ModuleEntry::TypeDef` (sum/enum) or a got-slotted product ctor `Def` carrying `DefKind::Constructor { type_def: Some(..) }` (type-name == ctor-name). Every consumer that needs an entry *as a type* — resolution, arity/exhaustiveness checks, introspection, **persistence** — reads this accessor instead of matching `ModuleEntry::TypeDef` directly; a bare `TypeDef` match is exactly the FIXME-0573 defect class (int's `save.rs generate_types` skipped product `deftype`s from backing-file persistence — silent data loss). Follows the `callable_got_slot()` read-through precedent (one accessor, no per-site re-patterning of the kind set); `type_ctor_names` (heap.rs) is the ctor-name projection over the same two-shape switch. Delegating consumers land in the S109 Phase-5 waves: typecheck's `type_def_view_of` (checker.rs) reduces to it; `save.rs` type emission keys on it. Read-side only — **no serde/cache impact**; +1 `public-api.txt` line.

**`ModuleEntry::TraitImpl.impl_module` — the amended-D45 discovery→storage pointer (S110 W0.1b `144828d1`, landed; `design/arch/backend-keyed-consumer.md` §1.1.1; amends `design/arch/decisions/0045-traitimpl-storage-in-trait-defining-module.md`).** An `(impl Trait Type …)` form written in module M splits across two placements. The `TraitImpl` **shell — the discovery record — lands in the TRAIT's defining module** (D45 pattern (b): importers chain-follow the trait reference back to its home and probe `impl$FQTypeName$FQTraitName` in O(1) — no closure walk, no cycle detection). The **mangled method `Def`s — the compilation record (`Trait.method$m/Type`) — land in M**, the impl-writer's module. This split is structurally forced, which is why D45's original method-co-location clause ("the method entries live in the same module that holds the `TraitImpl` entry") is AMENDED rather than the bodies moved: the bodies compile in M's codegen batch, and `compile_to_module` requires every compiled defn's entry + GOT slot in the compiling module's OWN table (relocating them would also push per-impl GOT-slot writes into shared tables — the 0604 write-race surface). `impl_module` is the pointer from the discovery record to the storage module, written from `state.current_module` at shell construction (`impl_check.rs`), so trait-method dispatch derives the selected entry's true home with one keyed probe — never a scan, never `current_module` (this resolves the callees.rs "Step 5" pending note and repairs the S101 session-transaction reverse index for cross-module trait calls). Its consumer twin is `ResolvedCall::TraitMethod.impl_module` (§Method Resolutions above), populated from this shell at resolution time. REQUIRED field — a defaulted `""` module is a representable-invalid state (Principle 20), and construction sites are forced to supply it (Principle 18). Landed inside the schema-19 window — no new `CACHE_SCHEMA_VERSION` bump. Per-field authority: the `module.rs` variant rustdoc.

### Definition Classification

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DefKind {
    /// A built-in primitive bundled in `cranelisp-primitives`. Payload-free
    /// unit variant (S69 Submission 36 retired the prior
    /// `Primitive { primitive_kind, jit_name }` payload). The discriminator
    /// alone signals "bundled compiler-provided body". The JIT linker name IS
    /// the symbol-table key uniformly (`src/CLAUDE.md` §"JIT Symbol Names");
    /// inline-eligibility is encoded per-call-site in
    /// `ResolvedCall::BuiltinFn { name }` (set by typecheck), not on this
    /// discriminator.
    Primitive,
    /// A DLL-routed platform effect. Promoted from a sub-variant of the
    /// retired `PrimitiveKind` to a `DefKind` sibling (S69 Submission 36).
    /// `scheduling_class` is a variant field (not a sibling on
    /// `ModuleEntry::Def`) so that only entries that actually carry a
    /// scheduling class can have one — see Decision 26. Written during
    /// `(platform ...)` form processing from the DLL manifest; read by
    /// `bind_chain_analysis.rs::classify_expr` via an Import-chain walk.
    PlatformEffect {
        scheduling_class: cranelisp_platform::SchedulingClass,
    },
    /// A host-promised extern primitive (test-discovery design, 2026-06-06).
    /// Payload-free unit variant — a `primitives`-module callable whose body
    /// lives in the integration layer (`int`) and is promised at JIT-finalize
    /// via `Jit::define_symbol`, not bundled (`Primitive`) or DLL-loaded
    /// (`PlatformEffect`). The symbol-table key IS the ABI name; `got_slot:
    /// None`, `code: None`; a call lowers `Linkage::Import` against the key
    /// (the `PlatformEffect` import shape) and is structurally untraceable.
    /// Motivating member: `discover-tests` (its body reads int's live session
    /// state — which `cranelisp-intrinsics` cannot, per Principle 18 / D0048).
    /// `PlatformEffect` is the direct structural precedent. See
    /// `bounded-contexts.md` §7 + `design/arch/test-discovery.md` §6/§7.
    PrimitiveExtern,
    UserFn {
        constrained_fn: Option<ConstrainedFn>,
    },
    Overloaded {
        variants: Vec<OverloadVariant>,
    },
    /// An ADT constructor. `type_def` is the **product-type dual facet**
    /// (S79 Option 3a, FIXME 0319): `Some(Box<TypeDefInfo>)` iff this ctor IS
    /// its own type (single-ctor product, type-name == ctor-name) — the entry
    /// answers both as a got-slotted ctor `Def` AND as its type; `None` for
    /// ordinary sum/enum ctors whose type is a separate `ModuleEntry::TypeDef`.
    /// Field names live on the Def's `param_names`, NOT in `TypeDefInfo`
    /// (single source, Principle 7). Replaces the retired
    /// `ModuleEntry::TypeDef.constructor_scheme` smuggling field.
    Constructor {
        type_name: FQTypeName,
        tag: usize,
        field_count: usize,
        internal: bool,
        type_def: Option<Box<TypeDefInfo>>,
    },
    Macro {
        clauses_meta: Vec<MacroClauseInfo>,
    },
    // SpecialForm retired from DefKind (S69 Submission 36) — promoted to its
    // own `ModuleEntry::SpecialForm` variant. PrimitiveKind enum retired
    // entirely (Inline/Extern were vestigial; PlatformEffect promoted to the
    // DefKind sibling above).
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OverloadVariant {
    pub param_types: Vec<Type>,
    pub ret_type: Type,
    pub mangled_name: Symbol,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstrainedFn {
    // S70 narrowing: `defn: Defn` → `variant: DefnVariant` (symmetry with
    // `ModuleEntry::Def.ast`; the outer `Defn` metadata is canonical on the
    // parent `Def`). Single-variant ALWAYS — since S112 (multi-sig ×
    // constrained SUPPORTED) each constrained clause is its OWN one-variant
    // template referenced from `OverloadVariant.mangled_name`; dispatch
    // routes on the referenced entry's kind. Canonical statement: the
    // `ConstrainedFn` rustdoc in `module.rs` + monomorphisation.md §11.4.
    pub variant: DefnVariant,
    pub scheme: Scheme,
}
```

### Backend-hosted `Code` Enum (in `cranelisp-backend`)

The integration layer's concrete `C` for `SymbolTable<C, L>` is the `Code`
enum defined below. **Lives in `cranelisp-backend/src/code.rs` per
Decision 41 (Sprint 64 — Layer 2 Option B retracts in the sense that
backend *names* `Code` in its own signatures).** Originally placed in
`src/code.rs` per Decision 35; the move to backend keeps `cranelisp-types
→ cranelisp-backend` forbidden (the dep direction Principle 3 protects),
hosting `Code` where its variants' backend types (`Jit`, `Linker`) live.
**Backend does NOT *construct* `Code` (S75 W2 Finding-A correction):**
`compile_to_module<M>` only borrows `&mut M` and never owns the `Arc<Jit>`,
so it cannot build `Code::Jit`; the integration layer composes both
variants — `Code::Jit` from the `Arc<Jit>` it owns after the call,
`Code::Linker` from the `LinkerArtefact` `load_object` returns — and
installs them via Decision 38's `write_code(&self, …)`. Backend's own
write is the GOT slot (`got().store_slot`); the `write_code` call is the
caller's. The integration layer names `Code` at the session boundary's
`SymbolTable<Code, ()>` instantiation, re-exporting from backend. See
`bounded-contexts.md` §3 (backend — invariant 3 + "Who composes `Code`")
and the `crates/cranelisp-backend/src/{code,lib}.rs` rustdoc for the
authoritative statement (`facades/backend.md` retired S75 W5b → BC §3 +
source rustdoc).

```rust
// crates/cranelisp-backend/src/code.rs; owned by /backend.
//
// Concrete `C: CodeStore` for SymbolTable<Code, ()>. Carries lifecycle
// ownership only — the per-entry call address lives on the sibling
// the per-module `GotTable` (S66 fn_ptr unification → rollback `1dc57ae`,
// 2026-05-09 — GOT is the single source of truth for callable addresses).
//
// See Decisions 35 (original location + L=() choice + mixed-lineage
// modules) + 41 (S64 location move + direct-write pattern; S66
// amendment slimming the variants).
#[non_exhaustive]
pub enum Code {
    Jit(Arc<Jit>),
    Linker(Arc<Linker>),
}

// SAFETY: lifecycle owners are Send + Sync via Arc; no raw pointers
// inside the variants post-S66.
```

**S66 amendment — variant slimming + GOT-as-single-source-of-truth (2026-05-09)**. The previous variant shapes `Code::Jit { jit, ptr }` and `Code::Linker { linker, ptr }` retire. The variants are now tuple-shaped, carrying lifecycle ownership only.

Two-step history of the per-entry ptr:

1. **`b09ec76` (S66 Wave 0):** the per-entry ptr was relocated to a unified `fn_ptr: Option<*const u8>` field on `ModuleEntry::Def` (subsuming the previously-separate `platform_fn_ptr`; superseding the briefly-planned `primitive_fn_ptr`).
2. **`1dc57ae` (same day, rollback):** the unified `fn_ptr` field was removed once /arch identified that it duplicated state already in the per-module `GotTable` — every callable entry already had a `got_slot`, and JIT-emitted code reads addresses from `got_base + slot * 8`. Stashing the same address on a sibling field was a Principle 7 violation.

**Canonical post-rollback statement.** GOT is the single source of truth for callable addresses. The variant-uniform `Code::ptr()` accessor retires with the embedded ptr; consumers read the address via `symbol_table.got().load_slot(entry.got_slot.unwrap())`. Decision 31 Scenario 2 reclaim semantics are preserved (lifecycle ownership stays inside `Code::Jit(Arc<Jit>)`; `Drop` chain unchanged; the GOT slot's stored ptr becomes invalid the instant `JITModule::free_memory()` runs). See `crates/cranelisp-types/src/module.rs` `ModuleEntry::Def.got_slot` rustdoc + `bounded-contexts.md` §7 + `bounded-contexts.md` §3 (backend — invariant 3) + the `crates/cranelisp-backend/src/code.rs` rustdoc for the authoritative shape (`facades/backend.md` retired S75 W5b → BC §3 + source rustdoc), and Decision 41's "S66 amendment + rollback" for the amendment record.

The session boundary types in `src/session_v4.rs` instantiate
`SymbolTable<Code, ()>` and `ModuleEntry<Code>`; backend signatures
continue to read `SymbolTable` (i.e. `SymbolTable<(), ()>`) per Decision
32 and `compile-to-module.md` §17.

Per Decision 41 (S66 amendment + rollback; S70 Phase B amendment; S75 W2 Finding-A correction), `compile_to_module<M: Module>` writes the resulting fn pointer **to the entry's GOT slot** via `symbol_table.got().store_slot(entry.got_slot.unwrap(), ptr)` (D41 #2) and returns the always-created introspection by value as `Result<CompilationArtifacts, CompilationError>`. It does **not** construct `Code`: the **caller** composes `Code::Jit(Arc<Jit>)` (from the `Arc<Jit>` it owns after the call — backend only borrows `&mut M`) and `Code::Linker(Arc<Linker>)` (from the `LinkerArtefact`) and installs it via `SymbolTable::write_code(&self, sym, code)` (Decision 38's interior-mutable signature; the call is the caller's, not backend's). There is no paired `fn_ptr`-field write — the GOT is the single source of truth for callable addresses. The historical CP1 Layer-2 Option-B return-tuple shape (`compile_to_module` returning `(Arc<Jit>, HashMap<Symbol, *const u8>)` for the integration layer to wrap into `Code::Jit { jit, ptr }`) is retracted by Decision 41. See `bounded-contexts.md` §3 (backend — invariant 3 + "Who composes `Code`") + the `crates/cranelisp-backend/src/lib.rs` rustdoc for the authoritative shape (`facades/backend.md` retired S75 W5b → BC §3 + source rustdoc).

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

---

## Resolution primitive — `resolve` / `resolve_macro_head` (S76 W-Macro fold-in)

> **S108 Wave G**: the free-fn entry points below are the landed S76/S81 state.
> The approved target reshapes them onto `ResolutionScope` — one lookup with
> the prelude fallback intrinsic, no public fallback-less entry point — per
> §"`ResolutionScope`" below and `design/arch/prelude-import-convergence.md`.
> `Resolved`, `ResolveError`, and everything in this section about the
> view-vs-primitive line, the Principle-16 split guards, and
> `substitute_module_alias` carries over unchanged.

```rust
// crates/cranelisp-types/src/resolve.rs
#[non_exhaustive]
pub struct Resolved<C: CodeStore = ()> {
    pub entry: ModuleEntry<C>,
    pub home: ModuleFullPath,
    pub fq: FQSymbol,          // reference identity: home + canonical WRITTEN spelling
    pub storage_key: Symbol,   // storage identity: the terminal table key (S110 W1.1, FIXME 0620)
}
impl<C: CodeStore> Resolved<C> {
    pub fn storage_fq(&self) -> FQSymbol;   // { home, storage_key } — the keyed-consumer carrier value
}

pub fn resolve<C, L>(
    symbol_tables: &SymbolTables<C, L>,
    module_aliases: &ModuleAliases,
    first_hop: &View<'_, C, L>,        // caller-chosen current-module view
    current_module: &ModuleFullPath,
    name: &str,
    span: Span,
) -> Result<Resolved<C>, ResolveError>;

pub fn resolve_macro_head<C, L>(
    symbol_tables: &SymbolTables<C, L>,
    module_aliases: &ModuleAliases,
    first_hop: &View<'_, C, L>,
    current_module: &ModuleFullPath,
    name: &str,
    span: Span,
) -> Result<Option<FQSymbol>, ResolveError>;   // Ok(None) = head is not a macro

#[non_exhaustive]
pub enum ResolveError {
    TraitNotFound { name, from_module, span },
    TypeNotFound { name, from_module, span },
    ConstructorNotFound { name, from_module, span },
    QualifiedModuleUnknown { module, name, span },
    PrivateInaccessible { name, defining_module, from_module, visibility_found, span },
}
```

**The two identities on `Resolved` (S110 W1.1, FIXME 0620).** `fq` is the *reference* identity — `home` + the canonical **written** spelling — consumed by display, error attribution, macro-head dispatch, §8.6.4 remedies, and `callees`. It does NOT in general address the entry: across a member alias (`v` → `Box.v`, `Pure` → `IO.Pure`), a renamed import/export (`[(foo bar)]`), or a renaming re-export, the written spelling is an `Import`-edge alias, not the table key. `storage_key` / `storage_fq()` is the *storage* identity — the exact key the chain-follow terminated at, captured by the walk itself (the only actor that knows it; a `ModuleEntry` does not carry its own key). Keyed consumers — the `var_refs`/`apply_refs` carrier (`VarRef::Global` / `ApplyRef::Dispatch` values) feeding the backend's `entry_at` direct read (`design/arch/backend-keyed-consumer.md` §1.1) — record `storage_fq()`, never `fq`. Composing a storage identity from a written spelling is the 0620 defect class.

The single types-owned query that turns a name into a resolved symbol-table entry — following imports/reexports, §8.6.6 module-path aliases, visibility, and Principle-17 chain-following. **Resolving a name is a query over the symbol-table data structure** (no inference, no unification, no substitution), so by Principle 15 (behaviour lives with the type) and Principle 7 (single source) it belongs in `cranelisp-types`, extending the `ensure_module_exists` + `got_data_symbol_name` + chain-follow precedent. It is pure over `symbol_tables` + `module_aliases` (both types-owned), generic over `<C, L>`, and carries **no `CheckState`** — which is what keeps it in the data-only crate.

**The primitive-vs-view line.** The *search primitive* is types-owned: "in this table set, resolve `name` from `current_module` following imports/aliases/visibility/chain." The *choice of which view to search stays with the caller*, supplied as the first-hop `View` over the current module:

- **int's Pass-1 macro recognition** searches the **committed** tables — `View::single(live)` over the live current module. No staging exists during Pass 1 (the expand phase precedes `check_forms`).
- **typecheck's Pass-2/3 body resolution** searches the **staging ∪ live union** — its `SymbolTableAccess` hands a `View::union(staging, live)`.

Same primitive, different first-hop view. Cross-module hops (chain-following an `Import` edge, or the alias-resolved FQ target) always land in *other, already-committed* modules — staging only ever holds the *current* cluster's module (Principle 17 + Decision 44) — so the view parameterises only the entry point, not the whole walk.

**Consolidation (retires two scattered copies).** `resolve_macro_head` replaces int's `SymbolTableMacroResolver::resolve_macro` chain-walk (`src/worker.rs`) — recognition is now a `cranelisp-types` query with **zero int→typecheck dependency**. typecheck's `resolve_trait` / `resolve_type` / `resolve_constructor` / `resolve_qualified` family (`crates/cranelisp-typecheck/src/checker.rs`, S72) becomes a set of thin callers of `resolve`, each projecting the generic `Resolved` / `ResolveError` to its kind-specific success/error. `ResolveError` moved here with the primitive (it was typecheck-local only because the resolver was); its `From<ResolveError> for CheckError` projection stays in `cranelisp-typecheck` because `CheckError` is typecheck-owned (the types-side projection target is the neutral `CranelispError`). **No DAG impact** — `cranelisp-types` has no dependencies; the primitive adds none.

Per Principle 6 (minimum surface), there is one general primitive (`resolve`) plus thin typed wrappers (`resolve_macro_head` is the first; typecheck's `resolve_*` family are the rest, kept crate-side as projections). See `bounded-contexts.md` §7 (types — the resolution-primitive responsibility), §2 (typecheck — caller), §6 (int — Pass-1 recognition via the primitive).

**`substitute_module_alias` is also public (S81 W-G item 0303, Principle 7).** The §8.6.6 step-5 longest-prefix dot-segment module-alias substitution — used internally by `resolve_qualified` — is promoted to `pub fn substitute_module_alias(module_aliases: &ModuleAliases, module_path: &ModuleFullPath) -> ModuleFullPath` because int's FQ-autoload boundary (`SymbolTableMacroResolver::recognize`, `src/process_form.rs`) computes the dependency module to load from a raw `mod/sym` reference *before* typecheck runs, so it must apply the same alias resolution. It now calls this primitive directly; the former byte-identical int-side `resolve_module_alias` re-implementation (which aged independently — two copies of the same §8.6.6 walk) is deleted. Baseline delta: **+1 line** (`pub fn substitute_module_alias`), additive/non-breaking.

**Qualified-split guard — a bare `/` operator is not a qualified name (S81 / FIXME 0331, ratified).** The two private split helpers inside `resolve.rs` — `split_qualified(name)` (resolve.rs:493, the `module/symbol` splitter) and `canonical_symbol(name)` (resolve.rs:591, the post-last-`/` local-symbol extractor) — both require a **non-empty remainder** before splitting on `/`. `split_qualified` filters `split_once('/')` on `!m.is_empty() && !s.is_empty()`; `canonical_symbol` filters `rsplit_once('/')` on a non-empty symbol part. A name whose split would yield an empty part — a bare punctuation operator (`/`, `//`) or a leading/trailing `foo/` / `/bar` — is treated as a literal bare name routed to the unqualified short-name path, never to `resolve_qualified` against an empty root module. This is the structural realization of **Principle 16** (a bare punctuation operator is not special) at the resolution layer: `/` resolves identically to `+` or any other operator. The guard fixes the FIXME-0328 regression (the `resolve_with_fallback` migration made bare `/` resolve as "undefined variable: /") and matches pre-S81-migration literal-lookup behaviour; both helpers are PRIVATE (`fn`, not `pub`) so the fix carries **zero `public-api.txt` delta** (verified — not present in the baseline; `public_api_relocations` passes unchanged).

### `ResolutionScope` — the one lookup, prelude fallback intrinsic (S108 Wave G; supersedes the S81 `resolve_with_fallback` shape)

> **Ruling home: `design/arch/prelude-import-convergence.md`.** This section is
> the facade-side record of the approved `cranelisp-types` surface (the crate
> has no `facades/{crate}.md`). The S81 free-fn `resolve_with_fallback` shape
> that previously occupied this section (landed FIXME 0316c) is superseded:
> per-call opt-in fallback (`fallback_on: bool` threaded at every site) proved
> forgettable — the S108 matrix (`tests/plan/PLAN.md` §"Prelude ≡ explicit
> import") found six `_or_prelude` variants and four RED silent-accept/skip
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
  gate). Unit pins: `resolve/tests.rs::scope_i1_filter_gates_on_prelude_head_
  not_terminal` (+ the public-reexport-edge complement). Internal walk body
  only — **zero `public-api.txt` delta, no cache impact**.
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
  cycle reads as a not-found miss, never a stack overflow. Pin:
  `resolve/tests.rs::same_module_alias_cycle_is_a_miss_not_a_stack_overflow`.

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

**R5 value-representation flattening — the single-sourced Copy/value-layout predicate (S103 Wave 1; `design/arch/ownership-inference.md` §6.3, `design/backend/ownership-codegen.md` §7.1).** Increment II's one genuinely-new cross-crate edge, landing beside `HeapHeader` in `crates/cranelisp-types/src/heap.rs` with a `CACHE_SCHEMA_VERSION` bump 14 → 15 (representation change; wholesale-invalidates every pre-R5 `.o` via the manifest `cache_format_version` global key).

```rust
pub const VALUE_LAYOUT_MAX_WORDS: usize = 1;      // one word (8 bytes), first landing (§7.2)

#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ValueLayout { pub words: usize }        // the classification result (a HeapCategory analogue — recomputed, not persisted)

pub fn value_layout<C, L>(
    ty: &ConcreteType,
    type_defs: Option<&SymbolTables<C, L>>,          // the same view HeapCategory::classify takes
) -> Option<ValueLayout>
where C: CodeStore, L: LinkerStore;
```

`Some(ValueLayout { words })` ⟺ **Copy-eligible** (a scalar, or a single-constructor ADT whose fields are all transitively value-eligible) **∧** the fully-flattened representation is `≤ VALUE_LAYOUT_MAX_WORDS` words; `None` ⟺ today's heap/scalar representation verbatim. **Soundness-coupled single-sourcing (Principle 7, resolving FIXME 0468):** typecheck's `Copy` mode classifier and the backend's `HeapCategory::Value` arm are two consumers that MUST agree — a param moded `Copy` whose representation the backend did *not* flatten is a pointer bit-copied with no `rc_inc` (a missing-inc UAF) — so ONE predicate lives here and both delegate; neither derives its own. **Monotone-sound conservatism** (first landing): `None` is always sound (keeps today's lowering), so multi-constructor ADTs, `Vec`/heap collections, and generic ctor fields whose stored scheme type is not already concrete (no per-instantiation substitution) all return `None`. The `HeapCategory::Value` consuming arm + the F2v single-ctor witness are the Wave-3 backend work; the carrier lands with the mechanism, never ahead (Principle 8) — Wave 1 is carrier + tests only.

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
```

No changes from v1.

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

Both the priority worker in `src/` (preparing `names` for a `compile_to_module` call) and the backend's internal compile loop (when it re-enumerates) consume the same predicate. Defining it on `SymbolTable` ensures they cannot diverge (Principle 7 — single source of truth). See Key Decision 22 and `design/typecheck/ast-annotation.md` §9.5.

```rust
impl SymbolTable {
    /// Iterate over codegen-compilable entries: those with `ast: Some(_)`
    /// whose kind is NOT `Overloaded` (dispatch index — its mangled
    /// variants are compiled instead) and NOT `UserFn { constrained_fn:
    /// Some(_) }` (template — mono specializations are compiled instead).
    ///
    /// Canonical location: `crates/cranelisp-types/src/module.rs`.
    /// Consumed by:
    /// - Priority worker in `/int`: collects `names` for `compile_to_module`.
    /// - `compile_to_module` in `/backend`: internal compile loop.
    /// - `constrained_fn_names` derivations: negation of the second filter
    ///   clause within `UserFn`.
    pub fn defined_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry)> {
        self.symbols.iter().filter(|(_, entry)| match entry {
            ModuleEntry::Def { ast: Some(_), kind, .. } => match kind.as_ref() {
                DefKind::Overloaded { .. } => false,
                DefKind::UserFn { constrained_fn: Some(_) } => false,
                _ => true,
            },
            _ => false,
        })
    }
}
```

The filter is deliberately strict: any `ModuleEntry::Def` with `ast: None` is excluded — whether pre-body-check, primitive, special form, `Overloaded` base, or constrained-fn template. Adding new non-compilable categories never silently breaks codegen, because the `ast.is_some()` clause comes first.

> Note on `ModuleEntry::Def.ast` / `code` / `got_slot`: the full set of typecheck- and codegen-populated fields on `ModuleEntry::Def` (`ast`, `code`, `got_slot`, `callees`, `trait_origin`) is now shown in the variant definition above. `ast` arrived in Sprint 55 (Phase 1); `code` shape landed in Sprint 57 Phase 3 G6 (concrete `Code` placeholder); the previously-separate `platform_fn_ptr` landed in Sprint 57 Phase 4 G8 (later removed in S66 — see below); `code` is parameterised to `Option<C>` in Sprint 58 Phase 5 Step 5c (G12) per Decision 32 — the integration layer chooses the concrete `C = Code` (re-exported from `cranelisp-backend` per Decision 41) so per-redefinition reclaim fires (Decision 31 Scenario 2). **Sprint 66 (2026-05-09 — fn_ptr unification + rollback)** worked in two steps: (1) commit `b09ec76` removed `platform_fn_ptr` and added a unified `fn_ptr: Option<*const u8>` covering all four ptr origins (JIT user fn, linker-loaded user fn, primitive, platform DLL fn); (2) commit `1dc57ae` (same day) **rolled back** the unified `fn_ptr` field as redundant with the per-module `GotTable` already in place. Post-rollback canonical statement: **GOT is the single source of truth for callable addresses** — `got_slot: Some(slot)` indexes into `SymbolTable.got()` (a `GotTable` per module — `crates/cranelisp-types/src/got.rs`); the runtime address lives at `symbol_table.got().load_slot(slot)`. The `Code` variant slim survived the rollback: `Code` carries only the two lifecycle-owning variants `Code::Jit(Arc<Jit>)` / `Code::Linker(Arc<Linker>)`. (A `Code::Primitive` marker variant was briefly added in S68 Phase 3 per Decision 0048 A2, then **reversed in S73 Phase 2 per FIXME 0244** — primitive-ness is read from `kind: DefKind::Primitive`, not from a `code` marker.) The `code` field is `#[serde(skip)]` — runtime-only, re-derivable from the AST + cache `.o` (constructs `Code::Linker(Arc<Linker>)` per `load_object` for user fns; primitives have process lifetime and carry `code = None` — the GOT holds the `*const u8`; platform DLL fns are also `code = None`, DLL handle held in `SharedState.kept_dlls`). See `design/typecheck/ast-annotation.md` §6 for the authoritative per-category table of which entries carry `ast: Some(_)`, and `crates/cranelisp-types/src/module.rs` `ModuleEntry::Def` rustdoc for the canonical post-rollback field shape.

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
- `CallGraph`, `CallEdge`, `CallInfo` — transient within-module call graph (rich, with tail-position/span)
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
- `CodeStore` + `LinkerStore` empty marker traits (Sprint 58 Step 5c, Decision 32) — generic boundary on `SymbolTable<C, L>` and `ModuleEntry<C>`. Both default to `()`. See `pipeline-v4.md` §9.1.
- `SymbolTable.imports`, `.exports`, `.platforms`, `.submodules` (Sprint 58 Step 5a, Decision 33) — structural declarations as fields, not a parallel store. Reuse existing `cranelisp-types::{ImportSpec, ExportSpec, PlatformSpec, ModDecl}`.
- `SymbolTable.linker: Option<L>` (Sprint 58 Step 5c) — per-module linker store for cache-hit `.o` mapping. `#[serde(skip)]`.
- `SymbolTable.schema_version: u32` (Sprint 58 Step 5b, Decision 34) — explicit cache schema version; mismatch invalidates the cache as if dependencies changed.
- `Code` enum (Sprint 58 Phase 3a, Decision 35; Sprint 64 location move per Decision 41; **Sprint 66 variant slimming preserved through the same-day fn_ptr-unification rollback**) — concrete `C` for `SymbolTable<Code, ()>`. Variants `Code::Jit(Arc<Jit>)` + `Code::Linker(Arc<Linker>)` — lifecycle owner ONLY post-S66; the per-entry call address lives in `SymbolTable.got()` (the post-rollback single source of truth — see `crates/cranelisp-types/src/got.rs`), indexed by `ModuleEntry::Def.got_slot`. Lives in `cranelisp-backend/src/code.rs` (moved from `src/code.rs` per Decision 41), NOT in `cranelisp-types` (Principle 3). The CP1 Layer-2-Option-B return-tuple pattern retracts: `compile_to_module` writes the resulting fn pointer to the entry's GOT slot via `symbol_table.got().store_slot(slot, ptr)` (D41 #2) and returns `Result<CompilationArtifacts, CompilationError>` (S70 Phase B). The **caller** composes `Code::Jit(Arc<Jit>)` / `Code::Linker(Arc<Linker>)` and installs it via Decision 38's `write_code` (D41 #1 — the caller's, not backend's, per S75 W2 Finding-A; backend only borrows `&mut M`). Documented at this boundary so every consumer of `SymbolTable<Code, ()>` references the same shape.
- `ModuleEntry::Def.got_slot: Option<usize>` — single source of truth for "where to call to invoke this entry" (Sprint 56 G7; reaffirmed Sprint 66 post-rollback per `1dc57ae`). Indexes into `SymbolTable.got()`; the runtime address is `got().load_slot(slot)`. The S66 unification briefly placed the address on a sibling `ModuleEntry::Def.fn_ptr` field (commit `b09ec76`); the same-day rollback `1dc57ae` removed that field as redundant with the GOT. No per-entry pointer field exists post-rollback. Origin encoded by `kind: DefKind` (UserFn → JIT/linker; Primitive { Inline | Extern } → primitive; Primitive { PlatformEffect } → platform DLL). See `crates/cranelisp-types/src/module.rs` `ModuleEntry::Def.got_slot` rustdoc + Decision 41 S66 amendment + rollback.
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
- `compile_to_module<M: Module>(scope, names, symbol_tables, module_aliases, module)` — normative signature (Sprint 56 Phase 2; `module_aliases` added S75 W2). No `CheckResult`, no `Program`, no intrinsic IDs, no GOT map, no arities parameter. **Per Decision 41 (Sprint 64) + S66 amendment + rollback + S70 Phase B amendment + S75 W2 Finding-A correction**: returns `Result<CompilationArtifacts, CompilationError>`; backend writes the resulting fn pointer to the entry's GOT slot via `symbol_table.got().store_slot(entry.got_slot.unwrap(), ptr)` directly (D41 #2 — the GOT is the post-rollback single source of truth for callable addresses; the briefly-considered sibling `fn_ptr` field landed in `b09ec76` and was rolled back the same day in `1dc57ae`). The **caller** composes `Code::Jit(Arc<Jit>)` / `Code::Linker(Arc<Linker>)` and installs it via `SymbolTable::write_code` (D41 #1 — the caller's; backend only borrows `&mut M`, never owns the `Arc<Jit>`). On-demand disassembly is the separate `produce_disasm(fq, code_size, symbol_tables)` (caller-supplied `code_size` + capstone; S75 W2 Finding-C). See `bounded-contexts.md` §3 (backend) + the `crates/cranelisp-backend/src/lib.rs` rustdoc (`facades/backend.md` retired S75 W5b → BC §3 + source rustdoc) and `design/backend/compile-to-module.md`.
- `cranelisp_frontend::build_form(sexp: &Sexp) -> Result<Vec<ParsedEntry>, CranelispError>` (Sprint 66, FIXME 0156) — replaces the prior `build_ast` shape at the frontend's per-form boundary. Returns a `Vec` because some shapes yield more than one entry per source form (multi-clause `defmacro`, `deftype` with constructors). See `crates/cranelisp-frontend/src/lib.rs` //! preamble (post-S70 B3-C the frontend canonical surface contract).
- `cranelisp_typecheck::check_form` collapses to a **single `check_forms` free function** (Sprint 66, FIXME 0160 + Decision 44 amended FIXME 0167 + 2026-05-13 third amendment): `check_forms(parsed: Vec<ParsedEntry>, ctx: &mut SymbolTableAccess<'_, C, L>, symbol_tables: &SymbolTables<C, L>) -> Result<(), CheckError>`. Pre-S66 the legacy `check_form` mutated the table in-place via a typecheck-internal `merge_form_result()`; FIXME 0160 first purified it to a single-call pure function; Decision 44 then split that single call into a two-function Pass 1 (signatures) + Pass 2 (bodies) shape so spec §5.13.1's two-pass mandate (forward references / mutual recursion) survives the orchestrator-side cluster. The two-function shape exposed implementation phasing across the facade and created a state-threading hole; the third amendment collapses it back into a single `check_forms` call that runs both passes internally. Pass-1-to-Pass-2 working state lives inside `check_forms`'s frame and never crosses the facade. FIXME 0167's Approach B + SymbolTableAccess discipline is preserved: staging is empty at cluster start; reads via `View::union(staging, live)`; writes go to staging via the same `current_symbol_table_mut` accessor used in committed-mode. `check_forms` is pure with respect to live state; it does not mutate the live `SymbolTable`. The 91 register-call sites in `program.rs` do not change individually — staging-vs-live is absorbed inside `SymbolTableAccess::current_symbol_table{,_mut}` accessors. The caller (`int::process_cluster`) constructs `SymbolTableAccess::Cluster` with a transient orchestrator-local staging table and commits staging into the live table atomically via `int::insert_cluster` only on whole-cluster success; on `Err(Gap)`, the orchestrator drops the staging frame and retries the whole `check_forms` call against a fresh staging frame; on `Err(TypeError)`, staging dissolves with the function frame (live table byte-identical). See `crates/cranelisp-typecheck/src/lib.rs` rustdoc (post-S72 W5 canonical; `facades/typecheck.md` retired — cross-surface narrative in `bounded-contexts.md` §2), `bounded-contexts.md` §6 (int) + `src/cluster.rs` rustdoc for the `process_cluster` orchestrator side (`facades/int.md` retired S81 W-Retire → BC §6 + `design/int/` + source rustdoc), and the `check_forms` section above.

### Functions added
- `CallGraph::add_edge()`, `reverse_index()`, `sccs()`, `non_tail_self_recursion()`
- `SymbolTable::defined_symbols() -> impl Iterator<Item = (&Symbol, &ModuleEntry)>` — shared codegen-compilable predicate (Decision 22, Sprint 56).
- ~~`declare_all_got_slots()`~~ — removed. GOT slots are assigned incrementally by `ModuleCodegenState::ensure_slot_for()` during function registration, not in a separate phase. See `pipeline-v2.md` §12.5.

### Coherence checklist
- [x] No structurally identical types at any pipeline boundary
- [x] No adapter functions between boundary types
- [x] Every pipeline stage has exactly one entry point per crate
- [x] Mode differences expressed as parameters, not separate types
- [x] All spec-required TopLevel variants present (§5.1–5.4, §4)
- [x] `Serialize`/`Deserialize` on all boundary types that need caching
- [x] Module context is an explicit parameter (`CompileContext`), not implicit mutable state
