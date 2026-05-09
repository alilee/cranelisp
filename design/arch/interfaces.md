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
string_newtype!(LinkerSymbol);        // JIT linker name: "add$Int+Int"

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
}
```

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

/// Trait implementation. spec: §5.4
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitImpl {
    pub trait_name: TraitName,
    pub target_type: TypeName,
    pub type_args: Vec<Symbol>,
    pub type_constraints: Vec<(Symbol, TraitName)>,
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
```

No changes from v1.

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
| `method_resolutions: MethodResolutions` | `Expr::Apply.resolved_call` on AST nodes (`ModuleEntry::Def.ast`). |
| `expr_types: HashMap<Span, Type>` | `Expr.inferred_type` on every AST node. |
| `mono_defns: Vec<MonoDefn>` | Registered eagerly by `register_mono_entry` as mangled `ModuleEntry::Def` entries with `ast: Some(_)` carrying fully-concrete annotations. |
| `default_method_defns: Vec<Defn>` | Registered by `register_mangled_method` as mangled `ModuleEntry::Def` entries with `ast: Some(_)`. |
| `constrained_fn_names: HashSet<Symbol>` | Derivable by scanning `SymbolTable` for `ModuleEntry::Def { kind: UserFn { constrained_fn: Some(_) }, .. }` — negation of `defined_symbols()` within `UserFn`. |
| `type_defs`, `constructor_to_type` | Already on `SymbolTable` as `ModuleEntry::TypeDef` / `ModuleEntry::Constructor`. |
| `call_graph: CallGraph` | Transient within-module graph still produced during typecheck for TCO / analysis (see §"Call Graph"); persistent per-symbol `callees: Vec<FQSymbol>` lives on `ModuleEntry::Def` / `ModuleEntry::Macro` per Decision 21. |

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
/// Map from call site span to resolution.
pub type MethodResolutions = HashMap<Span, ResolvedCall>;

/// How a function call was resolved by the typechecker.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ResolvedCall {
    TraitMethod {
        trait_name: TraitName,
        method_name: Symbol,
        impl_type: TypeName,
        mangled_name: LinkerSymbol,
    },
    SigDispatch {
        mangled_name: LinkerSymbol,
    },
    AutoCurry {
        target_name: Symbol,
        applied_count: usize,
        total_count: usize,
        trait_resolution: Option<Box<ResolvedCall>>,
    },
    BuiltinFn {
        name: Symbol,
    },
}
```

No changes from v1.

### Monomorphised Definitions

```rust
/// A monomorphised function definition with its specific resolutions.
#[derive(Debug)]
pub struct MonoDefn {
    pub defn: Defn,
    pub resolutions: MethodResolutions,
    pub expr_types: HashMap<Span, Type>,
}
```

No changes from v1.

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
`facades/types.md` §"`ParsedEntry`" for the full enum shape and
`facades/frontend.md` §"Free functions" + `facades/typecheck.md`
§"Free functions" for the producer/consumer signatures.

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

### `check_form` is pure (Sprint 66, FIXME 0160)

The pre-S66 `check_form` mutated the symbol table in-place and was
merged via a typecheck-internal `merge_form_result()` helper. Per FIXME
0160 resolution, `check_form` is now a **pure function**:

```rust
pub fn check_form<C, L>(
    parsed: ParsedEntry,
    table: &SymbolTable<C, L>,         // immutable — see Decision 38
    symbol_tables: &SymbolTables<C, L>, // for cross-module reads
) -> Result<Vec<(Symbol, ModuleEntry<C>)>, CheckError>;
```

The function does NOT call `insert_or_update`, does NOT install import
bindings, does NOT mutate the table. The caller (`int::insert_symbol`)
inserts the returned entries on `Ok`; on `Err(Gap | TypeError)` nothing
has been written, no rollback is needed. Per FIXME 0160 the post-Gap
state contract is **structural Option B** — the orchestrator's
snapshot-restore (`ReplSnapshot`) covers type-var-pool rollback inside
`CheckState` between calls, but the symbol table is unaffected by a
Gap or TypeError return because the function never wrote.

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
/// Information about a user-defined type.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeDefInfo {
    pub name: TypeName,
    pub type_params: Vec<Symbol>,
    pub constructors: Vec<ConstructorInfo>,
    pub docstring: Option<String>,
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

#### Two-GOT model — SymbolTable GOT vs `.o` data section GOT

Decision 23 (updated Sprint 58 Wave 2) records that every CLIF reference to `__cranelisp_got_{M}` resolves to a base address; the runtime memory the base addresses depends on the `Module` implementation used at finalize time. The two GOTs are distinct artefacts with different owners, lifetimes, mutability, and purposes — but they share the same name and the same per-slot semantics so that the backend can emit byte-identical CLIF in both modes.

| GOT | Backing | Owner / location | Lifetime | When read | Mutable? |
|---|---|---|---|---|---|
| **SymbolTable GOT** | `pub got: Arc<GotTable>` field on `SymbolTable` (above, line 870) — in-process memory | runtime / `cranelisp-types` | session — created at module registration, lives until session teardown | JIT (`--run`, REPL) — `JITBuilder::symbol_lookup_fn` (registered by the integration layer in `src/session_v4.rs`) returns `symbol_tables[M].got.base_ptr()` when Cranelift resolves the `Linkage::Import` data symbol at finalize | YES — REPL redefinition writes a new fn ptr into the existing slot via the Decision-31 atomic swap; the swap is the redefinition mechanism that makes existing callers see the new code |
| **`.o` data section GOT** | `Linkage::Export` data symbol named `__cranelisp_got_{M}` defined inside `M`'s own `.o`, with relocation initializers against the local function symbols (Decision 36) | object-file artefact emitted by `compile_to_module<ObjectModule>` | one per `.o` file on disk; in-memory only after `Linker::load_object` mmaps the `.o` | `--link` mode — system linker (`ld`) patches relocations against the defined data symbol when producing the executable; or our cache `Linker` in `--run`/REPL after cache-hit, when reading the `.o` to resolve cross-`.o` references | NO — initialised by the linker / loader once at load time, never mutated thereafter |

**Why two GOTs.** The SymbolTable GOT is for runtime — JIT calls index into it; REPL redefinition mutates it; it is the live store that user code reaches through. The `.o` data section GOT is for the on-disk artefact — the system linker in `--link` mode needs a defined data symbol to patch relocations against; without it, the system linker reports `__cranelisp_got_{M}` undefined (Bug B in `design/int/symbol-table-cache.md` §"Investigation findings"). The two are not stepping stones for each other — they serve different masters at different lifecycle phases.

**Same data symbol, different resolvers.** The CLIF emitted by `compile_to_module` declares `__cranelisp_got_{M}` as `Linkage::Import` from the caller's POV uniformly (the FnCompiler does not know which Module impl resolves it). The `.o` definition (`Linkage::Export`) appears only in the *defining* module's own `.o`, emitted via `compile_to_module<ObjectModule>`'s data-section emission step. JIT mode never reads the `.o` definition — `JITBuilder::symbol_lookup_fn` short-circuits the import resolution to the SymbolTable GOT base. `--link` mode never touches the SymbolTable GOT (the binary runs standalone and never instantiates a session).

**Mode dispatch is the Module impl, not the CLIF.** This is the canonical illustration of Principle 11 (single pipeline, mode parameters): one CLIF, two resolvers. Adding a third mode (e.g. AOT to a static archive) would add a third resolver behind a third Module impl — the CLIF would not change.

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
        /// Module-local GOT slot index (Sprint 56 Wave 0 §9.8 G7). Assigned
        /// at registration time for user-defined functions. `None` for
        /// primitives and special forms.
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
        /// — fn_ptr unification**).
        /// Written by the priority worker after `compile_to_module` returns
        /// (or by `load_object` on cache-hit). `None` until codegen completes,
        /// and `None` for entries whose lifecycle owner lives elsewhere
        /// (primitives — process-static `LazyLock<SymbolTable>` in
        /// `cranelisp-primitives`; platform DLL fns — DLL handle held in
        /// `SharedState.kept_dlls`). The integration layer chooses
        /// `C = Code` (re-exported from `cranelisp-backend`); the variants
        /// carry **lifecycle ownership only** — the call address lives on
        /// the sibling `fn_ptr` field below, not inside the variant.
        ///
        /// **Variant shape post-Sprint 66 (S66 fn_ptr unification)**:
        /// `Code::Jit(Arc<Jit>)` for JIT-built user fns;
        /// `Code::Linker(Arc<Linker>)` for cache-hit user fns. The previous
        /// `Code::Jit { jit, ptr }` / `Code::Linker { linker, ptr }` shapes
        /// are retired — the per-entry ptr is now on `fn_ptr`. Reading the
        /// call address through a variant-uniform `Code::ptr()` accessor is
        /// retired with the embedded ptr; consumers read `fn_ptr` directly.
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
        /// evidence). The safety invariant is maintained by: (a) the
        /// `fn_ptr` raw pointer becomes invalid the same instant
        /// `JITModule::free_memory()` runs (same lifecycle semantics as the
        /// pre-S66 in-variant ptr — only the field placement moved); (b)
        /// GOT slots are atomically swapped to new code before the old Arc
        /// can drop (Decision 41 per-symbol JIT cardinality means redefine
        /// → new `Code::Jit(Arc<Jit>)` written to entry → old Arc clone
        /// drops as the entry is replaced); (c) user-returned `fn` values
        /// are heap closures calling through the GOT, not raw code
        /// pointers.
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
        /// 41 (per-symbol JIT cardinality + S66 amendment relocating ptr
        /// to `fn_ptr`).
        #[serde(skip)]
        code: Option<C>,
        /// Unified function pointer — single source of truth for
        /// "where to call to invoke this entry" (Sprint 66 fn_ptr
        /// unification, 2026-05-09). Replaces the previously-separate
        /// `platform_fn_ptr` and supersedes the briefly-planned
        /// `primitive_fn_ptr`. Origin is encoded by `kind: DefKind`,
        /// NOT by which optional field is set:
        ///
        /// - `DefKind::UserFn { .. }` — JIT-built or linker-loaded user
        ///   fn; ptr written by backend's `compile_to_module` (JIT) or
        ///   by `load_object` (cache-hit `.o`); paired with
        ///   `code = Some(Code::Jit(_))` or `Some(Code::Linker(_))`.
        /// - `DefKind::Primitive { primitive_kind: Inline | Extern }` —
        ///   user-callable primitive; ptr written at static-init by
        ///   `cranelisp-primitives::PRIMITIVES_TABLE`; `code = None`
        ///   (process lifetime; no per-entry lifecycle owner).
        /// - `DefKind::Primitive { primitive_kind: PlatformEffect { .. } }`
        ///   — platform DLL fn; ptr resolved at platform-load time from
        ///   `OwnedPlatformFnDescriptor.ptr` during `(platform …)` form
        ///   processing; `code = None` (DLL handle held in
        ///   `SharedState.kept_dlls`; pages not unmapped while the
        ///   session lives). Replaces the per-DLL `PlatformRegistry`
        ///   the IO trampoline previously consulted.
        ///
        /// **Cycle-avoidance rationale (S66).** The `Code` enum lives
        /// in `cranelisp-backend` and references Cranelift types
        /// (`Jit`, `Linker`); `cranelisp-primitives` and
        /// `cranelisp-platform` must NOT depend on `cranelisp-backend`.
        /// The unified `fn_ptr` field decouples the call address from
        /// the lifecycle owner: primitives' static `SymbolTable` uses
        /// `SymbolTable<C = ()>` (Decision 32 default — `()` never
        /// names `Code`), populates `fn_ptr` from a function pointer
        /// constant, and leaves `code = None`. Same for platform DLL
        /// fns — `fn_ptr` is set from the manifest, `code` stays
        /// `None`, no Cranelift types are named in those crates. The
        /// dep DAG stays acyclic.
        ///
        /// **Ptr extraction.** Read `fn_ptr` directly. The variant-uniform
        /// `Code::ptr()` accessor is retired post-S66 — there is no ptr
        /// inside the `Code` variant to accessor over.
        ///
        /// **`scheduling_class` is NOT a sibling here.** It lives INSIDE
        /// `PrimitiveKind::PlatformEffect { scheduling_class }`. Only
        /// platform-effect entries can carry one — the asymmetry is
        /// deliberate (see Decision 26).
        ///
        /// `#[serde(skip)]` — runtime state. Cache re-derives `fn_ptr`
        /// on cache-hit load: from `ast` for user fns (`load_object`
        /// resolves each defined symbol's address); from
        /// `cranelisp-primitives::PRIMITIVES_TABLE` for primitives; from
        /// the owning `PlatformDecl` (re-resolving the DLL and reading
        /// its manifest) for platform DLL fns. See Decisions 25 +
        /// 26 + 41 (S66 amendments).
        #[serde(skip)]
        fn_ptr: Option<*const u8>,
    },
    Import { source: FQSymbol },
    Reexport { source: FQSymbol },
    TypeDef {
        info: TypeDefInfo,
        visibility: Visibility,
        constructor_scheme: Option<Scheme>,
        sexp: Option<Sexp>,
    },
    TraitDecl {
        decl: TraitDecl,
        visibility: Visibility,
        sexp: Option<Sexp>,
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
    Ambiguous,
}

impl ModuleEntry {
    pub fn is_public(&self) -> bool { ... }
}
```

### Definition Classification

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DefKind {
    SpecialForm { description: String },
    Primitive {
        primitive_kind: PrimitiveKind,
        jit_name: Option<LinkerSymbol>,
    },
    UserFn {
        constrained_fn: Option<ConstrainedFn>,
    },
    Overloaded {
        variants: Vec<OverloadVariant>,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PrimitiveKind {
    Inline,
    Extern,
    /// Platform DLL effect. `scheduling_class` is a variant field (not a
    /// sibling on `ModuleEntry::Def`) so that only entries that actually
    /// carry a scheduling class can have one — see Decision 26. Written
    /// during `(platform ...)` form processing from the DLL manifest; read
    /// by `bind_chain_analysis.rs::classify_expr` via an Import-chain walk.
    PlatformEffect {
        scheduling_class: cranelisp_platform::SchedulingClass,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OverloadVariant {
    pub param_types: Vec<Type>,
    pub ret_type: Type,
    pub mangled_name: Symbol,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstrainedFn {
    pub defn: Defn,
    pub scheme: Scheme,
}
```

No changes from v1.

### Backend-hosted `Code` Enum (in `cranelisp-backend`)

The integration layer's concrete `C` for `SymbolTable<C, L>` is the `Code`
enum defined below. **Lives in `cranelisp-backend/src/code.rs` per
Decision 41 (Sprint 64 — Layer 2 Option B retracts; backend constructs
`Code` directly inside `compile_to_module`).** Originally placed in
`src/code.rs` per Decision 35; the move to backend keeps `cranelisp-types
→ cranelisp-backend` forbidden (the dep direction Principle 3 protects)
while letting backend's direct-write pattern (Decision 38's
`write_code(&self, …)`) self-contain on the backend side. The
integration layer still names `Code` at the session boundary's
`SymbolTable<Code, ()>` instantiation, re-exporting from backend.

```rust
// crates/cranelisp-backend/src/code.rs; owned by /backend.
//
// Concrete `C: CodeStore` for SymbolTable<Code, ()>. Carries lifecycle
// ownership only — the per-entry call address lives on the sibling
// `ModuleEntry::Def.fn_ptr` field (S66 fn_ptr unification, 2026-05-09).
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

**S66 amendment — variant slimming (2026-05-09)**. The previous variant
shapes `Code::Jit { jit, ptr }` and `Code::Linker { linker, ptr }`
retire. The per-entry ptr migrates to a unified `fn_ptr: Option<*const
u8>` field on `ModuleEntry::Def` (subsumes the previously-separate
`platform_fn_ptr`; supersedes the briefly-planned `primitive_fn_ptr`).
The variant-uniform `Code::ptr()` accessor retires with the embedded
ptr; consumers read `fn_ptr` directly. Decision 31 Scenario 2 reclaim
semantics are preserved (lifecycle ownership stays inside
`Code::Jit(Arc<Jit>)`; `Drop` chain unchanged; the `fn_ptr` raw pointer
becomes invalid the same instant `JITModule::free_memory()` runs — same
lifecycle as the pre-S66 in-variant ptr, only the field placement
moved). See `facades/types.md` §"Symbol table — the single store" +
`facades/backend.md` §"`Code` — the per-symbol lifecycle owner" for the
authoritative shape, and Decision 41's "S66 amendment" for the
amendment record.

The session boundary types in `src/session_v4.rs` instantiate
`SymbolTable<Code, ()>` and `ModuleEntry<Code>`; backend signatures
continue to read `SymbolTable` (i.e. `SymbolTable<(), ()>`) per Decision
32 and `compile-to-module.md` §17.

Per Decision 41, `compile_to_module<M: Module>` no longer returns a
codegen artefact: it writes `Code::Jit(Arc<Jit>)` onto each defined
symbol's `Def.code` directly via `SymbolTable::write_code(&self, sym,
code)` (Decision 38's interior-mutable signature) AND writes the
resulting fn pointer to the same entry's `fn_ptr` field. The function
returns `Result<(), CompilationError>`. The historical CP1 Layer-2
Option-B return-tuple shape (`compile_to_module` returning
`(Arc<Jit>, HashMap<Symbol, *const u8>)` for the integration layer to
wrap into `Code::Jit { jit, ptr }`) is retracted by Decision 41; the
`int` post-loop in `worker.rs:2860-3018` collapses.

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

```rust
/// Snapshot of typechecker state for REPL error recovery.
#[derive(Debug, Clone)]
pub struct ReplSnapshot {
    pub next_type_id: TypeId,
    pub symbol_keys: HashSet<Symbol>,
    pub subst_len: usize,
    pub scope_depth: usize,
}
```

No changes from v1.

---

## Frontend Traits

```rust
/// Trait for expanding macros during AST building.
/// Implemented by the binary crate; allows frontend to remain
/// independent of backend.
pub trait MacroExpander {
    fn expand(
        &mut self,
        name: &Symbol,
        args: &[Sexp],
        span: Span,
    ) -> Result<Sexp, CranelispError>;

    fn is_macro(&self, name: &str) -> bool;
}
```

No changes from v1.

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

> Note on `ModuleEntry::Def.ast` / `code` / `fn_ptr`: the full set of typecheck- and codegen-populated fields on `ModuleEntry::Def` (`ast`, `code`, `fn_ptr`, `got_slot`, `callees`, `trait_origin`) is now shown in the variant definition above. `ast` arrived in Sprint 55 (Phase 1); `code` shape landed in Sprint 57 Phase 3 G6 (concrete `Code` placeholder); the previously-separate `platform_fn_ptr` landed in Sprint 57 Phase 4 G8; `code` is parameterised to `Option<C>` in Sprint 58 Phase 5 Step 5c (G12) per Decision 32 — the integration layer chooses the concrete `C = Code` (re-exported from `cranelisp-backend` per Decision 41) so per-redefinition reclaim fires (Decision 31 Scenario 2). **Sprint 66 (2026-05-09 — fn_ptr unification)** unifies `platform_fn_ptr` into a single `fn_ptr: Option<*const u8>` field that covers all four ptr origins (JIT user fn, linker-loaded user fn, primitive, platform DLL fn) and slims `Code` variants to lifecycle owner only (`Code::Jit(Arc<Jit>)` / `Code::Linker(Arc<Linker>)`). The `code` and `fn_ptr` fields are `#[serde(skip)]` — runtime-only, re-derivable from the AST + cache `.o` (`fn_ptr`/`code` for user fns), from `cranelisp-primitives::PRIMITIVES_TABLE` (`fn_ptr` for primitives), or from the owning `PlatformDecl` (`fn_ptr` for platform DLL fns) on cache-hit load. See `design/typecheck/ast-annotation.md` §6 for the authoritative per-category table of which entries carry `ast: Some(_)`, and `design/arch/facades/types.md` §"Symbol table — the single store" for the canonical S66 field shape.

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
- `Code` enum (Sprint 58 Phase 3a, Decision 35; Sprint 64 location move per Decision 41; **Sprint 66 variant slimming per S66 fn_ptr unification**) — concrete `C` for `SymbolTable<Code, ()>`. Variants `Code::Jit(Arc<Jit>)` + `Code::Linker(Arc<Linker>)` — lifecycle owner ONLY post-S66; the per-entry call address lives on the sibling `ModuleEntry::Def.fn_ptr` field. Lives in `cranelisp-backend/src/code.rs` (moved from `src/code.rs` per Decision 41), NOT in `cranelisp-types` (Principle 3). The CP1 Layer-2-Option-B return-tuple pattern retracts: `compile_to_module` writes `Code::Jit(Arc<Jit>)` and `fn_ptr` directly via Decision 38's `write_code` plus a paired `fn_ptr` write, returning `Result<(), CompilationError>`. Documented at this boundary so every consumer of `SymbolTable<Code, ()>` references the same shape.
- `ModuleEntry::Def.fn_ptr: Option<*const u8>` (Sprint 66 — fn_ptr unification, 2026-05-09). Single source of truth for "where to call to invoke this entry"; subsumes the previously-separate `platform_fn_ptr` field and supersedes the briefly-planned `primitive_fn_ptr`. Origin encoded by `kind: DefKind` (UserFn → JIT/linker; Primitive { Builtin/Inline } → primitive; Primitive { PlatformEffect } → platform DLL). `#[serde(skip)]`. See `facades/types.md` §"Symbol table — the single store" + Decision 41 S66 amendment.
- `ParsedEntry` enum (Sprint 66, FIXME 0156) — parse-time-only transient produced by `cranelisp_frontend::build_form` and consumed by `cranelisp_typecheck::check_form`. NEVER lands in `SymbolTable`. `#[non_exhaustive]`; not `Serialize/Deserialize`. See `facades/types.md` §"`ParsedEntry`" + `facades/frontend.md` + `facades/typecheck.md`.
- `DefmacroInfo` struct (Sprint 66, FIXME 0156) — moved from `cranelisp-frontend/src/defmacro.rs` to `cranelisp-types` so `int`'s post-`build_form` consumption path can name the type uniformly. Frontend's `parse_defmacro` becomes `pub(crate)` inside the `build_form` dispatcher.

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
- `compile_to_module<M: Module>(module_path, names, symbol_tables, module)` — four-parameter normative signature (Sprint 56 Phase 2). No `CheckResult`, no `Program`, no intrinsic IDs, no GOT map, no arities parameter. **Per Decision 41 (Sprint 64) + S66 amendment**: returns `Result<(), CompilationError>`; backend writes `Code::Jit(Arc<Jit>)` via `SymbolTable::write_code` and the resulting fn pointer to the same entry's `fn_ptr` field, directly. See `facades/backend.md` §"Free functions" and `design/backend/compile-to-module.md`.
- `cranelisp_frontend::build_form(sexp: &Sexp) -> Result<Vec<ParsedEntry>, CranelispError>` (Sprint 66, FIXME 0156) — replaces the prior `build_ast` shape at the frontend's per-form boundary. Returns a `Vec` because some shapes yield more than one entry per source form (multi-clause `defmacro`, `deftype` with constructors). See `facades/frontend.md`.
- `cranelisp_typecheck::check_form` is now a **pure function** (Sprint 66, FIXME 0160): `(parsed: ParsedEntry, table: &SymbolTable<C, L>, symbol_tables: &SymbolTables<C, L>) -> Result<Vec<(Symbol, ModuleEntry<C>)>, CheckError>`. Pre-S66 it mutated the table in-place via a typecheck-internal `merge_form_result()`; post-S66 the function does NOT mutate, the caller (`int::insert_symbol`) commits returned entries on `Ok`, and on `Err(Gap | TypeError)` nothing has been written. See `facades/typecheck.md` and §"`check_form` is pure" above.

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
