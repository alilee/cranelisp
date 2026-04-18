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
string_newtype!(JitSymbol);        // JIT linker name: "add$Int+Int"

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
        mangled_name: JitSymbol,
    },
    SigDispatch {
        mangled_name: JitSymbol,
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

### FormCheckResult (typecheck-internal)

Per-form typecheck output, returned by `tc.check_form()`. **Not a boundary type** — lives inside `cranelisp-typecheck` and is merged via `tc.merge_form_result()`. Merging deposits annotations onto AST nodes (`Expr.inferred_type`, `Expr::Apply.resolved_call`), writes call-graph edges to `ModuleEntry.callees`, and registers mangled multi-sig variants / mono specializations directly on the `SymbolTable`. It does not populate a cross-crate `CheckResult`.

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
/// Per-module symbol table. Pure data.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SymbolTable {
    pub path: ModuleFullPath,
    pub symbols: HashMap<Symbol, ModuleEntry>,
}

impl SymbolTable {
    pub fn get(&self, name: &str) -> Option<&ModuleEntry> { ... }
    pub fn insert(&mut self, name: Symbol, entry: ModuleEntry) { ... }
    pub fn public_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry)> { ... }
}

/// Module structural metadata.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModuleStructure {
    pub path: ModuleFullPath,
    pub file_path: Option<PathBuf>,
    pub mod_decls: Vec<ModuleName>,
    pub import_specs: Vec<ImportSpec>,
    pub export_specs: Vec<ExportSpec>,
    pub impl_sexps: Vec<ImplSexp>,
    pub impls: Vec<TraitImpl>,
    pub dll_path: Option<PathBuf>,
}
```

### Module Entries

```rust
/// An entry in a module's symbol table.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ModuleEntry {
    Def {
        scheme: Scheme,
        visibility: Visibility,
        docstring: Option<String>,
        param_names: Vec<Symbol>,
        kind: DefKind,
        /// Fully qualified callees, populated by finalize_check_result()
        /// from TC-sourced call graph edges. Used by scheduler for
        /// transitive macro dep discovery. See Decision 21.
        callees: Vec<FQSymbol>,
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
        jit_name: Option<JitSymbol>,
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
    PlatformEffect,
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

### HeapString (in `cranelisp-runtime`)

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

> Note on `ModuleEntry::Def.ast`: The `ast: Option<Defn>` field was introduced in Sprint 55 (Phase 1) so typecheck can deposit annotated bodies directly on symbol-table entries. It is not yet shown in the `ModuleEntry::Def` variant definition earlier in this document — a follow-up edit will add it alongside `scheme`, `visibility`, `kind`, `callees`, and `got_slot`. See `design/typecheck/ast-annotation.md` §6 for the authoritative per-category table of which entries carry `ast: Some(_)`.

---

## Summary of Changes from v1

### Types deleted
- `ReplInput` — replaced by `TopLevel` with `Expr` variant
- `ReplCheckResult` — replaced by `CheckResult` with `display: Option<DisplayInfo>`
- `CheckResult` as a **boundary type** — demoted to typecheck-internal (Sprint 55/56). The struct still exists transiently in `cranelisp-types/src/check.rs` carrying `warnings + display` plus legacy working fields pending Phase 5 slimming (FIXME filed by `/typecheck`). It is no longer a parameter of any backend function.

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
- `compile_to_module<M: Module>(module_path, names, symbol_tables, module)` — four-parameter normative signature (Sprint 56 Phase 2). No `CheckResult`, no `Program`, no intrinsic IDs, no GOT map, no arities parameter. See `design/backend/compile-to-module.md` §2.1.

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
