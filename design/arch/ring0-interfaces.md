# Ring 0 Interface Subset

Ring 0 subset of the boundary types defined in `design/arch/interfaces.md`. This document specifies the exact Rust signatures that compiler skills implement against during Ring 0. Types are defined in full (all variants) in `cranelisp-types` from the start; this document marks which variants/fields Ring 0 exercises and which are deferred.

Ring 0 property: **Expressions, types, functions, let, if, match. No heap allocation, no reference counting.**

## Workspace Status

- `cargo check` succeeds on the 7-crate workspace
- All crate stubs compile (empty `lib.rs` / `main.rs` with comments)
- Dependency DAG verified:
  - `cranelisp-types`: `serde` only
  - `cranelisp-frontend`: `cranelisp-types`
  - `cranelisp-typecheck`: `cranelisp-types`
  - `cranelisp-backend`: `cranelisp-types`, `cranelisp-runtime`
  - `cranelisp-runtime`: `cranelisp-platform`
  - `cranelisp-platform`: no cranelisp deps
  - `cranelisp` (binary): all six library crates

### Cranelift Dependencies

`cranelisp-backend/Cargo.toml` uses Cranelift **0.116** (not 0.125 as originally planned — 0.125 was unavailable). API differences are minor: `jump`/`brif` take `&[Value]` directly rather than `&[BlockArg]`.

```toml
[dependencies]
cranelift = "0.116"
cranelift-module = "0.116"
cranelift-jit = "0.116"
cranelift-native = "0.116"
cranelift-codegen = { version = "0.116", features = ["disas"] }
```

`cranelift-object` is needed for standalone executable generation (Ring 4 only). Not required in Ring 0.

---

## Foundation Types

### `Span`

**Ring 0 status**: Fully exercised.

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

**Notes**: Every AST node, every error, every `CheckResult` key uses `Span`. Fully exercised from Ring 0 onward. `SYNTHETIC` is used for compiler-generated nodes (e.g., implicit returns).

### String Newtypes

**Ring 0 status**: `Symbol` fully exercised. Others defined but lightly used.

```rust
string_newtype!(Symbol);           // exercised: local names in SymbolTable
string_newtype!(ModuleFullPath);   // exercised: single "user" module in Ring 0
string_newtype!(TraitName);        // defined, not exercised until Ring 2
string_newtype!(TypeName);         // defined, exercised for deftype names
string_newtype!(ModuleName);       // defined, not exercised until Ring 2
string_newtype!(JitSymbol);        // exercised: JIT linker names in Ring 0

/// Fully qualified symbol: module path + local name.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FQSymbol {
    pub module: ModuleFullPath,
    pub symbol: Symbol,
}
```

**Ring 0 constraint**: All compilation happens in a single implicit module (`"user"`). `ModuleFullPath` is set but cross-module resolution is not exercised until Ring 2.

### `CranelispError`

**Ring 0 status**: `ParseError`, `TypeError`, `CodegenError` exercised. `ModuleError` defined but not exercised.

```rust
#[derive(Debug)]
pub enum CranelispError {
    // --- Ring 0 exercised ---
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
    // --- Defined, deferred to Ring 2 ---
    ModuleError {
        message: String,
        file: Option<PathBuf>,
        span: Span,
    },
}
```

### `Warning`

**Ring 0 status**: Defined. Exercised if the typechecker produces any warnings (e.g., unused variable warnings).

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Warning {
    pub message: String,
    pub span: Span,
}
```

---

## Reader Output

### `Sexp`

**Ring 0 status**: All variants except `Str` exercised.

```rust
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Sexp {
    // --- Ring 0 exercised ---
    Symbol(String, Span),    // identifiers: foo, +, defn, if
    Int(i64, Span),          // integer literals: 42, -3
    Float(f64, Span),        // float literals: 3.14
    Bool(bool, Span),        // boolean literals: true, false
    List(Vec<Sexp>, Span),   // parenthesized forms: (f x y), (defn name [p] body)
    Bracket(Vec<Sexp>, Span),// bracketed lists: [a b c], [:Int x]

    // --- Defined, deferred to Ring 1 ---
    Str(String, Span),       // string literals: "hello"
}

impl Sexp {
    pub fn span(&self) -> Span { ... }
}
```

**Ring 0 notes**:
- The reader must parse all 7 variants from Ring 0 (including `Str`) so that error messages are correct. The AST builder rejects `Str` in Ring 0 with a clear error ("strings not yet supported").
- `Symbol` carries the raw identifier string, including qualified names like `core/map` (which Ring 0 will not resolve but should not reject at the reader level).
- `Bracket` is used for function parameter lists `[a b]`, type annotations `[:Int x]`, and `deftype` field lists.

---

## AST

### `Expr`

**Ring 0 status**: 10 of 12 variants exercised.

All variants have spec traceability:
- `IntLit`, `FloatLit`, `BoolLit`, `StringLit` — spec §4.1 (Literals)
- `Var` — spec §4.2 (Variable Reference)
- `Let` — spec §4.3 (Let Expression)
- `If` — spec §4.4 (If Expression)
- `Lambda` — spec §4.5 (Lambda Expression)
- `Apply` — spec §4.6 (Function Application)
- `Match` — spec §4.8 (Match Expression)
- `Annotate` — spec §4.9 (Type Annotation)
- `VecLit` — spec §4.10 (Vec Literal)
- `Trace` — spec §12 (Runtime Model, implementation extension)
- `RunTests` — REPL-only special form (no spec section)

Note: `ParLet` and `ParBind` have been removed. `par-let` was removed from the spec (§4.12 deleted); lenient evaluation (§12.4.3) covers parallel `let` transparently. There is no `par-bind!` form (§10.12).

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Expr {
    // --- Ring 0 exercised ---
    IntLit {
        value: i64,
        span: Span,
    },
    FloatLit {
        value: f64,
        span: Span,
    },
    BoolLit {
        value: bool,
        span: Span,
    },
    Var {
        name: Symbol,
        span: Span,
    },
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
    Annotate {
        annotation: TypeExpr,
        expr: Box<Expr>,
        span: Span,
    },

    // --- Defined, deferred to Ring 1 ---
    StringLit {
        value: String,
        span: Span,
    },
    VecLit {
        elements: Vec<Expr>,
        span: Span,
    },

    // --- Defined, deferred to Ring 4 ---
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
}

impl Expr {
    pub fn span(&self) -> Span { ... }
}
```

**Ring 0 exercised variants**:
- `IntLit`, `FloatLit`, `BoolLit` -- literal values (no heap allocation)
- `Var` -- variable references
- `Let` -- local bindings with `let`-polymorphism
- `If` -- conditional branching (requires Bool condition)
- `Lambda` -- function expressions (Ring 0: no closures -- all lambdas are top-level or non-capturing)
- `Apply` -- function application (including primitive operators like `+`, `-`, `*`, `=`, `<`)
- `Match` -- pattern matching over enum-only ADTs (no heap fields)
- `Annotate` -- explicit type annotations (`:Int`, `:(Fn [Int] Int)`)

**Ring 0 constraints on Lambda**: In Ring 0, lambdas do not capture variables from enclosing scopes. All lambda parameters and all referenced names must be either parameters or top-level definitions. Closure compilation (heap-allocated environment) is Ring 1. The typechecker infers `Fn` types for lambdas; the backend compiles them as bare function pointers without an environment.

### `Pattern` and `MatchArm`

**Ring 0 status**: All variants exercised (for enum-only ADTs).

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Pattern {
    /// Constructor pattern: `Red`, `Green`, `None`
    /// Ring 0: nullary constructors only (no bindings)
    Constructor {
        name: Symbol,
        bindings: Vec<Symbol>,  // empty in Ring 0 (enum-only)
        span: Span,
    },
    /// Wildcard: `_`
    Wildcard {
        span: Span,
    },
    /// Variable binding: `x`
    Var {
        name: Symbol,
        span: Span,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Expr,
    pub span: Span,
}
```

**Ring 0 constraint**: `Constructor` patterns have empty `bindings` because Ring 0 ADTs are enum-only (nullary constructors). Data constructors with fields (e.g., `(Some x)`) are Ring 1.

### `TypeExpr`

**Ring 0 status**: `Named`, `FnType`, `TypeVar` exercised. Others defined.

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TypeExpr {
    // --- Ring 0 exercised ---
    Named(TypeName),                        // :Int, :Bool, :Float
    FnType(Vec<TypeExpr>, Box<TypeExpr>),   // :(Fn [Int Int] Int)
    TypeVar(Symbol),                        // :a, :b

    // --- Defined, deferred ---
    SelfType,                               // Ring 2 (traits)
    Applied(TypeName, Vec<TypeExpr>),        // Ring 1 (parameterized ADTs)
}
```

### `TopLevel`

**Ring 0 status**: `Defn` and `TypeDef` (enum-only) exercised.

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Visibility {
    Public,    // Ring 0: defined, but no cross-module visibility checks
    Private,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Defn {
    pub name: Symbol,
    pub docstring: Option<String>,
    pub params: Vec<Symbol>,
    pub param_annotations: Vec<Option<TypeExpr>>,
    pub body: Expr,
    pub visibility: Visibility,
    pub span: Span,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TopLevel {
    // --- Ring 0 exercised ---
    Defn(Defn),
    TypeDef {
        name: TypeName,
        docstring: Option<String>,
        type_params: Vec<Symbol>,       // empty in Ring 0 (no parameterized ADTs)
        constructors: Vec<ConstructorDef>,  // all nullary in Ring 0
        visibility: Visibility,
        span: Span,
    },

    // --- Defined, deferred ---
    DefnMulti {                         // Ring 2 (multi-signature dispatch)
        name: Symbol,
        docstring: Option<String>,
        variants: Vec<DefnVariant>,
        visibility: Visibility,
        span: Span,
    },
    TraitDecl(TraitDecl),               // Ring 2
    TraitImpl(TraitImpl),               // Ring 2
}

pub type Program = Vec<TopLevel>;
```

**Ring 0 TypeDef constraints**:
- `type_params` is empty (no polymorphic ADTs until Ring 1)
- All `ConstructorDef` entries have empty `fields` (enum-only)
- Example: `(deftype Color Red Green Blue)` -- three nullary constructors

### `ConstructorDef` and `FieldDef`

**Ring 0 status**: `ConstructorDef` exercised (nullary only). `FieldDef` defined but not exercised.

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FieldDef {
    pub name: Symbol,
    pub type_expr: TypeExpr,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstructorDef {
    pub name: Symbol,
    pub docstring: Option<String>,
    pub fields: Vec<FieldDef>,     // empty in Ring 0
    pub span: Span,
}
```

### `ReplInput`

**Ring 0 status**: `Defn`, `Expr`, `TypeDef` exercised.

```rust
#[derive(Debug, Clone)]
pub enum ReplInput {
    // --- Ring 0 exercised ---
    Defn(Defn),
    Expr(Expr),
    TypeDef {
        name: TypeName,
        docstring: Option<String>,
        type_params: Vec<Symbol>,
        constructors: Vec<ConstructorDef>,
        visibility: Visibility,
        span: Span,
    },

    // --- Defined, deferred ---
    DefnMulti { ... },              // Ring 2
    TraitDecl(TraitDecl),           // Ring 2
    TraitImpl(TraitImpl),           // Ring 2
}
```

### Types Defined but NOT Exercised in Ring 0

The following AST-related types exist in `interfaces.md` but are entirely deferred:

| Type | Ring |
|------|------|
| `DefnVariant` | Ring 2 (multi-signature functions) |
| `TraitDecl` | Ring 2 |
| `TraitImpl` | Ring 2 |
| `TraitMethodSig` | Ring 2 |
| `MacroClauseInfo` | Ring 3 |
| `MacroParam` | Ring 3 |
| `ImportSpec` | Ring 2 |
| `ExportSpec` | Ring 2 |
| `ImportNames` | Ring 2 |
| `ImplSexp` | Ring 2 |
| `ModuleStructure` | Ring 2 |
| `OverloadVariant` | Ring 2 (multi-signature dispatch) |
| `ConstrainedFn` | Ring 2 (constrained polymorphism) |

The following types live in the **binary crate** (not `cranelisp-types`) and are entirely Ring 2+:

| Type | Ring | Purpose |
|------|------|---------|
| `ModuleInfo` | Ring 2 | Per-module discovery metadata |
| `ModuleGraph` | Ring 2 | Module dependency graph + compile order |
| `InlineModuleDecl` | Ring 2 | Inline `(mod name ...)` extraction |
| `ModuleDecls` | Ring 2 | Extracted import/export/mod/platform declarations |
| `ModuleRegistry` | Ring 2 | Composes SymbolTable + codegen + structure + cache |

All types in `cranelisp-types` should be defined in full from Ring 0 (all variants present) so no rework is needed when later rings begin. Only the code paths that exercise them are deferred.

---

## Type System

### `Type`

**Ring 0 status**: Full enum defined. `Int`, `Bool`, `Float`, `Fn`, `Var` exercised. `ADT` exercised for enum-only types (nullary constructors as bare i64 tags).

```rust
pub type TypeId = u32;

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Type {
    // --- Ring 0 exercised ---
    Int,
    Bool,
    Float,
    Fn(Vec<Type>, Box<Type>),       // function types (no closures)
    Var(TypeId),                     // unification variables (inference internal)

    // --- Ring 0 exercised (limited) ---
    ADT(TypeName, Vec<Type>),       // Ring 0: Vec<Type> always empty (enum-only)

    // --- Defined, deferred ---
    String,                          // Ring 1
    TyConApp(TypeId, Vec<Type>),     // Ring 2+ (higher-kinded types)
}

impl Type {
    pub fn from_name(name: &str) -> Option<Type> {
        match name {
            "Int" => Some(Type::Int),
            "Bool" => Some(Type::Bool),
            "String" => Some(Type::String),
            "Float" => Some(Type::Float),
            _ => None,
        }
    }

    pub fn type_name(&self) -> Option<&'static str> {
        match self {
            Type::Int => Some("Int"),
            Type::Bool => Some("Bool"),
            Type::String => Some("String"),
            Type::Float => Some("Float"),
            _ => None,
        }
    }

    <!-- RESOLVED (Wave 1): is_heap() retained as a quick check. HeapCategory::classify() is the
     authoritative source for codegen decisions. is_heap() is documented as a convenience that
     may over-report (Fn and ADT are "potentially heap" even when not). Codegen must use classify(). -->
    pub fn is_heap(&self) -> bool {
        matches!(self, Type::String | Type::ADT(_, _) | Type::Fn(_, _))
    }
}
```

**Ring 0 notes on `Type`**:
- `Fn` in Ring 0 represents simple function types (no closure environments). The typechecker infers `Fn([Int, Int], Int)` for `(fn [a b] (+ a b))` when applied with Int arguments. The backend compiles these as bare function pointers.
- `Var(TypeId)` is inference-internal. All `Var` occurrences must be resolved to concrete types before codegen. If a `Var` reaches the backend, it is a bug (`unreachable!`).
- `ADT` in Ring 0 has an empty `Vec<Type>` (no type parameters). E.g., `ADT("Color", vec![])`. The tag is the runtime representation (bare i64, no heap).
- `is_heap()` returns `true` for `Fn` and `ADT`, but in Ring 0, `Fn` values are bare function pointers and enum ADTs are bare tags -- neither is heap-allocated. The heap classification logic in Ring 0 should use `HeapCategory::classify()` which accounts for nullary ADTs.
- `Type::String` is defined but the AST builder should reject `StringLit` in Ring 0. `from_name("String")` still returns `Some(Type::String)` to allow type annotations to parse, but using `String` values is a Ring 1 feature.

### `Scheme`

**Ring 0 status**: Exercised with empty `constraints`.

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Scheme {
    pub vars: Vec<TypeId>,
    pub constraints: HashMap<TypeId, Vec<TraitName>>,  // empty in Ring 0
    pub ty: Type,
}
```

**Ring 0 notes**: `let`-polymorphism is exercised: `(defn id [x] x)` generalizes to `Scheme { vars: [t0], constraints: {}, ty: Fn([Var(t0)], Var(t0)) }`. Trait constraints on type variables are a Ring 2 feature.

### `Subst` and Utility Functions

**Ring 0 status**: Fully exercised.

```rust
pub type Subst = HashMap<TypeId, Type>;

/// Apply a substitution to a type, replacing Var(id) with the mapped type.
pub fn apply(subst: &Subst, ty: &Type) -> Type { ... }

/// Collect free (unbound) type variables in a type.
pub fn free_vars(ty: &Type) -> HashSet<TypeId> { ... }
```

---

## TypeChecker to Backend Boundary

### `CheckResult`

**Ring 0 status**: Exercised with limited fields.

```rust
#[derive(Debug)]
pub struct CheckResult {
    // --- Ring 0 exercised ---
    pub method_resolutions: MethodResolutions,  // Ring 0: only BuiltinFn resolutions
    pub expr_types: HashMap<Span, Type>,        // Ring 0: used, but no heap classification needed
    pub warnings: Vec<Warning>,

    // --- Defined, deferred ---
    pub constrained_fn_names: HashSet<Symbol>,   // Ring 2 (constrained polymorphism)
    pub mono_defns: Vec<MonoDefn>,              // Ring 2 (monomorphisation)
    pub default_method_defns: Vec<Defn>,         // Ring 2 (default trait methods)
}
```

**Ring 0 notes**:
- `method_resolutions` in Ring 0 contains `ResolvedCall::BuiltinFn` entries for primitive operators (`+`, `-`, `*`, `/`, `=`, `<`, `>`). No `TraitMethod`, `SigDispatch`, or `AutoCurry` resolutions exist.
- `expr_types` maps expression spans to their inferred types. In Ring 0, this is used by the backend to determine the type of each subexpression. No heap classification is needed because Ring 0 has no heap types.
- `constrained_fn_names` and `mono_defns` are empty `HashSet`/`Vec` in Ring 0.
- `default_method_defns` is an empty `Vec` in Ring 0.

### `MethodResolutions` and `ResolvedCall`

**Ring 0 status**: `BuiltinFn` exercised. Others defined.

```rust
pub type MethodResolutions = HashMap<Span, ResolvedCall>;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ResolvedCall {
    // --- Ring 0 exercised ---
    BuiltinFn {
        name: Symbol,           // "+", "-", "*", "/", "=", "<", ">", "<=", ">=", "not"
        operand_type: Option<Type>,  // Wave 1: disambiguates Int/Float for arithmetic/comparison
    },

    // --- Defined, deferred ---
    TraitMethod {               // Ring 2
        trait_name: TraitName,
        method_name: Symbol,
        impl_type: TypeName,
        mangled_name: JitSymbol,
    },
    SigDispatch {               // Ring 2
        mangled_name: JitSymbol,
    },
    AutoCurry {                 // Ring 2
        target_name: Symbol,
        applied_count: usize,
    },
}

#[derive(Debug)]
pub struct MonoDefn {           // Ring 2
    pub defn: Defn,
    pub resolutions: MethodResolutions,
}
```

<!-- RESOLVED (Wave 1): Single authoritative operator table now lives in cranelisp-types/src/operator.rs.
     ring0_operators() returns all 10 Ring 0 operators with category, Int instruction, and Float instruction.
     operator_scheme() generates the type scheme from the category.
     Three categories: Arithmetic (a,a)->a, Comparison (a,a)->Bool, Boolean (Bool)->Bool.
     Typechecker and backend both reference this single source. -->

**Ring 0 note on primitive operators**: The typechecker resolves `(+ 1 2)` by recognizing `+` as a builtin and recording `ResolvedCall::BuiltinFn { name: "+".into() }` keyed by the call site's `Span`. The backend uses this to emit inline Cranelift IR (`iadd`, `isub`, `imul`, `sdiv`, `icmp`) rather than function calls. Ring 0 builtins include at minimum:
- Arithmetic: `+`, `-`, `*`, `/` (Int and Float)
- Comparison: `=`, `<`, `>`, `<=`, `>=` (returning Bool)
- Boolean: `not` (Bool -> Bool)

---

## Module System (Ring 0 Subset)

### `SymbolTable`

**Ring 0 status**: Exercised with a single module.

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SymbolTable {
    pub path: ModuleFullPath,                   // "user" in Ring 0
    pub symbols: HashMap<Symbol, ModuleEntry>,
}

impl SymbolTable {
    pub fn get(&self, name: &str) -> Option<&ModuleEntry> {
        self.symbols.get(name)
    }

    pub fn insert(&mut self, name: Symbol, entry: ModuleEntry) {
        self.symbols.insert(name, entry);
    }

    pub fn public_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry)> {
        self.symbols.iter().filter(|(_, e)| e.is_public())
    }
}
```

**Ring 0 constraint**: One `SymbolTable` exists for the implicit `"user"` module. It contains:
- Primitive operator entries (`+`, `-`, `*`, `/`, `=`, `<`, `>`, `<=`, `>=`, `not`)
- User-defined function entries (from `defn`)
- User-defined type entries (from `deftype`)
- Constructor entries (from `deftype`)

### `ModuleEntry`

**Ring 0 status**: `Def` (with `Primitive` and `UserFn` DefKind), `TypeDef`, `Constructor` exercised.

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ModuleEntry {
    // --- Ring 0 exercised ---
    Def {
        scheme: Scheme,
        visibility: Visibility,
        docstring: Option<String>,
        param_names: Vec<Symbol>,
        kind: DefKind,
    },
    TypeDef {
        info: TypeDefInfo,
        visibility: Visibility,
        constructor_scheme: Option<Scheme>,
        sexp: Option<Sexp>,
    },
    Constructor {
        type_name: Symbol,
        info: ConstructorInfo,
        scheme: Scheme,
        visibility: Visibility,
    },

    // --- Defined, deferred ---
    Import { source: FQSymbol },            // Ring 2
    Reexport { source: FQSymbol },          // Ring 2
    TraitDecl {                             // Ring 2
        decl: TraitDecl,
        visibility: Visibility,
        sexp: Option<Sexp>,
    },
    Macro {                                 // Ring 3
        name: Symbol,
        clauses: Vec<MacroClauseInfo>,
        docstring: Option<String>,
        visibility: Visibility,
        sexp: Option<Sexp>,
        source: Option<String>,
    },
    PlatformDecl {                          // Ring 4
        dll_path: PathBuf,
        platform_module: ModuleFullPath,
    },
    Ambiguous,                              // Ring 2
}

impl ModuleEntry {
    pub fn is_public(&self) -> bool { ... }
}
```

### `DefKind`

**Ring 0 status**: `Primitive` (Inline only) and `UserFn` (no constrained) exercised. `SpecialForm` may be exercised for REPL introspection.

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DefKind {
    // --- Ring 0 exercised ---
    SpecialForm {
        description: String,        // "if", "let", "defn", "deftype", "match", "fn"
    },
    Primitive {
        primitive_kind: PrimitiveKind,
        jit_name: Option<JitSymbol>,    // None for Inline primitives
    },
    UserFn {
        constrained_fn: Option<ConstrainedFn>,  // None in Ring 0
    },

    // --- Defined, deferred ---
    Overloaded {                    // Ring 2
        variants: Vec<OverloadVariant>,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PrimitiveKind {
    // --- Ring 0 exercised ---
    Inline,                         // +, -, *, /, =, <, >, <=, >=, not

    // --- Defined, deferred ---
    Extern,                         // Ring 1 (string intrinsics, etc.)
    PlatformEffect,                 // Ring 4
}
```

**Ring 0 notes on primitives**: All Ring 0 arithmetic and comparison operators are `PrimitiveKind::Inline` -- the backend emits Cranelift IR directly at the call site (e.g., `iadd` for `+`, `icmp` for `=`). No `Extern` or `PlatformEffect` primitives exist in Ring 0.

### ADT Support Types

**Ring 0 status**: Exercised for enum-only types.

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeDefInfo {
    pub name: TypeName,             // e.g., TypeName::from("Color")
    pub type_params: Vec<Symbol>,   // empty in Ring 0
    pub constructors: Vec<ConstructorInfo>,
    pub docstring: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstructorInfo {
    pub name: Symbol,               // e.g., Symbol::from("Red")
    pub tag: usize,                 // 0, 1, 2, ...
    pub fields: Vec<FieldInfo>,     // empty in Ring 0 (enum-only)
    pub docstring: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FieldInfo {
    pub name: Symbol,
    pub ty: Type,
}
```

**Ring 0 constraint**: All constructors are nullary (empty `fields`). The runtime representation is a bare `i64` tag value. No heap allocation. Example: `(deftype Color Red Green Blue)` produces:
- `TypeDefInfo { name: "Color", type_params: [], constructors: [Red(tag=0), Green(tag=1), Blue(tag=2)] }`
- Three `ModuleEntry::Constructor` entries with `Scheme { vars: [], constraints: {}, ty: ADT("Color", []) }`

---

## Heap Classification

**Ring 0 status**: Defined. Returns `NeverHeap` for all Ring 0 types.

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HeapCategory {
    NeverHeap,      // Int, Bool, Float, nullary constructors
    AlwaysHeap,     // String, closures, data constructors with fields (Ring 1+)
    Mixed,          // polymorphic types, some ADTs with mixed constructors (Ring 1+)
}

impl HeapCategory {
    pub fn classify(ty: &Type) -> HeapCategory { ... }
}
```

**Ring 0 note**: In Ring 0, every concrete type classifies as `NeverHeap`. The `classify` function should still be implemented correctly for all types (returning `AlwaysHeap` for `Type::String`, etc.) because later rings depend on it. Ring 0 just happens to never encounter heap types.

---

## Pipeline Configuration

### `CompileMode`

**Ring 0 status**: `Interactive` and `Batch` exercised. `Release` defined, deferred to Phase H.

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompileMode {
    Interactive,    // GOT-indirect calls for hot-reload, REPL
    Batch,          // direct function calls, compile to module cache
    Release,        // Ring 4+ / Phase H: whole-program optimisation, standalone binary
}
```

**Ring 0 notes**: Two of three modes are exercised from Ring 0:
- `Interactive` is used by the REPL — GOT-indirect calls enable hot-reload
- `Batch` is used by integration tests and batch compilation — direct calls, no GOT
- `Release` is defined but deferred to Phase H (Tier 2 backend for optimised standalone binaries)
- The key difference between Interactive and Batch: `Batch` emits `call` instructions directly; `Interactive` emits `load` from GOT slot then `call_indirect`

### `CompileResult`

**Ring 0 status**: Exercised.

```rust
pub struct CompileResult {
    pub symbols: Vec<(Symbol, ModuleEntry)>,
    pub codegen: Vec<(Symbol, DefCodegen)>,
    pub warnings: Vec<Warning>,
}
```

---

## Backend Types (in `cranelisp-backend`)

### `ModuleCodegenState`

**Ring 0 status**: Exercised (GOT allocation for Interactive mode).

```rust
pub struct ModuleCodegenState {
    pub got_table: Option<Box<[*const u8; GOT_TABLE_SIZE]>>,
    pub next_got_slot: usize,
    pub def_codegen: HashMap<Symbol, DefCodegen>,
}

pub const GOT_TABLE_SIZE: usize = 1024;
```

### `DefCodegen`

**Ring 0 status**: Core fields exercised.

```rust
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct DefCodegen {
    // --- Ring 0 exercised ---
    pub got_slot: Option<usize>,
    #[serde(skip)]
    pub code_ptr: Option<*const u8>,
    pub defn: Option<Defn>,
    pub clif_ir: Option<String>,        // for /clif REPL command
    pub code_size: Option<usize>,
    #[serde(skip)]
    pub compile_duration: Option<std::time::Duration>,
    pub param_count: Option<usize>,

    // --- Defined, lightly used in Ring 0 ---
    pub source: Option<String>,         // stored for /source REPL command
    pub sexp: Option<Sexp>,             // stored for /sexp REPL command
    pub disasm: Option<String>,         // for /disasm REPL command
}
```

### `CacheMetadata`

**Ring 0 status**: Defined but not exercised (Ring 4 only).

```rust
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CacheMetadata {
    pub content_hash: Option<String>,
    #[serde(skip)]
    pub cache_method_resolutions: MethodResolutions,
    #[serde(skip)]
    pub cache_expr_types: HashMap<Span, Type>,
}
```

### `NULLARY_TAG_THRESHOLD`

**Ring 0 status**: Exercised (all ADT values are below threshold).

```rust
pub const NULLARY_TAG_THRESHOLD: usize = 1024;
```

---

## Frontend Traits

### `MacroExpander`

<!-- RESOLVED (Wave 1): MacroExpander trait lives in cranelisp-types (pipeline.rs).
     Dependency inversion: frontend depends on the trait, binary crate implements it.
     NoOpExpander also provided in cranelisp-types for Ring 0 convenience. -->

**Ring 0 status**: Defined. Ring 0 uses a no-op implementation.

```rust
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

**Ring 0 implementation**: The binary crate provides a `NoOpExpander` that:
- `is_macro()` always returns `false`
- `expand()` returns `Err(CranelispError::ModuleError { message: "macros not available".into(), file: None, span })`

---

## Summary: Ring 0 Type Exercise Matrix

| Type | Crate | Ring 0 Status |
|------|-------|---------------|
| `Span` | types | **Full** |
| `Symbol` | types | **Full** |
| `ModuleFullPath` | types | Set to `"user"` only |
| `FQSymbol` | types | Lightly used |
| `CranelispError` | types | `ParseError`, `TypeError`, `CodegenError` |
| `Warning` | types | **Full** |
| `Sexp` | types | All except `Str` |
| `Expr` | types | 10 of 12 variants |
| `Pattern` | types | **Full** (nullary constructors only) |
| `MatchArm` | types | **Full** |
| `TypeExpr` | types | `Named`, `FnType`, `TypeVar` |
| `TopLevel` | types | `Defn`, `TypeDef` (enum-only) |
| `Defn` | types | **Full** |
| `ConstructorDef` | types | Nullary only (empty `fields`) |
| `ReplInput` | types | `Defn`, `Expr`, `TypeDef` |
| `Type` | types | `Int`, `Bool`, `Float`, `Fn`, `Var`, `ADT` (enum-only) |
| `Scheme` | types | Empty `constraints` |
| `Subst` | types | **Full** |
| `CheckResult` | types | `method_resolutions`, `expr_types`, `warnings` |
| `ResolvedCall` | types | `BuiltinFn` only |
| `SymbolTable` | types | Single module |
| `ModuleEntry` | types | `Def`, `TypeDef`, `Constructor` |
| `DefKind` | types | `SpecialForm`, `Primitive` (Inline), `UserFn` (no constrained) |
| `HeapCategory` | types | Defined; always `NeverHeap` in Ring 0 |
| `CompileMode` | types | **Full** |
| `CompileResult` | types | **Full** |
| `ModuleCodegenState` | backend | **Full** |
| `DefCodegen` | backend | Core fields |
| `GOT_TABLE_SIZE` | backend | **Full** |
| `NULLARY_TAG_THRESHOLD` | backend | **Full** |
| `MacroExpander` | **types** | No-op impl |
| `NoOpExpander` | types | Ring 0 default |
| `ReplCheckResult` | types | **Full** |
| `ReplSnapshot` | types | **Full** |
| `PrimitiveDef` | types | **Full** (replaces BuiltinOperator, Wave 3.5) |

<!-- RESOLVED (Wave 1): REPL error recovery uses ReplSnapshot (defined in cranelisp-types/src/check.rs).
     Protocol:
     1. Binary crate calls typechecker.snapshot() before each REPL input.
     2. If typecheck fails: restore snapshot, report error, continue.
     3. If typecheck succeeds but codegen fails: restore snapshot, report error, continue.
     4. If both succeed: discard snapshot, commit state.
     ReplSnapshot captures: next_type_id, symbol_count, subst_len.
     The typechecker owns snapshot()/restore() methods; binary crate is the caller. -->

## Wave 1 Architectural Decisions (Sprint 1)

Resolved during Wave 1 implementation. These decisions are binding for Wave 2+ skills.

### 1. MacroExpander placement → `cranelisp-types`

The `MacroExpander` trait and `NoOpExpander` struct live in `cranelisp-types/src/pipeline.rs`. This is dependency inversion: the frontend depends on the trait (for AST building), the binary crate provides the real implementation (Ring 3). `NoOpExpander` is the Ring 0 default.

### 2. Ring 0 primitives (replaces operator dispatch — Wave 3.5)

**Supersedes**: The original operator type scheme categories (3 polymorphic categories) and the `operand_type` disambiguation. Per principle 8, operators like `+` are a Ring 2 feature (trait dispatch via `Num.+`). Ring 0 exposes only monomorphic named primitives.

**19 monomorphic primitives**, defined in `cranelisp-types/src/operator.rs` via `ring0_primitives()`:

| Primitive | Type | Cranelift instruction |
|-----------|------|----------------------|
| `add-i64` | `(Fn [Int Int] Int)` | `iadd` |
| `sub-i64` | `(Fn [Int Int] Int)` | `isub` |
| `mul-i64` | `(Fn [Int Int] Int)` | `imul` |
| `div-i64` | `(Fn [Int Int] Int)` | `sdiv` |
| `add-f64` | `(Fn [Float Float] Float)` | `fadd` |
| `sub-f64` | `(Fn [Float Float] Float)` | `fsub` |
| `mul-f64` | `(Fn [Float Float] Float)` | `fmul` |
| `div-f64` | `(Fn [Float Float] Float)` | `fdiv` |
| `eq-i64` | `(Fn [Int Int] Bool)` | `icmp_eq` |
| `lt-i64` | `(Fn [Int Int] Bool)` | `icmp_slt` |
| `gt-i64` | `(Fn [Int Int] Bool)` | `icmp_sgt` |
| `le-i64` | `(Fn [Int Int] Bool)` | `icmp_sle` |
| `ge-i64` | `(Fn [Int Int] Bool)` | `icmp_sge` |
| `eq-f64` | `(Fn [Float Float] Bool)` | `fcmp_eq` |
| `lt-f64` | `(Fn [Float Float] Bool)` | `fcmp_lt` |
| `gt-f64` | `(Fn [Float Float] Bool)` | `fcmp_gt` |
| `le-f64` | `(Fn [Float Float] Bool)` | `fcmp_le` |
| `ge-f64` | `(Fn [Float Float] Bool)` | `fcmp_ge` |
| `not` | `(Fn [Bool] Bool)` | `bxor` (with 1) |

**Key design properties:**

1. **Monomorphic**: Every primitive has a fixed, concrete type. No polymorphic type variables, no `operand_type` disambiguation needed.
2. **Name encodes operation**: The primitive name uniquely determines both the operand types and the Cranelift instruction. No lookup tables needed — just a match on name.
3. **Registered as `DefKind::Primitive { primitive_kind: PrimitiveKind::Inline }`** in the symbol table, not as operators. No `builtin_operators: HashSet` needed.
4. **No special inference handling**: Primitives are normal function entries in the symbol table. `infer_apply` uses standard unification. The typechecker records `ResolvedCall::BuiltinFn { name }` for calls to primitives so the backend knows to inline them.
5. **Accretive into Ring 2**: These primitives survive permanently. Ring 2 adds `Num.+` which dispatches to `add-i64`/`add-f64` via trait resolution. Ring 0 tests using `(add-i64 1 2)` remain as regression baselines.

**Removed infrastructure:**
- `OperatorCategory` enum
- `BuiltinOperator` struct
- `ring0_operators()` function
- `operator_scheme()` function
- `resolve_builtin_operator()` in infer.rs
- `builtin_operators: HashSet<Symbol>` on `TypeChecker`
- `operand_type: Option<Type>` on `ResolvedCall::BuiltinFn`

**Data flow:**
```
ring0_primitives() → PrimitiveDef { name, ty, cranelift_op }
  ↓                        ↓                    ↓
typecheck registers     scheme = mono(ty)    backend matches
in symbol table         no poly vars         on cranelift_op
  ↓
infer_apply sees DefKind::Primitive → records ResolvedCall::BuiltinFn { name }
  ↓
backend's compile_apply checks BuiltinFn → emits IR for cranelift_op
```

### 3. (Superseded by §2 — operand_type no longer needed)

`ResolvedCall::BuiltinFn` now carries only `name: Symbol`. The `operand_type` field is removed because the primitive name already encodes the operand type (`add-i64` is always Int, `add-f64` is always Float).

### 4. ReplCheckResult → new type in `cranelisp-types`

`ReplCheckResult` (in `check.rs`) carries per-input results for REPL display: `ty`, `scheme`, `method_resolutions`, `expr_types`, `warnings`, `type_defs`, `constructor_to_type`. Distinct from batch `CheckResult` because REPL processes one form at a time and needs the inferred type/scheme for display.

### 5. type_defs/constructor_to_type → added to CheckResult

`CheckResult` now includes `type_defs: HashMap<TypeName, TypeDefInfo>` and `constructor_to_type: HashMap<Symbol, TypeName>`. The backend needs these for ADT tag lookup during match codegen. No need for a separate `TypeContext` struct.

### 6. REPL error recovery → ReplSnapshot

`ReplSnapshot` (in `check.rs`) captures typechecker state before each REPL input. On failure (typecheck or codegen), the binary crate calls `restore()` to roll back. Fields: `next_type_id`, `symbol_count`, `subst_len`. The typechecker owns the snapshot/restore mechanism; the binary crate is the caller.

### 7. Warning type → struct (confirmed)

`Warning { message: String, span: Span }` — a struct, not an enum. Simple and sufficient for Ring 0. If warning categories are needed later, it can be extended with a `kind` field.

### 8. Borrow-splitting → explicit parameters for unify/occurs_check

The typechecker's `unify()`, `occurs_check()`, `apply_subst()`, and `fresh_var()` take explicit `&mut Subst` and `&mut TypeId` parameters rather than `&mut self`. This avoids the prototype's clone-to-avoid-borrow debt (audit HIGH-3). The `TypeChecker` struct holds these fields, but hot-path functions borrow them independently.

Pattern:
```rust
// Instead of: self.unify(t1, t2) where self is &mut TypeChecker
// Use: unify(&mut self.subst, &mut self.next_id, t1, t2)
fn unify(subst: &mut Subst, next_id: &mut TypeId, t1: &Type, t2: &Type) -> Result<(), CranelispError> { ... }
```

### 9. Operator wrappers → deferred to Ring 1

Operators-as-values (e.g., `(let [f +] (f 1 2))`) require closures to wrap bare function pointers. Since closures are Ring 1, operator wrappers are deferred to Ring 1. In Ring 0, using an operator in a non-call position is a type error.

### 10. Panic handler → `panic!()` + `catch_unwind` for Ring 0

Ring 0 has no nested JIT→Rust→JIT calls (no closures, no callbacks). `cranelisp_panic` uses Rust `panic!()`. The binary crate wraps JIT execution in `catch_unwind` to recover from match exhaustiveness failures without killing the REPL session. Ring 1+ (with closures and callbacks) will require a thread-local error flag for deeply nested cases.

## Action Items for Ring 0 Implementation

1. **`/arch`**: Add Cranelift 0.125 dependencies to `cranelisp-backend/Cargo.toml` when the `/backend` skill begins work.
2. **All skills**: Define the full enum/struct in `cranelisp-types` from the start. Ring 0 exercises a subset, but the full type definitions prevent rework.
3. **`/frontend`**: Reader must parse all `Sexp` variants (including `Str`). AST builder rejects non-Ring-0 forms with clear errors.
4. **`/typecheck`**: Implement the full `Type` enum and `from_name()`/`type_name()`. Ring 0 inference only produces `Int`, `Bool`, `Float`, `Fn`, `Var`, and nullary `ADT`.
5. **`/backend`**: Ring 0 codegen operates exclusively on non-heap types. No `alloc_with_rc`, no RC emission, no closure environments.
6. **`/qa`**: Integration tests should exercise all Ring 0 acceptance criteria listed in `roadmap.md` lines 24--33.
