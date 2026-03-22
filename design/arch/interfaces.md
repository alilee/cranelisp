# Interfaces — Boundary Type Definitions

Complete Rust type signatures for every type that crosses a crate boundary. These are the contracts that all compiler skills implement against. All types live in `cranelisp-types`.

Types are organized by pipeline stage, following the data flow: source text -> Sexp -> AST -> CheckResult -> executable code.

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

All identifiers use newtypes to prevent accidental mixing. Generated via a `string_newtype!` macro that derives `Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize` and implements `Deref<Target=str>`, `From<String>`, `From<&str>`, `AsRef<str>`, `Display`.

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
/// Enables filtering, counting by category, and future `-Werror=<kind>` support.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum WarningKind {
    /// A binding is defined but never referenced.
    UnusedBinding,
    /// A match arm can never be reached (dominated by earlier patterns).
    UnreachableArm,
    /// A binding shadows an existing binding in an outer scope.
    ShadowedName,
    /// Catch-all for diagnostics that don't fit a specific category.
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

## Reader Output (source text -> Sexp)

Produced by `cranelisp-frontend`, consumed by `cranelisp-frontend` (AST builder) and stored for introspection.

```rust
/// S-expression: the reader's output. 7 variants covering all syntactic forms.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Sexp {
    /// Symbol: `foo`, `+`, `defn`, `core/map`
    Symbol(String, Span),
    /// Integer literal: `42`, `-3`
    Int(i64, Span),
    /// Float literal: `3.14`, `-0.5`
    Float(f64, Span),
    /// Boolean literal: `true`, `false`
    Bool(bool, Span),
    /// String literal: `"hello"`
    Str(String, Span),
    /// Parenthesized list: `(f x y)`, `(defn add [a b] (+ a b))`
    List(Vec<Sexp>, Span),
    /// Bracketed list: `[a b c]`, `[:Int x :Int y]`
    Bracket(Vec<Sexp>, Span),
}

impl Sexp {
    /// Returns the span of this S-expression.
    pub fn span(&self) -> Span { ... }
}
```

## AST (Sexp -> typed AST)

Produced by `cranelisp-frontend`, consumed by `cranelisp-typecheck` and `cranelisp-backend`.

### Expressions

```rust
/// Expression AST node. Every variant carries a Span.
///
/// Expression AST node. Every variant carries a Span.
///
/// Spec traceability:
///   IntLit, FloatLit, BoolLit, StringLit — spec §4.1 (Literals)
///   Var — spec §4.2 (Variable Reference)
///   Let — spec §4.3 (Let Expression)
///   If — spec §4.4 (If Expression)
///   Lambda — spec §4.5 (Lambda Expression)
///   Apply — spec §4.6 (Function Application)
///   Match — spec §4.8 (Match Expression)
///   Annotate — spec §4.9 (Type Annotation)
///   VecLit — spec §4.10 (Vec Literal)
///   Trace — spec §12 (Runtime Model, implementation extension)
///   RunTests — REPL-only special form (no spec section)
///
/// Ring 0: IntLit, FloatLit, BoolLit, Var, Let, If, Lambda, Apply, Match, Annotate
/// Ring 1: StringLit, VecLit (heap-allocated)
/// Ring 4: Trace, RunTests (effects)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Expr {
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
    StringLit {
        value: String,
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
        /// true for compiler-generated match (e.g. from macro expansion)
        compiler_generated: bool,
    },
    VecLit {
        elements: Vec<Expr>,
        span: Span,
    },
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
}

impl Expr {
    /// Returns the span of this expression.
    pub fn span(&self) -> Span { ... }
}
```

### Patterns

```rust
/// Pattern in a match expression.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Pattern {
    /// Constructor pattern: `(Some x)`, `None`, `(Cons h t)`
    Constructor {
        name: Symbol,
        bindings: Vec<Symbol>,
        span: Span,
    },
    /// Wildcard: `_`
    Wildcard {
        span: Span,
    },
    /// Variable binding: `x` (binds the scrutinee to a name)
    Var {
        name: Symbol,
        span: Span,
    },
}

/// One arm of a match expression.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Expr,
    pub span: Span,
}
```

### Top-Level Definitions

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Visibility {
    Public,
    Private,
}

/// Function definition.
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

/// One variant of a multi-signature function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DefnVariant {
    pub params: Vec<Symbol>,
    pub param_annotations: Vec<Option<TypeExpr>>,
    pub body: Expr,
    pub span: Span,
}

/// Type expression in annotations and trait signatures.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TypeExpr {
    /// Named type: `Int`, `Bool`, `String`
    Named(TypeName),
    /// Self type in trait methods: `Self`
    SelfType,
    /// Function type: `(Fn [Int Int] Bool)`
    FnType(Vec<TypeExpr>, Box<TypeExpr>),
    /// Type variable: `:a`, `:b`
    TypeVar(Symbol),
    /// Applied type constructor: `(Option Int)`, `(List :a)`
    Applied(TypeName, Vec<TypeExpr>),
}

/// Trait method signature.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitMethodSig {
    pub name: Symbol,
    pub docstring: Option<String>,
    pub params: Vec<TypeExpr>,
    pub ret_type: TypeExpr,
    pub span: Span,
    /// Index of HKT parameter if this method uses higher-kinded types
    pub hkt_param_index: Option<usize>,
    /// Parameter names for default implementation
    pub default_param_names: Vec<Symbol>,
    /// Default method body as Sexp (compiled on demand)
    pub default_body: Option<Sexp>,
}

/// Trait declaration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitDecl {
    pub name: TraitName,
    pub docstring: Option<String>,
    pub type_params: Vec<Symbol>,
    pub methods: Vec<TraitMethodSig>,
    pub visibility: Visibility,
    pub span: Span,
}

/// Trait implementation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitImpl {
    pub trait_name: TraitName,
    pub target_type: TypeName,
    pub type_args: Vec<Symbol>,
    pub type_constraints: Vec<(Symbol, TraitName)>,
    pub methods: Vec<Defn>,
    pub span: Span,
}

/// Field in a data constructor.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FieldDef {
    pub name: Symbol,
    pub type_expr: TypeExpr,
}

/// Data constructor (one variant of a sum type, or the sole constructor of a product type).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstructorDef {
    pub name: Symbol,
    pub docstring: Option<String>,
    pub fields: Vec<FieldDef>,
    pub span: Span,
}

/// Top-level form: the unit of compilation.
///
/// Ring 0: Defn, DefnMulti, TypeDef (enum-only), TraitDecl (structural only)
/// Ring 1: TypeDef (with heap fields)
/// Ring 2: TraitDecl (full), TraitImpl, module declarations (Mod, Import, Export)
/// Ring 3: Macro definitions (handled by MacroExpander, not represented here)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TopLevel {
    Defn(Defn),
    DefnMulti {
        name: Symbol,
        docstring: Option<String>,
        variants: Vec<DefnVariant>,
        visibility: Visibility,
        span: Span,
    },
    TraitDecl(TraitDecl),
    TraitImpl(TraitImpl),
    TypeDef {
        name: TypeName,
        docstring: Option<String>,
        type_params: Vec<Symbol>,
        constructors: Vec<ConstructorDef>,
        visibility: Visibility,
        span: Span,
    },
}

/// A complete compilation unit: all top-level forms from one module.
pub type Program = Vec<TopLevel>;

/// REPL-specific input: wraps TopLevel forms plus bare expressions.
#[derive(Debug, Clone)]
pub enum ReplInput {
    Defn(Defn),
    DefnMulti {
        name: Symbol,
        docstring: Option<String>,
        variants: Vec<DefnVariant>,
        visibility: Visibility,
        span: Span,
    },
    Expr(Expr),
    TraitDecl(TraitDecl),
    TraitImpl(TraitImpl),
    TypeDef {
        name: TypeName,
        docstring: Option<String>,
        type_params: Vec<Symbol>,
        constructors: Vec<ConstructorDef>,
        visibility: Visibility,
        span: Span,
    },
}
```

## Type System

Internal to `cranelisp-typecheck`, but crosses to `cranelisp-backend` via `CheckResult`.

```rust
/// Type variable identifier. Narrow to u32 — 4 billion type vars is sufficient.
pub type TypeId = u32;

/// Concrete type.
///
/// All variants exist from Ring 0. Rings 0 exercises Int, Bool, Float, simple Fn.
/// Ring 1 adds String, ADT, Fn-with-closures. Ring 2 adds constrained Var usage.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Type {
    Int,
    Bool,
    String,
    Float,
    /// Function type: param types -> return type
    Fn(Vec<Type>, Box<Type>),
    /// Algebraic data type: type name + type arguments
    /// e.g. ADT(TypeName::from("Option"), [Type::Int]) for Option Int
    ADT(TypeName, Vec<Type>),
    /// Unification variable (inference internal; resolved before codegen)
    Var(TypeId),
    /// Type constructor application (for higher-kinded types)
    TyConApp(TypeId, Vec<Type>),
}

impl Type {
    /// Centralized primitive name -> Type mapping.
    /// Addresses audit LOW-1: eliminates 9 duplicate match blocks.
    pub fn from_name(name: &str) -> Option<Type> {
        match name {
            "Int" => Some(Type::Int),
            "Bool" => Some(Type::Bool),
            "String" => Some(Type::String),
            "Float" => Some(Type::Float),
            _ => None,
        }
    }

    /// Centralized Type -> display name mapping.
    pub fn type_name(&self) -> Option<&'static str> {
        match self {
            Type::Int => Some("Int"),
            Type::Bool => Some("Bool"),
            Type::String => Some("String"),
            Type::Float => Some("Float"),
            _ => None,
        }
    }

    /// Returns true if this type requires heap allocation at runtime.
    pub fn is_heap(&self) -> bool {
        matches!(self, Type::String | Type::ADT(_, _) | Type::Fn(_, _))
    }
}

/// Polymorphic type scheme: universally quantified type with optional trait constraints.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Scheme {
    /// Quantified type variables
    pub vars: Vec<TypeId>,
    /// Trait constraints on type variables: TypeId -> list of required trait names
    pub constraints: HashMap<TypeId, Vec<TraitName>>,
    /// The underlying type
    pub ty: Type,
}

/// Type substitution: mapping from type variables to concrete types.
pub type Subst = HashMap<TypeId, Type>;

/// Apply a substitution to a type, replacing Var(id) with the mapped type.
pub fn apply(subst: &Subst, ty: &Type) -> Type { ... }

/// Collect free (unbound) type variables in a type.
pub fn free_vars(ty: &Type) -> HashSet<TypeId> { ... }
```

## TypeChecker -> Backend Boundary

Produced by `cranelisp-typecheck`, consumed by `cranelisp-backend`.

```rust
/// Result of type checking a compilation unit.
/// This is the primary boundary type between typecheck and backend.
///
/// Self-contained: the backend can produce code from CheckResult + Program alone,
/// with no hidden state from the typechecker (NFR C.5.3 — backend-agnostic boundary).
#[derive(Debug)]
pub struct CheckResult {
    /// How each call site was resolved (trait dispatch, overload, auto-curry, builtin)
    pub method_resolutions: MethodResolutions,
    /// Names of constrained polymorphic functions requiring monomorphisation
    pub constrained_fn_names: HashSet<Symbol>,
    /// Monomorphised function definitions generated during checking
    pub mono_defns: Vec<MonoDefn>,
    /// Type of every expression, keyed by span (for codegen heap classification)
    pub expr_types: HashMap<Span, Type>,
    /// Default trait method implementations expanded during checking
    pub default_method_defns: Vec<Defn>,
    /// Non-fatal warnings accumulated during checking
    pub warnings: Vec<Warning>,
    /// All ADT definitions encountered in this compilation unit.
    /// Backend needs this for constructor allocation, match discrimination, and drop glue.
    /// Ring 1+. (Resolves deferred item M-2.)
    pub type_defs: HashMap<TypeName, TypeDefInfo>,
    /// Maps each constructor name to its parent type name.
    /// Backend uses this to look up tag, field count, and field types for a constructor.
    /// Ring 1+. (Resolves deferred item M-2.)
    pub constructor_to_type: HashMap<Symbol, TypeName>,
}

/// Map from call site span to how that call was resolved.
pub type MethodResolutions = HashMap<Span, ResolvedCall>;

/// How a function call was resolved by the typechecker.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ResolvedCall {
    /// Resolved to a trait method implementation
    TraitMethod {
        trait_name: TraitName,
        method_name: Symbol,
        impl_type: TypeName,
        mangled_name: JitSymbol,
    },
    /// Resolved to a specific multi-sig variant
    SigDispatch {
        mangled_name: JitSymbol,
    },
    /// Resolved to an auto-curried partial application
    AutoCurry {
        target_name: Symbol,
        applied_count: usize,
    },
    /// Resolved to a builtin function
    BuiltinFn {
        name: Symbol,
    },
}

/// A monomorphised function definition with its specific method resolutions.
/// Named struct, not a bare tuple — addresses audit MED-3.
#[derive(Debug)]
pub struct MonoDefn {
    /// The monomorphised function definition
    pub defn: Defn,
    /// Method resolutions specific to this monomorphisation
    pub resolutions: MethodResolutions,
    /// Per-expression types for this monomorphisation, keyed by AST span.
    /// The backend uses these instead of the program-wide expr_types map
    /// so that each specialization compiles against its concrete types.
    pub expr_types: HashMap<Span, Type>,
}
```

## Module System

### Symbol Table

Decomposed from the prototype's `CompiledModule`. Contains only symbol metadata — no GOT, no code pointers, no cache fields.

```rust
/// Per-module symbol table. Pure data — no runtime state.
/// Owned by TypeChecker, read by Backend for type information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SymbolTable {
    pub path: ModuleFullPath,
    pub symbols: HashMap<Symbol, ModuleEntry>,
}

impl SymbolTable {
    pub fn get(&self, name: &str) -> Option<&ModuleEntry> {
        self.symbols.get(name)
    }

    pub fn insert(&mut self, name: Symbol, entry: ModuleEntry) {
        self.symbols.insert(name, entry);
    }

    /// Returns all public symbols.
    pub fn public_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry)> {
        self.symbols.iter().filter(|(_, e)| e.is_public())
    }
}

/// Module structural metadata: file paths, declarations, imports, exports.
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
/// No `meta: Option<SymbolMeta>` field — DefKind is the sole classification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ModuleEntry {
    /// A definition: function, primitive, special form, constructor scheme, trait method.
    Def {
        scheme: Scheme,
        visibility: Visibility,
        docstring: Option<String>,
        param_names: Vec<Symbol>,
        kind: DefKind,
    },
    /// An imported name from another module.
    Import {
        source: FQSymbol,
    },
    /// A re-exported name from another module.
    Reexport {
        source: FQSymbol,
    },
    /// A type definition (deftype).
    TypeDef {
        info: TypeDefInfo,
        visibility: Visibility,
        constructor_scheme: Option<Scheme>,
        sexp: Option<Sexp>,
    },
    /// A trait declaration (deftrait).
    TraitDecl {
        decl: TraitDecl,
        visibility: Visibility,
        sexp: Option<Sexp>,
    },
    /// A constructor (from a deftype).
    Constructor {
        type_name: Symbol,
        info: ConstructorInfo,
        scheme: Scheme,
        visibility: Visibility,
    },
    /// A macro definition (defmacro).
    Macro {
        name: Symbol,
        clauses: Vec<MacroClauseInfo>,
        docstring: Option<String>,
        visibility: Visibility,
        sexp: Option<Sexp>,
        source: Option<String>,
    },
    /// A platform DLL declaration.
    PlatformDecl {
        dll_path: PathBuf,
        platform_module: ModuleFullPath,
    },
    /// A bare name that became ambiguous (two different sources registered it).
    Ambiguous,
}

impl ModuleEntry {
    /// Returns true if this entry is publicly visible.
    pub fn is_public(&self) -> bool { ... }
}
```

### Definition Classification

```rust
/// What kind of definition a symbol is. Sole classification — no separate SymbolMeta.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DefKind {
    /// A special form (if, let, defn, ...).
    SpecialForm {
        description: String,
    },
    /// A built-in primitive (inline IR, extern FFI, or platform effect).
    Primitive {
        primitive_kind: PrimitiveKind,
        jit_name: Option<JitSymbol>,
    },
    /// A user-defined function.
    UserFn {
        constrained_fn: Option<ConstrainedFn>,
    },
    /// Multi-sig overloaded function base name.
    Overloaded {
        variants: Vec<OverloadVariant>,
    },
}

/// Classification of primitive functions.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PrimitiveKind {
    /// Inlined as Cranelift IR at the call site
    Inline,
    /// Calls an extern Rust function via JIT symbol
    Extern,
    /// Platform effect (dispatched through IO trampoline)
    PlatformEffect,
}

/// One variant of an overloaded (multi-sig) function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OverloadVariant {
    pub param_types: Vec<Type>,
    pub ret_type: Type,
    pub mangled_name: Symbol,
}

/// A constrained polymorphic function awaiting monomorphisation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstrainedFn {
    pub defn: Defn,
    pub scheme: Scheme,
}
```

### ADT Support Types

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
}

/// Information about a constructor field.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FieldInfo {
    pub name: Symbol,
    pub ty: Type,
}
```

### Macro Support Types

```rust
/// Information about a single macro clause (for multi-clause defmacro).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MacroClauseInfo {
    pub params: Vec<MacroParam>,
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
```

### Import/Export

```rust
/// What names to import from a module.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ImportNames {
    /// Import specific names: `[Some None]`
    Specific(Vec<Symbol>),
    /// Import all public names: `[*]`
    Glob,
    /// Import all members of a type or trait: `[Display.*]`
    MemberGlob(Symbol),
    /// No names — alias-only: `[]`
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
```

## Backend Types (in `cranelisp-backend`)

These types live in `cranelisp-backend`, not in `cranelisp-types`, because they contain runtime state.

```rust
/// Per-module codegen state. Owns GOT and code artifacts.
/// Lives in cranelisp-backend, not cranelisp-types.
pub struct ModuleCodegenState {
    /// Global offset table: function pointer indirection for hot-reload
    pub got_table: Option<Box<[*const u8; GOT_TABLE_SIZE]>>,
    pub next_got_slot: usize,
    /// Per-definition codegen artifacts
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

/// Cache metadata for a compiled module. Ring 4 only.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CacheMetadata {
    pub content_hash: Option<String>,
    #[serde(skip)]
    pub cache_method_resolutions: MethodResolutions,
    #[serde(skip)]
    pub cache_expr_types: HashMap<Span, Type>,
}

/// Named constant for GOT table size.
pub const GOT_TABLE_SIZE: usize = 1024;

/// Named constant for nullary constructor tag threshold.
/// Values below this are nullary tags; values above are heap pointers.
pub const NULLARY_TAG_THRESHOLD: usize = 1024;
```

## Pipeline Configuration

```rust
/// Controls compilation strategy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompileMode {
    /// GOT-indirect calls for hot-reload. Used for REPL and multi-module batch
    /// compilation. Cached .o files are compiled in this mode so they are
    /// interchangeable between REPL and batch contexts.
    Interactive,
    /// Direct function calls, no GOT indirection. Used only for single-file
    /// test execution where no module caching or hot-reload is needed.
    Batch,
    /// Whole-program optimisation, standalone binary. Ring 4+ / Phase H.
    Release,
}

/// Result of compiling a single unit.
pub struct CompileResult {
    /// Updated symbol table entries
    pub symbols: Vec<(Symbol, ModuleEntry)>,
    /// Codegen artifacts
    pub codegen: Vec<(Symbol, DefCodegen)>,
    /// Accumulated warnings
    pub warnings: Vec<Warning>,
}
```

## Module Graph (in binary crate)

These types live in the `cranelisp` binary crate, not in `cranelisp-types`, because they orchestrate the full pipeline.

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

/// Inline module declaration extracted during discovery.
pub struct InlineModuleDecl {
    pub name: ModuleName,
    pub body: Vec<Sexp>,
    pub span: Span,
}

/// Extracted module-level declarations (imports, exports, mod, platform).
pub struct ModuleDecls {
    pub mod_names: Vec<(ModuleName, Span)>,
    pub inline_mods: Vec<InlineModuleDecl>,
    pub imports: Vec<ImportSpec>,
    pub exports: Vec<ExportSpec>,
    pub platforms: Vec<(String, Option<String>, Span)>,
    pub remaining: Vec<Sexp>,
}
```

## Heap Classification

```rust
/// Whether a type requires heap allocation at runtime.
/// Single definition — addresses audit codegen HIGH-2 (duplicate heap_category/classify_heap_type).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HeapCategory {
    /// Never heap-allocated: Int, Bool, Float, nullary constructors
    NeverHeap,
    /// Always heap-allocated: String, closures, data constructors with fields
    AlwaysHeap,
    /// May or may not be heap: polymorphic types, some ADTs with mixed constructors
    Mixed,
}

impl HeapCategory {
    /// Classify a type's heap behavior. Single source of truth.
    pub fn classify(ty: &Type) -> HeapCategory { ... }
}
```

## Frontend Traits (in `cranelisp-frontend`)

```rust
/// Trait for expanding macros during AST building.
/// Implemented by the binary crate; allows frontend to remain independent of backend.
pub trait MacroExpander {
    /// Expand a macro invocation, returning the expanded Sexp.
    fn expand(
        &mut self,
        name: &Symbol,
        args: &[Sexp],
        span: Span,
    ) -> Result<Sexp, CranelispError>;

    /// Check whether a name is a known macro.
    fn is_macro(&self, name: &str) -> bool;
}
```

---

## Heap Object Layouts (Ring 1)

Byte-level specifications for all heap-allocated value types. These `#[repr(C)]` structs define the memory layout with compile-time–verified offsets via `offset_of!`. All heap values share the `HeapHeader` prefix.

### ABI Decision: Base-Pointer Convention

`runtime/alloc` (Rust: `heap_alloc`) returns the **base pointer** — the start of the struct, not a payload pointer. All field offsets are positive, derived from struct layout. This departs from the sketch (which returned a payload pointer with negative offsets for the RC header at `ptr - 8`).

**Rationale**: Positive-only offsets eliminate a class of sign errors, simplify the mental model, and let `offset_of!` assertions verify the actual memory layout. The sketch's negative-offset convention was a transitional compromise to avoid a breaking change when the header was added after codegen was written.

### HeapHeader (in `cranelisp-types`)

The universal prefix for all heap-allocated values. Lives in `cranelisp-types` because both the backend and runtime need it.

```rust
use std::mem::{self, offset_of};

/// Universal header for all heap-allocated values.
/// All offsets in the compiler derive from this struct's layout.
#[repr(C)]
pub struct HeapHeader {
    /// Total allocation size in bytes (header + payload). Used by free().
    pub alloc_size: i64,
    /// Reference count. Accessed via atomic_rmw (seq-cst ordering) per NFR C.4.1.
    /// Initial value: 1 (the allocating binding owns the value).
    pub rc: i64,
}

impl HeapHeader {
    pub const SIZE: usize = mem::size_of::<Self>(); // 16
    pub const ALLOC_SIZE_OFFSET: i32 = offset_of!(Self, alloc_size) as i32; // 0
    /// RC is accessed by atomic_rmw in codegen. This offset is the single source of
    /// truth for RC field location — emit_rc_inc and emit_rc_dec use it exclusively.
    pub const RC_OFFSET: i32 = offset_of!(Self, rc) as i32; // 8
}

// Compile-time assertions — these fail at build time if the layout changes.
const _: () = assert!(HeapHeader::SIZE == 16);
const _: () = assert!(HeapHeader::ALLOC_SIZE_OFFSET == 0);
const _: () = assert!(HeapHeader::RC_OFFSET == 8);
```

### HeapString (in `cranelisp-runtime`)

The backend treats strings as **opaque heap pointers**. It knows `HeapHeader` (for RC operations) but never reads or writes string bytes directly — all string content access goes through extern functions in `cranelisp-runtime`. This containment enables future representation changes (e.g., ropes per NFR C.2.3) as runtime-only modifications.

The struct definition below is owned by `cranelisp-runtime`. The backend does NOT import it.

```rust
/// Heap string: [header | len | bytes...]
/// Owned by cranelisp-runtime. Opaque to the backend.
#[repr(C)]
pub struct HeapString {
    pub header: HeapHeader,
    /// Number of bytes (not characters) in the string.
    pub len: i64,
    // Bytes follow immediately at offset 24. Not a struct field because the
    // length is dynamic. Access via: base_ptr.byte_add(DATA_OFFSET)
}

impl HeapString {
    pub const LEN_OFFSET: i32 = offset_of!(Self, len) as i32;   // 16
    pub const DATA_OFFSET: i32 = mem::size_of::<Self>() as i32;  // 24

    /// Total payload size after the header: len field + byte data.
    pub const fn payload_size(byte_len: usize) -> usize {
        mem::size_of::<i64>() + byte_len
    }
}

const _: () = assert!(HeapString::LEN_OFFSET == 16);
const _: () = assert!(HeapString::DATA_OFFSET == 24);
```

**String allocation flow:**
1. Backend stores string literal bytes in JIT data section (compile time).
2. At runtime, backend emits `call runtime/alloc_string(data_ptr, len)`.
3. `cranelisp-runtime` (Rust: `heap_alloc_string`) allocates `HeapHeader::SIZE + payload_size(len)` bytes, writes header + len + copies bytes, returns base pointer.
4. Backend treats the returned i64 as an opaque heap pointer. RC operations use `HeapHeader::RC_OFFSET`.

### HeapAdt (in `cranelisp-backend`)

ADT layout knowledge is used by the backend for constructor allocation, match discrimination, field access, and drop glue generation. Lives in `cranelisp-backend`.

```rust
/// ADT data constructor: [header | tag | field_0 | field_1 | ... | field_n]
/// Nullary constructors are NOT heap-allocated — they are bare i64 tags.
#[repr(C)]
pub struct HeapAdt {
    pub header: HeapHeader,
    /// Constructor tag (same tag value whether nullary or data constructor).
    pub tag: i64,
    // Fields follow at FIELDS_START. Each field is an i64.
}

impl HeapAdt {
    pub const TAG_OFFSET: i32 = offset_of!(Self, tag) as i32;    // 16
    pub const FIELDS_START: usize = mem::size_of::<Self>();        // 24

    /// Offset of the i-th field from the base pointer.
    pub const fn field_offset(i: usize) -> i32 {
        (Self::FIELDS_START + i * mem::size_of::<i64>()) as i32
    }

    /// Payload size after the header: tag + n fields.
    pub const fn payload_size(field_count: usize) -> usize {
        mem::size_of::<i64>() + field_count * mem::size_of::<i64>()
    }
}

const _: () = assert!(HeapAdt::TAG_OFFSET == 16);
const _: () = assert!(HeapAdt::FIELDS_START == 24);
```

**Nullary/data discrimination:**
- Nullary constructors are bare i64 tags: `0`, `1`, `2`, ...
- Data constructors are heap pointers (well above `NULLARY_TAG_THRESHOLD`).
- Mixed sum types: runtime check `value < NULLARY_TAG_THRESHOLD` to discriminate.

### HeapClosure (in `cranelisp-backend`)

Closure layout is used by the backend for lambda compilation, closure calls, and drop glue. Lives in `cranelisp-backend`.

```rust
/// Closure: [header | code_ptr | drop_glue_ptr | cap_0 | cap_1 | ... | cap_n]
#[repr(C)]
pub struct HeapClosure {
    pub header: HeapHeader,
    /// Pointer to the compiled lambda body.
    /// Lambda body signature: (env_ptr: i64, params...) -> i64
    /// where env_ptr IS the closure base pointer (this allocation).
    pub code_ptr: i64, // ptr-width: i64 on native, i32 on wasm32 (see NFR C.5.4)
    /// Pointer to the drop glue function for this closure's captures.
    /// Drop glue signature: (env_ptr: i64) -> ()
    /// Decrements all heap-typed captures in the closure environment.
    /// Null (0) for closures with no heap-typed captures.
    pub drop_glue_ptr: i64,
    // Captures follow at CAPTURES_START. Each capture is an i64.
}

impl HeapClosure {
    pub const CODE_PTR_OFFSET: i32 = offset_of!(Self, code_ptr) as i32;         // 16
    pub const DROP_GLUE_PTR_OFFSET: i32 = offset_of!(Self, drop_glue_ptr) as i32; // 24
    pub const CAPTURES_START: usize = mem::size_of::<Self>();                      // 32

    /// Offset of the i-th captured value from the base pointer.
    pub const fn capture_offset(i: usize) -> i32 {
        (Self::CAPTURES_START + i * mem::size_of::<i64>()) as i32
    }

    /// Payload size after the header: code_ptr + drop_glue_ptr + n captures.
    pub const fn payload_size(capture_count: usize) -> usize {
        2 * mem::size_of::<i64>() + capture_count * mem::size_of::<i64>()
    }
}

const _: () = assert!(HeapClosure::CODE_PTR_OFFSET == 16);
const _: () = assert!(HeapClosure::DROP_GLUE_PTR_OFFSET == 24);
const _: () = assert!(HeapClosure::CAPTURES_START == 32);
```

### HeapVec (in `cranelisp-backend`)

Vec layout is used by the backend for Vec literal compilation, element access, COW mutation, and drop glue. Lives in `cranelisp-backend`.

A Vec value consists of **two allocations**: a Vec struct (with RC header) and a separate data buffer for elements. The data buffer is a plain byte allocation — no RC header of its own — because it is never independently reference-counted; its lifetime is tied to the Vec struct.

```rust
/// Vec struct: [header | len | cap | data_ptr]
/// The data buffer is a separate allocation: [elem_0 | elem_1 | ... | elem_{cap-1}]
/// Each element is i64 (uniform representation). Only the first `len` elements are live.
#[repr(C)]
pub struct HeapVec {
    pub header: HeapHeader,
    /// Number of live elements (0..len are initialized).
    pub len: i64,
    /// Capacity of the data buffer (in elements, not bytes).
    pub cap: i64,
    /// Pointer to the data buffer. The buffer holds `cap` slots of i64.
    pub data_ptr: i64, // ptr-width: i64 on native
}

impl HeapVec {
    pub const LEN_OFFSET: i32 = offset_of!(Self, len) as i32;           // 16
    pub const CAP_OFFSET: i32 = offset_of!(Self, cap) as i32;           // 24
    pub const DATA_PTR_OFFSET: i32 = offset_of!(Self, data_ptr) as i32; // 32

    /// Payload size after the header: len + cap + data_ptr.
    pub const fn payload_size() -> usize {
        3 * mem::size_of::<i64>()  // 24 bytes
    }
}

const _: () = assert!(HeapVec::LEN_OFFSET == 16);
const _: () = assert!(HeapVec::CAP_OFFSET == 24);
const _: () = assert!(HeapVec::DATA_PTR_OFFSET == 32);
const _: () = assert!(mem::size_of::<HeapVec>() == 40);
```

**Data buffer layout:**
```
data_ptr → [elem_0: i64 | elem_1: i64 | ... | elem_{cap-1}: i64]
             ↑ live (0..len)                    ↑ uninitialized (len..cap)
```

Element offset: `data_ptr + index * 8`. The data buffer is allocated as `cap * 8` bytes via the system allocator (no RC header). When the Vec struct is freed, the data buffer is freed separately.

**Vec type representation:** Vec reuses the existing `Type::ADT("Vec", vec![elem_type])` representation. The typechecker special-cases the name `"Vec"` to provide vec operations as typed primitives rather than ADT constructor calls. `VecLit` elements unify to determine `elem_type`; `[]` infers `Vec(a)` (polymorphic).

### Closure Calling Convention

**Lambda body signature:** `(env_ptr: i64, param_0: i64, ..., param_n: i64) -> i64`

- `env_ptr` is the closure's base pointer. The callee loads captures via `heap_load(builder, env_ptr, HeapClosure::capture_offset(i))`.
- Non-capturing lambdas and named-function-as-value wrappers allocate a minimal closure: `[HeapHeader | code_ptr | drop_glue_ptr(0)]` (zero captures, null drop glue). The wrapper function ignores `env_ptr`.
- Indirect call: `call_indirect(sig, code_ptr, [closure_ptr, args...])` where `code_ptr` is loaded from `HeapClosure::CODE_PTR_OFFSET`.

**Drop glue strategy — embedded drop_glue_ptr:**

Each closure carries a `drop_glue_ptr` at offset 24 (`HeapClosure::DROP_GLUE_PTR_OFFSET`). The drop glue function is generated per-lambda at compile time:

- **Signature:** `(env_ptr: i64) -> ()` — loads and dec's each heap-typed capture from the closure environment.
- **Null for no heap captures:** Closures with no heap-typed captures store `0` in `drop_glue_ptr`. The dec path checks for null before calling drop glue.
- **Self-contained operation:** When decrementing a closure (rc reaches zero), the runtime reads `drop_glue_ptr` directly from the closure struct and calls it. No external tables or module lookups are needed.

**Rationale:** An earlier design used a side table (`HashMap<*const u8, *const u8>` mapping `code_ptr → drop_fn`), but this was rejected during Ring 2 because: (1) cross-module closures cannot look up the creating module's side table, and (2) the embedded pointer makes closure dec a self-contained operation that works uniformly regardless of where the closure was created. The 8-byte overhead per closure is acceptable given the correctness and simplicity benefits. See `design/backend/ring2-rc.md` §1.3 and §9.1.

**Re-entrant JIT:** Not needed in Ring 1. Closures capture values, not thunks. The first case requiring re-entrant compilation is the macro mini-pipeline in Ring 3.

### Reference Counting Operations

RC operations use **atomic instructions** from Ring 1 per NFR C.4.1. The codegen emits Cranelift `atomic_rmw` with sequentially-consistent ordering (Cranelift's default for `atomic_rmw`). `MemFlags::trusted()` is used as a validity flag (non-trapping memory access), not a memory ordering directive.

```
emit_rc_inc(builder, ptr):
    atomic_rmw(Add, ptr + HeapHeader::RC_OFFSET, 1)  // seq-cst

emit_rc_dec(builder, ptr):
    old_rc = atomic_rmw(Sub, ptr + HeapHeader::RC_OFFSET, 1)  // seq-cst
    if old_rc == 1:
        // Acquire fence before reading object fields for drop glue
        fence(Acquire)
        call drop_glue(ptr)  // type-specific, generated per-type
        call runtime/dealloc(ptr)
```

The `atomic_rmw` provides sequentially-consistent ordering for both inc and dec. A separate Acquire fence is emitted on the free path (when `old_rc == 1`) to ensure all writes to the object are visible before reading fields for drop glue. See `design/backend/ring2-rc.md` §2.1.

**F-12 Null guard (prerequisite for Vec element RC):** `emit_rc_dec` MUST guard against bare i64 values that are not heap pointers before accessing the RC header. Nullary ADT constructors (e.g., `None` = 0, `Nil` = 0) are bare i64 tags, not heap pointers. Decrementing at `tag + HeapHeader::RC_OFFSET` would corrupt arbitrary memory.

Guard pattern for `emit_rc_dec`:
```
emit_rc_dec(builder, ptr, ty):
    if HeapCategory::classify(ty) == Mixed:
        brif ptr < NULLARY_TAG_THRESHOLD, skip_block, dec_block
    // ... proceed with atomic dec in dec_block
```

`NULLARY_TAG_THRESHOLD` is `1024` — any value below this is a nullary tag, not a heap pointer. This threshold is conservative: heap pointers from the allocator are always well above 1024. The guard is only needed for `Mixed` types (types with both nullary and data constructors, e.g., `Option`, `List`). `AlwaysHeap` types skip the guard. `NeverHeap` types skip the entire dec.

### Consuming Calling Convention (Ring 1)

Two conventions, classified at compile time by call site:

**Consuming (cranelisp-to-cranelisp calls):** Callee owns heap-typed parameters. Caller prepares arguments:
- **Last-use variable in scope**: transfer ownership (no RC inc). Mark consumed — caller's scope exit skips dec.
- **Non-last-use variable or capture**: RC inc before call. Callee's scope-exit dec won't destroy caller's reference.
- **Temporary expression result**: no action (callee takes ownership of rc=1 value).

**Borrowed (extern/platform calls):** Callee does not own parameters. Caller decs temps after the call returns.

**Capture rule:** Captured variables (closed over by a lambda) are NEVER eligible for last-use transfer. The closure environment holds an implicit reference; drop glue manages it.

**Scope cleanup:** At scope exit, the backend emits dec for all heap-typed values in the scope stack, EXCEPT the return value (which is transferred to the caller or to the parent scope).

---

## Ring 1 Extern Primitives

Extern functions exported by `cranelisp-runtime` and called from JIT-compiled code. All use the **borrowed** calling convention (callee does not own heap arguments — caller is responsible for RC).

All signatures use `i64` for both data values and heap pointers. The runtime interprets heap-pointer arguments by casting to the appropriate layout struct internally.

### Allocation

```rust
/// Allocate a heap object. Writes HeapHeader (alloc_size, rc=1). Returns base pointer.
/// payload_size: bytes needed after the header.
/// JIT name: "runtime/alloc"
extern "C" fn heap_alloc(payload_size: i64) -> i64;

/// Deallocate a heap object. Reads alloc_size from HeapHeader at base pointer.
/// JIT name: "runtime/dealloc"
extern "C" fn heap_dealloc(base_ptr: i64);
```

### String Primitives

```rust
/// Allocate a new string from raw bytes. Copies byte_len bytes from bytes_ptr.
/// Returns base pointer to a HeapString (rc=1).
/// JIT name: "runtime/alloc_string" (runtime infrastructure, not user-visible)
extern "C" fn heap_alloc_string(bytes_ptr: *const u8, byte_len: i64) -> i64;

/// Concatenate two strings. Returns a new string (rc=1).
/// str-concat :: (Fn [String String] String)
/// JIT name: "str-concat" (user-visible primitive)
extern "C" fn str_concat(a: i64, b: i64) -> i64;

/// String equality (byte-wise). Returns 1 (true) or 0 (false).
/// str-eq :: (Fn [String String] Bool)
/// JIT name: "str-eq"
extern "C" fn str_eq(a: i64, b: i64) -> i64;

/// String byte length.
/// str-len :: (Fn [String] Int)
/// JIT name: "str-len"
extern "C" fn str_len(s: i64) -> i64;

/// Convert Int to its decimal string representation.
/// int-to-string :: (Fn [Int] String)
/// JIT name: "int-to-string"
extern "C" fn int_to_string(n: i64) -> i64;

/// Convert Float to its string representation.
/// float-to-string :: (Fn [Float] String)
/// JIT name: "float-to-string"
extern "C" fn float_to_string(f: i64) -> i64;

/// Convert Bool to "true" or "false".
/// bool-to-string :: (Fn [Bool] String)
/// JIT name: "bool-to-string"
extern "C" fn bool_to_string(b: i64) -> i64;

/// Identity function for strings — increments RC and returns the same pointer.
/// Used when a string value needs to be copied (e.g., returned from a borrowed context).
/// string-identity :: (Fn [String] String)
/// JIT name: "string-identity"
extern "C" fn string_identity(s: i64) -> i64;

/// Parse an integer from a string. Returns an Option Int as a heap-allocated ADT.
/// Depends on Chunk B (Option type must be defined).
/// parse-int :: (Fn [String] (Option Int))
/// JIT name: "parse-int"
extern "C" fn parse_int(s: i64) -> i64;
```

### String Primitives — Registration

All string primitives are registered in the `primitives` module with `PrimitiveKind::Extern`:

| Cranelisp name | JIT symbol | Rust function | Type signature | Calling convention |
|---|---|---|---|---|
| `str-concat` | `str-concat` | `str_concat` | `(Fn [String String] String)` | Borrowed |
| `str-eq` | `str-eq` | `str_eq` | `(Fn [String String] Bool)` | Borrowed |
| `str-len` | `str-len` | `str_len` | `(Fn [String] Int)` | Borrowed |
| `int-to-string` | `int-to-string` | `int_to_string` | `(Fn [Int] String)` | Borrowed |
| `float-to-string` | `float-to-string` | `float_to_string` | `(Fn [Float] String)` | Borrowed |
| `bool-to-string` | `bool-to-string` | `bool_to_string` | `(Fn [Bool] String)` | Borrowed |
| `string-identity` | `string-identity` | `string_identity` | `(Fn [String] String)` | Borrowed |
| `parse-int` | `parse-int` | `parse_int` | `(Fn [String] (Option Int))` | Borrowed |

### Vec Primitives

Vec operations use a **hybrid inline + extern** approach. Fast paths are compiled as inline Cranelift IR by the backend; slow paths (copy, grow) call extern functions in `cranelisp-runtime`.

**Inline operations (emitted as Cranelift IR by the backend):**

```rust
/// vec-get: bounds-checked element access. O(1).
/// Loads element at data_ptr + index * 8.
/// Emits emit_rc_inc on the element for heap-typed elements (caller gets a new reference).
/// Borrowed read optimization: if the owner Vec is unique (branch_depth == 0),
/// skip inc and mark element as borrowed_temp.
/// Panics at runtime if index < 0 or index >= len.
/// vec-get :: (Fn [(Vec a) Int] a)
/// Inline codegen — no JIT symbol.

/// vec-set COW fast path: when is_last_use(vec) AND (static unique OR runtime rc==1),
/// mutate in place: dec old element, store new element, return same Vec pointer.
/// vec-set :: (Fn [(Vec a) Int a] (Vec a))
/// Inline codegen — falls through to vec-set-copy extern on the copy path.

/// vec-push COW fast path: when is_last_use(vec) AND (static unique OR runtime rc==1),
/// store at data[len], increment len. If len >= cap, call vec-push-grow extern.
/// vec-push :: (Fn [(Vec a) a] (Vec a))
/// Inline codegen — falls through to vec-push-copy or vec-push-grow extern.
```

**Extern operations (in `cranelisp-runtime`, borrowed calling convention):**

```rust
/// Allocate a new Vec with the given initial capacity. Returns base pointer (rc=1).
/// Data buffer is allocated separately as cap * 8 bytes.
/// JIT name: "runtime/vec_new"
extern "C" fn vec_new(cap: i64) -> i64;

/// Vec length. Loads len from HeapVec::LEN_OFFSET.
/// vec-len :: (Fn [(Vec a)] Int)
/// JIT name: "vec-len"
extern "C" fn vec_len(vec: i64) -> i64;

/// Vec set — copy path. Allocates a new Vec, copies all elements with per-element
/// RC inc via inc_fn, stores the new value at the given index.
/// inc_fn: function pointer for per-element RC inc (null for NeverHeap types).
/// Returns base pointer to the new Vec (rc=1).
/// JIT name: "vec-set-copy"
extern "C" fn vec_set_copy(vec: i64, index: i64, val: i64, inc_fn: i64) -> i64;

/// Vec push — copy path. Allocates a new Vec with capacity for the appended element,
/// copies all elements with per-element RC inc via inc_fn, appends val.
/// Returns base pointer to the new Vec (rc=1).
/// JIT name: "vec-push-copy"
extern "C" fn vec_push_copy(vec: i64, val: i64, inc_fn: i64) -> i64;

/// Vec push — COW growth path. Called when the Vec is unique (rc==1) but the data
/// buffer is full (len >= cap). Reallocs the data buffer (doubles capacity),
/// stores the new value, increments len. Returns the same Vec pointer.
/// JIT name: "vec-push-grow"
extern "C" fn vec_push_grow(vec: i64, val: i64) -> i64;

/// Vec drop. Loops 0..len calling dec_fn on each element, then frees the data
/// buffer and the Vec struct. Called from Vec drop glue.
/// dec_fn: function pointer for per-element RC dec (null for NeverHeap types).
/// JIT name: "runtime/vec_drop"
extern "C" fn vec_drop(vec: i64, dec_fn: i64);
```

### Vec Primitives — Registration

| Cranelisp name | Kind | JIT symbol | Type signature | Calling convention |
|---|---|---|---|---|
| `vec-get` | Inline | — | `(Fn [(Vec a) Int] a)` | Consuming (inline) |
| `vec-set` | Inline | — | `(Fn [(Vec a) Int a] (Vec a))` | Consuming (inline) |
| `vec-push` | Inline | — | `(Fn [(Vec a) a] (Vec a))` | Consuming (inline) |
| `vec-len` | Extern | `vec-len` | `(Fn [(Vec a)] Int)` | Borrowed |
| `vec-set-copy` | Extern | `vec-set-copy` | internal (not user-visible) | Borrowed |
| `vec-push-copy` | Extern | `vec-push-copy` | internal (not user-visible) | Borrowed |
| `vec-push-grow` | Extern | `vec-push-grow` | internal (not user-visible) | Borrowed |
| `runtime/vec_drop` | Extern | `runtime/vec_drop` | internal (not user-visible) | Borrowed |

### Vec Element Inc/Dec Functions (`vec_elem_inc_cache`)

Per-element-type standalone Cranelift functions used as callback function pointers by the Vec copy-path externs (`vec-set-copy`, `vec-push-copy`) and by Vec drop glue. Generated lazily and cached in `vec_elem_inc_cache` / `vec_elem_dec_cache` on `FnCompiler`.

Three variants by `HeapCategory::classify(elem_type)`:

| Category | Inc function | Dec function |
|---|---|---|
| `NeverHeap` (Int, Bool, Float) | null pointer (0) — extern skips the call | null pointer (0) — drop glue skips the call |
| `AlwaysHeap` (String, Fn, data-only ADT) | `atomic_rmw(Add, val + HeapHeader::RC_OFFSET, 1)` | Full `emit_rc_dec` pattern (atomic sub, conditional drop + free) |
| `Mixed` (sum types with nullary + data ctors) | Guard `val < NULLARY_TAG_THRESHOLD`, then atomic inc | Guard `val < NULLARY_TAG_THRESHOLD`, then full dec |

Function signature for both inc and dec callbacks: `(val: i64) -> i64` (return value ignored). The `i64 -> i64` signature allows uniform calling from extern Rust code.

Mangling convention: `vec_elem_inc$<mangled_type>`, `vec_elem_dec$<mangled_type>` where `<mangled_type>` uses the same mangling as drop functions (`mangle_type_for_drop`).

### Vec COW Protocol

Copy-on-write for `vec-set` and `vec-push` uses a three-level decision:

1. **Static COW** (compile-time only): `is_last_use(vec_arg) && is_var_unique(vec_name)` — the compiler statically knows the Vec is the sole reference. Mutate in place unconditionally. No runtime RC check emitted. Mark the Vec variable consumed.

2. **Runtime COW** (compile-time + runtime): `is_last_use(vec_arg)` but Vec is not statically unique. Emit runtime check: `atomic_load(ptr + HeapHeader::RC_OFFSET) == 1`. If unique at runtime, mutate in place. Otherwise fall through to the copy path. Mark the Vec variable consumed either way (the reference is either mutated or replaced).

3. **Copy** (always safe): Vec is not at last-use. Call `vec-set-copy` / `vec-push-copy` extern. The extern allocates a new Vec, copies all elements (calling inc_fn on each), and returns the new Vec. The caller's reference to the original Vec is NOT consumed (scope-exit dec will handle it).

**New value RC** follows the constructor Var arg pattern:
- Var + last-use → mark consumed (ownership transfers to Vec, no inc)
- Var + not-last-use → `emit_rc_inc` (Vec gets a new reference)
- Borrowed temp → `emit_rc_inc` (borrowed value escaping to a new owner)
- Temp expression → nothing (fresh rc=1 value, ownership transfers)

### Vec Drop Glue

Vec drop glue is invoked when `emit_rc_dec` on a Vec decrements the RC to zero. The drop glue must:

1. **Dec each live element** (indices `0..len`): Load each element from the data buffer, call the per-element-type dec function (from `vec_elem_dec_cache`). For `NeverHeap` elements, skip this step entirely (dec_fn is null).
2. **Free the data buffer**: `dealloc(data_ptr, cap * 8)`. The data buffer has no RC header — it uses a plain system allocator free.
3. **Free the Vec struct**: `runtime/dealloc(vec_ptr)`. This reads `HeapHeader::alloc_size` from the Vec struct's header and frees it.

The drop glue can be implemented as either:
- A generated Cranelift function (like ADT drop glue) that loops over elements inline.
- A call to `runtime/vec_drop(vec_ptr, dec_fn)` extern that performs the loop in Rust.

The extern approach is preferred because the loop body is trivial (load + call function pointer) and the Rust implementation is simpler to verify and debug. The generated-function approach is reserved for cases where the loop body needs type-specific inline code.

### Runtime Infrastructure

```rust
/// Match exhaustiveness panic. Called when pattern matching falls through all arms.
/// Prints a diagnostic and aborts. Ring 0 uses a Cranelift trap; Ring 1+ uses this
/// function to provide better diagnostics (source location, match value).
/// JIT name: "runtime/panic"
extern "C-unwind" fn runtime_panic(msg_ptr: *const u8, msg_len: i64) -> !;

/// RC underflow diagnostic. Called from JIT code (debug builds only) when an RC
/// decrement produces a value <= 0, indicating a double-free or use-after-free.
/// Uses debug_assert! internally — no-op in release builds.
/// JIT name: "runtime/rc_underflow_check"
extern "C-unwind" fn rc_underflow_check(ptr: i64, old_rc: i64);

/// Read a string's bytes for display/formatting. Returns (ptr, len) via out-params.
/// Used by the binary crate's ValueFormatter — NOT called from JIT code.
/// JIT name: "runtime/string_read" (runtime infrastructure, not user-visible)
extern "C" fn string_read(s: i64, out_ptr: *mut *const u8, out_len: *mut i64);
```

### Inline RC Operations

The core RC operations (`inc`, `dec`, `dealloc`) are emitted inline by the backend using `atomic_rmw` and layout constants — they are NOT extern functions. This avoids function-call overhead on the hot path.

---

## REPL Value Display (in binary crate)

Display of runtime values in the REPL (`:Type value` format). Lives in the binary crate because it needs both type information (from the typechecker) and runtime memory access (reading heap values).

```rust
/// Format a runtime value for REPL display.
///
/// Dispatches by type:
///   Int    → decimal representation
///   Bool   → "true" / "false"
///   Float  → decimal representation
///   String → reads bytes via string_read (JIT: "runtime/string_read"), wraps in quotes
///   ADT    → reads tag + fields from heap (HeapAdt layout), formats recursively
///            Nullary: constructor name. Data: "(Ctor.Name field1 field2 ...)"
///   Vec    → reads len + data_ptr from HeapVec, formats as "[elem, elem, ...]"
///            Comma-separated (visually distinct from bracket-literal syntax which has no commas).
///            Elements formatted recursively with their concrete element type.
///   Fn     → "<closure>" (closure environments are not user-inspectable)
///
/// symbol_tables provides constructor names and field info for ADT display.
pub fn format_result_value(
    result: i64,
    ty: &Type,
    symbol_tables: &HashMap<ModuleFullPath, SymbolTable>,
) -> String { ... }

/// Format a type for REPL display.
///
/// Examples:
///   Type::Int                       → "primitives/Int"
///   Type::Fn([Int], Int)            → "(Fn [primitives/Int] primitives/Int)"
///   Type::ADT("Option", [Int])      → "(user/Option primitives/Int)"
///   Type::Fn([Var(a)], Var(a))      → "(Fn [a] a)"
pub fn format_type(
    ty: &Type,
    symbol_tables: &HashMap<ModuleFullPath, SymbolTable>,
) -> String { ... }
```

**ADT display recursion:**
1. Check `value < NULLARY_TAG_THRESHOLD` → nullary constructor: look up tag in `TypeDefInfo.constructors` to find the name.
2. Otherwise, heap-allocated data constructor: read `HeapAdt::TAG_OFFSET` for tag, look up constructor info, read each field at `HeapAdt::field_offset(i)`, recurse with field type.
3. For polymorphic ADTs (e.g., `Option Int`), the `Type::ADT(name, args)` provides the concrete type arguments for recursive field formatting.

---

## Codegen Emit Helpers (in `cranelisp-backend`)

The emit helper pattern confines heap layout knowledge to a single file in the backend. Only emit helpers import layout constants (`HeapHeader`, `HeapAdt`, `HeapClosure`). All other codegen code calls emit helpers.

### Generic Heap Access

Free functions — work in any context that has a `FunctionBuilder`:

```rust
/// Load an i64 value from a heap object at the given byte offset.
/// The offset MUST come from a layout constant (HeapHeader::RC_OFFSET,
/// HeapAdt::field_offset(i), etc.) — never a bare numeric literal.
///
/// ptr is ptr-width (i64 on native; see NFR C.5.4 for wasm32 future).
/// The returned value is always data-width (i64).
pub fn heap_load(builder: &mut FunctionBuilder, ptr: Value, offset: i32) -> Value {
    builder.ins().load(types::I64, MemFlags::trusted(), ptr, offset)
}

/// Store an i64 value into a heap object at the given byte offset.
/// Same offset rules as heap_load.
pub fn heap_store(builder: &mut FunctionBuilder, val: Value, ptr: Value, offset: i32) {
    builder.ins().store(MemFlags::trusted(), val, ptr, offset);
}
```

### Per-Type Construction Helpers

Methods on `FnCompiler` — need access to `self` for allocation calls:

```rust
impl FnCompiler {
    /// Allocate a string from bytes stored in the JIT data section.
    /// Emits: call runtime/alloc_string(data_ptr, len).
    /// Returns: base pointer (i64) to the new HeapString.
    fn emit_string_alloc(&mut self, bytes: &[u8], span: Span) -> Result<Value>;

    /// Allocate an ADT data constructor.
    /// Emits: alloc(payload_size) + store tag + store each field.
    /// Returns: base pointer (i64) to the new HeapAdt.
    fn emit_adt_alloc(
        &mut self,
        tag: i64,
        field_vals: &[Value],
        span: Span,
    ) -> Result<Value>;

    /// Allocate a closure.
    /// Emits: alloc(payload_size) + store code_ptr + store each capture.
    /// Stores drop_glue_ptr in the closure (null if no heap-typed captures).
    /// Returns: base pointer (i64) to the new HeapClosure.
    fn emit_closure_alloc(
        &mut self,
        code_ptr: Value,
        captures: &[Value],
        capture_types: &[Type],
        span: Span,
    ) -> Result<Value>;

    /// Allocate a Vec literal.
    /// Emits: call runtime/vec_new(len) to allocate Vec struct + data buffer,
    /// then stores each element into the data buffer.
    /// Element RC follows the constructor Var arg pattern (emit_stored_value_rc).
    /// Returns: base pointer (i64) to the new HeapVec.
    fn emit_vec_alloc(
        &mut self,
        element_vals: &[Value],
        element_exprs: &[Expr],
        elem_type: &Type,
        span: Span,
    ) -> Result<Value>;
}
```

### RC Emission Helpers

```rust
impl FnCompiler {
    /// Emit atomic RC increment: atomic_rmw(Add, ptr + RC_OFFSET, 1, Release).
    fn emit_rc_inc(&mut self, ptr: Value);

    /// Emit atomic RC decrement + conditional dealloc.
    /// old = atomic_rmw(Sub, ptr + RC_OFFSET, 1, Release)
    /// if old == 1: fence(Acquire); call drop_glue(ptr); call runtime/dealloc(ptr)
    fn emit_rc_dec(&mut self, ptr: Value, ty: &Type);
}
```

### Representation Containment Rule

These helpers are the **only** codegen code that imports layout constants from `HeapHeader`, `HeapAdt`, and `HeapClosure`. No other module in `cranelisp-backend` may use `offset_of!` or numeric offsets for heap access. This is the enforcement mechanism for NFR C.5.2 (representation containment).

The `HeapString` layout is not imported by the backend at all — string operations go exclusively through extern functions. This is the strongest form of containment: the backend has zero knowledge of string internals.

### Pointer-Width Documentation Convention

Per NFR C.5.4 (target portability), emit helpers should document which values are pointer-width vs data-width:

```rust
// ptr-width: heap base pointers, code_ptr, data_ptr (i64 on native, i32 on wasm32)
// data-width: Int, Float, Bool, tags, field values (always i64)
```

No abstraction is needed now — both are `i64` on native. But documenting the distinction ensures a future wasm32 port can identify and update pointer-width values without auditing every i64 in the codebase.

---

## Ring 2A: Trait Dispatch Decisions (Sprint 4)

Architectural decisions for Ring 2A (traits and operator dispatch). These complement the existing type definitions already in this document (`TraitDecl`, `TraitImpl`, `TraitMethodSig`, `ResolvedCall::TraitMethod`, `CheckResult` Ring 2 fields, `Scheme.constraints`, `ConstrainedFn`, `MonoDefn`).

### Verification: Existing Types Are Sufficient

All Ring 2A boundary types already exist in `cranelisp-types` and are verified as sufficient for Sprint 4:

| Type | Location | Status |
|------|----------|--------|
| `TraitDecl` | `ast.rs` | Sufficient — has `name`, `type_params`, `methods` (with `TraitMethodSig`) |
| `TraitImpl` | `ast.rs` | Sufficient — has `trait_name`, `target_type`, `type_args`, `type_constraints`, `methods` |
| `TraitMethodSig` | `ast.rs` | Sufficient — has `default_body: Option<Sexp>`, `default_param_names` for defaults |
| `ResolvedCall::TraitMethod` | `check.rs` | Sufficient — has `trait_name`, `method_name`, `impl_type`, `mangled_name` |
| `CheckResult` Ring 2 fields | `check.rs` | Sufficient — `constrained_fn_names`, `mono_defns`, `default_method_defns` |
| `Scheme.constraints` | `types.rs` | Sufficient — `HashMap<TypeId, Vec<TraitName>>` |
| `ConstrainedFn` | `module.rs` | Sufficient — stores `defn` + `scheme` for deferred monomorphisation |
| `MonoDefn` | `check.rs` | Sufficient — stores monomorphised `defn` + per-specialization `resolutions` |
| `ModuleEntry::TraitDecl` | `module.rs` | Sufficient — stores the `TraitDecl` + visibility |
| `TopLevel::TraitDecl/TraitImpl` | `ast.rs` | Sufficient — parsing targets |
| `ReplInput::TraitDecl/TraitImpl` | `ast.rs` | Sufficient — REPL parsing targets |

**No new boundary types are needed for Ring 2A.**

### Gap: `ReplCheckResult` Missing Ring 2 Fields

`ReplCheckResult` is missing the Ring 2 fields that `CheckResult` already has. This must be fixed for REPL trait support.

**Specification:**

```rust
/// Result of type checking a single REPL input.
#[derive(Debug)]
pub struct ReplCheckResult {
    pub ty: Type,
    pub scheme: Option<Scheme>,
    pub method_resolutions: MethodResolutions,
    /// Names of constrained polymorphic functions requiring monomorphisation (Ring 2)
    pub constrained_fn_names: HashSet<Symbol>,
    /// Monomorphised function definitions generated during checking (Ring 2)
    pub mono_defns: Vec<MonoDefn>,
    /// Default trait method implementations expanded during checking (Ring 2)
    pub default_method_defns: Vec<Defn>,
    pub expr_types: HashMap<Span, Type>,
    pub warnings: Vec<Warning>,
    pub type_defs: HashMap<TypeName, TypeDefInfo>,
    pub constructor_to_type: HashMap<Symbol, TypeName>,
}
```

**Three locations must change atomically:**

1. **`cranelisp-types/src/check.rs`** — Add three fields to `ReplCheckResult`: `constrained_fn_names`, `mono_defns`, `default_method_defns`. (`/typecheck` owns this change via the types crate.)
2. **`cranelisp-typecheck/src/program.rs`** (`build_repl_result`) — Populate the new fields from typechecker state (same pattern as `build_check_result`). (`/typecheck`)
3. **`src/repl.rs`** (`build_check_for_backend`) — Forward the new fields from `ReplCheckResult` into `CheckResult` instead of hardcoding empty values. (`/qa` owns the binary crate pipeline wiring.)

### Decision: Primitive-Trait-Method Mapping

**How the backend knows that `Num.+$Int` means "emit iadd inline."**

The typecheck crate ALWAYS emits `ResolvedCall::TraitMethod` for operator calls after Ring 2A. It never emits `ResolvedCall::BuiltinFn` for operators. The backend is responsible for recognizing which trait method implementations correspond to primitive operations and emitting inline IR instead of function calls.

**Mechanism:** The backend maintains a compile-time mapping from `(TraitName, Symbol, TypeName)` to the primitive operation to emit:

```rust
/// Backend-side mapping from trait method implementations to inline IR.
/// Populated at startup — no runtime overhead.
///
/// Key: (trait_name, method_name, impl_type)
/// Value: the same inline IR that was previously emitted for the BuiltinFn
///
/// Example entries:
///   ("Num", "+", "Int")   → iadd
///   ("Num", "+", "Float") → fadd
///   ("Num", "-", "Int")   → isub
///   ("Num", "*", "Int")   → imul
///   ("Num", "/", "Int")   → sdiv
///   ("Eq",  "=", "Int")   → icmp eq
///   ("Eq",  "=", "Float") → fcmp eq
///   ("Ord", "<", "Int")   → icmp slt
///   ...
fn is_primitive_trait_method(
    trait_name: &TraitName,
    method_name: &Symbol,
    impl_type: &TypeName,
) -> Option<PrimitiveOp>;
```

**Rationale:** This keeps the typecheck layer clean (all operators flow through the trait dispatch path uniformly) while letting the backend optimize known primitives. The mapping is static and exhaustive — if a trait method isn't in the table, it's a user-defined method and gets compiled as a normal function call.

**Ring 0-1 coexistence:** Existing `ResolvedCall::BuiltinFn` entries for named primitives (`add-i64`, `eq-i64`, etc.) are UNCHANGED. They continue to work exactly as before. The `+`, `-`, etc. operators gain a NEW `ResolvedCall::TraitMethod` path alongside. Both paths coexist per principle 9 (rings are accretive).

### JIT Name Convention: Trait Method Implementations

Formalized mangling convention for trait method implementations:

```
Trait.method$Type
```

**Examples:**
- `Num.+$Int` — `+` method of `Num` trait for `Int`
- `Num.+$Float` — `+` method of `Num` trait for `Float`
- `Eq.=$Int` — `=` method of `Eq` trait for `Int`
- `Ord.<$Float` — `<` method of `Ord` trait for `Float`
- `Display.show$Color` — `show` method of `Display` trait for user type `Color`

**Polymorphic ADT impls:**
- `Display.show$Option` — polymorphic impl (type args not in mangled name since the method is constrained-polymorphic, monomorphised separately)

**Constrained function specializations** (user-defined):
```
name$Type1+Type2+...
```
- `add$Int+Int` — specialization of constrained `add` for `(Int, Int)` args
- `add$Float+Float` — specialization for `(Float, Float)` args

This extends the existing convention already documented in `src/CLAUDE.md` §"JIT Symbol Names".

### Constraint Propagation Protocol

How `Scheme.constraints` flows through the type inference pipeline:

**1. Trait method registration (startup):**
When a trait is registered (e.g., `(deftrait (Num a) (+ [a a] a))`), each method gets a constrained scheme:
```
+ :: forall [t0]. { t0: [Num] } => (Fn [t0 t0] t0)
```
The constraint `{ t0: [Num] }` is stored in `Scheme.constraints`.

**2. Instantiation at call sites:**
When `+` is used in `(+ x y)`, the typechecker instantiates the constrained scheme with fresh type variables. The constraints are carried forward on the fresh variables.

**3. Generalization with constraint propagation:**
When `(defn add [x y] (+ x y))` is generalized, the `generalize` function must:
1. Collect free type variables in the resolved function type as usual.
2. For each free variable, collect ALL constraints accumulated during body checking (from trait method calls that unified with that variable).
3. Store these in `Scheme.constraints` on the generalized scheme.

The result: `add :: forall [t0]. { t0: [Num] } => (Fn [t0 t0] t0)`.

**4. Constrained function detection:**
After generalization, if `scheme.constraints` is non-empty, the function is a constrained polymorphic function. It gets stored as a `ConstrainedFn` in `DefKind::UserFn { constrained_fn: Some(...) }` and its name is added to `CheckResult.constrained_fn_names`.

**5. Monomorphisation at call sites:**
When `(add 1 2)` is encountered:
1. Instantiate `add`'s scheme with fresh vars.
2. Unify args: `t_fresh = Int`.
3. Check constraint: `Num(Int)` — is there an `(impl Num Int ...)`? Yes.
4. Generate specialization `add$Int+Int` with concrete method resolutions: `{ (+ call span) → TraitMethod { Num, +, Int, "Num.+$Int" } }`.
5. Add to `CheckResult.mono_defns`.

**Implementation note:** The typechecker needs to track which constraints are active on which type variables during body checking. A `HashMap<TypeId, Vec<TraitName>>` on the checker state is sufficient — populated when a constrained scheme is instantiated, consulted during `generalize`.

### Special Forms: `deftrait` and `impl`

`deftrait` and `impl` must be registered as special forms in the typechecker's `register_special_forms()` for REPL `/help` display:

```rust
("deftrait", "trait declaration: (deftrait (TraitName a) (method [a ...] ret) ...)"),
("impl", "trait implementation: (impl TraitName Type (method [params] body) ...)"),
```

This is a `/typecheck` task (builtins.rs).

### Core Trait Definitions (Ring 2A)

The following traits are registered by the typechecker at startup (not from stdlib files — those require the module system in Sprint 5):

| Trait | Type param | Methods | Default methods |
|-------|-----------|---------|-----------------|
| `Num` | `a` | `+ [a a] a`, `- [a a] a`, `* [a a] a`, `/ [a a] a` | — |
| `Eq` | `a` | `= [a a] Bool`, `!= [a a] Bool` | `!=` defined as `(fn [x y] (not (= x y)))` |
| `Ord` | `a` | `< [a a] Bool`, `> [a a] Bool`, `<= [a a] Bool`, `>= [a a] Bool` | `>` as `(fn [x y] (< y x))`, `<=` as `(fn [x y] (not (< y x)))`, `>=` as `(fn [x y] (not (< x y)))` |

**Built-in impls** (also registered at startup):

| Trait | Type | Method → primitive mapping |
|-------|------|--------------------------|
| `Num` | `Int` | `+ → add-i64`, `- → sub-i64`, `* → mul-i64`, `/ → div-i64` |
| `Num` | `Float` | `+ → add-f64`, `- → sub-f64`, `* → mul-f64`, `/ → div-f64` |
| `Eq` | `Int` | `= → eq-i64` |
| `Eq` | `Float` | `= → eq-f64` |
| `Eq` | `Bool` | `= → eq-bool` |
| `Eq` | `String` | `= → str-eq` |
| `Ord` | `Int` | `< → lt-i64` |
| `Ord` | `Float` | `< → lt-f64` |

**Note:** `eq-bool` is a new Ring 2A primitive — boolean equality (Ring 0 only had `not`). It must be added to the primitive table alongside the existing Ring 0 primitives. `eq-bool` emits `icmp_eq` (booleans are i64 0/1).
