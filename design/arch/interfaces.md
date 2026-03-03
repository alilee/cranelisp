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
string_newtype!(JitSymbol);        // JIT linker name: "cranelisp_add$Int+Int"

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

/// Non-fatal diagnostic accumulated during compilation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Warning {
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
/// Ring 0: IntLit, FloatLit, BoolLit, Var, Let, If, Lambda, Apply, Match, Annotate
/// Ring 1: StringLit, VecLit (heap-allocated)
/// Ring 4: ParLet, ParBind, Trace, RunTests (effects)
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
        name: String,
        span: Span,
    },
    Let {
        bindings: Vec<(String, Expr)>,
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
        params: Vec<String>,
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
    ParLet {
        bindings: Vec<(String, Expr)>,
        body: Box<Expr>,
        span: Span,
    },
    ParBind {
        bindings: Vec<(String, Expr)>,
        body: Box<Expr>,
        span: Span,
    },
    Trace {
        modules: Vec<String>,
        body: Box<Expr>,
        span: Span,
    },
    RunTests {
        modules: Vec<String>,
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
        name: String,
        bindings: Vec<String>,
        span: Span,
    },
    /// Wildcard: `_`
    Wildcard {
        span: Span,
    },
    /// Variable binding: `x` (binds the scrutinee to a name)
    Var {
        name: String,
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
    pub name: String,
    pub docstring: Option<String>,
    pub params: Vec<String>,
    pub param_annotations: Vec<Option<TypeExpr>>,
    pub body: Expr,
    pub visibility: Visibility,
    pub span: Span,
}

/// One variant of a multi-signature function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DefnVariant {
    pub params: Vec<String>,
    pub param_annotations: Vec<Option<TypeExpr>>,
    pub body: Expr,
    pub span: Span,
}

/// Type expression in annotations and trait signatures.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TypeExpr {
    /// Named type: `Int`, `Bool`, `String`
    Named(String),
    /// Self type in trait methods: `Self`
    SelfType,
    /// Function type: `(Fn [Int Int] Bool)`
    FnType(Vec<TypeExpr>, Box<TypeExpr>),
    /// Type variable: `:a`, `:b`
    TypeVar(String),
    /// Applied type constructor: `(Option Int)`, `(List :a)`
    Applied(String, Vec<TypeExpr>),
}

/// Trait method signature.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitMethodSig {
    pub name: String,
    pub docstring: Option<String>,
    pub params: Vec<TypeExpr>,
    pub ret_type: TypeExpr,
    pub span: Span,
    /// Index of HKT parameter if this method uses higher-kinded types
    pub hkt_param_index: Option<usize>,
    /// Parameter names for default implementation
    pub default_param_names: Vec<String>,
    /// Default method body as Sexp (compiled on demand)
    pub default_body: Option<Sexp>,
}

/// Trait declaration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitDecl {
    pub name: String,
    pub docstring: Option<String>,
    pub type_params: Vec<String>,
    pub methods: Vec<TraitMethodSig>,
    pub visibility: Visibility,
    pub span: Span,
}

/// Trait implementation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitImpl {
    pub trait_name: String,
    pub target_type: String,
    pub type_args: Vec<String>,
    pub type_constraints: Vec<(String, String)>,
    pub methods: Vec<Defn>,
    pub span: Span,
}

/// Field in a data constructor.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FieldDef {
    pub name: String,
    pub type_expr: TypeExpr,
}

/// Data constructor (one variant of a sum type, or the sole constructor of a product type).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstructorDef {
    pub name: String,
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
        name: String,
        docstring: Option<String>,
        variants: Vec<DefnVariant>,
        visibility: Visibility,
        span: Span,
    },
    TraitDecl(TraitDecl),
    TraitImpl(TraitImpl),
    TypeDef {
        name: String,
        docstring: Option<String>,
        type_params: Vec<String>,
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
        name: String,
        docstring: Option<String>,
        variants: Vec<DefnVariant>,
        visibility: Visibility,
        span: Span,
    },
    Expr(Expr),
    TraitDecl(TraitDecl),
    TraitImpl(TraitImpl),
    TypeDef {
        name: String,
        docstring: Option<String>,
        type_params: Vec<String>,
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
    /// e.g. ADT("Option", [Type::Int]) for Option Int
    ADT(String, Vec<Type>),
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
    pub constraints: HashMap<TypeId, Vec<String>>,
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
#[derive(Debug)]
pub struct CheckResult {
    /// How each call site was resolved (trait dispatch, overload, auto-curry, builtin)
    pub method_resolutions: MethodResolutions,
    /// Names of constrained polymorphic functions requiring monomorphisation
    pub constrained_fn_names: HashSet<String>,
    /// Monomorphised function definitions generated during checking
    pub mono_defns: Vec<MonoDefn>,
    /// Type of every expression, keyed by span (for codegen heap classification)
    pub expr_types: HashMap<Span, Type>,
    /// Default trait method implementations expanded during checking
    pub default_method_defns: Vec<Defn>,
    /// Non-fatal warnings accumulated during checking
    pub warnings: Vec<Warning>,
}

/// Map from call site span to how that call was resolved.
pub type MethodResolutions = HashMap<Span, ResolvedCall>;

/// How a function call was resolved by the typechecker.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ResolvedCall {
    /// Resolved to a trait method implementation
    TraitMethod {
        trait_name: String,
        method_name: String,
        impl_type: String,
        mangled_name: String,
    },
    /// Resolved to a specific multi-sig variant
    SigDispatch {
        mangled_name: String,
    },
    /// Resolved to an auto-curried partial application
    AutoCurry {
        target_name: String,
        applied_count: usize,
    },
    /// Resolved to a builtin function
    BuiltinFn {
        name: String,
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
        param_names: Vec<String>,
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
        name: String,
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
    pub name: String,
    pub type_params: Vec<String>,
    pub constructors: Vec<ConstructorInfo>,
    pub docstring: Option<String>,
}

/// Information about a single data constructor.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstructorInfo {
    pub name: String,
    pub tag: usize,
    pub fields: Vec<FieldInfo>,
    pub docstring: Option<String>,
}

/// Information about a constructor field.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FieldInfo {
    pub name: String,
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
    Name(String),
    /// Bracket destructuring: `[fixed... & rest]`
    Bracket {
        fixed: Vec<String>,
        rest: Option<String>,
    },
}
```

### Import/Export

```rust
/// What names to import from a module.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ImportNames {
    /// Import specific names: `[Some None]`
    Specific(Vec<String>),
    /// Import all public names: `[*]`
    Glob,
    /// Import all members of a type or trait: `[Display.*]`
    MemberGlob(String),
    /// No names — alias-only: `[]`
    None,
}

/// An import declaration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImportSpec {
    pub module_path: ModuleFullPath,
    pub alias: Option<String>,
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
/// Controls batch vs interactive compilation differences.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompileMode {
    /// Direct function calls, no GOT indirection. Used for batch compilation.
    Batch,
    /// GOT-indirect calls for hot-reload. Used for REPL and module reloading.
    Interactive,
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
