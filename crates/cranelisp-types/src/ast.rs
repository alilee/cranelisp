use std::collections::HashSet;

use serde::{Deserialize, Serialize};

use crate::{Sexp, Span, Symbol, TraitName, TypeName};

// --- Type Expressions ---

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

// --- Patterns ---

/// Pattern in a match expression.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Pattern {
    /// Constructor pattern: `(Some x)`, `None`, `(Cons h t)`
    /// Ring 0: nullary constructors only (empty bindings)
    Constructor {
        name: Symbol,
        bindings: Vec<Symbol>,
        span: Span,
    },
    /// Wildcard: `_`
    Wildcard { span: Span },
    /// Variable binding: `x` (binds the scrutinee to a name)
    Var { name: Symbol, span: Span },
}

/// One arm of a match expression.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Expr,
    pub span: Span,
}

// --- Expressions ---

/// Expression AST node. Every variant carries a Span.
///
/// Spec traceability:
///   IntLit, FloatLit, BoolLit, StringLit -- spec 4.1 (Literals)
///   Var -- spec 4.2 (Variable Reference)
///   Let -- spec 4.3 (Let Expression)
///   If -- spec 4.4 (If Expression)
///   Lambda -- spec 4.5 (Lambda Expression)
///   Apply -- spec 4.6 (Function Application)
///   Match -- spec 4.8 (Match Expression)
///   Annotate -- spec 4.9 (Type Annotation)
///   VecLit -- spec 4.10 (Vec Literal)
///   Trace -- spec 12 (Runtime Model, implementation extension)
///   RunTests -- REPL-only special form (no spec section)
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
        /// true for compiler-generated match (e.g. from macro expansion)
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

    /// Parallel bind chain: produced by the bind! independence analysis pass.
    /// Semantically identical to a sequential `Let` for type-checking purposes,
    /// but codegen emits parallel IO dispatch via `IO_TAG_PAR`.
    /// spec: §10.12 (Automatic IO Scheduling)
    ParBind {
        bindings: Vec<(Symbol, Expr)>,
        body: Box<Expr>,
        span: Span,
    },
}

impl Expr {
    /// Returns the span of this expression.
    pub fn span(&self) -> Span {
        match self {
            Expr::IntLit { span, .. }
            | Expr::FloatLit { span, .. }
            | Expr::BoolLit { span, .. }
            | Expr::StringLit { span, .. }
            | Expr::Var { span, .. }
            | Expr::Let { span, .. }
            | Expr::If { span, .. }
            | Expr::Lambda { span, .. }
            | Expr::Apply { span, .. }
            | Expr::Match { span, .. }
            | Expr::VecLit { span, .. }
            | Expr::Annotate { span, .. }
            | Expr::Trace { span, .. }
            | Expr::RunTests { span, .. }
            | Expr::ParBind { span, .. } => *span,
        }
    }
}

// --- Top-Level Definitions ---

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

/// Field in a data constructor.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FieldDef {
    pub name: Symbol,
    pub type_expr: TypeExpr,
}

/// Data constructor definition.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstructorDef {
    pub name: Symbol,
    pub docstring: Option<String>,
    pub fields: Vec<FieldDef>,
    pub span: Span,
}

/// Trait method signature.
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

/// Top-level form: the unit of compilation.
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

// ---------------------------------------------------------------------------
// Free variable analysis for Expr (used by bind chain independence analysis)
// ---------------------------------------------------------------------------

/// Compute the set of free variables in an expression.
///
/// Variables listed in `globals` (top-level functions, builtins) are excluded.
/// Dotted names (e.g., `Type.Constructor`, `Trait.method`) are always treated
/// as global references and excluded.
///
/// This is a pure AST traversal with no external dependencies, suitable for
/// pre-typecheck analysis passes.
pub fn free_vars_expr(expr: &Expr, globals: &HashSet<Symbol>) -> HashSet<Symbol> {
    match expr {
        Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. } => HashSet::new(),

        Expr::Var { name, .. } => {
            // Dotted names are always global references.
            if globals.contains(name) || name.contains('.') {
                HashSet::new()
            } else {
                let mut s = HashSet::new();
                s.insert(name.clone());
                s
            }
        }

        Expr::Let { bindings, body, .. } => {
            let mut fv = HashSet::new();
            let mut bound = HashSet::new();
            for (name, val_expr) in bindings {
                let val_fv = free_vars_expr(val_expr, globals);
                for v in val_fv {
                    if !bound.contains(&v) {
                        fv.insert(v);
                    }
                }
                bound.insert(name.clone());
            }
            let body_fv = free_vars_expr(body, globals);
            for v in body_fv {
                if !bound.contains(&v) {
                    fv.insert(v);
                }
            }
            fv
        }

        Expr::If { cond, then_branch, else_branch, .. } => {
            let mut fv = free_vars_expr(cond, globals);
            fv.extend(free_vars_expr(then_branch, globals));
            fv.extend(free_vars_expr(else_branch, globals));
            fv
        }

        Expr::Lambda { params, body, .. } => {
            let body_fv = free_vars_expr(body, globals);
            let param_set: HashSet<Symbol> = params.iter().cloned().collect();
            body_fv.into_iter().filter(|v| !param_set.contains(v)).collect()
        }

        Expr::Apply { callee, args, .. } => {
            let mut fv = free_vars_expr(callee, globals);
            for arg in args {
                fv.extend(free_vars_expr(arg, globals));
            }
            fv
        }

        Expr::Match { scrutinee, arms, .. } => {
            let mut fv = free_vars_expr(scrutinee, globals);
            for arm in arms {
                let arm_fv = free_vars_expr(&arm.body, globals);
                let bound: HashSet<Symbol> = match &arm.pattern {
                    Pattern::Constructor { bindings, .. } => bindings.iter().cloned().collect(),
                    Pattern::Var { name, .. } => {
                        let mut s = HashSet::new();
                        s.insert(name.clone());
                        s
                    }
                    Pattern::Wildcard { .. } => HashSet::new(),
                };
                for v in arm_fv {
                    if !bound.contains(&v) {
                        fv.insert(v);
                    }
                }
            }
            fv
        }

        Expr::Annotate { expr, .. } => free_vars_expr(expr, globals),

        Expr::VecLit { elements, .. } => {
            let mut fv = HashSet::new();
            for elem in elements {
                fv.extend(free_vars_expr(elem, globals));
            }
            fv
        }

        Expr::ParBind { bindings, body, .. } => {
            // ParBind bindings are independent (no binding references another).
            let mut fv = HashSet::new();
            for (_, val_expr) in bindings {
                fv.extend(free_vars_expr(val_expr, globals));
            }
            let bound: HashSet<Symbol> = bindings.iter().map(|(n, _)| n.clone()).collect();
            let body_fv = free_vars_expr(body, globals);
            for v in body_fv {
                if !bound.contains(&v) {
                    fv.insert(v);
                }
            }
            fv
        }

        Expr::Trace { body, .. } => free_vars_expr(body, globals),

        Expr::RunTests { init, pass_fn, fail_fn, .. } => {
            let mut fv = free_vars_expr(init, globals);
            fv.extend(free_vars_expr(pass_fn, globals));
            fv.extend(free_vars_expr(fail_fn, globals));
            fv
        }
    }
}

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
