use std::collections::HashSet;

use serde::{Deserialize, Serialize};

use crate::{ResolvedCall, Sexp, Span, Symbol, TraitName, Type, TypeName};

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
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Expr {
    // --- Ring 0 exercised ---
    IntLit {
        value: i64,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    FloatLit {
        value: f64,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    BoolLit {
        value: bool,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    Var {
        name: Symbol,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    Let {
        bindings: Vec<(Symbol, Expr)>,
        body: Box<Expr>,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    If {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    Lambda {
        params: Vec<Symbol>,
        param_annotations: Vec<Option<TypeExpr>>,
        body: Box<Expr>,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    Apply {
        callee: Box<Expr>,
        args: Vec<Expr>,
        span: Span,
        /// How this call was resolved by the typechecker.
        /// None before typecheck; Some after body checking.
        /// Boxed to avoid bloating the Expr enum (see design/typecheck/ast-annotation.md §4.3).
        #[serde(default)]
        resolved_call: Option<Box<ResolvedCall>>,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
        span: Span,
        /// true for compiler-generated match (e.g. from macro expansion)
        compiler_generated: bool,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    Annotate {
        annotation: TypeExpr,
        expr: Box<Expr>,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },

    // --- Defined, deferred to Ring 1 ---
    StringLit {
        value: String,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    VecLit {
        elements: Vec<Expr>,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },

    // --- Defined, deferred to Ring 4 ---
    Trace {
        modules: Vec<Symbol>,
        body: Box<Expr>,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
    },
    /// Parallel bind chain: produced by the bind! independence analysis pass.
    /// Semantically identical to a sequential `Let` for type-checking purposes,
    /// but codegen emits parallel IO dispatch via `IO_TAG_PAR`.
    /// spec: §10.12 (Automatic IO Scheduling)
    ParBind {
        bindings: Vec<(Symbol, Expr)>,
        body: Box<Expr>,
        span: Span,
        #[serde(default)]
        inferred_type: Option<Box<Type>>,
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
            | Expr::ParBind { span, .. } => *span,
        }
    }

    /// Returns the inferred type annotation, if set by typecheck.
    pub fn inferred_type(&self) -> Option<&Type> {
        match self {
            Expr::IntLit { inferred_type, .. }
            | Expr::FloatLit { inferred_type, .. }
            | Expr::BoolLit { inferred_type, .. }
            | Expr::StringLit { inferred_type, .. }
            | Expr::Var { inferred_type, .. }
            | Expr::Let { inferred_type, .. }
            | Expr::If { inferred_type, .. }
            | Expr::Lambda { inferred_type, .. }
            | Expr::Apply { inferred_type, .. }
            | Expr::Match { inferred_type, .. }
            | Expr::VecLit { inferred_type, .. }
            | Expr::Annotate { inferred_type, .. }
            | Expr::Trace { inferred_type, .. }
            | Expr::ParBind { inferred_type, .. } => inferred_type.as_deref(),
        }
    }

    /// Sets the inferred type annotation on this expression node.
    pub fn set_inferred_type(&mut self, ty: Option<Box<Type>>) {
        match self {
            Expr::IntLit { inferred_type, .. }
            | Expr::FloatLit { inferred_type, .. }
            | Expr::BoolLit { inferred_type, .. }
            | Expr::StringLit { inferred_type, .. }
            | Expr::Var { inferred_type, .. }
            | Expr::Let { inferred_type, .. }
            | Expr::If { inferred_type, .. }
            | Expr::Lambda { inferred_type, .. }
            | Expr::Apply { inferred_type, .. }
            | Expr::Match { inferred_type, .. }
            | Expr::VecLit { inferred_type, .. }
            | Expr::Annotate { inferred_type, .. }
            | Expr::Trace { inferred_type, .. }
            | Expr::ParBind { inferred_type, .. } => *inferred_type = ty,
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
///
/// Unified representation for both single-sig and multi-sig functions.
/// Single-sig `(defn name [params] body)` has one variant in `variants`.
/// Multi-sig `(defn name ([p1] b1) ([p2] b2))` has multiple variants.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Defn {
    pub name: Symbol,
    pub docstring: Option<String>,
    pub variants: Vec<DefnVariant>,
    pub visibility: Visibility,
    pub span: Span,
}

impl Defn {
    /// Returns the params of a single-sig defn. Panics if multi-sig.
    pub fn params(&self) -> &[Symbol] {
        assert!(
            self.variants.len() == 1,
            "Defn::params() called on multi-sig defn '{}' with {} variants",
            self.name,
            self.variants.len()
        );
        &self.variants[0].params
    }

    /// Returns the body of a single-sig defn. Panics if multi-sig.
    pub fn body(&self) -> &Expr {
        assert!(
            self.variants.len() == 1,
            "Defn::body() called on multi-sig defn '{}' with {} variants",
            self.name,
            self.variants.len()
        );
        &self.variants[0].body
    }

    /// Returns a mutable reference to the body of a single-sig defn. Panics if multi-sig.
    pub fn body_mut(&mut self) -> &mut Expr {
        assert!(
            self.variants.len() == 1,
            "Defn::body_mut() called on multi-sig defn '{}' with {} variants",
            self.name,
            self.variants.len()
        );
        &mut self.variants[0].body
    }

    /// Returns the param annotations of a single-sig defn. Panics if multi-sig.
    pub fn param_annotations(&self) -> &[Option<TypeExpr>] {
        assert!(
            self.variants.len() == 1,
            "Defn::param_annotations() called on multi-sig defn '{}' with {} variants",
            self.name,
            self.variants.len()
        );
        &self.variants[0].param_annotations
    }

    /// Returns true if this defn has multiple signature variants.
    pub fn is_multi_sig(&self) -> bool {
        self.variants.len() > 1
    }
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

    }
}

