use std::fmt;

use serde::{Deserialize, Serialize};

use crate::error::Span;
use crate::types::Type;

/// Visibility of a top-level definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Visibility {
    Public,
    Private,
}

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
}

impl Expr {
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
            | Expr::Annotate { span, .. } => *span,
        }
    }
}

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

/// Type expression used in trait method signatures.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TypeExpr {
    Named(String),
    SelfType,
    FnType(Vec<TypeExpr>, Box<TypeExpr>),
    TypeVar(String),
    Applied(String, Vec<TypeExpr>),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitMethodSig {
    pub name: String,
    pub docstring: Option<String>,
    pub params: Vec<TypeExpr>,
    pub ret_type: TypeExpr,
    pub span: Span,
    /// For HKT trait methods: which parameter carries the type constructor.
    /// Set during `register_hkt_trait()`. None for non-HKT traits.
    pub hkt_param_index: Option<usize>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitDecl {
    pub name: String,
    pub docstring: Option<String>,
    pub type_params: Vec<String>,
    pub methods: Vec<TraitMethodSig>,
    pub visibility: Visibility,
    pub span: Span,
}

// ── ADT types ──────────────────────────────────────────────────────────

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FieldDef {
    pub name: String,
    pub type_expr: TypeExpr,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstructorDef {
    pub name: String,
    pub docstring: Option<String>,
    pub fields: Vec<FieldDef>,
    pub span: Span,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Pattern {
    Constructor {
        name: String,
        bindings: Vec<String>,
        span: Span,
    },
    Wildcard {
        span: Span,
    },
    Var {
        name: String,
        span: Span,
    },
}

impl Pattern {
    pub fn span(&self) -> Span {
        match self {
            Pattern::Constructor { span, .. }
            | Pattern::Wildcard { span }
            | Pattern::Var { span, .. } => *span,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Expr,
    pub span: Span,
}

/// A single variant in a multi-signature function definition.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DefnVariant {
    pub params: Vec<String>,
    pub param_annotations: Vec<Option<TypeExpr>>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitImpl {
    pub trait_name: String,
    pub target_type: String,
    pub type_args: Vec<String>,
    pub type_constraints: Vec<(String, String)>,
    pub methods: Vec<Defn>,
    pub span: Span,
}

impl TraitImpl {
    /// Compute the mangled target name for impl method names.
    /// - `("Option", ["Int"], [])` → `"Option$Int"`
    /// - `("Color", [], [])` → `"Color"`
    /// - `("Option", ["a"], [("a","Display")])` → `"Option"` (polymorphic)
    pub fn impl_target_mangled(&self) -> String {
        if self.type_args.is_empty() {
            self.target_type.clone()
        } else {
            // Check if any type arg is a type variable (lowercase)
            let all_concrete = self
                .type_args
                .iter()
                .all(|a| a.starts_with(|c: char| c.is_uppercase()));
            if all_concrete {
                format!("{}${}", self.target_type, self.type_args.join("+"))
            } else {
                // Polymorphic — no concrete suffix
                self.target_type.clone()
            }
        }
    }
}

#[derive(Debug, Clone)]
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

pub type Program = Vec<TopLevel>;

// ── AST pretty-printing (tree format, no spans) ───────────────────────

fn format_type_expr_display(te: &TypeExpr) -> String {
    match te {
        TypeExpr::Named(n) => n.clone(),
        TypeExpr::SelfType => "self".to_string(),
        TypeExpr::FnType(params, ret) => {
            let ps: Vec<String> = params.iter().map(format_type_expr_display).collect();
            format!("(Fn [{}] {})", ps.join(" "), format_type_expr_display(ret))
        }
        TypeExpr::TypeVar(v) => v.clone(),
        TypeExpr::Applied(name, args) => {
            let a: Vec<String> = args.iter().map(format_type_expr_display).collect();
            format!("({} {})", name, a.join(" "))
        }
    }
}

fn format_pattern_display(p: &Pattern) -> String {
    match p {
        Pattern::Constructor { name, bindings, .. } => {
            if bindings.is_empty() {
                name.clone()
            } else {
                format!("({} {})", name, bindings.join(" "))
            }
        }
        Pattern::Wildcard { .. } => "_".to_string(),
        Pattern::Var { name, .. } => name.clone(),
    }
}

impl Expr {
    /// Format as a tree with the given indentation level.
    pub fn format_tree(&self, indent: usize) -> String {
        let prefix = " ".repeat(indent);
        match self {
            Expr::IntLit { value, .. } => format!("{}IntLit {}", prefix, value),
            Expr::FloatLit { value, .. } => {
                let s = format!("{}", value);
                let float_str = if s.contains('.') {
                    s
                } else {
                    format!("{}.0", s)
                };
                format!("{}FloatLit {}", prefix, float_str)
            }
            Expr::BoolLit { value, .. } => format!("{}BoolLit {}", prefix, value),
            Expr::StringLit { value, .. } => format!("{}StringLit {:?}", prefix, value),
            Expr::Var { name, .. } => format!("{}Var {}", prefix, name),
            Expr::Let { bindings, body, .. } => {
                let mut lines = vec![format!("{}Let", prefix)];
                for (name, val) in bindings {
                    lines.push(format!("{}  {} =", prefix, name));
                    lines.push(val.format_tree(indent + 4));
                }
                lines.push(body.format_tree(indent + 2));
                lines.join("\n")
            }
            Expr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                let mut lines = vec![format!("{}If", prefix)];
                lines.push(cond.format_tree(indent + 2));
                lines.push(then_branch.format_tree(indent + 2));
                lines.push(else_branch.format_tree(indent + 2));
                lines.join("\n")
            }
            Expr::Lambda { params, body, .. } => {
                let mut lines = vec![format!("{}Lambda [{}]", prefix, params.join(" "))];
                lines.push(body.format_tree(indent + 2));
                lines.join("\n")
            }
            Expr::Apply { callee, args, .. } => {
                let mut lines = vec![format!("{}Apply", prefix)];
                lines.push(callee.format_tree(indent + 2));
                for arg in args {
                    lines.push(arg.format_tree(indent + 2));
                }
                lines.join("\n")
            }
            Expr::Match {
                scrutinee, arms, ..
            } => {
                let mut lines = vec![format!("{}Match", prefix)];
                lines.push(scrutinee.format_tree(indent + 2));
                for arm in arms {
                    lines.push(format!(
                        "{}  {}",
                        prefix,
                        format_pattern_display(&arm.pattern)
                    ));
                    lines.push(arm.body.format_tree(indent + 4));
                }
                lines.join("\n")
            }
            Expr::VecLit { elements, .. } => {
                if elements.is_empty() {
                    format!("{}VecLit []", prefix)
                } else {
                    let mut lines = vec![format!("{}VecLit", prefix)];
                    for elem in elements {
                        lines.push(elem.format_tree(indent + 2));
                    }
                    lines.join("\n")
                }
            }
            Expr::Annotate {
                annotation, expr, ..
            } => {
                let mut lines = vec![format!(
                    "{}Annotate :{}",
                    prefix,
                    format_type_expr_display(annotation)
                )];
                lines.push(expr.format_tree(indent + 2));
                lines.join("\n")
            }
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.format_tree(0))
    }
}

impl fmt::Display for Defn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Defn {} [{}]", self.name, self.params.join(" "))?;
        write!(f, "{}", self.body.format_tree(2))
    }
}

impl fmt::Display for ReplInput {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReplInput::Defn(d) => write!(f, "{}", d),
            ReplInput::DefnMulti { name, variants, .. } => {
                write!(f, "DefnMulti {}", name)?;
                for v in variants {
                    write!(f, "\n  Variant [{}]", v.params.join(" "))?;
                    write!(f, "\n{}", v.body.format_tree(4))?;
                }
                Ok(())
            }
            ReplInput::Expr(e) => write!(f, "{}", e.format_tree(0)),
            ReplInput::TraitDecl(td) => {
                write!(f, "TraitDecl {}", td.name)?;
                if !td.type_params.is_empty() {
                    write!(f, " [{}]", td.type_params.join(" "))?;
                }
                for m in &td.methods {
                    let ps: Vec<String> = m.params.iter().map(format_type_expr_display).collect();
                    write!(
                        f,
                        "\n  {} [{}] {}",
                        m.name,
                        ps.join(" "),
                        format_type_expr_display(&m.ret_type)
                    )?;
                }
                Ok(())
            }
            ReplInput::TraitImpl(ti) => {
                write!(f, "TraitImpl {} for {}", ti.trait_name, ti.target_type)?;
                if !ti.type_args.is_empty() {
                    write!(f, " [{}]", ti.type_args.join(" "))?;
                }
                for method in &ti.methods {
                    write!(f, "\n  {}", method)?;
                }
                Ok(())
            }
            ReplInput::TypeDef {
                name,
                type_params,
                constructors,
                ..
            } => {
                if type_params.is_empty() {
                    write!(f, "TypeDef {}", name)?;
                } else {
                    write!(f, "TypeDef ({} {})", name, type_params.join(" "))?;
                }
                for c in constructors {
                    if c.fields.is_empty() {
                        write!(f, "\n  {}", c.name)?;
                    } else {
                        let fields: Vec<String> = c
                            .fields
                            .iter()
                            .map(|fd| {
                                let te = format_type_expr_display(&fd.type_expr);
                                format!(":{} {}", te, fd.name)
                            })
                            .collect();
                        write!(f, "\n  {} [{}]", c.name, fields.join(" "))?;
                    }
                }
                Ok(())
            }
        }
    }
}

/// Desugar shortcut syntax: bare field names (TypeVar("")) get fresh type vars.
/// Returns (resolved_type_params, resolved_constructors).
pub fn desugar_type_def(
    _type_name: &str,
    explicit_params: &[String],
    constructors: &[ConstructorDef],
) -> (Vec<String>, Vec<ConstructorDef>) {
    // Collect all bare (untyped) field names across all constructors
    // and assign type variables a, b, c, ... in first-appearance order
    let mut next_var = 0u8;
    let mut name_to_var: std::collections::HashMap<String, String> =
        std::collections::HashMap::new();

    // First pass: discover which field names need fresh type vars
    for ctor in constructors {
        for field in &ctor.fields {
            if let TypeExpr::TypeVar(ref s) = field.type_expr {
                if s.is_empty() && !name_to_var.contains_key(&field.name) {
                    let var_name = String::from((b'a' + next_var) as char);
                    next_var += 1;
                    name_to_var.insert(field.name.clone(), var_name);
                }
            }
        }
    }

    // Resolve constructors: replace empty TypeVar with assigned variable
    let resolved_ctors: Vec<ConstructorDef> = constructors
        .iter()
        .map(|ctor| {
            let resolved_fields: Vec<FieldDef> = ctor
                .fields
                .iter()
                .map(|field| {
                    if let TypeExpr::TypeVar(ref s) = field.type_expr {
                        if s.is_empty() {
                            if let Some(var) = name_to_var.get(&field.name) {
                                return FieldDef {
                                    name: field.name.clone(),
                                    type_expr: TypeExpr::TypeVar(var.clone()),
                                };
                            }
                        }
                    }
                    field.clone()
                })
                .collect();
            ConstructorDef {
                name: ctor.name.clone(),
                docstring: ctor.docstring.clone(),
                fields: resolved_fields,
                span: ctor.span,
            }
        })
        .collect();

    // Determine type params: use explicit if provided, otherwise infer from assignments
    let type_params = if !explicit_params.is_empty() {
        explicit_params.to_vec()
    } else {
        // Collect in assignment order (a, b, c, ...)
        let mut params: Vec<String> = name_to_var.values().cloned().collect();
        params.sort();
        params.dedup();
        params
    };

    (type_params, resolved_ctors)
}

/// Extract references to all Defn items from a program.
pub fn defns(program: &Program) -> Vec<&Defn> {
    program
        .iter()
        .filter_map(|item| match item {
            TopLevel::Defn(d) => Some(d),
            _ => None,
        })
        .collect()
}

/// Extract references to all TraitDecl items from a program.
pub fn trait_decls(program: &Program) -> Vec<&TraitDecl> {
    program
        .iter()
        .filter_map(|item| match item {
            TopLevel::TraitDecl(td) => Some(td),
            _ => None,
        })
        .collect()
}

/// Extract impl method Defns with mangled names (e.g., `show$Int`, `show$Option$Int`).
pub fn impl_method_defns(program: &Program) -> Vec<Defn> {
    let mut result = Vec::new();
    for ti in trait_impls(program) {
        let target = ti.impl_target_mangled();
        for method in &ti.methods {
            result.push(Defn {
                visibility: Visibility::Public,
                name: format!("{}${}", method.name, target),
                docstring: None,
                params: method.params.clone(),
                param_annotations: method.param_annotations.clone(),
                body: method.body.clone(),
                span: method.span,
            });
        }
    }
    result
}

/// Extract references to all TraitImpl items from a program.
pub fn trait_impls(program: &Program) -> Vec<&TraitImpl> {
    program
        .iter()
        .filter_map(|item| match item {
            TopLevel::TraitImpl(ti) => Some(ti),
            _ => None,
        })
        .collect()
}

/// Extract TypeDef items from a program.
pub fn type_defs(program: &Program) -> Vec<(&str, &[String], &[ConstructorDef], Span)> {
    program
        .iter()
        .filter_map(|item| match item {
            TopLevel::TypeDef {
                name,
                type_params,
                constructors,
                span,
                ..
            } => Some((
                name.as_str(),
                type_params.as_slice(),
                constructors.as_slice(),
                *span,
            )),
            _ => None,
        })
        .collect()
}

/// Extract references to all DefnMulti items from a program.
pub fn defn_multis(program: &Program) -> Vec<(&str, &[DefnVariant], Span)> {
    program
        .iter()
        .filter_map(|item| match item {
            TopLevel::DefnMulti {
                name,
                variants,
                span,
                ..
            } => Some((name.as_str(), variants.as_slice(), *span)),
            _ => None,
        })
        .collect()
}

/// Mangle a function name with its parameter type signature.
/// e.g., mangle_sig("foo", &[Type::Int, Type::Bool]) → "foo$Int+Bool"
/// For ADTs with type args: mangle_sig("show", &[Type::ADT("Option", [Type::Int])]) → "show$Option$Int"
pub fn mangle_sig(name: &str, param_types: &[Type]) -> String {
    if param_types.is_empty() {
        format!("{}$", name)
    } else {
        let parts: Vec<String> = param_types.iter().map(mangle_type).collect();
        format!("{}${}", name, parts.join("+"))
    }
}

/// Mangle a single type into a string suitable for name mangling.
fn mangle_type(ty: &Type) -> String {
    match ty {
        Type::Int => "Int".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::String => "String".to_string(),
        Type::Float => "Float".to_string(),
        Type::Fn(_, _) => "Fn".to_string(),
        Type::ADT(name, args) => {
            if args.is_empty() {
                name.clone()
            } else {
                let arg_parts: Vec<String> = args.iter().map(mangle_type).collect();
                format!("{}${}", name, arg_parts.join("+"))
            }
        }
        Type::Var(_) => "Var".to_string(),
        Type::TyConApp(_, _) => "TyConApp".to_string(),
    }
}

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
