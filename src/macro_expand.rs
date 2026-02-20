//! Macro expansion: `defmacro` compilation and S-expression transformation.
//!
//! A macro is a function `(List Sexp) -> Sexp` that runs at compile time to
//! transform S-expressions before the AST builder sees them.
//!
//! ## Flow
//! 1. `is_defmacro(sexp)` — detect `(defmacro ...)` forms
//! 2. `parse_defmacro(sexp)` — extract name, params, rest param, body sexp
//! 3. `synthesize_macro_defn(...)` — build a Defn that wraps the body with arg destructuring
//! 4. `compile_macro(tc, jit, ...)` — type-check + compile → extract code_ptr
//! 5. `expand_sexp(sexp, env)` — recursively expand macro calls in an S-expression tree

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::ast::{Defn, Expr, MatchArm, Pattern, TypeExpr, Visibility};

/// Global counter for unique synthetic spans. Starts well above any realistic
/// source file size to avoid collisions with real source spans.
static SYNTHETIC_SPAN_COUNTER: AtomicUsize = AtomicUsize::new(1_000_000);
use crate::ast_builder::build_expr;
use crate::error::{CranelispError, Span};
use crate::jit::Jit;
use crate::marshal::{build_runtime_list, runtime_to_sexp, sexp_to_runtime};
use crate::sexp::Sexp;
use crate::typechecker::TypeChecker;
use crate::types::Type;

const MAX_EXPANSION_DEPTH: usize = 500;

// ── Data structures ────────────────────────────────────────────────────

pub struct MacroEntry {
    pub name: String,
    pub func_ptr: *const u8, // extern "C" fn(i64) -> i64
    pub docstring: Option<String>,
    pub fixed_params: Vec<String>,
    pub rest_param: Option<String>,
    pub body_sexp: Option<Sexp>,
}

pub struct MacroEnv {
    macros: HashMap<String, MacroEntry>,
}

impl Default for MacroEnv {
    fn default() -> Self {
        Self::new()
    }
}

impl MacroEnv {
    pub fn new() -> Self {
        MacroEnv {
            macros: HashMap::new(),
        }
    }

    pub fn register(
        &mut self,
        name: String,
        func_ptr: *const u8,
        docstring: Option<String>,
        fixed_params: Vec<String>,
        rest_param: Option<String>,
        body_sexp: Option<Sexp>,
    ) {
        self.macros.insert(
            name.clone(),
            MacroEntry {
                name,
                func_ptr,
                docstring,
                fixed_params,
                rest_param,
                body_sexp,
            },
        );
    }

    pub fn get(&self, name: &str) -> Option<&MacroEntry> {
        self.macros.get(name)
    }

    pub fn remove(&mut self, name: &str) {
        self.macros.remove(name);
    }

    pub fn is_empty(&self) -> bool {
        self.macros.is_empty()
    }

    pub fn names(&self) -> Vec<&str> {
        let mut names: Vec<&str> = self.macros.keys().map(|s| s.as_str()).collect();
        names.sort();
        names
    }
}

// ── Defmacro detection + parsing ───────────────────────────────────────

/// Returns true if the sexp is `(defmacro ...)` or `(defmacro- ...)`.
pub fn is_defmacro(sexp: &Sexp) -> bool {
    if let Sexp::List(children, _) = sexp {
        if let Some(Sexp::Symbol(head, _)) = children.first() {
            return head == "defmacro" || head == "defmacro-";
        }
    }
    false
}

/// Returns true if the sexp is `(begin ...)`.
pub fn is_begin(sexp: &Sexp) -> bool {
    if let Sexp::List(children, _) = sexp {
        if let Some(Sexp::Symbol(head, _)) = children.first() {
            return head == "begin";
        }
    }
    false
}

/// Flatten nested `(begin ...)` forms into individual top-level forms.
/// Non-begin forms are returned as-is in a single-element vec.
pub fn flatten_begin(sexp: Sexp) -> Vec<Sexp> {
    if is_begin(&sexp) {
        if let Sexp::List(children, _) = sexp {
            return children
                .into_iter()
                .skip(1)
                .flat_map(flatten_begin)
                .collect();
        }
    }
    vec![sexp]
}

/// Returns true if the sexp is `(deftype ...)` or `(deftype- ...)`.
pub fn is_deftype(sexp: &Sexp) -> bool {
    if let Sexp::List(children, _) = sexp {
        if let Some(Sexp::Symbol(head, _)) = children.first() {
            return head == "deftype" || head == "deftype-";
        }
    }
    false
}

/// Parsed defmacro components.
#[derive(Clone)]
pub struct DefmacroInfo {
    pub name: String,
    pub docstring: Option<String>,
    pub fixed_params: Vec<String>,
    pub rest_param: Option<String>,
    pub body_sexp: Sexp,
    pub visibility: crate::ast::Visibility,
    pub span: (usize, usize),
}

/// Parse `(defmacro name [a b & rest] body)`.
pub fn parse_defmacro(sexp: &Sexp) -> Result<DefmacroInfo, CranelispError> {
    let (children, span) = match sexp {
        Sexp::List(children, span) => (children, *span),
        _ => {
            return Err(CranelispError::ParseError {
                message: "defmacro requires a list form".to_string(),
                offset: sexp.span().0,
            })
        }
    };

    // (defmacro name [params] body) or (defmacro name "doc" [params] body)
    if children.len() < 4 || children.len() > 5 {
        return Err(CranelispError::ParseError {
            message: "defmacro requires name, optional docstring, params, and body".to_string(),
            offset: span.0,
        });
    }

    // Detect visibility from head form
    let visibility = match &children[0] {
        Sexp::Symbol(head, _) if head == "defmacro-" => crate::ast::Visibility::Private,
        _ => crate::ast::Visibility::Public,
    };

    let name = match &children[1] {
        Sexp::Symbol(n, _) => n.clone(),
        _ => {
            return Err(CranelispError::ParseError {
                message: "defmacro name must be a symbol".to_string(),
                offset: children[1].span().0,
            })
        }
    };

    // Optional docstring between name and params
    let (docstring, params_idx) = if children.len() == 5 {
        match &children[2] {
            Sexp::Str(s, _) => (Some(s.clone()), 3),
            _ => {
                return Err(CranelispError::ParseError {
                    message: "expected docstring or params after defmacro name".to_string(),
                    offset: children[2].span().0,
                })
            }
        }
    } else {
        (None, 2)
    };

    let params = match &children[params_idx] {
        Sexp::Bracket(items, _) => items,
        _ => {
            return Err(CranelispError::ParseError {
                message: "defmacro params must be a bracket list".to_string(),
                offset: children[params_idx].span().0,
            })
        }
    };

    // Parse params: [a b & rest] or [a b] or [& rest] or []
    let mut fixed_params = Vec::new();
    let mut rest_param = None;
    let mut i = 0;
    while i < params.len() {
        match &params[i] {
            Sexp::Symbol(s, _) if s == "&" => {
                // Next must be the rest param name
                if i + 1 >= params.len() {
                    return Err(CranelispError::ParseError {
                        message: "& must be followed by rest parameter name".to_string(),
                        offset: params[i].span().0,
                    });
                }
                match &params[i + 1] {
                    Sexp::Symbol(rname, _) => rest_param = Some(rname.clone()),
                    _ => {
                        return Err(CranelispError::ParseError {
                            message: "rest parameter must be a symbol".to_string(),
                            offset: params[i + 1].span().0,
                        })
                    }
                }
                i += 2;
            }
            Sexp::Symbol(pname, _) => {
                fixed_params.push(pname.clone());
                i += 1;
            }
            _ => {
                return Err(CranelispError::ParseError {
                    message: "defmacro param must be a symbol".to_string(),
                    offset: params[i].span().0,
                })
            }
        }
    }

    let body_idx = params_idx + 1;

    Ok(DefmacroInfo {
        name,
        docstring,
        fixed_params,
        rest_param,
        body_sexp: children[body_idx].clone(),
        visibility,
        span,
    })
}

// ── Macro body synthesis ───────────────────────────────────────────────

/// Synthesize a `Defn` that wraps the macro body with argument destructuring.
///
/// Given `(defmacro foo [a b & rest] body)`, generates nested match:
/// ```text
/// (defn __macro_foo__ [:(List Sexp) __args__]
///   (match __args__
///     [(Cons a __t1__)
///      (match __t1__
///        [(Cons b rest) body])]))
/// ```
///
/// Uses `match` instead of `let`+`head`/`tail` because match patterns
/// correctly increment RC on extracted fields, preventing use-after-free.
pub fn synthesize_macro_defn(info: &DefmacroInfo) -> Result<Defn, CranelispError> {
    let fn_name = format!("__macro_{}__", info.name);
    let args_name = "__args__";
    let span = info.span;

    // Expand quasiquotes in the body sexp before building AST
    let body_sexp = expand_quasiquotes(&info.body_sexp)?;

    // Build the body expr from the (possibly expanded) body sexp
    let body_expr = build_expr(&body_sexp)?;

    // Wrap body in nested match expressions for arg destructuring
    let wrapped_body = if info.fixed_params.is_empty() && info.rest_param.is_none() {
        body_expr
    } else {
        build_match_chain(
            args_name,
            &info.fixed_params,
            &info.rest_param,
            body_expr,
            span,
        )
    };

    // Parameter annotation: :(SList Sexp)
    let param_annotation = TypeExpr::Applied(
        "SList".to_string(),
        vec![TypeExpr::Named("Sexp".to_string())],
    );

    Ok(Defn {
        visibility: Visibility::Public,
        name: fn_name,
        docstring: None,
        params: vec![args_name.to_string()],
        param_annotations: vec![Some(param_annotation)],
        body: wrapped_body,
        span,
    })
}

/// Build nested match expressions to destructure a list into params.
///
/// Each level matches `(Cons param tail)` and recurses on the tail.
/// Uses unique synthetic spans for each match level so that expr_types entries
/// don't collide (the typechecker uses spans as keys, and shared spans cause
/// the scrutinee's type to be overwritten by the body's type).
fn build_match_chain(
    scrutinee_name: &str,
    params: &[String],
    rest_param: &Option<String>,
    body: Expr,
    span: Span,
) -> Expr {
    // Use unique synthetic spans for the match wrapper, scrutinee, and pattern.
    // The expr_types map is keyed by span, so if the scrutinee Var and the match
    // expression share a span, the match result type overwrites the scrutinee type.
    // This causes heap_category to misidentify Mixed ADTs (e.g. List) as AlwaysHeap.
    let depth = params.len() + if rest_param.is_some() { 1 } else { 0 };
    let match_span = (span.0 + depth * 3 + 1, span.1 + depth * 3 + 1);
    let scrut_span = (span.0 + depth * 3 + 2, span.1 + depth * 3 + 2);
    let pat_span = (span.0 + depth * 3 + 3, span.1 + depth * 3 + 3);

    if params.is_empty() {
        if let Some(rest_name) = rest_param {
            // Bind remaining list to rest_name via a Var pattern (increments RC)
            Expr::Match {
                scrutinee: Box::new(Expr::Var {
                    name: scrutinee_name.to_string(),
                    span: scrut_span,
                }),
                arms: vec![MatchArm {
                    pattern: Pattern::Var {
                        name: rest_name.clone(),
                        span: pat_span,
                    },
                    body,
                    span: pat_span,
                }],
                span: match_span,
            }
        } else {
            body
        }
    } else {
        let param = &params[0];

        // Determine the tail binding name
        let tail_binding = if params.len() == 1 {
            if let Some(rest_name) = rest_param {
                // Last fixed param: tail IS the rest param
                rest_name.clone()
            } else {
                format!("__t{}__", 0)
            }
        } else {
            format!("__t{}__", params.len() - 1)
        };

        // Build inner body: recurse for remaining params, or just the body
        let inner_body = if params.len() == 1 && rest_param.is_some() {
            // Tail already bound as rest param
            body
        } else {
            build_match_chain(&tail_binding, &params[1..], rest_param, body, span)
        };

        Expr::Match {
            scrutinee: Box::new(Expr::Var {
                name: scrutinee_name.to_string(),
                span: scrut_span,
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: "SCons".to_string(),
                    bindings: vec![param.clone(), tail_binding],
                    span: pat_span,
                },
                body: inner_body,
                span: pat_span,
            }],
            span: match_span,
        }
    }
}

// ── Macro compilation ──────────────────────────────────────────────────

/// Compile a defmacro form: synthesize defn → type-check → compile → extract code_ptr.
///
/// If `macro_env` is provided, macros in the body sexp (e.g. `(list ...)`) are
/// expanded before the body AST is built.
pub fn compile_macro(
    tc: &mut TypeChecker,
    jit: &mut Jit,
    info: &DefmacroInfo,
    macro_env: Option<&MacroEnv>,
) -> Result<*const u8, CranelispError> {
    // Expand macros in the body sexp (e.g. list, bind!) before synthesis
    let info = if let Some(env) = macro_env {
        if !env.is_empty() {
            let expanded_body = expand_sexp(info.body_sexp.clone(), env, 0)?;
            DefmacroInfo {
                body_sexp: expanded_body,
                name: info.name.clone(),
                docstring: info.docstring.clone(),
                fixed_params: info.fixed_params.clone(),
                rest_param: info.rest_param.clone(),
                visibility: info.visibility,
                span: info.span,
            }
        } else {
            info.clone()
        }
    } else {
        info.clone()
    };
    let defn = synthesize_macro_defn(&info)?;

    tc.check_defn(&defn)?;
    let mut mr = tc.resolve_methods()?;
    tc.resolve_overloads(&mut mr)?;
    let et = tc.resolve_expr_types();
    let scheme = tc.finalize_defn_type(&defn.name);

    // Verify return type is Sexp
    if let Type::Fn(_, ref ret) = scheme.ty {
        let resolved_ret = tc.resolve(ret);
        if resolved_ret != Type::ADT("Sexp".to_string(), vec![]) {
            return Err(CranelispError::TypeError {
                message: format!(
                    "macro '{}' body has type {}, expected Sexp",
                    info.name, resolved_ret
                ),
                span: info.span,
            });
        }
    }

    let mod_name = tc.current_module_name().to_string();
    let mod_path = crate::module::ModuleFullPath::from(mod_name.as_str());
    let slot = tc.modules.get_mut(&mod_path).unwrap().allocate_got_slot(defn.span)?;
    let fn_slots = jit.build_fn_slots_from_modules(&tc.modules);
    let meta = jit.compile_defn(&defn, &scheme, &mr, &et, slot, &fn_slots, &tc.modules)?;
    tc.modules.get_mut(&mod_path).unwrap().write_got_slot(slot, meta.code_ptr);

    Ok(meta.code_ptr)
}

// ── Macro invocation ───────────────────────────────────────────────────

/// Call a compiled macro function with the given arguments.
///
/// Marshals each arg sexp → runtime, builds a runtime List, calls the
/// function pointer, and unmarshals the result back to a Sexp.
fn call_macro(entry: &MacroEntry, args: &[Sexp]) -> Sexp {
    let runtime_args: Vec<i64> = args.iter().map(sexp_to_runtime).collect();
    let runtime_list = build_runtime_list(&runtime_args);

    // Named functions compiled via compile_function_indirect have the raw
    // parameter signature (params...) -> i64, not the closure convention.
    // Our macro fn has one param: (args: i64) -> i64.
    let func: extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(entry.func_ptr) };
    let result = func(runtime_list);
    runtime_to_sexp(result)
}

/// Rewrite all (0,0) spans in a Sexp to unique synthetic spans.
/// Uses a global atomic counter so that nested macro expansions
/// never produce colliding spans.
fn rewrite_spans(sexp: Sexp, _call_span: (usize, usize)) -> Sexp {
    rewrite_spans_inner(sexp)
}

fn rewrite_spans_inner(sexp: Sexp) -> Sexp {
    let next_span = || -> (usize, usize) {
        let n = SYNTHETIC_SPAN_COUNTER.fetch_add(1, Ordering::Relaxed);
        (n, n)
    };
    match sexp {
        Sexp::Symbol(s, sp) => Sexp::Symbol(s, if sp == (0, 0) { next_span() } else { sp }),
        Sexp::Int(v, sp) => Sexp::Int(v, if sp == (0, 0) { next_span() } else { sp }),
        Sexp::Float(v, sp) => Sexp::Float(v, if sp == (0, 0) { next_span() } else { sp }),
        Sexp::Bool(v, sp) => Sexp::Bool(v, if sp == (0, 0) { next_span() } else { sp }),
        Sexp::Str(s, sp) => Sexp::Str(s, if sp == (0, 0) { next_span() } else { sp }),
        Sexp::List(children, sp) => {
            let rewritten: Vec<Sexp> = children
                .into_iter()
                .map(rewrite_spans_inner)
                .collect();
            Sexp::List(
                rewritten,
                if sp == (0, 0) { next_span() } else { sp },
            )
        }
        Sexp::Bracket(children, sp) => {
            let rewritten: Vec<Sexp> = children
                .into_iter()
                .map(rewrite_spans_inner)
                .collect();
            Sexp::Bracket(
                rewritten,
                if sp == (0, 0) { next_span() } else { sp },
            )
        }
    }
}

// ── Quasiquote expansion ──────────────────────────────────────────────

/// Synthetic span used for generated nodes — `rewrite_spans` will replace these.
const SYN: (usize, usize) = (0, 0);

/// Check if children represent `(unquote expr)`.
fn is_unquote(children: &[Sexp]) -> bool {
    children.len() == 2 && matches!(&children[0], Sexp::Symbol(s, _) if s == "unquote")
}

/// Check if children represent `(unquote-splicing expr)`.
fn is_unquote_splicing(children: &[Sexp]) -> bool {
    children.len() == 2 && matches!(&children[0], Sexp::Symbol(s, _) if s == "unquote-splicing")
}

/// Check if children represent `(quasiquote form)`.
fn is_quasiquote(children: &[Sexp]) -> bool {
    children.len() == 2 && matches!(&children[0], Sexp::Symbol(s, _) if s == "quasiquote")
}

/// Build `(SexpSym "name")`.
fn make_sexp_sym(name: &str) -> Sexp {
    Sexp::List(
        vec![
            Sexp::Symbol("SexpSym".to_string(), SYN),
            Sexp::Str(name.to_string(), SYN),
        ],
        SYN,
    )
}

/// Build `(SexpInt val)`.
fn make_sexp_int(val: i64) -> Sexp {
    Sexp::List(
        vec![
            Sexp::Symbol("SexpInt".to_string(), SYN),
            Sexp::Int(val, SYN),
        ],
        SYN,
    )
}

/// Build `(SexpFloat val)`.
fn make_sexp_float(val: f64) -> Sexp {
    Sexp::List(
        vec![
            Sexp::Symbol("SexpFloat".to_string(), SYN),
            Sexp::Float(val, SYN),
        ],
        SYN,
    )
}

/// Build `(SexpBool val)`.
fn make_sexp_bool(val: bool) -> Sexp {
    Sexp::List(
        vec![
            Sexp::Symbol("SexpBool".to_string(), SYN),
            Sexp::Bool(val, SYN),
        ],
        SYN,
    )
}

/// Build `(SexpStr "val")`.
fn make_sexp_str(val: &str) -> Sexp {
    Sexp::List(
        vec![
            Sexp::Symbol("SexpStr".to_string(), SYN),
            Sexp::Str(val.to_string(), SYN),
        ],
        SYN,
    )
}

/// Build `(CtorName items_sexp)` where CtorName is SexpList or SexpBracket.
fn make_sexp_container(ctor: &str, items_sexp: Sexp) -> Sexp {
    Sexp::List(vec![Sexp::Symbol(ctor.to_string(), SYN), items_sexp], SYN)
}

/// Build nested `(SCons e0 (SCons e1 ... SNil))`.
fn make_list_call(elements: Vec<Sexp>) -> Sexp {
    let nil = Sexp::Symbol("SNil".to_string(), SYN);
    elements.into_iter().rev().fold(nil, |acc, elem| {
        Sexp::List(vec![Sexp::Symbol("SCons".to_string(), SYN), elem, acc], SYN)
    })
}

/// Build `(sconcat a b)`.
fn make_concat(a: Sexp, b: Sexp) -> Sexp {
    Sexp::List(vec![Sexp::Symbol("sconcat".to_string(), SYN), a, b], SYN)
}

/// Expand a quasiquote template at the given nesting level.
///
/// Level 0 means we're inside the outermost quasiquote and should evaluate
/// unquotes. Higher levels mean we're inside nested quasiquotes and should
/// quote unquote forms literally.
fn expand_qq_template(template: &Sexp, level: usize) -> Result<Sexp, CranelispError> {
    match template {
        // Atoms → constructor calls
        Sexp::Symbol(s, _) => Ok(make_sexp_sym(s)),
        Sexp::Int(v, _) => Ok(make_sexp_int(*v)),
        Sexp::Float(v, _) => Ok(make_sexp_float(*v)),
        Sexp::Bool(v, _) => Ok(make_sexp_bool(*v)),
        Sexp::Str(s, _) => Ok(make_sexp_str(s)),

        // Lists — check for special forms first
        Sexp::List(children, span) => {
            if children.is_empty() {
                return Ok(make_sexp_container("SexpList", make_list_call(vec![])));
            }

            // (unquote expr) at level 0 → return expr as-is
            if is_unquote(children) {
                if level == 0 {
                    return Ok(children[1].clone());
                } else {
                    // Deeper level: decrement and recurse, wrap result
                    let inner = expand_qq_template(&children[1], level - 1)?;
                    return Ok(make_sexp_container(
                        "SexpList",
                        make_list_call(vec![make_sexp_sym("unquote"), inner]),
                    ));
                }
            }

            // (unquote-splicing expr) at top level → error
            if is_unquote_splicing(children) {
                if level == 0 {
                    return Err(CranelispError::ParseError {
                        message: "unquote-splicing (~@) not valid at top level of quasiquote"
                            .to_string(),
                        offset: span.0,
                    });
                } else {
                    let inner = expand_qq_template(&children[1], level - 1)?;
                    return Ok(make_sexp_container(
                        "SexpList",
                        make_list_call(vec![make_sexp_sym("unquote-splicing"), inner]),
                    ));
                }
            }

            // (quasiquote form) → increment level
            if is_quasiquote(children) {
                let inner = expand_qq_template(&children[1], level + 1)?;
                return Ok(make_sexp_container(
                    "SexpList",
                    make_list_call(vec![make_sexp_sym("quasiquote"), inner]),
                ));
            }

            // Regular list — check for splicing
            expand_qq_list_children(children, level, "SexpList")
        }

        // Brackets — same as lists but with SexpBracket constructor
        Sexp::Bracket(children, _) => {
            if children.is_empty() {
                return Ok(make_sexp_container("SexpBracket", make_list_call(vec![])));
            }
            expand_qq_list_children(children, level, "SexpBracket")
        }
    }
}

/// Expand children of a list/bracket form within quasiquote.
///
/// If no child uses `~@`, produces `(Ctor (list qq(c0) qq(c1) ...))`.
/// If any child uses `~@`, segments into groups and chains with `concat`.
fn expand_qq_list_children(
    children: &[Sexp],
    level: usize,
    ctor: &str,
) -> Result<Sexp, CranelispError> {
    // Check if any child is a splice at this level
    let has_splice = level == 0
        && children
            .iter()
            .any(|c| matches!(c, Sexp::List(ch, _) if is_unquote_splicing(ch)));

    if !has_splice {
        // Simple case: no splicing, just recurse on each child
        let expanded: Vec<Sexp> = children
            .iter()
            .map(|c| expand_qq_template(c, level))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(make_sexp_container(ctor, make_list_call(expanded)))
    } else {
        // Splicing case: segment into groups
        // Each non-splice element gets wrapped in (list elem)
        // Each splice element contributes its expression directly
        // Chain everything with concat
        let mut segments: Vec<Sexp> = Vec::new();
        let mut current_group: Vec<Sexp> = Vec::new();

        for child in children {
            if let Sexp::List(ch, _) = child {
                if is_unquote_splicing(ch) && level == 0 {
                    // Flush current group
                    if !current_group.is_empty() {
                        segments.push(make_list_call(std::mem::take(&mut current_group)));
                    }
                    // Add splice expression directly
                    segments.push(ch[1].clone());
                    continue;
                }
            }
            current_group.push(expand_qq_template(child, level)?);
        }
        // Flush remaining group
        if !current_group.is_empty() {
            segments.push(make_list_call(current_group));
        }

        // Chain segments with concat: concat(s0, concat(s1, concat(s2, ...)))
        let mut result = segments.pop().unwrap(); // at least one segment exists
        while let Some(seg) = segments.pop() {
            result = make_concat(seg, result);
        }

        Ok(make_sexp_container(ctor, result))
    }
}

/// Walk a Sexp tree and expand any `(quasiquote ...)` forms.
///
/// This is used both in macro bodies (via `synthesize_macro_defn`) and in
/// general code (via `expand_sexp`).
pub fn expand_quasiquotes(sexp: &Sexp) -> Result<Sexp, CranelispError> {
    match sexp {
        Sexp::List(children, span) if !children.is_empty() => {
            if is_quasiquote(children) {
                let expanded = expand_qq_template(&children[1], 0)?;
                // Recurse into the result in case unquoted sub-expressions
                // contain their own quasiquotes
                return expand_quasiquotes(&expanded);
            }

            // Recurse into children
            let expanded: Vec<Sexp> = children
                .iter()
                .map(expand_quasiquotes)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Sexp::List(expanded, *span))
        }
        Sexp::List(children, span) => Ok(Sexp::List(children.clone(), *span)),
        Sexp::Bracket(children, span) => {
            let expanded: Vec<Sexp> = children
                .iter()
                .map(expand_quasiquotes)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Sexp::Bracket(expanded, *span))
        }
        other => Ok(other.clone()),
    }
}

// ── Expansion engine ───────────────────────────────────────────────────

/// Recursively expand macro calls in an S-expression tree.
pub fn expand_sexp(sexp: Sexp, env: &MacroEnv, depth: usize) -> Result<Sexp, CranelispError> {
    if depth > MAX_EXPANSION_DEPTH {
        return Err(CranelispError::ParseError {
            message: "macro expansion depth limit exceeded (possible infinite expansion)"
                .to_string(),
            offset: sexp.span().0,
        });
    }

    // Don't expand defmacro or begin forms themselves
    if is_defmacro(&sexp) || is_begin(&sexp) {
        return Ok(sexp);
    }

    match sexp {
        Sexp::List(children, span) if !children.is_empty() => {
            // Expand quasiquote forms before checking macros
            if let Sexp::Symbol(ref head, _) = children[0] {
                if head == "quasiquote" && children.len() == 2 {
                    let expanded = expand_qq_template(&children[1], 0)?;
                    // Recurse to expand any remaining quasiquotes or macro calls
                    return expand_sexp(expanded, env, depth + 1);
                }
            }

            // Check if head is a macro name
            if let Sexp::Symbol(ref head, _) = children[0] {
                if let Some(entry) = env.get(head) {
                    let args = &children[1..];
                    let expanded = call_macro(entry, args);
                    let expanded = rewrite_spans(expanded, span);
                    // Re-expand in case the result contains more macro calls
                    return expand_sexp(expanded, env, depth + 1);
                }
            }

            // Not a macro call — recursively expand children
            let expanded_children: Vec<Sexp> = children
                .into_iter()
                .map(|c| expand_sexp(c, env, depth))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Sexp::List(expanded_children, span))
        }
        Sexp::List(children, span) => {
            // Empty list — pass through
            Ok(Sexp::List(children, span))
        }
        Sexp::Bracket(children, span) => {
            let expanded_children: Vec<Sexp> = children
                .into_iter()
                .map(|c| expand_sexp(c, env, depth))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Sexp::Bracket(expanded_children, span))
        }
        // Bare symbol: expand zero-arg macros
        Sexp::Symbol(ref name, _) => {
            if let Some(entry) = env.get(name) {
                if entry.fixed_params.is_empty() && entry.rest_param.is_none() {
                    let expanded = call_macro(entry, &[]);
                    let expanded = rewrite_spans(expanded, sexp.span());
                    return expand_sexp(expanded, env, depth + 1);
                }
            }
            Ok(sexp)
        }
        // Other atoms pass through unchanged
        other => Ok(other),
    }
}

/// Expand all sexps in a slice, returning the expanded forms.
/// Defmacro forms are excluded from the output (they're consumed during compilation).
pub fn expand_sexps(sexps: Vec<Sexp>, env: &MacroEnv) -> Result<Vec<Sexp>, CranelispError> {
    let mut result = Vec::new();
    for sexp in sexps {
        if is_defmacro(&sexp) || is_begin(&sexp) {
            continue; // Already processed during macro compilation phase
        }
        result.push(expand_sexp(sexp, env, 0)?);
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sexp::parse_sexp;

    #[test]
    fn test_is_defmacro() {
        let sexp = parse_sexp("(defmacro foo [x] x)").unwrap();
        assert!(is_defmacro(&sexp));
    }

    #[test]
    fn test_is_not_defmacro() {
        let sexp = parse_sexp("(defn foo [x] x)").unwrap();
        assert!(!is_defmacro(&sexp));
    }

    #[test]
    fn test_is_defmacro_atom() {
        let sexp = parse_sexp("42").unwrap();
        assert!(!is_defmacro(&sexp));
    }

    #[test]
    fn test_parse_defmacro_no_params() {
        let sexp = parse_sexp("(defmacro always-42 [] (SexpInt 42))").unwrap();
        let info = parse_defmacro(&sexp).unwrap();
        assert_eq!(info.name, "always-42");
        assert!(info.fixed_params.is_empty());
        assert!(info.rest_param.is_none());
    }

    #[test]
    fn test_parse_defmacro_fixed_params() {
        let sexp = parse_sexp("(defmacro foo [a b] a)").unwrap();
        let info = parse_defmacro(&sexp).unwrap();
        assert_eq!(info.name, "foo");
        assert_eq!(info.fixed_params, vec!["a", "b"]);
        assert!(info.rest_param.is_none());
    }

    #[test]
    fn test_parse_defmacro_with_rest() {
        let sexp = parse_sexp("(defmacro foo [a & rest] a)").unwrap();
        let info = parse_defmacro(&sexp).unwrap();
        assert_eq!(info.name, "foo");
        assert_eq!(info.fixed_params, vec!["a"]);
        assert_eq!(info.rest_param, Some("rest".to_string()));
    }

    #[test]
    fn test_parse_defmacro_rest_only() {
        let sexp = parse_sexp("(defmacro foo [& args] (head args))").unwrap();
        let info = parse_defmacro(&sexp).unwrap();
        assert_eq!(info.name, "foo");
        assert!(info.fixed_params.is_empty());
        assert_eq!(info.rest_param, Some("args".to_string()));
    }

    #[test]
    fn test_synthesize_no_params() {
        let sexp = parse_sexp("(defmacro always-42 [] (SexpInt 42))").unwrap();
        let info = parse_defmacro(&sexp).unwrap();
        let defn = synthesize_macro_defn(&info).unwrap();
        assert_eq!(defn.name, "__macro_always-42__");
        assert_eq!(defn.params, vec!["__args__"]);
        // Body should be the raw expression (no let wrapper for zero params)
        assert!(matches!(defn.body, Expr::Apply { .. }));
    }

    #[test]
    fn test_synthesize_fixed_params() {
        let sexp = parse_sexp("(defmacro foo [a b] a)").unwrap();
        let info = parse_defmacro(&sexp).unwrap();
        let defn = synthesize_macro_defn(&info).unwrap();
        assert_eq!(defn.name, "__macro_foo__");
        // Should have nested Match for destructuring: match __args__ [(Cons a __t1__) (match __t1__ [(Cons b __t0__) body])]
        match &defn.body {
            Expr::Match { arms, .. } => {
                assert_eq!(arms.len(), 1);
                match &arms[0].pattern {
                    Pattern::Constructor { name, bindings, .. } => {
                        assert_eq!(name, "SCons");
                        assert_eq!(bindings[0], "a");
                    }
                    _ => panic!("expected Cons pattern"),
                }
                // Inner match for b
                match &arms[0].body {
                    Expr::Match {
                        arms: inner_arms, ..
                    } => match &inner_arms[0].pattern {
                        Pattern::Constructor { name, bindings, .. } => {
                            assert_eq!(name, "SCons");
                            assert_eq!(bindings[0], "b");
                        }
                        _ => panic!("expected inner Cons pattern"),
                    },
                    _ => panic!("expected inner Match"),
                }
            }
            _ => panic!("expected Match wrapper, got {:?}", defn.body),
        }
    }

    #[test]
    fn test_synthesize_with_rest() {
        let sexp = parse_sexp("(defmacro foo [a & rest] a)").unwrap();
        let info = parse_defmacro(&sexp).unwrap();
        let defn = synthesize_macro_defn(&info).unwrap();
        // match __args__ [(Cons a rest) body]
        match &defn.body {
            Expr::Match { arms, .. } => {
                assert_eq!(arms.len(), 1);
                match &arms[0].pattern {
                    Pattern::Constructor { name, bindings, .. } => {
                        assert_eq!(name, "SCons");
                        assert_eq!(bindings[0], "a");
                        assert_eq!(bindings[1], "rest");
                    }
                    _ => panic!("expected Cons pattern"),
                }
            }
            _ => panic!("expected Match wrapper"),
        }
    }

    #[test]
    fn test_expand_no_macros() {
        let env = MacroEnv::new();
        let sexp = parse_sexp("(+ 1 2)").unwrap();
        let expanded = expand_sexp(sexp.clone(), &env, 0).unwrap();
        // Should be unchanged
        assert_eq!(format!("{}", expanded), format!("{}", sexp));
    }

    #[test]
    fn test_expand_skips_defmacro() {
        let env = MacroEnv::new();
        let sexp = parse_sexp("(defmacro foo [x] x)").unwrap();
        let expanded = expand_sexp(sexp.clone(), &env, 0).unwrap();
        assert!(is_defmacro(&expanded));
    }

    #[test]
    fn test_rewrite_spans() {
        let sexp = Sexp::List(
            vec![
                Sexp::Symbol("+".to_string(), (0, 0)),
                Sexp::Int(1, (0, 0)),
                Sexp::Int(2, (0, 0)),
            ],
            (0, 0),
        );
        let rewritten = rewrite_spans(sexp, (10, 20));
        match rewritten {
            Sexp::List(children, span) => {
                // Each (0,0) node gets a unique span from global counter
                assert_ne!(children[0].span(), children[1].span());
                assert_ne!(children[1].span(), children[2].span());
                assert_ne!(span, children[0].span());
                // Spans are above the 1_000_000 base
                assert!(children[0].span().0 >= 1_000_000);
            }
            _ => panic!("expected List"),
        }
    }

    #[test]
    fn test_rewrite_spans_preserves_nonzero() {
        let sexp = Sexp::Symbol("foo".to_string(), (5, 8));
        let rewritten = rewrite_spans(sexp, (10, 20));
        assert_eq!(rewritten.span(), (5, 8)); // non-(0,0) preserved
    }

    // ── Quasiquote expansion tests ───────────────────────────────────

    #[test]
    fn test_qq_symbol() {
        let template = Sexp::Symbol("foo".to_string(), (0, 3));
        let result = expand_qq_template(&template, 0).unwrap();
        // Should produce (SexpSym "foo")
        let s = format!("{}", result);
        assert_eq!(s, r#"(SexpSym "foo")"#);
    }

    #[test]
    fn test_qq_int() {
        let template = Sexp::Int(42, (0, 2));
        let result = expand_qq_template(&template, 0).unwrap();
        let s = format!("{}", result);
        assert_eq!(s, "(SexpInt 42)");
    }

    #[test]
    fn test_qq_float() {
        let template = Sexp::Float(3.14, (0, 4));
        let result = expand_qq_template(&template, 0).unwrap();
        let s = format!("{}", result);
        assert_eq!(s, "(SexpFloat 3.14)");
    }

    #[test]
    fn test_qq_bool() {
        let template = Sexp::Bool(true, (0, 4));
        let result = expand_qq_template(&template, 0).unwrap();
        let s = format!("{}", result);
        assert_eq!(s, "(SexpBool true)");
    }

    #[test]
    fn test_qq_str() {
        let template = Sexp::Str("hello".to_string(), (0, 7));
        let result = expand_qq_template(&template, 0).unwrap();
        let s = format!("{}", result);
        assert_eq!(s, r#"(SexpStr "hello")"#);
    }

    #[test]
    fn test_qq_list_no_unquotes() {
        // `(if true 42) → (SexpList (list (SexpSym "if") (SexpBool true) (SexpInt 42)))
        let template = Sexp::List(
            vec![
                Sexp::Symbol("if".to_string(), SYN),
                Sexp::Bool(true, SYN),
                Sexp::Int(42, SYN),
            ],
            SYN,
        );
        let result = expand_qq_template(&template, 0).unwrap();
        let s = format!("{}", result);
        assert!(s.contains("SexpList"));
        assert!(s.contains(r#"(SexpSym "if")"#));
        assert!(s.contains("(SexpBool true)"));
        assert!(s.contains("(SexpInt 42)"));
    }

    #[test]
    fn test_qq_list_with_unquote() {
        // `(if ~c ~t ~e) → (SexpList (list (SexpSym "if") c t e))
        let template = Sexp::List(
            vec![
                Sexp::Symbol("if".to_string(), SYN),
                Sexp::List(
                    vec![
                        Sexp::Symbol("unquote".to_string(), SYN),
                        Sexp::Symbol("c".to_string(), SYN),
                    ],
                    SYN,
                ),
                Sexp::List(
                    vec![
                        Sexp::Symbol("unquote".to_string(), SYN),
                        Sexp::Symbol("t".to_string(), SYN),
                    ],
                    SYN,
                ),
                Sexp::List(
                    vec![
                        Sexp::Symbol("unquote".to_string(), SYN),
                        Sexp::Symbol("e".to_string(), SYN),
                    ],
                    SYN,
                ),
            ],
            SYN,
        );
        let result = expand_qq_template(&template, 0).unwrap();
        let s = format!("{}", result);
        // Should have (SexpList (list (SexpSym "if") c t e))
        assert!(s.contains("SexpList"));
        assert!(s.contains(r#"(SexpSym "if")"#));
        assert!(s.contains(" c "));
        assert!(s.contains(" t "));
    }

    #[test]
    fn test_qq_bracket_with_unquote() {
        // `[~v ~expr] → (SexpBracket (list v expr))
        let template = Sexp::Bracket(
            vec![
                Sexp::List(
                    vec![
                        Sexp::Symbol("unquote".to_string(), SYN),
                        Sexp::Symbol("v".to_string(), SYN),
                    ],
                    SYN,
                ),
                Sexp::List(
                    vec![
                        Sexp::Symbol("unquote".to_string(), SYN),
                        Sexp::Symbol("expr".to_string(), SYN),
                    ],
                    SYN,
                ),
            ],
            SYN,
        );
        let result = expand_qq_template(&template, 0).unwrap();
        let s = format!("{}", result);
        assert!(s.contains("SexpBracket"));
        assert!(s.contains(" v "));
        assert!(s.contains(" expr"));
    }

    #[test]
    fn test_qq_list_with_splicing() {
        // `(foo ~@args bar) → (SexpList (concat (list (SexpSym "foo")) (concat args (list (SexpSym "bar")))))
        let template = Sexp::List(
            vec![
                Sexp::Symbol("foo".to_string(), SYN),
                Sexp::List(
                    vec![
                        Sexp::Symbol("unquote-splicing".to_string(), SYN),
                        Sexp::Symbol("args".to_string(), SYN),
                    ],
                    SYN,
                ),
                Sexp::Symbol("bar".to_string(), SYN),
            ],
            SYN,
        );
        let result = expand_qq_template(&template, 0).unwrap();
        let s = format!("{}", result);
        assert!(s.contains("SexpList"));
        assert!(s.contains("concat"));
        assert!(s.contains("args"));
    }

    #[test]
    fn test_qq_nested_quasiquote() {
        // Nested QQ: `(a `(b ~c)) at level 0
        // The inner `(b ~c) should stay quoted (level incremented)
        let template = Sexp::List(
            vec![
                Sexp::Symbol("a".to_string(), SYN),
                Sexp::List(
                    vec![
                        Sexp::Symbol("quasiquote".to_string(), SYN),
                        Sexp::List(
                            vec![
                                Sexp::Symbol("b".to_string(), SYN),
                                Sexp::List(
                                    vec![
                                        Sexp::Symbol("unquote".to_string(), SYN),
                                        Sexp::Symbol("c".to_string(), SYN),
                                    ],
                                    SYN,
                                ),
                            ],
                            SYN,
                        ),
                    ],
                    SYN,
                ),
            ],
            SYN,
        );
        let result = expand_qq_template(&template, 0).unwrap();
        let s = format!("{}", result);
        // The inner quasiquote should be preserved as a literal
        assert!(s.contains(r#"(SexpSym "quasiquote")"#));
        // The inner unquote should also be preserved as a literal (not evaluated)
        assert!(s.contains(r#"(SexpSym "unquote")"#));
    }

    #[test]
    fn test_qq_splicing_at_top_level_errors() {
        let template = Sexp::List(
            vec![
                Sexp::Symbol("unquote-splicing".to_string(), SYN),
                Sexp::Symbol("xs".to_string(), SYN),
            ],
            SYN,
        );
        let result = expand_qq_template(&template, 0);
        assert!(result.is_err());
    }

    #[test]
    fn test_expand_quasiquotes_finds_nested_qq() {
        // (do (quasiquote foo)) should expand the inner quasiquote
        let sexp = parse_sexp("(do `foo)").unwrap();
        let result = expand_quasiquotes(&sexp).unwrap();
        let s = format!("{}", result);
        assert!(s.contains("SexpSym"));
        assert!(s.contains("foo"));
    }

    #[test]
    fn test_expand_quasiquotes_passthrough_no_qq() {
        let sexp = parse_sexp("(+ 1 2)").unwrap();
        let result = expand_quasiquotes(&sexp).unwrap();
        assert_eq!(format!("{}", result), format!("{}", sexp));
    }

    #[test]
    fn test_qq_empty_list() {
        let template = Sexp::List(vec![], SYN);
        let result = expand_qq_template(&template, 0).unwrap();
        let s = format!("{}", result);
        assert!(s.contains("SexpList"));
        assert!(s.contains("SNil"));
    }

    // ── is_begin / flatten_begin tests ──────────────────────────

    #[test]
    fn test_is_begin_true() {
        let sexp = parse_sexp("(begin 1 2 3)").unwrap();
        assert!(is_begin(&sexp));
    }

    #[test]
    fn test_is_begin_false_other_head() {
        let sexp = parse_sexp("(defn foo [] 42)").unwrap();
        assert!(!is_begin(&sexp));
    }

    #[test]
    fn test_is_begin_false_atom() {
        let sexp = parse_sexp("42").unwrap();
        assert!(!is_begin(&sexp));
    }

    #[test]
    fn test_is_begin_false_empty_list() {
        let sexp = Sexp::List(vec![], (0, 0));
        assert!(!is_begin(&sexp));
    }

    #[test]
    fn test_flatten_begin_single() {
        let sexp = parse_sexp("(begin (defn foo [] 1))").unwrap();
        let result = flatten_begin(sexp);
        assert_eq!(result.len(), 1);
    }

    #[test]
    fn test_flatten_begin_multiple() {
        let sexp = parse_sexp("(begin (defn foo [] 1) (defn bar [] 2))").unwrap();
        let result = flatten_begin(sexp);
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_flatten_begin_nested() {
        let sexp = parse_sexp("(begin (begin 1 2) 3)").unwrap();
        let result = flatten_begin(sexp);
        assert_eq!(result.len(), 3);
    }

    #[test]
    fn test_flatten_begin_non_begin() {
        let sexp = parse_sexp("(defn foo [] 42)").unwrap();
        let result = flatten_begin(sexp);
        assert_eq!(result.len(), 1);
    }
}
