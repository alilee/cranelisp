use crate::ast::*;
use crate::error::{CranelispError, Span};
use crate::sexp::Sexp;

/// Check if a head symbol is a definition form and return its base form and visibility.
/// E.g., "defn-" → Some(("defn", Private)), "defn" → Some(("defn", Public)),
/// "deftype-" → Some(("deftype", Private)), "foo" → None.
fn parse_def_visibility(head: &str) -> Option<(&str, Visibility)> {
    match head {
        "defn" => Some(("defn", Visibility::Public)),
        "defn-" => Some(("defn", Visibility::Private)),
        "deftype" => Some(("deftype", Visibility::Public)),
        "deftype-" => Some(("deftype", Visibility::Private)),
        "deftrait" => Some(("deftrait", Visibility::Public)),
        "deftrait-" => Some(("deftrait", Visibility::Private)),
        _ => None,
    }
}

// ── Error helper ────────────────────────────────────────────────────────

fn err(message: &str, span: Span) -> CranelispError {
    CranelispError::ParseError {
        message: message.to_string(),
        offset: span.0,
    }
}

// ── Sexp inspection helpers ─────────────────────────────────────────────

fn expect_symbol(sexp: &Sexp) -> Result<(&str, Span), CranelispError> {
    match sexp {
        Sexp::Symbol(s, span) => Ok((s.as_str(), *span)),
        _ => Err(err("expected symbol", sexp.span())),
    }
}

fn expect_list(sexp: &Sexp) -> Result<(&[Sexp], Span), CranelispError> {
    match sexp {
        Sexp::List(children, span) => Ok((children.as_slice(), *span)),
        _ => Err(err("expected list", sexp.span())),
    }
}

fn expect_bracket(sexp: &Sexp) -> Result<(&[Sexp], Span), CranelispError> {
    match sexp {
        Sexp::Bracket(children, span) => Ok((children.as_slice(), *span)),
        _ => Err(err("expected bracket", sexp.span())),
    }
}

/// Extract an optional docstring from `children[start]`. Returns (docstring, next_pos).
fn extract_optional_docstring(children: &[Sexp], start: usize) -> (Option<String>, usize) {
    if start < children.len() {
        if let Sexp::Str(s, _) = &children[start] {
            return (Some(s.clone()), start + 1);
        }
    }
    (None, start)
}

fn is_uppercase_start(s: &str) -> bool {
    s.starts_with(|c: char| c.is_uppercase())
}

// ── Public API ──────────────────────────────────────────────────────────

pub fn build_program(sexps: &[Sexp]) -> Result<Program, CranelispError> {
    sexps.iter().map(build_top_level).collect()
}

pub fn build_repl_input(sexp: &Sexp) -> Result<ReplInput, CranelispError> {
    // Try top-level forms first, fall back to expression
    match sexp {
        Sexp::List(children, span) if !children.is_empty() => {
            if let Sexp::Symbol(head, _) = &children[0] {
                match head.as_str() {
                    "defmacro" | "defmacro-" => {
                        return Err(err("defmacro should be handled before AST building (macro expansion phase)", *span));
                    }
                    "begin" => {
                        return Err(err("begin should be handled before AST building (macro expansion phase)", *span));
                    }
                    "mod" => {
                        return Err(err("(mod ...) should be handled before AST building (module loading phase)", *span));
                    }
                    "import" => {
                        return Err(err("(import ...) should be handled before AST building (module loading phase)", *span));
                    }
                    "export" => {
                        return Err(err("(export ...) should be handled before AST building (module loading phase)", *span));
                    }
                    "platform" => {
                        return Err(err("(platform ...) declaration should be handled before AST building", *span));
                    }
                    "impl" => {
                        let tl = build_impl(children, *span)?;
                        return match tl {
                            TopLevel::TraitImpl(ti) => Ok(ReplInput::TraitImpl(ti)),
                            _ => unreachable!(),
                        };
                    }
                    _ => {
                        // Check for definition forms (defn, defn-, deftype, deftype-, deftrait, deftrait-)
                        if let Some((base, vis)) = parse_def_visibility(head) {
                            return match base {
                                "defn" => build_defn_as_repl(children, *span, vis),
                                "deftype" => {
                                    let tl = build_deftype(children, *span, vis)?;
                                    match tl {
                                        TopLevel::TypeDef {
                                            name,
                                            docstring,
                                            type_params,
                                            constructors,
                                            visibility,
                                            span,
                                        } => Ok(ReplInput::TypeDef {
                                            name,
                                            docstring,
                                            type_params,
                                            constructors,
                                            visibility,
                                            span,
                                        }),
                                        _ => unreachable!(),
                                    }
                                }
                                "deftrait" => {
                                    let tl = build_deftrait(children, *span, vis)?;
                                    match tl {
                                        TopLevel::TraitDecl(td) => Ok(ReplInput::TraitDecl(td)),
                                        _ => unreachable!(),
                                    }
                                }
                                _ => unreachable!(),
                            };
                        }
                    }
                }
            }
        }
        // Bare operator as REPL input
        Sexp::Symbol(s, span) if is_operator(s) => {
            return Ok(ReplInput::Expr(Expr::Var {
                name: s.clone(),
                span: *span,
            }));
        }
        _ => {}
    }
    // Fall through to expression
    let expr = build_expr(sexp)?;
    Ok(ReplInput::Expr(expr))
}

pub fn build_expr(sexp: &Sexp) -> Result<Expr, CranelispError> {
    build_expr_inner(sexp)
}

// ── Convenience wrappers (compose sexp reader + AST builder) ───────────

pub fn parse_program(input: &str) -> Result<Program, CranelispError> {
    let sexps = crate::sexp::parse_sexps(input)?;
    // Filter out defmacro forms — they are handled in the macro expansion phase
    let non_macro: Vec<_> = sexps
        .into_iter()
        .filter(|s| !crate::macro_expand::is_defmacro(s))
        .collect();
    build_program(&non_macro)
}

/// Build a ReplInput from pre-parsed Sexp forms (split from parse_repl_input for
/// two-phase pipeline visibility: callers can capture the Sexp intermediate).
pub fn build_repl_input_from_sexps(sexps: &[Sexp]) -> Result<ReplInput, CranelispError> {
    if sexps.is_empty() {
        return Err(CranelispError::ParseError {
            message: "expected expression".to_string(),
            offset: 0,
        });
    }
    // Handle top-level annotation: `:Type expr` or `:(T a) expr`
    if sexps.len() > 1 {
        let args = build_args_with_annotations(sexps)?;
        if args.len() == 1 {
            return Ok(ReplInput::Expr(args.into_iter().next().unwrap()));
        }
        return Err(CranelispError::ParseError {
            message: "expected EOF".to_string(),
            offset: sexps[1].span().0,
        });
    }
    build_repl_input(&sexps[0])
}

pub fn parse_repl_input(input: &str) -> Result<ReplInput, CranelispError> {
    let sexps = crate::sexp::parse_sexps(input)?;
    build_repl_input_from_sexps(&sexps)
}

pub fn parse_expr(input: &str) -> Result<Expr, CranelispError> {
    let sexps = crate::sexp::parse_sexps(input)?;
    if sexps.is_empty() {
        return Err(CranelispError::ParseError {
            message: "expected expression".to_string(),
            offset: 0,
        });
    }
    // Handle top-level annotation: `:Type expr` or `:(T a) expr`
    if sexps.len() > 1 {
        let args = build_args_with_annotations(&sexps)?;
        if args.len() == 1 {
            return Ok(args.into_iter().next().unwrap());
        }
        return Err(CranelispError::ParseError {
            message: "expected EOF".to_string(),
            offset: sexps[1].span().0,
        });
    }
    build_expr(&sexps[0])
}

// ── Expression builders ─────────────────────────────────────────────────

fn build_expr_inner(sexp: &Sexp) -> Result<Expr, CranelispError> {
    match sexp {
        Sexp::Int(v, span) => Ok(Expr::IntLit {
            value: *v,
            span: *span,
        }),
        Sexp::Float(v, span) => Ok(Expr::FloatLit {
            value: *v,
            span: *span,
        }),
        Sexp::Bool(v, span) => Ok(Expr::BoolLit {
            value: *v,
            span: *span,
        }),
        Sexp::Str(v, span) => Ok(Expr::StringLit {
            value: v.clone(),
            span: *span,
        }),
        Sexp::Symbol(name, span) => {
            // Colon-prefixed symbols in expression position are annotations
            // `:Int 42` is two sexp items — handled by build_expr_sequence
            // A bare `:Int` with no following expr is just a Var
            Ok(Expr::Var {
                name: name.clone(),
                span: *span,
            })
        }
        Sexp::List(children, span) => build_list_expr(children, *span),
        Sexp::Bracket(children, span) => {
            // Bracket in expression position → VecLit
            let elements = children
                .iter()
                .map(build_expr_inner)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Expr::VecLit {
                elements,
                span: *span,
            })
        }
    }
}

fn build_list_expr(children: &[Sexp], span: Span) -> Result<Expr, CranelispError> {
    if children.is_empty() {
        // Empty list () → Apply with no callee; PEG parser would fail on this
        // but we'll produce an error
        return Err(err("empty application", span));
    }

    // Check if first child is a keyword symbol
    if let Sexp::Symbol(head, _) = &children[0] {
        match head.as_str() {
            "let" => return build_let(children, span),
            "if" => return build_if(children, span),
            "fn" => return build_fn(children, span),
            "match" => return build_match(children, span),
            "vec" => return build_vec_sugar(children, span),
            _ => {}
        }
    }

    // Check for annotation: `: type_expr expr` as the first items
    // The PEG parser handles `: type_expr expr` at the expr level, not inside a list.
    // In the sexp reader, `:` as a bare symbol followed by a type form would appear as children.
    // But `:Int 42` as a top-level expression would be two separate sexps, not inside a list.
    // Inside a list like `(: Int 42)`, this would just be an Apply.
    // The annotation form `:Type expr` is handled at the slice level in build_one_expr_from_slice.

    // Generic Apply
    build_apply(children, span)
}

fn build_apply(children: &[Sexp], span: Span) -> Result<Expr, CranelispError> {
    let callee = build_expr_inner(&children[0])?;
    let args = build_args_with_annotations(&children[1..])?;
    Ok(Expr::Apply {
        callee: Box::new(callee),
        args,
        span,
    })
}

/// Build one expression from a slice at `pos`, consuming annotation if present.
/// Returns `(expr, items_consumed)`.
fn build_one_expr_at(items: &[Sexp], pos: usize) -> Result<(Expr, usize), CranelispError> {
    if let Some((annotation, consumed)) = try_consume_annotation(items, pos) {
        let expr_pos = pos + consumed;
        if expr_pos >= items.len() {
            return Err(err("annotation missing expression", items[pos].span()));
        }
        let inner = build_expr_inner(&items[expr_pos])?;
        let span = (items[pos].span().0, items[expr_pos].span().1);
        Ok((
            Expr::Annotate {
                annotation,
                expr: Box::new(inner),
                span,
            },
            consumed + 1,
        ))
    } else {
        let expr = build_expr_inner(&items[pos])?;
        Ok((expr, 1))
    }
}

/// Build argument list, handling inline annotations (`:Type expr` → `Annotate`).
fn build_args_with_annotations(items: &[Sexp]) -> Result<Vec<Expr>, CranelispError> {
    let mut args = Vec::new();
    let mut i = 0;
    while i < items.len() {
        let (expr, consumed) = build_one_expr_at(items, i)?;
        args.push(expr);
        i += consumed;
    }
    Ok(args)
}

fn build_let(children: &[Sexp], span: Span) -> Result<Expr, CranelispError> {
    // (let [name val name val ...] body)
    if children.len() != 3 {
        return Err(err("let requires bindings and body", span));
    }
    let (bracket_items, _) = expect_bracket(&children[1])?;
    let bindings = build_let_bindings(bracket_items)?;
    let body = build_expr_inner(&children[2])?;
    Ok(Expr::Let {
        bindings,
        body: Box::new(body),
        span,
    })
}

fn build_let_bindings(items: &[Sexp]) -> Result<Vec<(String, Expr)>, CranelispError> {
    let mut bindings = Vec::new();
    let mut i = 0;
    while i < items.len() {
        let (name, _) = expect_symbol(&items[i])?;
        i += 1;
        if i >= items.len() {
            return Err(err("let binding missing value", items[i - 1].span()));
        }
        let (value, consumed) = build_one_expr_at(items, i)?;
        i += consumed;
        bindings.push((name.to_string(), value));
    }
    Ok(bindings)
}

fn build_if(children: &[Sexp], span: Span) -> Result<Expr, CranelispError> {
    // (if cond then else)
    if children.len() != 4 {
        return Err(err("if requires condition, then, and else branches", span));
    }
    let cond = build_expr_inner(&children[1])?;
    let then_branch = build_expr_inner(&children[2])?;
    let else_branch = build_expr_inner(&children[3])?;
    Ok(Expr::If {
        cond: Box::new(cond),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
        span,
    })
}

fn build_fn(children: &[Sexp], span: Span) -> Result<Expr, CranelispError> {
    // (fn [params] body)
    if children.len() != 3 {
        return Err(err("fn requires param list and body", span));
    }
    let (params, param_annotations) = build_annotated_params(&children[1])?;
    let body = build_expr_inner(&children[2])?;
    Ok(Expr::Lambda {
        params,
        param_annotations,
        body: Box::new(body),
        span,
    })
}

fn build_match(children: &[Sexp], span: Span) -> Result<Expr, CranelispError> {
    // (match scrutinee [pattern body pattern body ...])
    if children.len() != 3 {
        return Err(err("match requires scrutinee and arms", span));
    }
    let scrutinee = build_expr_inner(&children[1])?;
    let (bracket_items, _) = expect_bracket(&children[2])?;
    let arms = build_match_arms(bracket_items)?;
    Ok(Expr::Match {
        scrutinee: Box::new(scrutinee),
        arms,
        span,
    })
}

fn build_match_arms(items: &[Sexp]) -> Result<Vec<MatchArm>, CranelispError> {
    let mut arms = Vec::new();
    let mut i = 0;
    while i < items.len() {
        let pat_span_start = items[i].span().0;
        let pattern = build_pattern(&items[i])?;
        i += 1;
        if i >= items.len() {
            return Err(err("match arm missing body", items[i - 1].span()));
        }
        let body = build_expr_inner(&items[i])?;
        let arm_span = (pat_span_start, items[i].span().1);
        i += 1;
        arms.push(MatchArm {
            pattern,
            body,
            span: arm_span,
        });
    }
    Ok(arms)
}

fn build_pattern(sexp: &Sexp) -> Result<Pattern, CranelispError> {
    match sexp {
        Sexp::Symbol(name, span) => {
            if name == "_" {
                Ok(Pattern::Wildcard { span: *span })
            } else if is_uppercase_start(name) {
                // Nullary constructor
                Ok(Pattern::Constructor {
                    name: name.clone(),
                    bindings: vec![],
                    span: *span,
                })
            } else {
                Ok(Pattern::Var {
                    name: name.clone(),
                    span: *span,
                })
            }
        }
        Sexp::List(children, span) => {
            // (Constructor var1 var2 ...)
            if children.is_empty() {
                return Err(err("empty pattern", *span));
            }
            let (name, _) = expect_symbol(&children[0])?;
            let bindings = children[1..]
                .iter()
                .map(|s| {
                    let (n, _) = expect_symbol(s)?;
                    Ok(n.to_string())
                })
                .collect::<Result<Vec<_>, CranelispError>>()?;
            Ok(Pattern::Constructor {
                name: name.to_string(),
                bindings,
                span: *span,
            })
        }
        _ => Err(err("invalid pattern", sexp.span())),
    }
}

fn build_vec_sugar(children: &[Sexp], span: Span) -> Result<Expr, CranelispError> {
    // (vec e1 e2 ...) → VecLit
    let elements = children[1..]
        .iter()
        .map(build_expr_inner)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Expr::VecLit { elements, span })
}

// ── Annotation-aware expression building ────────────────────────────────

/// Try to consume a type annotation starting at `items[pos]`.
/// Returns `Some((TypeExpr, items_consumed))` or `None`.
fn try_consume_annotation(items: &[Sexp], pos: usize) -> Option<(TypeExpr, usize)> {
    if pos >= items.len() {
        return None;
    }
    match &items[pos] {
        // `:Int`, `:a`, `:Num` — simple colon-prefixed symbol
        Sexp::Symbol(s, _) if s.starts_with(':') && s.len() > 1 => {
            let name = &s[1..];
            let te = parse_annotation_name(name);
            Some((te, 1))
        }
        // `:` followed by `(Fn [...] ret)` or `(Option a)` etc — compound annotation
        Sexp::Symbol(s, _) if s == ":" => {
            if pos + 1 < items.len() {
                if let Ok(te) = build_type_expr(&items[pos + 1]) {
                    return Some((te, 2));
                }
            }
            None
        }
        _ => None,
    }
}

fn parse_annotation_name(name: &str) -> TypeExpr {
    if name == "self" {
        TypeExpr::SelfType
    } else if is_uppercase_start(name) {
        TypeExpr::Named(name.to_string())
    } else {
        TypeExpr::TypeVar(name.to_string())
    }
}

// ── Parameter list builders ─────────────────────────────────────────────

/// Build annotated parameter list from a Bracket sexp.
/// Returns (names, annotations). If no param has annotation, annotations is empty vec.
fn build_annotated_params(
    sexp: &Sexp,
) -> Result<(Vec<String>, Vec<Option<TypeExpr>>), CranelispError> {
    let (items, _) = expect_bracket(sexp)?;
    let mut names = Vec::new();
    let mut annotations = Vec::new();
    let mut i = 0;

    while i < items.len() {
        if let Some((te, consumed)) = try_consume_annotation(items, i) {
            // Next item after annotation is the param name
            let name_pos = i + consumed;
            if name_pos >= items.len() {
                return Err(err("annotation missing parameter name", items[i].span()));
            }
            let (name, _) = expect_symbol(&items[name_pos])?;
            names.push(name.to_string());
            annotations.push(Some(te));
            i = name_pos + 1;
        } else {
            let (name, _) = expect_symbol(&items[i])?;
            names.push(name.to_string());
            annotations.push(None);
            i += 1;
        }
    }

    let has_any = annotations.iter().any(|a| a.is_some());
    Ok((names, if has_any { annotations } else { vec![] }))
}

// ── Type expression builders ────────────────────────────────────────────

fn build_type_expr(sexp: &Sexp) -> Result<TypeExpr, CranelispError> {
    match sexp {
        Sexp::Symbol(name, _) => {
            if name == "self" {
                Ok(TypeExpr::SelfType)
            } else if is_uppercase_start(name) {
                Ok(TypeExpr::Named(name.clone()))
            } else {
                Ok(TypeExpr::TypeVar(name.clone()))
            }
        }
        Sexp::List(children, span) => build_type_expr_from_list(children, *span),
        _ => Err(err("invalid type expression", sexp.span())),
    }
}

fn build_type_expr_from_list(children: &[Sexp], span: Span) -> Result<TypeExpr, CranelispError> {
    if children.is_empty() {
        return Err(err("empty type expression", span));
    }
    if let Sexp::Symbol(head, _) = &children[0] {
        match head.as_str() {
            "Fn" => {
                // (Fn [param_types] ret_type)
                if children.len() != 3 {
                    return Err(err("Fn requires param types and return type", span));
                }
                let (param_items, _) = expect_bracket(&children[1])?;
                let params = param_items
                    .iter()
                    .map(build_type_expr)
                    .collect::<Result<Vec<_>, _>>()?;
                let ret = build_type_expr(&children[2])?;
                return Ok(TypeExpr::FnType(params, Box::new(ret)));
            }
            _ => {
                // (Name arg1 arg2 ...) → Applied
                let name = head.clone();
                let args = children[1..]
                    .iter()
                    .map(build_type_expr)
                    .collect::<Result<Vec<_>, _>>()?;
                return Ok(TypeExpr::Applied(name, args));
            }
        }
    }
    Err(err("invalid type expression", span))
}

// ── Top-level builders ──────────────────────────────────────────────────

fn build_top_level(sexp: &Sexp) -> Result<TopLevel, CranelispError> {
    let (children, span) = expect_list(sexp)?;
    if children.is_empty() {
        return Err(err("empty top-level form", span));
    }
    let (head, _) = expect_symbol(&children[0])?;

    // Check for defmacro/defmacro- (safety net)
    if head == "defmacro" || head == "defmacro-" {
        return Err(err(
            "defmacro should be handled before AST building (macro expansion phase)",
            span,
        ));
    }

    // Check for begin (safety net — should be flattened before AST building)
    if head == "begin" {
        return Err(err(
            "begin should be handled before AST building (macro expansion phase)",
            span,
        ));
    }

    // Check for module-phase forms
    match head {
        "mod" => {
            return Err(err(
                "(mod ...) should be handled before AST building (module loading phase)",
                span,
            ))
        }
        "import" => {
            return Err(err(
                "(import ...) should be handled before AST building (module loading phase)",
                span,
            ))
        }
        "export" => {
            return Err(err(
                "(export ...) should be handled before AST building (module loading phase)",
                span,
            ))
        }
        "platform" => {
            return Err(err(
                "(platform ...) declaration should be handled before AST building",
                span,
            ))
        }
        _ => {}
    }

    // Check for definition forms with visibility
    if let Some((base, vis)) = parse_def_visibility(head) {
        return match base {
            "defn" => build_defn(children, span, vis),
            "deftype" => build_deftype(children, span, vis),
            "deftrait" => build_deftrait(children, span, vis),
            _ => unreachable!(),
        };
    }

    // impl has no private variant
    if head == "impl" {
        return build_impl(children, span);
    }

    Err(err(&format!("unknown top-level form: {}", head), span))
}

fn build_defn(
    children: &[Sexp],
    span: Span,
    visibility: Visibility,
) -> Result<TopLevel, CranelispError> {
    // (defn name "doc"? [params] body)      — single
    // (defn name "doc"? ([p] b) ([p] b))    — multi
    if children.len() < 3 {
        return Err(err("defn requires name and body", span));
    }

    let name = get_defn_name(&children[1])?;
    let (docstring, next) = extract_optional_docstring(children, 2);

    if next >= children.len() {
        return Err(err("defn missing params or variants", span));
    }

    // Detect single vs multi: Bracket → single, List → multi
    match &children[next] {
        Sexp::Bracket(..) => {
            // Single defn
            let (params, param_annotations) = build_annotated_params(&children[next])?;
            let body_start = next + 1;
            let (body, consumed) = build_one_expr_at(children, body_start)?;
            if body_start + consumed != children.len() {
                return Err(err("defn requires params and body", span));
            }
            Ok(TopLevel::Defn(Defn {
                name,
                docstring,
                params,
                param_annotations,
                body,
                visibility,
                span,
            }))
        }
        Sexp::List(..) => {
            // Multi defn
            let variants = children[next..]
                .iter()
                .map(build_defn_variant)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(TopLevel::DefnMulti {
                name,
                docstring,
                variants,
                visibility,
                span,
            })
        }
        _ => Err(err(
            "defn: expected params [...] or variant (...)",
            children[next].span(),
        )),
    }
}

fn build_defn_as_repl(
    children: &[Sexp],
    span: Span,
    visibility: Visibility,
) -> Result<ReplInput, CranelispError> {
    if children.len() < 3 {
        return Err(err("defn requires name and body", span));
    }

    let name = get_defn_name(&children[1])?;
    let (docstring, next) = extract_optional_docstring(children, 2);

    if next >= children.len() {
        return Err(err("defn missing params or variants", span));
    }

    match &children[next] {
        Sexp::Bracket(..) => {
            let (params, param_annotations) = build_annotated_params(&children[next])?;
            let body_start = next + 1;
            let (body, consumed) = build_one_expr_at(children, body_start)?;
            if body_start + consumed != children.len() {
                return Err(err("defn requires params and body", span));
            }
            Ok(ReplInput::Defn(Defn {
                name,
                docstring,
                params,
                param_annotations,
                body,
                visibility,
                span,
            }))
        }
        Sexp::List(..) => {
            let variants = children[next..]
                .iter()
                .map(build_defn_variant)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(ReplInput::DefnMulti {
                name,
                docstring,
                variants,
                visibility,
                span,
            })
        }
        _ => Err(err(
            "defn: expected params or variant",
            children[next].span(),
        )),
    }
}

fn get_defn_name(sexp: &Sexp) -> Result<String, CranelispError> {
    match sexp {
        Sexp::Symbol(name, _) => Ok(name.clone()),
        _ => Err(err("expected function name", sexp.span())),
    }
}

fn build_defn_variant(sexp: &Sexp) -> Result<DefnVariant, CranelispError> {
    let (children, span) = expect_list(sexp)?;
    if children.len() != 2 {
        return Err(err("defn variant requires params and body", span));
    }
    let (params, param_annotations) = build_annotated_params(&children[0])?;
    let body = build_expr_inner(&children[1])?;
    Ok(DefnVariant {
        params,
        param_annotations,
        body,
        span,
    })
}

fn build_deftype(
    children: &[Sexp],
    span: Span,
    visibility: Visibility,
) -> Result<TopLevel, CranelispError> {
    // (deftype Head "doc"? [fields])              — product
    // (deftype Head "doc"? Ctor1 (Ctor2 [f]) ...) — sum/enum
    if children.len() < 2 {
        return Err(err("deftype requires a type head", span));
    }

    let (type_name, type_params) = build_type_head(&children[1])?;
    let (docstring, next) = extract_optional_docstring(children, 2);

    if next >= children.len() {
        return Err(err("deftype missing constructors", span));
    }

    // Detect product vs sum: Bracket → product shorthand, otherwise constructors
    let (raw_params, raw_ctors) = match &children[next] {
        Sexp::Bracket(..) => {
            // Product type: (deftype Name [fields])
            let fields = build_field_list(&children[next])?;
            let ctor = ConstructorDef {
                name: type_name.clone(),
                docstring: None,
                fields,
                span,
            };
            (type_params, vec![ctor])
        }
        _ => {
            // Sum/enum: constructors
            let ctors = children[next..]
                .iter()
                .map(build_constructor_def)
                .collect::<Result<Vec<_>, _>>()?;
            (type_params, ctors)
        }
    };

    let (resolved_params, resolved_ctors) = desugar_type_def(&type_name, &raw_params, &raw_ctors);

    Ok(TopLevel::TypeDef {
        name: type_name,
        docstring,
        type_params: resolved_params,
        constructors: resolved_ctors,
        visibility,
        span,
    })
}

fn build_type_head(sexp: &Sexp) -> Result<(String, Vec<String>), CranelispError> {
    match sexp {
        Sexp::Symbol(name, _) if is_uppercase_start(name) => Ok((name.clone(), vec![])),
        Sexp::List(children, span) => {
            if children.is_empty() {
                return Err(err("empty type head", *span));
            }
            let (name, _) = expect_symbol(&children[0])?;
            let params = children[1..]
                .iter()
                .map(|s| {
                    let (n, _) = expect_symbol(s)?;
                    Ok(n.to_string())
                })
                .collect::<Result<Vec<_>, CranelispError>>()?;
            Ok((name.to_string(), params))
        }
        _ => Err(err("expected type name or (Name params...)", sexp.span())),
    }
}

fn build_constructor_def(sexp: &Sexp) -> Result<ConstructorDef, CranelispError> {
    match sexp {
        // Nullary: bare UpperName
        Sexp::Symbol(name, span) if is_uppercase_start(name) => Ok(ConstructorDef {
            name: name.clone(),
            docstring: None,
            fields: vec![],
            span: *span,
        }),
        // Data or nullary-with-doc: (UpperName "doc"? [fields]?)
        Sexp::List(children, span) => {
            if children.is_empty() {
                return Err(err("empty constructor", *span));
            }
            let (name, _) = expect_symbol(&children[0])?;
            let (docstring, next) = extract_optional_docstring(children, 1);

            let fields = if next < children.len() {
                if let Sexp::Bracket(..) = &children[next] {
                    build_field_list(&children[next])?
                } else {
                    vec![]
                }
            } else {
                vec![]
            };

            Ok(ConstructorDef {
                name: name.to_string(),
                docstring,
                fields,
                span: *span,
            })
        }
        _ => Err(err("expected constructor definition", sexp.span())),
    }
}

fn build_field_list(sexp: &Sexp) -> Result<Vec<FieldDef>, CranelispError> {
    let (items, _) = expect_bracket(sexp)?;
    let mut fields = Vec::new();
    let mut i = 0;

    while i < items.len() {
        if let Some((te, consumed)) = try_consume_annotation(items, i) {
            let name_pos = i + consumed;
            if name_pos >= items.len() {
                return Err(err(
                    "field type annotation missing field name",
                    items[i].span(),
                ));
            }
            let (name, _) = expect_symbol(&items[name_pos])?;
            fields.push(FieldDef {
                name: name.to_string(),
                type_expr: te,
            });
            i = name_pos + 1;
        } else {
            // Bare name — shortcut syntax
            let (name, _) = expect_symbol(&items[i])?;
            fields.push(FieldDef {
                name: name.to_string(),
                type_expr: TypeExpr::TypeVar(String::new()),
            });
            i += 1;
        }
    }

    Ok(fields)
}

fn build_deftrait(
    children: &[Sexp],
    span: Span,
    visibility: Visibility,
) -> Result<TopLevel, CranelispError> {
    // (deftrait Head "doc"? methods...)
    if children.len() < 2 {
        return Err(err("deftrait requires name", span));
    }

    let (name, type_params) = build_trait_head(&children[1])?;
    let (docstring, next) = extract_optional_docstring(children, 2);

    let methods = children[next..]
        .iter()
        .map(build_trait_method_sig)
        .collect::<Result<Vec<_>, _>>()?;

    Ok(TopLevel::TraitDecl(TraitDecl {
        name,
        docstring,
        type_params,
        methods,
        visibility,
        span,
    }))
}

fn build_trait_head(sexp: &Sexp) -> Result<(String, Vec<String>), CranelispError> {
    match sexp {
        Sexp::Symbol(name, _) => Ok((name.clone(), vec![])),
        Sexp::List(children, span) => {
            if children.is_empty() {
                return Err(err("empty trait head", *span));
            }
            let (name, _) = expect_symbol(&children[0])?;
            let params = children[1..]
                .iter()
                .map(|s| {
                    let (n, _) = expect_symbol(s)?;
                    Ok(n.to_string())
                })
                .collect::<Result<Vec<_>, CranelispError>>()?;
            Ok((name.to_string(), params))
        }
        _ => Err(err("expected trait name or (Name params...)", sexp.span())),
    }
}

fn build_trait_method_sig(sexp: &Sexp) -> Result<TraitMethodSig, CranelispError> {
    // (method_name "doc"? [param_types] ret_type)
    let (children, span) = expect_list(sexp)?;
    if children.is_empty() {
        return Err(err("empty trait method signature", span));
    }

    let name = get_defn_name(&children[0])?;
    let (docstring, next) = extract_optional_docstring(children, 1);

    if next + 1 >= children.len() {
        return Err(err(
            "trait method requires param types and return type",
            span,
        ));
    }

    let (param_items, _) = expect_bracket(&children[next])?;
    let params = param_items
        .iter()
        .map(build_type_expr)
        .collect::<Result<Vec<_>, _>>()?;
    let ret_type = build_type_expr(&children[next + 1])?;

    Ok(TraitMethodSig {
        name,
        docstring,
        params,
        ret_type,
        span,
        hkt_param_index: None,
    })
}

fn build_impl(children: &[Sexp], span: Span) -> Result<TopLevel, CranelispError> {
    // (impl TraitName Target methods...)
    if children.len() < 3 {
        return Err(err("impl requires trait name and target", span));
    }

    let (trait_name, _) = expect_symbol(&children[1])?;
    let (target_type, type_args, type_constraints) = build_impl_target(&children[2])?;

    let methods = children[3..]
        .iter()
        .map(|sexp| {
            let (ch, sp) = expect_list(sexp)?;
            if ch.is_empty() {
                return Err(err("empty method definition", sp));
            }
            let (head, _) = expect_symbol(&ch[0])?;
            if head != "defn" {
                return Err(err("impl methods must be defn forms", sp));
            }
            build_defn_inner(ch, sp)
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok(TopLevel::TraitImpl(TraitImpl {
        trait_name: trait_name.to_string(),
        target_type,
        type_args,
        type_constraints,
        methods,
        span,
    }))
}

fn build_defn_inner(children: &[Sexp], span: Span) -> Result<Defn, CranelispError> {
    // (defn name "doc"? [params] body) — always single defn (impl methods, always public)
    if children.len() < 3 {
        return Err(err("defn requires name, params, and body", span));
    }
    let name = get_defn_name(&children[1])?;
    let (docstring, next) = extract_optional_docstring(children, 2);
    let (params, param_annotations) = build_annotated_params(&children[next])?;
    let body_start = next + 1;
    let (body, consumed) = build_one_expr_at(children, body_start)?;
    if body_start + consumed != children.len() {
        return Err(err("defn requires params and body", span));
    }
    Ok(Defn {
        name,
        docstring,
        params,
        param_annotations,
        body,
        visibility: Visibility::Public,
        span,
    })
}

fn build_impl_target(
    sexp: &Sexp,
) -> Result<(String, Vec<String>, Vec<(String, String)>), CranelispError> {
    match sexp {
        Sexp::Symbol(name, _) => Ok((name.clone(), vec![], vec![])),
        Sexp::List(children, span) => {
            if children.is_empty() {
                return Err(err("empty impl target", *span));
            }
            let (name, _) = expect_symbol(&children[0])?;
            if !is_uppercase_start(name) {
                return Err(err(
                    "impl target must start with uppercase",
                    children[0].span(),
                ));
            }
            let mut type_args = Vec::new();
            let mut constraints = Vec::new();

            let mut i = 1;
            while i < children.len() {
                // Check for `:Constraint var` pattern
                if let Sexp::Symbol(s, _) = &children[i] {
                    if s.starts_with(':') && s.len() > 1 {
                        let constraint = s[1..].to_string();
                        i += 1;
                        if i >= children.len() {
                            return Err(err(
                                "constraint missing type variable",
                                children[i - 1].span(),
                            ));
                        }
                        let (var, _) = expect_symbol(&children[i])?;
                        type_args.push(var.to_string());
                        constraints.push((var.to_string(), constraint));
                        i += 1;
                        continue;
                    }
                }
                let (arg, _) = expect_symbol(&children[i])?;
                type_args.push(arg.to_string());
                i += 1;
            }

            Ok((name.to_string(), type_args, constraints))
        }
        _ => Err(err("expected impl target", sexp.span())),
    }
}

fn is_operator(s: &str) -> bool {
    matches!(s, "+" | "-" | "*" | "/" | "=" | "<" | ">" | "<=" | ">=")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sexp::{parse_sexp, parse_sexps};

    // ── Atom tests ──────────────────────────────────────────────────────

    #[test]
    fn build_int() {
        let sexp = parse_sexp("42").unwrap();
        let expr = build_expr(&sexp).unwrap();
        match expr {
            Expr::IntLit { value, .. } => assert_eq!(value, 42),
            _ => panic!("expected IntLit"),
        }
    }

    #[test]
    fn build_negative_int() {
        let sexp = parse_sexp("-7").unwrap();
        let expr = build_expr(&sexp).unwrap();
        match expr {
            Expr::IntLit { value, .. } => assert_eq!(value, -7),
            _ => panic!("expected IntLit"),
        }
    }

    #[test]
    fn build_float() {
        let sexp = parse_sexp("3.14").unwrap();
        let expr = build_expr(&sexp).unwrap();
        match expr {
            Expr::FloatLit { value, .. } => assert!((value - 3.14).abs() < 1e-10),
            _ => panic!("expected FloatLit"),
        }
    }

    #[test]
    fn build_bool_true() {
        let sexp = parse_sexp("true").unwrap();
        let expr = build_expr(&sexp).unwrap();
        match expr {
            Expr::BoolLit { value, .. } => assert!(value),
            _ => panic!("expected BoolLit"),
        }
    }

    #[test]
    fn build_string() {
        let sexp = parse_sexp(r#""hello""#).unwrap();
        let expr = build_expr(&sexp).unwrap();
        match expr {
            Expr::StringLit { value, .. } => assert_eq!(value, "hello"),
            _ => panic!("expected StringLit"),
        }
    }

    #[test]
    fn build_var() {
        let sexp = parse_sexp("foo").unwrap();
        let expr = build_expr(&sexp).unwrap();
        match expr {
            Expr::Var { name, .. } => assert_eq!(name, "foo"),
            _ => panic!("expected Var"),
        }
    }

    // ── Apply tests ─────────────────────────────────────────────────────

    #[test]
    fn build_simple_apply() {
        let sexp = parse_sexp("(+ 1 2)").unwrap();
        let expr = build_expr(&sexp).unwrap();
        match expr {
            Expr::Apply { callee, args, .. } => {
                match *callee {
                    Expr::Var { name, .. } => assert_eq!(name, "+"),
                    _ => panic!("expected Var(+)"),
                }
                assert_eq!(args.len(), 2);
            }
            _ => panic!("expected Apply"),
        }
    }

    #[test]
    fn build_nested_apply() {
        let sexp = parse_sexp("(* n (fact (- n 1)))").unwrap();
        let expr = build_expr(&sexp).unwrap();
        assert!(matches!(expr, Expr::Apply { .. }));
    }

    // ── Special form tests ──────────────────────────────────────────────

    #[test]
    fn build_if_expr() {
        let sexp = parse_sexp("(if true 1 0)").unwrap();
        let expr = build_expr(&sexp).unwrap();
        match expr {
            Expr::If { cond, .. } => {
                assert!(matches!(*cond, Expr::BoolLit { value: true, .. }));
            }
            _ => panic!("expected If"),
        }
    }

    #[test]
    fn build_let_expr() {
        let sexp = parse_sexp("(let [x 1 y 2] (+ x y))").unwrap();
        let expr = build_expr(&sexp).unwrap();
        match expr {
            Expr::Let { bindings, .. } => {
                assert_eq!(bindings.len(), 2);
                assert_eq!(bindings[0].0, "x");
                assert_eq!(bindings[1].0, "y");
            }
            _ => panic!("expected Let"),
        }
    }

    #[test]
    fn build_fn_expr() {
        let sexp = parse_sexp("(fn [x] (+ x 1))").unwrap();
        let expr = build_expr(&sexp).unwrap();
        match expr {
            Expr::Lambda { params, .. } => assert_eq!(params, vec!["x"]),
            _ => panic!("expected Lambda"),
        }
    }

    #[test]
    fn build_fn_zero_params() {
        let sexp = parse_sexp("(fn [] 42)").unwrap();
        let expr = build_expr(&sexp).unwrap();
        match expr {
            Expr::Lambda { params, .. } => assert!(params.is_empty()),
            _ => panic!("expected Lambda"),
        }
    }

    #[test]
    fn build_do_as_apply() {
        // do is now a macro, not a special form — parses as Apply
        let sexp = parse_sexp("(do (print 1) (print 2))").unwrap();
        let expr = build_expr(&sexp).unwrap();
        assert!(matches!(expr, Expr::Apply { .. }));
    }

    #[test]
    fn build_pure_as_apply() {
        // pure is now a function, not a special form — parses as Apply
        let sexp = parse_sexp("(pure 42)").unwrap();
        let expr = build_expr(&sexp).unwrap();
        assert!(matches!(expr, Expr::Apply { .. }));
    }

    #[test]
    fn build_bind_as_apply() {
        // bind is now a function, not a special form — parses as Apply
        let sexp = parse_sexp("(bind (print 1) (fn [x] (pure x)))").unwrap();
        let expr = build_expr(&sexp).unwrap();
        assert!(matches!(expr, Expr::Apply { .. }));
    }

    #[test]
    fn build_match_expr() {
        let sexp = parse_sexp("(match x [None 0 (Some v) v])").unwrap();
        let expr = build_expr(&sexp).unwrap();
        match expr {
            Expr::Match { arms, .. } => {
                assert_eq!(arms.len(), 2);
                match &arms[0].pattern {
                    Pattern::Constructor { name, bindings, .. } => {
                        assert_eq!(name, "None");
                        assert!(bindings.is_empty());
                    }
                    _ => panic!("expected Constructor"),
                }
                match &arms[1].pattern {
                    Pattern::Constructor { name, bindings, .. } => {
                        assert_eq!(name, "Some");
                        assert_eq!(bindings, &["v"]);
                    }
                    _ => panic!("expected Constructor"),
                }
            }
            _ => panic!("expected Match"),
        }
    }

    #[test]
    fn build_match_wildcard() {
        let sexp = parse_sexp("(match x [_ 0])").unwrap();
        let expr = build_expr(&sexp).unwrap();
        match expr {
            Expr::Match { arms, .. } => {
                assert!(matches!(&arms[0].pattern, Pattern::Wildcard { .. }));
            }
            _ => panic!("expected Match"),
        }
    }

    #[test]
    fn build_match_var_pattern() {
        let sexp = parse_sexp("(match x [y (+ y 1)])").unwrap();
        let expr = build_expr(&sexp).unwrap();
        match expr {
            Expr::Match { arms, .. } => match &arms[0].pattern {
                Pattern::Var { name, .. } => assert_eq!(name, "y"),
                _ => panic!("expected Var pattern"),
            },
            _ => panic!("expected Match"),
        }
    }

    #[test]
    fn build_list_is_apply() {
        // After sugar removal, (list 1 2 3) is a regular Apply (macro expands it later)
        let sexp = parse_sexp("(list 1 2 3)").unwrap();
        let expr = build_expr(&sexp).unwrap();
        match &expr {
            Expr::Apply { callee, args, .. } => {
                match callee.as_ref() {
                    Expr::Var { name, .. } => assert_eq!(name, "list"),
                    _ => panic!("expected Var(list)"),
                }
                assert_eq!(args.len(), 3);
            }
            _ => panic!("expected Apply"),
        }
    }

    #[test]
    fn build_list_empty_is_apply() {
        // (list) with no args is a zero-arg Apply
        let sexp = parse_sexp("(list)").unwrap();
        let expr = build_expr(&sexp).unwrap();
        match &expr {
            Expr::Apply { callee, args, .. } => {
                match callee.as_ref() {
                    Expr::Var { name, .. } => assert_eq!(name, "list"),
                    _ => panic!("expected Var(list)"),
                }
                assert_eq!(args.len(), 0);
            }
            _ => panic!("expected Apply"),
        }
    }

    #[test]
    fn build_vec_sugar_expr() {
        let sexp = parse_sexp("(vec 1 2 3)").unwrap();
        let expr = build_expr(&sexp).unwrap();
        match expr {
            Expr::VecLit { elements, .. } => assert_eq!(elements.len(), 3),
            _ => panic!("expected VecLit"),
        }
    }

    #[test]
    fn build_vec_bracket() {
        let sexp = parse_sexp("[1 2 3]").unwrap();
        let expr = build_expr(&sexp).unwrap();
        match expr {
            Expr::VecLit { elements, .. } => assert_eq!(elements.len(), 3),
            _ => panic!("expected VecLit"),
        }
    }

    #[test]
    fn build_vec_empty() {
        let sexp = parse_sexp("[]").unwrap();
        let expr = build_expr(&sexp).unwrap();
        match expr {
            Expr::VecLit { elements, .. } => assert!(elements.is_empty()),
            _ => panic!("expected VecLit"),
        }
    }

    #[test]
    fn build_bind_bang_is_apply() {
        // After sugar removal, (bind! ...) is a regular Apply (macro expands it later)
        let sexp = parse_sexp("(bind! [x (read-line)] (print x))").unwrap();
        let expr = build_expr(&sexp).unwrap();
        match &expr {
            Expr::Apply { callee, args, .. } => {
                match callee.as_ref() {
                    Expr::Var { name, .. } => assert_eq!(name, "bind!"),
                    _ => panic!("expected Var(bind!)"),
                }
                assert_eq!(args.len(), 2);
            }
            _ => panic!("expected Apply"),
        }
    }

    #[test]
    fn build_apply_lambda() {
        let sexp = parse_sexp("((fn [x] x) 5)").unwrap();
        let expr = build_expr(&sexp).unwrap();
        match expr {
            Expr::Apply { callee, args, .. } => {
                assert!(matches!(*callee, Expr::Lambda { .. }));
                assert_eq!(args.len(), 1);
            }
            _ => panic!("expected Apply"),
        }
    }

    // ── Top-level tests ─────────────────────────────────────────────────

    #[test]
    fn build_defn_program() {
        let sexps = parse_sexps(
            "(defn fact [n] (if (= n 0) 1 (* n (fact (- n 1))))) (defn main [] (print (fact 10)))",
        )
        .unwrap();
        let prog = build_program(&sexps).unwrap();
        let ds = crate::ast::defns(&prog);
        assert_eq!(ds.len(), 2);
        assert_eq!(ds[0].name, "fact");
        assert_eq!(ds[0].params, vec!["n"]);
        assert_eq!(ds[1].name, "main");
    }

    #[test]
    fn build_trait_decl() {
        let sexps = parse_sexps("(deftrait Display (show [self] String))").unwrap();
        let prog = build_program(&sexps).unwrap();
        match &prog[0] {
            TopLevel::TraitDecl(td) => {
                assert_eq!(td.name, "Display");
                assert!(td.type_params.is_empty());
                assert_eq!(td.methods.len(), 1);
                assert_eq!(td.methods[0].name, "show");
            }
            _ => panic!("expected TraitDecl"),
        }
    }

    #[test]
    fn build_trait_with_type_params() {
        let sexps = parse_sexps("(deftrait (From a) (from [a] self))").unwrap();
        let prog = build_program(&sexps).unwrap();
        match &prog[0] {
            TopLevel::TraitDecl(td) => {
                assert_eq!(td.name, "From");
                assert_eq!(td.type_params, vec!["a"]);
            }
            _ => panic!("expected TraitDecl"),
        }
    }

    #[test]
    fn build_trait_impl() {
        let sexps = parse_sexps("(impl Display Int (defn show [x] x))").unwrap();
        let prog = build_program(&sexps).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(ti) => {
                assert_eq!(ti.trait_name, "Display");
                assert_eq!(ti.target_type, "Int");
                assert_eq!(ti.methods.len(), 1);
            }
            _ => panic!("expected TraitImpl"),
        }
    }

    #[test]
    fn build_deftype_product() {
        let sexps = parse_sexps("(deftype Point [:Int x :Int y])").unwrap();
        let prog = build_program(&sexps).unwrap();
        match &prog[0] {
            TopLevel::TypeDef {
                name,
                type_params,
                constructors,
                ..
            } => {
                assert_eq!(name, "Point");
                assert!(type_params.is_empty());
                assert_eq!(constructors.len(), 1);
                assert_eq!(constructors[0].name, "Point");
                assert_eq!(constructors[0].fields.len(), 2);
            }
            _ => panic!("expected TypeDef"),
        }
    }

    #[test]
    fn build_deftype_sum() {
        let sexps = parse_sexps("(deftype (Option a) None (Some [:a val]))").unwrap();
        let prog = build_program(&sexps).unwrap();
        match &prog[0] {
            TopLevel::TypeDef {
                name,
                type_params,
                constructors,
                ..
            } => {
                assert_eq!(name, "Option");
                assert_eq!(type_params, &["a"]);
                assert_eq!(constructors.len(), 2);
                assert_eq!(constructors[0].name, "None");
                assert_eq!(constructors[1].name, "Some");
            }
            _ => panic!("expected TypeDef"),
        }
    }

    #[test]
    fn build_deftype_enum() {
        let sexps = parse_sexps("(deftype Color Red Green Blue)").unwrap();
        let prog = build_program(&sexps).unwrap();
        match &prog[0] {
            TopLevel::TypeDef {
                name, constructors, ..
            } => {
                assert_eq!(name, "Color");
                assert_eq!(constructors.len(), 3);
            }
            _ => panic!("expected TypeDef"),
        }
    }

    #[test]
    fn build_deftype_shortcut() {
        let sexps = parse_sexps("(deftype Pair [first second])").unwrap();
        let prog = build_program(&sexps).unwrap();
        match &prog[0] {
            TopLevel::TypeDef {
                name,
                type_params,
                constructors,
                ..
            } => {
                assert_eq!(name, "Pair");
                assert_eq!(type_params, &["a", "b"]);
                assert!(
                    matches!(&constructors[0].fields[0].type_expr, TypeExpr::TypeVar(v) if v == "a")
                );
                assert!(
                    matches!(&constructors[0].fields[1].type_expr, TypeExpr::TypeVar(v) if v == "b")
                );
            }
            _ => panic!("expected TypeDef"),
        }
    }

    // ── Annotation tests ────────────────────────────────────────────────

    #[test]
    fn build_annotated_params_test() {
        let sexps = parse_sexps("(defn f [:Int x] x) (defn main [] (pure 0))").unwrap();
        let prog = build_program(&sexps).unwrap();
        match &prog[0] {
            TopLevel::Defn(d) => {
                assert_eq!(d.params, vec!["x"]);
                assert_eq!(d.param_annotations.len(), 1);
                assert!(matches!(&d.param_annotations[0], Some(TypeExpr::Named(n)) if n == "Int"));
            }
            _ => panic!("expected Defn"),
        }
    }

    #[test]
    fn build_unannotated_has_empty_annotations() {
        let sexps = parse_sexps("(defn f [x] x) (defn main [] (pure 0))").unwrap();
        let prog = build_program(&sexps).unwrap();
        match &prog[0] {
            TopLevel::Defn(d) => {
                assert!(d.param_annotations.is_empty());
            }
            _ => panic!("expected Defn"),
        }
    }

    // ── Docstring tests ─────────────────────────────────────────────────

    #[test]
    fn build_defn_with_docstring() {
        let sexp = parse_sexp(r#"(defn foo "adds one" [:Int x] (+ x 1))"#).unwrap();
        let input = build_repl_input(&sexp).unwrap();
        match input {
            ReplInput::Defn(d) => {
                assert_eq!(d.docstring, Some("adds one".to_string()));
            }
            _ => panic!("expected Defn"),
        }
    }

    #[test]
    fn build_defn_without_docstring() {
        let sexp = parse_sexp("(defn foo [x] x)").unwrap();
        let input = build_repl_input(&sexp).unwrap();
        match input {
            ReplInput::Defn(d) => {
                assert_eq!(d.docstring, None);
            }
            _ => panic!("expected Defn"),
        }
    }

    #[test]
    fn build_defn_multi_with_docstring() {
        let sexp = parse_sexp(r#"(defn bar "multi" ([x] x) ([x y] (+ x y)))"#).unwrap();
        let input = build_repl_input(&sexp).unwrap();
        match input {
            ReplInput::DefnMulti {
                docstring,
                variants,
                ..
            } => {
                assert_eq!(docstring, Some("multi".to_string()));
                assert_eq!(variants.len(), 2);
            }
            _ => panic!("expected DefnMulti"),
        }
    }

    #[test]
    fn build_trait_decl_with_docstring() {
        let sexp =
            parse_sexp(r#"(deftrait Display "converts to string" (show [self] String))"#).unwrap();
        let input = build_repl_input(&sexp).unwrap();
        match input {
            ReplInput::TraitDecl(td) => {
                assert_eq!(td.docstring, Some("converts to string".to_string()));
            }
            _ => panic!("expected TraitDecl"),
        }
    }

    #[test]
    fn build_trait_method_with_docstring() {
        let sexp =
            parse_sexp(r#"(deftrait Display (show "displays value" [self] String))"#).unwrap();
        let input = build_repl_input(&sexp).unwrap();
        match input {
            ReplInput::TraitDecl(td) => {
                assert_eq!(td.methods[0].docstring, Some("displays value".to_string()));
            }
            _ => panic!("expected TraitDecl"),
        }
    }

    #[test]
    fn build_deftype_with_docstring() {
        let sexp = parse_sexp(r#"(deftype Point "a 2D point" [:Int x :Int y])"#).unwrap();
        let input = build_repl_input(&sexp).unwrap();
        match input {
            ReplInput::TypeDef { docstring, .. } => {
                assert_eq!(docstring, Some("a 2D point".to_string()));
            }
            _ => panic!("expected TypeDef"),
        }
    }

    #[test]
    fn build_deftype_sum_with_docstrings() {
        let sexp = parse_sexp(
            r#"(deftype (Option a) "optional value" (None "represents absence") (Some "wraps a value" [:a val]))"#,
        ).unwrap();
        let input = build_repl_input(&sexp).unwrap();
        match input {
            ReplInput::TypeDef {
                docstring,
                constructors,
                ..
            } => {
                assert_eq!(docstring, Some("optional value".to_string()));
                assert_eq!(
                    constructors[0].docstring,
                    Some("represents absence".to_string())
                );
                assert_eq!(constructors[1].docstring, Some("wraps a value".to_string()));
            }
            _ => panic!("expected TypeDef"),
        }
    }

    // ── REPL input tests ────────────────────────────────────────────────

    #[test]
    fn repl_input_bare_expr() {
        let sexp = parse_sexp("42").unwrap();
        let input = build_repl_input(&sexp).unwrap();
        assert!(matches!(
            input,
            ReplInput::Expr(Expr::IntLit { value: 42, .. })
        ));
    }

    #[test]
    fn repl_input_operator() {
        let sexp = parse_sexp("+ ").unwrap();
        let input = build_repl_input(&sexp).unwrap();
        match input {
            ReplInput::Expr(Expr::Var { name, .. }) => assert_eq!(name, "+"),
            _ => panic!("expected Expr(Var(+))"),
        }
    }

    #[test]
    fn repl_input_deftype() {
        let sexp = parse_sexp("(deftype Color Red Green Blue)").unwrap();
        let input = build_repl_input(&sexp).unwrap();
        match input {
            ReplInput::TypeDef { name, .. } => assert_eq!(name, "Color"),
            _ => panic!("expected TypeDef"),
        }
    }

    // ── Operator defn name tests ────────────────────────────────────────

    #[test]
    fn build_defn_operator_name() {
        let sexps = parse_sexps("(defn + [x y] (add-i64 x y))").unwrap();
        let prog = build_program(&sexps).unwrap();
        match &prog[0] {
            TopLevel::Defn(d) => {
                assert_eq!(d.name, "+");
                assert_eq!(d.params, vec!["x", "y"]);
            }
            _ => panic!("expected Defn"),
        }
    }

    // ── Polymorphic impl target ─────────────────────────────────────────

    #[test]
    fn build_impl_polymorphic_target() {
        let sexps = parse_sexps(
            "(impl Display (Option :Display a) (defn show [self] (match self [None \"None\" (Some x) (show x)])))"
        ).unwrap();
        let prog = build_program(&sexps).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(ti) => {
                assert_eq!(ti.trait_name, "Display");
                assert_eq!(ti.target_type, "Option");
                assert_eq!(ti.type_args, vec!["a"]);
                assert_eq!(
                    ti.type_constraints,
                    vec![("a".to_string(), "Display".to_string())]
                );
            }
            _ => panic!("expected TraitImpl"),
        }
    }

    // ── HKT trait ───────────────────────────────────────────────────────

    #[test]
    fn build_hkt_trait() {
        let sexps = parse_sexps("(deftrait (Functor f) (fmap [(Fn [a] b) (f a)] (f b)))").unwrap();
        let prog = build_program(&sexps).unwrap();
        match &prog[0] {
            TopLevel::TraitDecl(td) => {
                assert_eq!(td.name, "Functor");
                assert_eq!(td.type_params, vec!["f"]);
                assert_eq!(td.methods.len(), 1);
                assert_eq!(td.methods[0].name, "fmap");
                assert_eq!(td.methods[0].params.len(), 2);
                // First param: (Fn [a] b)
                assert!(matches!(&td.methods[0].params[0], TypeExpr::FnType(..)));
                // Second param: (f a) → Applied
                assert!(matches!(&td.methods[0].params[1], TypeExpr::Applied(..)));
            }
            _ => panic!("expected TraitDecl"),
        }
    }

    // ── Compound type annotations ───────────────────────────────────────

    #[test]
    fn build_compound_field_annotation() {
        let sexps = parse_sexps("(deftype (List a) Nil (Cons [:a head :(List a) tail]))").unwrap();
        let prog = build_program(&sexps).unwrap();
        match &prog[0] {
            TopLevel::TypeDef { constructors, .. } => {
                let cons = &constructors[1];
                assert_eq!(cons.fields.len(), 2);
                assert_eq!(cons.fields[0].name, "head");
                assert_eq!(cons.fields[1].name, "tail");
                match &cons.fields[1].type_expr {
                    TypeExpr::Applied(name, args) => {
                        assert_eq!(name, "List");
                        assert_eq!(args.len(), 1);
                    }
                    _ => panic!("expected Applied type for tail"),
                }
            }
            _ => panic!("expected TypeDef"),
        }
    }

    // ── Mixed program ───────────────────────────────────────────────────

    #[test]
    fn build_mixed_program() {
        let sexps = parse_sexps(
            "(deftrait Display (show [self] String)) (impl Display Int (defn show [x] x)) (defn main [] (pure 0))"
        ).unwrap();
        let prog = build_program(&sexps).unwrap();
        assert_eq!(prog.len(), 3);
        assert!(matches!(&prog[0], TopLevel::TraitDecl(..)));
        assert!(matches!(&prog[1], TopLevel::TraitImpl(..)));
        assert!(matches!(&prog[2], TopLevel::Defn(..)));
    }
}
