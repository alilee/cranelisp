//! AST builder: converts S-expressions (`Vec<Sexp>`) into typed AST nodes
//! (`Vec<TopLevel>` for batch, `ReplInput` for REPL).
//!
//! Ring 0 forms: `defn`, `deftype`, `let`, `if`, `fn`/`lambda`, `match`,
//! type annotations (`:Type expr`).
//!
//! Non-Ring-0 forms are rejected with clear error messages indicating which
//! ring they belong to.

use cranelisp_types::{
    CranelispError, ConstructorDef, Defn, DefnVariant, Expr, FieldDef, MacroExpander, MatchArm,
    Pattern, Program, ReplInput, Sexp, Span, Symbol, TopLevel, TraitDecl, TraitImpl,
    TraitMethodSig, TraitName, TypeExpr, TypeName, Visibility,
};

// ---------------------------------------------------------------------------
// TopLevel -> ReplInput conversion
// ---------------------------------------------------------------------------

/// Convert a TopLevel form to a ReplInput, avoiding field-by-field destructuring.
fn toplevel_to_repl_input(tl: TopLevel) -> ReplInput {
    match tl {
        TopLevel::Defn(defn) => ReplInput::Defn(defn),
        TopLevel::DefnMulti {
            name,
            docstring,
            variants,
            visibility,
            span,
        } => ReplInput::DefnMulti {
            name,
            docstring,
            variants,
            visibility,
            span,
        },
        TopLevel::TraitDecl(decl) => ReplInput::TraitDecl(decl),
        TopLevel::TraitImpl(imp) => ReplInput::TraitImpl(imp),
        TopLevel::TypeDef {
            name,
            docstring,
            type_params,
            constructors,
            visibility,
            span,
        } => ReplInput::TypeDef {
            name,
            docstring,
            type_params,
            constructors,
            visibility,
            span,
        },
    }
}

// ---------------------------------------------------------------------------
// Error helpers
// ---------------------------------------------------------------------------

fn parse_err(message: &str, span: Span) -> CranelispError {
    CranelispError::ParseError {
        message: message.to_string(),
        span,
    }
}

// ---------------------------------------------------------------------------
// Sexp inspection helpers
// ---------------------------------------------------------------------------

fn expect_symbol(sexp: &Sexp) -> Result<(&str, Span), CranelispError> {
    match sexp {
        Sexp::Symbol(s, span) => Ok((s.as_str(), *span)),
        _ => Err(parse_err("expected symbol", sexp.span())),
    }
}

fn expect_list(sexp: &Sexp) -> Result<(&[Sexp], Span), CranelispError> {
    match sexp {
        Sexp::List(children, span) => Ok((children.as_slice(), *span)),
        _ => Err(parse_err("expected list", sexp.span())),
    }
}

fn expect_bracket(sexp: &Sexp) -> Result<(&[Sexp], Span), CranelispError> {
    match sexp {
        Sexp::Bracket(children, span) => Ok((children.as_slice(), *span)),
        _ => Err(parse_err("expected bracket", sexp.span())),
    }
}

/// Extract an optional docstring from `children[start]`. Returns `(docstring, next_pos)`.
fn extract_optional_docstring(children: &[Sexp], start: usize) -> (Option<String>, usize) {
    if start < children.len()
        && let Sexp::Str(s, _) = &children[start]
    {
        return (Some(s.clone()), start + 1);
    }
    (None, start)
}

fn is_uppercase_start(s: &str) -> bool {
    s.starts_with(|c: char| c.is_uppercase())
}

/// Check if a head symbol is a definition form and return its base form and visibility.
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

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Build a batch program from parsed S-expressions.
///
/// Each sexp must be a top-level form (`defn`, `deftype`, `deftrait`, `impl`).
pub fn build_program(
    sexps: &[Sexp],
    expander: &mut dyn MacroExpander,
) -> Result<Program, CranelispError> {
    sexps.iter().map(|s| build_top_level(s, expander)).collect()
}

/// Build REPL input from a single S-expression.
///
/// Accepts top-level forms and bare expressions.
pub fn build_repl_input(
    sexp: &Sexp,
    expander: &mut dyn MacroExpander,
) -> Result<ReplInput, CranelispError> {
    // Try top-level forms first, fall back to expression
    match sexp {
        Sexp::List(children, span) if !children.is_empty() => {
            if let Sexp::Symbol(head, head_span) = &children[0] {
                // Reject forms handled by other pipeline stages
                reject_pre_ast_forms(head, *span)?;

                // Check for non-Ring-0 forms
                reject_non_ring0_toplevel(head, *head_span)?;

                // impl has no private variant
                if head == "impl" {
                    let tl = build_trait_impl(children, *span, expander)?;
                    return Ok(toplevel_to_repl_input(tl));
                }

                // Check if head is a macro (I3: match what build_top_level does)
                if expander.is_macro(head) {
                    let expanded =
                        expander.expand(&head.as_str().into(), &children[1..], *span)?;
                    return build_repl_input(&expanded, expander);
                }

                // Check for definition forms with visibility
                if let Some((base, vis)) = parse_def_visibility(head) {
                    return match base {
                        "defn" => build_defn_as_repl(children, *span, vis, expander),
                        "deftype" => {
                            let tl = build_deftype(children, *span, vis)?;
                            Ok(toplevel_to_repl_input(tl))
                        }
                        "deftrait" => {
                            let tl = build_deftrait(children, *span, vis)?;
                            Ok(toplevel_to_repl_input(tl))
                        }
                        _ => unreachable!("invariant: parse_def_visibility returns known base"),
                    };
                }
            }
        }
        _ => {}
    }
    // Fall through to expression
    let expr = build_expr(sexp, expander)?;
    Ok(ReplInput::Expr(expr))
}

// ---------------------------------------------------------------------------
// Rejection helpers
// ---------------------------------------------------------------------------

/// Reject forms that should be handled by earlier pipeline stages.
fn reject_pre_ast_forms(head: &str, span: Span) -> Result<(), CranelispError> {
    match head {
        "defmacro" | "defmacro-" => Err(parse_err(
            "defmacro should be handled before AST building (macro expansion phase)",
            span,
        )),
        "begin" => Err(parse_err(
            "begin should be handled before AST building (macro expansion phase)",
            span,
        )),
        "mod" | "mod-" => Err(parse_err(
            "(mod ...) should be handled before AST building (module loading phase)",
            span,
        )),
        "import" => Err(parse_err(
            "(import ...) should be handled before AST building (module loading phase)",
            span,
        )),
        "export" => Err(parse_err(
            "(export ...) should be handled before AST building (module loading phase)",
            span,
        )),
        "platform" => Err(parse_err(
            "(platform ...) declaration should be handled before AST building",
            span,
        )),
        _ => Ok(()),
    }
}

/// Reject non-Ring-0 top-level forms with clear error messages.
fn reject_non_ring0_toplevel(_head: &str, _span: Span) -> Result<(), CranelispError> {
    // All formerly-rejected top-level forms (deftrait, impl) are now handled.
    Ok(())
}

/// Reject non-Ring-0 symbol forms in expression position.
fn reject_non_ring0_symbol(name: &str, span: Span) -> Result<(), CranelispError> {
    if name.starts_with('%') {
        return Err(parse_err(
            "percent parameters not yet supported (Ring 3)",
            span,
        ));
    }
    if name.starts_with('$') {
        return Err(parse_err("gensym not yet supported (Ring 3)", span));
    }
    if name.starts_with('&') {
        return Err(parse_err(
            "rest parameters not yet supported (Ring 3)",
            span,
        ));
    }
    if name.ends_with('#') {
        return Err(parse_err(
            "gensym shorthand not yet supported (Ring 3)",
            span,
        ));
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Top-level builders
// ---------------------------------------------------------------------------

fn build_top_level(
    sexp: &Sexp,
    expander: &mut dyn MacroExpander,
) -> Result<TopLevel, CranelispError> {
    let (children, span) = expect_list(sexp)?;
    if children.is_empty() {
        return Err(parse_err("empty top-level form", span));
    }
    let (head, head_span) = expect_symbol(&children[0])?;

    // Reject forms handled by earlier pipeline stages
    reject_pre_ast_forms(head, span)?;

    // Reject non-Ring-0 top-level forms
    reject_non_ring0_toplevel(head, head_span)?;

    // Check if head is a macro
    if expander.is_macro(head) {
        let expanded = expander.expand(
            &head.into(),
            &children[1..],
            span,
        )?;
        return build_top_level(&expanded, expander);
    }

    // Check for definition forms with visibility
    if let Some((base, vis)) = parse_def_visibility(head) {
        return match base {
            "defn" => build_defn(children, span, vis, expander),
            "deftype" => build_deftype(children, span, vis),
            "deftrait" => build_deftrait(children, span, vis),
            _ => unreachable!("invariant: parse_def_visibility returns known base"),
        };
    }

    // impl has no private variant
    if head == "impl" {
        return build_trait_impl(children, span, expander);
    }

    Err(parse_err(
        &format!("unknown top-level form: {head}"),
        span,
    ))
}

// ---------------------------------------------------------------------------
// defn builder
// ---------------------------------------------------------------------------

/// Parsed defn result before wrapping into TopLevel or ReplInput.
enum DefnInner {
    Single(Defn),
    Multi {
        name: Symbol,
        docstring: Option<String>,
        variants: Vec<DefnVariant>,
        visibility: Visibility,
        span: Span,
    },
}

impl From<DefnInner> for TopLevel {
    fn from(inner: DefnInner) -> Self {
        match inner {
            DefnInner::Single(defn) => TopLevel::Defn(defn),
            DefnInner::Multi {
                name,
                docstring,
                variants,
                visibility,
                span,
            } => TopLevel::DefnMulti {
                name,
                docstring,
                variants,
                visibility,
                span,
            },
        }
    }
}

impl From<DefnInner> for ReplInput {
    fn from(inner: DefnInner) -> Self {
        match inner {
            DefnInner::Single(defn) => ReplInput::Defn(defn),
            DefnInner::Multi {
                name,
                docstring,
                variants,
                visibility,
                span,
            } => ReplInput::DefnMulti {
                name,
                docstring,
                variants,
                visibility,
                span,
            },
        }
    }
}

fn build_defn(
    children: &[Sexp],
    span: Span,
    visibility: Visibility,
    expander: &mut dyn MacroExpander,
) -> Result<TopLevel, CranelispError> {
    build_defn_inner(children, span, visibility, expander).map(Into::into)
}

fn build_defn_as_repl(
    children: &[Sexp],
    span: Span,
    visibility: Visibility,
    expander: &mut dyn MacroExpander,
) -> Result<ReplInput, CranelispError> {
    build_defn_inner(children, span, visibility, expander).map(Into::into)
}

/// Shared defn parsing logic for both batch and REPL paths.
fn build_defn_inner(
    children: &[Sexp],
    span: Span,
    visibility: Visibility,
    expander: &mut dyn MacroExpander,
) -> Result<DefnInner, CranelispError> {
    // (defn name "doc"? [params] body)      -- single
    // (defn name "doc"? ([p] b) ([p] b))    -- multi
    if children.len() < 3 {
        return Err(parse_err("defn requires name and body", span));
    }

    let name = get_defn_name(&children[1])?;
    let (docstring, next) = extract_optional_docstring(children, 2);

    if next >= children.len() {
        return Err(parse_err("defn missing params or variants", span));
    }

    // Detect single vs multi: Bracket -> single, List -> multi
    match &children[next] {
        Sexp::Bracket(..) => {
            let (params, param_annotations) = build_annotated_params(&children[next])?;
            let body_start = next + 1;
            if body_start >= children.len() {
                return Err(parse_err("defn missing body", span));
            }
            let (body, consumed) = build_one_expr_at(children, body_start, expander)?;
            if body_start + consumed != children.len() {
                return Err(parse_err("defn has extra forms after body", span));
            }
            Ok(DefnInner::Single(Defn {
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
                .map(|s| build_defn_variant(s, expander))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(DefnInner::Multi {
                name,
                docstring,
                variants,
                visibility,
                span,
            })
        }
        _ => Err(parse_err(
            "defn: expected params [...] or variant (...)",
            children[next].span(),
        )),
    }
}

fn get_defn_name(sexp: &Sexp) -> Result<Symbol, CranelispError> {
    match sexp {
        Sexp::Symbol(name, _) => Ok(name.as_str().into()),
        _ => Err(parse_err("expected function name", sexp.span())),
    }
}

fn build_defn_variant(
    sexp: &Sexp,
    expander: &mut dyn MacroExpander,
) -> Result<DefnVariant, CranelispError> {
    let (children, span) = expect_list(sexp)?;
    if children.len() != 2 {
        return Err(parse_err("defn variant requires params and body", span));
    }
    let (params, param_annotations) = build_annotated_params(&children[0])?;
    let body = build_expr(&children[1], expander)?;
    Ok(DefnVariant {
        params,
        param_annotations,
        body,
        span,
    })
}

// ---------------------------------------------------------------------------
// deftype builder
// ---------------------------------------------------------------------------

fn build_deftype(
    children: &[Sexp],
    span: Span,
    visibility: Visibility,
) -> Result<TopLevel, CranelispError> {
    // (deftype Head "doc"? [fields])              -- product
    // (deftype Head "doc"? Ctor1 (Ctor2 [f]) ...) -- sum/enum
    if children.len() < 2 {
        return Err(parse_err("deftype requires a type head", span));
    }

    let (type_name, type_params) = build_type_head(&children[1])?;
    let (docstring, next) = extract_optional_docstring(children, 2);

    if next >= children.len() {
        return Err(parse_err("deftype missing constructors", span));
    }

    // Detect product vs sum: Bracket -> product shorthand, otherwise constructors
    let (resolved_params, constructors) = match &children[next] {
        Sexp::Bracket(..) => {
            let fields = build_field_list(&children[next])?;
            let ctor = ConstructorDef {
                name: type_name.0.clone().into(),
                docstring: None,
                fields,
                span,
            };
            desugar_type_def(&type_name.0, &type_params, &[ctor])
        }
        _ => {
            let ctors = children[next..]
                .iter()
                .map(build_constructor_def)
                .collect::<Result<Vec<_>, _>>()?;
            desugar_type_def(&type_name.0, &type_params, &ctors)
        }
    };

    Ok(TopLevel::TypeDef {
        name: type_name,
        docstring,
        type_params: resolved_params,
        constructors,
        visibility,
        span,
    })
}

fn build_type_head(sexp: &Sexp) -> Result<(TypeName, Vec<Symbol>), CranelispError> {
    match sexp {
        Sexp::Symbol(name, _) if is_uppercase_start(name) => {
            Ok((TypeName::from(name.as_str()), vec![]))
        }
        Sexp::List(children, span) => {
            if children.is_empty() {
                return Err(parse_err("empty type head", *span));
            }
            let (name, _) = expect_symbol(&children[0])?;
            let params: Vec<Symbol> = children[1..]
                .iter()
                .map(|s| {
                    let (n, _) = expect_symbol(s)?;
                    Ok(n.into())
                })
                .collect::<Result<Vec<_>, CranelispError>>()?;
            Ok((TypeName::from(name), params))
        }
        _ => Err(parse_err(
            "expected type name or (Name params...)",
            sexp.span(),
        )),
    }
}

fn build_constructor_def(sexp: &Sexp) -> Result<ConstructorDef, CranelispError> {
    match sexp {
        // Nullary: bare UpperName
        Sexp::Symbol(name, span) if is_uppercase_start(name) => Ok(ConstructorDef {
            name: name.as_str().into(),
            docstring: None,
            fields: vec![],
            span: *span,
        }),
        // Data or nullary-with-doc: (UpperName "doc"? [fields]?)
        Sexp::List(children, span) => {
            if children.is_empty() {
                return Err(parse_err("empty constructor", *span));
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
                name: name.into(),
                docstring,
                fields,
                span: *span,
            })
        }
        _ => Err(parse_err("expected constructor definition", sexp.span())),
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
                return Err(parse_err(
                    "field type annotation missing field name",
                    items[i].span(),
                ));
            }
            let (name, _) = expect_symbol(&items[name_pos])?;
            fields.push(FieldDef {
                name: name.into(),
                type_expr: te,
            });
            i = name_pos + 1;
        } else {
            // Bare name -- shortcut syntax (fresh type var)
            let (name, _) = expect_symbol(&items[i])?;
            fields.push(FieldDef {
                name: name.into(),
                type_expr: TypeExpr::TypeVar("".into()),
            });
            i += 1;
        }
    }

    Ok(fields)
}

/// Desugar type definitions: resolve bare field names to fresh type variables
/// using sequential letters (a, b, c, ...), and collect type params if none
/// were declared.
fn desugar_type_def(
    _type_name: &str,
    declared_params: &[Symbol],
    constructors: &[ConstructorDef],
) -> (Vec<Symbol>, Vec<ConstructorDef>) {
    // Collect all bare type vars (empty string vars) from field defs.
    // Map each unique field position to a sequential letter variable.
    let mut inferred_params: Vec<Symbol> = Vec::new();
    // Map field name -> assigned type var name for consistency across constructors
    let mut field_to_var: Vec<(String, Symbol)> = Vec::new();

    let resolved_ctors: Vec<ConstructorDef> = constructors
        .iter()
        .map(|ctor| {
            let resolved_fields: Vec<FieldDef> = ctor
                .fields
                .iter()
                .map(|f| {
                    if let TypeExpr::TypeVar(ref v) = f.type_expr {
                        if v.is_empty() {
                            // Check if this field name already has an assigned var
                            let var_name = if let Some((_, var)) =
                                field_to_var.iter().find(|(fname, _)| fname == &f.name.0)
                            {
                                var.clone()
                            } else {
                                // Assign next sequential letter
                                let letter = sequential_type_var(inferred_params.len());
                                let var: Symbol = letter.into();
                                field_to_var.push((f.name.0.clone(), var.clone()));
                                inferred_params.push(var.clone());
                                var
                            };
                            FieldDef {
                                name: f.name.clone(),
                                type_expr: TypeExpr::TypeVar(var_name),
                            }
                        } else {
                            f.clone()
                        }
                    } else {
                        f.clone()
                    }
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

    let final_params: Vec<Symbol> = if declared_params.is_empty() {
        inferred_params
    } else {
        declared_params.to_vec()
    };

    (final_params, resolved_ctors)
}

/// Generate sequential type variable names: a, b, c, ..., z, aa, ab, ...
fn sequential_type_var(index: usize) -> String {
    let mut result = String::new();
    let mut n = index;
    loop {
        result.insert(0, (b'a' + (n % 26) as u8) as char);
        if n < 26 {
            break;
        }
        n = n / 26 - 1;
    }
    result
}

// ---------------------------------------------------------------------------
// deftrait builder
// ---------------------------------------------------------------------------

fn build_deftrait(
    children: &[Sexp],
    span: Span,
    visibility: Visibility,
) -> Result<TopLevel, CranelispError> {
    // (deftrait Head "doc"? method_sig+)
    // Head = TraitName | (TraitName type_var)
    if children.len() < 3 {
        return Err(parse_err("deftrait requires a trait head and at least one method", span));
    }

    let (trait_name, type_params, hkt_param_name) = build_trait_head(&children[1])?;
    let (docstring, next) = extract_optional_docstring(children, 2);

    if next >= children.len() {
        return Err(parse_err("deftrait requires at least one method signature", span));
    }

    let is_hkt = hkt_param_name.is_some();
    let methods = children[next..]
        .iter()
        .map(|s| build_method_sig(s, is_hkt, &hkt_param_name))
        .collect::<Result<Vec<_>, _>>()?;

    Ok(TopLevel::TraitDecl(TraitDecl {
        name: trait_name,
        docstring,
        type_params,
        methods,
        visibility,
        span,
    }))
}

/// Parse a trait head: either `TraitName` or `(TraitName var)`.
/// Returns (trait_name, type_params, optional_hkt_param_name).
fn build_trait_head(sexp: &Sexp) -> Result<(TraitName, Vec<Symbol>, Option<Symbol>), CranelispError> {
    match sexp {
        Sexp::Symbol(name, _) if is_uppercase_start(name) => {
            Ok((TraitName::from(name.as_str()), vec![], None))
        }
        Sexp::List(children, span) => {
            if children.len() != 2 {
                return Err(parse_err(
                    "HKT trait head must be (TraitName var)",
                    *span,
                ));
            }
            let (name, _) = expect_symbol(&children[0])?;
            if !is_uppercase_start(name) {
                return Err(parse_err("trait name must start with uppercase", children[0].span()));
            }
            let (var, _) = expect_symbol(&children[1])?;
            Ok((TraitName::from(name), vec![var.into()], Some(var.into())))
        }
        _ => Err(parse_err("expected trait name or (TraitName var)", sexp.span())),
    }
}

/// Parse a method signature within a deftrait.
///
/// Without default: `(method_name "doc"? [type_expr+] ret_type)`
/// With default:    `(method_name "doc"? [param_name+] ret_type body)`
fn build_method_sig(
    sexp: &Sexp,
    is_hkt: bool,
    hkt_param_name: &Option<Symbol>,
) -> Result<TraitMethodSig, CranelispError> {
    let (children, span) = expect_list(sexp)?;
    if children.len() < 3 {
        return Err(parse_err("method signature requires name, params, and return type", span));
    }

    let (name, _) = expect_symbol(&children[0])?;
    let (docstring, next) = extract_optional_docstring(children, 1);

    let (bracket_items, _) = expect_bracket(&children[next])?;
    let ret_pos = next + 1;
    if ret_pos >= children.len() {
        return Err(parse_err("method signature missing return type", span));
    }
    let ret_type = build_type_expr(&children[ret_pos])?;

    let has_default_body = ret_pos + 1 < children.len();

    if has_default_body && is_hkt {
        return Err(parse_err(
            "default method implementations are not supported on higher-kinded traits",
            span,
        ));
    }

    // Detect HKT param index: find which parameter position uses the
    // constructor variable (e.g., `(f a)` where f is the HKT var).
    let hkt_param_index = if let Some(hkt_var) = hkt_param_name {
        bracket_items.iter().position(|item| {
            if let Sexp::List(inner, _) = item
                && let Some(Sexp::Symbol(s, _)) = inner.first()
            {
                return s.as_str() == hkt_var.as_ref();
            }
            false
        })
    } else {
        None
    };

    if has_default_body {
        // Default body: bracket items are param names, not type exprs
        let param_names: Vec<Symbol> = bracket_items
            .iter()
            .map(|s| {
                let (n, _) = expect_symbol(s)?;
                Ok(n.into())
            })
            .collect::<Result<Vec<_>, CranelispError>>()?;

        // Build param types as SelfType (self-typed) for each param
        let params = param_names.iter().map(|_| TypeExpr::SelfType).collect();

        // The default body is the raw sexp after the return type
        let default_body = Some(children[ret_pos + 1].clone());

        Ok(TraitMethodSig {
            name: name.into(),
            docstring,
            params,
            ret_type,
            span,
            hkt_param_index,
            default_param_names: param_names,
            default_body,
        })
    } else {
        // No default: bracket items are type expressions
        let params = bracket_items
            .iter()
            .map(build_type_expr)
            .collect::<Result<Vec<_>, _>>()?;

        Ok(TraitMethodSig {
            name: name.into(),
            docstring,
            params,
            ret_type,
            span,
            hkt_param_index,
            default_param_names: vec![],
            default_body: None,
        })
    }
}

// ---------------------------------------------------------------------------
// impl builder
// ---------------------------------------------------------------------------

fn build_trait_impl(
    children: &[Sexp],
    span: Span,
    expander: &mut dyn MacroExpander,
) -> Result<TopLevel, CranelispError> {
    // (impl TraitName impl_target method_def+)
    // impl_target = Type | (Type :Constraint var ...)
    if children.len() < 4 {
        return Err(parse_err(
            "impl requires trait name, target type, and at least one method",
            span,
        ));
    }

    let (trait_name, _) = expect_symbol(&children[1])?;
    if !is_uppercase_start(trait_name) {
        return Err(parse_err("trait name must start with uppercase", children[1].span()));
    }

    let (target_type, type_args, type_constraints) = build_impl_target(&children[2])?;

    let methods = children[3..]
        .iter()
        .map(|s| build_impl_method(s, expander))
        .collect::<Result<Vec<_>, _>>()?;

    Ok(TopLevel::TraitImpl(TraitImpl {
        trait_name: trait_name.into(),
        target_type,
        type_args,
        type_constraints,
        methods,
        span,
    }))
}

/// Parsed impl target: (type_name, type_params, trait_constraints).
type ImplTarget = (TypeName, Vec<Symbol>, Vec<(Symbol, TraitName)>);

/// Parse an impl target. Three forms:
///   - `Type` — concrete: bare type name
///   - `(Type :Constraint var ...)` — polymorphic ADT with constraints
///   - `(Type var ...)` — parameterized concrete (e.g., `(Option Int)`)
fn build_impl_target(
    sexp: &Sexp,
) -> Result<ImplTarget, CranelispError> {
    match sexp {
        Sexp::Symbol(name, _) if is_uppercase_start(name) => {
            Ok((TypeName::from(name.as_str()), vec![], vec![]))
        }
        Sexp::List(children, span) => {
            if children.is_empty() {
                return Err(parse_err("empty impl target", *span));
            }
            let (type_name, _) = expect_symbol(&children[0])?;
            if !is_uppercase_start(type_name) {
                return Err(parse_err(
                    "impl target type must start with uppercase",
                    children[0].span(),
                ));
            }

            let mut type_args = Vec::new();
            let mut type_constraints = Vec::new();
            let mut i = 1;

            while i < children.len() {
                if let Sexp::Symbol(s, _) = &children[i] {
                    if s.starts_with(':') && s.len() > 1 {
                        // Constraint annotation: `:TraitName` followed by type var
                        let constraint_name = &s[1..];
                        i += 1;
                        if i >= children.len() {
                            return Err(parse_err(
                                "constraint annotation missing type variable",
                                children[i - 1].span(),
                            ));
                        }
                        let (var_name, _) = expect_symbol(&children[i])?;
                        type_args.push(var_name.into());
                        type_constraints.push((
                            Symbol::from(var_name),
                            TraitName::from(constraint_name),
                        ));
                        i += 1;
                    } else {
                        // Bare type arg (concrete type or unconstrained var)
                        type_args.push(s.as_str().into());
                        i += 1;
                    }
                } else {
                    return Err(parse_err(
                        "expected symbol in impl target",
                        children[i].span(),
                    ));
                }
            }

            Ok((TypeName::from(type_name), type_args, type_constraints))
        }
        _ => Err(parse_err("expected impl target type", sexp.span())),
    }
}

/// Parse a method definition inside an impl block.
/// (defn method_name [params] body)
fn build_impl_method(
    sexp: &Sexp,
    expander: &mut dyn MacroExpander,
) -> Result<Defn, CranelispError> {
    let (children, span) = expect_list(sexp)?;
    if children.is_empty() {
        return Err(parse_err("empty method definition", span));
    }
    let (head, _) = expect_symbol(&children[0])?;
    if head != "defn" {
        return Err(parse_err(
            "impl methods must use (defn name [params] body)",
            span,
        ));
    }
    if children.len() < 4 {
        return Err(parse_err("method defn requires name, params, and body", span));
    }
    let name = get_defn_name(&children[1])?;
    let (params, param_annotations) = build_annotated_params(&children[2])?;
    let body = build_expr(&children[3], expander)?;

    Ok(Defn {
        name,
        docstring: None,
        params,
        param_annotations,
        body,
        visibility: Visibility::Public,
        span,
    })
}

// ---------------------------------------------------------------------------
// Expression builders
// ---------------------------------------------------------------------------

fn build_expr(sexp: &Sexp, expander: &mut dyn MacroExpander) -> Result<Expr, CranelispError> {
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
            reject_non_ring0_symbol(name, *span)?;
            Ok(Expr::Var {
                name: name.as_str().into(),
                span: *span,
            })
        }
        Sexp::List(children, span) => build_list_expr(children, *span, expander),
        Sexp::Bracket(children, span) => build_vec_lit(children, *span, expander),
    }
}

fn build_list_expr(
    children: &[Sexp],
    span: Span,
    expander: &mut dyn MacroExpander,
) -> Result<Expr, CranelispError> {
    if children.is_empty() {
        return Err(parse_err("empty application", span));
    }

    // Check if first child is a keyword symbol
    if let Sexp::Symbol(head, head_span) = &children[0] {
        match head.as_str() {
            "let" => return build_let(children, span, expander),
            "if" => return build_if(children, span, expander),
            "fn" | "lambda" => return build_fn(children, span, expander),
            "match" => return build_match(children, span, expander),
            // Reader-macro forms (desugared by reader, rejected here until their ring)
            "quote" => {
                return Err(parse_err("quote not yet supported (Ring 3)", *head_span))
            }
            "quasiquote" => {
                return Err(parse_err("quasiquote not yet supported (Ring 3)", *head_span))
            }
            "unquote" => {
                return Err(parse_err("unquote not yet supported (Ring 3)", *head_span))
            }
            "unquote-splicing" => {
                return Err(parse_err(
                    "unquote-splicing not yet supported (Ring 3)",
                    *head_span,
                ))
            }
            "anon-fn" => {
                return Err(parse_err(
                    "anonymous functions #(...) not yet supported (Ring 3)",
                    *head_span,
                ))
            }
            // Non-Ring-0 expression forms
            "trace" => return Err(parse_err("trace not yet supported (Ring 4)", *head_span)),
            "run-tests" => {
                return Err(parse_err("run-tests not yet supported (Ring 4)", *head_span))
            }
            "vec" => return Err(parse_err("vec literals not yet supported (Ring 1)", *head_span)),
            "par-let" => {
                return Err(parse_err("par-let not yet supported (Ring 4)", *head_span))
            }
            _ => {
                // Check for macros
                if expander.is_macro(head) {
                    let expanded = expander.expand(&head.as_str().into(), &children[1..], span)?;
                    return build_expr(&expanded, expander);
                }
            }
        }
    }

    // Generic Apply
    build_apply(children, span, expander)
}

fn build_apply(
    children: &[Sexp],
    span: Span,
    expander: &mut dyn MacroExpander,
) -> Result<Expr, CranelispError> {
    let callee = build_expr(&children[0], expander)?;
    let args = build_args_with_annotations(&children[1..], expander)?;
    Ok(Expr::Apply {
        callee: Box::new(callee),
        args,
        span,
    })
}

// ---------------------------------------------------------------------------
// let expression
// ---------------------------------------------------------------------------

fn build_let(
    children: &[Sexp],
    span: Span,
    expander: &mut dyn MacroExpander,
) -> Result<Expr, CranelispError> {
    // (let [name val name val ...] body)
    if children.len() != 3 {
        return Err(parse_err("let requires bindings and body", span));
    }
    let (bracket_items, _) = expect_bracket(&children[1])?;
    let bindings = build_let_bindings(bracket_items, expander)?;
    let body = build_expr(&children[2], expander)?;
    Ok(Expr::Let {
        bindings,
        body: Box::new(body),
        span,
    })
}

fn build_let_bindings(
    items: &[Sexp],
    expander: &mut dyn MacroExpander,
) -> Result<Vec<(cranelisp_types::Symbol, Expr)>, CranelispError> {
    let mut bindings = Vec::new();
    let mut i = 0;
    while i < items.len() {
        let (name, _) = expect_symbol(&items[i])?;
        i += 1;
        if i >= items.len() {
            return Err(parse_err("let binding missing value", items[i - 1].span()));
        }
        let (value, consumed) = build_one_expr_at(items, i, expander)?;
        i += consumed;
        bindings.push((name.into(), value));
    }
    Ok(bindings)
}

// ---------------------------------------------------------------------------
// if expression
// ---------------------------------------------------------------------------

fn build_if(
    children: &[Sexp],
    span: Span,
    expander: &mut dyn MacroExpander,
) -> Result<Expr, CranelispError> {
    // (if cond then else)
    if children.len() != 4 {
        return Err(parse_err(
            "if requires condition, then, and else branches",
            span,
        ));
    }
    let cond = build_expr(&children[1], expander)?;
    let then_branch = build_expr(&children[2], expander)?;
    let else_branch = build_expr(&children[3], expander)?;
    Ok(Expr::If {
        cond: Box::new(cond),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
        span,
    })
}

// ---------------------------------------------------------------------------
// fn / lambda expression
// ---------------------------------------------------------------------------

fn build_fn(
    children: &[Sexp],
    span: Span,
    expander: &mut dyn MacroExpander,
) -> Result<Expr, CranelispError> {
    // (fn [params] body) or (lambda [params] body)
    if children.len() != 3 {
        return Err(parse_err("fn requires param list and body", span));
    }
    let (params, param_annotations) = build_annotated_params(&children[1])?;
    let body = build_expr(&children[2], expander)?;
    Ok(Expr::Lambda {
        params,
        param_annotations,
        body: Box::new(body),
        span,
    })
}

// ---------------------------------------------------------------------------
// match expression
// ---------------------------------------------------------------------------

fn build_match(
    children: &[Sexp],
    span: Span,
    expander: &mut dyn MacroExpander,
) -> Result<Expr, CranelispError> {
    // (match scrutinee [pattern body pattern body ...])
    if children.len() != 3 {
        return Err(parse_err("match requires scrutinee and arms", span));
    }
    let scrutinee = build_expr(&children[1], expander)?;
    let (bracket_items, bracket_span) = expect_bracket(&children[2])?;
    if bracket_items.len() % 2 != 0 {
        return Err(parse_err(
            "match arms must have an even number of elements (pattern body pairs)",
            bracket_span,
        ));
    }
    let arms = build_match_arms(bracket_items, expander)?;
    Ok(Expr::Match {
        scrutinee: Box::new(scrutinee),
        arms,
        span,
        compiler_generated: false,
    })
}

fn build_match_arms(
    items: &[Sexp],
    expander: &mut dyn MacroExpander,
) -> Result<Vec<MatchArm>, CranelispError> {
    let mut arms = Vec::new();
    let mut i = 0;
    while i < items.len() {
        let pat_span = items[i].span();
        let pattern = build_pattern(&items[i])?;
        i += 1;
        if i >= items.len() {
            return Err(parse_err("match arm missing body", pat_span));
        }
        let body = build_expr(&items[i], expander)?;
        let arm_span = Span::new(pat_span.start, items[i].span().end);
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
                    name: name.as_str().into(),
                    bindings: vec![],
                    span: *span,
                })
            } else {
                Ok(Pattern::Var {
                    name: name.as_str().into(),
                    span: *span,
                })
            }
        }
        Sexp::List(children, span) => {
            // (Constructor var1 var2 ...)
            if children.is_empty() {
                return Err(parse_err("empty pattern", *span));
            }
            let (name, _) = expect_symbol(&children[0])?;
            let bindings = children[1..]
                .iter()
                .map(|s| {
                    let (n, _) = expect_symbol(s)?;
                    Ok(n.into())
                })
                .collect::<Result<Vec<_>, CranelispError>>()?;
            Ok(Pattern::Constructor {
                name: name.into(),
                bindings,
                span: *span,
            })
        }
        _ => Err(parse_err("invalid pattern", sexp.span())),
    }
}

// ---------------------------------------------------------------------------
// Vec literal
// ---------------------------------------------------------------------------

fn build_vec_lit(
    children: &[Sexp],
    span: Span,
    expander: &mut dyn MacroExpander,
) -> Result<Expr, CranelispError> {
    let elements = build_args_with_annotations(children, expander)?;
    Ok(Expr::VecLit { elements, span })
}

// ---------------------------------------------------------------------------
// Annotation-aware expression building
// ---------------------------------------------------------------------------

/// Try to consume a type annotation starting at `items[pos]`.
/// Returns `Some((TypeExpr, items_consumed))` or `None`.
fn try_consume_annotation(items: &[Sexp], pos: usize) -> Option<(TypeExpr, usize)> {
    if pos >= items.len() {
        return None;
    }
    match &items[pos] {
        // `:Int`, `:a`, `:Num` -- simple colon-prefixed symbol
        Sexp::Symbol(s, _) if s.starts_with(':') && s.len() > 1 => {
            let name = &s[1..];
            let te = parse_annotation_name(name);
            Some((te, 1))
        }
        // `:` followed by `(Fn [...] ret)` or `(Option a)` etc -- compound annotation
        Sexp::Symbol(s, _) if s == ":" => {
            if pos + 1 < items.len()
                && let Ok(te) = build_type_expr(&items[pos + 1])
            {
                return Some((te, 2));
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
        TypeExpr::Named(name.into())
    } else {
        TypeExpr::TypeVar(name.into())
    }
}

/// Build one expression from a slice at `pos`, consuming annotation if present.
/// Returns `(expr, items_consumed)`.
fn build_one_expr_at(
    items: &[Sexp],
    pos: usize,
    expander: &mut dyn MacroExpander,
) -> Result<(Expr, usize), CranelispError> {
    if let Some((annotation, consumed)) = try_consume_annotation(items, pos) {
        let expr_pos = pos + consumed;
        if expr_pos >= items.len() {
            return Err(parse_err("annotation missing expression", items[pos].span()));
        }
        let inner = build_expr(&items[expr_pos], expander)?;
        let span = Span::new(items[pos].span().start, items[expr_pos].span().end);
        Ok((
            Expr::Annotate {
                annotation,
                expr: Box::new(inner),
                span,
            },
            consumed + 1,
        ))
    } else {
        let expr = build_expr(&items[pos], expander)?;
        Ok((expr, 1))
    }
}

/// Build argument list, handling inline annotations (`:Type expr` -> `Annotate`).
fn build_args_with_annotations(
    items: &[Sexp],
    expander: &mut dyn MacroExpander,
) -> Result<Vec<Expr>, CranelispError> {
    let mut args = Vec::new();
    let mut i = 0;
    while i < items.len() {
        let (expr, consumed) = build_one_expr_at(items, i, expander)?;
        args.push(expr);
        i += consumed;
    }
    Ok(args)
}

// ---------------------------------------------------------------------------
// Parameter list builders
// ---------------------------------------------------------------------------

/// Build annotated parameter list from a Bracket sexp.
/// Returns (names, annotations).
fn build_annotated_params(
    sexp: &Sexp,
) -> Result<(Vec<Symbol>, Vec<Option<TypeExpr>>), CranelispError> {
    let (items, _) = expect_bracket(sexp)?;
    let mut names: Vec<Symbol> = Vec::new();
    let mut annotations = Vec::new();
    let mut i = 0;

    while i < items.len() {
        if let Some((te, consumed)) = try_consume_annotation(items, i) {
            // Next item after annotation is the param name
            let name_pos = i + consumed;
            if name_pos >= items.len() {
                return Err(parse_err(
                    "annotation missing parameter name",
                    items[i].span(),
                ));
            }
            let (name, _) = expect_symbol(&items[name_pos])?;
            names.push(name.into());
            annotations.push(Some(te));
            i = name_pos + 1;
        } else {
            let (name, _) = expect_symbol(&items[i])?;
            names.push(name.into());
            annotations.push(None);
            i += 1;
        }
    }

    let has_any = annotations.iter().any(|a| a.is_some());
    Ok((names, if has_any { annotations } else { vec![] }))
}

// ---------------------------------------------------------------------------
// Type expression builders
// ---------------------------------------------------------------------------

fn build_type_expr(sexp: &Sexp) -> Result<TypeExpr, CranelispError> {
    match sexp {
        Sexp::Symbol(name, _) => {
            if name == "self" {
                Ok(TypeExpr::SelfType)
            } else if is_uppercase_start(name) {
                Ok(TypeExpr::Named(name.as_str().into()))
            } else {
                Ok(TypeExpr::TypeVar(name.as_str().into()))
            }
        }
        Sexp::List(children, span) => build_type_expr_from_list(children, *span),
        _ => Err(parse_err("invalid type expression", sexp.span())),
    }
}

fn build_type_expr_from_list(
    children: &[Sexp],
    span: Span,
) -> Result<TypeExpr, CranelispError> {
    if children.is_empty() {
        return Err(parse_err("empty type expression", span));
    }
    if let Sexp::Symbol(head, _) = &children[0] {
        if head == "Fn" {
            // (Fn [param_types] ret_type)
            if children.len() != 3 {
                return Err(parse_err(
                    "Fn requires param types and return type",
                    span,
                ));
            }
            let (param_items, _) = expect_bracket(&children[1])?;
            let params = param_items
                .iter()
                .map(build_type_expr)
                .collect::<Result<Vec<_>, _>>()?;
            let ret = build_type_expr(&children[2])?;
            return Ok(TypeExpr::FnType(params, Box::new(ret)));
        }
        // (Name arg1 arg2 ...) -> Applied
        let args = children[1..]
            .iter()
            .map(build_type_expr)
            .collect::<Result<Vec<_>, _>>()?;
        return Ok(TypeExpr::Applied(head.as_str().into(), args));
    }
    Err(parse_err("invalid type expression", span))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::NoOpExpander;

    fn parse_and_build_program(input: &str) -> Result<Program, CranelispError> {
        let sexps = crate::reader::parse(input)?;
        let mut expander = NoOpExpander;
        build_program(&sexps, &mut expander)
    }

    fn parse_and_build_repl(input: &str) -> Result<ReplInput, CranelispError> {
        let sexps = crate::reader::parse(input)?;
        assert!(!sexps.is_empty(), "expected at least one sexp");
        let mut expander = NoOpExpander;
        build_repl_input(&sexps[0], &mut expander)
    }

    fn parse_and_build_expr(input: &str) -> Result<Expr, CranelispError> {
        let sexps = crate::reader::parse(input)?;
        assert!(!sexps.is_empty(), "expected at least one sexp");
        let mut expander = NoOpExpander;
        build_expr(&sexps[0], &mut expander)
    }

    // -- Literals --

    // spec: 02-grammar §2.3.1 — integer literal expression
    #[test]
    fn test_build_integer_literal() {
        match parse_and_build_expr("42").unwrap() {
            Expr::IntLit { value, .. } => assert_eq!(value, 42),
            other => panic!("expected IntLit, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.1 — negative integer literal expression
    #[test]
    fn test_build_negative_integer() {
        match parse_and_build_expr("-7").unwrap() {
            Expr::IntLit { value, .. } => assert_eq!(value, -7),
            other => panic!("expected IntLit, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.1 — float literal expression
    #[test]
    fn test_build_float_literal() {
        match parse_and_build_expr("2.72").unwrap() {
            Expr::FloatLit { value, .. } => assert!((value - 2.72).abs() < 1e-10),
            other => panic!("expected FloatLit, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.1 — boolean literal expression
    #[test]
    fn test_build_bool_literal() {
        match parse_and_build_expr("true").unwrap() {
            Expr::BoolLit { value, .. } => assert!(value),
            other => panic!("expected BoolLit, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.1 — string literal expression
    #[test]
    fn test_build_string_literal() {
        match parse_and_build_expr("\"hello\"").unwrap() {
            Expr::StringLit { value, .. } => assert_eq!(value, "hello"),
            other => panic!("expected StringLit, got {other:?}"),
        }
    }

    // -- Variable reference --

    // spec: 02-grammar §2.3.2 — variable reference
    #[test]
    fn test_build_variable() {
        match parse_and_build_expr("foo").unwrap() {
            Expr::Var { name, .. } => assert_eq!(name, "foo"),
            other => panic!("expected Var, got {other:?}"),
        }
    }

    // -- Let expression --

    // spec: 02-grammar §2.3.3 — let expression with single binding
    #[test]
    fn test_build_let() {
        match parse_and_build_expr("(let [x 42] x)").unwrap() {
            Expr::Let {
                bindings, body, ..
            } => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].0, "x");
                match &bindings[0].1 {
                    Expr::IntLit { value, .. } => assert_eq!(*value, 42),
                    other => panic!("expected IntLit in binding, got {other:?}"),
                }
                match body.as_ref() {
                    Expr::Var { name, .. } => assert_eq!(name, "x"),
                    other => panic!("expected Var in body, got {other:?}"),
                }
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.3 — let expression with multiple bindings
    #[test]
    fn test_build_let_multiple_bindings() {
        match parse_and_build_expr("(let [x 1 y 2] (+ x y))").unwrap() {
            Expr::Let { bindings, .. } => {
                assert_eq!(bindings.len(), 2);
                assert_eq!(bindings[0].0, "x");
                assert_eq!(bindings[1].0, "y");
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.3 — let requires body expression
    #[test]
    fn test_build_let_wrong_arity() {
        assert!(parse_and_build_expr("(let [x 1])").is_err());
    }

    // -- If expression --

    // spec: 02-grammar §2.3.4 — if expression with three sub-expressions
    #[test]
    fn test_build_if() {
        match parse_and_build_expr("(if true 1 0)").unwrap() {
            Expr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                assert!(matches!(cond.as_ref(), Expr::BoolLit { value: true, .. }));
                assert!(matches!(then_branch.as_ref(), Expr::IntLit { value: 1, .. }));
                assert!(matches!(
                    else_branch.as_ref(),
                    Expr::IntLit { value: 0, .. }
                ));
            }
            other => panic!("expected If, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.4 — if requires exactly three sub-expressions
    #[test]
    fn test_build_if_wrong_arity() {
        assert!(parse_and_build_expr("(if true 1)").is_err());
    }

    // -- Lambda expression --

    // spec: 02-grammar §2.3.5 — fn lambda expression
    #[test]
    fn test_build_lambda() {
        match parse_and_build_expr("(fn [x] x)").unwrap() {
            Expr::Lambda { params, body, .. } => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0], "x");
                match body.as_ref() {
                    Expr::Var { name, .. } => assert_eq!(name, "x"),
                    other => panic!("expected Var, got {other:?}"),
                }
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.5 — lambda keyword alias for fn
    #[test]
    fn test_build_lambda_with_lambda_keyword() {
        match parse_and_build_expr("(lambda [x] x)").unwrap() {
            Expr::Lambda { params, .. } => {
                assert_eq!(params.len(), 1);
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.8.2 — annotated parameter in lambda
    #[test]
    fn test_build_lambda_annotated_params() {
        match parse_and_build_expr("(fn [:Int x] x)").unwrap() {
            Expr::Lambda {
                params,
                param_annotations,
                ..
            } => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0], "x");
                assert_eq!(param_annotations.len(), 1);
                assert!(param_annotations[0].is_some());
                match param_annotations[0].as_ref().unwrap() {
                    TypeExpr::Named(n) => assert_eq!(*n, "Int"),
                    other => panic!("expected Named(Int), got {other:?}"),
                }
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    // -- Apply expression --

    // spec: 02-grammar §2.3.6 — function application
    #[test]
    fn test_build_apply() {
        match parse_and_build_expr("(+ 1 2)").unwrap() {
            Expr::Apply {
                callee, args, ..
            } => {
                match callee.as_ref() {
                    Expr::Var { name, .. } => assert_eq!(name, "+"),
                    other => panic!("expected Var, got {other:?}"),
                }
                assert_eq!(args.len(), 2);
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.8 — type annotation in function argument
    #[test]
    fn test_build_apply_with_annotation() {
        // (f :Int 42) -> Apply(f, [Annotate(:Int, 42)])
        match parse_and_build_expr("(f :Int 42)").unwrap() {
            Expr::Apply { args, .. } => {
                assert_eq!(args.len(), 1);
                match &args[0] {
                    Expr::Annotate { annotation, .. } => {
                        match annotation {
                            TypeExpr::Named(n) => assert_eq!(*n, "Int"),
                            other => panic!("expected Named(Int), got {other:?}"),
                        }
                    }
                    other => panic!("expected Annotate, got {other:?}"),
                }
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // -- Match expression --

    // spec: 02-grammar §2.3.7 — match expression with constructor patterns
    #[test]
    fn test_build_match() {
        match parse_and_build_expr("(match x [Red 1 Green 2 Blue 3])").unwrap() {
            Expr::Match { arms, .. } => {
                assert_eq!(arms.len(), 3);
                match &arms[0].pattern {
                    Pattern::Constructor { name, bindings, .. } => {
                        assert_eq!(name, "Red");
                        assert!(bindings.is_empty());
                    }
                    other => panic!("expected Constructor, got {other:?}"),
                }
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.5.2 — wildcard pattern in match
    #[test]
    fn test_build_match_with_wildcard() {
        match parse_and_build_expr("(match x [Red 1 _ 0])").unwrap() {
            Expr::Match { arms, .. } => {
                assert_eq!(arms.len(), 2);
                assert!(matches!(&arms[1].pattern, Pattern::Wildcard { .. }));
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.5.3 — variable pattern in match
    #[test]
    fn test_build_match_with_var_pattern() {
        match parse_and_build_expr("(match x [y y])").unwrap() {
            Expr::Match { arms, .. } => {
                assert_eq!(arms.len(), 1);
                match &arms[0].pattern {
                    Pattern::Var { name, .. } => assert_eq!(name, "y"),
                    other => panic!("expected Var, got {other:?}"),
                }
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.7 — match arms must be even number of elements
    #[test]
    fn test_build_match_odd_arms_rejected() {
        let err = parse_and_build_expr("(match x [Red 1 Green])").unwrap_err();
        assert!(err.message().contains("even number"));
    }

    // spec: 02-grammar §2.5.1 — constructor pattern with field bindings
    #[test]
    fn test_build_match_with_constructor_bindings() {
        match parse_and_build_expr("(match x [(Some v) v])").unwrap() {
            Expr::Match { arms, .. } => {
                assert_eq!(arms.len(), 1);
                match &arms[0].pattern {
                    Pattern::Constructor { name, bindings, .. } => {
                        assert_eq!(name, "Some");
                        assert_eq!(bindings.len(), 1);
                        assert_eq!(bindings[0], "v");
                    }
                    other => panic!("expected Constructor, got {other:?}"),
                }
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    // -- defn --

    // spec: 02-grammar §2.2.1 — defn single-signature form
    #[test]
    fn test_build_defn() {
        let prog = parse_and_build_program("(defn add [a b] (+ a b))").unwrap();
        assert_eq!(prog.len(), 1);
        match &prog[0] {
            TopLevel::Defn(defn) => {
                assert_eq!(defn.name, "add");
                assert_eq!(defn.params.len(), 2);
                assert_eq!(defn.visibility, Visibility::Public);
            }
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.6 — defn- private function definition
    #[test]
    fn test_build_defn_private() {
        let prog = parse_and_build_program("(defn- helper [x] x)").unwrap();
        match &prog[0] {
            TopLevel::Defn(defn) => {
                assert_eq!(defn.name, "helper");
                assert_eq!(defn.visibility, Visibility::Private);
            }
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.7 — defn with docstring
    #[test]
    fn test_build_defn_with_docstring() {
        let prog = parse_and_build_program("(defn add \"Adds two values\" [a b] (+ a b))").unwrap();
        match &prog[0] {
            TopLevel::Defn(defn) => {
                assert_eq!(defn.docstring.as_deref(), Some("Adds two values"));
            }
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.1 — defn multi-signature form
    #[test]
    fn test_build_defn_multi() {
        let prog = parse_and_build_program("(defn f ([x] x) ([x y] (+ x y)))").unwrap();
        match &prog[0] {
            TopLevel::DefnMulti { name, variants, .. } => {
                assert_eq!(name, "f");
                assert_eq!(variants.len(), 2);
                assert_eq!(variants[0].params.len(), 1);
                assert_eq!(variants[1].params.len(), 2);
            }
            other => panic!("expected DefnMulti, got {other:?}"),
        }
    }

    // -- deftype --

    // spec: 02-grammar §2.2.2 — deftype enum (all nullary constructors)
    #[test]
    fn test_build_deftype_enum() {
        let prog = parse_and_build_program("(deftype Color Red Green Blue)").unwrap();
        match &prog[0] {
            TopLevel::TypeDef {
                name,
                constructors,
                ..
            } => {
                assert_eq!(name, "Color");
                assert_eq!(constructors.len(), 3);
                assert_eq!(constructors[0].name, "Red");
                assert_eq!(constructors[1].name, "Green");
                assert_eq!(constructors[2].name, "Blue");
                assert!(constructors[0].fields.is_empty());
            }
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.2 — deftype product type with typed fields
    #[test]
    fn test_build_deftype_product() {
        let prog = parse_and_build_program("(deftype Point [:Int x :Int y])").unwrap();
        match &prog[0] {
            TopLevel::TypeDef {
                name,
                constructors,
                ..
            } => {
                assert_eq!(name, "Point");
                assert_eq!(constructors.len(), 1);
                assert_eq!(constructors[0].fields.len(), 2);
                assert_eq!(constructors[0].fields[0].name, "x");
                assert_eq!(constructors[0].fields[1].name, "y");
            }
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.2 — deftype polymorphic sum type
    #[test]
    fn test_build_deftype_sum() {
        let prog = parse_and_build_program("(deftype (Option a) None (Some [:a val]))").unwrap();
        match &prog[0] {
            TopLevel::TypeDef {
                name,
                type_params,
                constructors,
                ..
            } => {
                assert_eq!(name, "Option");
                assert_eq!(type_params.len(), 1);
                assert_eq!(type_params[0], "a");
                assert_eq!(constructors.len(), 2);
                assert_eq!(constructors[0].name, "None");
                assert!(constructors[0].fields.is_empty());
                assert_eq!(constructors[1].name, "Some");
                assert_eq!(constructors[1].fields.len(), 1);
            }
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.2 — deftype shortcut syntax (bare field names)
    #[test]
    fn test_build_deftype_shortcut_fields() {
        // (deftype Pair [first second]) — bare names get sequential type vars
        let prog = parse_and_build_program("(deftype Pair [first second])").unwrap();
        match &prog[0] {
            TopLevel::TypeDef {
                name,
                type_params,
                constructors,
                ..
            } => {
                assert_eq!(name, "Pair");
                assert_eq!(type_params.len(), 2);
                assert_eq!(type_params[0], "a");
                assert_eq!(type_params[1], "b");
                assert_eq!(constructors[0].fields.len(), 2);
                // Fields should have sequential type vars (a, b, c, ...)
                match &constructors[0].fields[0].type_expr {
                    TypeExpr::TypeVar(v) => assert_eq!(*v, "a"),
                    other => panic!("expected TypeVar, got {other:?}"),
                }
                match &constructors[0].fields[1].type_expr {
                    TypeExpr::TypeVar(v) => assert_eq!(*v, "b"),
                    other => panic!("expected TypeVar, got {other:?}"),
                }
            }
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    // -- REPL input --

    // spec: 02-grammar §2.1 — REPL top-level expression
    #[test]
    fn test_repl_expression() {
        match parse_and_build_repl("42").unwrap() {
            ReplInput::Expr(Expr::IntLit { value, .. }) => assert_eq!(value, 42),
            other => panic!("expected Expr(IntLit), got {other:?}"),
        }
    }

    // spec: 02-grammar §2.1 — REPL defn definition
    #[test]
    fn test_repl_defn() {
        match parse_and_build_repl("(defn f [x] x)").unwrap() {
            ReplInput::Defn(defn) => assert_eq!(defn.name, "f"),
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.1 — REPL deftype definition
    #[test]
    fn test_repl_deftype() {
        match parse_and_build_repl("(deftype Color Red Green Blue)").unwrap() {
            ReplInput::TypeDef { name, .. } => assert_eq!(name, "Color"),
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    // -- Rejected forms --

    // spec: 02-grammar §2.3 — trace not yet implemented
    #[test]
    fn test_reject_trace() {
        let err = parse_and_build_expr("(trace 42)").unwrap_err();
        assert!(err.message().contains("trace not yet supported"));
    }

    // spec: 02-grammar §2.3.9 — vec keyword form not yet implemented
    #[test]
    fn test_reject_vec_keyword() {
        let err = parse_and_build_expr("(vec 1 2 3)").unwrap_err();
        assert!(err.message().contains("vec literals not yet supported"));
    }

    // -- deftrait --

    // spec: 02-grammar §2.2.3 — simple deftrait with one method
    #[test]
    fn test_build_deftrait_simple() {
        let prog = parse_and_build_program(
            "(deftrait Display (show [self] String))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitDecl(decl) => {
                assert_eq!(decl.name, "Display");
                assert!(decl.type_params.is_empty());
                assert_eq!(decl.methods.len(), 1);
                assert_eq!(decl.methods[0].name, "show");
                assert_eq!(decl.methods[0].params.len(), 1);
                assert!(matches!(&decl.methods[0].params[0], TypeExpr::SelfType));
                assert!(matches!(&decl.methods[0].ret_type, TypeExpr::Named(n) if n == "String"));
                assert!(decl.methods[0].default_body.is_none());
            }
            other => panic!("expected TraitDecl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.7 — deftrait with docstring
    #[test]
    fn test_build_deftrait_with_docstring() {
        let prog = parse_and_build_program(
            "(deftrait Display \"Convert to string\" (show [self] String))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitDecl(decl) => {
                assert_eq!(decl.docstring.as_deref(), Some("Convert to string"));
            }
            other => panic!("expected TraitDecl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.3 — deftrait with multiple method signatures
    #[test]
    fn test_build_deftrait_multiple_methods() {
        let prog = parse_and_build_program(
            "(deftrait Num (+ [self self] self) (- [self self] self))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitDecl(decl) => {
                assert_eq!(decl.name, "Num");
                assert_eq!(decl.methods.len(), 2);
                assert_eq!(decl.methods[0].name, "+");
                assert_eq!(decl.methods[1].name, "-");
            }
            other => panic!("expected TraitDecl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.3 — higher-kinded deftrait
    #[test]
    fn test_build_deftrait_hkt() {
        let prog = parse_and_build_program(
            "(deftrait (Functor f) (fmap [(Fn [a] b) (f a)] (f b)))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitDecl(decl) => {
                assert_eq!(decl.name, "Functor");
                assert_eq!(decl.type_params.len(), 1);
                assert_eq!(decl.type_params[0], "f");
                assert_eq!(decl.methods[0].hkt_param_index, Some(1));
            }
            other => panic!("expected TraitDecl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.3 — deftrait with default method implementation
    #[test]
    fn test_build_deftrait_with_default() {
        let prog = parse_and_build_program(
            "(deftrait Ord (< [self self] Bool) (<= [x y] Bool (if (< x y) true (= x y))))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitDecl(decl) => {
                assert_eq!(decl.methods.len(), 2);
                assert!(decl.methods[0].default_body.is_none());
                assert!(decl.methods[0].default_param_names.is_empty());
                assert!(decl.methods[1].default_body.is_some());
                assert_eq!(decl.methods[1].default_param_names.len(), 2);
                assert_eq!(decl.methods[1].default_param_names[0], "x");
                assert_eq!(decl.methods[1].default_param_names[1], "y");
            }
            other => panic!("expected TraitDecl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.6 — deftrait- private trait declaration
    #[test]
    fn test_build_deftrait_private() {
        let prog = parse_and_build_program(
            "(deftrait- Internal (method [self] Int))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitDecl(decl) => {
                assert_eq!(decl.visibility, Visibility::Private);
            }
            other => panic!("expected TraitDecl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.3 — HKT traits reject default method implementations
    #[test]
    fn test_build_deftrait_hkt_default_rejected() {
        let err = parse_and_build_program(
            "(deftrait (Functor f) (fmap [x] (f Int) x))",
        ).unwrap_err();
        assert!(err.message().contains("default method implementations are not supported on higher-kinded traits"));
    }

    // -- impl --

    // spec: 02-grammar §2.2.4 — impl concrete type
    #[test]
    fn test_build_impl_concrete() {
        let prog = parse_and_build_program(
            "(impl Display Int (defn show [x] (int-to-string x)))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => {
                assert_eq!(imp.trait_name, "Display");
                assert_eq!(imp.target_type, "Int");
                assert!(imp.type_args.is_empty());
                assert!(imp.type_constraints.is_empty());
                assert_eq!(imp.methods.len(), 1);
                assert_eq!(imp.methods[0].name, "show");
                assert_eq!(imp.methods[0].params.len(), 1);
            }
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.4 — impl polymorphic type with trait constraint
    #[test]
    fn test_build_impl_polymorphic_with_constraint() {
        let prog = parse_and_build_program(
            "(impl Display (Option :Display a) (defn show [x] x))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => {
                assert_eq!(imp.trait_name, "Display");
                assert_eq!(imp.target_type, "Option");
                assert_eq!(imp.type_args.len(), 1);
                assert_eq!(imp.type_args[0], "a");
                assert_eq!(imp.type_constraints.len(), 1);
                assert_eq!(imp.type_constraints[0].0, "a");
                assert_eq!(imp.type_constraints[0].1, "Display");
            }
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.4 — impl higher-kinded trait
    #[test]
    fn test_build_impl_hkt() {
        let prog = parse_and_build_program(
            "(impl Functor Option (defn fmap [f opt] opt))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => {
                assert_eq!(imp.trait_name, "Functor");
                assert_eq!(imp.target_type, "Option");
                assert!(imp.type_args.is_empty());
            }
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.4 — impl in REPL context
    #[test]
    fn test_build_impl_repl() {
        match parse_and_build_repl(
            "(impl Eq Int (defn = [x y] (eq-i64 x y)))",
        ).unwrap() {
            ReplInput::TraitImpl(imp) => {
                assert_eq!(imp.trait_name, "Eq");
                assert_eq!(imp.target_type, "Int");
            }
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.3 — deftrait in REPL context
    #[test]
    fn test_build_deftrait_repl() {
        match parse_and_build_repl(
            "(deftrait Showable (show [self] String))",
        ).unwrap() {
            ReplInput::TraitDecl(decl) => {
                assert_eq!(decl.name, "Showable");
            }
            other => panic!("expected TraitDecl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.4 — impl with multiple methods
    #[test]
    fn test_build_impl_multiple_methods() {
        let prog = parse_and_build_program(
            "(impl Num Int (defn + [x y] (add-i64 x y)) (defn - [x y] (sub-i64 x y)))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitImpl(imp) => {
                assert_eq!(imp.methods.len(), 2);
                assert_eq!(imp.methods[0].name, "+");
                assert_eq!(imp.methods[1].name, "-");
            }
            other => panic!("expected TraitImpl, got {other:?}"),
        }
    }

    // -- Type annotations --

    // spec: 02-grammar §2.8.2 — simple named type annotation on param
    #[test]
    fn test_type_annotation_simple() {
        // (fn [:Int x] x) — annotation on param
        match parse_and_build_expr("(fn [:Int x] x)").unwrap() {
            Expr::Lambda {
                param_annotations, ..
            } => {
                assert_eq!(param_annotations.len(), 1);
                match param_annotations[0].as_ref().unwrap() {
                    TypeExpr::Named(n) => assert_eq!(*n, "Int"),
                    other => panic!("expected Named, got {other:?}"),
                }
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.4.2 — type variable annotation on param
    #[test]
    fn test_type_annotation_type_var() {
        match parse_and_build_expr("(fn [:a x] x)").unwrap() {
            Expr::Lambda {
                param_annotations, ..
            } => {
                assert_eq!(param_annotations.len(), 1);
                match param_annotations[0].as_ref().unwrap() {
                    TypeExpr::TypeVar(v) => assert_eq!(*v, "a"),
                    other => panic!("expected TypeVar, got {other:?}"),
                }
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.4.5 — function type annotation with bare colon
    #[test]
    fn test_type_annotation_fn_type() {
        // (fn [: (Fn [Int] Int) f] (f 42))
        match parse_and_build_expr("(fn [: (Fn [Int] Int) f] (f 42))").unwrap() {
            Expr::Lambda {
                params,
                param_annotations,
                ..
            } => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0], "f");
                match param_annotations[0].as_ref().unwrap() {
                    TypeExpr::FnType(params, ret) => {
                        assert_eq!(params.len(), 1);
                        match &params[0] {
                            TypeExpr::Named(n) => assert_eq!(*n, "Int"),
                            other => panic!("expected Named, got {other:?}"),
                        }
                        match ret.as_ref() {
                            TypeExpr::Named(n) => assert_eq!(*n, "Int"),
                            other => panic!("expected Named, got {other:?}"),
                        }
                    }
                    other => panic!("expected FnType, got {other:?}"),
                }
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    // -- Empty application --

    // spec: 02-grammar §2.3.6 — empty application is an error
    #[test]
    fn test_empty_application_rejected() {
        let err = parse_and_build_expr("()").unwrap_err();
        assert!(err.message().contains("empty application"));
    }

    // -- Spans --

    // spec: 02-grammar §2.3.1 — expression span tracking
    #[test]
    fn test_expr_span() {
        let expr = parse_and_build_expr("42").unwrap();
        assert_eq!(expr.span(), Span::new(0, 2));
    }

    // spec: 02-grammar §2.3.3 — let expression span tracking
    #[test]
    fn test_let_span() {
        let expr = parse_and_build_expr("(let [x 1] x)").unwrap();
        assert_eq!(expr.span(), Span::new(0, 13));
    }

    // -- Nested expressions --

    // spec: 02-grammar §2.3.4 — nested let inside if branch
    #[test]
    fn test_nested_let_in_if() {
        let expr = parse_and_build_expr("(if true (let [x 1] x) 0)").unwrap();
        match expr {
            Expr::If { then_branch, .. } => {
                assert!(matches!(then_branch.as_ref(), Expr::Let { .. }));
            }
            other => panic!("expected If, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.5 — lambda in let binding value
    #[test]
    fn test_lambda_in_let() {
        let expr = parse_and_build_expr("(let [f (fn [x] x)] (f 42))").unwrap();
        match expr {
            Expr::Let { bindings, .. } => {
                assert!(matches!(&bindings[0].1, Expr::Lambda { .. }));
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    // -- Rejection of reader-macro forms --

    // spec: 01-lexical §1.6 — quote form rejected (Ring 3)
    #[test]
    fn test_reject_quote() {
        let err = parse_and_build_expr("'foo").unwrap_err();
        assert!(err.message().contains("quote not yet supported"));
        assert!(err.message().contains("Ring 3"));
    }

    // spec: 01-lexical §1.6 — quasiquote form rejected (Ring 3)
    #[test]
    fn test_reject_quasiquote() {
        let err = parse_and_build_expr("`foo").unwrap_err();
        assert!(err.message().contains("quasiquote not yet supported"));
        assert!(err.message().contains("Ring 3"));
    }

    // spec: 01-lexical §1.6 — unquote form rejected (Ring 3)
    #[test]
    fn test_reject_unquote() {
        let err = parse_and_build_expr("~x").unwrap_err();
        assert!(err.message().contains("unquote not yet supported"));
        assert!(err.message().contains("Ring 3"));
    }

    // spec: 01-lexical §1.6 — unquote-splicing form rejected (Ring 3)
    #[test]
    fn test_reject_unquote_splicing() {
        let err = parse_and_build_expr("~@xs").unwrap_err();
        assert!(err.message().contains("unquote-splicing not yet supported"));
        assert!(err.message().contains("Ring 3"));
    }

    // spec: 01-lexical §1.6 — anonymous function form rejected (Ring 3)
    #[test]
    fn test_reject_anon_fn() {
        let err = parse_and_build_expr("#(+ %1 %2)").unwrap_err();
        assert!(err.message().contains("anonymous functions"));
        assert!(err.message().contains("Ring 3"));
    }

    // spec: 01-lexical §1.4.7 — percent param rejected in AST (Ring 3)
    #[test]
    fn test_reject_percent_param() {
        let err = parse_and_build_expr("%1").unwrap_err();
        assert!(err.message().contains("percent parameters not yet supported"));
        assert!(err.message().contains("Ring 3"));
    }

    // spec: 01-lexical §1.4.6 — gensym dollar rejected in AST (Ring 3)
    #[test]
    fn test_reject_gensym_dollar() {
        let err = parse_and_build_expr("$foo").unwrap_err();
        assert!(err.message().contains("gensym not yet supported"));
        assert!(err.message().contains("Ring 3"));
    }

    // spec: 01-lexical §1.4.8 — ampersand rejected in AST (Ring 3)
    #[test]
    fn test_reject_ampersand() {
        let err = parse_and_build_expr("&rest").unwrap_err();
        assert!(err.message().contains("rest parameters not yet supported"));
        assert!(err.message().contains("Ring 3"));
    }

    // spec: 01-lexical §1.4.6 — gensym shorthand rejected in AST (Ring 3)
    #[test]
    fn test_reject_gensym_shorthand() {
        let err = parse_and_build_expr("foo#").unwrap_err();
        assert!(err.message().contains("gensym shorthand not yet supported"));
        assert!(err.message().contains("Ring 3"));
    }

    // -- Ring 1: String literal --

    // spec: 02-grammar §2.3.1 — empty string literal in AST
    #[test]
    fn test_string_literal_empty() {
        match parse_and_build_expr("\"\"").unwrap() {
            Expr::StringLit { value, .. } => assert_eq!(value, ""),
            other => panic!("expected StringLit, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.1 — string literal with escape sequences in AST
    #[test]
    fn test_string_literal_with_escapes() {
        match parse_and_build_expr("\"line1\\nline2\"").unwrap() {
            Expr::StringLit { value, .. } => assert_eq!(value, "line1\nline2"),
            other => panic!("expected StringLit, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.1 — string literal span tracking in AST
    #[test]
    fn test_string_literal_span() {
        let expr = parse_and_build_expr("\"hello\"").unwrap();
        assert_eq!(expr.span(), Span::new(0, 7));
    }

    // spec: 02-grammar §2.3.3 — string literal in let binding value
    #[test]
    fn test_string_in_let_binding() {
        match parse_and_build_expr("(let [s \"hello\"] s)").unwrap() {
            Expr::Let { bindings, .. } => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].0, "s");
                match &bindings[0].1 {
                    Expr::StringLit { value, .. } => assert_eq!(value, "hello"),
                    other => panic!("expected StringLit in binding, got {other:?}"),
                }
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.6 — string literal as function argument
    #[test]
    fn test_string_as_function_argument() {
        match parse_and_build_expr("(f \"world\")").unwrap() {
            Expr::Apply { args, .. } => {
                assert_eq!(args.len(), 1);
                match &args[0] {
                    Expr::StringLit { value, .. } => assert_eq!(value, "world"),
                    other => panic!("expected StringLit, got {other:?}"),
                }
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.4 — string literals in if branches
    #[test]
    fn test_string_in_if_branches() {
        match parse_and_build_expr("(if true \"yes\" \"no\")").unwrap() {
            Expr::If {
                then_branch,
                else_branch,
                ..
            } => {
                match then_branch.as_ref() {
                    Expr::StringLit { value, .. } => assert_eq!(value, "yes"),
                    other => panic!("expected StringLit in then, got {other:?}"),
                }
                match else_branch.as_ref() {
                    Expr::StringLit { value, .. } => assert_eq!(value, "no"),
                    other => panic!("expected StringLit in else, got {other:?}"),
                }
            }
            other => panic!("expected If, got {other:?}"),
        }
    }

    // -- Ring 1: Docstring interaction audit --

    // spec: 02-grammar §2.7 — docstring captured between name and params
    #[test]
    fn test_docstring_captured_in_defn() {
        let prog =
            parse_and_build_program("(defn greet \"docstring\" [x] x)").unwrap();
        match &prog[0] {
            TopLevel::Defn(defn) => {
                assert_eq!(defn.docstring.as_deref(), Some("docstring"));
                assert_eq!(defn.params.len(), 1);
                assert_eq!(defn.params[0], "x");
            }
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.7 — string in let binding is value, not docstring
    #[test]
    fn test_string_in_let_is_not_docstring() {
        // A string in a let binding position is a value, not a docstring.
        match parse_and_build_expr("(let [s \"hello\"] s)").unwrap() {
            Expr::Let { bindings, body, .. } => {
                match &bindings[0].1 {
                    Expr::StringLit { value, .. } => assert_eq!(value, "hello"),
                    other => panic!("expected StringLit, got {other:?}"),
                }
                match body.as_ref() {
                    Expr::Var { name, .. } => assert_eq!(name, "s"),
                    other => panic!("expected Var in body, got {other:?}"),
                }
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.7 — docstring is None when absent
    #[test]
    fn test_docstring_not_captured_when_absent() {
        let prog = parse_and_build_program("(defn f [x] x)").unwrap();
        match &prog[0] {
            TopLevel::Defn(defn) => {
                assert!(defn.docstring.is_none());
            }
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.7 — deftype docstring between head and body
    #[test]
    fn test_docstring_in_deftype() {
        let prog =
            parse_and_build_program("(deftype Color \"Primary colors\" Red Green Blue)")
                .unwrap();
        match &prog[0] {
            TopLevel::TypeDef { docstring, .. } => {
                assert_eq!(docstring.as_deref(), Some("Primary colors"));
            }
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    // -- Ring 1: TypeExpr::Applied via annotation --

    // spec: 02-grammar §2.4.4 — applied type annotation :(Option Int)
    #[test]
    fn test_type_annotation_applied() {
        // :(Option Int) expr -> Annotate { Applied("Option", [Named("Int")]) }
        match parse_and_build_expr("(f :(Option Int) 42)").unwrap() {
            Expr::Apply { args, .. } => {
                assert_eq!(args.len(), 1);
                match &args[0] {
                    Expr::Annotate { annotation, .. } => match annotation {
                        TypeExpr::Applied(name, type_args) => {
                            assert_eq!(*name, "Option");
                            assert_eq!(type_args.len(), 1);
                            match &type_args[0] {
                                TypeExpr::Named(n) => assert_eq!(*n, "Int"),
                                other => panic!("expected Named(Int), got {other:?}"),
                            }
                        }
                        other => panic!("expected Applied, got {other:?}"),
                    },
                    other => panic!("expected Annotate, got {other:?}"),
                }
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.4.4 — applied type with multiple type args
    #[test]
    fn test_type_annotation_applied_multiple_args() {
        // :(Map String Int) expr
        match parse_and_build_expr("(f :(Map String Int) x)").unwrap() {
            Expr::Apply { args, .. } => {
                assert_eq!(args.len(), 1);
                match &args[0] {
                    Expr::Annotate { annotation, .. } => match annotation {
                        TypeExpr::Applied(name, type_args) => {
                            assert_eq!(*name, "Map");
                            assert_eq!(type_args.len(), 2);
                        }
                        other => panic!("expected Applied, got {other:?}"),
                    },
                    other => panic!("expected Annotate, got {other:?}"),
                }
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // -- Ring 1: Constructor pattern with field bindings --

    // spec: 02-grammar §2.5.1 — constructor pattern with single field binding
    #[test]
    fn test_constructor_pattern_with_single_binding() {
        match parse_and_build_expr("(match x [(Some v) v])").unwrap() {
            Expr::Match { arms, .. } => {
                assert_eq!(arms.len(), 1);
                match &arms[0].pattern {
                    Pattern::Constructor { name, bindings, .. } => {
                        assert_eq!(name, "Some");
                        assert_eq!(bindings.len(), 1);
                        assert_eq!(bindings[0], "v");
                    }
                    other => panic!("expected Constructor, got {other:?}"),
                }
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.5.1 — constructor pattern with multiple field bindings
    #[test]
    fn test_constructor_pattern_with_multiple_bindings() {
        match parse_and_build_expr("(match p [(Point x y) (+ x y)])").unwrap() {
            Expr::Match { arms, .. } => {
                assert_eq!(arms.len(), 1);
                match &arms[0].pattern {
                    Pattern::Constructor { name, bindings, .. } => {
                        assert_eq!(name, "Point");
                        assert_eq!(bindings.len(), 2);
                        assert_eq!(bindings[0], "x");
                        assert_eq!(bindings[1], "y");
                    }
                    other => panic!("expected Constructor, got {other:?}"),
                }
            }
            other => panic!("expected Match, got {other:?}"),
        }
    }

    // -- Ring 1: Product type with fields --

    // spec: 02-grammar §2.2.2 — product type field type expressions
    #[test]
    fn test_product_type_field_types() {
        let prog = parse_and_build_program("(deftype Point [:Int x :Int y])").unwrap();
        match &prog[0] {
            TopLevel::TypeDef {
                name,
                constructors,
                ..
            } => {
                assert_eq!(name, "Point");
                assert_eq!(constructors.len(), 1);
                let ctor = &constructors[0];
                assert_eq!(ctor.name, "Point");
                assert_eq!(ctor.fields.len(), 2);
                assert_eq!(ctor.fields[0].name, "x");
                match &ctor.fields[0].type_expr {
                    TypeExpr::Named(n) => assert_eq!(*n, "Int"),
                    other => panic!("expected Named(Int), got {other:?}"),
                }
                assert_eq!(ctor.fields[1].name, "y");
                match &ctor.fields[1].type_expr {
                    TypeExpr::Named(n) => assert_eq!(*n, "Int"),
                    other => panic!("expected Named(Int), got {other:?}"),
                }
            }
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    // -- Ring 1: Sum type with data constructors --

    // spec: 02-grammar §2.2.2 — sum type constructor details
    #[test]
    fn test_sum_type_constructor_details() {
        let prog = parse_and_build_program(
            "(deftype (Option a) None (Some [:a val]))",
        )
        .unwrap();
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
                // None: nullary
                assert_eq!(constructors[0].name, "None");
                assert!(constructors[0].fields.is_empty());
                // Some: one field
                assert_eq!(constructors[1].name, "Some");
                assert_eq!(constructors[1].fields.len(), 1);
                assert_eq!(constructors[1].fields[0].name, "val");
                match &constructors[1].fields[0].type_expr {
                    TypeExpr::TypeVar(v) => assert_eq!(*v, "a"),
                    other => panic!("expected TypeVar(a), got {other:?}"),
                }
            }
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    // -- Ring 1: REPL string literal --

    // spec: 02-grammar §2.3.1 — REPL string literal expression
    #[test]
    fn test_repl_string_literal() {
        match parse_and_build_repl("\"hello\"").unwrap() {
            ReplInput::Expr(Expr::StringLit { value, .. }) => {
                assert_eq!(value, "hello");
            }
            other => panic!("expected Expr(StringLit), got {other:?}"),
        }
    }

    // -- Ring 1: Vec literals --

    // spec: 02-grammar §2.3.9 — Vec literal with integers
    #[test]
    fn test_vec_lit_integers() {
        match parse_and_build_expr("[1 2 3]").unwrap() {
            Expr::VecLit { elements, .. } => {
                assert_eq!(elements.len(), 3);
                match &elements[0] {
                    Expr::IntLit { value, .. } => assert_eq!(*value, 1),
                    other => panic!("expected IntLit, got {other:?}"),
                }
                match &elements[2] {
                    Expr::IntLit { value, .. } => assert_eq!(*value, 3),
                    other => panic!("expected IntLit, got {other:?}"),
                }
            }
            other => panic!("expected VecLit, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.9 — empty Vec literal
    #[test]
    fn test_vec_lit_empty() {
        match parse_and_build_expr("[]").unwrap() {
            Expr::VecLit { elements, .. } => {
                assert_eq!(elements.len(), 0);
            }
            other => panic!("expected VecLit, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.9 — nested Vec literals
    #[test]
    fn test_vec_lit_nested() {
        match parse_and_build_expr("[[1] [2]]").unwrap() {
            Expr::VecLit { elements, .. } => {
                assert_eq!(elements.len(), 2);
                match &elements[0] {
                    Expr::VecLit { elements: inner, .. } => {
                        assert_eq!(inner.len(), 1);
                        match &inner[0] {
                            Expr::IntLit { value, .. } => assert_eq!(*value, 1),
                            other => panic!("expected IntLit, got {other:?}"),
                        }
                    }
                    other => panic!("expected nested VecLit, got {other:?}"),
                }
            }
            other => panic!("expected VecLit, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.9 — Vec literal with mixed element types
    #[test]
    fn test_vec_lit_mixed_types() {
        match parse_and_build_expr("[true \"hello\" 42]").unwrap() {
            Expr::VecLit { elements, .. } => {
                assert_eq!(elements.len(), 3);
                assert!(matches!(&elements[0], Expr::BoolLit { value: true, .. }));
                assert!(matches!(&elements[1], Expr::StringLit { .. }));
                assert!(matches!(&elements[2], Expr::IntLit { value: 42, .. }));
            }
            other => panic!("expected VecLit, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.8.2 — brackets in defn are param list, not VecLit
    #[test]
    fn test_defn_params_still_work() {
        // Brackets in defn position are still parameter lists, not VecLit
        match parse_and_build_program("(defn foo [x] x)").unwrap().as_slice() {
            [TopLevel::Defn(defn)] => {
                assert_eq!(defn.name, "foo");
                assert_eq!(defn.params.len(), 1);
                assert_eq!(defn.params[0], "x");
            }
            other => panic!("expected single Defn, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.9 — Vec literal in let binding value
    #[test]
    fn test_vec_lit_in_let_binding() {
        // Vec literal in a let binding value position
        match parse_and_build_expr("(let [v [1 2 3]] v)").unwrap() {
            Expr::Let { bindings, .. } => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].0, "v");
                match &bindings[0].1 {
                    Expr::VecLit { elements, .. } => assert_eq!(elements.len(), 3),
                    other => panic!("expected VecLit in binding, got {other:?}"),
                }
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.9 — Vec literal as function argument
    #[test]
    fn test_vec_lit_as_function_arg() {
        // Vec literal as argument to a function
        match parse_and_build_expr("(f [1 2])").unwrap() {
            Expr::Apply { args, .. } => {
                assert_eq!(args.len(), 1);
                match &args[0] {
                    Expr::VecLit { elements, .. } => assert_eq!(elements.len(), 2),
                    other => panic!("expected VecLit arg, got {other:?}"),
                }
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }
}
