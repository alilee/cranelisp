//! AST builder: converts S-expressions to per-form parser-stage entries.
//!
//! Post-FIXME-0156 (Wave 3a-β) the public surface is two free functions:
//!   - `build_form(&Sexp) -> Result<Vec<ParsedEntry>, CranelispError>` —
//!     dispatches on the top-level form head (`defn` / `deftype` /
//!     `deftrait` / `impl` / `defmacro`) and yields one or more
//!     transient `ParsedEntry` values for the orchestrator to feed into
//!     the cluster-atomic typecheck.
//!   - `build_expr(&Sexp) -> Result<Expr, CranelispError>` — pure
//!     structural transform of a single S-expression into an `Expr`,
//!     used by REPL eval of bare expressions and recursively by the
//!     per-shape parsers when lowering bodies.
//!
//! Per-shape parsers (`parse_defn`, `parse_deftype`, `parse_deftrait`,
//! `parse_impl`) are `pub(crate)` helpers invoked from `build_form`.
//! Pre-AST forms (`begin`, `mod`/`mod-`, `import`, `export`, `platform`)
//! are rejected — the orchestrator must peel them off before calling
//! `build_form`. Callers must expand macros before calling either
//! function.

use std::collections::HashSet;

use cranelisp_types::{ErrorLocation,
    CranelispError, ConstructorDef, Defn, DefnVariant, Expr, FieldDef, MatchArm,
    ModuleFullPath, ParsedEntry, Pattern, Sexp, Span, Symbol, SymbolRef, TopLevel,
    TraitDecl, TraitImpl, TraitMethodSig, TraitName, TraitRef, TypeExpr, TypeName,
    TypeRef, Visibility,
};

// `(trace ...)` build is mode-agnostic and works in ALL build modes including
// `--link` — the trace bodies are ordinary intrinsics resolved in every mode
// (see design/arch/tracing.md §2.5). `trace` is a root special form: its name
// is reserved and cannot be defined or bound (see `reject_reserved_binder_name`
// + spec/02-grammar.md §2.9).
// `Defn` is used by `build_impl_method` to package a method into the
// `TraitImpl.methods` list. `TopLevel` is named by `build_forms` (S81, BC §1
// invariant 9) — the form-sequence builder that pairs a leading `:Type` with
// the following top-level form and yields the bare-expression `TopLevel::Expr`
// shape int's orchestration consumes. `Program` remains unnamed by frontend
// code.

use crate::defmacro::parse_defmacro;


// ---------------------------------------------------------------------------
// Error helpers
// ---------------------------------------------------------------------------

fn parse_err(message: &str, span: Span) -> CranelispError {
    CranelispError::ParseError {
        message: message.to_string(),
        location: ErrorLocation::from_span(span),
    }
}

/// Reserved names that root special forms claim. A root special form's name
/// cannot be defined or bound by user code (spec/02-grammar.md §2.9, Principle
/// 10's two-category amendment). The set is **only** `trace` — the other root
/// special forms (`defn`, `let`, `if`, `match`, …) cannot reach a binder
/// position as a bound *name* because the parser dispatches them in head
/// position; `trace` is the case that slips through because it can appear as a
/// plain symbol in a binder slot. Per Principle 6 (complexity has a budget) the
/// set is not speculatively widened beyond what the ruling requires.
const RESERVED_BINDER_NAMES: &[&str] = &["trace"];

/// Reject `name` in a binder or definition position when it is a reserved
/// root-special-form name. Single-sourced (Principle 7) so every binder site
/// (defn/defn- names, let binders, fn/lambda + defn + method + macro params,
/// match pattern variable binders, defmacro names) enforces the identical rule.
///
/// Reference/head position is NOT a binder: `(trace expr)` stays the
/// special-form dispatch and never reaches this check. Constructor and field
/// names in patterns are not binders either — only the variables a pattern
/// introduces are.
pub(crate) fn reject_reserved_binder_name(name: &str, span: Span) -> Result<(), CranelispError> {
    if RESERVED_BINDER_NAMES.contains(&name) {
        return Err(parse_err(
            &format!("'{name}' is a reserved special-form name and cannot be defined or bound"),
            span,
        ));
    }
    Ok(())
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
    // For module-qualified names like `macros/Sexp`, the type-vs-variable
    // distinction is on the name part AFTER the final slash. `macros/Sexp`
    // is a named type (uppercase after slash); `a` or `module/a` would be
    // a type variable. The slash itself is rejected by the reader for
    // type-variable names (they're bare lowercase identifiers).
    let bare = s.rsplit('/').next().unwrap_or(s);
    bare.starts_with(|c: char| c.is_uppercase())
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
// Public API — `build_form` and `build_expr` (per FIXME 0156 + facade)
// ---------------------------------------------------------------------------

/// Build per-form [`ParsedEntry`] values from a single top-level
/// S-expression.
///
/// Dispatches on form head and returns a `Vec<ParsedEntry>` because
/// some shapes yield more than one entry per source form (notably
/// `defmacro` with multiple clauses, and `deftype` whose constructors
/// register independently via the ctor-as-Def synthesis path — see
/// crate-root preamble §"Deftype expander").
///
/// `build_form` is the **single public per-form dispatcher** for
/// top-level shapes (`defn` / `deftype` / `deftrait` / `impl` /
/// `defmacro`). Internally dispatches to per-shape `pub(crate)`
/// helpers (`parse_defn`, `parse_deftype`, `parse_deftrait`,
/// `parse_impl`, `parse_defmacro`).
///
/// # Caller contract
///
/// Bare expressions, structural decls (`mod`/`mod-`/`import`/`export`/
/// `platform`), and `begin` clusters must be handled by the orchestrator
/// BEFORE calling `build_form`:
/// - structural decls are peeled by
///   [`extract_module_declarations`](crate::extract_module_declarations);
/// - `begin` is flattened by [`flatten_begin`](crate::flatten_begin);
/// - bare expressions go through [`build_expr`].
///
/// `build_form` rejects these head shapes directly with a diagnostic
/// message to surface the missing orchestration step early. Macros must
/// be expanded via `expand` before calling `build_form`
/// — unexpanded macro calls become silent generic applications and fail
/// later with confusing diagnostics.
///
/// See `design/frontend/wave-3a-build-form.md` §2.3 for the detailed
/// design.
pub fn build_form(sexp: &Sexp) -> Result<Vec<ParsedEntry>, CranelispError> {
    let (children, span) = match sexp {
        Sexp::List(c, s) if !c.is_empty() => (c.as_slice(), *s),
        Sexp::Comment(_, span) => {
            return Err(parse_err(
                "build_form: comment forms must be filtered by the caller",
                *span,
            ));
        }
        _ => {
            return Err(parse_err(
                "build_form expects a top-level form (list with a head symbol)",
                sexp.span(),
            ));
        }
    };

    let (head, head_span) = match &children[0] {
        Sexp::Symbol(s, sp) => (s.as_str(), *sp),
        _ => {
            return Err(parse_err(
                "build_form: top-level form head must be a symbol",
                children[0].span(),
            ));
        }
    };

    // Pre-AST forms are not accepted by `build_form`. begin / module-decl
    // forms are the orchestrator's responsibility; defmacro is dispatched
    // separately below (it's a top-level form vocabulary entry, not pre-AST).
    match head {
        "begin" => {
            return Err(parse_err(
                "build_form: `(begin …)` must be flattened by the orchestrator before per-form dispatch",
                head_span,
            ));
        }
        "mod" | "mod-" | "import" | "export" | "platform" => {
            return Err(parse_err(
                "build_form: structural declarations must be peeled by `extract_module_declarations` before per-form dispatch",
                head_span,
            ));
        }
        _ => {}
    }

    // defmacro / defmacro-: package as ParsedEntry::Macro.
    if head == "defmacro" || head == "defmacro-" {
        let info = parse_defmacro(sexp)?;
        return Ok(vec![ParsedEntry::Macro { info }]);
    }

    // impl: no private variant.
    if head == "impl" {
        return parse_impl(children, span).map(|e| vec![e]);
    }

    // defn / deftype / deftrait (with visibility suffix `-`).
    if let Some((base, vis)) = parse_def_visibility(head) {
        return match base {
            "defn" => parse_defn(children, span, vis).map(|e| vec![e]),
            "deftype" => parse_deftype(children, span, vis),
            "deftrait" => parse_deftrait(children, span, vis).map(|e| vec![e]),
            _ => unreachable!("invariant: parse_def_visibility returns known base"),
        };
    }

    Err(parse_err(
        &format!("unknown top-level form: `{head}`"),
        head_span,
    ))
}

/// Build a sequence of top-level forms, performing `:Type` annotation pairing
/// across the sequence.
///
/// This is the **form-sequence boundary** (S81, BC §1 invariant 9): the
/// single seam where the `:Type`-binds-the-following-form pairing is applied
/// at the TOP LEVEL. A leading `:Type` sexp (a `colon_prefix` atom, or the
/// bare `:` followed by a compound type form) pairs with the immediately
/// following form into an `Expr::Annotate`, surfaced as a `TopLevel::Expr`.
/// Every other sexp is delegated per-form:
/// - a top-level form (`defn`/`deftype`/`deftrait`/`impl`/`defmacro` and their
///   `-` variants) goes through [`build_form`], each resulting `ParsedEntry`
///   converted to its `TopLevel` shape; `Macro` and `Constructor` entries are
///   dropped (handled by the macro pipeline and ADT-constructor synthesis
///   respectively, outside the `TopLevel` typecheck dispatch — matching the
///   orchestrator's prior `build_program_compat` behaviour);
/// - any other sexp is a bare expression, built via [`build_expr`] and wrapped
///   as `TopLevel::Expr`.
///
/// A trailing `:Type` with no following form is a parse error
/// (`annotation missing expression`).
///
/// # Caller contract
///
/// `sexps` MUST already be begin-flattened and have structural declarations
/// (`mod`/`mod-`/`import`/`export`/`platform`) peeled off — those are the
/// orchestrator's responsibility (via `flatten_begin` /
/// [`extract_module_declarations`](crate::extract_module_declarations)), the
/// same precondition [`build_form`] documents. Macros MUST be expanded before
/// calling `build_forms`.
///
/// This is the entry the orchestrator (`int`) calls in place of driving a
/// per-sexp `build_form`/`build_expr` loop itself, so that top-level `:Type`
/// pairing lives ENTIRELY in the frontend — the single owning seam (BC §1
/// invariant 9; Principle 7).
pub fn build_forms(sexps: &[Sexp]) -> Result<Vec<TopLevel>, CranelispError> {
    let mut out: Vec<TopLevel> = Vec::with_capacity(sexps.len());
    let mut i = 0;
    while i < sexps.len() {
        // A leading `:Type` pairs with the FOLLOWING form (BC §1 invariant 9).
        // `build_one_expr_at` performs the pairing over the sexp slice; when
        // `sexps[i]` is not an annotation it builds exactly like `build_expr`,
        // so the non-annotated path below handles the per-form dispatch that
        // `build_one_expr_at`'s plain-`build_expr` arm cannot (it has no
        // knowledge of top-level forms).
        if try_consume_annotation(sexps, i).is_some() {
            let (expr, consumed) = build_one_expr_at(sexps, i)?;
            out.push(TopLevel::Expr(expr));
            i += consumed;
            continue;
        }

        let sexp = &sexps[i];
        if matches!(sexp, Sexp::Comment(_, _)) {
            i += 1;
            continue;
        }

        if is_top_level_form_sexp(sexp) {
            for entry in build_form(sexp)? {
                if let Some(tl) = parsed_entry_to_top_level(entry) {
                    out.push(tl);
                }
            }
        } else {
            out.push(TopLevel::Expr(build_expr(sexp)?));
        }
        i += 1;
    }
    Ok(out)
}

/// Detect a top-level form head (`defn`/`deftype`/`deftrait`/`impl`/`defmacro`
/// and their `-` variants) so [`build_forms`] knows whether to route a sexp to
/// [`build_form`] or treat it as a bare expression. Mirrors the orchestrator's
/// prior `is_top_level_form` heuristic.
fn is_top_level_form_sexp(sexp: &Sexp) -> bool {
    if let Sexp::List(children, _) = sexp
        && let Some(Sexp::Symbol(head, _)) = children.first()
    {
        return matches!(
            head.as_str(),
            "defn" | "defn-" | "deftype" | "deftype-" | "deftrait" | "deftrait-"
                | "impl" | "defmacro" | "defmacro-"
        );
    }
    false
}

/// Convert a `ParsedEntry` to its `TopLevel` shape for [`build_forms`].
/// `Macro` and `Constructor` entries return `None` — they are handled by the
/// macro pipeline and ADT-constructor synthesis respectively, not by the
/// `TopLevel` typecheck dispatch (matching the orchestrator's prior
/// `build_program_compat`).
fn parsed_entry_to_top_level(entry: ParsedEntry) -> Option<TopLevel> {
    match entry {
        ParsedEntry::Def { name, variants, visibility, docstring, span } => {
            Some(TopLevel::Defn(Defn { name, docstring, variants, visibility, span }))
        }
        ParsedEntry::TypeDef { name, type_params, constructors, visibility, docstring, span } => {
            // `TopLevel::TypeDef.type_params` is `Vec<Symbol>` — pass through
            // (both `ParsedEntry::TypeDef` and `TopLevel::TypeDef` carry
            // `Vec<Symbol>` per the S70 Phase 3 newtype fix).
            Some(TopLevel::TypeDef {
                name,
                docstring,
                type_params,
                constructors,
                visibility,
                span,
            })
        }
        ParsedEntry::TraitDecl { decl } => Some(TopLevel::TraitDecl(decl)),
        ParsedEntry::TraitImpl { impl_ } => Some(TopLevel::TraitImpl(impl_)),
        ParsedEntry::Macro { .. } | ParsedEntry::Constructor { .. } => None,
        // `ParsedEntry` is `#[non_exhaustive]`; any future parser-only entry
        // not surfaced as a `TopLevel` is dropped here, consistent with the
        // Macro/Constructor disposition.
        _ => None,
    }
}

// `build_expr` is the public per-form expression builder (see the function
// definition further below — promoted from internal helper to `pub` per
// FIXME 0156 + the Wave 3a facade).

// ---------------------------------------------------------------------------
// Rejection helpers
// ---------------------------------------------------------------------------

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
// Per-shape parsers (pub(crate) helpers for build_form)
// ---------------------------------------------------------------------------

pub(crate) fn parse_defn(
    children: &[Sexp],
    span: Span,
    visibility: Visibility,
) -> Result<ParsedEntry, CranelispError> {
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
    let variants = match &children[next] {
        Sexp::Bracket(..) => {
            let params = build_annotated_params(&children[next])?;
            let body_start = next + 1;
            if body_start >= children.len() {
                return Err(parse_err("defn missing body", span));
            }
            let (body, consumed) = build_one_expr_at(children, body_start)?;
            if body_start + consumed != children.len() {
                return Err(parse_err("defn has extra forms after body", span));
            }
            vec![DefnVariant {
                params,
                body,
                span,
            }]
        }
        Sexp::List(..) => {
            children[next..]
                .iter()
                .map(build_defn_variant)
                .collect::<Result<Vec<_>, _>>()?
        }
        _ => return Err(parse_err(
            "defn: expected params [...] or variant (...)",
            children[next].span(),
        )),
    };

    Ok(ParsedEntry::Def {
        name,
        variants,
        visibility,
        docstring,
        span,
    })
}

fn get_defn_name(sexp: &Sexp) -> Result<Symbol, CranelispError> {
    match sexp {
        Sexp::Symbol(name, span) => {
            reject_reserved_binder_name(name, *span)?;
            Ok(name.as_str().into())
        }
        _ => Err(parse_err("expected function name", sexp.span())),
    }
}

fn build_defn_variant(sexp: &Sexp) -> Result<DefnVariant, CranelispError> {
    let (children, span) = expect_list(sexp)?;
    if children.len() != 2 {
        return Err(parse_err("defn variant requires params and body", span));
    }
    let params = build_annotated_params(&children[0])?;
    let body = build_expr(&children[1])?;
    Ok(DefnVariant {
        params,
        body,
        span,
    })
}

// ---------------------------------------------------------------------------
// deftype builder
// ---------------------------------------------------------------------------

pub(crate) fn parse_deftype(
    children: &[Sexp],
    span: Span,
    visibility: Visibility,
) -> Result<Vec<ParsedEntry>, CranelispError> {
    // (deftype Head "doc"? [fields])              -- product
    // (deftype Head "doc"? Ctor1 (Ctor2 [f]) ...) -- sum/enum
    //
    // Yields one ParsedEntry::TypeDef followed by one ParsedEntry::Constructor
    // per declared variant in source-declaration order.
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
                name: Symbol::from(type_name.as_ref()),
                docstring: None,
                fields,
                span,
            };
            desugar_type_def(type_name.as_ref(), &type_params, &[ctor])
        }
        _ => {
            let ctors = children[next..]
                .iter()
                .map(build_constructor_def)
                .collect::<Result<Vec<_>, _>>()?;
            desugar_type_def(type_name.as_ref(), &type_params, &ctors)
        }
    };

    // ParsedEntry::TypeDef carries type_params as `Vec<Symbol>` per the
    // canonical types-crate shape (S70 Phase 3 step 2A); pass through.
    let mut out = Vec::with_capacity(constructors.len() + 1);
    out.push(ParsedEntry::TypeDef {
        name: type_name.clone(),
        type_params: resolved_params.clone(),
        constructors: constructors.clone(),
        visibility,
        docstring,
        span,
    });
    for ctor in &constructors {
        out.push(ParsedEntry::Constructor {
            name: ctor.name.clone(),
            of_type: type_name.clone(),
            fields: ctor.fields.clone(),
            span: ctor.span,
        });
    }
    Ok(out)
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
            let (name, name_span) = expect_symbol(&items[name_pos])?;
            fields.push(FieldDef {
                name: name.into(),
                type_expr: te,
                span: name_span,
            });
            i = name_pos + 1;
        } else {
            // Bare name -- shortcut syntax (fresh type var)
            let (name, name_span) = expect_symbol(&items[i])?;
            fields.push(FieldDef {
                name: name.into(),
                type_expr: TypeExpr::TypeVar("".into()),
                span: name_span,
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
                                field_to_var.iter().find(|(fname, _)| fname.as_str() == f.name.as_ref())
                            {
                                var.clone()
                            } else {
                                // Assign next sequential letter
                                let letter = sequential_type_var(inferred_params.len());
                                let var: Symbol = letter.into();
                                field_to_var.push((f.name.as_ref().to_string(), var.clone()));
                                inferred_params.push(var.clone());
                                var
                            };
                            FieldDef {
                                name: f.name.clone(),
                                type_expr: TypeExpr::TypeVar(var_name),
                                span: f.span,
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

pub(crate) fn parse_deftrait(
    children: &[Sexp],
    span: Span,
    visibility: Visibility,
) -> Result<ParsedEntry, CranelispError> {
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

    Ok(ParsedEntry::TraitDecl {
        decl: TraitDecl {
            name: trait_name,
            docstring,
            type_params,
            methods,
            visibility,
            span,
        },
    })
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

    expect_bracket(&children[next])?;
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

    // Both required and default methods carry named params per spec §5.3
    // EBNF (`param = ':' type_expr symbol | symbol`). Bare names default
    // to `TypeExpr::SelfType` per spec §5.3.1; annotated names use the
    // annotation. Fused `params: Vec<(Symbol, TypeExpr)>` per S69 Sub 26
    // (Principle 18 — the prior `default_param_names` parallel-vec carried
    // an unenforced lockstep with `default_body`).
    let annotated = build_annotated_params(&children[next])?;
    let params: Vec<(Symbol, TypeExpr)> = annotated
        .into_iter()
        .map(|(name, annotation)| (name, annotation.unwrap_or(TypeExpr::SelfType)))
        .collect();

    // Detect HKT param index: find which **parameter position** uses the
    // constructor variable (e.g., `(f a)` where f is the HKT var). With the
    // fused param shape (S69 Sub 26), the index counts parsed params, not
    // raw bracket items (annotations are not separate items now). The HKT
    // variable manifests as a `TypeExpr::Applied(TypeRef { name == hkt_var,
    // module: None }, _)` annotation per spec §5.3.2.
    let hkt_param_index = if let Some(hkt_var) = hkt_param_name {
        params.iter().position(|(_, ty)| {
            matches!(ty, TypeExpr::Applied(head, _)
                if head.module.is_none() && head.name.as_ref() == hkt_var.as_ref())
        })
    } else {
        None
    };

    let default_body = if has_default_body {
        // Default body lowered to Expr per S69 Sub 26 — building the AST at
        // trait-decl time catches structural errors in special forms (`let`,
        // `if`, `match`, …) immediately, rather than per-impl.
        Some(build_expr(&children[ret_pos + 1])?)
    } else {
        None
    };

    Ok(TraitMethodSig {
        name: name.into(),
        docstring,
        params,
        ret_type,
        span,
        hkt_param_index,
        default_body,
    })
}

// ---------------------------------------------------------------------------
// impl builder
// ---------------------------------------------------------------------------

pub(crate) fn parse_impl(
    children: &[Sexp],
    span: Span,
) -> Result<ParsedEntry, CranelispError> {
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

    let (target, type_constraints) = build_impl_target(&children[2])?;

    let methods = children[3..]
        .iter()
        .map(build_impl_method)
        .collect::<Result<Vec<_>, _>>()?;

    Ok(ParsedEntry::TraitImpl {
        impl_: TraitImpl {
            trait_name: TraitRef::new(None, TraitName::from(trait_name)),
            target,
            type_constraints,
            methods,
            span,
        },
    })
}

/// Parsed impl target: (target type expression, trait constraints).
///
/// Per S69 Submission 27 (`TraitImpl.target: TypeExpr` unified):
/// - `Type` lowers to `TypeExpr::Named(TypeRef::new(None, TypeName::from(name)))`
/// - `(Type :Constraint var ...)` / `(Type var ...)` lowers to
///   `TypeExpr::Applied(TypeRef::new(None, head), args)` where each
///   bare-symbol arg becomes `TypeExpr::TypeVar(name)` (or, if uppercase,
///   `TypeExpr::Named(...)`); constraints carry on the side.
type ImplTarget = (TypeExpr, Vec<(Symbol, TraitRef)>);

/// Parse an impl target. Three forms:
///   - `Type` — concrete: bare type name
///   - `(Type :Constraint var ...)` — polymorphic ADT with constraints
///   - `(Type var ...)` — parameterized concrete (e.g., `(Option Int)`)
fn build_impl_target(
    sexp: &Sexp,
) -> Result<ImplTarget, CranelispError> {
    match sexp {
        Sexp::Symbol(name, _) if is_uppercase_start(name) => {
            let target = TypeExpr::Named(TypeRef::new(None, TypeName::from(name.as_str())));
            Ok((target, vec![]))
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

            let mut type_args: Vec<TypeExpr> = Vec::new();
            let mut type_constraints: Vec<(Symbol, TraitRef)> = Vec::new();
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
                        type_args.push(TypeExpr::TypeVar(Symbol::from(var_name)));
                        type_constraints.push((
                            Symbol::from(var_name),
                            TraitRef::new(None, TraitName::from(constraint_name)),
                        ));
                        i += 1;
                    } else {
                        // Bare type arg — uppercase becomes Named, lowercase TypeVar
                        let arg = if is_uppercase_start(s) {
                            TypeExpr::Named(TypeRef::new(None, TypeName::from(s.as_str())))
                        } else {
                            TypeExpr::TypeVar(Symbol::from(s.as_str()))
                        };
                        type_args.push(arg);
                        i += 1;
                    }
                } else {
                    return Err(parse_err(
                        "expected symbol in impl target",
                        children[i].span(),
                    ));
                }
            }

            let target = TypeExpr::Applied(
                TypeRef::new(None, TypeName::from(type_name)),
                type_args,
            );
            Ok((target, type_constraints))
        }
        _ => Err(parse_err("expected impl target type", sexp.span())),
    }
}

/// Parse a method definition inside an impl block.
/// (defn method_name [params] body)
fn build_impl_method(sexp: &Sexp) -> Result<Defn, CranelispError> {
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
    let params = build_annotated_params(&children[2])?;
    let body = build_expr(&children[3])?;

    Ok(Defn {
        name,
        docstring: None,
        variants: vec![DefnVariant {
            params,
            body,
            span,
        }],
        visibility: Visibility::Public,
        span,
    })
}

// ---------------------------------------------------------------------------
// Expression builders
// ---------------------------------------------------------------------------

/// Build an [`Expr`] from a single S-expression.
///
/// Pure structural transform — no symbol-tables lookup, no gap returns.
/// One of the four free-function entries of the frontend boundary (see
/// crate-root preamble). Used by the REPL eval path for bare-expression
/// evals and recursively by the per-shape parsers when lowering bodies.
///
/// # Caller contract
///
/// Callers must expand macros via `expand` before
/// calling `build_expr`. Unexpanded macro calls become silent generic
/// applications and fail later with confusing diagnostics.
///
/// `build_expr` is mode-agnostic. `(trace ...)` works in ALL build modes
/// including `--link` — the trace bodies are ordinary intrinsics resolved
/// in every mode (see `design/arch/tracing.md` §2.5); no frontend pre-pass
/// check is needed.
pub fn build_expr(sexp: &Sexp) -> Result<Expr, CranelispError> {
    match sexp {
        Sexp::Int(v, span) => Ok(Expr::IntLit {
            value: *v,
            span: *span,
            inferred_type: None,
        }),
        Sexp::Float(v, span) => Ok(Expr::FloatLit {
            value: *v,
            span: *span,
            inferred_type: None,
        }),
        Sexp::Bool(v, span) => Ok(Expr::BoolLit {
            value: *v,
            span: *span,
            inferred_type: None,
        }),
        Sexp::Str(v, span) => Ok(Expr::StringLit {
            value: v.clone(),
            span: *span,
            inferred_type: None,
        }),
        Sexp::Symbol(name, span) => {
            // A `colon_prefix` token (`:Int`, `:a`, `:Num`) is an annotation
            // introducer, never a standalone variable reference (spec §1.4.5
            // normative note; §2.3.8; BC §1 invariant 9). A bare `:Type` with
            // no following form to bind is a parse error. A bare `:` (the
            // field separator) is not an annotation introducer here — it is
            // only meaningful in binding/field positions, so it also has
            // nothing to bind in expression position.
            if name.starts_with(':') && name.len() > 1 {
                return Err(parse_err("annotation missing expression", *span));
            }
            reject_non_ring0_symbol(name, *span)?;
            Ok(Expr::Var {
                name: name.as_str().into(),
                span: *span,
                inferred_type: None,
                resolved_call: None,
            })
        }
        Sexp::List(children, span) => build_list_expr(children, *span),
        Sexp::Bracket(children, span) => build_vec_lit(children, *span),
        Sexp::Comment(_, span) => Err(CranelispError::ParseError {
            message: "unexpected comment in expression position".to_string(),
            location: ErrorLocation::from_span(*span),
        }),
    }
}

fn build_list_expr(
    children: &[Sexp],
    span: Span,
) -> Result<Expr, CranelispError> {
    if children.is_empty() {
        return Err(parse_err("empty application", span));
    }

    // Check if first child is a keyword symbol
    if let Sexp::Symbol(head, head_span) = &children[0] {
        match head.as_str() {
            "let" => return build_let(children, span),
            "if" => return build_if(children, span),
            "fn" | "lambda" => return build_fn(children, span),
            "match" => return build_match(children, span),
            // Reader-macro forms — should be handled by the expander before reaching AST builder
            "quote" => {
                return Err(parse_err("unexpected quote form — should have been expanded", *head_span))
            }
            "quasiquote" => {
                return Err(parse_err("unexpected quasiquote form — should have been expanded", *head_span))
            }
            "unquote" => {
                return Err(parse_err("unexpected unquote form — should have been expanded", *head_span))
            }
            "unquote-splicing" => {
                return Err(parse_err(
                    "unexpected unquote-splicing form — should have been expanded",
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
            "trace" => return build_trace(children, span),
            // `discover-tests` and `run-test` are NOT special forms. Under the
            // settled test-discovery design (design/arch/test-discovery.md
            // §"Frontend — nothing (zero special-casing)"), `discover-tests` is
            // an ordinary `primitives` PrimitiveExtern and `run-test` is retired
            // entirely. Both build as plain `Expr::Apply` here and resolve
            // through the symbol table like any other name.
            // "vec" is handled by the prelude vec macro — no AST intercept needed.
            "par-let" => {
                return Err(parse_err("par-let not yet supported (Ring 4)", *head_span))
            }
            // If an unexpanded macro call reaches here, it will be treated as a
            // regular function application and fail at typecheck. All callers
            // should expand macros before calling the AST builder.
            _ => {}
        }
    }

    // Generic Apply
    build_apply(children, span)
}

// ---------------------------------------------------------------------------
// trace expression
// ---------------------------------------------------------------------------

fn build_trace(
    children: &[Sexp],
    span: Span,
) -> Result<Expr, CranelispError> {
    // (trace expr)
    //
    // `trace` is a root special form (Principle 10's two-category amendment;
    // design/arch/tracing.md §3.1) — recognised here in head position, always
    // available with no import and no module path. Build is mode-agnostic and
    // `(trace ...)` works in ALL build modes including `--link`: the 12 trace
    // bodies are ordinary intrinsics published through `intrinsics_table()` and
    // resolve everywhere (JIT symbol registration for REPL/`--run`, the
    // `cranelisp-intrinsics` archive for `--link`). See tracing.md §2.5. The
    // earlier `--link` missing-symbol rejection is retracted (D40 trace-half
    // retracted 2026-06-04).
    //
    // The reserved-name enforcement that rejects `trace` in binder/definition
    // positions lives at the binder sites (`reject_reserved_binder_name`), not
    // here — this is the legitimate head/reference position.
    //
    // Quoted occurrences (`'(trace x)`, `` `(trace x) ``) are desugared by the
    // expander into `Sexp` constructor calls before reaching this builder, so
    // they appear as `Expr::Apply` to those constructors (not `Expr::Trace`).
    if children.len() != 2 {
        return Err(parse_err(
            "trace requires exactly one expression",
            span,
        ));
    }
    let body = build_expr(&children[1])?;
    Ok(Expr::Trace {
        modules: vec![],
        body: Box::new(body),
        span,
        inferred_type: None,
    })
}

fn build_apply(
    children: &[Sexp],
    span: Span,
) -> Result<Expr, CranelispError> {
    // A leading `:Type` inside a parenthesized list annotates the SINGLE
    // following element — it is NOT the application callee and NOT an
    // annotation of the whole list (spec §2.3.8; BC §1 invariant 9). The
    // reader binds `:Type` to the next form, yielding a one-element list whose
    // sole element is that `Annotate`; the list is then the ordinary
    // application of that one annotated element. We therefore build the head
    // element through the same annotation-pairing primitive (`build_one_expr_at`)
    // used for arguments — when the head is not an annotation it builds exactly
    // like `build_expr`, so the common `(f arg ...)` shape is unchanged.
    let (callee, consumed) = build_one_expr_at(children, 0)?;
    let args = build_args_with_annotations(&children[consumed..])?;
    Ok(Expr::Apply {
        callee: Box::new(callee),
        args,
        span,
        resolved_call: None,
        inferred_type: None,
    })
}

// ---------------------------------------------------------------------------
// let expression
// ---------------------------------------------------------------------------

fn build_let(
    children: &[Sexp],
    span: Span,
) -> Result<Expr, CranelispError> {
    // (let [name val name val ...] body)
    if children.len() != 3 {
        return Err(parse_err("let requires bindings and body", span));
    }
    let (bracket_items, _) = expect_bracket(&children[1])?;
    let bindings = build_let_bindings(bracket_items)?;
    let body = build_expr(&children[2])?;
    Ok(Expr::Let {
        bindings,
        body: Box::new(body),
        span,
        inferred_type: None,
    })
}

fn build_let_bindings(
    items: &[Sexp],
) -> Result<Vec<(cranelisp_types::Symbol, Expr)>, CranelispError> {
    let mut bindings = Vec::new();
    let mut i = 0;
    while i < items.len() {
        let (name, name_span) = expect_symbol(&items[i])?;
        reject_reserved_binder_name(name, name_span)?;
        i += 1;
        if i >= items.len() {
            return Err(parse_err("let binding missing value", items[i - 1].span()));
        }
        let (value, consumed) = build_one_expr_at(items, i)?;
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
) -> Result<Expr, CranelispError> {
    // (if cond then else)
    if children.len() != 4 {
        return Err(parse_err(
            "if requires condition, then, and else branches",
            span,
        ));
    }
    let cond = build_expr(&children[1])?;
    let then_branch = build_expr(&children[2])?;
    let else_branch = build_expr(&children[3])?;
    Ok(Expr::If {
        cond: Box::new(cond),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
        span,
        inferred_type: None,
    })
}

// ---------------------------------------------------------------------------
// fn / lambda expression
// ---------------------------------------------------------------------------

fn build_fn(
    children: &[Sexp],
    span: Span,
) -> Result<Expr, CranelispError> {
    // (fn [params] body) or (lambda [params] body)
    if children.len() != 3 {
        return Err(parse_err("fn requires param list and body", span));
    }
    let params = build_annotated_params(&children[1])?;
    let body = build_expr(&children[2])?;
    Ok(Expr::Lambda {
        params,
        body: Box::new(body),
        span,
        inferred_type: None,
    })
}

// ---------------------------------------------------------------------------
// match expression
// ---------------------------------------------------------------------------

fn build_match(
    children: &[Sexp],
    span: Span,
) -> Result<Expr, CranelispError> {
    // (match scrutinee [pattern body pattern body ...])
    if children.len() != 3 {
        return Err(parse_err("match requires scrutinee and arms", span));
    }
    let scrutinee = build_expr(&children[1])?;
    let (bracket_items, bracket_span) = expect_bracket(&children[2])?;
    if bracket_items.len() % 2 != 0 {
        return Err(parse_err(
            "match arms must have an even number of elements (pattern body pairs)",
            bracket_span,
        ));
    }
    let arms = build_match_arms(bracket_items)?;
    Ok(Expr::Match {
        scrutinee: Box::new(scrutinee),
        arms,
        span,
        compiler_generated: false,
        inferred_type: None,
    })
}

fn build_match_arms(
    items: &[Sexp],
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
        let body = build_expr(&items[i])?;
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
                    name: SymbolRef::new(None, Symbol::from(name.as_str())),
                    bindings: vec![],
                    span: *span,
                })
            } else {
                // A bare lowercase pattern symbol is a variable binder.
                reject_reserved_binder_name(name, *span)?;
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
            // children[0] is the constructor name (not a binder). The remaining
            // symbols are variable binders the pattern introduces.
            let bindings = children[1..]
                .iter()
                .map(|s| {
                    let (n, n_span) = expect_symbol(s)?;
                    reject_reserved_binder_name(n, n_span)?;
                    Ok(n.into())
                })
                .collect::<Result<Vec<_>, CranelispError>>()?;
            Ok(Pattern::Constructor {
                name: SymbolRef::new(None, Symbol::from(name)),
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
) -> Result<Expr, CranelispError> {
    let elements = build_args_with_annotations(children)?;
    Ok(Expr::VecLit { elements, span, inferred_type: None })
}

// ---------------------------------------------------------------------------
// Trace
// ---------------------------------------------------------------------------

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

/// Split an as-written type name `module/Name` into its `(module, name)`
/// parts for a `TypeRef`, mirroring the trait-ref split in
/// [`type_expr_to_trait_ref`] and `split_qualified` in
/// `cranelisp_types::resolve`.
///
/// A qualified name (`t/Box`, `a.b/Box`) splits at the LAST `/` — module is
/// everything before, name is everything after — only when BOTH halves are
/// non-empty. A bare `Name` (no `/`), or any name that fails the non-empty
/// guard, stays `module: None`. This is the frontend half of FIXME 0362: a
/// self-qualified type reference `:t/Box` written inside module `t` must
/// arrive at typecheck as `TypeRef { module: Some("t"), name: "Box" }`, not
/// as the un-split `TypeRef { module: None, name: "t/Box" }`.
fn type_ref_from_name(name: &str) -> TypeRef {
    match name.rsplit_once('/') {
        Some((m, n)) if !m.is_empty() && !n.is_empty() => {
            TypeRef::new(Some(ModuleFullPath::from(m)), TypeName::from(n))
        }
        _ => TypeRef::new(None, TypeName::from(name)),
    }
}

fn parse_annotation_name(name: &str) -> TypeExpr {
    if name == "self" {
        TypeExpr::SelfType
    } else if is_uppercase_start(name) {
        TypeExpr::Named(type_ref_from_name(name))
    } else {
        TypeExpr::TypeVar(name.into())
    }
}

/// Build one expression from a slice at `pos`, consuming annotation if present.
/// Returns `(expr, items_consumed)`.
fn build_one_expr_at(
    items: &[Sexp],
    pos: usize,
) -> Result<(Expr, usize), CranelispError> {
    if let Some((annotation, consumed)) = try_consume_annotation(items, pos) {
        let expr_pos = pos + consumed;
        if expr_pos >= items.len() {
            return Err(parse_err("annotation missing expression", items[pos].span()));
        }
        let inner = build_expr(&items[expr_pos])?;
        let span = Span::new(items[pos].span().start, items[expr_pos].span().end);
        Ok((
            Expr::Annotate {
                annotation,
                expr: Box::new(inner),
                span,
                inferred_type: None,
            },
            consumed + 1,
        ))
    } else {
        let expr = build_expr(&items[pos])?;
        Ok((expr, 1))
    }
}

/// Build argument list, handling inline annotations (`:Type expr` -> `Annotate`).
fn build_args_with_annotations(
    items: &[Sexp],
) -> Result<Vec<Expr>, CranelispError> {
    let mut args = Vec::new();
    let mut i = 0;
    while i < items.len() {
        let (expr, consumed) = build_one_expr_at(items, i)?;
        args.push(expr);
        i += consumed;
    }
    Ok(args)
}

// ---------------------------------------------------------------------------
// Parameter list builders
// ---------------------------------------------------------------------------

/// Build annotated parameter list from a Bracket sexp.
///
/// Returns the fused `Vec<(Symbol, Option<TypeExpr>)>` shape per S69
/// Submission 23 / 24 (Principle 18 — enforce invariants structurally;
/// the prior parallel-vec `(Vec<Symbol>, Vec<Option<TypeExpr>>)` shape
/// carried an unenforced `len()` lockstep invariant).
fn build_annotated_params(
    sexp: &Sexp,
) -> Result<Vec<(Symbol, Option<TypeExpr>)>, CranelispError> {
    let (items, _) = expect_bracket(sexp)?;
    let mut params: Vec<(Symbol, Option<TypeExpr>)> = Vec::new();
    let mut i = 0;

    while i < items.len() {
        if let Some((te, consumed)) = try_consume_annotation(items, i) {
            // Accumulate the RUN of consecutive annotations preceding the binder
            // name. A `:Type`/`:Trait` annotation is reader-macro-like — it binds
            // the immediately-following form (FIXME 0341,
            // `memory/annotation-reader-macro-binds-following-form.md`), so a run
            // of stacked annotations all attach to the one binder that terminates
            // the run. The single-annotation case is the run-of-length-1.
            let mut run: Vec<TypeExpr> = vec![te];
            let mut name_pos = i + consumed;
            while let Some((te, consumed)) = try_consume_annotation(items, name_pos) {
                run.push(te);
                name_pos += consumed;
            }
            if name_pos >= items.len() {
                return Err(parse_err(
                    "annotation missing parameter name",
                    items[i].span(),
                ));
            }
            let (name, name_span) = expect_symbol(&items[name_pos])?;
            reject_reserved_binder_name(name, name_span)?;
            params.push((name.into(), Some(annotation_run_carrier(run))));
            i = name_pos + 1;
        } else {
            let (name, name_span) = expect_symbol(&items[i])?;
            reject_reserved_binder_name(name, name_span)?;
            params.push((name.into(), None));
            i += 1;
        }
    }

    // Check for duplicate parameter names (spec §5.1.1 — defn params must be distinct,
    // except `_` which is a discard parameter exempt from the uniqueness check)
    let mut seen = HashSet::new();
    for (name, _) in &params {
        if name == "_" {
            continue;
        }
        if !seen.insert(name.as_ref()) {
            return Err(parse_err(
                &format!("duplicate parameter name '{}'", name),
                sexp.span(),
            ));
        }
    }

    Ok(params)
}

/// Choose the carrier `TypeExpr` for an accumulated run of param annotations
/// (FIXME 0341 / 0346).
///
/// A run of length 1 is ambiguous between a concrete-type annotation
/// (`:Int x`) and a single trait bound (`:Eq a`); it is left as the resolved
/// `TypeExpr` so the existing concrete-type path is unchanged and typecheck's
/// try-type-then-trait resolution (spec §3.9.3) disambiguates downstream.
///
/// A run of length N>1 (`:Eq :Display a`) can ONLY be a set of trait bounds —
/// you cannot stack concrete types onto one binder — so it is carried as
/// `TypeExpr::Bounds([..])`, the shape typecheck's `resolve_bound_param`
/// consumes (FIXME 0346 ruled the `Bounds` variant the carrier).
fn annotation_run_carrier(mut run: Vec<TypeExpr>) -> TypeExpr {
    debug_assert!(!run.is_empty(), "annotation run must be non-empty");
    if run.len() == 1 {
        run.pop().expect("run of length 1 has one element")
    } else {
        TypeExpr::Bounds(run.into_iter().map(type_expr_to_trait_ref).collect())
    }
}

/// Convert a parsed annotation `TypeExpr` to the `TraitRef` carried by
/// `TypeExpr::Bounds`. Trait annotations parse as `Named`/`Applied` (uppercase
/// `:Eq`, qualified `:fmt/Display`) or — defensively — `TypeVar`. The
/// as-written qualification is preserved for typecheck to resolve.
fn type_expr_to_trait_ref(te: TypeExpr) -> TraitRef {
    let (module, name): (Option<&str>, &str) = match &te {
        TypeExpr::Named(r) | TypeExpr::Applied(r, _) => {
            (r.module.as_deref(), r.name.as_ref())
        }
        TypeExpr::TypeVar(s) => (None, s.as_ref()),
        TypeExpr::SelfType => (None, "Self"),
        TypeExpr::FnType(..) | TypeExpr::Bounds(_) => (None, ""),
    };
    // A name may carry as-written qualification `module/Trait` (parsed into the
    // `TypeName` whole); split it onto the `TraitRef`'s optional module.
    match name.rsplit_once('/') {
        Some((m, n)) if !m.is_empty() && !n.is_empty() => TraitRef::new(
            Some(ModuleFullPath::from(m)),
            TraitName::from(n),
        ),
        _ => {
            let module = module.map(ModuleFullPath::from);
            TraitRef::new(module, TraitName::from(name))
        }
    }
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
                Ok(TypeExpr::Named(type_ref_from_name(name.as_str())))
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
        return Ok(TypeExpr::Applied(type_ref_from_name(head.as_str()), args));
    }
    Err(parse_err("invalid type expression", span))
}

/// Parse a single type-expression S-expression into the canonical
/// `TypeExpr` AST shape.
///
/// Bounded: **string in, one `TypeExpr` out**. The source must be a single
/// type-expression form (a bare type name, a `(Fn [..] R)`, or an applied
/// `(Name arg..)`) — NOT a program form, NOT a sequence. More than one
/// form, or zero forms, is a `CranelispError`.
///
/// Returns `TypeExpr` (syntactic), NOT `Type` (resolution is typecheck's
/// `check_type_expr`). Reuses the existing `parse` reader + the
/// type-expression production already in this module (`build_type_expr`).
/// No new grammar.
pub fn parse_type_expr(source: &str) -> Result<TypeExpr, CranelispError> {
    let sexps = crate::reader::parse(source)?;
    match sexps.as_slice() {
        [sexp] => build_type_expr(sexp),
        other => Err(parse_err(
            &format!(
                "type expression must be a single form, found {}",
                other.len()
            ),
            other.first().map(Sexp::span).unwrap_or(Span::SYNTHETIC),
        )),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    use cranelisp_types::TopLevel;

    /// Test-only adapter: builds a synthetic batch program from one or more
    /// source forms by calling `build_form`/`build_expr` and re-packaging the
    /// resulting `ParsedEntry` values into the legacy `Vec<TopLevel>` shape
    /// the existing assertions match against. The orchestrator now owns this
    /// re-packaging at runtime; the adapter exists only to preserve test
    /// surface during the Wave 3a-β cutover.
    type Program = Vec<TopLevel>;

    fn parsed_entry_to_top_level(entry: ParsedEntry) -> TopLevel {
        use cranelisp_types::Defn;
        match entry {
            ParsedEntry::Def {
                name,
                variants,
                visibility,
                docstring,
                span,
            } => TopLevel::Defn(Defn {
                name,
                docstring,
                variants,
                visibility,
                span,
            }),
            ParsedEntry::TypeDef {
                name,
                type_params,
                constructors,
                visibility,
                docstring,
                span,
            } => {
                // The legacy TopLevel::TypeDef carries type_params as Vec<Symbol>.
                let type_params_as_symbols: Vec<Symbol> = type_params
                    .into_iter()
                    .map(|t| Symbol::from(t.as_ref()))
                    .collect();
                TopLevel::TypeDef {
                    name,
                    docstring,
                    type_params: type_params_as_symbols,
                    constructors,
                    visibility,
                    span,
                }
            }
            ParsedEntry::TraitDecl { decl } => TopLevel::TraitDecl(decl),
            ParsedEntry::TraitImpl { impl_ } => TopLevel::TraitImpl(impl_),
            ParsedEntry::Macro { .. } | ParsedEntry::Constructor { .. } => {
                unreachable!(
                    "test adapter: parser-only entries (Macro/Constructor) should not appear in TopLevel-shaped assertions"
                )
            }
            _ => unreachable!("test adapter: unknown ParsedEntry variant"),
        }
    }

    /// Detect a top-level form head (defn/deftype/deftrait/impl/defmacro and
    /// their `-` variants) so the test adapter knows whether to route to
    /// `build_form` (and propagate its errors) or fall through to
    /// `build_expr`.
    fn is_top_level_form(sexp: &Sexp) -> bool {
        if let Sexp::List(children, _) = sexp
            && let Some(Sexp::Symbol(head, _)) = children.first()
        {
            return matches!(
                head.as_str(),
                "defn" | "defn-" | "deftype" | "deftype-" | "deftrait" | "deftrait-"
                    | "impl" | "defmacro" | "defmacro-"
            );
        }
        false
    }

    fn parse_and_build_program(input: &str) -> Result<Program, CranelispError> {
        let sexps = crate::reader::parse(input)?;
        let mut out = Vec::new();
        for s in sexps {
            if matches!(s, Sexp::Comment(_, _)) {
                continue;
            }
            if is_top_level_form(&s) {
                // Top-level form: route through build_form and propagate
                // errors. Drop per-deftype Constructor entries — they were
                // not in the legacy `Program` shape; the TypeDef entry
                // alone carries the constructor list inline for assertion.
                let entries = build_form(&s)?;
                for entry in entries {
                    if matches!(entry, ParsedEntry::Constructor { .. }) {
                        continue;
                    }
                    out.push(parsed_entry_to_top_level(entry));
                }
            } else {
                let expr = build_expr(&s)?;
                out.push(TopLevel::Expr(expr));
            }
        }
        Ok(out)
    }

    fn parse_and_build_repl(input: &str) -> Result<TopLevel, CranelispError> {
        let sexps = crate::reader::parse(input)?;
        assert!(!sexps.is_empty(), "expected at least one sexp");
        if is_top_level_form(&sexps[0]) {
            let mut entries = build_form(&sexps[0])?;
            entries.retain(|e| !matches!(e, ParsedEntry::Constructor { .. }));
            assert!(!entries.is_empty(), "expected at least one TopLevel-shaped entry");
            Ok(parsed_entry_to_top_level(entries.remove(0)))
        } else {
            let expr = build_expr(&sexps[0])?;
            Ok(TopLevel::Expr(expr))
        }
    }

    fn parse_and_build_expr(input: &str) -> Result<Expr, CranelispError> {
        let sexps = crate::reader::parse(input)?;
        assert!(!sexps.is_empty(), "expected at least one sexp");
        build_expr(&sexps[0])
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
                assert_eq!(params[0].0, "x");
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
            Expr::Lambda { params, .. } => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0].0, "x");
                assert!(params[0].1.is_some());
                match params[0].1.as_ref().unwrap() {
                    TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
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
                            TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                            other => panic!("expected Named(Int), got {other:?}"),
                        }
                    }
                    other => panic!("expected Annotate, got {other:?}"),
                }
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // -- `:Type` annotation pairing in every position (S81; BC §1 inv 9) --

    // spec: 02-grammar §2.3.8 — a standalone/top-level `:Type form` binds the
    // following form into a single `Annotate` (NOT a `Var` + separate literal).
    #[test]
    fn build_forms_top_level_annotation_binds_following_form() {
        let sexps = crate::reader::parse(":Int 42").unwrap();
        let forms = build_forms(&sexps).unwrap();
        assert_eq!(forms.len(), 1, "`:Int 42` is ONE annotated form, not two");
        match &forms[0] {
            TopLevel::Expr(Expr::Annotate { annotation, expr, .. }) => {
                match annotation {
                    TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                    other => panic!("expected Named(Int), got {other:?}"),
                }
                assert!(
                    matches!(**expr, Expr::IntLit { value: 42, .. }),
                    "annotation must bind the literal 42, got {expr:?}"
                );
            }
            other => panic!("expected TopLevel::Expr(Annotate), got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.8 — a leading `:Type` inside a parenthesized list
    // annotates the SINGLE following element; the list is the application of
    // that one annotated element (callee is the `Annotate`, NOT `:Int`).
    #[test]
    fn list_head_annotation_is_application_of_annotated_element() {
        match parse_and_build_expr("(:Int 42)").unwrap() {
            Expr::Apply { callee, args, .. } => {
                assert!(args.is_empty(), "one-element list — no args");
                match *callee {
                    Expr::Annotate { annotation, expr, .. } => {
                        match annotation {
                            TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                            other => panic!("expected Named(Int), got {other:?}"),
                        }
                        assert!(
                            matches!(*expr, Expr::IntLit { value: 42, .. }),
                            "the annotated element is `42`, got {expr:?}"
                        );
                    }
                    other => panic!("callee must be the annotated `42`, got {other:?}"),
                }
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.3.8 — a genuine apply argument `(f :Int 42)` still
    // annotates the arg (callee `f` unannotated). Regression guard for the
    // build_apply pairing change.
    #[test]
    fn apply_arg_annotation_unchanged() {
        match parse_and_build_expr("(f :Int 42)").unwrap() {
            Expr::Apply { callee, args, .. } => {
                assert!(
                    matches!(*callee, Expr::Var { .. }),
                    "callee `f` is an unannotated Var, got {callee:?}"
                );
                assert_eq!(args.len(), 1, "`:Int 42` is one annotated arg");
                assert!(
                    matches!(args[0], Expr::Annotate { .. }),
                    "the sole arg is an Annotate, got {:?}",
                    args[0]
                );
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.4.5 / 02-grammar §2.3.8 — a dangling `:Type` with no
    // following form is a parse error in EVERY position.
    #[test]
    fn dangling_annotation_top_level_is_error() {
        let sexps = crate::reader::parse(":Int").unwrap();
        let err = build_forms(&sexps).unwrap_err();
        assert!(
            format!("{err:?}").contains("annotation missing expression"),
            "expected `annotation missing expression`, got {err:?}"
        );
    }

    // spec: 01-lexical §1.4.5 — a bare `:Type` symbol reaching expression
    // position with nothing to bind is a parse error, never a `Var`.
    #[test]
    fn dangling_annotation_expr_position_is_error() {
        let err = parse_and_build_expr(":Foo").unwrap_err();
        assert!(
            format!("{err:?}").contains("annotation missing expression"),
            "expected `annotation missing expression`, got {err:?}"
        );
    }

    // spec: 01-lexical §1.4.5 / 02-grammar §2.3.8 — a dangling `:Type` inside a
    // list (`(:Int)`) is a parse error: the annotation has no element to bind.
    #[test]
    fn dangling_annotation_in_empty_paren_is_error() {
        let err = parse_and_build_expr("(:Int)").unwrap_err();
        assert!(
            format!("{err:?}").contains("annotation missing expression"),
            "expected `annotation missing expression`, got {err:?}"
        );
    }

    // spec: 02-grammar §2.3.8 — build_forms delegates non-annotated forms
    // per-form: a `defn` becomes `TopLevel::Defn`, a following bare `:Int 42`
    // becomes one annotated `TopLevel::Expr`.
    #[test]
    fn build_forms_mixes_defn_and_annotated_expr() {
        let sexps = crate::reader::parse("(defn id [x] x)\n:Int 42").unwrap();
        let forms = build_forms(&sexps).unwrap();
        assert_eq!(forms.len(), 2);
        assert!(matches!(forms[0], TopLevel::Defn(_)), "first is the defn");
        assert!(
            matches!(forms[1], TopLevel::Expr(Expr::Annotate { .. })),
            "second is the annotated expr, got {:?}",
            forms[1]
        );
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
                        assert_eq!(name.name.as_ref(), "Red");
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
                        assert_eq!(name.name.as_ref(), "Some");
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
                assert_eq!(defn.params().len(), 2);
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
            TopLevel::Defn(defn) => {
                assert_eq!(defn.name, "f");
                assert!(defn.is_multi_sig());
                assert_eq!(defn.variants.len(), 2);
                assert_eq!(defn.variants[0].params.len(), 1);
                assert_eq!(defn.variants[1].params.len(), 2);
            }
            other => panic!("expected Defn (multi-sig), got {other:?}"),
        }
    }

    // 0341 (FIXED): stacked trait-bound param annotations `[:Eq :Display a]`
    // attach BOTH bounds to the single binder `a`, yielding ONE param named `a`
    // (not two, with `:Display` mis-read as a second binder name). The run of
    // `:Trait` annotations preceding a binder all attach to it as a
    // `TypeExpr::Bounds([..])` carrier (FIXME 0341 frontend half / 0346 carrier).
    //
    // spec: spec/07-traits.md §7.8.2 — explicit constraint param annotations
    #[test]
    fn stacked_trait_bound_annotations_attach_to_single_param() {
        let prog = parse_and_build_program("(defn g [:Eq :Display a] a)").unwrap();
        assert_eq!(prog.len(), 1);
        match &prog[0] {
            TopLevel::Defn(defn) => {
                assert_eq!(defn.name, "g");
                // The stacked `:Eq :Display` bounds belong to `a`, so there is
                // exactly ONE parameter, named `a` — never a `:Display` binder.
                assert_eq!(
                    defn.params().len(),
                    1,
                    "stacked annotations must yield ONE param `a`; \
                     got {} params: {:?}",
                    defn.params().len(),
                    defn.params(),
                );
                assert_eq!(
                    defn.params()[0].0,
                    "a",
                    "the single param must be named `a`, not a mis-read \
                     `:Display` annotation"
                );
                // The accumulated run is carried as `Bounds([Eq, Display])` —
                // the shape typecheck's `resolve_bound_param` consumes.
                match &defn.params()[0].1 {
                    Some(TypeExpr::Bounds(bounds)) => {
                        let names: Vec<&str> =
                            bounds.iter().map(|t| t.name.as_ref()).collect();
                        assert_eq!(names, vec!["Eq", "Display"],
                            "the stacked bounds must be Bounds([Eq, Display])");
                        assert!(bounds.iter().all(|t| t.module.is_none()),
                            "unqualified bounds carry no module");
                    }
                    other => panic!(
                        "expected Some(Bounds([Eq, Display])), got {other:?}"
                    ),
                }
            }
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // 0341 (FIXED): the `assert-eq`-shaped TWO-param stacked signature
    // `[:Eq :Display a :Eq :Display b]` must parse — each binder takes the run
    // of `:Eq :Display` bounds preceding it, NOT a `duplicate parameter name
    // ':Display'` error from `:Display` being mis-read as a second binder.
    //
    // spec: spec/07-traits.md §7.8.2 — explicit constraint param annotations
    #[test]
    fn stacked_trait_bounds_two_params_no_duplicate_error() {
        let prog =
            parse_and_build_program("(defn f [:Eq :Display a :Eq :Display b] a)")
                .expect("two stacked-bound params must parse, not duplicate-error");
        assert_eq!(prog.len(), 1);
        match &prog[0] {
            TopLevel::Defn(defn) => {
                let params = defn.params();
                assert_eq!(
                    params.len(),
                    2,
                    "exactly two binders `a` and `b`; got {:?}",
                    params,
                );
                assert_eq!(params[0].0, "a");
                assert_eq!(params[1].0, "b");
                for (i, name) in [(0usize, "a"), (1usize, "b")] {
                    match &params[i].1 {
                        Some(TypeExpr::Bounds(bounds)) => {
                            let ns: Vec<&str> =
                                bounds.iter().map(|t| t.name.as_ref()).collect();
                            assert_eq!(ns, vec!["Eq", "Display"],
                                "param {name} must carry Bounds([Eq, Display])");
                        }
                        other => panic!(
                            "param {name} expected Bounds([Eq, Display]), got {other:?}"
                        ),
                    }
                }
            }
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // Regression: a SINGLE trait-bound `[:Eq a]` is the run-of-length-1 and is
    // left as the resolved `TypeExpr` (NOT wrapped in `Bounds`), so the existing
    // single-annotation path is unchanged.
    //
    // spec: spec/07-traits.md §7.8.2 — single explicit constraint param annotation
    #[test]
    fn single_trait_bound_annotation_unchanged() {
        let prog = parse_and_build_program("(defn g [:Eq a] a)").unwrap();
        match &prog[0] {
            TopLevel::Defn(defn) => {
                assert_eq!(defn.params().len(), 1);
                assert_eq!(defn.params()[0].0, "a");
                // Run-of-1: not promoted to Bounds — stays a Named annotation.
                assert!(
                    !matches!(defn.params()[0].1, Some(TypeExpr::Bounds(_))),
                    "single bound must NOT be wrapped in Bounds: {:?}",
                    defn.params()[0].1,
                );
            }
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // Regression: a concrete-type annotation `[:Int x]` still emits
    // `Some(Named(Int))`, NOT `Bounds`.
    //
    // spec: spec/03-types.md §3.9.2 — concrete-type param annotation
    #[test]
    fn concrete_type_param_annotation_is_named() {
        let prog = parse_and_build_program("(defn g [:Int x] x)").unwrap();
        match &prog[0] {
            TopLevel::Defn(defn) => {
                assert_eq!(defn.params().len(), 1);
                match &defn.params()[0].1 {
                    Some(TypeExpr::Named(r)) => assert_eq!(r.name.as_ref(), "Int"),
                    other => panic!("expected Some(Named(Int)), got {other:?}"),
                }
            }
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // Regression: a genuine duplicate binder `[x x]` still errors.
    //
    // spec: spec/07-traits.md §7.8.2 — distinct param names
    #[test]
    fn genuine_duplicate_binder_still_errors() {
        let err = parse_and_build_program("(defn g [x x] x)").unwrap_err();
        assert!(
            format!("{err:?}").contains("duplicate parameter name"),
            "genuine duplicate binder must still error: {err:?}",
        );
    }

    // Edge: a trailing annotation run with no terminating binder `[:Eq]` is the
    // "annotation missing parameter name" error.
    //
    // spec: spec/07-traits.md §7.8.2 — annotation must bind a parameter
    #[test]
    fn trailing_annotation_without_binder_errors() {
        let err = parse_and_build_program("(defn g [:Eq] 0)").unwrap_err();
        assert!(
            format!("{err:?}").contains("annotation missing parameter name"),
            "trailing annotation run must error: {err:?}",
        );
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
            TopLevel::Expr(Expr::IntLit { value, .. }) => assert_eq!(value, 42),
            other => panic!("expected Expr(IntLit), got {other:?}"),
        }
    }

    // spec: 02-grammar §2.1 — REPL defn definition
    #[test]
    fn test_repl_defn() {
        match parse_and_build_repl("(defn f [x] x)").unwrap() {
            TopLevel::Defn(defn) => assert_eq!(defn.name, "f"),
            other => panic!("expected Defn, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.1 — REPL deftype definition
    #[test]
    fn test_repl_deftype() {
        match parse_and_build_repl("(deftype Color Red Green Blue)").unwrap() {
            TopLevel::TypeDef { name, .. } => assert_eq!(name, "Color"),
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    // -- Rejected forms --

    // spec: spec/04-expressions.md §4.12 — trace produces Expr::Trace
    #[test]
    fn test_trace_produces_trace_node() {
        match parse_and_build_expr("(trace 42)").unwrap() {
            Expr::Trace { modules, body, .. } => {
                assert!(modules.is_empty());
                match *body {
                    Expr::IntLit { value, .. } => assert_eq!(value, 42),
                    other => panic!("expected IntLit body, got {other:?}"),
                }
            }
            other => panic!("expected Trace, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.4 — trace in head/reference position is the special
    // form and still builds Expr::Trace (it is NOT a binder, not rejected).
    #[test]
    fn test_trace_head_position_still_builds_trace_node() {
        match parse_and_build_expr("(trace (f 1))").unwrap() {
            Expr::Trace { body, .. } => {
                assert!(matches!(*body, Expr::Apply { .. }), "expected Apply body");
            }
            other => panic!("expected Trace, got {other:?}"),
        }
    }

    // -- test-discovery: `discover-tests` / `run-test` are NOT special forms --
    // design/arch/test-discovery.md §"Frontend — nothing (zero special-casing)"

    // spec: appendix-a-builtins §A.4 — `discover-tests` parses as an ordinary
    // application (no head-position dispatch), resolving through the symbol table.
    #[test]
    fn test_discover_tests_builds_as_apply() {
        match parse_and_build_expr("(discover-tests [\"user\"])").unwrap() {
            Expr::Apply { callee, args, .. } => {
                assert!(
                    matches!(&*callee, Expr::Var { name, .. } if name.as_ref() == "discover-tests"),
                    "expected Var(discover-tests) callee, got {callee:?}"
                );
                assert_eq!(args.len(), 1, "expected the vec-literal argument preserved");
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // spec: appendix-a-builtins §A.4 — no-arg `(discover-tests)` is an ordinary
    // zero-arg application now (the no-arg sugar is a stdlib-macro concern, not a
    // frontend special form).
    #[test]
    fn test_discover_tests_no_arg_builds_as_apply() {
        match parse_and_build_expr("(discover-tests)").unwrap() {
            Expr::Apply { callee, args, .. } => {
                assert!(
                    matches!(&*callee, Expr::Var { name, .. } if name.as_ref() == "discover-tests"),
                    "expected Var(discover-tests) callee, got {callee:?}"
                );
                assert!(args.is_empty(), "expected no synthesised arguments");
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // spec: appendix-a-builtins §A.4 — `run-test` is retired; it no longer parses
    // as a special form. It builds as an ordinary application (and will fail at
    // typecheck because no such symbol exists).
    #[test]
    fn test_run_test_builds_as_apply() {
        match parse_and_build_expr("(run-test foo)").unwrap() {
            Expr::Apply { callee, .. } => {
                assert!(
                    matches!(&*callee, Expr::Var { name, .. } if name.as_ref() == "run-test"),
                    "expected Var(run-test) callee, got {callee:?}"
                );
            }
            other => panic!("expected Apply, got {other:?}"),
        }
    }

    // spec: appendix-a-builtins §A.4 — `discover-tests` is NOT a reserved binder
    // (only `trace` is); defining it is allowed.
    #[test]
    fn test_defn_discover_tests_allowed() {
        let prog = parse_and_build_program("(defn discover-tests [x] x)").unwrap();
        assert!(!prog.is_empty(), "expected the defn to build");
    }

    // -- Reserved binder name: `trace` (spec/02-grammar.md §2.9) --

    fn assert_reserved_trace_error(err: CranelispError) {
        let msg = format!("{err}");
        assert!(
            msg.contains("'trace' is a reserved special-form name"),
            "expected reserved-name error, got: {msg}"
        );
    }

    // spec: 02-grammar §2.9 — `trace` rejected as a defn name
    #[test]
    fn test_reject_trace_defn_name() {
        let err = parse_and_build_program("(defn trace [x] x)").unwrap_err();
        assert_reserved_trace_error(err);
    }

    // spec: 02-grammar §2.9 — `trace` rejected as a let binder
    #[test]
    fn test_reject_trace_let_binder() {
        let err = parse_and_build_expr("(let [trace 1] trace)").unwrap_err();
        assert_reserved_trace_error(err);
    }

    // spec: 02-grammar §2.9 — `trace` rejected as a fn parameter
    #[test]
    fn test_reject_trace_fn_param() {
        let err = parse_and_build_expr("(fn [trace] trace)").unwrap_err();
        assert_reserved_trace_error(err);
    }

    // spec: 02-grammar §2.9 — `trace` rejected as a match pattern variable
    // binder (a bare lowercase pattern symbol is a binder).
    #[test]
    fn test_reject_trace_match_pattern_var() {
        let err = parse_and_build_expr("(match x [trace trace])").unwrap_err();
        assert_reserved_trace_error(err);
    }

    // spec: 02-grammar §2.9 — `trace` rejected as a constructor-pattern binding
    // (the bound variable is a binder; the constructor name is not).
    #[test]
    fn test_reject_trace_constructor_pattern_binding() {
        let err = parse_and_build_expr("(match x [(Some trace) trace])").unwrap_err();
        assert_reserved_trace_error(err);
    }

    // spec: 02-grammar §2.9 — `trace` rejected as a defmacro name (any
    // binder/definition position; spec §2.9 prose covers "any other position").
    #[test]
    fn test_reject_trace_defmacro_name() {
        let err = parse_and_build_program("(defmacro trace [x] x)").unwrap_err();
        assert_reserved_trace_error(err);
    }

    // spec: 02-grammar §2.9 — `trace` rejected as a defmacro parameter.
    #[test]
    fn test_reject_trace_defmacro_param() {
        let err = parse_and_build_program("(defmacro m [trace] trace)").unwrap_err();
        assert_reserved_trace_error(err);
    }

    // spec: 02-grammar §2.9 — a constructor NAME `Trace` is not a binder and is
    // unaffected (only the reserved lowercase keyword `trace` is rejected).
    #[test]
    fn test_constructor_name_unaffected() {
        // `traced` (a different name containing the substring) must bind fine.
        let expr = parse_and_build_expr("(let [traced 1] traced)").unwrap();
        assert!(matches!(expr, Expr::Let { .. }));
    }

    // spec: 02-grammar §2.3.9 — vec is now handled by the prelude vec macro
    // (no AST intercept). It parses as a regular function application.
    #[test]
    fn test_vec_parses_as_call() {
        // (vec 1 2 3) should parse as a regular Apply, not be rejected.
        let expr = parse_and_build_expr("(vec 1 2 3)").unwrap();
        assert!(matches!(expr, cranelisp_types::Expr::Apply { .. }));
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
                assert!(matches!(&decl.methods[0].params[0].1, TypeExpr::SelfType));
                assert!(matches!(&decl.methods[0].ret_type, TypeExpr::Named(n) if n.name.as_ref() == "String"));
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
        // Per spec §5.3 EBNF (`param = ':' type_expr symbol | symbol`) required-method
        // params now carry names; bare params default to SelfType per spec §5.3.1.
        // S70 cascade row #9 — pre-cascade test input used `[self self]` (the bare
        // type-only no-default-branch reading) which is spec-non-compliant on the
        // post-S69-Sub-26 fused shape. Inputs rewritten to spec-conformant `[a b]`.
        let prog = parse_and_build_program(
            "(deftrait Num (+ [a b] self) (- [a b] self))",
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
        // S70 cascade row #9 — pre-cascade input used bare type expressions in the
        // bracket; spec §5.3 EBNF requires param names. The HKT param-index detect
        // logic walks `bracket_items` looking for a `(f ...)` shape, so the param
        // name must be annotated alongside an `(f a)` type. Use `:Type name` form.
        let prog = parse_and_build_program(
            "(deftrait (Functor f) (fmap [:(Fn [a] b) g :(f a) x] (f b)))",
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
        // S70 cascade row #9 — `[self self]` pre-cascade input rewritten to spec
        // conformant `[a b]` (bare params default to SelfType per spec §5.3.1).
        let prog = parse_and_build_program(
            "(deftrait Ord (< [a b] Bool) (<= [x y] Bool (if (< x y) true (= x y))))",
        ).unwrap();
        match &prog[0] {
            TopLevel::TraitDecl(decl) => {
                assert_eq!(decl.methods.len(), 2);
                assert!(decl.methods[0].default_body.is_none());
                // Names live with params now (S69 Sub 26) — verify the no-default
                // method has its two self-typed params.
                assert_eq!(decl.methods[0].params.len(), 2);
                assert!(decl.methods[1].default_body.is_some());
                assert_eq!(decl.methods[1].params.len(), 2);
                assert_eq!(decl.methods[1].params[0].0, "x");
                assert_eq!(decl.methods[1].params[1].0, "y");
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
                assert_eq!(imp.trait_name.name.as_ref(), "Display");
                // Concrete target: TypeExpr::Named(Int)
                match &imp.target {
                    TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                    other => panic!("expected Named, got {other:?}"),
                }
                assert!(imp.type_constraints.is_empty());
                assert_eq!(imp.methods.len(), 1);
                assert_eq!(imp.methods[0].name, "show");
                assert_eq!(imp.methods[0].params().len(), 1);
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
                assert_eq!(imp.trait_name.name.as_ref(), "Display");
                // Polymorphic target: TypeExpr::Applied(Option, [TypeVar(a)])
                match &imp.target {
                    TypeExpr::Applied(head, args) => {
                        assert_eq!(head.name.as_ref(), "Option");
                        assert_eq!(args.len(), 1);
                        match &args[0] {
                            TypeExpr::TypeVar(v) => assert_eq!(v, "a"),
                            other => panic!("expected TypeVar(a), got {other:?}"),
                        }
                    }
                    other => panic!("expected Applied, got {other:?}"),
                }
                assert_eq!(imp.type_constraints.len(), 1);
                assert_eq!(imp.type_constraints[0].0, "a");
                assert_eq!(imp.type_constraints[0].1.name.as_ref(), "Display");
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
                assert_eq!(imp.trait_name.name.as_ref(), "Functor");
                // Concrete target (bare symbol form): TypeExpr::Named(Option)
                match &imp.target {
                    TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Option"),
                    other => panic!("expected Named, got {other:?}"),
                }
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
            TopLevel::TraitImpl(imp) => {
                assert_eq!(imp.trait_name.name.as_ref(), "Eq");
                match &imp.target {
                    TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                    other => panic!("expected Named, got {other:?}"),
                }
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
            TopLevel::TraitDecl(decl) => {
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
            Expr::Lambda { params, .. } => {
                assert_eq!(params.len(), 1);
                match params[0].1.as_ref().unwrap() {
                    TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
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
            Expr::Lambda { params, .. } => {
                assert_eq!(params.len(), 1);
                match params[0].1.as_ref().unwrap() {
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
            Expr::Lambda { params, .. } => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0].0, "f");
                match params[0].1.as_ref().unwrap() {
                    TypeExpr::FnType(fn_params, ret) => {
                        assert_eq!(fn_params.len(), 1);
                        match &fn_params[0] {
                            TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                            other => panic!("expected Named, got {other:?}"),
                        }
                        match ret.as_ref() {
                            TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
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

    // -- Unexpected reader-macro forms (should be handled by expander) --

    // spec: 01-lexical §1.6 — quote form unexpected in AST builder (expander should handle)
    #[test]
    fn test_reject_quote() {
        let err = parse_and_build_expr("'foo").unwrap_err();
        assert!(err.message().contains("unexpected quote form"));
        assert!(err.message().contains("should have been expanded"));
    }

    // spec: 01-lexical §1.6 — quasiquote form unexpected in AST builder (expander should handle)
    #[test]
    fn test_reject_quasiquote() {
        let err = parse_and_build_expr("`foo").unwrap_err();
        assert!(err.message().contains("unexpected quasiquote form"));
        assert!(err.message().contains("should have been expanded"));
    }

    // spec: 01-lexical §1.6 — unquote form unexpected in AST builder (expander should handle)
    #[test]
    fn test_reject_unquote() {
        let err = parse_and_build_expr("~x").unwrap_err();
        assert!(err.message().contains("unexpected unquote form"));
        assert!(err.message().contains("should have been expanded"));
    }

    // spec: 01-lexical §1.6 — unquote-splicing form unexpected in AST builder (expander should handle)
    #[test]
    fn test_reject_unquote_splicing() {
        let err = parse_and_build_expr("~@xs").unwrap_err();
        assert!(err.message().contains("unexpected unquote-splicing form"));
        assert!(err.message().contains("should have been expanded"));
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
                assert_eq!(defn.params().len(), 1);
                assert_eq!(defn.params()[0].0, "x");
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
                            assert_eq!(name.name.as_ref(), "Option");
                            assert_eq!(type_args.len(), 1);
                            match &type_args[0] {
                                TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
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
                            assert_eq!(name.name.as_ref(), "Map");
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
                        assert_eq!(name.name.as_ref(), "Some");
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
                        assert_eq!(name.name.as_ref(), "Point");
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
                    TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                    other => panic!("expected Named(Int), got {other:?}"),
                }
                assert_eq!(ctor.fields[1].name, "y");
                match &ctor.fields[1].type_expr {
                    TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
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
            TopLevel::Expr(Expr::StringLit { value, .. }) => {
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
                assert_eq!(defn.params().len(), 1);
                assert_eq!(defn.params()[0].0, "x");
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

    // -- Duplicate parameter names --

    // spec: 05-definitions §5 — duplicate param names rejected in defn (batch)
    #[test]
    fn test_duplicate_param_names_defn_batch() {
        let err = parse_and_build_program("(defn bad [x x] (add-i64 x x))").unwrap_err();
        let msg = format!("{err}");
        assert!(msg.contains("duplicate parameter name 'x'"), "got: {msg}");
    }

    // spec: 05-definitions §5 — duplicate param names rejected in defn (REPL)
    #[test]
    fn test_duplicate_param_names_defn_repl() {
        let err = parse_and_build_repl("(defn bad [x x] (add-i64 x x))").unwrap_err();
        let msg = format!("{err}");
        assert!(msg.contains("duplicate parameter name 'x'"), "got: {msg}");
    }

    // spec: 04-expressions §4 — duplicate param names rejected in lambda
    #[test]
    fn test_duplicate_param_names_lambda() {
        let err = parse_and_build_expr("(fn [a a] a)").unwrap_err();
        let msg = format!("{err}");
        assert!(msg.contains("duplicate parameter name 'a'"), "got: {msg}");
    }

    // spec: 05-definitions §5 — distinct param names accepted
    #[test]
    fn test_distinct_param_names_ok() {
        assert!(parse_and_build_program("(defn good [x y] (add-i64 x y))").is_ok());
    }

    // ---------------------------------------------------------------------
    // build_form direct tests (Wave 3a-β — FIXME 0156)
    // ---------------------------------------------------------------------

    fn parse_one(input: &str) -> Sexp {
        let sexps = crate::reader::parse(input).unwrap();
        sexps.into_iter().next().unwrap()
    }

    // spec: 02-grammar §2.2.1 + facade frontend.md §"Free functions" — defn
    // yields exactly one ParsedEntry::Def.
    #[test]
    fn build_form_defn_yields_single_def() {
        let entries = build_form(&parse_one("(defn add [a b] (add-i64 a b))")).unwrap();
        assert_eq!(entries.len(), 1, "defn should yield 1 entry");
        match &entries[0] {
            ParsedEntry::Def { name, variants, visibility, .. } => {
                assert_eq!(name.as_ref(), "add");
                assert_eq!(variants.len(), 1);
                assert_eq!(variants[0].params.len(), 2);
                assert_eq!(*visibility, Visibility::Public);
            }
            other => panic!("expected ParsedEntry::Def, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.6 — defn- yields Private visibility.
    #[test]
    fn build_form_defn_private() {
        let entries = build_form(&parse_one("(defn- helper [x] x)")).unwrap();
        match &entries[0] {
            ParsedEntry::Def { visibility, .. } => {
                assert_eq!(*visibility, Visibility::Private);
            }
            other => panic!("expected ParsedEntry::Def, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.2 + facade — deftype with N constructors yields
    // 1 TypeDef + N Constructor entries (in source-declaration order).
    #[test]
    fn build_form_deftype_yields_typedef_plus_per_constructor() {
        // 3 variants → 4 entries.
        let entries = build_form(&parse_one("(deftype Color Red Green Blue)")).unwrap();
        assert_eq!(entries.len(), 4, "1 TypeDef + 3 Constructors expected");
        match &entries[0] {
            ParsedEntry::TypeDef { name, constructors, .. } => {
                assert_eq!(name.as_ref(), "Color");
                assert_eq!(constructors.len(), 3);
            }
            other => panic!("entries[0] should be TypeDef, got {other:?}"),
        }
        // Ordering: TypeDef, then Constructors in source order.
        for (i, expected_name) in ["Red", "Green", "Blue"].iter().enumerate() {
            match &entries[i + 1] {
                ParsedEntry::Constructor { name, of_type, .. } => {
                    assert_eq!(name.as_ref(), *expected_name);
                    assert_eq!(of_type.as_ref(), "Color");
                }
                other => panic!("entries[{}] should be Constructor, got {other:?}", i + 1),
            }
        }
    }

    // spec: 02-grammar §2.2.2 — product type (single bracketed-fields ctor)
    // yields 1 TypeDef + 1 Constructor.
    #[test]
    fn build_form_deftype_product_yields_two_entries() {
        let entries = build_form(&parse_one("(deftype Point [:Int x :Int y])")).unwrap();
        assert_eq!(entries.len(), 2);
        assert!(matches!(&entries[0], ParsedEntry::TypeDef { .. }));
        match &entries[1] {
            ParsedEntry::Constructor { name, of_type, fields, .. } => {
                assert_eq!(name.as_ref(), "Point");
                assert_eq!(of_type.as_ref(), "Point");
                assert_eq!(fields.len(), 2);
            }
            other => panic!("entries[1] should be Constructor, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.3 — deftrait yields exactly one TraitDecl.
    #[test]
    fn build_form_deftrait_yields_single_trait_decl() {
        let entries = build_form(&parse_one("(deftrait Display (show [self] String))")).unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            ParsedEntry::TraitDecl { decl } => {
                assert_eq!(decl.name.as_ref(), "Display");
                assert_eq!(decl.methods.len(), 1);
            }
            other => panic!("expected ParsedEntry::TraitDecl, got {other:?}"),
        }
    }

    // spec: 02-grammar §2.2.4 — impl yields exactly one TraitImpl.
    #[test]
    fn build_form_impl_yields_single_trait_impl() {
        let entries = build_form(
            &parse_one("(impl Display Int (defn show [x] (int-to-string x)))"),
        )
        .unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            ParsedEntry::TraitImpl { impl_ } => {
                assert_eq!(impl_.trait_name.name.as_ref(), "Display");
                match &impl_.target {
                    TypeExpr::Named(n) => assert_eq!(n.name.as_ref(), "Int"),
                    other => panic!("expected Named(Int), got {other:?}"),
                }
            }
            other => panic!("expected ParsedEntry::TraitImpl, got {other:?}"),
        }
    }

    // spec: 09-macros.md + facade — defmacro yields one ParsedEntry::Macro
    // carrying ALL clauses in DefmacroInfo.clauses.
    #[test]
    fn build_form_defmacro_yields_single_macro_with_all_clauses() {
        let entries = build_form(
            &parse_one("(defmacro when ([cond body] (if cond body 0)))"),
        )
        .unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            ParsedEntry::Macro { info } => {
                assert_eq!(info.name.as_ref(), "when");
                assert_eq!(info.clauses.len(), 1);
                assert!(!info.is_private);
            }
            other => panic!("expected ParsedEntry::Macro, got {other:?}"),
        }
    }

    // spec: 09-macros.md — multi-clause defmacro packages every clause
    // inside one Macro entry (NOT per-clause Macro entries).
    #[test]
    fn build_form_multi_clause_defmacro_yields_single_macro() {
        let entries = build_form(
            &parse_one("(defmacro pick ([x] x) ([x y] x) ([x y z] x))"),
        )
        .unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            ParsedEntry::Macro { info } => {
                assert_eq!(info.clauses.len(), 3);
            }
            other => panic!("expected single Macro entry, got {other:?}"),
        }
    }

    // facade — `begin` must be flattened by the orchestrator; reaching
    // `build_form` is a caller bug.
    #[test]
    fn build_form_rejects_begin() {
        let err = build_form(&parse_one("(begin 1 2)")).unwrap_err();
        let msg = format!("{err}");
        assert!(
            msg.contains("begin") && msg.contains("flatten"),
            "got: {msg}"
        );
    }

    // facade — structural decls must be peeled by extract_module_declarations.
    #[test]
    fn build_form_rejects_import() {
        let err = build_form(&parse_one("(import [user [foo]])")).unwrap_err();
        let msg = format!("{err}");
        assert!(msg.contains("structural"), "got: {msg}");
    }

    // facade — `build_form` rejects bare expressions (route to build_expr).
    #[test]
    fn build_form_rejects_bare_expression() {
        // A bare int isn't a top-level form vocabulary entry.
        let err = build_form(&parse_one("42")).unwrap_err();
        let msg = format!("{err}");
        assert!(msg.contains("top-level form"), "got: {msg}");
    }

    // facade — unknown top-level head produces a clear error.
    #[test]
    fn build_form_rejects_unknown_head() {
        let err = build_form(&parse_one("(woot foo bar)")).unwrap_err();
        let msg = format!("{err}");
        assert!(
            msg.contains("unknown top-level form"),
            "got: {msg}"
        );
    }

    // facade — `build_expr` is a pure structural transform; no macro lookup.
    #[test]
    fn build_expr_pure_int_literal() {
        let expr = build_expr(&parse_one("42")).unwrap();
        assert!(matches!(expr, Expr::IntLit { value: 42, .. }));
    }

    // FIXME 0230 — `parse_type_expr` parses a bare named type.
    #[test]
    fn parse_type_expr_named() {
        let te = parse_type_expr("Int").unwrap();
        match te {
            TypeExpr::Named(r) => assert_eq!(r.name.as_ref(), "Int"),
            other => panic!("expected Named, got {other:?}"),
        }
    }

    // FIXME 0230 — `parse_type_expr` parses a type variable (lowercase).
    #[test]
    fn parse_type_expr_type_var() {
        let te = parse_type_expr("a").unwrap();
        assert!(matches!(te, TypeExpr::TypeVar(_)));
    }

    // FIXME 0230 — `parse_type_expr` parses a `(Fn [..] R)` form.
    #[test]
    fn parse_type_expr_fn() {
        let te = parse_type_expr("(Fn [Int] Bool)").unwrap();
        match te {
            TypeExpr::FnType(params, ret) => {
                assert_eq!(params.len(), 1);
                assert!(matches!(*ret, TypeExpr::Named(_)));
            }
            other => panic!("expected FnType, got {other:?}"),
        }
    }

    // FIXME 0230 — `parse_type_expr` parses an applied `(Name arg..)` form.
    #[test]
    fn parse_type_expr_applied() {
        let te = parse_type_expr("(Option Int)").unwrap();
        match te {
            TypeExpr::Applied(r, args) => {
                assert_eq!(r.name.as_ref(), "Option");
                assert_eq!(args.len(), 1);
            }
            other => panic!("expected Applied, got {other:?}"),
        }
    }

    // FIXME 0230 — more than one form is rejected (string in / one out).
    #[test]
    fn parse_type_expr_rejects_multiple_forms() {
        let err = parse_type_expr("Int Bool").unwrap_err();
        let msg = format!("{err}");
        assert!(msg.contains("single form"), "got: {msg}");
    }

    // FIXME 0230 — zero forms is rejected.
    #[test]
    fn parse_type_expr_rejects_empty() {
        let err = parse_type_expr("").unwrap_err();
        let msg = format!("{err}");
        assert!(msg.contains("single form"), "got: {msg}");
    }

    // FIXME 0362 — a self-qualified type annotation `:t/Box` must split the
    // `module/Name` qualifier so it arrives downstream as
    // `TypeRef { module: Some("t"), name: "Box" }`, not the un-split
    // `TypeRef { module: None, name: "t/Box" }` (whose empty from-module is the
    // tell of the original `unknown type 't/Box' (from module '')` defect).
    #[test]
    fn parse_annotation_name_splits_module_qualifier() {
        match parse_annotation_name("t/Box") {
            TypeExpr::Named(r) => {
                assert_eq!(r.module.as_deref(), Some("t"));
                assert_eq!(r.name.as_ref(), "Box");
            }
            other => panic!("expected Named, got {other:?}"),
        }
    }

    // FIXME 0362 — a bare (unqualified) type name stays `module: None`.
    #[test]
    fn parse_annotation_name_bare_stays_unqualified() {
        match parse_annotation_name("Box") {
            TypeExpr::Named(r) => {
                assert_eq!(r.module, None);
                assert_eq!(r.name.as_ref(), "Box");
            }
            other => panic!("expected Named, got {other:?}"),
        }
    }

    // FIXME 0362 — a deep-qualified type name `a.b/Box` splits at the LAST `/`
    // (module = `a.b`, name = `Box`), matching the trait-ref precedent.
    #[test]
    fn parse_annotation_name_deep_qualified_splits_at_last_slash() {
        match parse_annotation_name("a.b/Box") {
            TypeExpr::Named(r) => {
                assert_eq!(r.module.as_deref(), Some("a.b"));
                assert_eq!(r.name.as_ref(), "Box");
            }
            other => panic!("expected Named, got {other:?}"),
        }
    }

    // FIXME 0362 — the qualifier split also applies in type-expression position
    // (`parse_type_expr` → `build_type_expr`), both for a bare qualified name
    // and for the applied `(t/Box arg)` head.
    #[test]
    fn parse_type_expr_splits_module_qualifier() {
        match parse_type_expr("t/Box").unwrap() {
            TypeExpr::Named(r) => {
                assert_eq!(r.module.as_deref(), Some("t"));
                assert_eq!(r.name.as_ref(), "Box");
            }
            other => panic!("expected Named, got {other:?}"),
        }
        match parse_type_expr("(t/Box Int)").unwrap() {
            TypeExpr::Applied(r, args) => {
                assert_eq!(r.module.as_deref(), Some("t"));
                assert_eq!(r.name.as_ref(), "Box");
                assert_eq!(args.len(), 1);
            }
            other => panic!("expected Applied, got {other:?}"),
        }
    }
}
