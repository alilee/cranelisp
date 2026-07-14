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
                match &children[next] {
                    Sexp::Bracket(..) => build_field_list(&children[next])?,
                    // A trailing form that is neither a docstring nor a
                    // `[:Type name]` bracket is malformed (spec §5.2 requires
                    // constructor fields to be a bracketed list). Historically
                    // this fell through to `vec![]`, silently dropping the field
                    // and collapsing e.g. `(L :Int)` to a NULLARY constructor
                    // (a silent enum). Reject it with a self-documenting error.
                    other => {
                        return Err(parse_err(
                            &format!(
                                "constructor `{name}` field must be a bracketed `[:Type name]` \
                                 list; found a bare form with no field name. Write \
                                 `({name} [:Type name])` — e.g. `({name} [:Int n])`"
                            ),
                            other.span(),
                        ));
                    }
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
    let ret_type = build_ret_type(&children[ret_pos])?;

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
            trait_name: trait_ref_from_name(trait_name),
            target,
            type_constraints,
            methods,
            span,
        },
    })
}

/// Parsed impl target: (target type expression, trait constraints).
///
/// Per S69 Submission 27 (`TraitImpl.target: TypeExpr` unified). Every name
/// position routes through the §8.5 splitters (`type_ref_from_name` /
/// `trait_ref_from_name`) so a qualified `module/Name` is canonicalised into
/// `Some(module)` rather than left whole with `module: None` (which would
/// re-root it under the current module — the D-qual defect class, S91 Thread B):
/// - `Type` (or `module/Type`) lowers to
///   `TypeExpr::Named(type_ref_from_name(name))`
/// - `(Type :Constraint var ...)` / `(Type var ...)` lowers to
///   `TypeExpr::Applied(type_ref_from_name(head), args)` where each bare-symbol
///   arg becomes `TypeExpr::TypeVar(name)` (or, if uppercase,
///   `TypeExpr::Named(type_ref_from_name(name))`); each constraint trait carries
///   on the side as `trait_ref_from_name(constraint_name)`.
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
            // §8.5: a qualified target (`primitives/Int`) is canonical — split it
            // through the shared splitter rather than stuffing the whole slash-name
            // into the bare-name slot (which re-roots it under the current module).
            let target = TypeExpr::Named(type_ref_from_name(name.as_str()));
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
                        // §8.5: a qualified constraint trait (`:fmt/Eq a`,
                        // spec/07-traits.md:749) is canonical — split through the
                        // shared splitter rather than stuffing the slash-name into
                        // the bare-name slot (which re-roots the trait under the
                        // current module). Same root-cause class as the impl
                        // trait-name and target sites.
                        type_constraints.push((
                            Symbol::from(var_name),
                            trait_ref_from_name(constraint_name),
                        ));
                        i += 1;
                    } else {
                        // Bare type arg — uppercase becomes Named, lowercase TypeVar.
                        // §8.5: a qualified uppercase arg (`(Option primitives/Int)`)
                        // is canonical — split through the shared splitter.
                        let arg = if is_uppercase_start(s) {
                            TypeExpr::Named(type_ref_from_name(s.as_str()))
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

            // §8.5: a qualified applied head (`(primitives/Map K V)`) is canonical —
            // split through the shared splitter rather than stuffing the slash-name
            // into the bare-name slot.
            let target = TypeExpr::Applied(
                type_ref_from_name(type_name),
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
    // (fn [params] body) or (lambda [params] body) — single-arity ONLY
    // (spec §4.5). A `[params]` is a `Sexp::Bracket`; when the first operand is
    // instead a `Sexp::List` `([params] body)` the user wrote the parenthesised
    // MULTI-ARITY clause form, which is `defn`-only. Name the real constraint
    // (0575) rather than the misleading "requires param list and body" (which
    // reads as if `fn` got no params).
    if children.len() >= 2 && matches!(&children[1], Sexp::List(..)) {
        return Err(parse_err(
            "fn is single-arity: it takes one [params] bracket and a body. The \
             parenthesised multi-arity clause form `(fn ([p] …) ([p q] …))` is \
             defn-only — use defn for multiple arities (spec §4.5)",
            span,
        ));
    }
    if children.len() != 3 {
        return Err(parse_err(
            "fn is single-arity: it takes one [params] bracket and a body \
             (use defn for multiple arities, spec §4.5)",
            span,
        ));
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
    //
    // The scrutinee may carry a `:Type form` annotation (BC §1 invariant 9;
    // spec §2.3.8 — `:Type` is reader-macro-like, binding the immediately
    // following form in ALL positions, including a match scrutinee). Consume
    // it through the same annotation-pairing primitive (`build_one_expr_at`)
    // used for call arguments and vec literals so the annotated scrutinee
    // groups into ONE `Expr::Annotate` rather than presenting as extra
    // children that defeat a positional arity guard (FIXME 0389).
    //
    // Minimum shape: `(match <scrutinee...> [arms])` — at least the `match`
    // head, one scrutinee token, and the arms bracket.
    if children.len() < 3 {
        return Err(parse_err("match requires scrutinee and arms", span));
    }
    let (scrutinee, consumed) = build_one_expr_at(children, 1)?;
    let arms_pos = 1 + consumed;
    if arms_pos + 1 != children.len() {
        return Err(parse_err("match requires scrutinee and arms", span));
    }
    let (bracket_items, bracket_span) = expect_bracket(&children[arms_pos])?;
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

/// Split an as-written trait name `module/Trait` into its `(module, name)` parts
/// for a `TraitRef`, mirroring [`type_ref_from_name`]. This is the §8.5
/// canonicalisation rule applied at the **trait-name** position of an `impl`:
/// a qualified trait (`(impl primitives/Num Int …)`) must arrive at typecheck as
/// `TraitRef { module: Some("primitives"), name: "Num" }`, not as the un-split
/// `TraitRef { module: None, name: "primitives/Num" }` (which would re-root the
/// trait under the current module the same way the impl-target defect did).
fn trait_ref_from_name(name: &str) -> TraitRef {
    match name.rsplit_once('/') {
        Some((m, n)) if !m.is_empty() && !n.is_empty() => {
            TraitRef::new(Some(ModuleFullPath::from(m)), TraitName::from(n))
        }
        _ => TraitRef::new(None, TraitName::from(name)),
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

/// Build a method-signature return type. A return type is a type expression
/// (spec/07-traits.md §7.1 — `self`, a named type, an applied type, or a type
/// variable), written either bare (`Int`) or with the annotation colon
/// (`:Int`, `:primitives/Int`).
///
/// For a colon-prefixed **named** return type (`:Int`, `:primitives/Int` —
/// uppercase after any final `/`), strip the annotation colon and route the
/// remaining name through `parse_annotation_name` so a qualified return type is
/// canonicalised through the §8.5 splitter — exactly as the param-annotation
/// path already does — rather than reaching `type_ref_from_name` with the colon
/// still attached (which would make the module side `:primitives` and yield
/// "unknown type"). The colon-prefixed **type-variable** form (`:a`) is left to
/// `build_type_expr` unchanged: it stays a `TypeExpr::TypeVar` carrying the
/// as-written token, preserving the established return-type-var display. Compound
/// annotation forms (`(Fn …)`, `(Option self)`) and bare type expressions also
/// fall through to `build_type_expr`.
fn build_ret_type(sexp: &Sexp) -> Result<TypeExpr, CranelispError> {
    if let Sexp::Symbol(s, _) = sexp
        && let Some(rest) = s.strip_prefix(':')
        && !rest.is_empty()
        && is_uppercase_start(rest)
    {
        return Ok(parse_annotation_name(rest));
    }
    build_type_expr(sexp)
}

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
mod tests;
