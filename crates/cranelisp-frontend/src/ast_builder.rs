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

/// The ONE qualified-name splitter for the frontend (audit R2, FIXME 0677).
///
/// A written name is qualified **iff** splitting at the LAST `/` yields two
/// NON-EMPTY halves — `Some((module, bare))`. A bare name, a bare `/` operator,
/// and a degenerate `foo/` / `/bar` all return `None` (Principle 16: punctuation
/// symbols are not special; a bare `/` is the legitimate division-operator
/// name). This is the frontend twin of `cranelisp_types::resolve::split_qualified`
/// (crate-private there — the frontend keeps its own copy rather than widen the
/// types-crate surface, no cross-crate need). Every place that used to hand-roll
/// `name.rsplit_once('/')` with the both-halves-non-empty guard
/// (`reject_qualified_binder_head`, `type_ref_from_name`, `trait_ref_from_name`,
/// the `type_expr_to_trait_ref` structural assert) delegates here so the split
/// grammar cannot drift across sites.
fn split_qualified_name(name: &str) -> Option<(&str, &str)> {
    name.rsplit_once('/')
        .filter(|(module, bare)| !module.is_empty() && !bare.is_empty())
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

/// Reject a qualified (slash-bearing) spelling in DECLARATION-HEAD position.
///
/// A declaration head is a binder, not a reference (spec/05-definitions.md §5,
/// "Declaration heads are binders") — it binds a NEW name into the CURRENT
/// module and MUST be a bare (unqualified) symbol. A qualified head (`fmt/foo`,
/// `fmt/Foo`) is a compile-time error; there is no mechanism for declaring a
/// name into another module. This is the exact dual of the §8.5 reference
/// splitters (`type_ref_from_name` / `trait_ref_from_name`) that split a
/// *reference* at the last `/`: a reference reaches across modules; a binder
/// never does.
///
/// Single-sourced (Principle 7) so every binder head site enforces the
/// identical rule — the sibling of [`reject_reserved_binder_name`]: one gates
/// reserved names (`trace`), one gates qualified spellings; both fire where
/// binder-ness is decided (Principle 18).
///
/// A name is qualified iff splitting at the LAST `/` yields two NON-EMPTY halves
/// — the exact guard the §8.5 reference splitters use (`type_ref_from_name` /
/// `trait_ref_from_name`), so this is their precise dual. The both-halves-
/// non-empty condition is load-bearing (Principle 16): a bare `/` is the
/// legitimate division-operator name (`(deftrait Num (/ [a b] self) …)`,
/// `stdlib/num/num.cl`), and `/`, `foo/`, `/bar` all split to an empty half and
/// are therefore NOT qualified — a coarse `contains('/')` would wrongly reject
/// the `/` operator binder. The predicate keys on `/` only: a dotted name
/// (`Point.x`) is a member/accessor form, never a raw declaration head, and
/// widening to `.` is out of scope (Principle 6).
pub(crate) fn reject_qualified_binder_head(name: &str, span: Span) -> Result<(), CranelispError> {
    if let Some((_module, bare)) = split_qualified_name(name) {
        return Err(parse_err(
            &format!(
                "'{name}' is a qualified name, but a definition head is a binder and must be a \
                 bare (unqualified) name — write '{bare}' (a definition binds into the current \
                 module; use an import/qualified reference to reach another module)"
            ),
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

/// The kind of a top-level form head. The ONE head-vocabulary classifier (audit
/// R3, FIXME 0678): every site that dispatches on a form head — `build_form_inner`
/// (per-form dispatch), `is_top_level_form_sexp` (build_form-vs-bare-expr
/// routing), and the test adapter — consumes [`classify_head`], so adding a
/// top-level head is exactly ONE edit here and the test router cannot drift from
/// the prod router (Principle 7).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum HeadKind {
    /// A definition form (`defn`/`deftype`/`deftrait`, with `-` = private):
    /// its `base` name (suffix stripped) and visibility.
    Def { base: &'static str, visibility: Visibility },
    /// `defmacro` / `defmacro-`.
    Defmacro,
    /// `impl` (no visibility variant).
    Impl,
    /// `begin` — a cluster the orchestrator must flatten before per-form dispatch.
    Begin,
    /// A module-phase structural declaration (`mod`/`mod-`/`import`/`export`/
    /// `platform`) the orchestrator must peel before per-form dispatch.
    StructuralDecl,
    /// Not a recognised top-level head — a bare expression / unknown form.
    Expr,
}

/// Classify a form head symbol. The single source of the top-level head
/// vocabulary (FIXME 0678).
pub(crate) fn classify_head(head: &str) -> HeadKind {
    match head {
        "defn" => HeadKind::Def { base: "defn", visibility: Visibility::Public },
        "defn-" => HeadKind::Def { base: "defn", visibility: Visibility::Private },
        "deftype" => HeadKind::Def { base: "deftype", visibility: Visibility::Public },
        "deftype-" => HeadKind::Def { base: "deftype", visibility: Visibility::Private },
        "deftrait" => HeadKind::Def { base: "deftrait", visibility: Visibility::Public },
        "deftrait-" => HeadKind::Def { base: "deftrait", visibility: Visibility::Private },
        "defmacro" | "defmacro-" => HeadKind::Defmacro,
        "impl" => HeadKind::Impl,
        "begin" => HeadKind::Begin,
        "mod" | "mod-" | "import" | "export" | "platform" => HeadKind::StructuralDecl,
        _ => HeadKind::Expr,
    }
}

/// True when `head` names a top-level definition/impl/macro form — the routing
/// predicate that sends a sexp to [`build_form`] rather than [`build_expr`].
/// Structural decls and `begin` are NOT included: they are peeled/flattened by
/// the orchestrator before dispatch (they answer `false` here). Single-sourced
/// via [`classify_head`] (FIXME 0678) so `build_forms` and the test adapter
/// share the ONE router.
pub(crate) fn head_is_top_level_form(head: &str) -> bool {
    matches!(
        classify_head(head),
        HeadKind::Def { .. } | HeadKind::Defmacro | HeadKind::Impl
    )
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
    // Desugar the reader-quote family (`quote`/`quasiquote`/`unquote`/
    // `unquote-splicing`) as the FIRST step, before head-shape dispatch, so
    // quote/quasiquote are legal wherever an expression is legal (spec §9.4.4;
    // `design/frontend/quasiquote-fold.md` §1). Idempotent fixpoint (§2): one
    // pass leaves no quote head, so a caller that already desugared (the
    // `macro_clause.rs` synthesis path) re-desugars harmlessly.
    let desugared = crate::quasiquote::expand_quasiquotes(sexp)?;
    build_form_inner(&desugared)
}

/// The per-form dispatch core. Assumes its input is already
/// quasiquote-desugared (the public [`build_form`] folds first; [`build_forms`]
/// desugars its whole slice up front and calls this directly). A surviving
/// `quote`/`quasiquote`/`unquote`/`unquote-splicing` head reaching the AST
/// builder via this core is caught by the [`build_list_expr`] backstop (§3).
fn build_form_inner(sexp: &Sexp) -> Result<Vec<ParsedEntry>, CranelispError> {
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

    // Dispatch on the ONE head classifier (FIXME 0678). Pre-AST forms
    // (`begin` / structural decls) are the orchestrator's responsibility and
    // are rejected here to surface the missing peel/flatten step early.
    match classify_head(head) {
        HeadKind::Begin => Err(parse_err(
            "build_form: `(begin …)` must be flattened by the orchestrator before per-form dispatch",
            head_span,
        )),
        HeadKind::StructuralDecl => Err(parse_err(
            "build_form: structural declarations must be peeled by `extract_module_declarations` before per-form dispatch",
            head_span,
        )),
        HeadKind::Defmacro => {
            let info = parse_defmacro(sexp)?;
            Ok(vec![ParsedEntry::Macro { info }])
        }
        HeadKind::Impl => parse_impl(children, span).map(|e| vec![e]),
        HeadKind::Def { base, visibility } => match base {
            "defn" => parse_defn(children, span, visibility).map(|e| vec![e]),
            "deftype" => parse_deftype(children, span, visibility),
            "deftrait" => parse_deftrait(children, span, visibility).map(|e| vec![e]),
            _ => unreachable!("invariant: classify_head returns a known Def base"),
        },
        HeadKind::Expr => Err(parse_err(
            &format!("unknown top-level form: `{head}`"),
            head_span,
        )),
    }
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
    // Desugar the reader-quote family over the whole slice ONCE, up front —
    // before `:Type` pairing and per-form dispatch (spec §9.4.4;
    // `design/frontend/quasiquote-fold.md` §1.1). `expand_quasiquotes`
    // preserves structure (each slice element maps to exactly one element, and
    // a leading `:Type` annotation atom is untouched), so desugar-then-pair is
    // order-safe (BC §1 invariant 9). Dispatch below runs on the desugared vec
    // and calls `build_form_inner` (already desugared — no redundant re-walk).
    let desugared: Vec<Sexp> = sexps
        .iter()
        .map(crate::quasiquote::expand_quasiquotes)
        .collect::<Result<Vec<_>, _>>()?;
    let sexps = &desugared[..];
    let mut out: Vec<TopLevel> = Vec::with_capacity(sexps.len());
    let mut i = 0;
    while i < sexps.len() {
        // A leading `:Type` pairs with the FOLLOWING form (BC §1 invariant 9).
        // `build_one_expr_at` performs the pairing over the sexp slice; when
        // `sexps[i]` is not an annotation it builds exactly like `build_expr`,
        // so the non-annotated path below handles the per-form dispatch that
        // `build_one_expr_at`'s plain-`build_expr` arm cannot (it has no
        // knowledge of top-level forms).
        if try_consume_annotation(sexps, i)?.is_some() {
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
            for entry in build_form_inner(sexp)? {
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
/// [`build_form`] or treat it as a bare expression. The head vocabulary is
/// single-sourced via [`head_is_top_level_form`] → [`classify_head`] (FIXME
/// 0678) — the test adapter routes through the SAME predicate, so the two
/// routers cannot drift.
pub(crate) fn is_top_level_form_sexp(sexp: &Sexp) -> bool {
    if let Sexp::List(children, _) = sexp
        && let Some(Sexp::Symbol(head, _)) = children.first()
    {
        return head_is_top_level_form(head);
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
            "percent parameters (`%1`, `%&`) are not yet supported — write an \
             explicit `(fn [x] …)` with named parameters",
            span,
        ));
    }
    if name.starts_with('$') {
        return Err(parse_err(
            "gensym (`$name`) is not yet supported — use a `let`-bound name",
            span,
        ));
    }
    if name.starts_with('&') {
        return Err(parse_err(
            "rest parameters (`&rest`) are not yet supported in expression \
             position — write explicit fixed parameters",
            span,
        ));
    }
    if name.ends_with('#') {
        return Err(parse_err(
            "auto-gensym shorthand (`name#`) is not yet supported — use a \
             `let`-bound name",
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
            // A `defn`/`defn-` head — and, via `build_impl_method`, an impl-body
            // method-defn head — is a binder, so a qualified spelling is a
            // compile-time error (spec §5; S1). One seam covers both callers.
            reject_qualified_binder_head(name, *span)?;
            Ok(name.as_str().into())
        }
        _ => Err(parse_err("expected function name", sexp.span())),
    }
}

fn build_defn_variant(sexp: &Sexp) -> Result<DefnVariant, CranelispError> {
    let (children, span) = expect_list(sexp)?;
    if children.len() < 2 {
        return Err(parse_err("defn variant requires params and body", span));
    }
    let params = build_annotated_params(&children[0])?;
    // The clause body may carry a `:Type body` ascription (BC §1 invariant 9;
    // spec §2.3.8 — `:Type` binds the immediately-following form in ALL
    // positions, so a multi-arity clause body parses like the single-arity
    // body, FV-6). Route it through the annotation-pairing primitive rather
    // than a raw `build_expr` (0591 AP-1).
    let (body, consumed) = build_one_expr_at(children, 1)?;
    if 1 + consumed != children.len() {
        return Err(parse_err("defn variant requires params and body", span));
    }
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
        Sexp::Symbol(name, span) if is_uppercase_start(name) => {
            // A `deftype`/`deftype-` head is a binder (spec §5; S2, bare arm) —
            // a qualified spelling is a compile-time error.
            reject_qualified_binder_head(name, *span)?;
            Ok((TypeName::from(name.as_str()), vec![]))
        }
        Sexp::List(children, span) => {
            if children.is_empty() {
                return Err(parse_err("empty type head", *span));
            }
            let (name, name_span) = expect_symbol(&children[0])?;
            // The head NAME of the `(Name params…)` arm is the binder (spec §5;
            // S2, list arm) — reject a qualified spelling before it re-roots
            // under the current module via `TypeName::from`.
            reject_qualified_binder_head(name, name_span)?;
            // The parenthesized head name must start uppercase, the SAME rule the
            // bare `Symbol` arm enforces via its match guard (spec §5.2 — a type
            // name is uppercase). Without this the list arm silently accepted a
            // lowercase head `(deftype (point a) …)` while the bare form
            // `(deftype point …)` was correctly rejected (audit S113 finding 2).
            if !is_uppercase_start(name) {
                return Err(parse_err("type name must start with uppercase", name_span));
            }
            let params: Vec<Symbol> = children[1..]
                .iter()
                .map(|s| {
                    let (n, n_span) = expect_symbol(s)?;
                    // A `deftype` type parameter is a type VARIABLE and MUST be a
                    // lowercase symbol (spec §2.2.2 `type_param = SYMBOL
                    // (* lowercase *)`; §2.4.2 — an uppercase symbol is a
                    // named-type reference, not a parameter binder). This
                    // converges deftype onto the SAME case rule
                    // `parse_trait_head_shape` already enforces for deftrait
                    // con-vars (M2-TP1/M2-TP2, audit R1 Done criterion). A
                    // silently-accepted uppercase param was the §2.2.2
                    // `class=silent-accept` defect.
                    if is_uppercase_start(n) {
                        return Err(parse_err(
                            &format!(
                                "type parameter `{n}` must be a lowercase symbol (a type \
                                 variable); an uppercase name is a named-type reference, not a \
                                 parameter (spec §2.2.2)"
                            ),
                            n_span,
                        ));
                    }
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
        Sexp::Symbol(name, span) if is_uppercase_start(name) => {
            // A constructor name is a binder (spec §5.2.2, user ruling 2026-07-19)
            // — it mints a module-level callable, so a qualified spelling
            // `(deftype Shape fmt/Circle)` is a compile-time error (span at the
            // ctor name). `is_uppercase_start` keys on the after-slash segment, so
            // `fmt/Circle` reaches this arm; reject it here (0660 cell (b)).
            reject_qualified_binder_head(name, *span)?;
            Ok(ConstructorDef {
                name: name.as_str().into(),
                docstring: None,
                fields: vec![],
                span: *span,
            })
        }
        // Data or nullary-with-doc: (UpperName "doc"? [fields]?)
        Sexp::List(children, span) => {
            if children.is_empty() {
                return Err(parse_err("empty constructor", *span));
            }
            let (name, name_span) = expect_symbol(&children[0])?;
            // A constructor name is a binder (spec §5.2.2) — a qualified spelling
            // `(deftype Shape (fmt/Circle …))` rejects here, span at the ctor name
            // (0660 cell (b)). Checked BEFORE the uppercase rule so a qualified
            // name names the qualified fault regardless of its after-slash case.
            reject_qualified_binder_head(name, name_span)?;
            // A constructor name must start uppercase (spec §5.2), the SAME rule
            // the bare-nullary arm enforces via its match guard. Without this the
            // list arm silently accepted a lowercase parenthesized constructor
            // `(deftype Shape (circle [:Int r]))` — callable but UNMATCHABLE in
            // patterns (patterns dispatch on uppercase constructor names). Located
            // at the name element, fix-naming (0660 cell (a)).
            if !is_uppercase_start(name) {
                let cap = {
                    let mut chars = name.chars();
                    match chars.next() {
                        Some(first) => {
                            first.to_uppercase().collect::<String>() + chars.as_str()
                        }
                        None => name.to_string(),
                    }
                };
                return Err(parse_err(
                    &format!(
                        "constructor name `{name}` must start with uppercase so it is \
                         matchable in patterns (spec §5.2) — write `{cap}`"
                    ),
                    name_span,
                ));
            }
            let (docstring, next) = extract_optional_docstring(children, 1);

            let fields = if next < children.len() {
                match &children[next] {
                    Sexp::Bracket(..) => {
                        let fields = build_field_list(&children[next])?;
                        // A constructor is `( name docstring? field_list )` —
                        // NOTHING follows the field bracket (spec §5.2 grammar).
                        // A form after a VALID `[:Type name]` bracket was silently
                        // dropped (`(deftype Box (Box [:Int n] extra))` collapsed
                        // to a one-field `Box`). Reject it located — the
                        // constructor-position sibling of BD-A2, mirroring the
                        // `other =>` arm below and `parse_defn`'s trailing reject.
                        if next + 1 != children.len() {
                            return Err(parse_err(
                                &format!(
                                    "constructor `{name}` has an unexpected trailing form after \
                                     its field list — a constructor is `({name} [:Type name])` \
                                     with nothing after the field bracket (spec §5.2)"
                                ),
                                children[next + 1].span(),
                            ));
                        }
                        fields
                    }
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
        if let Some((te, consumed)) = try_consume_annotation(items, i)? {
            let name_pos = i + consumed;
            if name_pos >= items.len() {
                return Err(parse_err(
                    "field type annotation missing field name",
                    items[i].span(),
                ));
            }
            let (name, name_span) = expect_symbol(&items[name_pos])?;
            // A field name is a binder — it mints a module-level `Type.field`
            // accessor (spec §5.2.6, user ruling 2026-07-19) — so a qualified
            // field name `(deftype T [:Int fmt/r])` is a compile-time error, span
            // at the field name (0660 field-cell).
            reject_qualified_binder_head(name, name_span)?;
            fields.push(FieldDef {
                name: name.into(),
                type_expr: te,
                span: name_span,
            });
            i = name_pos + 1;
        } else {
            // Bare name -- shortcut syntax (fresh type var)
            let (name, name_span) = expect_symbol(&items[i])?;
            // Field name is a binder (spec §5.2.6) — qualified rejects here too.
            reject_qualified_binder_head(name, name_span)?;
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

/// Parse the STRUCTURAL shape of a trait head — the `deftrait` head (spec §7.2)
/// AND the `impl` slot-1 echoed head (spec §7.3). Single-sourced so
/// `build_trait_head` and `parse_impl` cannot drift on what a legal head *looks
/// like* (Principle 7): spec §7.3 states the `impl` slot-1 shape **is** the
/// `deftrait` head shape, so one grammar governs both.
///
/// Accepts exactly two shapes:
///   - bare `Symbol` (uppercase)         → `(name, None)`            — kind `*`
///   - 2-element `(UpperSymbol con_var)` → `(name, Some((var,span)))` — HK head
///
/// Structural ONLY — it enforces the shape, the uppercase-head rule, and the
/// lowercase-con_var rule (spec §7.2 `con_var = lowercase_symbol`; /qa F2
/// ruling S112, `tests/plan/s112-0628-ic-wave.md` §7.2 — the ONE seam covering
/// BOTH head parsers, closing the two-parser drift window). It does NO
/// name-resolution and NO kind classification: it returns the raw head name
/// **unsplit**, and each caller applies its own §8.5 policy (`build_trait_head`
/// keeps the name in its home module; `parse_impl` applies the D-qual splitter).
///
/// Diagnostics are phrased **neutrally** ("trait head") rather than
/// caller-specific ("impl head") so the one message reads correctly for both
/// callers and stays single-sourced (design/frontend/trait-impl-head-parse.md §4
/// note — the explicitly-sanctioned option). Every rejection is located and
/// names the fix.
fn parse_trait_head_shape(
    sexp: &Sexp,
) -> Result<(&str, Span, Option<(Symbol, Span)>), CranelispError> {
    match sexp {
        Sexp::Symbol(name, span) => {
            if !is_uppercase_start(name) {
                return Err(parse_err("trait name must start with uppercase", *span));
            }
            Ok((name.as_str(), *span, None))
        }
        Sexp::List(children, span) => {
            if children.is_empty() {
                return Err(parse_err(
                    "empty trait head — write the bare trait name, or `(Trait con_var)`",
                    *span,
                ));
            }
            // The head element must be a bare uppercase symbol — checked BEFORE
            // arity so a non-symbol head (`((Functor f))`) names that fault
            // rather than an arity one (design §4 table).
            let (name, name_span) = match &children[0] {
                Sexp::Symbol(n, sp) => (n.as_str(), *sp),
                _ => {
                    return Err(parse_err(
                        "trait name must be a bare symbol",
                        children[0].span(),
                    ));
                }
            };
            if !is_uppercase_start(name) {
                return Err(parse_err(
                    "trait name must start with uppercase",
                    name_span,
                ));
            }
            match children.len() {
                1 => Err(parse_err(
                    "higher-kinded trait head is missing its constructor variable — write `(Trait con_var)`, e.g. `(Functor f)`",
                    *span,
                )),
                2 => {
                    // con_var: a lowercase symbol (spec §7.2 `con_var =
                    // lowercase_symbol`).
                    let (var, var_span) = match &children[1] {
                        Sexp::Symbol(v, sp) => (v.as_str(), *sp),
                        _ => {
                            return Err(parse_err(
                                "constructor variable must be a symbol — write a name, e.g. `(Functor f)`",
                                children[1].span(),
                            ));
                        }
                    };
                    if is_uppercase_start(var) {
                        return Err(parse_err(
                            "constructor variable must start with lowercase — write `(Trait con_var)`, e.g. `(Functor f)`",
                            var_span,
                        ));
                    }
                    // A con_var is a BARE lowercase binder (spec §7.2 `con_var =
                    // lowercase_symbol`; BD-M4). The uppercase gate above keys on
                    // the after-slash segment, so a slash-bearing con_var
                    // (`prim/x`) slips past it — reject it as a qualified binder.
                    // This lives in the SHARED shape parser because a con_var is a
                    // binder in BOTH `deftrait` and the `impl` echoed head.
                    reject_qualified_binder_head(var, var_span)?;
                    Ok((name, name_span, Some((Symbol::from(var), var_span))))
                }
                _ => Err(parse_err(
                    "too many elements in trait head — a higher-kinded head is `(Trait con_var)`",
                    *span,
                )),
            }
        }
        _ => Err(parse_err(
            "expected trait name or `(Trait con_var)`",
            sexp.span(),
        )),
    }
}

/// Parse a trait head: either `TraitName` or `(TraitName var)`.
/// Returns (trait_name, type_params, optional_hkt_param_name).
///
/// Shares the head-shape grammar with `parse_impl` via
/// [`parse_trait_head_shape`] (Principle 7); the deftrait-specific name policy —
/// keep the name in its home module (`TraitName::from`, no §8.5 split) and fold
/// the con_var into `type_params` + `hkt_param_name` — stays here.
fn build_trait_head(sexp: &Sexp) -> Result<(TraitName, Vec<Symbol>, Option<Symbol>), CranelispError> {
    let (name, name_span, con_var) = parse_trait_head_shape(sexp)?;
    // A `deftrait`/`deftrait-` head is a binder (spec §5; S3) — reject a
    // qualified spelling. This is the deftrait-CALLER policy: it lives here, not
    // in the shared shape parser, because `impl` slot-1 echoes a trait
    // REFERENCE (a qualified spelling there is legal — the D-qual splitter
    // handles it — see `parse_impl`), exactly as `TraitName::from` (home-module,
    // no split) already contrasts with the impl side's `trait_ref_from_name`.
    reject_qualified_binder_head(name, name_span)?;
    match con_var {
        None => Ok((TraitName::from(name), vec![], None)),
        Some((var, _span)) => Ok((TraitName::from(name), vec![var.clone()], Some(var))),
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

    let (name, name_span) = expect_symbol(&children[0])?;
    // A deftrait method-signature name introduces a method name into scope
    // (spec §5.3.3; S5) — it is a binder, so a qualified spelling is rejected.
    reject_qualified_binder_head(name, name_span)?;
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
        // `if`, `match`, …) immediately, rather than per-impl. The default body
        // is a single-body operand position: `:Type body` ascription valid
        // (spec §2.3.8), a trailing form after it rejected located (BD-A1/A2).
        // ONE seam.
        Some(build_body_to_end(children, ret_pos + 1, "trait default method body")?)
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
    // (impl <head> impl_target method_def+)
    //   <head>      = TraitName | (TraitName con_var)   -- spec §7.2/§7.3
    //   impl_target = Type | (Type :Constraint var ...) -- slot 2, unchanged
    //
    // Slot 1 admits BOTH head shapes (S112 b0): the bare conventional head
    // (kind `*`, `head_con_var: None`) and the higher-kinded echo-the-head form
    // `(Functor f)` (`head_con_var: Some("f")` — the written con_var recorded
    // VERBATIM as a shape bit only). The parser does NO kind classification and
    // NO echo validation against the trait declaration — whether slot 1's shape
    // matches the trait's declared kind is checked at typecheck's ONE §7.3.5
    // Case-3 seam, the single site holding the trait declaration (a second
    // parser-side classifier could only ever agree with it — spec §7.3.5,
    // Principle 24 "resolve once"). Slot 2 rides the existing `build_impl_target`
    // path untouched; `(Functor Option)` parses to `Applied` like any type
    // application and is kind-interpreted only at that same Case-3 seam.
    if children.len() < 4 {
        return Err(parse_err(
            "impl requires trait name, target type, and at least one method",
            span,
        ));
    }

    // Slot 1: the echoed head shape (single-sourced with `deftrait` via
    // `parse_trait_head_shape`, Principle 7). The impl-side name policy — apply
    // the §8.5 D-qual splitter to a qualified echoed head (`(fmt/Functor f)`) —
    // stays here, mirroring the deftrait side's home-module policy.
    // Slot 1 is a trait REFERENCE, not a binder: a qualified echoed head
    // (`(fmt/Functor f)`) is legal and the §8.5 D-qual splitter re-homes it, so
    // NO `reject_qualified_binder_head` here (the shared shape parser's name span
    // is discarded). The con_var reject inside `parse_trait_head_shape` DOES
    // apply — a con_var is a binder in both forms (BD-M4).
    let (head_name, _head_name_span, con_var) = parse_trait_head_shape(&children[1])?;
    let trait_name = trait_ref_from_name(head_name);
    let head_con_var = con_var.map(|(var, _span)| var);

    let (target, type_constraints) = build_impl_target(&children[2])?;

    let methods = children[3..]
        .iter()
        .map(build_impl_method)
        .collect::<Result<Vec<_>, _>>()?;

    Ok(ParsedEntry::TraitImpl {
        impl_: TraitImpl {
            head_con_var,
            trait_name,
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
                        let (var_name, var_span) = expect_symbol(&children[i])?;
                        // The constrained type variable in `(Type :Constraint var)`
                        // is a type-var BINDER (the constraint binds to it), so a
                        // qualified spelling (`:Eq mod/a`) is a qualified binder —
                        // rejected exactly as a slash-bearing con_var is (spec §7.2,
                        // design §3.1). Routing to `Named` is NOT an option here: the
                        // constraint pair below must be keyed on a BARE var name, and
                        // binding a type var into another module is nonsensical.
                        reject_qualified_binder_head(var_name, var_span)?;
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
                        // is canonical — split through the shared splitter. A
                        // qualified-LOWERCASE arg (`(Pair mod/x)`) is likewise NOT a
                        // bare type var (spec §3.3) — route it through the splitter to
                        // `Named` rather than mint a slash-carrying `TypeVar`
                        // (Principle 18, FIXME 0589; the same routing the other
                        // type-var decision points apply).
                        let arg = if is_uppercase_start(s) || s.contains('/') {
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
    // The impl-method body is a single-body operand position: `:Type body`
    // ascription valid (spec §2.3.8), a trailing form rejected located (mirrors
    // `parse_defn`, closing the BD-A2 silent-drop). ONE seam.
    let body = build_body_to_end(children, 3, "impl method body")?;

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
                    "anonymous-function shorthand `#(…)` is not yet supported — \
                     write an explicit `(fn [x] …)`",
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
                return Err(parse_err(
                    "`par-let` is not yet supported — use a sequential `let`",
                    *head_span,
                ))
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
    // The traced operand is a single-body operand position: it may carry a
    // `:Type body` ascription (spec §2.3.8 — `(trace :Int 5)`) and rejects a
    // trailing form. Route through the ONE seam; a missing operand `(trace)`
    // reports "trace: missing body expression", a trailing `(trace x y)`
    // reports "trace: unexpected trailing form after body" (clearer than the
    // former blanket arity error).
    let body = build_body_to_end(children, 1, "trace")?;
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
    if children.len() < 3 {
        return Err(parse_err("let requires bindings and body", span));
    }
    let (bracket_items, _) = expect_bracket(&children[1])?;
    let bindings = build_let_bindings(bracket_items)?;
    // The let BODY is a single-body operand position: it may carry a `:Type body`
    // ascription (spec §2.3.8 — `(let [x 1] :Int x)`) and rejects a trailing form
    // located. ONE seam (`build_body_to_end`) for every single-body position.
    let body = build_body_to_end(children, 2, "let body")?;
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
        // A `let` binding name is a value-level binder (spec §5 binder-positions
        // table) — a qualified spelling `[a/b 5]` is a compile-time error. Sound
        // since 0670 (int's expansion pass skips binder slots), so the reject
        // fires only on the user's WRITTEN qualified spelling, never int's
        // output. Re-landed S114 W-D2 (same helper, Principle 7).
        reject_qualified_binder_head(name, name_span)?;
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
    // (if cond then else) — each of the three operands may carry a `:Type form`
    // ascription (spec §2.3.8 — `:Type` binds the immediately-following form in
    // ALL positions, an `if` branch included). Consume each through the
    // annotation-pairing primitive (0591 AP-4) rather than a positional
    // `children[n]` that a leading annotation would offset.
    let arity_err = || parse_err("if requires condition, then, and else branches", span);
    let mut pos = 1;
    if pos >= children.len() {
        return Err(arity_err());
    }
    let (cond, c) = build_one_expr_at(children, pos)?;
    pos += c;
    if pos >= children.len() {
        return Err(arity_err());
    }
    let (then_branch, c) = build_one_expr_at(children, pos)?;
    pos += c;
    if pos >= children.len() {
        return Err(arity_err());
    }
    let (else_branch, c) = build_one_expr_at(children, pos)?;
    pos += c;
    if pos != children.len() {
        return Err(arity_err());
    }
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
    if children.len() < 3 {
        return Err(parse_err(
            "fn is single-arity: it takes one [params] bracket and a body \
             (use defn for multiple arities, spec §4.5)",
            span,
        ));
    }
    let params = build_annotated_params(&children[1])?;
    // The body may carry a `:Type body` ascription (spec §2.3.8 — `:Type` binds
    // the immediately-following form in ALL positions; the `fn` body is not
    // special). Route it through the annotation-pairing primitive (0591 AP-2).
    let (body, consumed) = build_one_expr_at(children, 2)?;
    if 2 + consumed != children.len() {
        return Err(parse_err(
            "fn is single-arity: it takes one [params] bracket and a body \
             (use defn for multiple arities, spec §4.5)",
            span,
        ));
    }
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
    let (bracket_items, _bracket_span) = expect_bracket(&children[arms_pos])?;
    // No fixed parity check: an arm BODY may carry a `:Type body` ascription
    // (spec §2.3.8), so `pattern body` is not always a 2-token pair. The
    // consume-based `build_match_arms` loop reports an unpaired final pattern as
    // "match arm missing body" (0591 AP-3).
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
        // The arm body may carry a `:Type body` ascription (spec §2.3.8) — one
        // or two tokens. Route it through the annotation-pairing primitive so
        // the body groups into ONE `Expr::Annotate` (0591 AP-3).
        let (body, consumed) = build_one_expr_at(items, i)?;
        let body_end = items[i + consumed - 1].span().end;
        let arm_span = Span::new(pat_span.start, body_end);
        i += consumed;
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
                // A bare lowercase pattern symbol is a variable binder (spec
                // §6.2.4) — a qualified spelling `a/b` is a compile-time error.
                // Sound since 0670 (int's expansion pass skips binder slots), so
                // the reject fires only on the user's WRITTEN qualified spelling,
                // never int's output. Re-landed S114 W-D2.
                reject_reserved_binder_name(name, *span)?;
                reject_qualified_binder_head(name, *span)?;
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
            // children[0] is the constructor name (a REFERENCE, not a binder —
            // qualifier permitted, spec §6.2.1). The remaining symbols are variable
            // binders (spec §6.2.4): a qualified spelling `a/b` is a compile-time
            // error (re-landed S114 W-D2; sound since 0670 skips binder slots in
            // int's expansion pass — fires only on the written qualified spelling).
            let bindings = children[1..]
                .iter()
                .map(|s| {
                    let (n, n_span) = expect_symbol(s)?;
                    reject_reserved_binder_name(n, n_span)?;
                    reject_qualified_binder_head(n, n_span)?;
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
///
/// Returns `Ok(Some((TypeExpr, items_consumed)))` when `items[pos]` is an
/// annotation introducer, `Ok(None)` when it is not, and `Err` when it IS an
/// introducer (a bare `:`) but the form it binds is not a type expression.
///
/// A bare `:` token is **only ever** an annotation introducer (never a `Var`;
/// crate `CLAUDE.md` §`:Type`), so the form it binds MUST parse as a type
/// expression. The bare-`:` arm therefore raises a LOCATED reject naming the fix
/// rather than swallowing a `build_type_expr` failure and letting `:` fall
/// through to `Expr::Var{ name: ":" }` (the opaque "unresolved symbol `:`"
/// degradation — RA-N5, spec §2.3.8).
fn try_consume_annotation(
    items: &[Sexp],
    pos: usize,
) -> Result<Option<(TypeExpr, usize)>, CranelispError> {
    if pos >= items.len() {
        return Ok(None);
    }
    match &items[pos] {
        // `:Int`, `:a`, `:Num` -- simple colon-prefixed symbol
        Sexp::Symbol(s, _) if s.starts_with(':') && s.len() > 1 => {
            let name = &s[1..];
            let te = parse_annotation_name(name);
            Ok(Some((te, 1)))
        }
        // `:` followed by `(Fn [...] ret)` or `(Option a)` etc -- compound annotation
        Sexp::Symbol(s, sp) if s == ":" => {
            if pos + 1 >= items.len() {
                // Trailing bare `:` with nothing to bind — not an annotation here;
                // downstream `build_expr` reports "annotation missing expression".
                return Ok(None);
            }
            match build_type_expr(&items[pos + 1]) {
                Ok(te) => Ok(Some((te, 2))),
                Err(_) => Err(parse_err(
                    &format!(
                        "the form bound by `:` must be a type expression; found `{}`",
                        items[pos + 1].format_flat()
                    ),
                    *sp,
                )),
            }
        }
        _ => Ok(None),
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
    match split_qualified_name(name) {
        Some((m, n)) => TypeRef::new(Some(ModuleFullPath::from(m)), TypeName::from(n)),
        None => TypeRef::new(None, TypeName::from(name)),
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
    match split_qualified_name(name) {
        Some((m, n)) => TraitRef::new(Some(ModuleFullPath::from(m)), TraitName::from(n)),
        None => TraitRef::new(None, TraitName::from(name)),
    }
}

fn parse_annotation_name(name: &str) -> TypeExpr {
    if name == "self" {
        TypeExpr::SelfType
    } else if is_uppercase_start(name) || name.contains('/') {
        // A qualified-lowercase annotation (`user/int`) is NOT a bare type var
        // (spec §3.3 — a type var is a bare lowercase identifier), so route it
        // through the §8.5 splitter (which peels the module) rather than minting
        // a `TypeVar` that carries the slash: a `TypeVar` must NEVER carry a `/`
        // (Principle 18, FIXME 0589). The unknown-type error then names the
        // module. `Named` above already covers the uppercase (`mod/Type`) case;
        // this arm adds the qualified-lowercase case.
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
    if let Some((annotation, consumed)) = try_consume_annotation(items, pos)? {
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

/// Build the single trailing body-expression at `children[pos..]`, routing it
/// through the annotation-pairing primitive (so `:Type body` ascription works —
/// spec §2.3.8) and rejecting any form left after it (so `(form … body junk)` is
/// a LOCATED error, not a silent drop).
///
/// The ONE seam for every single-body operand position — let-body,
/// impl-method body, trait-default body, `trace` operand
/// (`design/frontend/enforcement-matrices.md` §1; Principle 7 single-source,
/// Principle 18 enforce-where-built). Mirrors the tail-consumption discipline
/// `parse_defn` / `build_defn_variant` already have on their own bodies.
fn build_body_to_end(children: &[Sexp], pos: usize, ctx: &str) -> Result<Expr, CranelispError> {
    if pos >= children.len() {
        return Err(parse_err(
            &format!("{ctx}: missing body expression"),
            children.last().map(Sexp::span).unwrap_or(Span::SYNTHETIC),
        ));
    }
    let (expr, consumed) = build_one_expr_at(children, pos)?;
    if pos + consumed != children.len() {
        return Err(parse_err(
            &format!("{ctx}: unexpected trailing form after body"),
            children[pos + consumed].span(),
        ));
    }
    Ok(expr)
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
        if let Some((te, consumed)) = try_consume_annotation(items, i)? {
            // Accumulate the RUN of consecutive annotations preceding the binder
            // name. A `:Type`/`:Trait` annotation is reader-macro-like — it binds
            // the immediately-following form (FIXME 0341,
            // `memory/annotation-reader-macro-binds-following-form.md`), so a run
            // of stacked annotations all attach to the one binder that terminates
            // the run. The single-annotation case is the run-of-length-1.
            let mut run: Vec<TypeExpr> = vec![te];
            let mut name_pos = i + consumed;
            while let Some((te, consumed)) = try_consume_annotation(items, name_pos)? {
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
            // A `defn`/`fn`/`defmacro` param is a value-level binder (spec §5
            // binder-positions table) — a qualified spelling `[a/b]` is a
            // compile-time error, same seam/helper as the §5 native heads. Sound
            // to enforce here since 0670 (int's expansion pass now SKIPS binder
            // slots, so int never mangles a colliding binder into a qualified
            // name — a bare `name` reaches here unmangled; the reject fires only
            // on the user's WRITTEN qualified spelling). Re-landed S114 W-D2.
            reject_qualified_binder_head(name, name_span)?;
            params.push((name.into(), Some(annotation_run_carrier(run))));
            i = name_pos + 1;
        } else {
            let (name, name_span) = expect_symbol(&items[i])?;
            reject_reserved_binder_name(name, name_span)?;
            reject_qualified_binder_head(name, name_span)?;
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

/// Convert a parsed annotation `TypeExpr` (a stacked-bounds run element) to the
/// `TraitRef` carried by `TypeExpr::Bounds`. Trait annotations parse as
/// `Named`/`Applied` (uppercase `:Eq`, qualified `:fmt/Display`) or — defensively
/// — `TypeVar`. The module is already split off upstream; this only reshapes.
///
/// **No re-split here (P7).** Every name reaching this function is ALREADY
/// module-split: `Named`/`Applied` names come from the §8.5 splitter
/// (`type_ref_from_name`), and `parse_annotation_name` — the sole producer of a
/// run element's `TypeVar` (`try_consume_annotation`'s simple-`:Name` arm) —
/// never mints a slash-carrying `TypeVar` since FIXME 0589 (S113). The prior
/// hand-rolled `rsplit_once('/')` here was a THIRD splitter copy that existed
/// only to compensate for 0589's slash-carrying `TypeVar`; that input is now
/// impossible, so the copy is retired and the invariant is enforced structurally
/// (P18, `debug_assert`) rather than re-derived downstream.
fn type_expr_to_trait_ref(te: TypeExpr) -> TraitRef {
    let (module, name): (Option<&str>, &str) = match &te {
        TypeExpr::Named(r) | TypeExpr::Applied(r, _) => {
            (r.module.as_deref(), r.name.as_ref())
        }
        TypeExpr::TypeVar(s) => (None, s.as_ref()),
        TypeExpr::SelfType => (None, "Self"),
        TypeExpr::FnType(..) | TypeExpr::Bounds(_) => (None, ""),
    };
    // The invariant is the EXACT dual of the §8.5 splitter guard
    // (`split_qualified_name`): no *splittable* qualified spelling (two non-empty
    // halves) survives upstream. Since the S114 RA reader reject (0684,
    // `enforcement-matrices.md` §3.2), a written `foo/`/`/bar` is rejected at
    // tokenization, so only a bare `/` (the division operator) can reach the
    // splitters unsplit — `split_qualified_name` returns `None` for it (Principle
    // 16), so the assert holds without the stronger `!contains('/')`.
    debug_assert!(
        split_qualified_name(name).is_none(),
        "type_expr_to_trait_ref received a splittable qualified name `{name}` — the \
         §8.5 split must happen upstream (type_ref_from_name / parse_annotation_name), \
         never be re-derived here (P7/FIXME 0589)"
    );
    TraitRef::new(module.map(ModuleFullPath::from), TraitName::from(name))
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
            } else if is_uppercase_start(name) || name.contains('/') {
                // The SECOND type-var decision point (mirror of
                // `parse_annotation_name`, FIXME 0589): a qualified-lowercase
                // type-arg (`mod/x` in `(Option mod/x)` / `(Fn [mod/x] …)`) is
                // NOT a bare type var (spec §3.3), so route it through the §8.5
                // splitter (`Named`) — a `TypeVar` must never carry a `/`
                // (Principle 18, enforced where type-var-ness is decided, not
                // merely backstopped downstream). Uppercase `mod/Type` already
                // took this arm; this adds the qualified-lowercase case.
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
