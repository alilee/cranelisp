//! `defmacro` parsing and body synthesis — macro-resolver helpers.
//!
//! Parses `defmacro` forms from Sexp, extracts name/docstring/clauses,
//! and synthesizes function Sexps for each clause with argument
//! destructuring via nested match expressions. Also provides shape
//! recognisers ([`is_defmacro`], [`is_begin`]) and the
//! [`flatten_begin`] orchestration helper.
//!
//! These items are **internal-but-exposed** per the crate-root preamble
//! §"Macro-resolver helpers": pub at the crate root and via this module,
//! but not part of the four-free-function form-by-form boundary. They are
//! called directly by `int` (`src/process_form.rs`, `src/repl/commands.rs`,
//! `src/session_v4/index_worker.rs`) — a settled, permanent part of the
//! surface (`design/frontend/frontend.md` §9.1: `lib.rs` is correct, there
//! is NO "narrow back"). The former "narrow to `pub(crate)` at FIXME 0098
//! Phase 2 close" plan was withdrawn by S76 W-Macro, which DELETED `expand`
//! rather than migrating it — the conditioning event never happens.

use cranelisp_types::{CranelispError, ErrorLocation, MacroParam, Sexp, Span, Symbol};

use crate::synth;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

// `DefmacroInfo` and `MacroClause` are defined in `cranelisp_types::parsed`
// per FIXME 0156 (Sprint 66 Wave 0). They are re-exported through this
// module's public surface and through `cranelisp_frontend::lib.rs`.

pub use cranelisp_types::{DefmacroInfo, MacroClause};

// ---------------------------------------------------------------------------
// Form detection
// ---------------------------------------------------------------------------

/// Returns true if the sexp is `(defmacro ...)` or `(defmacro- ...)`.
///
/// Shape recogniser used by the orchestrator to route forms to the
/// correct per-shape handler before invoking [`parse_defmacro`].
pub fn is_defmacro(sexp: &Sexp) -> bool {
    if let Sexp::List(children, _) = sexp
        && let Some(Sexp::Symbol(head, _)) = children.first()
    {
        return head == "defmacro" || head == "defmacro-";
    }
    false
}

/// Returns true if the sexp is `(begin ...)`.
///
/// Shape recogniser. `begin` forms are pre-AST: they must be flattened
/// by [`flatten_begin`] before per-form `build_form` dispatch. The
/// `build_form` entry point rejects `begin` directly to surface the
/// missing flatten step early.
pub fn is_begin(sexp: &Sexp) -> bool {
    if let Sexp::List(children, _) = sexp
        && let Some(Sexp::Symbol(head, _)) = children.first()
    {
        return head == "begin";
    }
    false
}

/// Flatten nested `(begin ...)` forms into individual top-level forms.
/// Non-begin forms are returned as-is in a single-element vec.
///
/// Orchestrator-side helper: `build_form` does NOT accept `begin` forms
/// (it errors out to surface the missing flatten step). The orchestrator
/// must call `flatten_begin` on each parsed source form before per-form
/// dispatch; this allows nested `(begin (begin ...))` to fully unfold to
/// a flat sequence of definitions.
pub fn flatten_begin(sexp: Sexp) -> Vec<Sexp> {
    if is_begin(&sexp)
        && let Sexp::List(children, _) = sexp
    {
        return children
            .into_iter()
            .skip(1) // skip the `begin` symbol
            .flat_map(flatten_begin)
            .collect();
    }
    vec![sexp]
}

// ---------------------------------------------------------------------------
// Macro parameter parsing
// ---------------------------------------------------------------------------

/// Parse param items from a slice (used for both top-level and bracket patterns).
///
/// The reader parses `&rest` or `& rest` as a single symbol `"&rest"` (ampersand prefix),
/// so rest params appear as symbols starting with `&`.
fn parse_param_items(
    items: &[Sexp],
) -> Result<(Vec<MacroParam>, Option<Symbol>), CranelispError> {
    let mut fixed_params = Vec::new();
    let mut rest_param = None;
    let mut i = 0;

    while i < items.len() {
        match &items[i] {
            Sexp::Symbol(s, sym_span) if s.starts_with('&') && s.len() > 1 => {
                // Reader produces "&rest" as a single symbol.
                let rest_name = &s[1..];
                crate::ast_builder::reject_reserved_binder_name(rest_name, *sym_span)?;
                // A defmacro param is a local binder (spec §5 binder-positions
                // table) — a qualified spelling rejects.
                crate::ast_builder::reject_qualified_binder_head(rest_name, *sym_span)?;
                rest_param = Some(rest_name.into());
                i += 1;
            }
            Sexp::Symbol(pname, sym_span) => {
                crate::ast_builder::reject_reserved_binder_name(pname, *sym_span)?;
                crate::ast_builder::reject_qualified_binder_head(pname, *sym_span)?;
                fixed_params.push(MacroParam::Name(pname.as_str().into()));
                i += 1;
            }
            Sexp::Bracket(inner, _) => {
                let (bracket_fixed, bracket_rest) = parse_bracket_pattern(inner)?;
                fixed_params.push(MacroParam::Bracket {
                    fixed: bracket_fixed,
                    rest: bracket_rest,
                });
                i += 1;
            }
            other => {
                return Err(CranelispError::ParseError {
                    message: "defmacro param must be a symbol or bracket pattern".to_string(),
                    location: ErrorLocation::from_span(other.span()),
                });
            }
        }
    }
    Ok((fixed_params, rest_param))
}

/// Parse a bracket destructuring pattern's inner items.
///
/// The reader parses `&rest` or `& rest` as `"&rest"`, so rest params appear as
/// symbols starting with `&`.
fn parse_bracket_pattern(
    inner: &[Sexp],
) -> Result<(Vec<Symbol>, Option<Symbol>), CranelispError> {
    let mut fixed = Vec::new();
    let mut rest = None;
    let mut j = 0;

    while j < inner.len() {
        match &inner[j] {
            Sexp::Symbol(s, sym_span) if s.starts_with('&') && s.len() > 1 => {
                let rest_name = &s[1..];
                crate::ast_builder::reject_reserved_binder_name(rest_name, *sym_span)?;
                crate::ast_builder::reject_qualified_binder_head(rest_name, *sym_span)?;
                rest = Some(rest_name.into());
                j += 1;
            }
            Sexp::Symbol(pname, sym_span) => {
                crate::ast_builder::reject_reserved_binder_name(pname, *sym_span)?;
                crate::ast_builder::reject_qualified_binder_head(pname, *sym_span)?;
                fixed.push(pname.as_str().into());
                j += 1;
            }
            other => {
                return Err(CranelispError::ParseError {
                    message: "bracket destructuring param must be a symbol".to_string(),
                    location: ErrorLocation::from_span(other.span()),
                });
            }
        }
    }
    Ok((fixed, rest))
}

// ---------------------------------------------------------------------------
// defmacro parsing
// ---------------------------------------------------------------------------

/// Parse a `(defmacro name ...)` or `(defmacro- name ...)` form into
/// a [`DefmacroInfo`] carrier.
///
/// Handles both single-clause `(defmacro name [params] body)` and
/// multi-clause `(defmacro name ([params] body) ([params] body))`
/// syntax, with optional docstring.
///
/// Internal-but-exposed: pub at the crate root, called directly by `int`
/// (`src/process_form.rs`, `src/repl/commands.rs`, index worker) — a settled
/// part of the surface (`frontend.md` §9.1: no "narrow back").
///
/// `MacroParam`, `MacroClauseInfo`, and `DefmacroInfo` live in
/// `cranelisp-types` (they cross the typecheck boundary).
/// `DefmacroInfo` joined them per FIXME 0156 resolution.
pub fn parse_defmacro(sexp: &Sexp) -> Result<DefmacroInfo, CranelispError> {
    let (children, span) = match sexp {
        Sexp::List(children, span) => (children, *span),
        _ => {
            return Err(CranelispError::ParseError {
                message: "defmacro requires a list form".to_string(),
                location: ErrorLocation::from_span(sexp.span()),
            });
        }
    };

    if children.len() < 3 {
        return Err(CranelispError::ParseError {
            message: "defmacro requires at least name and one clause".to_string(),
            location: ErrorLocation::from_span(span),
        });
    }

    // Detect visibility from head form.
    let is_private = matches!(&children[0], Sexp::Symbol(head, _) if head == "defmacro-");

    // Extract name.
    let name: Symbol = match &children[1] {
        Sexp::Symbol(n, n_span) => {
            crate::ast_builder::reject_reserved_binder_name(n, *n_span)?;
            // A `defmacro`/`defmacro-` head is a binder (spec §5; S4) — reject a
            // qualified spelling.
            crate::ast_builder::reject_qualified_binder_head(n, *n_span)?;
            n.as_str().into()
        }
        _ => {
            return Err(CranelispError::ParseError {
                message: "defmacro name must be a symbol".to_string(),
                location: ErrorLocation::from_span(children[1].span()),
            });
        }
    };

    // Optional docstring after name.
    let (docstring, next_idx) = match &children[2] {
        Sexp::Str(s, _) => (Some(s.clone()), 3),
        _ => (None, 2),
    };

    if next_idx >= children.len() {
        return Err(CranelispError::ParseError {
            message: "defmacro requires params or clauses after name".to_string(),
            location: ErrorLocation::from_span(span),
        });
    }

    // Detect single-clause vs multi-clause.
    let clauses = match &children[next_idx] {
        Sexp::Bracket(items, _) => {
            // Single clause: (defmacro name [params] body)
            if next_idx + 1 >= children.len() {
                return Err(CranelispError::ParseError {
                    message: "defmacro requires a body after params".to_string(),
                    location: ErrorLocation::from_span(span),
                });
            }
            let (fixed_params, rest_param) = parse_param_items(items)?;
            vec![MacroClause {
                fixed_params,
                rest_param,
                body_sexp: children[next_idx + 1].clone(),
            }]
        }
        Sexp::List(..) => {
            // Multi-clause: (defmacro name ([params] body) ([params] body) ...)
            children[next_idx..]
                .iter()
                .map(parse_single_clause)
                .collect::<Result<Vec<_>, _>>()?
        }
        _ => {
            return Err(CranelispError::ParseError {
                message: "expected bracket params or clause list after defmacro name".to_string(),
                location: ErrorLocation::from_span(children[next_idx].span()),
            });
        }
    };

    Ok(DefmacroInfo::new(
        name,
        is_private,
        docstring,
        clauses,
        span,
    ))
}

/// Parse a single clause from `([params] body)`.
fn parse_single_clause(sexp: &Sexp) -> Result<MacroClause, CranelispError> {
    let (children, span) = match sexp {
        Sexp::List(children, span) => (children, *span),
        _ => {
            return Err(CranelispError::ParseError {
                message: "defmacro clause must be a list ([params] body)".to_string(),
                location: ErrorLocation::from_span(sexp.span()),
            });
        }
    };

    if children.len() != 2 {
        return Err(CranelispError::ParseError {
            message: "defmacro clause requires params and body".to_string(),
            location: ErrorLocation::from_span(span),
        });
    }

    let bracket_items = match &children[0] {
        Sexp::Bracket(items, _) => items,
        _ => {
            return Err(CranelispError::ParseError {
                message: "defmacro clause params must be a bracket list".to_string(),
                location: ErrorLocation::from_span(children[0].span()),
            });
        }
    };

    let (fixed_params, rest_param) = parse_param_items(bracket_items)?;
    Ok(MacroClause {
        fixed_params,
        rest_param,
        body_sexp: children[1].clone(),
    })
}

// ---------------------------------------------------------------------------
// Macro clause defn synthesis
// ---------------------------------------------------------------------------

/// Synthesize a Sexp representing a function definition for a single
/// macro clause.
///
/// Internal-but-exposed (per the crate-root preamble §"Macro-resolver
/// helpers"): pub at the crate root so `int` can build per-clause `Defn`s
/// for the backend per Decision 21 without rebuilding the shape-checking
/// logic outside the frontend. A settled part of the surface (`frontend.md`
/// §9.1: no "narrow back").
///
/// Takes a `&MacroClause` parameter — the type comes from
/// `cranelisp_types::parsed::MacroClause` (re-exported at crate root for
/// ergonomics per Principle 15's narrow exception).
///
/// # Output shape
///
/// The returned Sexp is:
/// ```text
/// (defn __macro_{name}_clause_{idx} [:(SList Sexp) __args__]
///   (match __args__
///     [(macros/SCons param1 __t1__)
///       (match __t1__
///         [(macros/SCons param2 __t0__)
///           <body>]
///         [_ (macros/SexpInt 0)])]
///     [_ (macros/SexpInt 0)]))
/// ```
///
/// Type names in annotations are module-qualified (`macros/SList`,
/// `macros/Sexp`) because Sprint 66 Wave 3a-α tightened typecheck to
/// current-module-only short-name resolution per Principle 17 — a
/// synthesized defn that lands in the user's module cannot resolve bare
/// `SList` without an explicit `(import [macros [...]])` in scope.
/// Constructor names in match patterns remain module-qualified (the
/// typechecker resolves them through the module system).
///
/// Each match on `SList` includes a wildcard dead arm for exhaustiveness
/// — the typechecker requires all constructors to be covered but macro
/// arity is validated before invocation.
///
/// For bracket destructure parameters, an additional inner match peels
/// the `SexpBracket` and destructures its inner `SList`.
///
/// # Downstream
///
/// The caller (the cluster orchestrator's macro-compilation path) will
/// process this Sexp through quasiquote expansion, AST building,
/// typechecking, and compilation. The resulting `Def { kind: UserFn, … }`
/// lives under the mangled name `{macro-name}$clause-{N}` and is
/// reachable through the parent `Def { kind: Macro { clauses_meta }, … }`
/// entry's GOT-dispatch path (per BC §7 "Macros are Defs").
pub fn synthesize_macro_clause_defn(
    name: &str,
    clause_idx: usize,
    clause: &MacroClause,
    span: Span,
) -> Sexp {
    let fn_name = format!("__macro_{name}_clause_{clause_idx}");
    let args_name = "__args__";

    // Build the match chain body.
    let has_params = !clause.fixed_params.is_empty() || clause.rest_param.is_some();
    let body = if has_params {
        build_macro_param_chain(
            args_name,
            &clause.fixed_params,
            &clause.rest_param,
            clause.body_sexp.clone(),
        )
    } else {
        clause.body_sexp.clone()
    };

    // Build: (defn __macro_name_clause_N [: (macros/SList macros/Sexp) __args__] <body>)
    // The bracket items must be at the top level — the AST builder's
    // build_annotated_params expects `:` + type-expr + name as separate bracket items.
    //
    // Type names must be FQ (`macros/SList`, `macros/Sexp`). Sprint 66 Wave 3a-α
    // tightened typecheck to current-module-only short-name resolution per
    // Principle 17 — a synthesized defn that lands in the user's module cannot
    // resolve bare `SList` without an explicit `(import [macros [...]])` in scope.
    // Emitting the FQ form lets the resolver bypass short-name lookup entirely.
    // (Pre-Wave-3a-α this code emitted unqualified `SList`/`Sexp`; the typechecker's
    // known_types registry used to be flat, but is no longer.)
    let type_expr = synth::list(vec![synth::sym("macros/SList"), synth::sym("macros/Sexp")]);

    let param_bracket = synth::bracket(vec![synth::sym(":"), type_expr, synth::sym(args_name)]);

    // Outer list span carries the user-source span of the originating
    // clause — the underscore in the parameter was a "not yet wired"
    // marker; the value now feeds the synthesised defn so downstream
    // errors trace back to the source clause.
    Sexp::List(
        vec![synth::sym("defn-"), synth::sym(&fn_name), param_bracket, body],
        span,
    )
}

// ---------------------------------------------------------------------------
// Match chain building (Sexp-level)
// ---------------------------------------------------------------------------

/// Build nested match Sexps to destructure the argument SList.
///
/// Each fixed param peels one `(macros/SCons param tail)` from the list.
/// A rest param binds the remaining tail directly.
fn build_macro_param_chain(
    scrutinee_name: &str,
    params: &[MacroParam],
    rest_param: &Option<Symbol>,
    body: Sexp,
) -> Sexp {
    if params.is_empty() {
        if let Some(rest_name) = rest_param {
            // Bind remaining list to rest_name via a var pattern.
            return make_match_sexp(
                scrutinee_name,
                make_var_pattern(rest_name),
                body,
            );
        }
        return body;
    }

    let param = &params[0];
    let is_last = params.len() == 1;

    match param {
        MacroParam::Name(pname) => {
            let tail_binding = compute_tail_binding(is_last, rest_param, params.len());
            let inner = if is_last && rest_param.is_some() {
                body
            } else {
                build_macro_param_chain(&tail_binding, &params[1..], rest_param, body)
            };
            make_scons_match(scrutinee_name, pname, &tail_binding, inner)
        }
        MacroParam::Bracket { fixed, rest } => {
            let tail_binding = compute_tail_binding(is_last, rest_param, params.len());
            let bracket_temp = format!("__bracket_{}__", params.len());
            let continuation = if is_last && rest_param.is_some() {
                body
            } else {
                build_macro_param_chain(&tail_binding, &params[1..], rest_param, body)
            };
            let bracket_inner =
                build_bracket_destructure_sexp(&bracket_temp, fixed, rest, continuation);
            make_scons_match(scrutinee_name, &bracket_temp.as_str().into(), &tail_binding, bracket_inner)
        }
    }
}

/// Compute the tail binding name for a param chain step.
fn compute_tail_binding(is_last: bool, rest_param: &Option<Symbol>, remaining: usize) -> String {
    if is_last {
        if let Some(rest_name) = rest_param {
            return rest_name.to_string();
        }
        format!("__t{}__", 0)
    } else {
        format!("__t{}__", remaining - 1)
    }
}

/// Build a match Sexp that peels one SCons:
/// ```text
/// (match <scrutinee>
///   [(macros/SCons <head> <tail>) <body>]
///   [_ (macros/SexpInt 0)])
/// ```
///
/// The wildcard arm is unreachable — macro arity is validated before invocation —
/// but the typechecker requires exhaustive match coverage on SList.
fn make_scons_match(scrutinee_name: &str, head_name: &Symbol, tail_name: &str, body: Sexp) -> Sexp {
    // The SCons DESTRUCTURING pattern shares the `(macros/SCons head tail)` shape
    // that `synth::cons` builds for construction (audit R4).
    let pattern = synth::cons(synth::sym(head_name), synth::sym(tail_name));
    make_match_sexp_exhaustive(scrutinee_name, pattern, body)
}

/// Build `(match <scrutinee> [<pattern> <body>])`.
///
/// The arms bracket uses `Sexp::Bracket` per the AST builder's `build_match`
/// expectation (it calls `expect_bracket` on the third element).
fn make_match_sexp(scrutinee_name: &str, pattern: Sexp, body: Sexp) -> Sexp {
    let arm = synth::bracket(vec![pattern, body]);
    synth::list(vec![synth::sym("match"), synth::sym(scrutinee_name), arm])
}

/// Build `(match <scrutinee> [<pattern> <body> _ <dead>])`.
///
/// Like `make_match_sexp` but adds a wildcard arm for exhaustiveness. The dead
/// arm body is `(macros/SexpInt 0)` — a valid Sexp value that will never execute
/// because macro arity is validated before invocation.
///
/// The AST builder expects match syntax as `(match scrutinee [pat1 body1 pat2 body2 ...])`
/// with all pattern-body pairs in a single bracket.
fn make_match_sexp_exhaustive(scrutinee_name: &str, pattern: Sexp, body: Sexp) -> Sexp {
    // Dead arm body: (macros/SexpInt 0)
    let dead_body = synth::list(vec![synth::sym("macros/SexpInt"), synth::int(0)]);

    // All arms in a single bracket: [pattern body _ dead_body]
    let arms = synth::bracket(vec![pattern, body, synth::sym("_"), dead_body]);

    synth::list(vec![synth::sym("match"), synth::sym(scrutinee_name), arms])
}

/// Build a var pattern (just a symbol that binds the whole scrutinee).
fn make_var_pattern(name: &Symbol) -> Sexp {
    synth::sym(name)
}

/// Build bracket destructuring: match against SexpBracket, then destructure inner SList.
///
/// Generates:
/// ```text
/// (match <scrutinee>
///   [(macros/SexpBracket __inner__)
///     (match __inner__
///       [(macros/SCons x (macros/SCons y __inner_t0__))
///         <continuation>])])
/// ```
///
/// Inner tail bindings use `__inner_t{N}__` prefix to avoid shadowing outer
/// `__t{N}__` bindings.
fn build_bracket_destructure_sexp(
    scrutinee_name: &str,
    fixed: &[Symbol],
    rest: &Option<Symbol>,
    continuation: Sexp,
) -> Sexp {
    let inner_name = format!("{scrutinee_name}_items__");

    // Build the inner destructuring of the SList.
    let inner_body =
        build_inner_slist_chain(&inner_name, fixed, rest, continuation);

    // Outer match: (match scrutinee [(macros/SexpBracket __inner__) <inner_body>] [_ ...])
    // Wildcard arm needed for exhaustiveness — Sexp has 7 constructors.
    let bracket_pattern =
        synth::list(vec![synth::sym("macros/SexpBracket"), synth::sym(&inner_name)]);

    make_match_sexp_exhaustive(scrutinee_name, bracket_pattern, inner_body)
}

/// Build nested SCons match chain for bracket destructuring inner elements.
///
/// Uses `__inner_t{N}__` prefix for tail bindings to avoid collisions with
/// the outer param chain's `__t{N}__` bindings.
fn build_inner_slist_chain(
    scrutinee_name: &str,
    fixed: &[Symbol],
    rest: &Option<Symbol>,
    body: Sexp,
) -> Sexp {
    if fixed.is_empty() {
        if let Some(rest_name) = rest {
            return make_match_sexp(
                scrutinee_name,
                make_var_pattern(rest_name),
                body,
            );
        }
        return body;
    }

    let head = &fixed[0];
    let is_last = fixed.len() == 1;
    let tail_binding = if is_last {
        if let Some(rest_name) = rest {
            rest_name.to_string()
        } else {
            format!("__inner_t{}__", 0)
        }
    } else {
        format!("__inner_t{}__", fixed.len() - 1)
    };

    let inner = if is_last && rest.is_some() {
        body
    } else {
        build_inner_slist_chain(&tail_binding, &fixed[1..], rest, body)
    };

    make_scons_match(scrutinee_name, head, &tail_binding, inner)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
