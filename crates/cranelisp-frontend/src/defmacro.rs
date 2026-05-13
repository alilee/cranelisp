//! `defmacro` parsing and body synthesis.
//!
//! Parses `defmacro` forms from Sexp, extracts name/docstring/clauses, and
//! synthesizes function Sexps for each clause with argument destructuring via
//! nested match expressions.
//!
//! Also provides `is_defmacro`, `is_begin`, and `flatten_begin` for pipeline
//! orchestration.

use cranelisp_types::{CranelispError, ErrorLocation, MacroParam, Sexp, Span, Symbol};

use crate::quasiquote::next_synthetic_span;

/// Allocate a fresh synthetic span (delegates to shared counter in quasiquote).
fn next_span() -> Span {
    next_synthetic_span()
}

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
pub fn is_defmacro(sexp: &Sexp) -> bool {
    if let Sexp::List(children, _) = sexp
        && let Some(Sexp::Symbol(head, _)) = children.first()
    {
        return head == "defmacro" || head == "defmacro-";
    }
    false
}

/// Returns true if the sexp is `(begin ...)`.
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

/// Parse macro parameters from bracket items.
///
/// Supports simple names, bracket destructuring, and `& rest` syntax.
/// Examples: `[a b]`, `[a & rest]`, `[[x y] body]`
///
/// Demoted to `pub(crate)` per facade row 16; retained as a facade entry
/// for future REPL/slash-command surfacing.
#[allow(dead_code)]
pub(crate) fn parse_macro_params(
    bracket: &Sexp,
) -> Result<(Vec<MacroParam>, Option<Symbol>), CranelispError> {
    let (items, _span) = match bracket {
        Sexp::Bracket(items, span) => (items, *span),
        _ => {
            return Err(CranelispError::ParseError {
                message: "macro params must be a bracket list".to_string(),
                location: ErrorLocation::from_span(bracket.span()),
            });
        }
    };
    parse_param_items(items)
}

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
            Sexp::Symbol(s, _) if s.starts_with('&') && s.len() > 1 => {
                // Reader produces "&rest" as a single symbol.
                let rest_name = &s[1..];
                rest_param = Some(rest_name.into());
                i += 1;
            }
            Sexp::Symbol(pname, _) => {
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
            Sexp::Symbol(s, _) if s.starts_with('&') && s.len() > 1 => {
                let rest_name = &s[1..];
                rest = Some(rest_name.into());
                j += 1;
            }
            Sexp::Symbol(pname, _) => {
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

/// Parse a `(defmacro name ...)` or `(defmacro- name ...)` form.
///
/// Handles both single-clause `(defmacro name [params] body)` and multi-clause
/// `(defmacro name ([params] body) ([params] body))` syntax, with optional
/// docstring.
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
        Sexp::Symbol(n, _) => n.as_str().into(),
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

/// Synthesize a Sexp representing a function definition for a single macro clause.
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
/// Type names in annotations are unqualified (the typechecker's `known_types`
/// stores bare names). Constructor names in match patterns remain module-qualified
/// (the typechecker resolves them through the module system).
///
/// Each match on SList includes a wildcard dead arm for exhaustiveness — the
/// typechecker requires all constructors to be covered but macro arity is
/// validated before invocation.
///
/// For bracket destructure parameters, an additional inner match peels the
/// `SexpBracket` and destructures its inner `SList`.
///
/// The caller (Phase 4's CraneliftExpander) will process this Sexp through
/// quasiquote expansion, AST building, typechecking, and compilation.
pub fn synthesize_macro_clause_defn(
    name: &str,
    clause_idx: usize,
    clause: &MacroClause,
    _span: Span,
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
    let type_expr = Sexp::List(
        vec![
            Sexp::Symbol("macros/SList".to_string(), next_span()),
            Sexp::Symbol("macros/Sexp".to_string(), next_span()),
        ],
        next_span(),
    );

    let param_bracket = Sexp::Bracket(
        vec![
            Sexp::Symbol(":".to_string(), next_span()),
            type_expr,
            Sexp::Symbol(args_name.to_string(), next_span()),
        ],
        next_span(),
    );

    Sexp::List(
        vec![
            Sexp::Symbol("defn-".to_string(), next_span()),
            Sexp::Symbol(fn_name, next_span()),
            param_bracket,
            body,
        ],
        next_span(),
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
    let pattern = Sexp::List(
        vec![
            Sexp::Symbol("macros/SCons".to_string(), next_span()),
            Sexp::Symbol(head_name.to_string(), next_span()),
            Sexp::Symbol(tail_name.to_string(), next_span()),
        ],
        next_span(),
    );

    make_match_sexp_exhaustive(scrutinee_name, pattern, body)
}

/// Build `(match <scrutinee> [<pattern> <body>])`.
///
/// The arms bracket uses `Sexp::Bracket` per the AST builder's `build_match`
/// expectation (it calls `expect_bracket` on the third element).
fn make_match_sexp(scrutinee_name: &str, pattern: Sexp, body: Sexp) -> Sexp {
    let arm = Sexp::Bracket(vec![pattern, body], next_span());
    Sexp::List(
        vec![
            Sexp::Symbol("match".to_string(), next_span()),
            Sexp::Symbol(scrutinee_name.to_string(), next_span()),
            arm,
        ],
        next_span(),
    )
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
    let dead_body = Sexp::List(
        vec![
            Sexp::Symbol("macros/SexpInt".to_string(), next_span()),
            Sexp::Int(0, next_span()),
        ],
        next_span(),
    );

    // All arms in a single bracket: [pattern body _ dead_body]
    let arms = Sexp::Bracket(
        vec![
            pattern,
            body,
            Sexp::Symbol("_".to_string(), next_span()),
            dead_body,
        ],
        next_span(),
    );

    Sexp::List(
        vec![
            Sexp::Symbol("match".to_string(), next_span()),
            Sexp::Symbol(scrutinee_name.to_string(), next_span()),
            arms,
        ],
        next_span(),
    )
}

/// Build a var pattern (just a symbol that binds the whole scrutinee).
fn make_var_pattern(name: &Symbol) -> Sexp {
    Sexp::Symbol(name.to_string(), next_span())
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
    let bracket_pattern = Sexp::List(
        vec![
            Sexp::Symbol("macros/SexpBracket".to_string(), next_span()),
            Sexp::Symbol(inner_name.to_string(), next_span()),
        ],
        next_span(),
    );

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
mod tests {
    use super::*;

    /// Helper: parse source text into a single Sexp.
    fn parse_one(src: &str) -> Sexp {
        let sexps = crate::reader::parse(src).expect("parse failed");
        assert_eq!(sexps.len(), 1, "expected exactly one sexp");
        sexps.into_iter().next().unwrap()
    }

    /// Helper: check if a Sexp is a list whose head symbol matches `name`.
    fn is_list_headed_by(sexp: &Sexp, name: &str) -> bool {
        matches!(sexp, Sexp::List(ch, _) if !ch.is_empty()
            && matches!(&ch[0], Sexp::Symbol(s, _) if s == name))
    }

    /// Helper: recursively check if a symbol appears anywhere in a Sexp tree.
    fn contains_symbol(sexp: &Sexp, name: &str) -> bool {
        match sexp {
            Sexp::Symbol(s, _) => s == name,
            Sexp::List(children, _) | Sexp::Bracket(children, _) => {
                children.iter().any(|c| contains_symbol(c, name))
            }
            _ => false,
        }
    }

    // -- is_defmacro --

    // spec: 09-macros.md section 9.2.1 -- defmacro detection
    #[test]
    fn is_defmacro_positive() {
        let sexp = parse_one("(defmacro foo [x] x)");
        assert!(is_defmacro(&sexp));
    }

    // spec: 09-macros.md section 9.2.1 -- defmacro- detection
    #[test]
    fn is_defmacro_private_positive() {
        let sexp = parse_one("(defmacro- foo [x] x)");
        assert!(is_defmacro(&sexp));
    }

    // spec: 09-macros.md section 9.2.1 -- non-defmacro detection
    #[test]
    fn is_defmacro_negative() {
        let sexp = parse_one("(defn foo [x] x)");
        assert!(!is_defmacro(&sexp));
    }

    #[test]
    fn is_defmacro_negative_atom() {
        let sexp = parse_one("42");
        assert!(!is_defmacro(&sexp));
    }

    // -- is_begin --

    // spec: 09-macros.md section 9.6 -- begin detection
    #[test]
    fn is_begin_positive() {
        let sexp = parse_one("(begin 1 2 3)");
        assert!(is_begin(&sexp));
    }

    // spec: 09-macros.md section 9.6 -- non-begin detection
    #[test]
    fn is_begin_negative() {
        let sexp = parse_one("(defn foo [] 1)");
        assert!(!is_begin(&sexp));
    }

    // -- flatten_begin --

    // spec: 09-macros.md section 9.6 -- begin flattening
    #[test]
    fn flatten_begin_extracts_forms() {
        let sexp = parse_one("(begin 1 2 3)");
        let forms = flatten_begin(sexp);
        assert_eq!(forms.len(), 3);
        assert!(matches!(&forms[0], Sexp::Int(1, _)));
        assert!(matches!(&forms[1], Sexp::Int(2, _)));
        assert!(matches!(&forms[2], Sexp::Int(3, _)));
    }

    // spec: 09-macros.md section 9.6 -- nested begin flattening
    #[test]
    fn flatten_begin_nested() {
        let sexp = parse_one("(begin 1 (begin 2 3) 4)");
        let forms = flatten_begin(sexp);
        assert_eq!(forms.len(), 4);
    }

    // spec: 09-macros.md section 9.6 -- non-begin passthrough
    #[test]
    fn flatten_begin_non_begin() {
        let sexp = parse_one("42");
        let forms = flatten_begin(sexp);
        assert_eq!(forms.len(), 1);
        assert!(matches!(&forms[0], Sexp::Int(42, _)));
    }

    // -- parse_defmacro --

    // spec: 09-macros.md section 9.2.1 -- single-clause parse
    #[test]
    fn parse_single_clause() {
        let sexp = parse_one("(defmacro my-if [c t e] `(if ~c ~t ~e))");
        let info = parse_defmacro(&sexp).unwrap();
        assert_eq!(info.name.as_ref(), "my-if");
        assert!(!info.is_private);
        assert!(info.docstring.is_none());
        assert_eq!(info.clauses.len(), 1);
        assert_eq!(info.clauses[0].fixed_params.len(), 3);
        assert!(info.clauses[0].rest_param.is_none());
    }

    // spec: 09-macros.md section 9.2.6 -- multi-clause parse
    #[test]
    fn parse_multi_clause() {
        // Note: reimplemented reader parses `&rest` as a single symbol "&rest"
        let sexp = parse_one("(defmacro cond ([x] x) ([x body &rest] `(if ~x ~body (cond ~@rest))))");
        let info = parse_defmacro(&sexp).unwrap();
        assert_eq!(info.name.as_ref(), "cond");
        assert_eq!(info.clauses.len(), 2);
        // First clause: 1 fixed param, no rest
        assert_eq!(info.clauses[0].fixed_params.len(), 1);
        assert!(info.clauses[0].rest_param.is_none());
        // Second clause: 2 fixed params + rest
        assert_eq!(info.clauses[1].fixed_params.len(), 2);
        assert!(info.clauses[1].rest_param.is_some());
    }

    // spec: 09-macros.md section 9.2.2 -- rest parameter parse (no space)
    #[test]
    fn parse_rest_param() {
        // Reader parses `&args` as a single symbol "&args"
        let sexp = parse_one("(defmacro my-add [&args] `(+ ~@args))");
        let info = parse_defmacro(&sexp).unwrap();
        assert_eq!(info.clauses[0].fixed_params.len(), 0);
        assert_eq!(info.clauses[0].rest_param.as_ref().unwrap().as_ref(), "args");
    }

    // spec: 09-macros.md section 9.2.2 -- rest parameter parse (with space)
    #[test]
    fn parse_rest_param_with_space() {
        // Reader now accepts `& args` (with space) — Clojure convention
        let sexp = parse_one("(defmacro my-add [& args] `(+ ~@args))");
        let info = parse_defmacro(&sexp).unwrap();
        assert_eq!(info.clauses[0].fixed_params.len(), 0);
        assert_eq!(info.clauses[0].rest_param.as_ref().unwrap().as_ref(), "args");
    }

    // spec: 09-macros.md section 9.2.3 -- variadic multi-clause with & rest (with space)
    #[test]
    fn parse_multi_clause_rest_with_space() {
        let sexp = parse_one("(defmacro my-cond ([x] x) ([x body & rest] `(if ~x ~body (my-cond ~@rest))))");
        let info = parse_defmacro(&sexp).unwrap();
        assert_eq!(info.clauses.len(), 2);
        assert_eq!(info.clauses[1].fixed_params.len(), 2);
        assert!(info.clauses[1].rest_param.is_some());
        assert_eq!(info.clauses[1].rest_param.as_ref().unwrap().as_ref(), "rest");
    }

    // spec: 09-macros.md section 9.2.4 -- docstring extraction
    #[test]
    fn parse_docstring() {
        // Note: reimplemented reader parses `&elems` as a single symbol "&elems"
        let sexp = parse_one("(defmacro list \"Construct a list\" [&elems] `Nil)");
        let info = parse_defmacro(&sexp).unwrap();
        assert_eq!(info.docstring.as_deref(), Some("Construct a list"));
    }

    // spec: 09-macros.md section 9.2.1 -- private macro
    #[test]
    fn parse_private_macro() {
        let sexp = parse_one("(defmacro- internal [x] x)");
        let info = parse_defmacro(&sexp).unwrap();
        assert!(info.is_private);
    }

    // spec: 09-macros.md section 9.2.7 -- bracket destructure parameter
    #[test]
    fn parse_bracket_destructure() {
        let sexp = parse_one("(defmacro my-let [[name expr] body] `(let [~name ~expr] ~body))");
        let info = parse_defmacro(&sexp).unwrap();
        assert_eq!(info.clauses[0].fixed_params.len(), 2);
        match &info.clauses[0].fixed_params[0] {
            MacroParam::Bracket { fixed, rest } => {
                assert_eq!(fixed.len(), 2);
                assert_eq!(fixed[0].as_ref(), "name");
                assert_eq!(fixed[1].as_ref(), "expr");
                assert!(rest.is_none());
            }
            _ => panic!("expected bracket param"),
        }
        match &info.clauses[0].fixed_params[1] {
            MacroParam::Name(n) => assert_eq!(n.as_ref(), "body"),
            _ => panic!("expected name param"),
        }
    }

    // -- synthesize_macro_clause_defn --

    // spec: 09-macros.md section 9.2 -- synthesized defn structure
    #[test]
    fn synthesize_simple_clause() {
        let clause = MacroClause {
            fixed_params: vec![
                MacroParam::Name("a".into()),
                MacroParam::Name("b".into()),
            ],
            rest_param: None,
            body_sexp: Sexp::Symbol("a".to_string(), Span::SYNTHETIC),
        };
        let result = synthesize_macro_clause_defn("test", 0, &clause, Span::SYNTHETIC);

        // Should be (defn- __macro_test_clause_0 [...] (match ...))
        assert!(is_list_headed_by(&result, "defn-"));
        // Check function name
        if let Sexp::List(ch, _) = &result {
            assert!(matches!(&ch[1], Sexp::Symbol(s, _) if s == "__macro_test_clause_0"));
            // Should have nested match chain with macros/SCons patterns
            assert!(contains_symbol(&result, "macros/SCons"));
            assert!(contains_symbol(&result, "match"));
        }
    }

    // spec: 09-macros.md section 9.2 -- zero-arg clause
    #[test]
    fn synthesize_zero_arg_clause() {
        let clause = MacroClause {
            fixed_params: vec![],
            rest_param: None,
            body_sexp: Sexp::Int(42, Span::SYNTHETIC),
        };
        let result = synthesize_macro_clause_defn("const", 0, &clause, Span::SYNTHETIC);

        // Should be (defn- __macro_const_clause_0 [...] 42)
        assert!(is_list_headed_by(&result, "defn-"));
        // Body should be the integer directly (no match chain)
        if let Sexp::List(ch, _) = &result {
            // ch[3] is the body
            assert!(matches!(&ch[3], Sexp::Int(42, _)));
        }
    }

    // spec: 09-macros.md section 9.2.2 -- rest param in synthesized defn
    #[test]
    fn synthesize_rest_param_clause() {
        let clause = MacroClause {
            fixed_params: vec![MacroParam::Name("x".into())],
            rest_param: Some("rest".into()),
            body_sexp: Sexp::Symbol("x".to_string(), Span::SYNTHETIC),
        };
        let result = synthesize_macro_clause_defn("thread", 0, &clause, Span::SYNTHETIC);

        // The match chain should bind rest directly as the tail
        assert!(contains_symbol(&result, "rest"));
        assert!(contains_symbol(&result, "macros/SCons"));
    }

    // spec: 09-macros.md section 9.2.7 -- bracket destructure in synthesized defn
    #[test]
    fn synthesize_bracket_destructure_clause() {
        let clause = MacroClause {
            fixed_params: vec![
                MacroParam::Bracket {
                    fixed: vec!["x".into(), "y".into()],
                    rest: None,
                },
                MacroParam::Name("body".into()),
            ],
            rest_param: None,
            body_sexp: Sexp::Symbol("body".to_string(), Span::SYNTHETIC),
        };
        let result = synthesize_macro_clause_defn("mylet", 0, &clause, Span::SYNTHETIC);

        // Should contain SexpBracket pattern for bracket destructuring
        assert!(contains_symbol(&result, "macros/SexpBracket"));
        // Inner bindings should use __inner_t prefixed names (not __t)
        // The main param chain should use __t or direct bindings
        assert!(contains_symbol(&result, "macros/SCons"));
    }

    // -- Type annotation in synthesized param --

    // spec: 09-macros.md section 9.2 -- param type annotation
    #[test]
    fn synthesize_has_slist_sexp_annotation() {
        let clause = MacroClause {
            fixed_params: vec![MacroParam::Name("x".into())],
            rest_param: None,
            body_sexp: Sexp::Symbol("x".to_string(), Span::SYNTHETIC),
        };
        let result = synthesize_macro_clause_defn("test", 0, &clause, Span::SYNTHETIC);

        // The param bracket should contain type annotation with macros/SList
        // and macros/Sexp (FQ — Sprint 66 Wave 3a-α requires FQ for cross-module
        // refs since typecheck is current-module-only per Principle 17).
        assert!(contains_symbol(&result, "macros/SList"));
        assert!(contains_symbol(&result, "macros/Sexp"));
    }
}
