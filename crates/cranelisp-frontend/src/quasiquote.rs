//! Quasiquote expansion: Sexp-to-Sexp transformation.
//!
//! Converts template syntax (`` ` ``, `~`, `~@`) into explicit `Sexp`
//! constructor calls using `macros/`-qualified references. This runs at
//! the Sexp level, before AST building.
//!
//! Also handles `(quote ...)` forms (pure structural quotation without
//! unquote).
//!
//! Pub-at-root items ([`expand_quasiquotes`], [`expand_quote_template`],
//! [`next_synthetic_span`]) are the **standing public quasiquote API**
//! per the crate-root preamble §"Macro-resolver helpers" — used by
//! user-authored macros at expansion time and by REPL `/expand`. Unlike
//! the [`crate::defmacro`] helpers, these do NOT narrow back at FIXME
//! 0098 Phase 2 close.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, Ordering};

use cranelisp_types::{ErrorLocation, CranelispError, Sexp, Span};

/// Global counter for unique synthetic spans. Starts well above any realistic
/// source file size to avoid collisions with real source spans.
///
/// Shared by quasiquote and defmacro modules — all synthetic spans use this
/// single counter to guarantee uniqueness.
static SYNTHETIC_SPAN_COUNTER: AtomicU32 = AtomicU32::new(1_000_000);

/// Allocate a fresh synthetic span with a unique value.
///
/// Synthetic-span allocator for forms produced by macro expansion.
/// Reused across the session — span uniqueness is a frontend invariant
/// (BC invariant #4: synthetic spans are unique). Monotonically
/// increasing; no two synthetic spans collide within a session.
///
/// Pub at the crate root and via this module per the standing
/// quasiquote API. Shared by [`crate::defmacro`] through a thin
/// delegating wrapper so the counter is single-sourced here.
pub fn next_synthetic_span() -> Span {
    let v = SYNTHETIC_SPAN_COUNTER.fetch_add(1, Ordering::Relaxed);
    Span::new(v, v)
}

/// Allocate a fresh synthetic span (crate-internal alias).
fn next_span() -> Span {
    next_synthetic_span()
}

// ---------------------------------------------------------------------------
// Sexp form detection helpers
// ---------------------------------------------------------------------------

fn is_quasiquote(children: &[Sexp]) -> bool {
    children.len() == 2 && matches!(&children[0], Sexp::Symbol(s, _) if s == "quasiquote")
}

fn is_quote(children: &[Sexp]) -> bool {
    children.len() == 2 && matches!(&children[0], Sexp::Symbol(s, _) if s == "quote")
}

fn is_unquote(children: &[Sexp]) -> bool {
    children.len() == 2 && matches!(&children[0], Sexp::Symbol(s, _) if s == "unquote")
}

fn is_unquote_splicing(children: &[Sexp]) -> bool {
    children.len() == 2
        && matches!(&children[0], Sexp::Symbol(s, _) if s == "unquote-splicing")
}

// ---------------------------------------------------------------------------
// Sexp constructor builders (all macros/-qualified)
// ---------------------------------------------------------------------------

/// Build `(macros/SexpSym "name")`.
fn make_sexp_sym(name: &str) -> Sexp {
    Sexp::List(
        vec![
            Sexp::Symbol("macros/SexpSym".to_string(), next_span()),
            Sexp::Str(name.to_string(), next_span()),
        ],
        next_span(),
    )
}

/// Build `(macros/SexpInt val)`.
fn make_sexp_int(val: i64) -> Sexp {
    Sexp::List(
        vec![
            Sexp::Symbol("macros/SexpInt".to_string(), next_span()),
            Sexp::Int(val, next_span()),
        ],
        next_span(),
    )
}

/// Build `(macros/SexpFloat val)`.
fn make_sexp_float(val: f64) -> Sexp {
    Sexp::List(
        vec![
            Sexp::Symbol("macros/SexpFloat".to_string(), next_span()),
            Sexp::Float(val, next_span()),
        ],
        next_span(),
    )
}

/// Build `(macros/SexpBool val)`.
fn make_sexp_bool(val: bool) -> Sexp {
    Sexp::List(
        vec![
            Sexp::Symbol("macros/SexpBool".to_string(), next_span()),
            Sexp::Bool(val, next_span()),
        ],
        next_span(),
    )
}

/// Build `(macros/SexpStr "val")`.
fn make_sexp_str(val: &str) -> Sexp {
    Sexp::List(
        vec![
            Sexp::Symbol("macros/SexpStr".to_string(), next_span()),
            Sexp::Str(val.to_string(), next_span()),
        ],
        next_span(),
    )
}

/// Build `(ctor items_sexp)` where `ctor` is `macros/SexpList` or `macros/SexpBracket`.
fn make_sexp_container(ctor: &str, items_sexp: Sexp) -> Sexp {
    Sexp::List(
        vec![Sexp::Symbol(ctor.to_string(), next_span()), items_sexp],
        next_span(),
    )
}

/// Build nested `(macros/SCons e0 (macros/SCons e1 ... macros/SNil))`.
fn make_slist(elements: Vec<Sexp>) -> Sexp {
    let nil = Sexp::Symbol("macros/SNil".to_string(), next_span());
    elements.into_iter().rev().fold(nil, |acc, elem| {
        Sexp::List(
            vec![
                Sexp::Symbol("macros/SCons".to_string(), next_span()),
                elem,
                acc,
            ],
            next_span(),
        )
    })
}

/// Build `(macros/sconcat a b)`.
fn make_sconcat(a: Sexp, b: Sexp) -> Sexp {
    Sexp::List(
        vec![
            Sexp::Symbol("macros/sconcat".to_string(), next_span()),
            a,
            b,
        ],
        next_span(),
    )
}

// ---------------------------------------------------------------------------
// Auto-gensym
// ---------------------------------------------------------------------------

/// Generate a unique gensym name for an auto-gensym symbol like `x#`.
///
/// Strips the trailing `#` and appends `__auto_NNNN` where NNNN is a unique
/// counter value.
fn make_gensym_name(base: &str) -> String {
    let counter = SYNTHETIC_SPAN_COUNTER.fetch_add(1, Ordering::Relaxed);
    let stem = &base[..base.len() - 1];
    format!("{stem}__auto_{counter}")
}

// ---------------------------------------------------------------------------
// Top-level entry: expand_quasiquotes
// ---------------------------------------------------------------------------

/// Walk a Sexp tree and expand any `(quasiquote ...)` and `(quote ...)`
/// forms into explicit `macros/`-qualified constructor calls.
///
/// Pure Sexp-to-Sexp transformation with no typechecker or backend
/// access needed. Invoked unconditionally at the top of [`crate::expand()`]
/// before macro-head dispatch, so user macros see already-desugared
/// template syntax.
///
/// Pub at the crate root per the standing quasiquote API (used by REPL
/// `/expand` and by user-authored macros at expansion time).
pub fn expand_quasiquotes(sexp: &Sexp) -> Result<Sexp, CranelispError> {
    match sexp {
        Sexp::List(children, span) if !children.is_empty() => {
            if is_quasiquote(children) {
                let mut gensyms = HashMap::new();
                let expanded = expand_qq_template(&children[1], 0, &mut gensyms)?;
                // Recurse into the result in case unquoted sub-expressions
                // contain their own quasiquotes.
                return expand_quasiquotes(&expanded);
            }

            if is_quote(children) {
                return Ok(expand_quote_template(&children[1]));
            }

            // Recurse into children.
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
        Sexp::Comment(_, _) => Ok(sexp.clone()),
        other => Ok(other.clone()),
    }
}

// ---------------------------------------------------------------------------
// Quote expansion (pure structural quotation)
// ---------------------------------------------------------------------------

/// Expand a `(quote ...)` form into Sexp constructor calls.
///
/// Unlike quasiquote, quote is pure structural quotation — no unquote
/// handling. Every node is converted to its `macros/Sexp*` constructor
/// form.
///
/// Pub at the crate root per the standing quasiquote API.
pub fn expand_quote_template(template: &Sexp) -> Sexp {
    match template {
        Sexp::Symbol(s, _) => make_sexp_sym(s),
        Sexp::Int(v, _) => make_sexp_int(*v),
        Sexp::Float(v, _) => make_sexp_float(*v),
        Sexp::Bool(v, _) => make_sexp_bool(*v),
        Sexp::Str(s, _) => make_sexp_str(s),
        Sexp::List(children, _) => {
            let expanded: Vec<Sexp> = children.iter().map(expand_quote_template).collect();
            make_sexp_container("macros/SexpList", make_slist(expanded))
        }
        Sexp::Bracket(children, _) => {
            let expanded: Vec<Sexp> = children.iter().map(expand_quote_template).collect();
            make_sexp_container("macros/SexpBracket", make_slist(expanded))
        }
        // Comments are not meaningful in quoted forms; pass through as-is.
        Sexp::Comment(_, _) => template.clone(),
    }
}

// ---------------------------------------------------------------------------
// Quasiquote template expansion
// ---------------------------------------------------------------------------

/// Recursively expand a quasiquote template at the given nesting depth.
///
/// At depth 0, `(unquote expr)` passes `expr` through and `(unquote-splicing expr)`
/// generates `sconcat` calls. At depth > 0 (nested quasiquote), forms are
/// structurally quoted with depth adjustments.
fn expand_qq_template(
    template: &Sexp,
    depth: usize,
    gensym_map: &mut HashMap<String, String>,
) -> Result<Sexp, CranelispError> {
    match template {
        // Atoms -> constructor calls
        Sexp::Symbol(s, _) => {
            // Auto-gensym: at depth 0, symbols ending in '#' get unique names.
            if depth == 0 && s.ends_with('#') && s.len() > 1 {
                let generated = gensym_map
                    .entry(s.clone())
                    .or_insert_with(|| make_gensym_name(s))
                    .clone();
                Ok(make_sexp_sym(&generated))
            } else {
                Ok(make_sexp_sym(s))
            }
        }
        Sexp::Int(v, _) => Ok(make_sexp_int(*v)),
        Sexp::Float(v, _) => Ok(make_sexp_float(*v)),
        Sexp::Bool(v, _) => Ok(make_sexp_bool(*v)),
        Sexp::Str(s, _) => Ok(make_sexp_str(s)),

        // Lists -- check for special forms first
        Sexp::List(children, span) => {
            expand_qq_list(children, depth, *span, "macros/SexpList", gensym_map)
        }

        // Brackets -- same as lists but with macros/SexpBracket constructor
        Sexp::Bracket(children, span) => {
            expand_qq_list(children, depth, *span, "macros/SexpBracket", gensym_map)
        }

        // Comments are not meaningful in quasiquoted forms; pass through as-is.
        Sexp::Comment(_, _) => Ok(template.clone()),
    }
}

/// Handle list/bracket forms within quasiquote expansion.
///
/// Checks for `unquote`, `unquote-splicing`, and nested `quasiquote` before
/// falling through to the general children expansion.
fn expand_qq_list(
    children: &[Sexp],
    depth: usize,
    span: Span,
    ctor: &str,
    gensym_map: &mut HashMap<String, String>,
) -> Result<Sexp, CranelispError> {
    if children.is_empty() {
        return Ok(make_sexp_container(ctor, make_slist(vec![])));
    }

    // Only check for unquote/quasiquote special forms in true lists,
    // not brackets (brackets cannot contain these as head forms).
    if ctor == "macros/SexpList" {
        // (unquote expr) at depth 0 -> return expr as-is
        if is_unquote(children) {
            if depth == 0 {
                return Ok(children[1].clone());
            }
            // Deeper depth: decrement and recurse, wrap result
            let inner = expand_qq_template(&children[1], depth - 1, gensym_map)?;
            return Ok(make_sexp_container(
                ctor,
                make_slist(vec![make_sexp_sym("unquote"), inner]),
            ));
        }

        // (unquote-splicing expr) at top level -> error
        if is_unquote_splicing(children) {
            if depth == 0 {
                return Err(CranelispError::ParseError {
                    message:
                        "unquote-splicing (~@) not valid at top level of quasiquote".to_string(),
                    location: ErrorLocation::from_span(span),
                });
            }
            let inner = expand_qq_template(&children[1], depth - 1, gensym_map)?;
            return Ok(make_sexp_container(
                ctor,
                make_slist(vec![make_sexp_sym("unquote-splicing"), inner]),
            ));
        }

        // (quasiquote form) -> increment depth
        if is_quasiquote(children) {
            let inner = expand_qq_template(&children[1], depth + 1, gensym_map)?;
            return Ok(make_sexp_container(
                ctor,
                make_slist(vec![make_sexp_sym("quasiquote"), inner]),
            ));
        }
    }

    // General case: expand children, handling splicing
    expand_qq_children(children, depth, ctor, gensym_map)
}

/// Expand children of a list/bracket form within quasiquote.
///
/// If no child uses `~@`, produces `(Ctor (SCons qq(c0) (SCons qq(c1) ... SNil)))`.
/// If any child uses `~@`, segments into groups and chains with `sconcat`.
fn expand_qq_children(
    children: &[Sexp],
    depth: usize,
    ctor: &str,
    gensym_map: &mut HashMap<String, String>,
) -> Result<Sexp, CranelispError> {
    let has_splice = depth == 0
        && children
            .iter()
            .any(|c| matches!(c, Sexp::List(ch, _) if is_unquote_splicing(ch)));

    if !has_splice {
        // Simple case: no splicing, recurse on each child.
        let expanded: Vec<Sexp> = children
            .iter()
            .map(|c| expand_qq_template(c, depth, gensym_map))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(make_sexp_container(ctor, make_slist(expanded)))
    } else {
        // Splicing case: segment into groups.
        expand_qq_spliced(children, depth, ctor, gensym_map)
    }
}

/// Handle the splicing case where at least one child uses `~@`.
///
/// Non-splice elements are grouped into `(SCons ...)` segments. Splice elements
/// contribute their expression directly. All segments are chained with `sconcat`.
fn expand_qq_spliced(
    children: &[Sexp],
    depth: usize,
    ctor: &str,
    gensym_map: &mut HashMap<String, String>,
) -> Result<Sexp, CranelispError> {
    let mut segments: Vec<Sexp> = Vec::new();
    let mut current_group: Vec<Sexp> = Vec::new();

    for child in children {
        if let Sexp::List(ch, _) = child
            && is_unquote_splicing(ch)
            && depth == 0
        {
            // Flush current group.
            if !current_group.is_empty() {
                segments.push(make_slist(std::mem::take(&mut current_group)));
            }
            // Add splice expression directly.
            segments.push(ch[1].clone());
            continue;
        }
        current_group.push(expand_qq_template(child, depth, gensym_map)?);
    }
    // Flush remaining group.
    if !current_group.is_empty() {
        segments.push(make_slist(current_group));
    }

    // Chain segments with sconcat: sconcat(s0, sconcat(s1, sconcat(s2, ...)))
    let Some(mut result) = segments.pop() else {
        unreachable!("invariant: at least one segment must exist when splicing is present");
    };
    while let Some(seg) = segments.pop() {
        result = make_sconcat(seg, result);
    }

    Ok(make_sexp_container(ctor, result))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: parse a source string into a single Sexp.
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

    // -- Integer literal expansion --

    // spec: 09-macros.md section 9.4.2 -- integer literal in quasiquote
    #[test]
    fn expand_qq_integer() {
        let sexp = parse_one("`42");
        let result = expand_quasiquotes(&sexp).unwrap();
        assert!(is_list_headed_by(&result, "macros/SexpInt"));
        if let Sexp::List(ch, _) = &result {
            assert!(matches!(&ch[1], Sexp::Int(42, _)));
        }
    }

    // -- String literal expansion --

    // spec: 09-macros.md section 9.4.2 -- string literal in quasiquote
    #[test]
    fn expand_qq_string() {
        let sexp = parse_one("`\"hello\"");
        let result = expand_quasiquotes(&sexp).unwrap();
        assert!(is_list_headed_by(&result, "macros/SexpStr"));
        if let Sexp::List(ch, _) = &result {
            assert!(matches!(&ch[1], Sexp::Str(s, _) if s == "hello"));
        }
    }

    // -- Symbol expansion --

    // spec: 09-macros.md section 9.4.2 -- symbol in quasiquote
    #[test]
    fn expand_qq_symbol() {
        let sexp = parse_one("`foo");
        let result = expand_quasiquotes(&sexp).unwrap();
        assert!(is_list_headed_by(&result, "macros/SexpSym"));
        if let Sexp::List(ch, _) = &result {
            assert!(matches!(&ch[1], Sexp::Str(s, _) if s == "foo"));
        }
    }

    // -- Unquote pass-through --

    // spec: 09-macros.md section 9.4.2 -- unquote evaluates expr
    #[test]
    fn expand_qq_unquote() {
        let sexp = parse_one("`~x");
        let result = expand_quasiquotes(&sexp).unwrap();
        // ~x should pass through as a bare symbol reference
        assert!(matches!(&result, Sexp::Symbol(s, _) if s == "x"));
    }

    // -- List expansion (nested SCons/SNil) --

    // spec: 09-macros.md section 9.4.2 -- list in quasiquote
    #[test]
    fn expand_qq_list() {
        let sexp = parse_one("`(a b)");
        let result = expand_quasiquotes(&sexp).unwrap();
        // Should be (macros/SexpList (macros/SCons <a> (macros/SCons <b> macros/SNil)))
        assert!(is_list_headed_by(&result, "macros/SexpList"));
        assert!(contains_symbol(&result, "macros/SCons"));
        assert!(contains_symbol(&result, "macros/SNil"));
    }

    // -- Bracket expansion --

    // spec: 09-macros.md section 9.4.2 -- bracket in quasiquote
    #[test]
    fn expand_qq_bracket() {
        let sexp = parse_one("`[a b]");
        let result = expand_quasiquotes(&sexp).unwrap();
        // Should be (macros/SexpBracket (macros/SCons <a> (macros/SCons <b> macros/SNil)))
        assert!(is_list_headed_by(&result, "macros/SexpBracket"));
        assert!(contains_symbol(&result, "macros/SCons"));
    }

    // -- Float and Bool expansion --

    // spec: 09-macros.md section 9.4.2 -- float literal in quasiquote
    #[test]
    fn expand_qq_float() {
        let sexp = parse_one("`3.14");
        let result = expand_quasiquotes(&sexp).unwrap();
        assert!(is_list_headed_by(&result, "macros/SexpFloat"));
    }

    // spec: 09-macros.md section 9.4.2 -- boolean literal in quasiquote
    #[test]
    fn expand_qq_bool() {
        let sexp = parse_one("`true");
        let result = expand_quasiquotes(&sexp).unwrap();
        assert!(is_list_headed_by(&result, "macros/SexpBool"));
    }

    // -- Auto-gensym consistency within one expansion --

    // spec: 09-macros.md section 9.8.1 -- auto-gensym consistency
    #[test]
    fn expand_qq_auto_gensym_consistent() {
        // `(let [x# 1] x#) should produce the same generated name for both x#
        let sexp = parse_one("`(let [x# 1] x#)");
        let result = expand_quasiquotes(&sexp).unwrap();
        // Find all SexpSym nodes with auto-generated names
        let mut auto_names = Vec::new();
        collect_auto_gensyms(&result, &mut auto_names);
        // Should have exactly 2 occurrences of the same auto name
        let x_autos: Vec<&str> = auto_names
            .iter()
            .filter(|n| n.starts_with("x__auto_"))
            .map(|s| s.as_str())
            .collect();
        assert_eq!(x_autos.len(), 2, "expected two x# auto-gensyms");
        assert_eq!(x_autos[0], x_autos[1], "both x# should produce same name");
    }

    // -- Auto-gensym uniqueness across expansions --

    // spec: 09-macros.md section 9.8.1 -- auto-gensym uniqueness
    #[test]
    fn expand_qq_auto_gensym_unique_across() {
        let sexp1 = parse_one("`x#");
        let result1 = expand_quasiquotes(&sexp1).unwrap();
        let sexp2 = parse_one("`x#");
        let result2 = expand_quasiquotes(&sexp2).unwrap();
        // The two expansions should produce different names
        let name1 = extract_sexp_sym_value(&result1);
        let name2 = extract_sexp_sym_value(&result2);
        assert_ne!(name1, name2, "different expansions should produce different names");
    }

    // -- Nested quasiquote (depth > 0) --

    // spec: 09-macros.md section 9.4.2 -- nested quasiquote increments depth
    #[test]
    fn expand_qq_nested() {
        // ``~x should produce (SexpList (SCons (SexpSym "quasiquote") (SCons (SexpList ...) SNil)))
        // The inner quasiquote form is structurally quoted, not expanded
        let sexp = parse_one("``~x");
        let result = expand_quasiquotes(&sexp).unwrap();
        // The result should contain "quasiquote" as a quoted symbol
        assert!(contains_symbol(&result, "macros/SexpSym"));
        // And the inner ~x should NOT have been passed through
        // (it should be quoted as a list with "unquote" head)
    }

    // -- Quote expansion --

    // spec: 09-macros.md section 9.4.2 -- quote is pure structural quotation
    #[test]
    fn expand_quote_basic() {
        let sexp = parse_one("'(a b)");
        let result = expand_quasiquotes(&sexp).unwrap();
        assert!(is_list_headed_by(&result, "macros/SexpList"));
        assert!(contains_symbol(&result, "macros/SCons"));
    }

    // -- Unquote splicing --

    // spec: 09-macros.md section 9.4.2 -- unquote-splicing in list
    #[test]
    fn expand_qq_splice_in_list() {
        let sexp = parse_one("`(a ~@xs b)");
        let result = expand_quasiquotes(&sexp).unwrap();
        // Should contain sconcat call for splicing
        assert!(contains_symbol(&result, "macros/sconcat"));
        assert!(is_list_headed_by(&result, "macros/SexpList"));
    }

    // -- Splicing at top level is an error --

    // spec: 09-macros.md section 9.4.2 -- unquote-splicing at top level
    #[test]
    fn expand_qq_splice_top_level_error() {
        let sexp = parse_one("`~@xs");
        let result = expand_quasiquotes(&sexp);
        assert!(result.is_err(), "~@ at top level should be an error");
    }

    // -- Empty list --

    // spec: 09-macros.md section 9.4.2 -- empty list in quasiquote
    #[test]
    fn expand_qq_empty_list() {
        let sexp = parse_one("`()");
        let result = expand_quasiquotes(&sexp).unwrap();
        assert!(is_list_headed_by(&result, "macros/SexpList"));
        assert!(contains_symbol(&result, "macros/SNil"));
    }

    // -- Helpers for tests --

    fn collect_auto_gensyms(sexp: &Sexp, out: &mut Vec<String>) {
        match sexp {
            Sexp::List(ch, _) => {
                // Check for (macros/SexpSym "x__auto_...")
                if ch.len() == 2 {
                    if let Sexp::Symbol(head, _) = &ch[0] {
                        if head == "macros/SexpSym" {
                            if let Sexp::Str(name, _) = &ch[1] {
                                if name.contains("__auto_") {
                                    out.push(name.clone());
                                }
                            }
                        }
                    }
                }
                for c in ch {
                    collect_auto_gensyms(c, out);
                }
            }
            Sexp::Bracket(ch, _) => {
                for c in ch {
                    collect_auto_gensyms(c, out);
                }
            }
            _ => {}
        }
    }

    fn extract_sexp_sym_value(sexp: &Sexp) -> String {
        if let Sexp::List(ch, _) = sexp {
            if ch.len() == 2 {
                if let Sexp::Symbol(head, _) = &ch[0] {
                    if head == "macros/SexpSym" {
                        if let Sexp::Str(name, _) = &ch[1] {
                            return name.clone();
                        }
                    }
                }
            }
        }
        panic!("expected (macros/SexpSym \"...\"), got {:?}", sexp);
    }
}
