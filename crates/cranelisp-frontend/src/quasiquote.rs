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

use crate::synth;

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
//
// These are the quasiquote-specific COMPOSITES — `macros/`-qualified ctor
// calls — layered on the shared `crate::synth` primitives (audit R4, FIXME
// 0679). The primitive `Sexp::{Symbol,List,…}` + span construction lives in
// `synth`; these name the ctor vocabulary.
// ---------------------------------------------------------------------------

/// Build `(macros/SexpSym "name")`.
fn make_sexp_sym(name: &str) -> Sexp {
    synth::list(vec![synth::sym("macros/SexpSym"), synth::str(name)])
}

/// Build `(macros/SexpInt val)`.
fn make_sexp_int(val: i64) -> Sexp {
    synth::list(vec![synth::sym("macros/SexpInt"), synth::int(val)])
}

/// Build `(macros/SexpFloat val)`.
fn make_sexp_float(val: f64) -> Sexp {
    synth::list(vec![synth::sym("macros/SexpFloat"), synth::float(val)])
}

/// Build `(macros/SexpBool val)`.
fn make_sexp_bool(val: bool) -> Sexp {
    synth::list(vec![synth::sym("macros/SexpBool"), synth::bool(val)])
}

/// Build `(macros/SexpStr "val")`.
fn make_sexp_str(val: &str) -> Sexp {
    synth::list(vec![synth::sym("macros/SexpStr"), synth::str(val)])
}

/// Build `(ctor items_sexp)` where `ctor` is `macros/SexpList` or `macros/SexpBracket`.
fn make_sexp_container(ctor: &str, items_sexp: Sexp) -> Sexp {
    synth::list(vec![synth::sym(ctor), items_sexp])
}

/// Build nested `(macros/SCons e0 (macros/SCons e1 ... macros/SNil))`.
fn make_slist(elements: Vec<Sexp>) -> Sexp {
    elements
        .into_iter()
        .rev()
        .fold(synth::nil(), |acc, elem| synth::cons(elem, acc))
}

/// Build `(macros/sconcat a b)`.
fn make_sconcat(a: Sexp, b: Sexp) -> Sexp {
    synth::list(vec![synth::sym("macros/sconcat"), a, b])
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
/// access needed. Invoked by int/typecheck before macro-head dispatch,
/// so user macros see already-desugared template syntax. (Post-S76
/// W-Macro the frontend no longer hosts an `expand` entry; quasiquote
/// desugaring is the frontend's only syntactic-rewrite step.)
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
mod tests;
