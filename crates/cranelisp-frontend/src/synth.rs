//! Synthetic-`Sexp` construction kit (audit R4, FIXME 0679).
//!
//! The ONE set of span-allocating `Sexp` primitives shared by quasiquote
//! desugaring ([`crate::quasiquote`]) and defmacro clause synthesis
//! ([`crate::defmacro`]). Both modules previously hand-rolled the SAME
//! `Sexp::{Symbol,List,Bracket,…}` + `next_synthetic_span()` shape against an
//! implicit lock with `ast_builder`'s consumption of these forms — two
//! constructor DSLs over one shape. Consolidating the primitives here means a
//! change to how a synthetic form is spanned or shaped is ONE edit (Principle 7);
//! module-specific composites (the `macros/`-qualified ctor calls in quasiquote;
//! the per-clause `defn`/`match` scaffolding in defmacro) layer ON TOP of these
//! primitives rather than re-deriving them.
//!
//! Every primitive draws a fresh synthetic span from the single crate counter
//! (`quasiquote::SYNTHETIC_SPAN_COUNTER`, BC invariant 4 — synthetic spans are
//! unique). Span VALUES are opaque (≥ 1_000_000, uniqueness is the only
//! contract), so a call-count change across a refactor is behaviour-preserving.

use cranelisp_types::{Sexp, Span};

use crate::quasiquote::next_synthetic_span;

/// A fresh unique synthetic span (delegates to the single crate counter).
fn span() -> Span {
    next_synthetic_span()
}

/// `Sexp::Symbol(name)` — a synthetic symbol atom (bare or `macros/`-qualified).
pub(crate) fn sym(name: &str) -> Sexp {
    Sexp::Symbol(name.to_string(), span())
}

/// `Sexp::Int(v)` — a synthetic integer literal.
pub(crate) fn int(v: i64) -> Sexp {
    Sexp::Int(v, span())
}

/// `Sexp::Float(v)` — a synthetic float literal.
pub(crate) fn float(v: f64) -> Sexp {
    Sexp::Float(v, span())
}

/// `Sexp::Bool(v)` — a synthetic boolean literal.
pub(crate) fn bool(v: bool) -> Sexp {
    Sexp::Bool(v, span())
}

/// `Sexp::Str(v)` — a synthetic string literal.
pub(crate) fn str(v: &str) -> Sexp {
    Sexp::Str(v.to_string(), span())
}

/// `Sexp::List(items)` — a synthetic parenthesised form.
pub(crate) fn list(items: Vec<Sexp>) -> Sexp {
    Sexp::List(items, span())
}

/// `Sexp::Bracket(items)` — a synthetic bracket (params / vec / arm) form.
pub(crate) fn bracket(items: Vec<Sexp>) -> Sexp {
    Sexp::Bracket(items, span())
}

/// `Sexp::Annotated { annotation, subject }` — a synthetic reader-folded
/// annotation. Synthetic trees bypass the reader, so callers must construct
/// the structural form directly rather than reproducing the source tokens.
pub(crate) fn annotated(annotation: Sexp, subject: Sexp) -> Sexp {
    Sexp::Annotated {
        annotation: Box::new(annotation),
        subject: Box::new(subject),
        span: span(),
    }
}

/// A `macros/`-qualified list cell `(macros/SCons head tail)` — the shared
/// list-cell shape both quasiquote (SList construction) and defmacro (SCons
/// destructuring patterns) build.
pub(crate) fn cons(head: Sexp, tail: Sexp) -> Sexp {
    list(vec![sym("macros/SCons"), head, tail])
}

/// The `macros/`-qualified empty-list marker `macros/SNil`.
pub(crate) fn nil() -> Sexp {
    sym("macros/SNil")
}

#[cfg(test)]
mod tests {
    use super::*;

    // Every primitive draws a UNIQUE synthetic span (BC invariant 4); the
    // shapes match what `ast_builder` consumes.
    #[test]
    fn primitives_shape_and_unique_spans() {
        assert!(matches!(sym("x"), Sexp::Symbol(ref s, _) if s == "x"));
        assert!(matches!(int(3), Sexp::Int(3, _)));
        assert!(matches!(str("s"), Sexp::Str(ref s, _) if s == "s"));
        assert!(matches!(list(vec![]), Sexp::List(_, _)));
        assert!(matches!(bracket(vec![]), Sexp::Bracket(_, _)));
        assert!(matches!(
            annotated(sym("Int"), sym("x")),
            Sexp::Annotated { annotation, subject, .. }
                if matches!(*annotation, Sexp::Symbol(ref s, _) if s == "Int")
                    && matches!(*subject, Sexp::Symbol(ref s, _) if s == "x")
        ));

        // Synthetic spans are unique (>= 1_000_000) across a batch of atoms.
        let a = sym("a");
        let b = sym("b");
        assert_ne!(a.span(), b.span());
        assert!(a.span().start >= 1_000_000);
    }

    // `cons`/`nil` build the `(macros/SCons head tail)` / `macros/SNil` list-cell
    // shapes shared by quasiquote construction and defmacro destructuring.
    #[test]
    fn cons_nil_list_cell_shapes() {
        assert!(matches!(nil(), Sexp::Symbol(ref s, _) if s == "macros/SNil"));
        match cons(int(1), nil()) {
            Sexp::List(items, _) => {
                assert_eq!(items.len(), 3);
                assert!(matches!(&items[0], Sexp::Symbol(s, _) if s == "macros/SCons"));
                assert!(matches!(&items[1], Sexp::Int(1, _)));
                assert!(matches!(&items[2], Sexp::Symbol(s, _) if s == "macros/SNil"));
            }
            other => panic!("expected SCons list, got {other:?}"),
        }
    }
}
