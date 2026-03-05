use serde::{Deserialize, Serialize};

use crate::Span;

/// S-expression: the reader's output. 7 variants covering all syntactic forms.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Sexp {
    /// Symbol: `foo`, `+`, `defn`, `core/map`
    Symbol(String, Span),
    /// Integer literal: `42`, `-3`
    Int(i64, Span),
    /// Float literal: `3.14`, `-0.5`
    Float(f64, Span),
    /// Boolean literal: `true`, `false`
    Bool(bool, Span),
    /// String literal: `"hello"`
    Str(String, Span),
    /// Parenthesized list: `(f x y)`, `(defn add [a b] (+ a b))`
    List(Vec<Sexp>, Span),
    /// Bracketed list: `[a b c]`, `[:Int x :Int y]`
    Bracket(Vec<Sexp>, Span),
}

impl Sexp {
    /// Returns the span of this S-expression.
    pub fn span(&self) -> Span {
        match self {
            Sexp::Symbol(_, s)
            | Sexp::Int(_, s)
            | Sexp::Float(_, s)
            | Sexp::Bool(_, s)
            | Sexp::Str(_, s)
            | Sexp::List(_, s)
            | Sexp::Bracket(_, s) => *s,
        }
    }
}
