use serde::{Deserialize, Serialize};

use crate::Span;

/// Structural reader form introduced by one of the four quote heads.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuoteHead {
    /// Preserve the subject as literal structural data without evaluation.
    Quote,
    /// Build structural data while permitting nested unquote operations.
    Quasiquote,
    /// Evaluate one subject within the enclosing quasiquote.
    Unquote,
    /// Evaluate one subject and splice its elements into the enclosing
    /// quasiquoted list.
    UnquoteSplicing,
}

/// Classify an exact two-element reader quote form.
///
/// Qualification and any arity other than one subject are deliberately not
/// quote syntax at this structural boundary.
pub fn quote_head(children: &[Sexp]) -> Option<QuoteHead> {
    let [Sexp::Symbol(head, _), _subject] = children else {
        return None;
    };
    match head.as_str() {
        "quote" => Some(QuoteHead::Quote),
        "quasiquote" => Some(QuoteHead::Quasiquote),
        "unquote" => Some(QuoteHead::Unquote),
        "unquote-splicing" => Some(QuoteHead::UnquoteSplicing),
        _ => None,
    }
}

/// S-expression: the reader's structural output.
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
    /// `:Type <form>` — a read-time annotation fold.
    Annotated {
        annotation: Box<Sexp>,
        subject: Box<Sexp>,
        /// Span from the colon introducer through the end of `subject`.
        span: Span,
    },
    /// Comment: `; some text` — preserved only in comment-preserving reader mode
    Comment(String, Span),
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
            | Sexp::Bracket(_, s)
            | Sexp::Comment(_, s) => *s,
            Sexp::Annotated { span, .. } => *span,
        }
    }

    /// Format as a single line (no indentation).
    pub fn format_flat(&self) -> String {
        match self {
            Sexp::Symbol(s, _) => s.clone(),
            Sexp::Int(v, _) => v.to_string(),
            Sexp::Float(v, _) => {
                let s = format!("{v}");
                if s.contains('.') { s } else { format!("{s}.0") }
            }
            Sexp::Bool(v, _) => if *v { "true" } else { "false" }.to_string(),
            Sexp::Str(s, _) => {
                let escaped = s
                    .replace('\\', "\\\\")
                    .replace('"', "\\\"")
                    .replace('\n', "\\n")
                    .replace('\t', "\\t");
                format!("\"{escaped}\"")
            }
            Sexp::List(children, _) => {
                let parts: Vec<String> = children.iter().map(|c| c.format_flat()).collect();
                format!("({})", parts.join(" "))
            }
            Sexp::Bracket(children, _) => {
                let parts: Vec<String> = children.iter().map(|c| c.format_flat()).collect();
                format!("[{}]", parts.join(" "))
            }
            Sexp::Annotated {
                annotation,
                subject,
                ..
            } => {
                format!(":{} {}", annotation.format_flat(), subject.format_flat())
            }
            Sexp::Comment(text, _) => {
                if text.is_empty() {
                    ";".to_string()
                } else {
                    format!("; {text}")
                }
            }
        }
    }

    /// Pretty-print with indentation for long forms.
    ///
    /// Short forms (<=60 chars flat) are kept on one line.
    /// Longer forms are broken across lines with 2-space indentation.
    pub fn format_indented(&self, indent: usize) -> String {
        // Comments are always single-line; skip the length check.
        if matches!(self, Sexp::Comment(_, _)) {
            return self.format_flat();
        }
        let flat = self.format_flat();
        if flat.len() <= 60 {
            return flat;
        }
        match self {
            Sexp::List(children, _) if !children.is_empty() => {
                let child_indent = indent + 2;
                let pad = " ".repeat(child_indent);
                // Greedily fit short items on first line
                let mut first_line = format!("({}", children[0].format_flat());
                let mut rest_start = 1;
                while rest_start < children.len() {
                    let next_flat = children[rest_start].format_flat();
                    if first_line.len() + 1 + next_flat.len() <= 60 {
                        first_line.push(' ');
                        first_line.push_str(&next_flat);
                        rest_start += 1;
                    } else {
                        break;
                    }
                }
                if rest_start >= children.len() {
                    first_line.push(')');
                    return first_line;
                }
                let mut result = first_line;
                for child in &children[rest_start..] {
                    let child_str = child.format_indented(child_indent);
                    result.push('\n');
                    result.push_str(&pad);
                    result.push_str(&child_str);
                }
                result.push(')');
                result
            }
            Sexp::Bracket(children, _) if !children.is_empty() => {
                let child_indent = indent + 1;
                let pad = " ".repeat(child_indent);
                let mut first_line = format!("[{}", children[0].format_flat());
                let mut rest_start = 1;
                while rest_start < children.len() {
                    let next_flat = children[rest_start].format_flat();
                    if first_line.len() + 1 + next_flat.len() <= 60 {
                        first_line.push(' ');
                        first_line.push_str(&next_flat);
                        rest_start += 1;
                    } else {
                        break;
                    }
                }
                if rest_start >= children.len() {
                    first_line.push(']');
                    return first_line;
                }
                let mut result = first_line;
                for child in &children[rest_start..] {
                    let child_str = child.format_indented(child_indent);
                    result.push('\n');
                    result.push_str(&pad);
                    result.push_str(&child_str);
                }
                result.push(']');
                result
            }
            Sexp::Annotated {
                annotation,
                subject,
                ..
            } => {
                format!(
                    ":{} {}",
                    annotation.format_flat(),
                    subject.format_indented(indent + 2)
                )
            }
            _ => flat,
        }
    }
}

impl std::fmt::Display for Sexp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.format_indented(0))
    }
}

#[cfg(test)]
mod quote_head_tests {
    use super::*;

    fn sym(name: &str) -> Sexp {
        Sexp::Symbol(name.to_string(), Span::SYNTHETIC)
    }

    #[test]
    fn exact_reader_quote_heads_are_closed_and_arity_checked() {
        for (name, expected) in [
            ("quote", QuoteHead::Quote),
            ("quasiquote", QuoteHead::Quasiquote),
            ("unquote", QuoteHead::Unquote),
            ("unquote-splicing", QuoteHead::UnquoteSplicing),
        ] {
            assert_eq!(quote_head(&[sym(name), sym("x")]), Some(expected));
        }
        assert_eq!(quote_head(&[sym("macros/quote"), sym("x")]), None);
        assert_eq!(quote_head(&[sym("quote")]), None);
        assert_eq!(quote_head(&[sym("quote"), sym("x"), sym("y")]), None);
        assert_eq!(quote_head(&[Sexp::Int(1, Span::SYNTHETIC), sym("x")]), None);
    }
}
