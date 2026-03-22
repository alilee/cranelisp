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
        }
    }

    /// Pretty-print with indentation for long forms.
    ///
    /// Short forms (<=60 chars flat) are kept on one line.
    /// Longer forms are broken across lines with 2-space indentation.
    pub fn format_indented(&self, indent: usize) -> String {
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
            _ => flat,
        }
    }
}

impl std::fmt::Display for Sexp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.format_indented(0))
    }
}
