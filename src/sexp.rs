use std::fmt;

use serde::{Deserialize, Serialize};

use crate::error::CranelispError;

/// Byte offset range in source text.
pub type Span = (usize, usize);

/// Generic S-expression tree — output of Phase 1 parsing.
/// Knows nothing about defn, let, if, etc. — just balanced delimiters, atoms,
/// strings, comments, and quasiquote reader syntax.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Sexp {
    Symbol(String, Span),
    Int(i64, Span),
    Float(f64, Span),
    Bool(bool, Span),
    Str(String, Span),
    List(Vec<Sexp>, Span),    // (...)
    Bracket(Vec<Sexp>, Span), // [...]
}

impl Sexp {
    /// Return the span for any Sexp variant.
    pub fn span(&self) -> Span {
        match self {
            Sexp::Symbol(_, s) => *s,
            Sexp::Int(_, s) => *s,
            Sexp::Float(_, s) => *s,
            Sexp::Bool(_, s) => *s,
            Sexp::Str(_, s) => *s,
            Sexp::List(_, s) => *s,
            Sexp::Bracket(_, s) => *s,
        }
    }
}

impl Sexp {
    /// Render this S-expression as a flat single-line string.
    fn format_flat(&self) -> String {
        match self {
            Sexp::Symbol(s, _) => s.clone(),
            Sexp::Int(v, _) => v.to_string(),
            Sexp::Float(v, _) => {
                let s = format!("{}", v);
                if s.contains('.') {
                    s
                } else {
                    format!("{}.0", s)
                }
            }
            Sexp::Bool(v, _) => if *v { "true" } else { "false" }.to_string(),
            Sexp::Str(s, _) => {
                let escaped = s
                    .replace('\\', "\\\\")
                    .replace('"', "\\\"")
                    .replace('\n', "\\n")
                    .replace('\t', "\\t");
                format!("\"{}\"", escaped)
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

impl fmt::Display for Sexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.format_indented(0))
    }
}

peg::parser! {
    grammar sexp_parser() for str {
        rule comment() = ";" [^ '\n']* ("\n" / ![_])

        rule ws() = quiet!{([' ' | '\t' | '\n' | '\r' | ','] / comment())*}

        rule float() -> (f64, Span)
            = s:position!() n:$("-"? ['0'..='9']+ "." ['0'..='9']+) e:position!()
              {? n.parse::<f64>().map(|v| (v, (s, e))).or(Err("float")) }

        rule integer() -> (i64, Span)
            = s:position!() "+" n:$(['0'..='9']+) e:position!()
              {? n.parse::<i64>().map(|v| (v, (s, e))).or(Err("integer")) }
            / s:position!() n:$("-"? ['0'..='9']+) e:position!()
              {? n.parse::<i64>().map(|v| (v, (s, e))).or(Err("integer")) }

        rule symbol_char() -> char
            = c:['a'..='z' | 'A'..='Z' | '0'..='9' | '_' | '-' | '?' | '!'] { c }

        rule boolean() -> (bool, Span)
            = s:position!() "true" !symbol_char() e:position!() { (true, (s, e)) }
            / s:position!() "false" !symbol_char() e:position!() { (false, (s, e)) }

        rule string_char() -> char
            = "\\n" { '\n' }
            / "\\t" { '\t' }
            / "\\\\" { '\\' }
            / "\\\"" { '"' }
            / c:[^ '"' | '\\'] { c }

        rule string_literal() -> (String, Span)
            = s:position!() "\"" chars:string_char()* "\"" e:position!()
              { (chars.into_iter().collect(), (s, e)) }

        rule symbol() -> (String, Span)
            = s:position!() name:$(['a'..='z' | 'A'..='Z' | '_'] symbol_char()*)
              e:position!()
              { (name.to_string(), (s, e)) }

        rule operator_char() -> char
            = c:['+' | '-' | '*' | '/' | '=' | '<' | '>'] { c }

        rule operator_symbol() -> (String, Span)
            = s:position!() name:$(operator_char()+) !['0'..='9'] e:position!()
              { (name.to_string(), (s, e)) }

        rule qualified_symbol() -> (String, Span)
            = s:position!()
              module:$(
                  ['a'..='z' | 'A'..='Z' | '_'] symbol_char()*
                  ("." ['a'..='z' | 'A'..='Z' | '_'] symbol_char()*)*
              )
              "/"
              local:$(
                  // Try dotted local name first (longer match)
                  ['a'..='z' | 'A'..='Z' | '_'] symbol_char()* "." (symbol_char()+ / operator_char()+)
                  / ['a'..='z' | 'A'..='Z' | '_'] symbol_char()*
                  / operator_char()+
              )
              e:position!()
              { (format!("{}/{}", module, local), (s, e)) }

        rule dotted_symbol() -> (String, Span)
            = s:position!()
              parent:$(['a'..='z' | 'A'..='Z' | '_'] symbol_char()*)
              "."
              member:$(symbol_char()+ / operator_char()+)
              e:position!()
              { (format!("{}.{}", parent, member), (s, e)) }

        rule colon_prefix() -> (String, Span)
            = s:position!() ":" name:$(['a'..='z' | 'A'..='Z' | '_'] symbol_char()*)
              e:position!()
              { (format!(":{}", name), (s, e)) }

        rule colon_bare() -> (String, Span)
            = s:position!() ":" !symbol_char() e:position!()
              { (":".to_string(), (s, e)) }

        rule ampersand() -> (String, Span)
            = s:position!() "&" !symbol_char() e:position!()
              { ("&".to_string(), (s, e)) }

        rule atom() -> Sexp
            = v:float() { Sexp::Float(v.0, v.1) }
            / v:integer() { Sexp::Int(v.0, v.1) }
            / v:boolean() { Sexp::Bool(v.0, v.1) }
            / v:string_literal() { Sexp::Str(v.0, v.1) }
            / v:colon_prefix() { Sexp::Symbol(v.0, v.1) }
            / v:colon_bare() { Sexp::Symbol(v.0, v.1) }
            / v:ampersand() { Sexp::Symbol(v.0, v.1) }
            / v:qualified_symbol() { Sexp::Symbol(v.0, v.1) }
            / v:dotted_symbol() { Sexp::Symbol(v.0, v.1) }
            / v:operator_symbol() { Sexp::Symbol(v.0, v.1) }
            / v:symbol() { Sexp::Symbol(v.0, v.1) }

        rule list() -> Sexp
            = s:position!() "(" ws() children:form()* ws() ")" e:position!()
              { Sexp::List(children, (s, e)) }

        rule bracket() -> Sexp
            = s:position!() "[" ws() children:form()* ws() "]" e:position!()
              { Sexp::Bracket(children, (s, e)) }

        rule quasiquote() -> Sexp
            = s:position!() "`" f:form() e:position!()
              {
                  Sexp::List(vec![
                      Sexp::Symbol("quasiquote".to_string(), (s, s + 1)),
                      f,
                  ], (s, e))
              }

        rule unquote_splicing() -> Sexp
            = s:position!() "~@" f:form() e:position!()
              {
                  Sexp::List(vec![
                      Sexp::Symbol("unquote-splicing".to_string(), (s, s + 2)),
                      f,
                  ], (s, e))
              }

        rule unquote() -> Sexp
            = s:position!() "~" f:form() e:position!()
              {
                  Sexp::List(vec![
                      Sexp::Symbol("unquote".to_string(), (s, s + 1)),
                      f,
                  ], (s, e))
              }

        rule form() -> Sexp
            = ws() f:(quasiquote() / unquote_splicing() / unquote()
                      / list() / bracket() / atom()) ws()
              { f }

        pub rule parse_single() -> Sexp
            = ws() f:form() ws() { f }

        pub rule parse_multi() -> Vec<Sexp>
            = ws() forms:form()* ws() { forms }
    }
}

/// Parse source text into a single Sexp form.
pub fn parse_sexp(input: &str) -> Result<Sexp, CranelispError> {
    sexp_parser::parse_single(input).map_err(|e| CranelispError::ParseError {
        message: format!("expected {}", e.expected),
        offset: e.location.offset,
    })
}

/// Parse source text into a sequence of top-level Sexp forms.
pub fn parse_sexps(input: &str) -> Result<Vec<Sexp>, CranelispError> {
    sexp_parser::parse_multi(input).map_err(|e| CranelispError::ParseError {
        message: format!("expected {}", e.expected),
        offset: e.location.offset,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const PRELUDE: &str = include_str!("unittest_prelude.cl");

    // ── Atom tests ──────────────────────────────────────────────────────

    #[test]
    fn parse_positive_integer() {
        let sexp = parse_sexp("42").unwrap();
        assert_eq!(sexp, Sexp::Int(42, (0, 2)));
    }

    #[test]
    fn parse_negative_integer() {
        let sexp = parse_sexp("-7").unwrap();
        assert_eq!(sexp, Sexp::Int(-7, (0, 2)));
    }

    #[test]
    fn parse_positive_prefix_integer() {
        let sexp = parse_sexp("+3").unwrap();
        assert_eq!(sexp, Sexp::Int(3, (0, 2)));
    }

    #[test]
    fn parse_zero() {
        let sexp = parse_sexp("0").unwrap();
        assert_eq!(sexp, Sexp::Int(0, (0, 1)));
    }

    #[test]
    fn parse_float_positive() {
        let sexp = parse_sexp("3.14").unwrap();
        match sexp {
            Sexp::Float(v, (0, 4)) => assert!((v - 3.14).abs() < 1e-10),
            other => panic!("expected Float, got {:?}", other),
        }
    }

    #[test]
    fn parse_float_negative() {
        let sexp = parse_sexp("-2.5").unwrap();
        match sexp {
            Sexp::Float(v, (0, 4)) => assert!((v - (-2.5)).abs() < 1e-10),
            other => panic!("expected Float, got {:?}", other),
        }
    }

    #[test]
    fn parse_boolean_true() {
        let sexp = parse_sexp("true").unwrap();
        assert_eq!(sexp, Sexp::Bool(true, (0, 4)));
    }

    #[test]
    fn parse_boolean_false() {
        let sexp = parse_sexp("false").unwrap();
        assert_eq!(sexp, Sexp::Bool(false, (0, 5)));
    }

    #[test]
    fn parse_boolean_boundary_true() {
        // "trueness" should parse as a symbol, not true + ness
        let sexp = parse_sexp("trueness").unwrap();
        assert_eq!(sexp, Sexp::Symbol("trueness".to_string(), (0, 8)));
    }

    #[test]
    fn parse_boolean_boundary_false() {
        let sexp = parse_sexp("falsehood").unwrap();
        assert_eq!(sexp, Sexp::Symbol("falsehood".to_string(), (0, 9)));
    }

    #[test]
    fn parse_string_simple() {
        let sexp = parse_sexp(r#""hello""#).unwrap();
        assert_eq!(sexp, Sexp::Str("hello".to_string(), (0, 7)));
    }

    #[test]
    fn parse_string_with_escapes() {
        let sexp = parse_sexp(r#""a\nb\t\\\"end""#).unwrap();
        match sexp {
            Sexp::Str(v, _) => assert_eq!(v, "a\nb\t\\\"end"),
            other => panic!("expected Str, got {:?}", other),
        }
    }

    #[test]
    fn parse_string_empty() {
        let sexp = parse_sexp(r#""""#).unwrap();
        assert_eq!(sexp, Sexp::Str(String::new(), (0, 2)));
    }

    #[test]
    fn parse_symbol_simple() {
        let sexp = parse_sexp("foo").unwrap();
        assert_eq!(sexp, Sexp::Symbol("foo".to_string(), (0, 3)));
    }

    #[test]
    fn parse_symbol_with_hyphens() {
        let sexp = parse_sexp("my-var").unwrap();
        assert_eq!(sexp, Sexp::Symbol("my-var".to_string(), (0, 6)));
    }

    #[test]
    fn parse_symbol_with_question_mark() {
        let sexp = parse_sexp("empty?").unwrap();
        assert_eq!(sexp, Sexp::Symbol("empty?".to_string(), (0, 6)));
    }

    #[test]
    fn parse_symbol_uppercase() {
        let sexp = parse_sexp("None").unwrap();
        assert_eq!(sexp, Sexp::Symbol("None".to_string(), (0, 4)));
    }

    #[test]
    fn parse_symbol_underscore_start() {
        let sexp = parse_sexp("_foo").unwrap();
        assert_eq!(sexp, Sexp::Symbol("_foo".to_string(), (0, 4)));
    }

    #[test]
    fn parse_operator_plus() {
        let sexp = parse_sexp("+ ").unwrap();
        assert_eq!(sexp, Sexp::Symbol("+".to_string(), (0, 1)));
    }

    #[test]
    fn parse_operator_minus() {
        let sexp = parse_sexp("- ").unwrap();
        assert_eq!(sexp, Sexp::Symbol("-".to_string(), (0, 1)));
    }

    #[test]
    fn parse_operator_star() {
        let sexp = parse_sexp("* ").unwrap();
        assert_eq!(sexp, Sexp::Symbol("*".to_string(), (0, 1)));
    }

    #[test]
    fn parse_operator_slash() {
        let sexp = parse_sexp("/ ").unwrap();
        assert_eq!(sexp, Sexp::Symbol("/".to_string(), (0, 1)));
    }

    #[test]
    fn parse_operator_eq() {
        let sexp = parse_sexp("= ").unwrap();
        assert_eq!(sexp, Sexp::Symbol("=".to_string(), (0, 1)));
    }

    #[test]
    fn parse_operator_le() {
        let sexp = parse_sexp("<= ").unwrap();
        assert_eq!(sexp, Sexp::Symbol("<=".to_string(), (0, 2)));
    }

    #[test]
    fn parse_operator_ge() {
        let sexp = parse_sexp(">= ").unwrap();
        assert_eq!(sexp, Sexp::Symbol(">=".to_string(), (0, 2)));
    }

    #[test]
    fn parse_operator_lt() {
        let sexp = parse_sexp("< ").unwrap();
        assert_eq!(sexp, Sexp::Symbol("<".to_string(), (0, 1)));
    }

    #[test]
    fn parse_operator_gt() {
        let sexp = parse_sexp("> ").unwrap();
        assert_eq!(sexp, Sexp::Symbol(">".to_string(), (0, 1)));
    }

    #[test]
    fn parse_operator_thread_first() {
        let sexp = parse_sexp("-> ").unwrap();
        assert_eq!(sexp, Sexp::Symbol("->".to_string(), (0, 2)));
    }

    #[test]
    fn parse_operator_thread_last() {
        let sexp = parse_sexp("->> ").unwrap();
        assert_eq!(sexp, Sexp::Symbol("->>".to_string(), (0, 3)));
    }

    #[test]
    fn parse_operator_multi_char() {
        // Any sequence of operator chars is valid
        let sexp = parse_sexp("=> ").unwrap();
        assert_eq!(sexp, Sexp::Symbol("=>".to_string(), (0, 2)));
    }

    #[test]
    fn parse_thread_first_in_list() {
        let sexp = parse_sexp("(-> 5 inc)").unwrap();
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 3);
                assert_eq!(children[0], Sexp::Symbol("->".to_string(), (1, 3)));
                assert_eq!(children[1], Sexp::Int(5, (4, 5)));
                assert_eq!(children[2], Sexp::Symbol("inc".to_string(), (6, 9)));
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    // ── Operator disambiguation ─────────────────────────────────────────

    #[test]
    fn operator_plus_vs_positive_int() {
        // +3 is a positive integer, not operator + then 3
        let sexp = parse_sexp("+3").unwrap();
        assert_eq!(sexp, Sexp::Int(3, (0, 2)));
    }

    #[test]
    fn operator_minus_vs_negative_int() {
        // -7 is a negative integer, not operator - then 7
        let sexp = parse_sexp("-7").unwrap();
        assert_eq!(sexp, Sexp::Int(-7, (0, 2)));
    }

    #[test]
    fn operator_with_space() {
        // (+ 3 4) — operator with space
        let sexp = parse_sexp("(+ 3 4)").unwrap();
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 3);
                assert_eq!(children[0], Sexp::Symbol("+".to_string(), (1, 2)));
                assert_eq!(children[1], Sexp::Int(3, (3, 4)));
                assert_eq!(children[2], Sexp::Int(4, (5, 6)));
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn operator_minus_space_number() {
        // (- 3) — minus with space, then 3
        let sexp = parse_sexp("(- 3)").unwrap();
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 2);
                assert_eq!(children[0], Sexp::Symbol("-".to_string(), (1, 2)));
                assert_eq!(children[1], Sexp::Int(3, (3, 4)));
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    // ── Colon prefix/bare ───────────────────────────────────────────────

    #[test]
    fn parse_colon_prefix() {
        let sexp = parse_sexp(":Int").unwrap();
        assert_eq!(sexp, Sexp::Symbol(":Int".to_string(), (0, 4)));
    }

    #[test]
    fn parse_colon_prefix_lowercase() {
        let sexp = parse_sexp(":a").unwrap();
        assert_eq!(sexp, Sexp::Symbol(":a".to_string(), (0, 2)));
    }

    #[test]
    fn parse_colon_prefix_display() {
        let sexp = parse_sexp(":Display").unwrap();
        assert_eq!(sexp, Sexp::Symbol(":Display".to_string(), (0, 8)));
    }

    #[test]
    fn parse_colon_bare_before_paren() {
        // ":(List a)" at sexp level: `:` as separate symbol, then `(List a)` as separate form
        let sexps = parse_sexps(":(List a)").unwrap();
        assert_eq!(sexps.len(), 2);
        assert_eq!(sexps[0], Sexp::Symbol(":".to_string(), (0, 1)));
        match &sexps[1] {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 2);
                assert_eq!(children[0], Sexp::Symbol("List".to_string(), (2, 6)));
                assert_eq!(children[1], Sexp::Symbol("a".to_string(), (7, 8)));
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn parse_colon_in_bracket() {
        // [:Int x] — colon prefix in brackets
        let sexp = parse_sexp("[:Int x]").unwrap();
        match sexp {
            Sexp::Bracket(children, _) => {
                assert_eq!(children.len(), 2);
                assert_eq!(children[0], Sexp::Symbol(":Int".to_string(), (1, 5)));
                assert_eq!(children[1], Sexp::Symbol("x".to_string(), (6, 7)));
            }
            other => panic!("expected Bracket, got {:?}", other),
        }
    }

    #[test]
    fn parse_colon_compound_in_bracket() {
        // [:(List a) tail] — bare colon + compound type in brackets
        let sexp = parse_sexp("[:(List a) tail]").unwrap();
        match sexp {
            Sexp::Bracket(children, _) => {
                assert_eq!(children.len(), 3);
                assert_eq!(children[0], Sexp::Symbol(":".to_string(), (1, 2)));
                match &children[1] {
                    Sexp::List(inner, _) => {
                        assert_eq!(inner.len(), 2);
                        assert_eq!(inner[0], Sexp::Symbol("List".to_string(), (3, 7)));
                    }
                    other => panic!("expected List, got {:?}", other),
                }
                assert_eq!(children[2], Sexp::Symbol("tail".to_string(), (11, 15)));
            }
            other => panic!("expected Bracket, got {:?}", other),
        }
    }

    // ── Compound forms ──────────────────────────────────────────────────

    #[test]
    fn parse_empty_list() {
        let sexp = parse_sexp("()").unwrap();
        assert_eq!(sexp, Sexp::List(vec![], (0, 2)));
    }

    #[test]
    fn parse_simple_list() {
        let sexp = parse_sexp("(+ 1 2)").unwrap();
        match sexp {
            Sexp::List(children, (0, 7)) => {
                assert_eq!(children.len(), 3);
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn parse_nested_list() {
        let sexp = parse_sexp("(* n (fact (- n 1)))").unwrap();
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 3);
                assert_eq!(children[0], Sexp::Symbol("*".to_string(), (1, 2)));
                assert_eq!(children[1], Sexp::Symbol("n".to_string(), (3, 4)));
                match &children[2] {
                    Sexp::List(inner, _) => {
                        assert_eq!(inner.len(), 2);
                        assert_eq!(inner[0], Sexp::Symbol("fact".to_string(), (6, 10)));
                    }
                    other => panic!("expected inner List, got {:?}", other),
                }
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn parse_empty_bracket() {
        let sexp = parse_sexp("[]").unwrap();
        assert_eq!(sexp, Sexp::Bracket(vec![], (0, 2)));
    }

    #[test]
    fn parse_bracket_with_items() {
        let sexp = parse_sexp("[x y z]").unwrap();
        match sexp {
            Sexp::Bracket(children, (0, 7)) => {
                assert_eq!(children.len(), 3);
                assert_eq!(children[0], Sexp::Symbol("x".to_string(), (1, 2)));
                assert_eq!(children[1], Sexp::Symbol("y".to_string(), (3, 4)));
                assert_eq!(children[2], Sexp::Symbol("z".to_string(), (5, 6)));
            }
            other => panic!("expected Bracket, got {:?}", other),
        }
    }

    #[test]
    fn parse_mixed_nesting() {
        let sexp = parse_sexp("(let [x 1] (+ x 2))").unwrap();
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 3);
                assert_eq!(children[0], Sexp::Symbol("let".to_string(), (1, 4)));
                assert!(matches!(&children[1], Sexp::Bracket(..)));
                assert!(matches!(&children[2], Sexp::List(..)));
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    // ── Whitespace / comments ───────────────────────────────────────────

    #[test]
    fn parse_commas_as_whitespace() {
        let sexp = parse_sexp("[1, 2, 3]").unwrap();
        match sexp {
            Sexp::Bracket(children, _) => {
                assert_eq!(children.len(), 3);
                assert_eq!(children[0], Sexp::Int(1, (1, 2)));
                assert_eq!(children[1], Sexp::Int(2, (4, 5)));
                assert_eq!(children[2], Sexp::Int(3, (7, 8)));
            }
            other => panic!("expected Bracket, got {:?}", other),
        }
    }

    #[test]
    fn parse_comment_line() {
        let sexp = parse_sexp("; this is a comment\n42").unwrap();
        assert_eq!(sexp, Sexp::Int(42, (20, 22)));
    }

    #[test]
    fn parse_inline_comment() {
        let sexp = parse_sexp("(+ 1 ; add\n 2)").unwrap();
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 3);
                assert_eq!(children[2], Sexp::Int(2, (12, 13)));
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn parse_leading_trailing_whitespace() {
        let sexp = parse_sexp("  42  ").unwrap();
        assert_eq!(sexp, Sexp::Int(42, (2, 4)));
    }

    #[test]
    fn parse_multiple_forms_with_whitespace() {
        let sexps = parse_sexps("  1  2  3  ").unwrap();
        assert_eq!(sexps.len(), 3);
        assert_eq!(sexps[0], Sexp::Int(1, (2, 3)));
        assert_eq!(sexps[1], Sexp::Int(2, (5, 6)));
        assert_eq!(sexps[2], Sexp::Int(3, (8, 9)));
    }

    // ── Quasiquote ──────────────────────────────────────────────────────

    #[test]
    fn parse_quasiquote_atom() {
        let sexp = parse_sexp("`foo").unwrap();
        match sexp {
            Sexp::List(children, (0, 4)) => {
                assert_eq!(children.len(), 2);
                assert_eq!(children[0], Sexp::Symbol("quasiquote".to_string(), (0, 1)));
                assert_eq!(children[1], Sexp::Symbol("foo".to_string(), (1, 4)));
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn parse_quasiquote_list() {
        let sexp = parse_sexp("`(a b)").unwrap();
        match sexp {
            Sexp::List(children, (0, 6)) => {
                assert_eq!(children.len(), 2);
                assert_eq!(children[0], Sexp::Symbol("quasiquote".to_string(), (0, 1)));
                match &children[1] {
                    Sexp::List(inner, (1, 6)) => {
                        assert_eq!(inner.len(), 2);
                    }
                    other => panic!("expected inner List, got {:?}", other),
                }
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn parse_unquote() {
        let sexp = parse_sexp("~x").unwrap();
        match sexp {
            Sexp::List(children, (0, 2)) => {
                assert_eq!(children.len(), 2);
                assert_eq!(children[0], Sexp::Symbol("unquote".to_string(), (0, 1)));
                assert_eq!(children[1], Sexp::Symbol("x".to_string(), (1, 2)));
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn parse_unquote_splicing() {
        let sexp = parse_sexp("~@xs").unwrap();
        match sexp {
            Sexp::List(children, (0, 4)) => {
                assert_eq!(children.len(), 2);
                assert_eq!(
                    children[0],
                    Sexp::Symbol("unquote-splicing".to_string(), (0, 2))
                );
                assert_eq!(children[1], Sexp::Symbol("xs".to_string(), (2, 4)));
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn parse_quasiquote_with_unquote_in_list() {
        let sexp = parse_sexp("`(a ~b ~@c)").unwrap();
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 2);
                assert_eq!(children[0], Sexp::Symbol("quasiquote".to_string(), (0, 1)));
                match &children[1] {
                    Sexp::List(inner, _) => {
                        assert_eq!(inner.len(), 3);
                        assert_eq!(inner[0], Sexp::Symbol("a".to_string(), (2, 3)));
                        // ~b → (unquote b)
                        match &inner[1] {
                            Sexp::List(uq, _) => {
                                assert_eq!(uq[0], Sexp::Symbol("unquote".to_string(), (4, 5)));
                                assert_eq!(uq[1], Sexp::Symbol("b".to_string(), (5, 6)));
                            }
                            other => panic!("expected unquote List, got {:?}", other),
                        }
                        // ~@c → (unquote-splicing c)
                        match &inner[2] {
                            Sexp::List(uqs, _) => {
                                assert_eq!(
                                    uqs[0],
                                    Sexp::Symbol("unquote-splicing".to_string(), (7, 9))
                                );
                                assert_eq!(uqs[1], Sexp::Symbol("c".to_string(), (9, 10)));
                            }
                            other => panic!("expected unquote-splicing List, got {:?}", other),
                        }
                    }
                    other => panic!("expected inner List, got {:?}", other),
                }
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    // ── & symbol ────────────────────────────────────────────────────────

    #[test]
    fn parse_ampersand_in_bracket() {
        let sexp = parse_sexp("[x & rest]").unwrap();
        match sexp {
            Sexp::Bracket(children, _) => {
                assert_eq!(children.len(), 3);
                assert_eq!(children[0], Sexp::Symbol("x".to_string(), (1, 2)));
                assert_eq!(children[1], Sexp::Symbol("&".to_string(), (3, 4)));
                assert_eq!(children[2], Sexp::Symbol("rest".to_string(), (5, 9)));
            }
            other => panic!("expected Bracket, got {:?}", other),
        }
    }

    // ── Span tests ──────────────────────────────────────────────────────

    #[test]
    fn span_for_atoms() {
        let sexp = parse_sexp("  42  ").unwrap();
        assert_eq!(sexp.span(), (2, 4));

        let sexp = parse_sexp("  foo  ").unwrap();
        assert_eq!(sexp.span(), (2, 5));

        let sexp = parse_sexp(r#"  "hi"  "#).unwrap();
        assert_eq!(sexp.span(), (2, 6));
    }

    #[test]
    fn span_for_compound() {
        let sexp = parse_sexp("  (a b)  ").unwrap();
        assert_eq!(sexp.span(), (2, 7));

        let sexp = parse_sexp("  [1 2]  ").unwrap();
        assert_eq!(sexp.span(), (2, 7));
    }

    #[test]
    fn span_helper_method() {
        let sexp = parse_sexp("42").unwrap();
        assert_eq!(sexp.span(), (0, 2));

        let sexp = parse_sexp("3.14").unwrap();
        assert_eq!(sexp.span(), (0, 4));

        let sexp = parse_sexp("true").unwrap();
        assert_eq!(sexp.span(), (0, 4));

        let sexp = parse_sexp(r#""hi""#).unwrap();
        assert_eq!(sexp.span(), (0, 4));
    }

    // ── Error tests ─────────────────────────────────────────────────────

    #[test]
    fn error_unclosed_paren() {
        let result = parse_sexp("(a b");
        assert!(result.is_err());
    }

    #[test]
    fn error_unclosed_bracket() {
        let result = parse_sexp("[a b");
        assert!(result.is_err());
    }

    #[test]
    fn error_unclosed_string() {
        let result = parse_sexp(r#""unclosed"#);
        assert!(result.is_err());
    }

    #[test]
    fn error_extra_close_paren() {
        // parse_sexp expects exactly one form — extra `)` leaves unparsed input
        let result = parse_sexp("(a))");
        assert!(result.is_err());
    }

    #[test]
    fn error_extra_close_bracket() {
        let result = parse_sexp("[a]]");
        assert!(result.is_err());
    }

    #[test]
    fn error_empty_input() {
        let result = parse_sexp("");
        assert!(result.is_err());
    }

    // ── Multi-form tests ────────────────────────────────────────────────

    #[test]
    fn parse_sexps_empty() {
        let sexps = parse_sexps("").unwrap();
        assert!(sexps.is_empty());
    }

    #[test]
    fn parse_sexps_single() {
        let sexps = parse_sexps("42").unwrap();
        assert_eq!(sexps.len(), 1);
        assert_eq!(sexps[0], Sexp::Int(42, (0, 2)));
    }

    #[test]
    fn parse_sexps_multiple() {
        let sexps = parse_sexps("(defn foo [x] x) (defn bar [y] y)").unwrap();
        assert_eq!(sexps.len(), 2);
        match &sexps[0] {
            Sexp::List(children, _) => {
                assert_eq!(children[0], Sexp::Symbol("defn".to_string(), (1, 5)));
                assert_eq!(children[1], Sexp::Symbol("foo".to_string(), (6, 9)));
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn parse_sexps_with_comments() {
        let src = r#"
            ; first definition
            (defn foo [x] x)
            ; second definition
            (defn bar [y] y)
        "#;
        let sexps = parse_sexps(src).unwrap();
        assert_eq!(sexps.len(), 2);
    }

    // ── Round-trip: parse example files through parse_sexps ────────────

    #[test]
    fn roundtrip_prelude() {
        let src = PRELUDE;
        let sexps = parse_sexps(src).unwrap();
        // Test prelude has many top-level forms
        assert!(
            sexps.len() > 10,
            "test prelude should have many forms, got {}",
            sexps.len()
        );
        // Each form should be a list (all forms are s-exprs)
        for (i, sexp) in sexps.iter().enumerate() {
            assert!(
                matches!(sexp, Sexp::List(..)),
                "prelude form {} should be a List, got {:?}",
                i,
                sexp
            );
        }
    }

    #[test]
    fn roundtrip_hello() {
        let src = include_str!("../examples/hello.cl");
        let sexps = parse_sexps(src).unwrap();
        assert!(!sexps.is_empty());
    }

    #[test]
    fn roundtrip_factorial() {
        let src = include_str!("../examples/factorial.cl");
        let sexps = parse_sexps(src).unwrap();
        assert!(!sexps.is_empty());
    }

    #[test]
    fn roundtrip_adt() {
        let src = include_str!("../examples/adt.cl");
        let sexps = parse_sexps(src).unwrap();
        assert!(!sexps.is_empty());
    }

    #[test]
    fn roundtrip_closure() {
        let src = include_str!("../examples/closure.cl");
        let sexps = parse_sexps(src).unwrap();
        assert!(!sexps.is_empty());
    }

    #[test]
    fn roundtrip_traits() {
        let src = include_str!("../examples/traits.cl");
        let sexps = parse_sexps(src).unwrap();
        assert!(!sexps.is_empty());
    }

    #[test]
    fn roundtrip_float() {
        let src = include_str!("../examples/float.cl");
        let sexps = parse_sexps(src).unwrap();
        assert!(!sexps.is_empty());
    }

    #[test]
    fn roundtrip_strings() {
        let src = include_str!("../examples/strings.cl");
        let sexps = parse_sexps(src).unwrap();
        assert!(!sexps.is_empty());
    }

    #[test]
    fn roundtrip_list() {
        let src = include_str!("../examples/list.cl");
        let sexps = parse_sexps(src).unwrap();
        assert!(!sexps.is_empty());
    }

    #[test]
    fn roundtrip_vec() {
        let src = include_str!("../examples/vec.cl");
        let sexps = parse_sexps(src).unwrap();
        assert!(!sexps.is_empty());
    }

    #[test]
    fn roundtrip_seq() {
        let src = include_str!("../examples/seq.cl");
        let sexps = parse_sexps(src).unwrap();
        assert!(!sexps.is_empty());
    }

    #[test]
    fn roundtrip_curry() {
        let src = include_str!("../examples/curry.cl");
        let sexps = parse_sexps(src).unwrap();
        assert!(!sexps.is_empty());
    }

    #[test]
    fn roundtrip_functor() {
        let src = include_str!("../examples/functor.cl");
        let sexps = parse_sexps(src).unwrap();
        assert!(!sexps.is_empty());
    }

    #[test]
    fn roundtrip_mapfold() {
        let src = include_str!("../examples/mapfold.cl");
        let sexps = parse_sexps(src).unwrap();
        assert!(!sexps.is_empty());
    }

    #[test]
    fn roundtrip_sum_input() {
        let src = include_str!("../examples/sum-input.cl");
        let sexps = parse_sexps(src).unwrap();
        assert!(!sexps.is_empty());
    }

    #[test]
    fn roundtrip_threading() {
        let src = include_str!("../examples/threading.cl");
        let sexps = parse_sexps(src).unwrap();
        assert!(!sexps.is_empty());
    }

    // ── Complex form tests ──────────────────────────────────────────────

    #[test]
    fn parse_defn_form() {
        let sexp = parse_sexp("(defn fact [n] (if (= n 0) 1 (* n (fact (- n 1)))))").unwrap();
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children[0], Sexp::Symbol("defn".to_string(), (1, 5)));
                assert_eq!(children[1], Sexp::Symbol("fact".to_string(), (6, 10)));
                assert!(matches!(&children[2], Sexp::Bracket(..)));
                assert!(matches!(&children[3], Sexp::List(..)));
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn parse_deftype_form() {
        let sexp = parse_sexp("(deftype (Option a) None (Some [:a val]))").unwrap();
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 4);
                assert_eq!(children[0], Sexp::Symbol("deftype".to_string(), (1, 8)));
                // (Option a) is a nested list
                match &children[1] {
                    Sexp::List(inner, _) => {
                        assert_eq!(inner.len(), 2);
                        assert_eq!(inner[0], Sexp::Symbol("Option".to_string(), (10, 16)));
                        assert_eq!(inner[1], Sexp::Symbol("a".to_string(), (17, 18)));
                    }
                    other => panic!("expected List, got {:?}", other),
                }
                assert_eq!(children[2], Sexp::Symbol("None".to_string(), (20, 24)));
                // (Some [:a val]) is a list
                match &children[3] {
                    Sexp::List(inner, _) => {
                        assert_eq!(inner.len(), 2);
                        assert_eq!(inner[0], Sexp::Symbol("Some".to_string(), (26, 30)));
                    }
                    other => panic!("expected List, got {:?}", other),
                }
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn parse_trait_form() {
        let sexp = parse_sexp("(deftrait Display (show [self] String))").unwrap();
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 3);
                assert_eq!(children[0], Sexp::Symbol("deftrait".to_string(), (1, 9)));
                assert_eq!(children[1], Sexp::Symbol("Display".to_string(), (10, 17)));
                // The method spec is (show [self] String)
                match &children[2] {
                    Sexp::List(inner, _) => {
                        assert_eq!(inner[0], Sexp::Symbol("show".to_string(), (19, 23)));
                    }
                    other => panic!("expected List, got {:?}", other),
                }
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn parse_deftrait_with_name_param() {
        // (deftrait Display ...) — `Display` is a plain symbol, not a list
        let sexp = parse_sexp("(deftrait Display (show [self] String))").unwrap();
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children[0], Sexp::Symbol("deftrait".to_string(), (1, 9)));
                assert_eq!(children[1], Sexp::Symbol("Display".to_string(), (10, 17)));
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn parse_string_with_docstring() {
        let sexp = parse_sexp(r#"(defn foo "adds one" [x] (+ x 1))"#).unwrap();
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 5);
                assert_eq!(children[0], Sexp::Symbol("defn".to_string(), (1, 5)));
                assert_eq!(children[1], Sexp::Symbol("foo".to_string(), (6, 9)));
                assert_eq!(children[2], Sexp::Str("adds one".to_string(), (10, 20)));
                assert!(matches!(&children[3], Sexp::Bracket(..)));
                assert!(matches!(&children[4], Sexp::List(..)));
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn parse_comment_at_end_of_input() {
        // Comment at EOF (no trailing newline)
        let sexps = parse_sexps("42 ; trailing comment").unwrap();
        assert_eq!(sexps.len(), 1);
        assert_eq!(sexps[0], Sexp::Int(42, (0, 2)));
    }

    // ── Dotted symbol tests ────────────────────────────────────────────

    #[test]
    fn parse_dotted_type_constructor() {
        let sexp = parse_sexp("Option.Some").unwrap();
        assert_eq!(sexp, Sexp::Symbol("Option.Some".to_string(), (0, 11)));
    }

    #[test]
    fn parse_dotted_nullary_constructor() {
        let sexp = parse_sexp("Option.None").unwrap();
        assert_eq!(sexp, Sexp::Symbol("Option.None".to_string(), (0, 11)));
    }

    #[test]
    fn parse_dotted_trait_method() {
        let sexp = parse_sexp("Display.show").unwrap();
        assert_eq!(sexp, Sexp::Symbol("Display.show".to_string(), (0, 12)));
    }

    #[test]
    fn parse_dotted_operator() {
        let sexp = parse_sexp("Num.+ ").unwrap();
        assert_eq!(sexp, Sexp::Symbol("Num.+".to_string(), (0, 5)));
    }

    #[test]
    fn parse_dotted_operator_star() {
        let sexp = parse_sexp("Num.* ").unwrap();
        assert_eq!(sexp, Sexp::Symbol("Num.*".to_string(), (0, 5)));
    }

    #[test]
    fn parse_dotted_list_constructor() {
        let sexp = parse_sexp("List.Cons").unwrap();
        assert_eq!(sexp, Sexp::Symbol("List.Cons".to_string(), (0, 9)));
    }

    #[test]
    fn parse_dotted_does_not_break_float() {
        // 3.14 should still parse as Float, not dotted symbol
        let sexp = parse_sexp("3.14").unwrap();
        match sexp {
            Sexp::Float(v, (0, 4)) => assert!((v - 3.14).abs() < 1e-10),
            other => panic!("expected Float, got {:?}", other),
        }
    }

    #[test]
    fn parse_dotted_does_not_break_negative_float() {
        let sexp = parse_sexp("-2.5").unwrap();
        match sexp {
            Sexp::Float(v, (0, 4)) => assert!((v - (-2.5)).abs() < 1e-10),
            other => panic!("expected Float, got {:?}", other),
        }
    }

    #[test]
    fn parse_bare_symbol_still_works() {
        let sexp = parse_sexp("foo").unwrap();
        assert_eq!(sexp, Sexp::Symbol("foo".to_string(), (0, 3)));
    }

    #[test]
    fn roundtrip_dot_notation() {
        let src = include_str!("../examples/dot_notation.cl");
        let sexps = parse_sexps(src).unwrap();
        assert!(!sexps.is_empty());
    }

    #[test]
    fn parse_dotted_in_list() {
        let sexp = parse_sexp("(Option.Some 42)").unwrap();
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 2);
                assert_eq!(
                    children[0],
                    Sexp::Symbol("Option.Some".to_string(), (1, 12))
                );
                assert_eq!(children[1], Sexp::Int(42, (13, 15)));
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    // ── Qualified symbol tests ───────────────────────────────────────

    #[test]
    fn parse_qualified_simple() {
        let sexp = parse_sexp("core.option/Some").unwrap();
        assert_eq!(sexp, Sexp::Symbol("core.option/Some".to_string(), (0, 16)));
    }

    #[test]
    fn parse_qualified_dotted_local() {
        let sexp = parse_sexp("core.option/Option.Some").unwrap();
        assert_eq!(
            sexp,
            Sexp::Symbol("core.option/Option.Some".to_string(), (0, 23))
        );
    }

    #[test]
    fn parse_qualified_operator() {
        let sexp = parse_sexp("core.math/+ ").unwrap();
        assert_eq!(sexp, Sexp::Symbol("core.math/+".to_string(), (0, 11)));
    }

    #[test]
    fn parse_qualified_single_segment_module() {
        let sexp = parse_sexp("math/add").unwrap();
        assert_eq!(sexp, Sexp::Symbol("math/add".to_string(), (0, 8)));
    }

    #[test]
    fn parse_qualified_deep_module() {
        let sexp = parse_sexp("core.option.internal/helper").unwrap();
        assert_eq!(
            sexp,
            Sexp::Symbol("core.option.internal/helper".to_string(), (0, 27))
        );
    }

    #[test]
    fn parse_qualified_does_not_break_division() {
        let sexp = parse_sexp("(/ 10 2)").unwrap();
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 3);
                assert_eq!(children[0], Sexp::Symbol("/".to_string(), (1, 2)));
                assert_eq!(children[1], Sexp::Int(10, (3, 5)));
                assert_eq!(children[2], Sexp::Int(2, (6, 7)));
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn parse_qualified_does_not_break_dotted() {
        let sexp = parse_sexp("Option.Some").unwrap();
        assert_eq!(sexp, Sexp::Symbol("Option.Some".to_string(), (0, 11)));
    }

    #[test]
    fn parse_qualified_in_call() {
        let sexp = parse_sexp("(core.option/Option.Some 42)").unwrap();
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 2);
                assert_eq!(
                    children[0],
                    Sexp::Symbol("core.option/Option.Some".to_string(), (1, 24))
                );
                assert_eq!(children[1], Sexp::Int(42, (25, 27)));
            }
            other => panic!("expected List, got {:?}", other),
        }
    }

    #[test]
    fn parse_qualified_operator_in_call() {
        let sexp = parse_sexp("(core.math/+ 1 2)").unwrap();
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 3);
                assert_eq!(
                    children[0],
                    Sexp::Symbol("core.math/+".to_string(), (1, 12))
                );
                assert_eq!(children[1], Sexp::Int(1, (13, 14)));
                assert_eq!(children[2], Sexp::Int(2, (15, 16)));
            }
            other => panic!("expected List, got {:?}", other),
        }
    }
}
