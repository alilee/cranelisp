//! S-expression reader: source text -> Vec<Sexp>.
//!
//! Hand-written recursive descent parser. Token precedence follows spec 1.7:
//! float before integer (to capture decimal point), integer before operator
//! (so `-3` parses as integer), boolean before symbol (`true` is not a symbol).
//!
//! Commas are whitespace (Clojure convention). Comments run from `;` to EOL.

use cranelisp_types::{CranelispError, Sexp, Span};

// ---------------------------------------------------------------------------
// Parser state
// ---------------------------------------------------------------------------

/// Cursor into source text with byte-offset tracking.
struct Reader<'a> {
    src: &'a str,
    pos: usize,
}

impl<'a> Reader<'a> {
    fn new(src: &'a str) -> Self {
        Reader { src, pos: 0 }
    }

    /// Remaining source text from current position.
    fn rest(&self) -> &'a str {
        &self.src[self.pos..]
    }

    /// Peek at the next byte without consuming.
    fn peek(&self) -> Option<u8> {
        self.src.as_bytes().get(self.pos).copied()
    }

    /// Advance by `n` bytes.
    fn advance(&mut self, n: usize) {
        self.pos += n;
    }

    /// True when all input has been consumed.
    fn at_end(&self) -> bool {
        self.pos >= self.src.len()
    }

    /// Create a ParseError at the current position.
    fn error(&self, message: &str) -> CranelispError {
        let pos = self.pos as u32;
        CranelispError::ParseError {
            message: message.to_string(),
            span: Span::new(pos, pos),
        }
    }

    /// Create a ParseError spanning [start, end).
    fn error_at(&self, message: &str, start: u32, end: u32) -> CranelispError {
        CranelispError::ParseError {
            message: message.to_string(),
            span: Span::new(start, end),
        }
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Parse source text into a sequence of S-expressions.
#[must_use = "parsing produces a result that should be checked for errors"]
pub fn parse(source: &str) -> Result<Vec<Sexp>, CranelispError> {
    let mut reader = Reader::new(source);
    let mut sexps = Vec::new();
    skip_whitespace_and_comments(&mut reader);
    while !reader.at_end() {
        let sexp = read_form(&mut reader)?;
        sexps.push(sexp);
        skip_whitespace_and_comments(&mut reader);
    }
    Ok(sexps)
}

// ---------------------------------------------------------------------------
// Whitespace & comments
// ---------------------------------------------------------------------------

fn is_whitespace(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\n' | b'\r' | b',')
}

fn skip_whitespace_and_comments(r: &mut Reader) {
    loop {
        // Skip whitespace characters
        while let Some(b) = r.peek() {
            if is_whitespace(b) {
                r.advance(1);
            } else {
                break;
            }
        }
        // Skip line comment
        if r.peek() == Some(b';') {
            while let Some(b) = r.peek() {
                r.advance(1);
                if b == b'\n' {
                    break;
                }
            }
        } else {
            break;
        }
    }
}

// ---------------------------------------------------------------------------
// Character classification
// ---------------------------------------------------------------------------

fn is_symbol_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_'
}

fn is_symbol_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || matches!(b, b'_' | b'-' | b'?' | b'!')
}

fn is_operator_char(b: u8) -> bool {
    matches!(b, b'+' | b'-' | b'*' | b'/' | b'=' | b'<' | b'>' | b'!')
}

fn is_digit(b: u8) -> bool {
    b.is_ascii_digit()
}

// ---------------------------------------------------------------------------
// Form reader (entry point for one S-expression)
// ---------------------------------------------------------------------------

fn read_form(r: &mut Reader) -> Result<Sexp, CranelispError> {
    match r.peek() {
        None => Err(r.error("unexpected end of input")),
        Some(b'(') => read_list(r),
        Some(b'[') => read_bracket(r),
        Some(b'"') => read_string(r),
        Some(b':') => read_colon_prefix(r),
        Some(b'\'') => read_quote(r),
        Some(b'`') => read_quasiquote(r),
        Some(b'~') => read_unquote(r),
        Some(b'#') => read_hash_dispatch(r),
        Some(b'%') => read_percent_param(r),
        Some(b'$') => read_gensym(r),
        Some(b'&') => read_ampersand(r),
        Some(b) if is_digit(b) => read_number(r),
        Some(b'+') => read_plus_or_operator(r),
        Some(b'-') => read_minus_or_number(r),
        Some(b) if is_operator_char(b) => read_operator(r),
        Some(b) if is_symbol_start(b) => read_symbol_or_keyword(r),
        Some(b) => Err(r.error(&format!("unexpected character: '{}'", b as char))),
    }
}

// ---------------------------------------------------------------------------
// Delimited forms
// ---------------------------------------------------------------------------

fn read_list(r: &mut Reader) -> Result<Sexp, CranelispError> {
    let start = r.pos as u32;
    r.advance(1); // skip '('
    let mut children = Vec::new();
    skip_whitespace_and_comments(r);
    while r.peek() != Some(b')') {
        if r.at_end() {
            return Err(r.error_at("unclosed '('", start, r.pos as u32));
        }
        children.push(read_form(r)?);
        skip_whitespace_and_comments(r);
    }
    r.advance(1); // skip ')'
    let end = r.pos as u32;
    Ok(Sexp::List(children, Span::new(start, end)))
}

fn read_bracket(r: &mut Reader) -> Result<Sexp, CranelispError> {
    let start = r.pos as u32;
    r.advance(1); // skip '['
    let mut children = Vec::new();
    skip_whitespace_and_comments(r);
    while r.peek() != Some(b']') {
        if r.at_end() {
            return Err(r.error_at("unclosed '['", start, r.pos as u32));
        }
        children.push(read_form(r)?);
        skip_whitespace_and_comments(r);
    }
    r.advance(1); // skip ']'
    let end = r.pos as u32;
    Ok(Sexp::Bracket(children, Span::new(start, end)))
}

// ---------------------------------------------------------------------------
// String literals
// ---------------------------------------------------------------------------

fn read_string(r: &mut Reader) -> Result<Sexp, CranelispError> {
    let start = r.pos as u32;
    r.advance(1); // skip opening '"'
    let mut buf = String::new();
    loop {
        match r.peek() {
            None => return Err(r.error_at("unterminated string", start, r.pos as u32)),
            Some(b'"') => {
                r.advance(1);
                let end = r.pos as u32;
                return Ok(Sexp::Str(buf, Span::new(start, end)));
            }
            Some(b'\\') => {
                r.advance(1);
                match r.peek() {
                    Some(b'n') => {
                        buf.push('\n');
                        r.advance(1);
                    }
                    Some(b't') => {
                        buf.push('\t');
                        r.advance(1);
                    }
                    Some(b'\\') => {
                        buf.push('\\');
                        r.advance(1);
                    }
                    Some(b'"') => {
                        buf.push('"');
                        r.advance(1);
                    }
                    Some(b) => {
                        return Err(r.error_at(
                            &format!("unknown escape sequence: '\\{}'", b as char),
                            start,
                            r.pos as u32 + 1,
                        ));
                    }
                    None => {
                        return Err(r.error_at("unterminated string", start, r.pos as u32));
                    }
                }
            }
            Some(_) => {
                // Read one UTF-8 character
                let ch = read_utf8_char(r);
                buf.push(ch);
            }
        }
    }
}

/// Read one UTF-8 character from the reader, advancing the position.
fn read_utf8_char(r: &mut Reader) -> char {
    let rest = r.rest();
    let Some(ch) = rest.chars().next() else {
        unreachable!("invariant: caller checked non-empty via peek()")
    };
    r.advance(ch.len_utf8());
    ch
}

// ---------------------------------------------------------------------------
// Colon-prefixed symbols (type annotations)
// ---------------------------------------------------------------------------

fn read_colon_prefix(r: &mut Reader) -> Result<Sexp, CranelispError> {
    let start = r.pos as u32;
    r.advance(1); // skip ':'

    // Check if next char is a symbol start -> colon-prefixed symbol
    if let Some(b) = r.peek() {
        if is_symbol_start(b) {
            let sym_start = r.pos;
            consume_symbol_chars(r);
            let name = &r.src[sym_start..r.pos];
            let end = r.pos as u32;
            let full = format!(":{name}");
            return Ok(Sexp::Symbol(full, Span::new(start, end)));
        }
        if b == b'(' {
            // :(Fn [...] ret) or :(Option a) — compound type annotation
            // Return the bare colon as a symbol, let the AST builder handle it
            let end = r.pos as u32;
            return Ok(Sexp::Symbol(":".to_string(), Span::new(start, end)));
        }
    }

    // Bare colon
    let end = r.pos as u32;
    Ok(Sexp::Symbol(":".to_string(), Span::new(start, end)))
}

// ---------------------------------------------------------------------------
// Numbers: integer and float
// ---------------------------------------------------------------------------

/// Read a number starting with a digit. Tries float first, then integer.
fn read_number(r: &mut Reader) -> Result<Sexp, CranelispError> {
    read_number_from(r, false)
}

/// Read a number, optionally negated. Digits must be at current position.
fn read_number_from(r: &mut Reader, negative: bool) -> Result<Sexp, CranelispError> {
    let start = if negative {
        (r.pos - 1) as u32
    } else {
        r.pos as u32
    };

    let digits_start = r.pos;
    consume_digits(r);
    let digits_end = r.pos;

    // Check for float: digits followed by '.' and more digits
    if r.peek() == Some(b'.') && looks_like_float_continuation(r) {
        r.advance(1); // skip '.'
        let frac_start = r.pos;
        consume_digits(r);
        if r.pos == frac_start {
            // '.' with no fractional digits — not a valid float
            // Back up: treat as integer followed by '.'
            r.pos = digits_end;
        } else {
            let end = r.pos as u32;
            let text = &r.src[if negative { digits_start - 1 } else { digits_start }..r.pos];
            let value = text.parse::<f64>().map_err(|_| {
                r.error_at("invalid float literal", start, end)
            })?;
            return Ok(Sexp::Float(value, Span::new(start, end)));
        }
    }

    // Integer
    let end = r.pos as u32;
    let text = &r.src[if negative { digits_start - 1 } else { digits_start }..r.pos];
    let value = text.parse::<i64>().map_err(|_| {
        r.error_at("invalid integer literal", start, end)
    })?;
    Ok(Sexp::Int(value, Span::new(start, end)))
}

/// Check if position after digits looks like a float continuation: '.' followed by digit.
fn looks_like_float_continuation(r: &Reader) -> bool {
    let bytes = r.src.as_bytes();
    // Current position should be at '.', check next byte is a digit
    if r.pos + 1 < bytes.len() {
        is_digit(bytes[r.pos + 1])
    } else {
        false
    }
}

fn consume_digits(r: &mut Reader) {
    while let Some(b) = r.peek() {
        if is_digit(b) {
            r.advance(1);
        } else {
            break;
        }
    }
}

// ---------------------------------------------------------------------------
// Leading '+' disambiguation
// ---------------------------------------------------------------------------

/// `+` can start:
///   - A positive integer: `+3` -> Int(3)
///   - An operator symbol: `+`, `+=`, `++`
fn read_plus_or_operator(r: &mut Reader) -> Result<Sexp, CranelispError> {
    let start = r.pos as u32;
    r.advance(1); // skip '+'

    // Check for positive integer: '+' followed by digit
    if let Some(b) = r.peek()
        && is_digit(b)
    {
        return read_number_from(r, false);
    }

    // Operator: consume remaining operator chars
    consume_operator_chars(r);
    let end = r.pos as u32;
    let text = &r.src[start as usize..r.pos];
    Ok(Sexp::Symbol(text.to_string(), Span::new(start, end)))
}

// ---------------------------------------------------------------------------
// Leading '-' disambiguation
// ---------------------------------------------------------------------------

/// `-` can start:
///   - A negative number: `-3`, `-3.14`
///   - An operator symbol: `-`, `->`, `-->`, `->>`.
fn read_minus_or_number(r: &mut Reader) -> Result<Sexp, CranelispError> {
    let start = r.pos as u32;
    r.advance(1); // skip '-'

    // Check for negative number: '-' followed by digit
    if let Some(b) = r.peek()
        && is_digit(b)
    {
        return read_number_from(r, true);
    }

    // Operator: consume remaining operator chars
    consume_operator_chars(r);
    let end = r.pos as u32;
    let text = &r.src[start as usize..r.pos];
    Ok(Sexp::Symbol(text.to_string(), Span::new(start, end)))
}

// ---------------------------------------------------------------------------
// Operator symbols
// ---------------------------------------------------------------------------

fn read_operator(r: &mut Reader) -> Result<Sexp, CranelispError> {
    let start = r.pos as u32;
    consume_operator_chars(r);
    let end = r.pos as u32;

    // Operator must not be immediately followed by a digit (spec 1.4.2)
    if let Some(b) = r.peek()
        && is_digit(b)
    {
        return Err(r.error_at(
            "operator symbol must not be immediately followed by a digit",
            start,
            end,
        ));
    }

    let text = &r.src[start as usize..r.pos];
    Ok(Sexp::Symbol(text.to_string(), Span::new(start, end)))
}

fn consume_operator_chars(r: &mut Reader) {
    while let Some(b) = r.peek() {
        if is_operator_char(b) {
            r.advance(1);
        } else {
            break;
        }
    }
}

// ---------------------------------------------------------------------------
// Symbols and keywords (true, false, qualified, dotted)
// ---------------------------------------------------------------------------

/// Read a symbol starting with a letter or '_'. Handles:
///   - `true` / `false` -> Bool
///   - Qualified: `module/name`
///   - Dotted: `Type.method`
///   - Simple symbol
fn read_symbol_or_keyword(r: &mut Reader) -> Result<Sexp, CranelispError> {
    let start = r.pos as u32;
    let sym_start = r.pos;
    consume_symbol_chars_with_hash(r);
    let first_part = &r.src[sym_start..r.pos];

    // Check for booleans: must not be followed by a symbol char
    let at_boundary = r.peek().is_none_or(|b| !is_symbol_char(b));
    if at_boundary {
        if first_part == "true" {
            return Ok(Sexp::Bool(true, Span::new(start, r.pos as u32)));
        }
        if first_part == "false" {
            return Ok(Sexp::Bool(false, Span::new(start, r.pos as u32)));
        }
    }

    // Check for qualified symbol: `first/rest` or dotted module: `first.seg/rest`
    if r.peek() == Some(b'/') {
        return read_qualified_symbol(r, first_part, start);
    }

    // Check for dotted: `first.rest`
    // Could be dotted symbol (Option.Some) or dotted module path (core.io/pure)
    if r.peek() == Some(b'.') {
        // Peek ahead: is this a dotted module path leading to '/'?
        let saved_pos = r.pos;
        let mut module = first_part.to_string();
        let mut found_slash = false;
        while r.peek() == Some(b'.') {
            let dot_pos = r.pos;
            r.advance(1); // skip '.'
            if let Some(b) = r.peek() {
                if is_symbol_start(b) {
                    let seg_start = r.pos;
                    consume_symbol_chars(r);
                    let segment = &r.src[seg_start..r.pos];
                    module.push('.');
                    module.push_str(segment);
                    if r.peek() == Some(b'/') {
                        found_slash = true;
                        break;
                    }
                    // Continue looking for more dots or '/'
                    continue;
                }
                // Not a symbol start (could be operator char like Num.+)
                // Back up and let dotted symbol handler deal with it
                r.pos = dot_pos;
                break;
            }
            // '.' not followed by valid continuation: back up
            r.pos = dot_pos;
            break;
        }

        if found_slash {
            // module contains the full dotted module path, and we're at '/'
            r.advance(1); // skip '/'
            let local = read_local_name(r)?;
            let end = r.pos as u32;
            let full = format!("{module}/{local}");
            return Ok(Sexp::Symbol(full, Span::new(start, end)));
        }

        // Not a dotted module path — reset and try dotted symbol
        r.pos = saved_pos;
        return read_dotted_symbol(r, first_part, start);
    }

    let end = r.pos as u32;
    Ok(Sexp::Symbol(first_part.to_string(), Span::new(start, end)))
}

/// Read qualified symbol after we have consumed `module_part` and see '/'.
/// The caller has already checked that the next char is '/'.
fn read_qualified_symbol(
    r: &mut Reader,
    module_part: &str,
    start: u32,
) -> Result<Sexp, CranelispError> {
    r.advance(1); // skip '/'

    // Read local name: can be symbol or operator
    let local = read_local_name(r)?;

    let end = r.pos as u32;
    let full = format!("{module_part}/{local}");
    Ok(Sexp::Symbol(full, Span::new(start, end)))
}

/// Read the local name portion of a qualified symbol (after '/').
fn read_local_name(r: &mut Reader) -> Result<String, CranelispError> {
    if let Some(b) = r.peek() {
        if is_symbol_start(b) {
            let name_start = r.pos;
            consume_symbol_chars(r);
            let name = r.src[name_start..r.pos].to_string();
            // Check for dotted local: `module/Type.method`
            if r.peek() == Some(b'.') {
                let dot_pos = r.pos;
                r.advance(1);
                if let Some(b2) = r.peek()
                    && (is_symbol_char(b2) || is_operator_char(b2))
                {
                    let member_start = r.pos;
                    if is_operator_char(b2) {
                        consume_operator_chars(r);
                    } else {
                        consume_symbol_chars(r);
                    }
                    let member = &r.src[member_start..r.pos];
                    return Ok(format!("{name}.{member}"));
                }
                r.pos = dot_pos;
            }
            return Ok(name);
        }
        if is_operator_char(b) {
            let op_start = r.pos;
            consume_operator_chars(r);
            return Ok(r.src[op_start..r.pos].to_string());
        }
    }
    Err(r.error("expected local name after '/'"))
}

/// Read dotted symbol continuation after we've consumed the first part.
fn read_dotted_symbol(
    r: &mut Reader,
    first_part: &str,
    start: u32,
) -> Result<Sexp, CranelispError> {
    let dot_pos = r.pos;
    r.advance(1); // skip '.'

    // Member can be symbol chars or operator chars
    if let Some(b) = r.peek() {
        if is_symbol_char(b) || is_symbol_start(b) {
            let member_start = r.pos;
            consume_symbol_chars(r);
            let member = &r.src[member_start..r.pos];
            let end = r.pos as u32;
            let full = format!("{first_part}.{member}");
            return Ok(Sexp::Symbol(full, Span::new(start, end)));
        }
        if is_operator_char(b) {
            let member_start = r.pos;
            consume_operator_chars(r);
            let member = &r.src[member_start..r.pos];
            let end = r.pos as u32;
            let full = format!("{first_part}.{member}");
            return Ok(Sexp::Symbol(full, Span::new(start, end)));
        }
    }

    // '.' not followed by a valid member: back up, treat as plain symbol
    r.pos = dot_pos;
    let end = r.pos as u32;
    Ok(Sexp::Symbol(first_part.to_string(), Span::new(start, end)))
}

fn consume_symbol_chars(r: &mut Reader) {
    while let Some(b) = r.peek() {
        if is_symbol_char(b) {
            r.advance(1);
        } else {
            break;
        }
    }
}

/// Consume symbol chars followed by an optional trailing `#` (gensym shorthand).
fn consume_symbol_chars_with_hash(r: &mut Reader) {
    consume_symbol_chars(r);
    // Trailing `#` for gensym shorthand: `name#`
    if r.peek() == Some(b'#') {
        r.advance(1);
    }
}

// ---------------------------------------------------------------------------
// Reader macros: quote, quasiquote, unquote, anonymous fn, etc.
// ---------------------------------------------------------------------------

/// `'expr` -> `(quote expr)`
fn read_quote(r: &mut Reader) -> Result<Sexp, CranelispError> {
    let start = r.pos as u32;
    r.advance(1); // skip '\''
    skip_whitespace_and_comments(r);
    let inner = read_form(r)?;
    let end = r.pos as u32;
    let span = Span::new(start, end);
    Ok(Sexp::List(
        vec![Sexp::Symbol("quote".to_string(), span), inner],
        span,
    ))
}

/// `` `expr `` -> `(quasiquote expr)`
fn read_quasiquote(r: &mut Reader) -> Result<Sexp, CranelispError> {
    let start = r.pos as u32;
    r.advance(1); // skip '`'
    skip_whitespace_and_comments(r);
    let inner = read_form(r)?;
    let end = r.pos as u32;
    let span = Span::new(start, end);
    Ok(Sexp::List(
        vec![Sexp::Symbol("quasiquote".to_string(), span), inner],
        span,
    ))
}

/// `~@expr` -> `(unquote-splicing expr)`, `~expr` -> `(unquote expr)`
fn read_unquote(r: &mut Reader) -> Result<Sexp, CranelispError> {
    let start = r.pos as u32;
    r.advance(1); // skip '~'
    let splicing = r.peek() == Some(b'@');
    if splicing {
        r.advance(1); // skip '@'
    }
    skip_whitespace_and_comments(r);
    let inner = read_form(r)?;
    let end = r.pos as u32;
    let span = Span::new(start, end);
    let name = if splicing {
        "unquote-splicing"
    } else {
        "unquote"
    };
    Ok(Sexp::List(
        vec![Sexp::Symbol(name.to_string(), span), inner],
        span,
    ))
}

/// `#(...)` -> `(anon-fn (...))`
fn read_hash_dispatch(r: &mut Reader) -> Result<Sexp, CranelispError> {
    let start = r.pos as u32;
    r.advance(1); // skip '#'
    match r.peek() {
        Some(b'(') => {
            let inner = read_list(r)?;
            let end = r.pos as u32;
            let span = Span::new(start, end);
            Ok(Sexp::List(
                vec![Sexp::Symbol("anon-fn".to_string(), span), inner],
                span,
            ))
        }
        _ => Err(r.error_at("expected '(' after '#'", start, r.pos as u32)),
    }
}

/// `%`, `%1`, `%2`, ... -> `Sexp::Symbol("%1")`, etc.
fn read_percent_param(r: &mut Reader) -> Result<Sexp, CranelispError> {
    let start = r.pos as u32;
    r.advance(1); // skip '%'
    if let Some(b) = r.peek()
        && is_digit(b)
    {
        let digit_start = r.pos;
        consume_digits(r);
        let digits = &r.src[digit_start..r.pos];
        let end = r.pos as u32;
        let name = format!("%{digits}");
        Ok(Sexp::Symbol(name, Span::new(start, end)))
    } else {
        // Bare `%` is shorthand for `%1`
        let end = r.pos as u32;
        Ok(Sexp::Symbol("%1".to_string(), Span::new(start, end)))
    }
}

/// `$name` -> `Sexp::Symbol("$name")`
fn read_gensym(r: &mut Reader) -> Result<Sexp, CranelispError> {
    let start = r.pos as u32;
    r.advance(1); // skip '$'
    if let Some(b) = r.peek()
        && is_symbol_start(b)
    {
        let name_start = r.pos;
        consume_symbol_chars(r);
        let name = &r.src[name_start..r.pos];
        let end = r.pos as u32;
        let full = format!("${name}");
        Ok(Sexp::Symbol(full, Span::new(start, end)))
    } else {
        Err(r.error_at("expected name after '$'", start, r.pos as u32))
    }
}

/// `&name` -> `Sexp::Symbol("&name")`
fn read_ampersand(r: &mut Reader) -> Result<Sexp, CranelispError> {
    let start = r.pos as u32;
    r.advance(1); // skip '&'
    if let Some(b) = r.peek()
        && is_symbol_start(b)
    {
        let name_start = r.pos;
        consume_symbol_chars(r);
        let name = &r.src[name_start..r.pos];
        let end = r.pos as u32;
        let full = format!("&{name}");
        Ok(Sexp::Symbol(full, Span::new(start, end)))
    } else {
        Err(r.error_at("expected name after '&'", start, r.pos as u32))
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_one(input: &str) -> Sexp {
        let sexps = parse(input).unwrap();
        assert_eq!(sexps.len(), 1, "expected exactly one sexp from: {input:?}");
        sexps.into_iter().next().unwrap()
    }

    fn assert_symbol(sexp: &Sexp, expected: &str) {
        match sexp {
            Sexp::Symbol(s, _) => assert_eq!(s, expected),
            other => panic!("expected Symbol({expected:?}), got {other:?}"),
        }
    }

    fn assert_int(sexp: &Sexp, expected: i64) {
        match sexp {
            Sexp::Int(v, _) => assert_eq!(*v, expected),
            other => panic!("expected Int({expected}), got {other:?}"),
        }
    }

    fn assert_float(sexp: &Sexp, expected: f64) {
        match sexp {
            Sexp::Float(v, _) => assert!((v - expected).abs() < 1e-10, "expected {expected}, got {v}"),
            other => panic!("expected Float({expected}), got {other:?}"),
        }
    }

    // -- Integer literals --

    #[test]
    fn test_parse_integer_literal() {
        assert_int(&parse_one("42"), 42);
    }

    #[test]
    fn test_parse_negative_integer() {
        assert_int(&parse_one("-7"), -7);
    }

    #[test]
    fn test_parse_zero() {
        assert_int(&parse_one("0"), 0);
    }

    #[test]
    fn test_parse_positive_integer() {
        assert_int(&parse_one("+3"), 3);
    }

    // -- Float literals --

    #[test]
    fn test_parse_float_literal() {
        assert_float(&parse_one("2.72"), 2.72);
    }

    #[test]
    fn test_parse_negative_float() {
        assert_float(&parse_one("-0.5"), -0.5);
    }

    #[test]
    fn test_parse_zero_float() {
        assert_float(&parse_one("0.0"), 0.0);
    }

    // -- Boolean literals --

    #[test]
    fn test_parse_true() {
        match parse_one("true") {
            Sexp::Bool(true, _) => {}
            other => panic!("expected Bool(true), got {other:?}"),
        }
    }

    #[test]
    fn test_parse_false() {
        match parse_one("false") {
            Sexp::Bool(false, _) => {}
            other => panic!("expected Bool(false), got {other:?}"),
        }
    }

    #[test]
    fn test_true_prefix_is_symbol() {
        // `trueness` should parse as a symbol, not boolean + "ness"
        assert_symbol(&parse_one("trueness"), "trueness");
    }

    #[test]
    fn test_false_prefix_is_symbol() {
        assert_symbol(&parse_one("falsehood"), "falsehood");
    }

    // -- String literals --

    #[test]
    fn test_parse_string() {
        match parse_one("\"hello\"") {
            Sexp::Str(s, _) => assert_eq!(s, "hello"),
            other => panic!("expected Str, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_string_escapes() {
        match parse_one("\"line1\\nline2\"") {
            Sexp::Str(s, _) => assert_eq!(s, "line1\nline2"),
            other => panic!("expected Str, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_string_escaped_quote() {
        match parse_one("\"she said \\\"hi\\\"\"") {
            Sexp::Str(s, _) => assert_eq!(s, "she said \"hi\""),
            other => panic!("expected Str, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_empty_string() {
        match parse_one("\"\"") {
            Sexp::Str(s, _) => assert_eq!(s, ""),
            other => panic!("expected Str, got {other:?}"),
        }
    }

    #[test]
    fn test_unterminated_string() {
        assert!(parse("\"hello").is_err());
    }

    // -- Symbols --

    #[test]
    fn test_parse_simple_symbol() {
        assert_symbol(&parse_one("foo"), "foo");
    }

    #[test]
    fn test_parse_symbol_with_hyphens() {
        assert_symbol(&parse_one("my-func"), "my-func");
    }

    #[test]
    fn test_parse_symbol_with_question_mark() {
        assert_symbol(&parse_one("empty?"), "empty?");
    }

    #[test]
    fn test_parse_symbol_with_exclamation() {
        assert_symbol(&parse_one("do!"), "do!");
    }

    #[test]
    fn test_parse_underscore_symbol() {
        assert_symbol(&parse_one("_private"), "_private");
    }

    #[test]
    fn test_parse_uppercase_symbol() {
        assert_symbol(&parse_one("Point"), "Point");
    }

    // -- Operator symbols --

    #[test]
    fn test_parse_operator_plus() {
        assert_symbol(&parse_one("+"), "+");
    }

    #[test]
    fn test_parse_operator_minus() {
        assert_symbol(&parse_one("- "), "-");
    }

    #[test]
    fn test_parse_operator_less_equal() {
        assert_symbol(&parse_one("<="), "<=");
    }

    #[test]
    fn test_parse_operator_arrow() {
        assert_symbol(&parse_one("->"), "->");
    }

    #[test]
    fn test_parse_operator_thread_last() {
        assert_symbol(&parse_one("->>"), "->>");
    }

    #[test]
    fn test_parse_operator_not_equal() {
        assert_symbol(&parse_one("!="), "!=");
    }

    #[test]
    fn test_parse_operator_bang_alone() {
        assert_symbol(&parse_one("!"), "!");
    }

    // -- Qualified symbols --

    #[test]
    fn test_parse_qualified_symbol() {
        assert_symbol(&parse_one("math/sin"), "math/sin");
    }

    #[test]
    fn test_parse_qualified_dotted_module() {
        assert_symbol(&parse_one("core.io/pure"), "core.io/pure");
    }

    #[test]
    fn test_parse_qualified_operator() {
        assert_symbol(&parse_one("math/+"), "math/+");
    }

    // -- Dotted symbols --

    #[test]
    fn test_parse_dotted_symbol() {
        assert_symbol(&parse_one("Option.Some"), "Option.Some");
    }

    #[test]
    fn test_parse_dotted_operator() {
        assert_symbol(&parse_one("Num.+"), "Num.+");
    }

    // -- Colon-prefixed symbols --

    #[test]
    fn test_parse_colon_prefix() {
        assert_symbol(&parse_one(":Int"), ":Int");
    }

    #[test]
    fn test_parse_colon_type_var() {
        assert_symbol(&parse_one(":a"), ":a");
    }

    #[test]
    fn test_parse_bare_colon() {
        assert_symbol(&parse_one(": "), ":");
    }

    // -- Lists --

    #[test]
    fn test_parse_list() {
        let sexp = parse_one("(+ 1 2)");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 3);
                assert_symbol(&children[0], "+");
                assert_int(&children[1], 1);
                assert_int(&children[2], 2);
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_empty_list() {
        match parse_one("()") {
            Sexp::List(children, _) => assert!(children.is_empty()),
            other => panic!("expected empty List, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_nested_list() {
        let sexp = parse_one("(+ (* 2 3) 4)");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 3);
                assert!(matches!(&children[1], Sexp::List(..)));
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    // -- Brackets --

    #[test]
    fn test_parse_bracket() {
        let sexp = parse_one("[a b c]");
        match sexp {
            Sexp::Bracket(children, _) => {
                assert_eq!(children.len(), 3);
                assert_symbol(&children[0], "a");
                assert_symbol(&children[1], "b");
                assert_symbol(&children[2], "c");
            }
            other => panic!("expected Bracket, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_bracket_with_types() {
        let sexp = parse_one("[:Int x :Int y]");
        match sexp {
            Sexp::Bracket(children, _) => {
                assert_eq!(children.len(), 4);
                assert_symbol(&children[0], ":Int");
                assert_symbol(&children[1], "x");
                assert_symbol(&children[2], ":Int");
                assert_symbol(&children[3], "y");
            }
            other => panic!("expected Bracket, got {other:?}"),
        }
    }

    // -- Comments --

    #[test]
    fn test_parse_with_comment() {
        let sexps = parse("42 ; this is a comment\n43").unwrap();
        assert_eq!(sexps.len(), 2);
        assert_int(&sexps[0], 42);
        assert_int(&sexps[1], 43);
    }

    #[test]
    fn test_parse_comment_at_end() {
        let sexps = parse("42 ; trailing comment").unwrap();
        assert_eq!(sexps.len(), 1);
        assert_int(&sexps[0], 42);
    }

    // -- Commas as whitespace --

    #[test]
    fn test_commas_are_whitespace() {
        let sexp = parse_one("[1, 2, 3]");
        match sexp {
            Sexp::Bracket(children, _) => {
                assert_eq!(children.len(), 3);
                assert_int(&children[0], 1);
                assert_int(&children[1], 2);
                assert_int(&children[2], 3);
            }
            other => panic!("expected Bracket, got {other:?}"),
        }
    }

    // -- Multiple forms --

    #[test]
    fn test_parse_multiple_forms() {
        let sexps = parse("(defn f [x] x) (f 42)").unwrap();
        assert_eq!(sexps.len(), 2);
    }

    // -- Spans --

    #[test]
    fn test_span_integer() {
        let sexp = parse_one("42");
        assert_eq!(sexp.span(), Span::new(0, 2));
    }

    #[test]
    fn test_span_list() {
        let sexp = parse_one("(+ 1 2)");
        assert_eq!(sexp.span(), Span::new(0, 7));
    }

    #[test]
    fn test_span_string() {
        let sexp = parse_one("\"hello\"");
        assert_eq!(sexp.span(), Span::new(0, 7));
    }

    // -- Error cases --

    #[test]
    fn test_unclosed_paren() {
        assert!(parse("(+ 1 2").is_err());
    }

    #[test]
    fn test_unclosed_bracket() {
        assert!(parse("[1 2").is_err());
    }

    #[test]
    fn test_unexpected_close_paren() {
        assert!(parse(")").is_err());
    }

    // -- Complex forms --

    #[test]
    fn test_parse_defn() {
        let sexp = parse_one("(defn add [a b] (+ a b))");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 4);
                assert_symbol(&children[0], "defn");
                assert_symbol(&children[1], "add");
                assert!(matches!(&children[2], Sexp::Bracket(..)));
                assert!(matches!(&children[3], Sexp::List(..)));
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_deftype_enum() {
        let sexp = parse_one("(deftype Color Red Green Blue)");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 5);
                assert_symbol(&children[0], "deftype");
                assert_symbol(&children[1], "Color");
                assert_symbol(&children[2], "Red");
                assert_symbol(&children[3], "Green");
                assert_symbol(&children[4], "Blue");
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_type_annotation() {
        let sexp = parse_one("(:Int)");
        // Wait, this is a list containing a colon-prefixed symbol — not valid as an expr
        // but the reader doesn't care.
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 1);
                assert_symbol(&children[0], ":Int");
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_compound_type_annotation() {
        // :(Fn [Int] Int) should produce : followed by (Fn [Int] Int)
        let sexps = parse(":(Fn [Int] Int) 42").unwrap();
        assert_eq!(sexps.len(), 3);
        assert_symbol(&sexps[0], ":");
        match &sexps[1] {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 3);
                assert_symbol(&children[0], "Fn");
            }
            other => panic!("expected List, got {other:?}"),
        }
        assert_int(&sexps[2], 42);
    }

    // -- Whitespace edge cases --

    #[test]
    fn test_parse_empty_input() {
        let sexps = parse("").unwrap();
        assert!(sexps.is_empty());
    }

    #[test]
    fn test_parse_whitespace_only() {
        let sexps = parse("   \n\t  ").unwrap();
        assert!(sexps.is_empty());
    }

    #[test]
    fn test_parse_comment_only() {
        let sexps = parse("; just a comment").unwrap();
        assert!(sexps.is_empty());
    }

    // -- Minus as operator vs negative number --

    #[test]
    fn test_minus_in_list_is_operator() {
        let sexp = parse_one("(- 3 1)");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 3);
                assert_symbol(&children[0], "-");
                assert_int(&children[1], 3);
                assert_int(&children[2], 1);
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    #[test]
    fn test_negative_three_standalone() {
        assert_int(&parse_one("-3"), -3);
    }

    // -- Reader macros: quote, quasiquote, unquote --

    #[test]
    fn test_parse_quote() {
        let sexp = parse_one("'foo");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 2);
                assert_symbol(&children[0], "quote");
                assert_symbol(&children[1], "foo");
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_quote_list() {
        let sexp = parse_one("'(1 2 3)");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 2);
                assert_symbol(&children[0], "quote");
                assert!(matches!(&children[1], Sexp::List(..)));
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_quasiquote() {
        let sexp = parse_one("`foo");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 2);
                assert_symbol(&children[0], "quasiquote");
                assert_symbol(&children[1], "foo");
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_quasiquote_list() {
        let sexp = parse_one("`(a b c)");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 2);
                assert_symbol(&children[0], "quasiquote");
                assert!(matches!(&children[1], Sexp::List(..)));
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_unquote() {
        let sexp = parse_one("~x");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 2);
                assert_symbol(&children[0], "unquote");
                assert_symbol(&children[1], "x");
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_unquote_splicing() {
        let sexp = parse_one("~@xs");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 2);
                assert_symbol(&children[0], "unquote-splicing");
                assert_symbol(&children[1], "xs");
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    // -- Anonymous function --

    #[test]
    fn test_parse_anon_fn() {
        let sexp = parse_one("#(+ %1 %2)");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 2);
                assert_symbol(&children[0], "anon-fn");
                match &children[1] {
                    Sexp::List(inner, _) => {
                        assert_eq!(inner.len(), 3);
                        assert_symbol(&inner[0], "+");
                        assert_symbol(&inner[1], "%1");
                        assert_symbol(&inner[2], "%2");
                    }
                    other => panic!("expected inner List, got {other:?}"),
                }
            }
            other => panic!("expected List, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_hash_without_paren_fails() {
        assert!(parse("#foo").is_err());
    }

    // -- Percent params --

    #[test]
    fn test_parse_percent_param_bare() {
        // Bare `%` is shorthand for `%1`
        assert_symbol(&parse_one("% "), "%1");
    }

    #[test]
    fn test_parse_percent_param_1() {
        assert_symbol(&parse_one("%1"), "%1");
    }

    #[test]
    fn test_parse_percent_param_2() {
        assert_symbol(&parse_one("%2"), "%2");
    }

    // -- Gensym --

    #[test]
    fn test_parse_gensym_dollar() {
        assert_symbol(&parse_one("$foo"), "$foo");
    }

    #[test]
    fn test_parse_gensym_dollar_needs_name() {
        assert!(parse("$ ").is_err());
    }

    // -- Ampersand --

    #[test]
    fn test_parse_ampersand() {
        assert_symbol(&parse_one("&rest"), "&rest");
    }

    #[test]
    fn test_parse_ampersand_needs_name() {
        assert!(parse("& ").is_err());
    }

    // -- Gensym shorthand (name#) --

    #[test]
    fn test_parse_gensym_shorthand() {
        assert_symbol(&parse_one("foo#"), "foo#");
    }

    #[test]
    fn test_parse_gensym_shorthand_in_list() {
        let sexp = parse_one("(let [x# 1] x#)");
        match sexp {
            Sexp::List(children, _) => {
                assert_eq!(children.len(), 3);
                assert_symbol(&children[0], "let");
                match &children[1] {
                    Sexp::Bracket(items, _) => {
                        assert_symbol(&items[0], "x#");
                        assert_int(&items[1], 1);
                    }
                    other => panic!("expected Bracket, got {other:?}"),
                }
                assert_symbol(&children[2], "x#");
            }
            other => panic!("expected List, got {other:?}"),
        }
    }
}
