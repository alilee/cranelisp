//! S-expression reader: source text → `Vec<Sexp>`.
//!
//! Hand-written recursive descent parser. Token precedence follows spec 1.7:
//! float before integer (to capture decimal point), integer before operator
//! (so `-3` parses as integer), boolean before symbol (`true` is not a symbol).
//!
//! Commas are whitespace (Clojure convention). Comments run from `;` to EOL.

use cranelisp_types::{ErrorLocation, CranelispError, Sexp, Span};

// ---------------------------------------------------------------------------
// Parser state
// ---------------------------------------------------------------------------

/// Cursor into source text with byte-offset tracking.
struct Reader<'a> {
    src: &'a str,
    pos: usize,
    preserve_comments: bool,
}

impl<'a> Reader<'a> {
    fn new(src: &'a str) -> Self {
        Reader { src, pos: 0, preserve_comments: false }
    }

    fn new_preserving_comments(src: &'a str) -> Self {
        Reader { src, pos: 0, preserve_comments: true }
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
            location: ErrorLocation::from_span(Span::new(pos, pos)),
        }
    }

    /// Create a ParseError spanning [start, end).
    fn error_at(&self, message: &str, start: u32, end: u32) -> CranelispError {
        CranelispError::ParseError {
            message: message.to_string(),
            location: ErrorLocation::from_span(Span::new(start, end)),
        }
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Parse source text into a sequence of S-expressions.
///
/// One of the four free-function entries of the frontend boundary (see
/// crate-root preamble §"Public surface — the form-by-form boundary").
/// Pure source-to-sexp lowering with no structural-decl harvesting —
/// the reusable building block. Orchestration consumers continue with
/// [`crate::extract_module_declarations`]; REPL slash commands,
/// comment-preserving variants, and test fixtures use the flat result
/// directly.
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

/// Parse source text, preserving comments as `Sexp::Comment` nodes.
///
/// Used by REPL slash commands like `/source` that need to round-trip
/// the user's source text including comments. Otherwise equivalent to
/// [`parse`].
#[must_use = "parsing produces a result that should be checked for errors"]
pub fn parse_preserving_comments(source: &str) -> Result<Vec<Sexp>, CranelispError> {
    let mut reader = Reader::new_preserving_comments(source);
    let mut sexps = Vec::new();
    skip_ws_collect_comments(&mut reader, &mut sexps);
    while !reader.at_end() {
        let sexp = read_form(&mut reader)?;
        sexps.push(sexp);
        skip_ws_collect_comments(&mut reader, &mut sexps);
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

/// Dispatch: when preserving comments, collect them; otherwise discard.
fn skip_ws_or_comments(r: &mut Reader, children: &mut Vec<Sexp>) {
    if r.preserve_comments {
        skip_ws_collect_comments(r, children);
    } else {
        skip_whitespace_and_comments(r);
    }
}

/// Skip whitespace only (no comments).
fn skip_whitespace(r: &mut Reader) {
    while let Some(b) = r.peek() {
        if is_whitespace(b) {
            r.advance(1);
        } else {
            break;
        }
    }
}

/// If positioned at `;`, read the comment text and return a `Sexp::Comment`.
/// Strips the `;` and one leading space if present.
fn try_read_comment(r: &mut Reader) -> Option<Sexp> {
    if r.peek() != Some(b';') {
        return None;
    }
    let start = r.pos as u32;
    r.advance(1); // skip ';'

    // Strip one leading space if present
    if r.peek() == Some(b' ') {
        r.advance(1);
    }

    let text_start = r.pos;
    // Advance until newline or EOF
    while let Some(b) = r.peek() {
        if b == b'\n' {
            break;
        }
        r.advance(1);
    }
    let text_end = r.pos;
    let end = r.pos as u32;

    // Advance past newline if present
    if r.peek() == Some(b'\n') {
        r.advance(1);
    }

    let text = r.src[text_start..text_end].to_string();
    Some(Sexp::Comment(text, Span::new(start, end)))
}

/// Skip whitespace and collect any comments as `Sexp::Comment` nodes.
/// Used by the comment-preserving parse path.
fn skip_ws_collect_comments(r: &mut Reader, comments: &mut Vec<Sexp>) {
    loop {
        skip_whitespace(r);
        if let Some(comment) = try_read_comment(r) {
            comments.push(comment);
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
    skip_ws_or_comments(r, &mut children);
    while r.peek() != Some(b')') {
        if r.at_end() {
            return Err(r.error_at("unclosed '('", start, r.pos as u32));
        }
        children.push(read_form(r)?);
        skip_ws_or_comments(r, &mut children);
    }
    r.advance(1); // skip ')'
    let end = r.pos as u32;
    Ok(Sexp::List(children, Span::new(start, end)))
}

fn read_bracket(r: &mut Reader) -> Result<Sexp, CranelispError> {
    let start = r.pos as u32;
    r.advance(1); // skip '['
    let mut children = Vec::new();
    skip_ws_or_comments(r, &mut children);
    while r.peek() != Some(b']') {
        if r.at_end() {
            return Err(r.error_at("unclosed '['", start, r.pos as u32));
        }
        children.push(read_form(r)?);
        skip_ws_or_comments(r, &mut children);
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

        // No '/' found — if we collected multiple dot-separated segments,
        // return the whole dotted path as a symbol (e.g. `main.shell.inner`
        // in import forms). Otherwise fall back to single-dot symbol parsing.
        if module.contains('.') {
            let end = r.pos as u32;
            return Ok(Sexp::Symbol(module, Span::new(start, end)));
        }

        // Single segment after first_part — reset and try dotted symbol
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

/// `&name` or `& name` -> `Sexp::Symbol("&name")`
///
/// Whitespace between `&` and the name is allowed (Clojure convention).
fn read_ampersand(r: &mut Reader) -> Result<Sexp, CranelispError> {
    let start = r.pos as u32;
    r.advance(1); // skip '&'
    // Skip optional whitespace between '&' and the name.
    skip_whitespace_and_comments(r);
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

    // spec: 01-lexical §1.3.1 — integer literal (positive)
    #[test]
    fn test_parse_integer_literal() {
        assert_int(&parse_one("42"), 42);
    }

    // spec: 01-lexical §1.3.1 — negative integer literal
    #[test]
    fn test_parse_negative_integer() {
        assert_int(&parse_one("-7"), -7);
    }

    // spec: 01-lexical §1.3.1 — zero integer literal
    #[test]
    fn test_parse_zero() {
        assert_int(&parse_one("0"), 0);
    }

    // spec: 01-lexical §1.3.1 — explicit positive sign integer
    #[test]
    fn test_parse_positive_integer() {
        assert_int(&parse_one("+3"), 3);
    }

    // -- Float literals --

    // spec: 01-lexical §1.3.2 — float literal
    #[test]
    fn test_parse_float_literal() {
        assert_float(&parse_one("2.72"), 2.72);
    }

    // spec: 01-lexical §1.3.2 — negative float literal
    #[test]
    fn test_parse_negative_float() {
        assert_float(&parse_one("-0.5"), -0.5);
    }

    // spec: 01-lexical §1.3.2 — zero float literal
    #[test]
    fn test_parse_zero_float() {
        assert_float(&parse_one("0.0"), 0.0);
    }

    // -- Boolean literals --

    // spec: 01-lexical §1.3.3 — boolean literal true
    #[test]
    fn test_parse_true() {
        match parse_one("true") {
            Sexp::Bool(true, _) => {}
            other => panic!("expected Bool(true), got {other:?}"),
        }
    }

    // spec: 01-lexical §1.3.3 — boolean literal false
    #[test]
    fn test_parse_false() {
        match parse_one("false") {
            Sexp::Bool(false, _) => {}
            other => panic!("expected Bool(false), got {other:?}"),
        }
    }

    // spec: 01-lexical §1.3.3 — boolean must not be followed by symbol char
    #[test]
    fn test_true_prefix_is_symbol() {
        // `trueness` should parse as a symbol, not boolean + "ness"
        assert_symbol(&parse_one("trueness"), "trueness");
    }

    // spec: 01-lexical §1.3.3 — false prefix is a symbol, not boolean
    #[test]
    fn test_false_prefix_is_symbol() {
        assert_symbol(&parse_one("falsehood"), "falsehood");
    }

    // -- String literals --

    // spec: 01-lexical §1.3.4 — simple string literal
    #[test]
    fn test_parse_string() {
        match parse_one("\"hello\"") {
            Sexp::Str(s, _) => assert_eq!(s, "hello"),
            other => panic!("expected Str, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.3.4 — string escape sequences (newline)
    #[test]
    fn test_parse_string_escapes() {
        match parse_one("\"line1\\nline2\"") {
            Sexp::Str(s, _) => assert_eq!(s, "line1\nline2"),
            other => panic!("expected Str, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.3.4 — string escape sequences (escaped quote)
    #[test]
    fn test_parse_string_escaped_quote() {
        match parse_one("\"she said \\\"hi\\\"\"") {
            Sexp::Str(s, _) => assert_eq!(s, "she said \"hi\""),
            other => panic!("expected Str, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.3.4 — empty string literal
    #[test]
    fn test_parse_empty_string() {
        match parse_one("\"\"") {
            Sexp::Str(s, _) => assert_eq!(s, ""),
            other => panic!("expected Str, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.3.4 — unterminated string is an error
    #[test]
    fn test_unterminated_string() {
        assert!(parse("\"hello").is_err());
    }

    // -- Symbols --

    // spec: 01-lexical §1.4.1 — simple symbol
    #[test]
    fn test_parse_simple_symbol() {
        assert_symbol(&parse_one("foo"), "foo");
    }

    // spec: 01-lexical §1.4.1 — symbol with hyphens
    #[test]
    fn test_parse_symbol_with_hyphens() {
        assert_symbol(&parse_one("my-func"), "my-func");
    }

    // spec: 01-lexical §1.4.1 — symbol with question mark
    #[test]
    fn test_parse_symbol_with_question_mark() {
        assert_symbol(&parse_one("empty?"), "empty?");
    }

    // spec: 01-lexical §1.4.1 — symbol with exclamation mark
    #[test]
    fn test_parse_symbol_with_exclamation() {
        assert_symbol(&parse_one("do!"), "do!");
    }

    // spec: 01-lexical §1.4.1 — underscore-prefixed symbol
    #[test]
    fn test_parse_underscore_symbol() {
        assert_symbol(&parse_one("_private"), "_private");
    }

    // spec: 01-lexical §1.4.1 — uppercase symbol (type/constructor name)
    #[test]
    fn test_parse_uppercase_symbol() {
        assert_symbol(&parse_one("Point"), "Point");
    }

    // -- Operator symbols --

    // spec: 01-lexical §1.4.2 — operator symbol (+)
    #[test]
    fn test_parse_operator_plus() {
        assert_symbol(&parse_one("+"), "+");
    }

    // spec: 01-lexical §1.4.2 — operator symbol (-)
    #[test]
    fn test_parse_operator_minus() {
        assert_symbol(&parse_one("- "), "-");
    }

    // spec: 01-lexical §1.4.2 — multi-char operator symbol (<=)
    #[test]
    fn test_parse_operator_less_equal() {
        assert_symbol(&parse_one("<="), "<=");
    }

    // spec: 01-lexical §1.4.2 — arrow operator symbol (->)
    #[test]
    fn test_parse_operator_arrow() {
        assert_symbol(&parse_one("->"), "->");
    }

    // spec: 01-lexical §1.4.2 — thread-last operator symbol (->>)
    #[test]
    fn test_parse_operator_thread_last() {
        assert_symbol(&parse_one("->>"), "->>");
    }

    // spec: 01-lexical §1.4.2 — not-equal operator symbol (!=)
    #[test]
    fn test_parse_operator_not_equal() {
        assert_symbol(&parse_one("!="), "!=");
    }

    // spec: 01-lexical §1.4.2 — single-char operator symbol (!)
    #[test]
    fn test_parse_operator_bang_alone() {
        assert_symbol(&parse_one("!"), "!");
    }

    // -- Qualified symbols --

    // spec: 01-lexical §1.4.3 — qualified symbol (module/name)
    #[test]
    fn test_parse_qualified_symbol() {
        assert_symbol(&parse_one("math/sin"), "math/sin");
    }

    // spec: 01-lexical §1.4.3 — qualified symbol with dotted module path
    #[test]
    fn test_parse_qualified_dotted_module() {
        assert_symbol(&parse_one("core.io/pure"), "core.io/pure");
    }

    // spec: 01-lexical §1.4.3 — qualified operator symbol (module/+)
    #[test]
    fn test_parse_qualified_operator() {
        assert_symbol(&parse_one("math/+"), "math/+");
    }

    // -- Dotted symbols --

    // spec: 01-lexical §1.4.4 — dotted symbol (Type.member)
    #[test]
    fn test_parse_dotted_symbol() {
        assert_symbol(&parse_one("Option.Some"), "Option.Some");
    }

    // spec: 01-lexical §1.4.4 — dotted operator symbol (Trait.+)
    #[test]
    fn test_parse_dotted_operator() {
        assert_symbol(&parse_one("Num.+"), "Num.+");
    }

    // -- Colon-prefixed symbols --

    // spec: 01-lexical §1.4.5 — colon-prefixed type annotation
    #[test]
    fn test_parse_colon_prefix() {
        assert_symbol(&parse_one(":Int"), ":Int");
    }

    // spec: 01-lexical §1.4.5 — colon-prefixed type variable
    #[test]
    fn test_parse_colon_type_var() {
        assert_symbol(&parse_one(":a"), ":a");
    }

    // spec: 01-lexical §1.4.5 — bare colon (field separator)
    #[test]
    fn test_parse_bare_colon() {
        assert_symbol(&parse_one(": "), ":");
    }

    // -- Lists --

    // spec: 01-lexical §1.8 — parenthesized list form
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

    // spec: 01-lexical §1.8 — empty parenthesized list
    #[test]
    fn test_parse_empty_list() {
        match parse_one("()") {
            Sexp::List(children, _) => assert!(children.is_empty()),
            other => panic!("expected empty List, got {other:?}"),
        }
    }

    // spec: 01-lexical §1.8 — nested list forms
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

    // spec: 01-lexical §1.5 — bracket form
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

    // spec: 01-lexical §1.5 — bracket with colon-prefixed type annotations
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

    // spec: 01-lexical §1.2 — line comments
    #[test]
    fn test_parse_with_comment() {
        let sexps = parse("42 ; this is a comment\n43").unwrap();
        assert_eq!(sexps.len(), 2);
        assert_int(&sexps[0], 42);
        assert_int(&sexps[1], 43);
    }

    // spec: 01-lexical §1.2 — trailing comment at end of input
    #[test]
    fn test_parse_comment_at_end() {
        let sexps = parse("42 ; trailing comment").unwrap();
        assert_eq!(sexps.len(), 1);
        assert_int(&sexps[0], 42);
    }

    // -- Commas as whitespace --

    // spec: 01-lexical §1.2 — commas are whitespace
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

    // spec: 01-lexical §1.8 — program is sequence of forms
    #[test]
    fn test_parse_multiple_forms() {
        let sexps = parse("(defn f [x] x) (f 42)").unwrap();
        assert_eq!(sexps.len(), 2);
    }

    // -- Spans --

    // spec: 01-lexical §1.3.1 — integer literal span tracking
    #[test]
    fn test_span_integer() {
        let sexp = parse_one("42");
        assert_eq!(sexp.span(), Span::new(0, 2));
    }

    // spec: 01-lexical §1.8 — list form span tracking
    #[test]
    fn test_span_list() {
        let sexp = parse_one("(+ 1 2)");
        assert_eq!(sexp.span(), Span::new(0, 7));
    }

    // spec: 01-lexical §1.3.4 — string literal span tracking
    #[test]
    fn test_span_string() {
        let sexp = parse_one("\"hello\"");
        assert_eq!(sexp.span(), Span::new(0, 7));
    }

    // -- Error cases --

    // spec: 01-lexical §1.5 — unclosed parenthesis is an error
    #[test]
    fn test_unclosed_paren() {
        assert!(parse("(+ 1 2").is_err());
    }

    // spec: 01-lexical §1.5 — unclosed bracket is an error
    #[test]
    fn test_unclosed_bracket() {
        assert!(parse("[1 2").is_err());
    }

    // spec: 01-lexical §1.5 — unexpected close paren is an error
    #[test]
    fn test_unexpected_close_paren() {
        assert!(parse(")").is_err());
    }

    // -- Complex forms --

    // spec: 02-grammar §2.2.1 — defn form parsed as list
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

    // spec: 02-grammar §2.2.2 — deftype enum form parsed as list
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

    // spec: 01-lexical §1.4.5 — colon-prefixed symbol in list context
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

    // spec: 02-grammar §2.8.3 — compound type annotation with bare colon
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

    // spec: 01-lexical §1.8 — empty input produces no forms
    #[test]
    fn test_parse_empty_input() {
        let sexps = parse("").unwrap();
        assert!(sexps.is_empty());
    }

    // spec: 01-lexical §1.2 — whitespace-only input produces no forms
    #[test]
    fn test_parse_whitespace_only() {
        let sexps = parse("   \n\t  ").unwrap();
        assert!(sexps.is_empty());
    }

    // spec: 01-lexical §1.2 — comment-only input produces no forms
    #[test]
    fn test_parse_comment_only() {
        let sexps = parse("; just a comment").unwrap();
        assert!(sexps.is_empty());
    }

    // -- Minus as operator vs negative number --

    // spec: 01-lexical §1.7 — minus in list head is operator, not negative
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

    // spec: 01-lexical §1.7 — standalone -3 parses as negative integer
    #[test]
    fn test_negative_three_standalone() {
        assert_int(&parse_one("-3"), -3);
    }

    // -- Reader macros: quote, quasiquote, unquote --

    // spec: 01-lexical §1.6 — quote reader macro ('form -> (quote form))
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

    // spec: 01-lexical §1.6 — quote reader macro on list form
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

    // spec: 01-lexical §1.6 — quasiquote reader macro (`form -> (quasiquote form))
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

    // spec: 01-lexical §1.6 — quasiquote reader macro on list form
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

    // spec: 01-lexical §1.6 — unquote reader macro (~form -> (unquote form))
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

    // spec: 01-lexical §1.6 — unquote-splicing reader macro (~@form)
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

    // spec: 01-lexical §1.6 — anonymous function reader macro #(...)
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

    // spec: 01-lexical §1.6 — # without ( is an error
    #[test]
    fn test_parse_hash_without_paren_fails() {
        assert!(parse("#foo").is_err());
    }

    // -- Percent params --

    // spec: 01-lexical §1.4.7 — bare % is shorthand for %1
    #[test]
    fn test_parse_percent_param_bare() {
        // Bare `%` is shorthand for `%1`
        assert_symbol(&parse_one("% "), "%1");
    }

    // spec: 01-lexical §1.4.7 — explicit %1 percent parameter
    #[test]
    fn test_parse_percent_param_1() {
        assert_symbol(&parse_one("%1"), "%1");
    }

    // spec: 01-lexical §1.4.7 — %2 percent parameter
    #[test]
    fn test_parse_percent_param_2() {
        assert_symbol(&parse_one("%2"), "%2");
    }

    // -- Gensym --

    // spec: 01-lexical §1.4.6 — gensym dollar-prefixed symbol
    #[test]
    fn test_parse_gensym_dollar() {
        assert_symbol(&parse_one("$foo"), "$foo");
    }

    // spec: 01-lexical §1.4.6 — bare $ without name is an error
    #[test]
    fn test_parse_gensym_dollar_needs_name() {
        assert!(parse("$ ").is_err());
    }

    // -- Ampersand --

    // spec: 01-lexical §1.4.8 — ampersand with rest parameter name (no space)
    #[test]
    fn test_parse_ampersand() {
        assert_symbol(&parse_one("&rest"), "&rest");
    }

    // spec: 01-lexical §1.4.8 — ampersand with rest parameter name (with space)
    #[test]
    fn test_parse_ampersand_with_space() {
        assert_symbol(&parse_one("& rest"), "&rest");
    }

    // spec: 01-lexical §1.4.8 — & rest in bracket context produces &rest symbol
    #[test]
    fn test_parse_ampersand_in_bracket() {
        let sexp = parse_one("[x & rest]");
        if let Sexp::Bracket(items, _) = &sexp {
            assert_eq!(items.len(), 2);
            assert_symbol(&items[0], "x");
            assert_symbol(&items[1], "&rest");
        } else {
            panic!("expected bracket, got: {sexp:?}");
        }
    }

    // spec: 01-lexical §1.4.8 — bare & without name is an error
    #[test]
    fn test_parse_ampersand_needs_name() {
        assert!(parse("& ").is_err());
    }

    // -- Gensym shorthand (name#) --

    // spec: 01-lexical §1.4.6 — gensym shorthand (name#)
    #[test]
    fn test_parse_gensym_shorthand() {
        assert_symbol(&parse_one("foo#"), "foo#");
    }

    // spec: 01-lexical §1.4.6 — gensym shorthand in list context
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
