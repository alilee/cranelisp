//! S-expression reader: source text → `Vec<Sexp>`.
//!
//! Hand-written recursive descent parser. Token precedence follows spec 1.7:
//! float before integer (to capture decimal point), integer before operator
//! (so `-3` parses as integer), boolean before symbol (`true` is not a symbol).
//!
//! Commas are whitespace (Clojure convention). Comments run from `;` to EOL.

use cranelisp_types::{CranelispError, ErrorLocation, Sexp, Span};

// ---------------------------------------------------------------------------
// Parser state
// ---------------------------------------------------------------------------

/// Cursor into source text with byte-offset tracking.
struct Reader<'a> {
    src: &'a str,
    pos: usize,
    preserve_comments: bool,
    /// Comments consumed inside an annotation fold. The enclosing output
    /// sequence drains these immediately before the completed Annotated node.
    hoisted_comments: Vec<Sexp>,
}

impl<'a> Reader<'a> {
    fn new(src: &'a str) -> Self {
        Reader {
            src,
            pos: 0,
            preserve_comments: false,
            hoisted_comments: Vec::new(),
        }
    }

    fn new_preserving_comments(src: &'a str) -> Self {
        Reader {
            src,
            pos: 0,
            preserve_comments: true,
            hoisted_comments: Vec::new(),
        }
    }

    /// Remaining source text from current position.
    fn rest(&self) -> &'a str {
        &self.src[self.pos..]
    }

    /// Peek at the next byte without consuming.
    fn peek(&self) -> Option<u8> {
        self.src.as_bytes().get(self.pos).copied()
    }

    /// Peek at the byte `offset` positions ahead without consuming.
    fn peek_at(&self, offset: usize) -> Option<u8> {
        self.src.as_bytes().get(self.pos + offset).copied()
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
        sexps.append(&mut reader.hoisted_comments);
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

/// Skip an annotation-internal gap while retaining comments for the enclosing
/// sequence in comment-preserving mode. `Sexp::Annotated` has exactly two
/// syntax children, so comments cannot be stored as a third child; the settled
/// contract hoists them immediately before the completed node.
fn skip_annotation_gap(r: &mut Reader) {
    if r.preserve_comments {
        let mut comments = Vec::new();
        skip_ws_collect_comments(r, &mut comments);
        r.hoisted_comments.extend(comments);
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

/// Operator characters that may appear *interior* to an alphabetic symbol
/// (e.g. the `->` in `char->digit`, the `<=` in `lt-or-eq<=fallback`).
///
/// This is the subset of `is_operator_char` that is NOT already a
/// `is_symbol_char` and is NOT structurally significant to qualified/dotted
/// symbol parsing: `/` separates a module qualifier (`math/+`) and `.`
/// separates a dotted member (`Num.+`), so neither may be silently absorbed
/// into a symbol body. (`-`, `?`, `!` are already `is_symbol_char`.) An
/// interior run of these characters is absorbed into the symbol token only
/// when it is immediately followed by another symbol char — a *trailing*
/// run is left for the operator reader, preserving the standalone-operator
/// boundary (`->` alone, `a <= b`).
fn is_interior_operator_char(b: u8) -> bool {
    matches!(b, b'+' | b'*' | b'=' | b'<' | b'>')
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
        let form = read_form(r)?;
        children.append(&mut r.hoisted_comments);
        children.push(form);
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
        let form = read_form(r)?;
        children.append(&mut r.hoisted_comments);
        children.push(form);
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

    // The annotation half is read with the introducer stripped.  The compact
    // `:Int` spelling keeps the qualified-name lexer; `: (Fn ...)` and `: Int`
    // use the ordinary recursive form reader.  In both cases the subject is
    // read here too, making annotation folding universal (including macro
    // arguments) by construction rather than by positional AST-builder scans.
    let annotation = if r.peek().is_some_and(is_symbol_start) {
        let sym_start = r.pos;
        consume_symbol_chars(r);
        let first_part = r.src[sym_start..r.pos].to_string();
        let name = read_qualified_tail(r, &first_part)?;
        Sexp::Symbol(name, Span::new(sym_start as u32, r.pos as u32))
    } else {
        skip_annotation_gap(r);
        match r.peek() {
            None | Some(b')' | b']') => {
                return Err(r.error_at("annotation missing type expression", start, start + 1));
            }
            _ => read_form(r)?,
        }
    };

    skip_annotation_gap(r);
    let subject = match r.peek() {
        None | Some(b')' | b']') => {
            return Err(r.error_at("annotation missing expression", start, start + 1));
        }
        _ => read_form(r)?,
    };
    let end = subject.span().end;
    Ok(Sexp::Annotated {
        annotation: Box::new(annotation),
        subject: Box::new(subject),
        span: Span::new(start, end),
    })
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
            let text = &r.src[if negative {
                digits_start - 1
            } else {
                digits_start
            }..r.pos];
            let value = text
                .parse::<f64>()
                .map_err(|_| r.error_at("invalid float literal", start, end))?;
            return Ok(Sexp::Float(value, Span::new(start, end)));
        }
    }

    // Integer
    let end = r.pos as u32;
    let text = &r.src[if negative {
        digits_start - 1
    } else {
        digits_start
    }..r.pos];
    let value = text
        .parse::<i64>()
        .map_err(|_| r.error_at("invalid integer literal", start, end))?;
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
    let text = &r.src[start as usize..r.pos];

    // `/bar` — a lone `/` immediately followed (no whitespace boundary) by a name
    // is a dangling qualifier with an EMPTY module half (spec §8.5.1; 0682/0686
    // ruling). Keyed on `"/"` EXACTLY (Principle 16 — only `/` is the qualifier
    // char; `->`, `*foo`, `<=` read as operator text ≠ `"/"`) and on
    // symbol-adjacency, so a bare `/` DIVISION operator (`(/ 6 2)`, `(map / xs)`,
    // `/` at a boundary/EOF) stays the division symbol (RA-N4 fence). This is the
    // ONE genuinely-new lexical reject; the qualified-name swallows elsewhere
    // un-swallow existing paths. The reject fires at tokenization — before any
    // downstream defn-tail — so `/bar` cannot degrade to an incidental
    // "extra forms" / "undefined variable: /" split (RA-N6).
    if text == "/" && r.peek().is_some_and(is_symbol_start) {
        return Err(r.error_at(
            "`/` here has no module name before it — a qualified name needs a \
             non-empty module (`mod/name`); a bare `/` division must be separated \
             (`(/ a b)`)",
            start,
            end,
        ));
    }

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
    // Could be a dotted module path (`core.io/pure`, `/`-terminated) or a bare
    // dotted symbol (`Option.Some`, `Num.+`, `main.shell.inner`). ONE shared
    // module-path consumer decides (audit R7); a run that does not terminate in
    // `/` is a dotted symbol.
    if r.peek() == Some(b'.') {
        if let Some(full) = consume_dotted_module_path(r, first_part)? {
            return Ok(Sexp::Symbol(full, Span::new(start, r.pos as u32)));
        }
        // No `/`-terminated module path — position rewound to the first `.`.
        return Ok(read_dotted_name(r, first_part, start));
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

/// Given an already-consumed first symbol segment, consume any qualified or
/// dotted-module-path continuation and return the full name string.
///
/// Handles, mirroring `read_symbol_or_keyword`:
///   - `first/local`            -> `"first/local"`
///   - `first.seg.../local`     -> `"first.seg.../local"` (dotted module path)
///   - `first` (no `/`)         -> `"first"` (unchanged; dots left untouched —
///     a colon annotation never names a dotted *symbol*, only a possibly-dotted
///     module path that ends in `/`)
///
/// Used by `read_colon_prefix` so a `:`-prefixed type annotation can carry a
/// qualified type name (`:primitives/Int`, `:core.option/Option`).
fn read_qualified_tail(r: &mut Reader, first_part: &str) -> Result<String, CranelispError> {
    // Simple qualified: `first/local`.
    if r.peek() == Some(b'/') {
        r.advance(1); // skip '/'
        // A dangling qualifier `:foo/` (empty local half) is a LOCATED error —
        // `read_local_name` raises "expected local name after '/'". Propagate it
        // (`?`) rather than swallowing to `:foo`: the annotation path reaches
        // parity with the value path (RA-N1, spec §1.4.5). The former swallow
        // silently degraded `:foo/` to a minted `:foo` type-var (0682 ruling).
        let local = read_local_name(r)?;
        return Ok(format!("{first_part}/{local}"));
    }

    // Dotted module path leading to `/`: `first.seg.../local`.
    if r.peek() == Some(b'.') {
        // ONE fallible dotted-module-path consumer (audit R7 — the second swallow
        // site vanishes). A dangling `:a.b/` (empty local) propagates as a located
        // error (RA-N2), a `/`-terminated path returns the full name, and a run
        // with no `/` rewinds (the helper leaves the dots for later tokens — a
        // colon annotation never names a dotted *symbol*).
        if let Some(full) = consume_dotted_module_path(r, first_part)? {
            return Ok(full);
        }
        return Ok(first_part.to_string());
    }

    Ok(first_part.to_string())
}

/// Consume a `.seg.seg…/local` DOTTED-MODULE-PATH continuation from an
/// already-read `first_part`. The caller must have checked `r.peek() == '.'`;
/// the immediate `first/local` form is the caller's own concern.
///
/// The ONE dotted-module-path lexer (audit R7 / S87 F5) — shared by
/// `read_qualified_tail` (annotation position) and `read_symbol_or_keyword`
/// (value position), so the second swallow site cannot re-grow. Returns:
///   - `Ok(Some(full))` — a `/`-terminated path `module/local` was consumed
///     (position past the local name);
///   - `Ok(None)`       — no `/` terminated the dotted run; position is REWOUND
///     to the first `.` (the caller keeps `first_part` / reads a dotted symbol);
///   - `Err(..)`        — a `/` terminated the run but no valid local name
///     followed (a dangling qualifier — located, via `read_local_name`).
fn consume_dotted_module_path(
    r: &mut Reader,
    first_part: &str,
) -> Result<Option<String>, CranelispError> {
    debug_assert_eq!(r.peek(), Some(b'.'));
    let saved_pos = r.pos;
    let mut module = first_part.to_string();
    let mut found_slash = false;
    while r.peek() == Some(b'.') {
        let dot_pos = r.pos;
        r.advance(1); // skip '.'
        match r.peek() {
            Some(b) if is_symbol_start(b) => {
                let seg_start = r.pos;
                consume_symbol_chars(r);
                module.push('.');
                module.push_str(&r.src[seg_start..r.pos]);
                if r.peek() == Some(b'/') {
                    found_slash = true;
                    break;
                }
            }
            // `.` not followed by a symbol start (an operator member like
            // `Num.+`, or EOF): not a module path — back up and stop.
            _ => {
                r.pos = dot_pos;
                break;
            }
        }
    }

    if found_slash {
        r.advance(1); // skip '/'
        let local = read_local_name(r)?; // dangling qualifier -> located error
        return Ok(Some(format!("{module}/{local}")));
    }

    // No `/` terminated the dotted run — rewind so the caller sees the dots.
    r.pos = saved_pos;
    Ok(None)
}

/// Read a bare DOTTED-SYMBOL run (`Option.Some`, `main.shell.inner`, `Num.+`)
/// from an already-read `first_part`, positioned at the first `.`. Used by
/// `read_symbol_or_keyword` when the dotted run is NOT a `/`-terminated module
/// path (`consume_dotted_module_path` returned `None`). All-symbol segments join
/// verbatim; a `.`-operator member (`Num.+`) joins one member and terminates.
fn read_dotted_name(r: &mut Reader, first_part: &str, start: u32) -> Sexp {
    let mut name = first_part.to_string();
    while r.peek() == Some(b'.') {
        let dot_pos = r.pos;
        r.advance(1); // skip '.'
        match r.peek() {
            Some(b) if is_symbol_start(b) => {
                let seg_start = r.pos;
                consume_symbol_chars(r);
                name.push('.');
                name.push_str(&r.src[seg_start..r.pos]);
            }
            Some(b) if is_operator_char(b) => {
                let member_start = r.pos;
                consume_operator_chars(r);
                name.push('.');
                name.push_str(&r.src[member_start..r.pos]);
                break;
            }
            // `.` not followed by a valid member: back up, stop.
            _ => {
                r.pos = dot_pos;
                break;
            }
        }
    }
    Sexp::Symbol(name, Span::new(start, r.pos as u32))
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
    // Empty LOCAL half (`foo/`, `:foo/`, `a.b/`) — the dangling-qualifier twin of
    // the empty-MODULE-half `/bar` reject in `read_operator`. Brought to message
    // PARITY with that sibling (FIXME 0710): name the malformed shape and the
    // remedy, not just the missing token. Message text only — same `Err`, same
    // seam, same located span (spec §8.5.1 both-halves-non-empty).
    Err(r.error(
        "`/` here has no local name after it — a qualified name needs a non-empty \
         local (`mod/name`); drop the trailing `/` to write a bare name",
    ))
}

fn consume_symbol_chars(r: &mut Reader) {
    while let Some(b) = r.peek() {
        if is_symbol_char(b) {
            r.advance(1);
        } else if is_interior_operator_char(b) && interior_operator_run_then_symbol(r) {
            // An interior run of operator chars (e.g. the `->` in
            // `char->digit`) is part of THIS symbol token because more
            // symbol-char body follows it. Absorb the whole run.
            while r.peek().is_some_and(is_interior_operator_char) {
                r.advance(1);
            }
        } else {
            break;
        }
    }
}

/// At a position whose current byte is an interior-operator char, look ahead
/// across the maximal run of interior-operator chars and report whether that
/// run is immediately followed by a symbol char. When true, the operator run
/// is *interior* to the surrounding symbol (`char->digit`) and is absorbed;
/// when false the run is *trailing* (`a <= b`, `->` standalone) and is left
/// for the operator reader. Does not advance the cursor.
fn interior_operator_run_then_symbol(r: &Reader) -> bool {
    let mut offset = 0;
    while r.peek_at(offset).is_some_and(is_interior_operator_char) {
        offset += 1;
    }
    r.peek_at(offset).is_some_and(is_symbol_char)
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
mod tests;
