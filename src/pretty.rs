// S-expression pretty-printer with syntax highlighting.
//
// Layer 2 of the terminal styling system (design/int/terminal-styling.md).
// Takes a Sexp tree and produces indented, syntax-highlighted text.
// All structured REPL output flows through this single formatter.

use cranelisp_types::Sexp;

use crate::style::{Style, styled};

/// Flat-length threshold: forms shorter than this are kept on one line.
const FLAT_THRESHOLD: usize = 40;

/// Special forms that use 2-space body indentation instead of argument alignment.
const SPECIAL_FORM_INDENT: &[&str] = &[
    "defn", "deftype", "deftrait", "impl", "let", "match",
    "fn", "if", "do", "defmacro",
];

/// Pretty-print and syntax-highlight a Sexp tree.
///
/// Returns a styled, indented string. When colour is disabled,
/// returns plain indented text (indentation always applies).
pub fn pretty_print(sexp: &Sexp) -> String {
    pp(sexp, 0, false)
}

/// Pretty-print a string by parsing it to Sexp first.
///
/// If parsing fails, returns the input string unstyled.
/// Handles comment suffixes (e.g., `; defn - description`) by splitting
/// them out before parsing and re-attaching with italic styling.
pub fn pretty_print_str(source: &str) -> String {
    // Split into lines and process each line group.
    // Many REPL display strings are multi-line with comment lines
    // (e.g., `:Type name ; class\n; match:\n;  Red Green Blue`).
    let mut result_lines: Vec<String> = Vec::new();

    for line in source.lines() {
        let trimmed = line.trim();
        // Pure comment lines (start with ;).
        if trimmed.starts_with(';') {
            result_lines.push(pp_comment_text(trimmed));
            continue;
        }

        // Lines with inline comments: split at first unquoted `;`.
        let (code_part, comment_part) = split_inline_comment(line);

        if code_part.trim().is_empty() {
            // Nothing to parse, just the comment.
            if let Some(comment) = comment_part {
                result_lines.push(pp_comment_text(comment));
            } else {
                result_lines.push(line.to_string());
            }
            continue;
        }

        // Parse the code portion. Verify that the round-trip produces
        // equivalent content; fall back to token-level styling if not
        // (e.g., qualified type names like `:primitives/Int` don't
        // round-trip through the S-expression reader).
        let mut line_result = match try_parse_and_format(code_part) {
            Some(formatted) => formatted,
            None => style_tokens(code_part),
        };

        // Re-attach comment suffix with italic styling.
        if let Some(comment) = comment_part {
            line_result.push(' ');
            line_result.push_str(&pp_comment_text(comment));
        }

        result_lines.push(line_result);
    }

    result_lines.join("\n")
}

/// Split a line into (code, optional_comment) at the first unquoted `;`.
fn split_inline_comment(line: &str) -> (&str, Option<&str>) {
    let mut in_string = false;
    let mut escape = false;
    for (i, ch) in line.char_indices() {
        if escape {
            escape = false;
            continue;
        }
        if ch == '\\' && in_string {
            escape = true;
            continue;
        }
        if ch == '"' {
            in_string = !in_string;
            continue;
        }
        if ch == ';' && !in_string {
            return (&line[..i], Some(line[i..].trim()));
        }
    }
    (line, None)
}

/// Try to parse code through the S-expression reader and pretty-print it.
///
/// Returns None if parsing fails or the round-trip changes the content
/// (e.g., qualified names with `/` in colon-prefixed symbols).
fn try_parse_and_format(code: &str) -> Option<String> {
    let sexps = cranelisp_frontend::parse(code).ok()?;
    if sexps.is_empty() {
        return None;
    }
    // Verify round-trip: if the flat representation differs from input,
    // the parser didn't preserve the content faithfully.
    let flat_parts: Vec<String> = sexps.iter().map(|s| s.format_flat()).collect();
    let round_tripped = flat_parts.join(" ");
    if round_tripped.trim() != code.trim() {
        return None;
    }
    let pp_parts: Vec<String> = sexps.iter().map(|s| pp(s, 0, false)).collect();
    Some(pp_parts.join(" "))
}

/// Apply token-level styling when full S-expression parsing doesn't round-trip.
///
/// Handles the common REPL display patterns:
/// - `:TypeName` or `:module/Type` -> cyan
/// - `:(Fn [...] ret)` compound types -> cyan
/// - Integer/float literals -> yellow
/// - `true`/`false` -> yellow
/// - `"string"` -> green
/// - Everything else -> default
fn style_tokens(code: &str) -> String {
    let mut result = String::new();
    let mut chars = code.char_indices().peekable();

    while let Some(&(i, ch)) = chars.peek() {
        if ch == ':' {
            // Type annotation: consume the colon and everything that follows
            // until whitespace (for simple types) or until matching paren
            // (for compound types).
            let type_span = consume_type_annotation(code, i);
            result.push_str(&styled(&code[i..i + type_span], Style::Cyan));
            // Advance past consumed chars.
            for _ in 0..type_span {
                chars.next();
            }
        } else if ch == '"' {
            // String literal.
            let str_span = consume_string_literal(code, i);
            result.push_str(&styled(&code[i..i + str_span], Style::Green));
            for _ in 0..str_span {
                chars.next();
            }
        } else if ch.is_ascii_digit() || (ch == '-' && matches!(code.as_bytes().get(i + 1), Some(b) if b.is_ascii_digit())) {
            // Number literal.
            let num_span = consume_number(code, i);
            result.push_str(&styled(&code[i..i + num_span], Style::Yellow));
            for _ in 0..num_span {
                chars.next();
            }
        } else if code[i..].starts_with("true") && !code.as_bytes().get(i + 4).is_some_and(|b| b.is_ascii_alphanumeric()) {
            result.push_str(&styled("true", Style::Yellow));
            for _ in 0..4 { chars.next(); }
        } else if code[i..].starts_with("false") && !code.as_bytes().get(i + 5).is_some_and(|b| b.is_ascii_alphanumeric()) {
            result.push_str(&styled("false", Style::Yellow));
            for _ in 0..5 { chars.next(); }
        } else if ch == '(' {
            // Opening paren — peek ahead to see if the next token is a
            // capitalized name (constructor/type in head position) and bold it.
            result.push('(');
            chars.next();
            // Skip whitespace after '('.
            while let Some(&(_, ws)) = chars.peek() {
                if ws == ' ' || ws == '\t' {
                    result.push(ws);
                    chars.next();
                } else {
                    break;
                }
            }
            // Check if next token starts with uppercase (ADT constructor).
            if let Some(&(head_start, head_ch)) = chars.peek()
                && head_ch.is_ascii_uppercase()
            {
                // Consume the head symbol and bold it.
                let head_span = consume_symbol(code, head_start);
                result.push_str(&styled(&code[head_start..head_start + head_span], Style::Bold));
                for _ in 0..head_span {
                    chars.next();
                }
            }
        } else {
            result.push(ch);
            chars.next();
        }
    }
    result
}

/// Consume a type annotation starting at position `start` (which is a `:`).
/// Returns the byte length of the annotation.
fn consume_type_annotation(code: &str, start: usize) -> usize {
    let bytes = code.as_bytes();
    let mut pos = start + 1; // skip ':'

    if pos >= bytes.len() {
        return 1;
    }

    // Check for compound type: `:(...)`.
    if bytes[pos] == b'(' {
        let mut depth = 1;
        pos += 1;
        while pos < bytes.len() && depth > 0 {
            match bytes[pos] {
                b'(' => depth += 1,
                b')' => depth -= 1,
                _ => {}
            }
            pos += 1;
        }
        return pos - start;
    }

    // Simple type: consume until whitespace or end.
    while pos < bytes.len() && !bytes[pos].is_ascii_whitespace() {
        pos += 1;
    }
    pos - start
}

/// Consume a string literal starting at position `start` (which is a `"`).
/// Returns the byte length including quotes.
fn consume_string_literal(code: &str, start: usize) -> usize {
    let bytes = code.as_bytes();
    let mut pos = start + 1; // skip opening quote
    while pos < bytes.len() {
        if bytes[pos] == b'\\' {
            pos += 2; // skip escape
        } else if bytes[pos] == b'"' {
            pos += 1; // include closing quote
            return pos - start;
        } else {
            pos += 1;
        }
    }
    pos - start // unclosed string: consume everything
}

/// Consume a number literal starting at position `start`.
/// Returns the byte length.
fn consume_number(code: &str, start: usize) -> usize {
    let bytes = code.as_bytes();
    let mut pos = start;
    if pos < bytes.len() && bytes[pos] == b'-' {
        pos += 1;
    }
    while pos < bytes.len() && (bytes[pos].is_ascii_digit() || bytes[pos] == b'.') {
        pos += 1;
    }
    pos - start
}

/// Consume a symbol token (alphanumeric, `.`, `/`, `-`, `_`, `?`, `!`).
/// Returns the byte length of the symbol.
fn consume_symbol(code: &str, start: usize) -> usize {
    let bytes = code.as_bytes();
    let mut pos = start;
    while pos < bytes.len() {
        let b = bytes[pos];
        if b.is_ascii_alphanumeric() || b == b'.' || b == b'/' || b == b'-' || b == b'_' || b == b'?' || b == b'!' {
            pos += 1;
        } else {
            break;
        }
    }
    pos - start
}

/// Style a comment string (including its `;` prefix) as italic.
fn pp_comment_text(text: &str) -> String {
    styled(text, Style::Italic)
}

/// Recursive pretty-printer core.
///
/// - `sexp`: the node to format
/// - `indent`: current indentation level (characters from left margin)
/// - `in_head`: whether this node is in head position of a parent list
fn pp(sexp: &Sexp, indent: usize, in_head: bool) -> String {
    match sexp {
        Sexp::Symbol(name, _) => pp_symbol(name, in_head),
        Sexp::Int(v, _) => style_atom(&v.to_string(), in_head, Style::Yellow),
        Sexp::Float(v, _) => {
            let s = format!("{v}");
            let s = if s.contains('.') { s } else { format!("{s}.0") };
            style_atom(&s, in_head, Style::Yellow)
        }
        Sexp::Bool(v, _) => {
            let s = if *v { "true" } else { "false" };
            style_atom(s, in_head, Style::Yellow)
        }
        Sexp::Str(s, _) => {
            let escaped = s
                .replace('\\', "\\\\")
                .replace('"', "\\\"")
                .replace('\n', "\\n")
                .replace('\t', "\\t");
            let text = format!("\"{escaped}\"");
            style_atom(&text, in_head, Style::Green)
        }
        Sexp::List(children, _) => pp_list(children, indent, in_head),
        Sexp::Bracket(children, _) => pp_bracket(children, indent),
        Sexp::Comment(text, _) => {
            if text.is_empty() {
                ";".to_string()
            } else {
                format!("; {text}")
            }
        }
    }
}

/// Style an atom node. If in head position, bold overrides the default style.
/// If the atom has a specific style (literal), that is used unless head overrides.
fn style_atom(text: &str, in_head: bool, default_style: Style) -> String {
    if in_head {
        styled(text, Style::Bold)
    } else {
        styled(text, default_style)
    }
}

/// Style a symbol node, applying head-position, type-annotation, or default rules.
fn pp_symbol(name: &str, in_head: bool) -> String {
    if in_head {
        styled(name, Style::Bold)
    } else if name.starts_with(':') {
        styled(name, Style::Cyan)
    } else {
        name.to_string()
    }
}

/// Pretty-print a parenthesized list.
fn pp_list(children: &[Sexp], indent: usize, in_head: bool) -> String {
    if children.is_empty() {
        return maybe_bold_brackets("(", ")", in_head, "");
    }

    // Check if this is a type annotation list: first child is :symbol.
    if is_type_annotation_list(children) {
        return pp_type_annotation_list(children, indent, in_head);
    }

    // Aligned `let`/`match` pair layout (repl/spec.md §3.11 P0–P5).
    // Sits before the FLAT_THRESHOLD check because P0 forces multi-line whenever
    // a recognised binding/arm vector has >=2 pairs, even if the whole form fits flat.
    if let Some(s) = try_pp_pair_form(children, indent, in_head) {
        return s;
    }

    // Compute flat representation to measure length.
    let flat = flat_list(children);
    // Take the flat path only when it fits AND no descendant is a forced
    // multi-line pair-form (repl/spec.md §3.11 P0). The flat path (`pp_list_flat`)
    // renders children at `indent = 0`, so a nested >=2-pair `let`/`match` would
    // align to column 0 instead of its true position deep in the parent line
    // (FIXME 0554). Skipping the flat path forces this enclosing form multi-line,
    // threading a correct `indent` down to the pair-form. The subtree scan is
    // bounded: it runs only when `flat.len() <= FLAT_THRESHOLD`, so the subtree
    // examined is itself <= FLAT_THRESHOLD chars of content — no O(n^2) blow-up.
    if flat.len() <= FLAT_THRESHOLD && !children.iter().any(subtree_contains_pair_form) {
        return pp_list_flat(children, in_head);
    }

    // Multi-line mode.
    pp_list_multiline(children, indent, in_head)
}

/// Does `sexp` contain — at any depth — a form that §3.11 P0 forces multi-line
/// (a `let` with a >=2-pair binding vector, or a `match` with a >=2-pair arm
/// vector)? Such a form MUST render multi-line even when it would fit flat, so
/// every ENCLOSING form must also avoid the pair-unaware flat path (which would
/// render the nested form at `indent = 0`, misaligned). Single-sources the
/// force-multiline decision with `try_pp_pair_form`. Short-circuits on the first
/// hit.
fn subtree_contains_pair_form(sexp: &Sexp) -> bool {
    match sexp {
        Sexp::List(children, _) => {
            is_forced_pair_form(children) || children.iter().any(subtree_contains_pair_form)
        }
        Sexp::Bracket(children, _) => children.iter().any(subtree_contains_pair_form),
        _ => false,
    }
}

/// True when `children` is a `let`/`match` form whose binding/arm vector holds
/// **>=2 pairs** — the P0 force-multiline trigger. Mirrors the recognition in
/// `try_pp_let`/`try_pp_match` (even-count vector via `as_pairs`, so an odd or
/// wrong-shaped vector is NOT forced — it falls back to flat, per P5).
fn is_forced_pair_form(children: &[Sexp]) -> bool {
    match children.first().and_then(head_symbol_name).as_deref() {
        Some("let") => matches!(
            children.get(1),
            Some(Sexp::Bracket(items, _)) if as_pairs(items).is_some_and(|p| p.len() >= 2)
        ),
        Some("match") => {
            children.len() == 3
                && matches!(
                    &children[2],
                    Sexp::Bracket(items, _) if as_pairs(items).is_some_and(|p| p.len() >= 2)
                )
        }
        _ => false,
    }
}

/// Aligned pair-layout dispatch for `let` / `match` (repl/spec.md §3.11).
///
/// Structural recognition on the `Sexp` tree (Phase-2 durability MUST — never
/// string post-processing). Returns `Some(text)` only when it takes over the
/// whole form: a recognised head (`let`/`match`) whose binding/arm vector holds
/// **>=2 pairs** (P0). Returns `None` — falling through to the existing
/// flat/threshold layout — for any non-recognised head, a missing/wrong-shaped
/// vector, fewer than 2 pairs (nothing to align), or an odd element count
/// (P5 graceful fallback).
fn try_pp_pair_form(children: &[Sexp], indent: usize, in_head: bool) -> Option<String> {
    match head_symbol_name(children.first()?)?.as_str() {
        "let" => try_pp_let(children, indent, in_head),
        "match" => try_pp_match(children, indent, in_head),
        _ => None,
    }
}

/// `(let [l0 r0 l1 r1 …] body…)` — the binding vector is the first `[...]` arg
/// (§3.11). The `[` sits at column `indent + len("(let ")` (= `indent + 5`), so
/// the left column starts at `indent + 6`. Body forms follow at the special-form
/// body indent (`indent + 2`), unchanged.
fn try_pp_let(children: &[Sexp], indent: usize, in_head: bool) -> Option<String> {
    let binding = match children.get(1) {
        Some(Sexp::Bracket(items, _)) => items,
        _ => return None,
    };
    let pairs = as_pairs(binding)?;
    if pairs.len() < 2 {
        return None; // P0 — 0/1 pair has nothing to align.
    }
    let (open, close) = pair_form_brackets(in_head);
    let head = styled("let", Style::Bold);
    // Prefix "(let " is 5 unstyled columns; the `[` lands at indent + 5, its
    // content (left column) at indent + 6.
    let left_col = indent + 6;
    let mut result = format!("{open}{head} ");
    result.push_str(&pair_vector_layout(&pairs, left_col));

    let body_indent = indent + 2;
    let pad = " ".repeat(body_indent);
    for body in &children[2..] {
        result.push('\n');
        result.push_str(&pad);
        result.push_str(&pp(body, body_indent, false));
    }
    result.push_str(&close);
    Some(result)
}

/// `(match <scrutinee> [l0 r0 l1 r1 …])` — the arm vector is the `[...]`
/// following the scrutinee (§3.11). The scrutinee stays flat on the head line;
/// the `[` sits at `indent + len("(match ") + flatwidth(scrutinee) + 1`, so the
/// left column starts one past that.
fn try_pp_match(children: &[Sexp], indent: usize, in_head: bool) -> Option<String> {
    // Exactly `(match scrut [arms])` — arm vector must be the final element.
    if children.len() != 3 {
        return None;
    }
    let scrutinee = &children[1];
    let arms = match &children[2] {
        Sexp::Bracket(items, _) => items,
        _ => return None,
    };
    let pairs = as_pairs(arms)?;
    if pairs.len() < 2 {
        return None; // P0 — 0/1 pair has nothing to align.
    }
    let (open, close) = pair_form_brackets(in_head);
    let head = styled("match", Style::Bold);
    let scrut_styled = pp(scrutinee, 0, false);
    // Prefix "(match " (7) + scrutinee (flat) + " " (1); the `[` lands after it,
    // and the left column starts one past the `[`.
    let left_col = indent + 7 + scrutinee.format_flat().len() + 1 + 1;
    let mut result = format!("{open}{head} {scrut_styled} ");
    result.push_str(&pair_vector_layout(&pairs, left_col));
    result.push_str(&close);
    Some(result)
}

/// The `(` / `)` for a pair-layout form, bolded when in head position.
fn pair_form_brackets(in_head: bool) -> (String, String) {
    if in_head {
        (styled("(", Style::Bold), styled(")", Style::Bold))
    } else {
        ("(".to_string(), ")".to_string())
    }
}

/// Split a bracket's children into consecutive `(left, right)` pairs.
/// `None` on an odd count (P5 graceful fallback — never crashes, never drops).
fn as_pairs(items: &[Sexp]) -> Option<Vec<(&Sexp, &Sexp)>> {
    if !items.len().is_multiple_of(2) {
        return None;
    }
    Some(items.chunks_exact(2).map(|c| (&c[0], &c[1])).collect())
}

/// Lay out a pair-structured vector as aligned two-column pairs (§3.11 P1–P4).
///
/// `left_col` is the absolute column of the left-term column (one past the `[`).
/// `W` = the max flat (unstyled) width over all left terms of this one vector;
/// the right column starts at `left_col + W + 1` (one min space after the widest
/// left term). Each right term is printed as if its opening column were the
/// right-column start (P4 — multi-line right terms indent under the right column
/// via `pp`'s ordinary recursive rules). The closing `]` attaches to the last
/// right term's final line.
fn pair_vector_layout(pairs: &[(&Sexp, &Sexp)], left_col: usize) -> String {
    let w = pairs
        .iter()
        .map(|(l, _)| l.format_flat().len())
        .max()
        .unwrap_or(0);
    let right_col = left_col + w + 1;

    let mut out = String::from("[");
    for (i, (left, right)) in pairs.iter().enumerate() {
        if i > 0 {
            out.push('\n');
            out.push_str(&" ".repeat(left_col)); // P1/P2 — one pair per line, left column.
        }
        out.push_str(&pp(left, 0, false)); // left term rendered flat (styled)
        let left_width = left.format_flat().len();
        out.push_str(&" ".repeat(right_col - left_col - left_width)); // P3 pad to right column
        out.push_str(&pp(right, right_col, false)); // P4 — right term opens at right_col
    }
    out.push(']');
    out
}

/// Check if a list is a type annotation list (first child is :symbol).
fn is_type_annotation_list(children: &[Sexp]) -> bool {
    matches!(children.first(), Some(Sexp::Symbol(name, _)) if name.starts_with(':'))
}

/// Render an entire type annotation list in cyan.
/// Per spec 10.3.4: the entire type annotation is styled as a single cyan span.
fn pp_type_annotation_list(children: &[Sexp], indent: usize, in_head: bool) -> String {
    // Compute the flat representation.
    let flat = flat_list(children);

    if flat.len() <= FLAT_THRESHOLD {
        // Single-line: wrap everything in cyan.
        let inner = flat_content_unstyled(children);
        let text = format!("({inner})");
        if in_head {
            styled(&text, Style::Bold)
        } else {
            styled(&text, Style::Cyan)
        }
    } else {
        // Multi-line type annotations — still all cyan.
        let inner = pp_type_multiline_unstyled(children, indent);
        if in_head {
            styled(&inner, Style::Bold)
        } else {
            styled(&inner, Style::Cyan)
        }
    }
}

/// Multi-line formatting for type annotation lists, producing unstyled text
/// that will be wrapped in a single cyan/bold span.
fn pp_type_multiline_unstyled(children: &[Sexp], indent: usize) -> String {
    let head_flat = children[0].format_flat();
    let body_indent = indent + 2;
    let pad = " ".repeat(body_indent);

    let mut result = format!("({head_flat}");
    for child in &children[1..] {
        let child_flat = child.format_flat();
        result.push('\n');
        result.push_str(&pad);
        result.push_str(&child_flat);
    }
    result.push(')');
    result
}

/// Flat content of a list without styling, for wrapping in a single style.
fn flat_content_unstyled(children: &[Sexp]) -> String {
    let parts: Vec<String> = children.iter().map(|c| c.format_flat()).collect();
    parts.join(" ")
}

/// Flat representation of a list for length measurement.
fn flat_list(children: &[Sexp]) -> String {
    let parts: Vec<String> = children.iter().map(|c| c.format_flat()).collect();
    format!("({})", parts.join(" "))
}

/// Render a short list on a single line with styling.
fn pp_list_flat(children: &[Sexp], in_head: bool) -> String {
    let mut parts = Vec::with_capacity(children.len());
    for (i, child) in children.iter().enumerate() {
        parts.push(pp(child, 0, i == 0));
    }
    let inner = parts.join(" ");
    maybe_bold_brackets("(", ")", in_head, &inner)
}

/// Render a long list across multiple lines.
fn pp_list_multiline(children: &[Sexp], indent: usize, in_head: bool) -> String {
    let head = &children[0];
    let head_str = pp(head, indent, true);
    let head_name = head_symbol_name(head);

    let is_special = head_name
        .as_ref()
        .map(|n| SPECIAL_FORM_INDENT.contains(&n.as_str()))
        .unwrap_or(false);

    let open = if in_head { styled("(", Style::Bold) } else { "(".to_string() };
    let close = if in_head { styled(")", Style::Bold) } else { ")".to_string() };

    if children.len() == 1 {
        return format!("{open}{head_str}{close}");
    }

    if is_special {
        // Special form: 2-space body indent.
        let body_indent = indent + 2;
        let pad = " ".repeat(body_indent);
        let mut result = format!("{open}{head_str}");

        // First argument on the same line as the head.
        let first_arg = pp(&children[1], body_indent, false);
        result.push(' ');
        result.push_str(&first_arg);

        // Remaining arguments on new lines.
        for child in &children[2..] {
            let child_str = pp(child, body_indent, false);
            result.push('\n');
            result.push_str(&pad);
            result.push_str(&child_str);
        }
        result.push_str(&close);
        result
    } else {
        // Standard alignment: subsequent args align with first argument.
        // head_flat_len is the unstyled length of the head for alignment.
        let head_flat_len = head.format_flat().len();
        let arg_indent = indent + 1 + head_flat_len + 1; // '(' + head + ' '
        let pad = " ".repeat(arg_indent);

        let mut result = format!("{open}{head_str}");

        // First argument on the same line.
        let first_arg = pp(&children[1], arg_indent, false);
        result.push(' ');
        result.push_str(&first_arg);

        // Remaining arguments aligned with first argument.
        for child in &children[2..] {
            let child_str = pp(child, arg_indent, false);
            result.push('\n');
            result.push_str(&pad);
            result.push_str(&child_str);
        }
        result.push_str(&close);
        result
    }
}

/// Extract the symbol name from a head node, if it is a plain symbol.
fn head_symbol_name(sexp: &Sexp) -> Option<String> {
    match sexp {
        Sexp::Symbol(name, _) => Some(name.clone()),
        _ => None,
    }
}

/// Pretty-print a bracket form.
fn pp_bracket(children: &[Sexp], indent: usize) -> String {
    if children.is_empty() {
        return "[]".to_string();
    }

    // Flat representation for length measurement.
    let parts: Vec<String> = children.iter().map(|c| c.format_flat()).collect();
    let flat = format!("[{}]", parts.join(" "));
    // As in `pp_list`: the single-line path renders children at `indent = 0`, so
    // avoid it when a descendant is a forced multi-line pair-form (FIXME 0554).
    if flat.len() <= FLAT_THRESHOLD && !children.iter().any(subtree_contains_pair_form) {
        // Single line: no head-position bolding in brackets.
        let styled_parts: Vec<String> = children.iter().map(|c| pp(c, 0, false)).collect();
        return format!("[{}]", styled_parts.join(" "));
    }

    // Multi-line bracket form.
    let child_indent = indent + 1;
    let pad = " ".repeat(child_indent);
    let first = pp(&children[0], child_indent, false);
    let mut result = format!("[{first}");

    let mut unstyled_line_len = children[0].format_flat().len() + 1; // '[' + first child
    for child in &children[1..] {
        let child_str = pp(child, child_indent, false);
        // Try to fit on the current line.
        // Use unstyled length to avoid ANSI escape sequences inflating the count.
        // A forced multi-line pair-form child (FIXME 0554) never shares a line —
        // it must open at `child_indent` where `pp` aligns it correctly.
        let child_flat_len = child.format_flat().len();
        if !subtree_contains_pair_form(child)
            && unstyled_line_len + 1 + child_flat_len <= FLAT_THRESHOLD
        {
            result.push(' ');
            unstyled_line_len += 1 + child_flat_len;
            result.push_str(&child_str);
        } else {
            result.push('\n');
            result.push_str(&pad);
            result.push_str(&child_str);
            unstyled_line_len = child_indent + child_flat_len;
        }
    }
    result.push(']');
    result
}

/// Wrap inner content with brackets, bolding them if in head position.
fn maybe_bold_brackets(open: &str, close: &str, in_head: bool, inner: &str) -> String {
    if in_head {
        format!("{}{}{}", styled(open, Style::Bold), inner, styled(close, Style::Bold))
    } else {
        format!("{}{}{}", open, inner, close)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // In test context, colour is disabled (stdout is not a TTY),
    // so we test indentation behavior without escape sequences.

    #[test]
    fn short_form_single_line() {
        let result = pretty_print_str("(+ 1 2)");
        assert_eq!(result, "(+ 1 2)");
    }

    #[test]
    fn type_annotation_symbol() {
        let result = pretty_print_str(":Int");
        assert_eq!(result, ":Int");
    }

    #[test]
    fn string_literal() {
        let result = pretty_print_str("\"hello\"");
        assert_eq!(result, "\"hello\"");
    }

    #[test]
    fn bracket_form() {
        let result = pretty_print_str("[1 2 3]");
        assert_eq!(result, "[1 2 3]");
    }

    #[test]
    fn nested_short_form() {
        let result = pretty_print_str("(defn f [x] (+ x 1))");
        assert_eq!(result, "(defn f [x] (+ x 1))");
    }

    #[test]
    fn special_form_multiline() {
        // Build a form long enough to trigger multi-line.
        let input = "(defn factorial [n] (if (= n 0) 1 (* n (factorial (- n 1)))))";
        let result = pretty_print_str(input);
        // Should be multi-line with 2-space body indent.
        assert!(result.contains('\n'), "Expected multi-line output for: {input}");
        // First line should start with (defn.
        assert!(result.starts_with("(defn"), "Expected to start with (defn: {result}");
    }

    #[test]
    fn comment_line() {
        let result = pretty_print_str("; hello world");
        assert_eq!(result, "; hello world");
    }

    #[test]
    fn inline_comment() {
        let result = pretty_print_str(":Int 42 ; defn");
        // Should contain the code and comment parts.
        assert!(result.contains("42"));
        assert!(result.contains("; defn"));
    }

    #[test]
    fn parse_failure_returns_original() {
        let input = "(unclosed";
        let result = pretty_print_str(input);
        assert_eq!(result, input);
    }

    #[test]
    fn empty_list() {
        let result = pretty_print_str("()");
        assert_eq!(result, "()");
    }

    #[test]
    fn empty_bracket() {
        let result = pretty_print_str("[]");
        assert_eq!(result, "[]");
    }

    #[test]
    fn compound_type_annotation() {
        let result = pretty_print_str(":(Fn [Int] Int)");
        assert_eq!(result, ":(Fn [Int] Int)");
    }

    #[test]
    fn result_display_format() {
        // Typical REPL result: `:Type value`
        let result = pretty_print_str(":primitives/Int 42");
        assert_eq!(result, ":primitives/Int 42");
    }

    #[test]
    fn definition_display_format() {
        // Typical REPL definition: `:Type name ; class`
        let result = pretty_print_str(":(Fn [primitives/Int] primitives/Int) user/double");
        assert!(result.contains("user/double"));
    }

    // --- §3.11 aligned let/match pair layout (P0–P5) ---------------------------
    //
    // These exercise the pair-aware printer directly on Sexp trees parsed from
    // source. Colour is off in the test process, so bytes are exact.

    /// Parse one form and pretty-print it (colour-off).
    fn pp_form(src: &str) -> String {
        let sexps = cranelisp_frontend::parse(src).unwrap();
        pretty_print(&sexps[0])
    }

    #[test]
    fn p0_two_pair_let_aligns_two_columns() {
        // spec: repl/spec.md §3.11 P0/P1/P2/P3 — a >=2-pair let renders one pair
        // per line with a shared right column at leftCol + W + 1.
        let out = pp_form("(let [a 1 bb 2] a)");
        let expected = concat!(
            "(let [a  1\n",
            "      bb 2]\n",
            "  a)",
        );
        assert_eq!(out, expected, "got:\n{out}");
    }

    #[test]
    fn p0_two_arm_match_aligns_and_forces_multiline() {
        // spec: repl/spec.md §3.11 P0 — a two-arm match that would fit flat MUST
        // render multi-line aligned; the arm patterns MUST NOT share a line.
        let out = pp_form("(match x [(A a) 1 (B b) 2])");
        let expected = concat!(
            "(match x [(A a) 1\n",
            "          (B b) 2])",
        );
        assert_eq!(out, expected, "got:\n{out}");
        assert!(
            !out.lines().any(|l| l.contains("(A a)") && l.contains("(B b)")),
            "arm patterns must not share a line:\n{out}"
        );
    }

    #[test]
    fn p3_right_column_uses_widest_left_term() {
        // spec: repl/spec.md §3.11 P3 — W = max flat width over ALL left terms of
        // the vector; the right column is leftCol + W + 1. `final-pos` (9) is the
        // widest of d/new-pos/final-pos, so every value aligns to that column.
        let out = pp_form("(let [d 1 new-pos 2 final-pos 3] d)");
        let expected = concat!(
            "(let [d         1\n",
            "      new-pos   2\n",
            "      final-pos 3]\n",
            "  d)",
        );
        assert_eq!(out, expected, "got:\n{out}");
        // Each value begins at the same column (leftCol 6 + W 9 + 1 = 16).
        for line in out.lines().take(3) {
            let col = line.find(['1', '2', '3']);
            if let Some(c) = col {
                assert_eq!(c, 16, "value must align to right column 16: {line:?}");
            }
        }
    }

    #[test]
    fn p0_single_pair_let_falls_back_to_flat() {
        // spec: repl/spec.md §3.11 P0 — a 1-pair let has nothing to align and
        // follows the pre-existing flat layout unchanged.
        let out = pp_form("(let [x 5] x)");
        assert_eq!(out, "(let [x 5] x)", "got:\n{out}");
    }

    #[test]
    fn p5_odd_count_let_binding_falls_back() {
        // spec: repl/spec.md §3.11 P5 — an odd element count (malformed) falls
        // back to the pre-existing bracket layout, never a crash or dropped item.
        // Build the Sexp directly (an odd binding vector won't survive real let
        // parsing, but the printer must still handle it gracefully).
        use cranelisp_types::Span;
        let sp = Span::new(0, 0);
        let odd_binding = Sexp::Bracket(
            vec![
                Sexp::Symbol("a".into(), sp),
                Sexp::Int(1, sp),
                Sexp::Symbol("b".into(), sp),
            ],
            sp,
        );
        let form = Sexp::List(
            vec![
                Sexp::Symbol("let".into(), sp),
                odd_binding,
                Sexp::Symbol("a".into(), sp),
            ],
            sp,
        );
        let out = pretty_print(&form);
        // No panic; all three binding elements are preserved somewhere.
        assert!(out.contains('a') && out.contains('1') && out.contains('b'), "got:\n{out}");
    }

    #[test]
    fn p4_nested_multiline_right_term_indents_under_right_column() {
        // spec: repl/spec.md §3.11 P4 — a multi-line right term (here a nested
        // two-arm match) opens at the right column and its continuation lines
        // indent relative to that column (its own per-vector W recurses).
        let out = pp_form("(let [d (match r [(L l) 1 (R r) 2]) e 9] d)");
        let expected = concat!(
            "(let [d (match r [(L l) 1\n",
            "                  (R r) 2])\n",
            "      e 9]\n",
            "  d)",
        );
        assert_eq!(out, expected, "got:\n{out}");
    }

    #[test]
    fn p0_zero_pair_empty_let_binding_stays_flat() {
        // spec: repl/spec.md §3.11 P0 — an empty binding vector has nothing to
        // align and renders flat with no spurious padding.
        let out = pp_form("(let [] 7)");
        assert_eq!(out, "(let [] 7)", "got:\n{out}");
    }

    // --- §3.11 P0 force-multiline propagation to ancestors (FIXME 0554) --------
    //
    // A >=2-pair let/match forces itself multi-line even when it would fit flat.
    // Every ENCLOSING form must then also render multi-line so a correct indent
    // threads down; otherwise the flat parent path renders the nested pair-form
    // at column 0, visibly misaligned.

    #[test]
    fn p0_parent_of_two_pair_let_forces_multiline_aligned() {
        // spec: repl/spec.md §3.11 P0 — the enclosing `defn` fits flat (<=40)
        // but contains a >=2-pair let, so it MUST render multi-line and the let's
        // right column MUST align to its true (indented) position, not column 0.
        let out = pp_form("(defn g [x] (let [a 1 bb 2] a))");
        let expected = concat!(
            "(defn g\n",
            "  [x]\n",
            "  (let [a  1\n",
            "        bb 2]\n",
            "    a))",
        );
        assert_eq!(out, expected, "got:\n{out}");
    }

    #[test]
    fn p0_parent_of_two_arm_match_forces_multiline_aligned() {
        // spec: repl/spec.md §3.11 P0 — same propagation for a two-arm match that
        // would fit flat inside its enclosing `defn`.
        let out = pp_form("(defn f [r] (match r [(L l) l (R r) r]))");
        let expected = concat!(
            "(defn f\n",
            "  [r]\n",
            "  (match r [(L l) l\n",
            "            (R r) r]))",
        );
        assert_eq!(out, expected, "got:\n{out}");
    }

    #[test]
    fn p0_deep_nesting_propagates_through_ancestors() {
        // spec: repl/spec.md §3.11 P0 — the force propagates through more than one
        // enclosing level; every ancestor renders multi-line and the pair-form
        // aligns to its deep indent, never column 0.
        let out = pp_form("(do (defn g [x] (let [a 1 bb 2] a)))");
        // No line other than the let's own may carry a mis-columned `bb`; the
        // binding pair `bb` must sit under `a` (right column stable).
        let a_col = out.lines().find_map(|l| l.find("[a ")).map(|c| c + 1);
        let bb_col = out.lines().find_map(|l| l.find("bb "));
        assert_eq!(a_col, bb_col, "left column must align:\n{out}");
        assert!(out.contains("bb 2]"), "pair form must be aligned:\n{out}");
    }

    #[test]
    fn p0_bracket_parent_of_two_pair_let_does_not_share_line() {
        // spec: repl/spec.md §3.11 P0 — a bracket holding a >=2-pair let must not
        // render single-line (which would place the let at column 0). The let is
        // pushed to its own line and aligns correctly.
        let out = pp_form("[x (let [a 1 bb 2] a)]");
        assert!(out.contains('\n'), "bracket must break to multi-line:\n{out}");
        let a_col = out.lines().find_map(|l| l.find("[a ")).map(|c| c + 1);
        let bb_col = out.lines().find_map(|l| l.find("bb "));
        assert_eq!(a_col, bb_col, "nested let left column must align:\n{out}");
    }

    #[test]
    fn subtree_predicate_detects_nested_and_ignores_shallow() {
        // Unit-level guard on the propagation predicate itself.
        let two_pair = cranelisp_frontend::parse("(defn g [x] (let [a 1 bb 2] a))").unwrap();
        assert!(subtree_contains_pair_form(&two_pair[0]));
        let one_pair = cranelisp_frontend::parse("(defn g [x] (let [a 1] a))").unwrap();
        assert!(!subtree_contains_pair_form(&one_pair[0]));
        let no_pair = cranelisp_frontend::parse("(defn g [x] (+ x 1))").unwrap();
        assert!(!subtree_contains_pair_form(&no_pair[0]));
    }
}
