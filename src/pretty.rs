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

    // Compute flat representation to measure length.
    let flat = flat_list(children);
    if flat.len() <= FLAT_THRESHOLD {
        return pp_list_flat(children, in_head);
    }

    // Multi-line mode.
    pp_list_multiline(children, indent, in_head)
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
    if flat.len() <= FLAT_THRESHOLD {
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
        let child_flat_len = child.format_flat().len();
        if unstyled_line_len + 1 + child_flat_len <= FLAT_THRESHOLD {
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
}
