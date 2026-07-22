// S-expression pretty-printer — the code half of the ONE styling seam.
//
// The code printer is ONE role-assignment walk over the `Sexp` tree with two
// emitters (design/arch/repl-styling-seam.md §4 P4/P5):
//
//   - `pp` — the COMPUTED-LAYOUT emitter: the §3.11 alignment algorithm
//     (FLAT_THRESHOLD, pair forms, special-form indent) building a `StyledDoc`
//     of role-tagged spans instead of calling `styled()` inline. Used for
//     `/sexp`, single-line round-trippable `/source` code, agent code blocks.
//   - `style_source_verbatim` — the SPANS-OVER-ORIGINAL-BYTES emitter: parses
//     caller-supplied source and lays role spans over the ORIGINAL byte ranges
//     (gaps are `Plain`), so the user's own whitespace/layout is preserved
//     exactly; a parse failure emits the whole text as `Plain` (never a
//     wrong-guess scan). This REPLACES the deleted `style_tokens` byte-scanner
//     and its `consume_*` helpers.
//
// Both emitters assign roles by node KIND from the same vocabulary; `render`
// (the seam) applies the §10.3 style table once. No `styled()` call lives here.

use cranelisp_types::Sexp;

use crate::styled::{Role, StyledDoc, render};

/// Flat-length threshold: forms shorter than this are kept on one line.
const FLAT_THRESHOLD: usize = 40;

/// Special forms that use 2-space body indentation instead of argument alignment.
const SPECIAL_FORM_INDENT: &[&str] = &[
    "defn", "deftype", "deftrait", "impl", "let", "match",
    "fn", "if", "do", "defmacro",
];

/// Pretty-print and syntax-highlight a Sexp tree (`/sexp`, agent code blocks).
///
/// Returns a rendered string. When colour is disabled, returns plain indented
/// text — byte-identical to the role-free content (§10.3 requirement 2).
pub fn pretty_print(sexp: &Sexp) -> String {
    render(&pp(sexp, 0, false))
}

/// The `StyledDoc` for a Sexp tree — the composition point for callers that wrap
/// the code in a larger doc (e.g. a `; source for NAME` header) before rendering.
pub(crate) fn pretty_print_doc(sexp: &Sexp) -> StyledDoc {
    pp(sexp, 0, false)
}

/// Serialize a Sexp tree to PLAIN indented text — the role-free `.text()` of the
/// pretty-print doc, forced regardless of the global colour gate.
///
/// This is the **data-serialization** path (persisted `.cl` backing source, the
/// `FailedForm.text`, the introspection `source` fallback), distinct from
/// `pretty_print` whose output is colour-gated for **display**. Under colour-ON a
/// TTY REPL session that serialized through `pretty_print` would embed SGR escape
/// bytes into the persisted source, so the next load fails to re-parse it. This
/// function is `render`-free — it never consults the colour gate — so the bytes
/// it produces are always re-parseable (§10.2: no escape ever enters stored
/// source).
pub fn pretty_print_plain(sexp: &Sexp) -> String {
    pp(sexp, 0, false).text()
}

/// Pretty-print caller-supplied source (`/source`, agent ```lisp blocks).
///
/// Renders `pretty_print_str_doc`. Colour-off is byte-identical to the source's
/// role-free content (the verbatim-echo contract).
pub fn pretty_print_str(source: &str) -> String {
    render(&pretty_print_str_doc(source))
}

/// The `StyledDoc` for caller-supplied source — role spans over the ORIGINAL
/// bytes so the user's own whitespace/layout is preserved exactly.
///
/// Line-by-line (REPL display strings are often multi-line):
///   - a pure `;` comment line is a SOURCE comment (R5 italic);
///   - a code line that round-trips through the reader is re-laid-out via `pp`
///     (the computed-layout emitter — the §3.11 alignment `/sexp` shares);
///   - any other code line is emitted verbatim, role spans over its original
///     bytes (`style_source_verbatim`) so qualified names / multi-line user
///     layout survive untouched.
///
/// An inline comment suffix is split off and re-attached as an R5 span.
pub(crate) fn pretty_print_str_doc(source: &str) -> StyledDoc {
    let mut doc = StyledDoc::new();
    for (idx, line) in source.lines().enumerate() {
        if idx > 0 {
            doc.plain("\n");
        }
        let trimmed = line.trim();
        // Pure comment lines (start with ;) — a user source comment (R5).
        if trimmed.starts_with(';') {
            doc.push(Role::SourceComment, trimmed);
            continue;
        }

        // Lines with inline comments: split at first unquoted `;`.
        let (code_part, comment_part) = split_inline_comment(line);

        if code_part.trim().is_empty() {
            // Nothing to parse, just the comment (or the raw line verbatim).
            match comment_part {
                Some(comment) => doc.push(Role::SourceComment, comment),
                None => doc.plain(line),
            }
            continue;
        }

        // Parse the code portion. When the reader round-trips it (the flat form
        // equals the input), re-lay-out via `pp`; otherwise lay role spans over
        // the ORIGINAL bytes so qualified names / user layout survive (this is
        // the emitter that replaces the deleted `style_tokens` byte-scanner).
        match try_parse_and_format_doc(code_part) {
            Some(code_doc) => doc.extend(code_doc),
            None => doc.extend(style_source_verbatim(code_part)),
        }

        // Re-attach comment suffix as a source comment (R5).
        if let Some(comment) = comment_part {
            doc.plain(" ");
            doc.push(Role::SourceComment, comment);
        }
    }
    doc
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

/// Try to parse code through the reader and re-lay-it-out via `pp`.
///
/// Returns `None` if parsing fails or the round-trip changes the content
/// (e.g., qualified names with `/` in colon-prefixed symbols, reader
/// shorthand, or non-canonical whitespace) — the caller then falls back to the
/// verbatim byte-span emitter, which preserves the original bytes exactly.
fn try_parse_and_format_doc(code: &str) -> Option<StyledDoc> {
    let sexps = cranelisp_frontend::parse(code).ok()?;
    if sexps.is_empty() {
        return None;
    }
    // Verify round-trip: if the flat representation differs from input, the
    // parser didn't preserve the content faithfully.
    let flat_parts: Vec<String> = sexps.iter().map(|s| s.format_flat()).collect();
    let round_tripped = flat_parts.join(" ");
    if round_tripped.trim() != code.trim() {
        return None;
    }
    let mut doc = StyledDoc::new();
    for (i, s) in sexps.iter().enumerate() {
        if i > 0 {
            doc.plain(" ");
        }
        doc.extend(pp(s, 0, false));
    }
    Some(doc)
}

/// The verbatim-source emitter — role spans over the ORIGINAL byte ranges.
///
/// Parses `code` and walks the tree, laying a role span over each atom's
/// original byte range and leaving gaps (parens, brackets, whitespace) as
/// `Plain`; the concatenation of the spans is therefore the original text,
/// preserving the caller's layout exactly. On parse failure — or if the byte
/// walk ever fails to reproduce `code` exactly (a defensive guard against a
/// reader span that does not align to the source, e.g. desugared reader
/// shorthand) — the whole text is emitted as one `Plain` span (never a
/// wrong-guess scan). This replaces the deleted `style_tokens` byte-scanner.
fn style_source_verbatim(code: &str) -> StyledDoc {
    if let Ok(sexps) = cranelisp_frontend::parse(code)
        && !sexps.is_empty()
    {
        let mut doc = StyledDoc::new();
        let mut cursor = 0usize;
        let walked = sexps
            .iter()
            .all(|s| emit_source_spans(code, s, false, &mut cursor, &mut doc));
        if walked {
            if cursor < code.len() && code.is_char_boundary(cursor) {
                doc.plain(&code[cursor..]);
            }
            // Ultimate byte-identity guard: the verbatim echo MUST reproduce the
            // input exactly (§10.3 requirement 2). If a reader span mis-aligned,
            // fall back to whole-Plain rather than corrupt the bytes.
            if doc.text() == code {
                return doc;
            }
        }
    }
    StyledDoc::span(Role::Plain, code)
}

/// Emit role spans for `sexp` over `code`'s original bytes, advancing `cursor`.
/// Returns `false` on any span that is out of bounds, non-monotonic, or off a
/// char boundary — the caller then discards the partial walk and emits whole-
/// Plain. Atoms carry their kind's role (head position ⇒ `Head`); parens/
/// brackets/whitespace fall in the `Plain` gaps.
fn emit_source_spans(
    code: &str,
    sexp: &Sexp,
    in_head: bool,
    cursor: &mut usize,
    doc: &mut StyledDoc,
) -> bool {
    let sp = sexp.span();
    let s = sp.start as usize;
    let e = sp.end as usize;
    if e > code.len()
        || s > e
        || s < *cursor
        || !code.is_char_boundary(s)
        || !code.is_char_boundary(e)
        || !code.is_char_boundary(*cursor)
    {
        return false;
    }
    if s > *cursor {
        doc.plain(&code[*cursor..s]);
        *cursor = s;
    }
    match sexp {
        Sexp::List(children, _) | Sexp::Bracket(children, _) => {
            let is_list = matches!(sexp, Sexp::List(..));
            for (i, ch) in children.iter().enumerate() {
                if !emit_source_spans(code, ch, is_list && i == 0, cursor, doc) {
                    return false;
                }
            }
            // Trailing gap within this node — the closing `)`/`]` and any inner
            // whitespace after the last child.
            if e > *cursor {
                doc.plain(&code[*cursor..e]);
                *cursor = e;
            }
        }
        Sexp::Annotated {
            annotation,
            subject,
            ..
        } => {
            let annotation_end = annotation.span().end as usize;
            if annotation_end > e || annotation_end < s {
                return false;
            }
            doc.push(Role::TypeAnnotation, &code[s..annotation_end]);
            *cursor = annotation_end;
            if !emit_source_spans(code, subject, false, cursor, doc) {
                return false;
            }
        }
        Sexp::Symbol(name, _) => {
            let role = if in_head {
                Role::Head
            } else if name.starts_with(':') {
                Role::TypeAnnotation
            } else {
                Role::Plain
            };
            doc.push(role, &code[s..e]);
            *cursor = e;
        }
        Sexp::Int(_, _) | Sexp::Float(_, _) | Sexp::Bool(_, _) => {
            doc.push(if in_head { Role::Head } else { Role::LitNumBool }, &code[s..e]);
            *cursor = e;
        }
        Sexp::Str(_, _) => {
            doc.push(if in_head { Role::Head } else { Role::LitStr }, &code[s..e]);
            *cursor = e;
        }
        Sexp::Comment(_, _) => {
            doc.push(Role::SourceComment, &code[s..e]);
            *cursor = e;
        }
    }
    true
}

/// Recursive computed-layout pretty-printer core (the §3.11 alignment emitter).
///
/// - `sexp`: the node to format
/// - `indent`: current indentation level (characters from left margin)
/// - `in_head`: whether this node is in head position of a parent list
///
/// Builds a `StyledDoc` of role-tagged spans; `render` (the seam) is the sole
/// site that turns roles into SGR.
fn pp(sexp: &Sexp, indent: usize, in_head: bool) -> StyledDoc {
    match sexp {
        Sexp::Symbol(name, _) => pp_symbol(name, in_head),
        Sexp::Int(v, _) => style_atom(&v.to_string(), in_head, Role::LitNumBool),
        Sexp::Float(v, _) => {
            let s = format!("{v}");
            let s = if s.contains('.') { s } else { format!("{s}.0") };
            style_atom(&s, in_head, Role::LitNumBool)
        }
        Sexp::Bool(v, _) => {
            let s = if *v { "true" } else { "false" };
            style_atom(s, in_head, Role::LitNumBool)
        }
        Sexp::Str(s, _) => {
            let escaped = s
                .replace('\\', "\\\\")
                .replace('"', "\\\"")
                .replace('\n', "\\n")
                .replace('\t', "\\t");
            let text = format!("\"{escaped}\"");
            style_atom(&text, in_head, Role::LitStr)
        }
        Sexp::List(children, _) => pp_list(children, indent, in_head),
        Sexp::Bracket(children, _) => pp_bracket(children, indent),
        Sexp::Annotated {
            annotation,
            subject,
            ..
        } => {
            let mut doc = StyledDoc::new();
            doc.push(Role::TypeAnnotation, format!(":{}", annotation.format_flat()));
            doc.plain(" ");
            doc.extend(pp(subject, indent + 2, false));
            doc
        }
        Sexp::Comment(text, _) => {
            let t = if text.is_empty() {
                ";".to_string()
            } else {
                format!("; {text}")
            };
            StyledDoc::span(Role::SourceComment, t)
        }
    }
}

/// An atom span: bold in head position, else its literal role (R2/R3).
fn style_atom(text: &str, in_head: bool, lit_role: Role) -> StyledDoc {
    StyledDoc::span(if in_head { Role::Head } else { lit_role }, text)
}

/// A symbol span: `Head` in head position, `TypeAnnotation` for a `:`-prefixed
/// symbol, else `Plain` (R15 name).
fn pp_symbol(name: &str, in_head: bool) -> StyledDoc {
    let role = if in_head {
        Role::Head
    } else if name.starts_with(':') {
        Role::TypeAnnotation
    } else {
        Role::Plain
    };
    StyledDoc::span(role, name)
}

/// Pretty-print a parenthesized list.
fn pp_list(children: &[Sexp], indent: usize, in_head: bool) -> StyledDoc {
    if children.is_empty() {
        return maybe_bold_brackets("(", ")", in_head, StyledDoc::new());
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
fn try_pp_pair_form(children: &[Sexp], indent: usize, in_head: bool) -> Option<StyledDoc> {
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
fn try_pp_let(children: &[Sexp], indent: usize, in_head: bool) -> Option<StyledDoc> {
    let binding = match children.get(1) {
        Some(Sexp::Bracket(items, _)) => items,
        _ => return None,
    };
    let pairs = as_pairs(binding)?;
    if pairs.len() < 2 {
        return None; // P0 — 0/1 pair has nothing to align.
    }
    let (open, close) = pair_form_brackets(in_head);
    // Prefix "(let " is 5 unstyled columns; the `[` lands at indent + 5, its
    // content (left column) at indent + 6.
    let left_col = indent + 6;
    let mut result = StyledDoc::new();
    result.extend(open);
    result.push(Role::Head, "let");
    result.plain(" ");
    result.extend(pair_vector_layout(&pairs, left_col));

    let body_indent = indent + 2;
    let pad = " ".repeat(body_indent);
    for body in &children[2..] {
        result.plain(format!("\n{pad}"));
        result.extend(pp(body, body_indent, false));
    }
    result.extend(close);
    Some(result)
}

/// `(match <scrutinee> [l0 r0 l1 r1 …])` — the arm vector is the `[...]`
/// following the scrutinee (§3.11). The scrutinee stays flat on the head line;
/// the `[` sits at `indent + len("(match ") + flatwidth(scrutinee) + 1`, so the
/// left column starts one past that.
fn try_pp_match(children: &[Sexp], indent: usize, in_head: bool) -> Option<StyledDoc> {
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
    // Prefix "(match " (7) + scrutinee (flat) + " " (1); the `[` lands after it,
    // and the left column starts one past the `[`.
    let left_col = indent + 7 + scrutinee.format_flat().len() + 1 + 1;
    let mut result = StyledDoc::new();
    result.extend(open);
    result.push(Role::Head, "match");
    result.plain(" ");
    result.extend(pp(scrutinee, 0, false));
    result.plain(" ");
    result.extend(pair_vector_layout(&pairs, left_col));
    result.extend(close);
    Some(result)
}

/// The `(` / `)` spans for a pair-layout form, bolded (Head) when in head position.
fn pair_form_brackets(in_head: bool) -> (StyledDoc, StyledDoc) {
    let role = if in_head { Role::Head } else { Role::Plain };
    (StyledDoc::span(role, "("), StyledDoc::span(role, ")"))
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
fn pair_vector_layout(pairs: &[(&Sexp, &Sexp)], left_col: usize) -> StyledDoc {
    let w = pairs
        .iter()
        .map(|(l, _)| l.format_flat().len())
        .max()
        .unwrap_or(0);
    let right_col = left_col + w + 1;

    let mut out = StyledDoc::new();
    out.plain("[");
    for (i, (left, right)) in pairs.iter().enumerate() {
        if i > 0 {
            // P1/P2 — one pair per line, left column.
            out.plain(format!("\n{}", " ".repeat(left_col)));
        }
        out.extend(pp(left, 0, false)); // left term rendered flat (styled)
        let left_width = left.format_flat().len();
        out.plain(" ".repeat(right_col - left_col - left_width)); // P3 pad to right column
        out.extend(pp(right, right_col, false)); // P4 — right term opens at right_col
    }
    out.plain("]");
    out
}

/// Check if a list is a type annotation list (first child is :symbol).
fn is_type_annotation_list(children: &[Sexp]) -> bool {
    matches!(children.first(), Some(Sexp::Symbol(name, _)) if name.starts_with(':'))
}

/// Render an entire type annotation list as a single R4 span (cyan).
/// Per §10.3 R4: the whole type annotation is one cyan construct (no internal
/// `module/` decomposition). In head position it is bolded (R1) instead.
fn pp_type_annotation_list(children: &[Sexp], indent: usize, in_head: bool) -> StyledDoc {
    // Compute the flat representation.
    let flat = flat_list(children);

    let role = if in_head { Role::Head } else { Role::TypeAnnotation };
    if flat.len() <= FLAT_THRESHOLD {
        // Single-line: the whole annotation is one span.
        let inner = flat_content_unstyled(children);
        StyledDoc::span(role, format!("({inner})"))
    } else {
        // Multi-line type annotations — still one span (render splits per line).
        StyledDoc::span(role, pp_type_multiline_unstyled(children, indent))
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
fn pp_list_flat(children: &[Sexp], in_head: bool) -> StyledDoc {
    let mut inner = StyledDoc::new();
    for (i, child) in children.iter().enumerate() {
        if i > 0 {
            inner.plain(" ");
        }
        inner.extend(pp(child, 0, i == 0));
    }
    maybe_bold_brackets("(", ")", in_head, inner)
}

/// Render a long list across multiple lines.
fn pp_list_multiline(children: &[Sexp], indent: usize, in_head: bool) -> StyledDoc {
    let head = &children[0];
    let head_doc = pp(head, indent, true);
    let head_name = head_symbol_name(head);

    let is_special = head_name
        .as_ref()
        .map(|n| SPECIAL_FORM_INDENT.contains(&n.as_str()))
        .unwrap_or(false);

    let bracket_role = if in_head { Role::Head } else { Role::Plain };

    let mut result = StyledDoc::new();
    result.push(bracket_role, "(");
    result.extend(head_doc);

    if children.len() == 1 {
        result.push(bracket_role, ")");
        return result;
    }

    // Body indent differs between special forms (2-space) and standard forms
    // (align under the first argument).
    let arg_indent = if is_special {
        indent + 2
    } else {
        indent + 1 + head.format_flat().len() + 1 // '(' + head + ' '
    };
    let pad = " ".repeat(arg_indent);

    // First argument on the same line as the head.
    result.plain(" ");
    result.extend(pp(&children[1], arg_indent, false));

    // Remaining arguments on new lines.
    for child in &children[2..] {
        result.plain(format!("\n{pad}"));
        result.extend(pp(child, arg_indent, false));
    }
    result.push(bracket_role, ")");
    result
}

/// Extract the symbol name from a head node, if it is a plain symbol.
fn head_symbol_name(sexp: &Sexp) -> Option<String> {
    match sexp {
        Sexp::Symbol(name, _) => Some(name.clone()),
        _ => None,
    }
}

/// Pretty-print a bracket form.
fn pp_bracket(children: &[Sexp], indent: usize) -> StyledDoc {
    if children.is_empty() {
        return StyledDoc::span(Role::Plain, "[]");
    }

    // Flat representation for length measurement.
    let parts: Vec<String> = children.iter().map(|c| c.format_flat()).collect();
    let flat = format!("[{}]", parts.join(" "));
    // As in `pp_list`: the single-line path renders children at `indent = 0`, so
    // avoid it when a descendant is a forced multi-line pair-form (FIXME 0554).
    if flat.len() <= FLAT_THRESHOLD && !children.iter().any(subtree_contains_pair_form) {
        // Single line: no head-position bolding in brackets.
        let mut result = StyledDoc::new();
        result.plain("[");
        for (i, child) in children.iter().enumerate() {
            if i > 0 {
                result.plain(" ");
            }
            result.extend(pp(child, 0, false));
        }
        result.plain("]");
        return result;
    }

    // Multi-line bracket form.
    let child_indent = indent + 1;
    let pad = " ".repeat(child_indent);
    let mut result = StyledDoc::new();
    result.plain("[");
    result.extend(pp(&children[0], child_indent, false));

    let mut unstyled_line_len = children[0].format_flat().len() + 1; // '[' + first child
    for child in &children[1..] {
        // Try to fit on the current line.
        // Use unstyled length to avoid ANSI escape sequences inflating the count.
        // A forced multi-line pair-form child (FIXME 0554) never shares a line —
        // it must open at `child_indent` where `pp` aligns it correctly.
        let child_flat_len = child.format_flat().len();
        if !subtree_contains_pair_form(child)
            && unstyled_line_len + 1 + child_flat_len <= FLAT_THRESHOLD
        {
            result.plain(" ");
            unstyled_line_len += 1 + child_flat_len;
            result.extend(pp(child, child_indent, false));
        } else {
            result.plain(format!("\n{pad}"));
            result.extend(pp(child, child_indent, false));
            unstyled_line_len = child_indent + child_flat_len;
        }
    }
    result.plain("]");
    result
}

/// Wrap `inner` with brackets, bolding them (Head role) if in head position.
fn maybe_bold_brackets(open: &str, close: &str, in_head: bool, inner: StyledDoc) -> StyledDoc {
    let role = if in_head { Role::Head } else { Role::Plain };
    let mut doc = StyledDoc::new();
    doc.push(role, open);
    doc.extend(inner);
    doc.push(role, close);
    doc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::style::test_support::ColorGuard;

    // In test context, colour is disabled (stdout is not a TTY),
    // so we test indentation behavior without escape sequences.

    // === §10.3 colour-ON byte-exact code fixtures (Wave-D /dev obligation) ====

    // K5 — code: the head of an apply form is R1 bold, int literals R2 yellow,
    // parens/whitespace R15 (§10.3 R1/R2). The SGR spans wrap the SAME chars at
    // the same columns the colour-off output produces (requirement 3).
    // spec: repl/spec.md §10.3 R1/R2 — pretty-printed code.
    #[test]
    fn colour_on_k5_code_head_bold_literals_yellow() {
        let _g = ColorGuard::force(true);
        assert_eq!(
            pretty_print_str("(+ 1 2)"),
            "(\x1b[1m+\x1b[0m \x1b[33m1\x1b[0m \x1b[33m2\x1b[0m)"
        );
    }

    // K6 — a `;` SOURCE comment is R5 italic (FIXME 0561: source = italic, NOT
    // the dim R6 the REPL metadata `;` lines use). Colour-off it is plain.
    // spec: repl/spec.md §10.3 R5 — source comment (0561 source half).
    #[test]
    fn colour_on_k6_source_comment_italic() {
        let _g = ColorGuard::force(true);
        assert_eq!(pretty_print_str("; double it"), "\x1b[3m; double it\x1b[0m");
    }

    // Colour-off, the same source comment is exactly its text (no SGR).
    #[test]
    fn colour_off_k6_source_comment_plain() {
        let _g = ColorGuard::force(false);
        assert_eq!(pretty_print_str("; double it"), "; double it");
    }

    // The DATA-serialization path (`pretty_print_plain`) NEVER embeds SGR, even
    // when colour is forced ON — the persisted `.cl` backing source / failed-form
    // text must always re-parse. This pins the I1 correctness fix: a TTY session
    // (colour ON) serializing a definition through the DISPLAY path (`pretty_print`)
    // would write escape bytes into stored source; the plain path must not.
    // spec: repl/spec.md §10.2 — no SGR ever enters stored source (must re-parse).
    #[test]
    fn pretty_print_plain_never_embeds_sgr_and_round_trips() {
        let _g = ColorGuard::force(true);
        // A form with a string literal + head symbol + int literal — every element
        // the display highlighter would wrap in SGR.
        let src = "(defn greet [] \"hi\")";
        let sexp = &cranelisp_frontend::parse(src).unwrap()[0];

        // Confirm the DISPLAY path DOES embed SGR under colour-ON — this is exactly
        // the byte that corrupts persisted source, so a revert of any of the four
        // I1 sites back to `pretty_print` re-breaks re-parseability.
        assert!(
            crate::pretty::pretty_print(sexp).contains('\u{1b}'),
            "display pretty_print embeds SGR under colour-ON (the bug pretty_print_plain avoids)"
        );

        // The data-serialization path must be SGR-free and re-parseable.
        let plain = pretty_print_plain(sexp);
        assert!(
            !plain.contains('\u{1b}'),
            "pretty_print_plain must never embed SGR: {plain:?}"
        );
        let reparsed = cranelisp_frontend::parse(&plain)
            .unwrap_or_else(|e| panic!("stored source must re-parse: {e} ({plain:?})"));
        assert_eq!(reparsed.len(), 1, "round-trips to one form: {plain:?}");
    }

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
