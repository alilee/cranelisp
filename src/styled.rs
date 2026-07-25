// The role-span carrier and the ONE render — the single manifestation of the
// `repl/spec.md` §10.3 Token/Element Styling Contract (S108 Increment 3, E4).
//
// This module is Layer 1.5 of the terminal styling system — it sits between the
// low-level `style::styled` SGR primitive and every token-styled REPL producer
// (values, introspection lines, pretty-printed code, `/search` rows, errors,
// warnings, prompts, banners). A producer emits ROLE-tagged spans at
// construction (`StyledDoc`); `render` applies the §10.3 style table ONCE, at
// the display boundary. Role knowledge is defined once here (`role_style`) and
// applied once here (`render`) — drift between surfaces is structurally
// impossible (Principle 7 single-source; Principle 18 enforce-by-representation).
//
// `render` is the sole caller of `style::styled` for role-based output. The only
// other `style::styled` callers are the agent prose frame (`style::agent_prose`
// R14 gutter) and the agent markdown formatter (`agent/render.rs`) — both the
// pre-existing agent-frame single-source the E4 design leaves UNCHANGED
// (`design/arch/repl-styling-seam.md` §5 P9).

use crate::style::{self, Style};

/// The §10.3 element → style-role vocabulary. Exactly one role per byte of
/// token-styled output (§10.3 requirement 1). The `repl/spec.md` §10.3 role
/// table (R1..R15) maps 1:1 onto these variants; `role_style` is the single code
/// manifestation of that table.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Role {
    /// R1 — head of an apply form (pretty-printed code only); bold.
    Head,
    /// R2 — int / float / bool literal (code AND value display); yellow.
    LitNumBool,
    /// R3 — string literal (code AND value display); green.
    LitStr,
    /// R4 — a type annotation `:Type`/`:module/Type`/`:(Fn …)`, styled as a
    /// SINGLE cyan construct (no internal `module/` decomposition — user ruling
    /// 2026-07-12); cyan.
    TypeAnnotation,
    /// R5 — a `;` SOURCE-code comment (user-authored, surfaced by `/source`/
    /// `/sexp`/agent code blocks); italic. (FIXME 0561: source = italic.)
    SourceComment,
    /// R6 — a REPL structured-metadata `;` line/suffix (`; defn`, `; match:`,
    /// `; impl:`, `; doc:`, `; warning:` prefix, lifecycle notes); dim.
    /// (FIXME 0561: REPL metadata = dim, distinct from a source comment.)
    ReplMetadata,
    /// R7 — the `module/` prefix on a bare fully-qualified symbol NAME (NOT
    /// inside a type annotation); dim.
    ModulePrefix,
    /// R8 — the `Error:` / `runtime error:` keyword; bold red.
    ErrorKeyword,
    /// R9 — the error message body; red.
    ErrorDetail,
    /// R10 — the `Warning:`-class keyword; bold yellow. Part of the complete
    /// §10.3 role vocabulary (requirement 1). The REPL currently surfaces warnings
    /// via the `; warning:` comment form (R6 prefix + R11 detail, `format_eval_result`),
    /// so no producer emits a bare `Warning:` keyword yet — the role is kept so a
    /// future `Warning:`-keyword surface has its byte-pinned role (the per-role SGR
    /// is pinned in `role_style_matches_10_3_table`).
    #[allow(dead_code)]
    WarnKeyword,
    /// R11 — the warning message body; yellow.
    WarnDetail,
    /// R12 — a slash-command category header (`Fns:`, `Types:`, …); bold.
    Header,
    /// R13 — the prompt line and the startup banner; dim.
    Prompt,
    /// R14 — the agent prose-frame `▌` gutter; bright magenta.
    AgentGutter,
    /// R15 — everything else (non-prefix name parts, ctor dot-names, `<closure>`,
    /// bracket/paren punctuation, whitespace, layout padding); default (unstyled).
    Plain,
}

/// Map a role to its concrete `Style` (`None` ⇒ R15 default, no SGR).
///
/// This is the SINGLE code manifestation of the `repl/spec.md` §10.3 role table.
/// The per-role SGR bytes are pinned by unit tests (`role_style_matches_10_3_table`).
pub(crate) fn role_style(role: Role) -> Option<Style> {
    match role {
        Role::Head => Some(Style::Bold),                 // R1  — 1
        Role::LitNumBool => Some(Style::Yellow),         // R2  — 33
        Role::LitStr => Some(Style::Green),              // R3  — 32
        Role::TypeAnnotation => Some(Style::Cyan),       // R4  — 36
        Role::SourceComment => Some(Style::Italic),      // R5  — 3
        Role::ReplMetadata => Some(Style::Dim),          // R6  — 2
        Role::ModulePrefix => Some(Style::Dim),          // R7  — 2
        Role::ErrorKeyword => Some(Style::BoldRed),      // R8  — 1;31
        Role::ErrorDetail => Some(Style::Red),           // R9  — 31
        Role::WarnKeyword => Some(Style::BoldYellow),    // R10 — 1;33
        Role::WarnDetail => Some(Style::Yellow),         // R11 — 33
        Role::Header => Some(Style::Bold),               // R12 — 1
        Role::Prompt => Some(Style::Dim),                // R13 — 2
        Role::AgentGutter => Some(Style::BrightMagenta), // R14 — 95
        Role::Plain => None,                             // R15 — default
    }
}

/// A role-tagged span sequence — the carrier a producer builds at construction.
/// Newlines are ordinary `Plain` span content; the concatenation of every span's
/// text is the role-free plain text (`text`).
#[derive(Debug, Clone, Default)]
pub(crate) struct StyledDoc {
    spans: Vec<(Role, String)>,
}

impl StyledDoc {
    pub(crate) fn new() -> Self {
        StyledDoc { spans: Vec::new() }
    }

    /// A single-span doc.
    pub(crate) fn span(role: Role, text: impl Into<String>) -> Self {
        let mut d = StyledDoc::new();
        d.push(role, text);
        d
    }

    /// Push a role-tagged span. An empty span is dropped (keeps `render`
    /// deterministic — no zero-width SGR wrappers).
    pub(crate) fn push(&mut self, role: Role, text: impl Into<String>) {
        let text = text.into();
        if !text.is_empty() {
            self.spans.push((role, text));
        }
    }

    /// Push a `Plain` (R15) span.
    pub(crate) fn plain(&mut self, text: impl Into<String>) {
        self.push(Role::Plain, text);
    }

    /// Append another doc's spans.
    pub(crate) fn extend(&mut self, other: StyledDoc) {
        self.spans.extend(other.spans);
    }

    /// The role-free plain text: the concatenation of every span's content, with
    /// NO SGR whatsoever. `render(colour-off)` is byte-identical to this (§10.3
    /// requirement 2 — the non-TTY golden / agent `strip_ansi` membrane contract).
    pub(crate) fn text(&self) -> String {
        let mut s = String::new();
        for (_, t) in &self.spans {
            s.push_str(t);
        }
        s
    }
}

/// Render a `StyledDoc` — the ONLY site that applies §10.3 styling to role spans.
///
/// - Colour OFF (§10.1 — `--no-color`, `NO_COLOR`, non-TTY): returns exactly the
///   plain text (`doc.text()`) — byte-identical to the role-free content, zero
///   SGR (§10.3 requirement 2).
/// - Colour ON: wraps each non-`Plain` span in its role's SGR (§10.3 req 3), at
///   the SAME columns the plain text produces. A span whose text spans multiple
///   lines is wrapped PER LINE — the reset is emitted before every newline and
///   the SGR reopened after (§10.2: no styled span crosses a newline). The
///   newlines themselves stay unstyled, so column positions are unchanged.
pub(crate) fn render(doc: &StyledDoc) -> String {
    if !style::is_color_enabled() {
        return doc.text();
    }
    let mut out = String::with_capacity(doc.text().len());
    for (role, text) in &doc.spans {
        match role_style(*role) {
            None => out.push_str(text),
            Some(st) => {
                // §10.2 — terminate the span before any newline and reopen after,
                // so no SGR run crosses a line boundary.
                let mut first = true;
                for segment in text.split('\n') {
                    if !first {
                        out.push('\n');
                    }
                    first = false;
                    if !segment.is_empty() {
                        out.push_str(&style::styled(segment, st));
                    }
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::style::test_support::ColorGuard;

    // spec: repl/spec.md §10.3 — the per-role SGR parameter string of the R1..R14
    // role table, pinned via `role_style` → `Style::sgr_code`. Forces colour ON
    // (ColorGuard) so the SGR path is exercised from a non-TTY unit process.
    #[test]
    fn role_style_matches_10_3_table() {
        let _g = ColorGuard::force(true);
        // Each role wraps a marker in exactly the §10.3 SGR.
        let cases: &[(Role, &str)] = &[
            (Role::Head, "1"),            // R1
            (Role::LitNumBool, "33"),     // R2
            (Role::LitStr, "32"),         // R3
            (Role::TypeAnnotation, "36"), // R4
            (Role::SourceComment, "3"),   // R5
            (Role::ReplMetadata, "2"),    // R6
            (Role::ModulePrefix, "2"),    // R7
            (Role::ErrorKeyword, "1;31"), // R8
            (Role::ErrorDetail, "31"),    // R9
            (Role::WarnKeyword, "1;33"),  // R10
            (Role::WarnDetail, "33"),     // R11
            (Role::Header, "1"),          // R12
            (Role::Prompt, "2"),          // R13
            (Role::AgentGutter, "95"),    // R14
        ];
        for (role, sgr) in cases {
            let doc = StyledDoc::span(*role, "X");
            assert_eq!(
                render(&doc),
                format!("\x1b[{sgr}mX\x1b[0m"),
                "role {role:?} must render SGR {sgr}"
            );
        }
        // R15 Plain adds no SGR.
        assert_eq!(render(&StyledDoc::span(Role::Plain, "X")), "X");
    }

    // spec: repl/spec.md §10.3 requirement 2 — `render(colour-off)` is byte-
    // identical to `doc.text()` (the plain-text / agent-membrane contract).
    #[test]
    fn render_colour_off_is_plain_text() {
        let _g = ColorGuard::force(false);
        let mut doc = StyledDoc::new();
        doc.push(Role::TypeAnnotation, ":primitives/Int");
        doc.plain(" ");
        doc.push(Role::LitNumBool, "3");
        assert_eq!(render(&doc), ":primitives/Int 3");
        assert_eq!(render(&doc), doc.text());
        assert!(!render(&doc).contains('\u{1b}'));
    }

    // spec: repl/spec.md §10.2 — a styled span terminates with a reset before a
    // newline and reopens after; no SGR crosses a line boundary, and the newline
    // stays unstyled (columns unchanged).
    #[test]
    fn multiline_span_resets_before_newline() {
        let _g = ColorGuard::force(true);
        let doc = StyledDoc::span(Role::TypeAnnotation, "(Fn\n  a)");
        assert_eq!(render(&doc), "\x1b[36m(Fn\x1b[0m\n\x1b[36m  a)\x1b[0m");
        // Every styled run is reset-terminated; no ESC precedes a raw '\n'.
        let r = render(&doc);
        for (i, _) in r.match_indices('\n') {
            assert!(
                r[..i].ends_with("\x1b[0m"),
                "reset must precede newline: {r:?}"
            );
        }
    }

    // Colour-off, the same multi-line span is exactly its text (no SGR).
    #[test]
    fn multiline_span_colour_off_is_text() {
        let _g = ColorGuard::force(false);
        let doc = StyledDoc::span(Role::TypeAnnotation, "(Fn\n  a)");
        assert_eq!(render(&doc), "(Fn\n  a)");
    }
}
