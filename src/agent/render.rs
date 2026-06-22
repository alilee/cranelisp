// agent/render.rs — agent output rendering (design/int/agent.md §14, Cluster A).
//
// R1 (binding): everything here is AGENT-OUTPUT-ONLY and fully
// `#[cfg(feature = "agent")]`. It *consumes* `crate::pretty` and `crate::style`,
// never modifies them, and is never reachable from the default REPL render path.
// Feature-off this module does not exist and the binary is byte-identical (§1).
//
// Three experience improvements + the ANSI-leak defect fix (§14.6):
//   1. `agent_input_prefix` — the `agent>` glyph at BOTH agent-echo sites (§14.2),
//      so the pull echo and the (S89) Build-submit echo cannot diverge.
//   2. `markdown_to_terminal` — formats the markdown the model emits (headings,
//      lists, **bold**/*emphasis*, `inline code`) into terminal SGR using the
//      EXISTING `style::Style` palette (§14.3). No new colour mode / writer
//      target (R2). Degrades under `--no-color` via the `styled()` short-circuit.
//   3. `split_fences` + `render_agent_prose` route ```lisp / ```cranelisp fences
//      through the EXISTING `crate::pretty::pretty_print_str` (§14.4/14.5,
//      Principle-7 reuse — the same printer `/source` and `/sexp` use).
//
// §14.6 ANSI-leak ROOT CAUSE + FIX. Colour is a single global decision owned by
// `style::is_color_enabled()`; `style::styled()` is the ONLY styler and honours
// it. The leak the §17.13.3 repro pins is that today the model's raw markdown —
// including the raw ```lisp fence markers — is passed VERBATIM to `agent_prose`,
// which only gutters and never formats the body. So fences survive raw and any
// prose markdown passes through unrendered. The fix is "style ONCE at the leaf":
// `render_agent_prose` produces each run's final text exactly once (the markdown
// leaf OR the `pretty_print_str` leaf, both funnelling all SGR through
// `style::styled`), then `agent_prose` gutters the already-final body WITHOUT
// re-escaping it. No signature change to `pretty_print*`; no colour param (R2).

#![cfg(feature = "agent")]

use crate::style::{self, Style, styled};

/// The agent-input prompt token (§14.2). A pulled command (and, S89, a Build
/// submit) is echoed behind this prefix so the transcript reads honestly: who
/// typed what. It is DISTINCT from the human prompt and from the `▌` prose
/// gutter (commands are not prose — §17.2). When colour is on it is dim (it is a
/// prompt marker, like the human prompt); under `--no-color` it degrades to the
/// plain token via the `styled()` short-circuit. The trailing space separates it
/// from the echoed command text.
pub(crate) fn agent_input_prefix() -> String {
    format!("{} ", styled("agent>", Style::Dim))
}

/// A run of the model's markdown: literal prose, or a fenced lisp code block.
enum Run {
    /// Prose (formatted as terminal markdown, §14.3) — includes non-lisp fences,
    /// which render as literal blocks.
    Prose(String),
    /// A ```lisp / ```cranelisp fenced form — routed through `pretty_print_str`.
    Lisp(String),
}

/// The Cluster-A entry (§14.1). Splits the model's markdown into prose / lisp
/// runs (§14.4), formats prose runs as terminal markdown (§14.3), routes lisp
/// fences through `crate::pretty::pretty_print_str` (§14.5, Principle-7 reuse),
/// re-assembles, and wraps the whole in the `▌` agent frame via
/// `style::agent_prose`. This is the SINGLE styling site for prose (§14.6): each
/// run is styled exactly once at its leaf; `agent_prose` only gutters and never
/// re-escapes the body.
pub(crate) fn render_agent_prose(prose: &str) -> String {
    let mut body = String::new();
    for run in split_fences(prose) {
        match run {
            Run::Prose(text) => body.push_str(&markdown_to_terminal(&text)),
            Run::Lisp(code) => {
                let trimmed = code.trim_matches('\n');
                body.push_str(&crate::pretty::pretty_print_str(trimmed));
            }
        }
        if !body.ends_with('\n') {
            body.push('\n');
        }
    }
    // Drop a single trailing newline so `agent_prose` does not emit a blank
    // gutter line at the end (it gutters per `lines()`).
    if body.ends_with('\n') {
        body.pop();
    }
    style::agent_prose(&body)
}

/// Partition the prose into prose / lisp runs by ```` ``` ```` fences (§14.4).
/// A fence whose info-string is `lisp` or `cranelisp` becomes a `Run::Lisp`; any
/// other fence (e.g. ```` ```sh ````) stays prose and renders as a literal block.
fn split_fences(prose: &str) -> Vec<Run> {
    let mut runs: Vec<Run> = Vec::new();
    let mut prose_buf = String::new();
    // State while inside a fence: Some(is_lisp, body-accumulator).
    let mut fence: Option<(bool, String)> = None;

    for line in prose.lines() {
        let trimmed = line.trim_start();
        if let Some(info) = trimmed.strip_prefix("```") {
            match fence.take() {
                None => {
                    // Opening fence. Flush any pending prose first.
                    if !prose_buf.is_empty() {
                        runs.push(Run::Prose(std::mem::take(&mut prose_buf)));
                    }
                    let info = info.trim().to_ascii_lowercase();
                    let is_lisp = info == "lisp" || info == "cranelisp";
                    fence = Some((is_lisp, String::new()));
                }
                Some((is_lisp, code)) => {
                    // Closing fence.
                    if is_lisp {
                        runs.push(Run::Lisp(code));
                    } else {
                        // A non-lisp fence renders as a literal prose block.
                        runs.push(Run::Prose(code));
                    }
                }
            }
            continue;
        }
        match fence.as_mut() {
            Some((_, code)) => {
                code.push_str(line);
                code.push('\n');
            }
            None => {
                prose_buf.push_str(line);
                prose_buf.push('\n');
            }
        }
    }
    // Unterminated fence at EOF: treat the accumulated body per its kind.
    if let Some((is_lisp, code)) = fence.take() {
        if is_lisp {
            runs.push(Run::Lisp(code));
        } else {
            runs.push(Run::Prose(code));
        }
    }
    if !prose_buf.is_empty() {
        runs.push(Run::Prose(prose_buf));
    }
    runs
}

/// Format the common inline/block markdown the model emits into terminal SGR
/// using the EXISTING `style::Style` palette (§14.3). A bounded formatter
/// (Principle 6) — headings, bullet/numbered lists, `**bold**` / `*emphasis*` /
/// `_emphasis_`, and `` `inline code` `` — NOT a full CommonMark engine. Every
/// span flows through `style::styled`, so under `--no-color` it short-circuits to
/// plain text (markers stripped to their words), honouring the one global colour
/// gate (§14.6). The returned text carries NO `▌` gutter — `render_agent_prose`
/// adds that once, around the whole body.
fn markdown_to_terminal(run: &str) -> String {
    let mut out = String::new();
    for line in run.lines() {
        out.push_str(&format_md_line(line));
        out.push('\n');
    }
    out
}

/// Format a single markdown line: block-level prefix (heading / list) then the
/// inline spans.
fn format_md_line(line: &str) -> String {
    let trimmed = line.trim_start();

    // ATX heading: one-or-more leading `#`, then a space, then the text.
    if let Some(rest) = strip_heading(trimmed) {
        return styled(&format_inline(rest), Style::Bold);
    }

    // Bullet list item: `- ` / `* ` / `+ ` → a `•` bullet + inline spans.
    if let Some(rest) = strip_bullet(trimmed) {
        let indent = &line[..line.len() - trimmed.len()];
        return format!("{indent}  \u{2022} {}", format_inline(rest));
    }

    // Ordinary line (numbered lists keep their `N.` marker as plain text).
    format_inline(line)
}

/// If `s` is an ATX heading (`#`..`######` then a space), return the heading text.
fn strip_heading(s: &str) -> Option<&str> {
    let hashes = s.bytes().take_while(|&b| b == b'#').count();
    if (1..=6).contains(&hashes) {
        let rest = &s[hashes..];
        return rest.strip_prefix(' ').map(str::trim_end);
    }
    None
}

/// If `s` is a bullet list item (`- ` / `* ` / `+ `), return the item text.
fn strip_bullet(s: &str) -> Option<&str> {
    for marker in ["- ", "* ", "+ "] {
        if let Some(rest) = s.strip_prefix(marker) {
            return Some(rest);
        }
    }
    None
}

/// Format inline markdown spans: `**bold**`, `*emphasis*` / `_emphasis_`, and
/// `` `inline code` ``. Each styled span goes through `style::styled`, so the
/// markers are stripped (and re-styled, or not, per the colour gate) — they
/// NEVER survive as literal source into the output.
fn format_inline(text: &str) -> String {
    let mut out = String::new();
    let mut rest = text;
    while !rest.is_empty() {
        if let Some((before, span, kind, after)) = next_span(rest) {
            out.push_str(before);
            let style = match kind {
                SpanKind::Bold => Style::Bold,
                SpanKind::Emphasis => Style::Italic,
                SpanKind::Code => Style::Green,
            };
            out.push_str(&styled(span, style));
            rest = after;
        } else {
            out.push_str(rest);
            break;
        }
    }
    out
}

#[derive(Clone, Copy)]
enum SpanKind {
    Bold,
    Emphasis,
    Code,
}

/// Find the next inline span in `text`. Returns `(before, span_text, kind,
/// after)` for the first recognised delimiter pair, or `None` if there is no
/// complete span (so the remaining text is emitted verbatim).
fn next_span(text: &str) -> Option<(&str, &str, SpanKind, &str)> {
    // Ordered so `**` is tried before `*`.
    let delims: &[(&str, SpanKind)] = &[
        ("**", SpanKind::Bold),
        ("`", SpanKind::Code),
        ("*", SpanKind::Emphasis),
        ("_", SpanKind::Emphasis),
    ];
    // Pick the earliest-opening, completable span across all delimiters.
    let mut best: Option<(usize, usize, usize, SpanKind)> = None; // (open, close, dlen, kind)
    for (delim, kind) in delims {
        let dlen = delim.len();
        if let Some(open) = text.find(delim) {
            let after_open = open + dlen;
            if let Some(rel_close) = text[after_open..].find(delim) {
                let close = after_open + rel_close;
                if close > after_open {
                    let better = match &best {
                        Some((b_open, _, _, _)) => open < *b_open,
                        None => true,
                    };
                    if better {
                        best = Some((open, close, dlen, *kind));
                    }
                }
            }
        }
    }
    let (open, close, dlen, kind) = best?;
    let before = &text[..open];
    let span = &text[open + dlen..close];
    let after = &text[close + dlen..];
    Some((before, span, kind, after))
}

#[cfg(test)]
mod tests {
    use super::*;

    // §14.6 — the MANDATORY leaf-styling guard (the seam the e2e harness
    // structurally cannot reach: it pipes stdout ⇒ colour auto-off). Colour OFF:
    // a ```lisp fence routed through render_agent_prose contains NO literal
    // `\x1b`. (Colour-ON is exercised by `lisp_fence_color_on_emits_well_formed_sgr`
    // which sets the global gate; here the test process is a non-TTY so colour is
    // off by default.)
    #[test]
    fn lisp_fence_color_off_no_literal_escape() {
        let out = render_agent_prose(
            "Here is a definition:\n```lisp\n(defn double [x] (add-i64 x x))\n```",
        );
        assert!(
            !out.contains('\u{1b}'),
            "no literal ANSI escape under colour-off, got: {out:?}"
        );
        // The fence is pretty-printed, NOT echoed raw.
        assert!(!out.contains("```"), "raw fence must not survive: {out:?}");
        assert!(out.contains("double") && out.contains("add-i64"), "form rendered: {out:?}");
        // Framed.
        assert!(out.contains('\u{258c}'), "framed: {out:?}");
    }

    // §14.6 colour-ON leaf guard: when the global colour gate is ON, the render
    // path genuinely emits ANSI, AND every escape is a WELL-FORMED SGR sequence
    // (ESC immediately followed by `[`), never an orphan literal escape byte.
    // This pins the half the e2e harness structurally cannot reach (it pipes
    // stdout ⇒ colour auto-off). The colour gate is a process-wide OnceLock fed
    // by `is_terminal()` (always false in the non-TTY test process), so we use
    // the `#[cfg(test)]` force seam in `style.rs` to drive it ON for real — not
    // the vacuous `init_color(false)` which left colour OFF and made this guard
    // hold trivially with no ESC at all. nextest = one process per test ⇒ the
    // process-global force cannot race a sibling; the RAII guard restores it.
    #[test]
    fn lisp_fence_color_on_emits_well_formed_sgr() {
        let _guard = style::test_support::ColorGuard::force(true);
        assert!(
            style::is_color_enabled(),
            "the force seam must drive the gate ON, else this guard is vacuous"
        );
        let out = render_agent_prose(
            "Here is **bold** prose:\n```lisp\n(defn double [x] (add-i64 x x))\n```",
        );
        // The gate is ON ⇒ the render path MUST actually emit ANSI (the markdown
        // `**bold**` span and/or the pretty-printed fence). A vacuous guard would
        // produce zero escapes; this assertion makes the test bite.
        assert!(
            out.contains('\u{1b}'),
            "colour ON must emit at least one SGR escape: {out:?}"
        );
        // Every escape introduces a well-formed SGR (ESC '['), no orphan bytes.
        for (i, _) in out.match_indices('\u{1b}') {
            let after = &out[i + 1..];
            assert!(
                after.starts_with('['),
                "every ESC must introduce a well-formed SGR (ESC '['); orphan at {i}: {out:?}"
            );
        }
    }

    // §14.4 — split partitions prose and a lisp fence.
    #[test]
    fn split_fences_partitions_prose_and_lisp() {
        let runs = split_fences("before\n```lisp\n(+ 1 2)\n```\nafter");
        assert_eq!(runs.len(), 3);
        assert!(matches!(runs[0], Run::Prose(_)));
        assert!(matches!(runs[1], Run::Lisp(_)));
        assert!(matches!(runs[2], Run::Prose(_)));
        if let Run::Lisp(code) = &runs[1] {
            assert_eq!(code.trim(), "(+ 1 2)");
        }
    }

    // §14.4 — a non-lisp fence stays prose (literal block).
    #[test]
    fn split_fences_non_lisp_fence_is_prose() {
        let runs = split_fences("```sh\necho hi\n```");
        assert_eq!(runs.len(), 1);
        assert!(matches!(runs[0], Run::Prose(_)));
    }

    // §14.3 — markdown markers are stripped (no `##`, `**`, backticks survive)
    // under colour-off, and the text words survive.
    #[test]
    fn markdown_strips_markers_color_off() {
        let out = markdown_to_terminal("## Heading\nUse **defn** to define a `function`.");
        assert!(out.contains("Heading"), "heading text survives: {out:?}");
        assert!(out.contains("defn") && out.contains("function"), "words survive: {out:?}");
        assert!(
            !out.contains("##") && !out.contains("**") && !out.contains('`'),
            "raw markers must NOT survive: {out:?}"
        );
    }

    // §14.3 — a bullet list renders with a `•` marker, the `- ` source stripped.
    #[test]
    fn markdown_bullet_renders_glyph() {
        let out = markdown_to_terminal("- first point\n- second point");
        assert!(out.contains('\u{2022}'), "bullet glyph present: {out:?}");
        assert!(out.contains("first point") && out.contains("second point"), "{out:?}");
        // The literal `- ` list marker at line start must not survive.
        for line in out.lines() {
            assert!(!line.trim_start().starts_with("- "), "raw `- ` survived: {line:?}");
        }
    }

    // §14.2 — the agent-input prefix carries the `agent>` token (plain under
    // colour-off in the test process).
    #[test]
    fn agent_input_prefix_carries_token() {
        let p = agent_input_prefix();
        assert!(p.contains("agent>"), "prefix carries the glyph: {p:?}");
        // Colour off in tests ⇒ no escape.
        assert!(!p.contains('\u{1b}'), "no escape colour-off: {p:?}");
    }

    // The whole-prose render frames the body and strips markdown — no literal
    // escape under colour-off, gutter present.
    #[test]
    fn render_agent_prose_frames_and_formats() {
        let out = render_agent_prose("## Title\nsome **bold** prose");
        assert!(out.contains('\u{258c}'), "framed: {out:?}");
        assert!(out.contains("Title") && out.contains("bold"), "text survives: {out:?}");
        assert!(!out.contains("##") && !out.contains("**"), "markers stripped: {out:?}");
        assert!(!out.contains('\u{1b}'), "no escape colour-off: {out:?}");
    }
}
