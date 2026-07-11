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
//   3. The `StreamingRenderer` (+ its one-delta wrapper `render_agent_prose`)
//      route ```lisp / ```cranelisp fences through the EXISTING
//      `crate::pretty::pretty_print_str` (§14.4/14.5, Principle-7 reuse — the same
//      printer `/source` and `/sexp` use).
//
// §14A.3 (0555) single render core. `render_agent_prose` (the single-shot
// reference renderer) and the LIVE streaming path (`agent_turn` → `StreamingRenderer`)
// are the SAME state machine driven at different delta granularity, so the §17.22
// differential invariant (streamed-concatenated == single-shot) holds BY
// CONSTRUCTION. `push_prose_run` / `push_lisp_block` are the shared leaves;
// `classify_fence_line` is the single fence classifier.
//
// §14.6 ANSI-leak ROOT CAUSE + FIX. Colour is a single global decision owned by
// `style::is_color_enabled()`; `style::styled()` is the ONLY styler and honours
// it. The leak the §17.13.3 repro pins is that the model's raw markdown —
// including the raw ```lisp fence markers — was passed VERBATIM to `agent_prose`,
// which only gutters and never formats the body. So fences survived raw and any
// prose markdown passed through unrendered. The fix is "style ONCE at the leaf":
// each leaf produces its final text exactly once (the markdown leaf OR the
// `pretty_print_str` leaf, both funnelling all SGR through `style::styled`); a
// ```lisp block is emitted un-guttered (§14A.2, 0556) and every prose line is
// guttered via `agent_prose`. No signature change to `pretty_print*`; no colour
// param (R2).

#![cfg(feature = "agent")]

use std::io::Write;

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

/// The single-shot reference renderer (§14.1 / §14A.2). Renders a COMPLETE model
/// answer to terminal bytes: prose runs are markdown-formatted (§14.3) and
/// guttered via `style::agent_prose`; a ```lisp / ```cranelisp fence is
/// pretty-printed (§14.5, Principle-7 reuse) and emitted **un-guttered** so it
/// copy-pastes clean (§17.2 item 3 / §17.13.2 / §14A.2, FIXME 0556). This is the
/// SINGLE styling site for prose (§14.6): each run is styled exactly once at its
/// leaf, so a ```lisp block is byte-identical (colour-off) to `pretty_print_str`
/// for the same form.
///
/// §14A.3 (0555) unification: `render_agent_prose` is expressed AS a one-delta
/// drive of the very same `StreamingRenderer` the live streaming path uses, so
/// the §17.22 differential invariant (streamed-concatenated == single-shot) holds
/// BY CONSTRUCTION — there is literally one render core, not two that must agree
/// (Principle 7 / Principle 18). Production rendering no longer calls this — the
/// terminal answer streams live through `StreamingRenderer` (§14A.3 S4) — so it is
/// retained test-gated as the invariant's comparand (the /qa + /dev oracle).
#[cfg(test)]
pub(crate) fn render_agent_prose(prose: &str) -> String {
    let mut out: Vec<u8> = Vec::new();
    let mut renderer = StreamingRenderer::new();
    renderer.push(prose, &mut out);
    renderer.finish(&mut out);
    String::from_utf8(out).unwrap_or_default()
}

/// Emit a prose run **guttered** (§14A.2): markdown-format it (§14.3), then wrap
/// each line in the `▌` frame via `style::agent_prose` (unchanged prose
/// behaviour). A run that is empty OR whitespace-only contributes nothing —
/// `agent_prose` frames an empty body with one lone `▌` gutter line by design, so
/// a fence at buffer start, two adjacent fences, or a spaces-only line would
/// otherwise emit a stray gutter. The whitespace-only guard (`trim`, not
/// `trim_matches('\n')`) closes the spaces-only-run gap (0556 /review Minor #1).
fn push_prose_run(out: &mut dyn Write, text: &str) {
    let formatted = markdown_to_terminal(text);
    if formatted.trim().is_empty() {
        return;
    }
    let _ = out.write_all(style::agent_prose(&formatted).as_bytes());
}

/// Emit a lisp fence **un-guttered** (§14A.2 — the 0556 fix): the pretty-printed
/// form carries NO `▌` gutter on any code line, and its bytes are byte-identical
/// (colour-off) to `crate::pretty::pretty_print_str` — the same printer `/sexp`
/// and `/source` use — for that form, with nothing prepended to any line. A
/// multi-line selection over the block therefore pastes clean and re-runs
/// verbatim. The trailing newline separates the block from the following run.
fn push_lisp_block(out: &mut dyn Write, code: &str) {
    let _ = out.write_all(crate::pretty::pretty_print_str(code.trim_matches('\n')).as_bytes());
    let _ = out.write_all(b"\n");
}

/// Classify a single line as a ```` ``` ```` fence marker (§14.4). Returns
/// `Some(is_lisp)` when the line's first non-whitespace token is a fence marker
/// (`is_lisp` = its info-string is `lisp`/`cranelisp`), `None` for a non-fence
/// line. The SINGLE fence classifier (Principle 7) — `StreamingRenderer` is its
/// only consumer; the `is_lisp` flag is meaningful only on an OPENING fence (a
/// closing fence carries no info-string and reuses the open's stored flag).
fn classify_fence_line(line: &str) -> Option<bool> {
    line.trim_start().strip_prefix("```").map(|info| {
        let info = info.trim().to_ascii_lowercase();
        info == "lisp" || info == "cranelisp"
    })
}

/// The incremental agent-output render state machine (§14A.3, 0555). Consumes raw
/// markdown deltas and emits rendered bytes to `out` line by line: complete prose
/// lines gutter + format LIVE (§17.22 line-granular); a ```lisp fence body is
/// buffered while open and flushed whole — formatted + un-guttered — at
/// fence-close (a fence cannot stream token-by-token: the pretty-printer needs the
/// whole form, §17.22 / §3.11). Two states: outside-fence (`fence.is_none()`) and
/// inside-fence (`fence.is_some()`).
///
/// Byte-identity with `render_agent_prose` is STRUCTURAL: `process_line` reuses
/// the SAME `push_prose_run` / `push_lisp_block` leaves and the SAME
/// `classify_fence_line` predicate, and the line buffer reassembles complete lines
/// regardless of where delta boundaries fall (mid-line or mid-fence). So
/// concatenating everything a turn streams equals the single-shot render of its
/// full text (§17.22 differential invariant, by construction).
pub(crate) struct StreamingRenderer {
    /// The partial trailing line not yet terminated by `\n` (withheld until it is
    /// — §17.22 line-granular streaming).
    line_buf: String,
    /// `Some((is_lisp, body))` ⇒ inside an open fence, buffering its body.
    fence: Option<(bool, String)>,
}

impl StreamingRenderer {
    pub(crate) fn new() -> Self {
        Self {
            line_buf: String::new(),
            fence: None,
        }
    }

    /// Feed one raw model delta. Appends to the line buffer and flushes every
    /// COMPLETE line (the partial trailing line waits for its newline).
    pub(crate) fn push(&mut self, delta: &str, out: &mut dyn Write) {
        self.line_buf.push_str(delta);
        while let Some(nl) = self.line_buf.find('\n') {
            let mut line: String = self.line_buf.drain(..=nl).collect();
            line.pop(); // drop the trailing '\n'
            self.process_line(&line, out);
        }
    }

    /// Process one COMPLETE line: toggle fence state on a fence marker, else
    /// buffer it (inside a fence) or gutter + format it live (outside).
    fn process_line(&mut self, line: &str, out: &mut dyn Write) {
        if let Some(open_is_lisp) = classify_fence_line(line) {
            match self.fence.take() {
                // OPEN — emit nothing; start buffering the body.
                None => self.fence = Some((open_is_lisp, String::new())),
                // CLOSE — flush the buffered body per its (opening) kind.
                Some((is_lisp, body)) => {
                    if is_lisp {
                        push_lisp_block(out, &body);
                    } else {
                        // A non-lisp fence (e.g. ```sh) renders as a literal prose block.
                        push_prose_run(out, &body);
                    }
                }
            }
        } else {
            match self.fence.as_mut() {
                // INSIDE a fence — buffer, no echo (the pretty-printer needs the whole form).
                Some((_, body)) => {
                    body.push_str(line);
                    body.push('\n');
                }
                // OUTSIDE — gutter + format this one prose line LIVE. `push_prose_run`
                // over a single `line\n` equals its share of a whole-run render
                // (both `markdown_to_terminal` and `agent_prose` are line-independent).
                None => {
                    let mut run = String::with_capacity(line.len() + 1);
                    run.push_str(line);
                    run.push('\n');
                    push_prose_run(out, &run);
                }
            }
        }
    }

    /// End of the turn's stream: flush a partial trailing line, then an
    /// unterminated fence at EOF (treated per its kind — matching the old
    /// `split_fences` EOF behaviour).
    pub(crate) fn finish(&mut self, out: &mut dyn Write) {
        if !self.line_buf.is_empty() {
            let line = std::mem::take(&mut self.line_buf);
            self.process_line(&line, out);
        }
        if let Some((is_lisp, body)) = self.fence.take() {
            if is_lisp {
                push_lisp_block(out, &body);
            } else {
                push_prose_run(out, &body);
            }
        }
    }
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

    // §14.4 — a non-lisp fence (```sh) renders as guttered prose (its markers
    // stripped, body NOT pretty-printed) — the old `split_fences` literal-block
    // behaviour, now via the single render core.
    #[test]
    fn non_lisp_fence_renders_as_guttered_prose() {
        let out = render_agent_prose("```sh\necho hi\n```");
        assert!(!out.contains("```"), "fence markers stripped: {out:?}");
        assert!(
            out.lines()
                .any(|l| l.contains("echo hi") && l.starts_with('\u{258c}')),
            "an sh fence body renders as guttered prose, not pretty-printed: {out:?}"
        );
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
    // escape under colour-off, gutter present. (Pure-prose input: every line is
    // guttered — the §14A.2 code-vs-prose split does not affect a fence-free run.)
    #[test]
    fn render_agent_prose_frames_and_formats() {
        let out = render_agent_prose("## Title\nsome **bold** prose");
        assert!(out.contains('\u{258c}'), "framed: {out:?}");
        assert!(out.contains("Title") && out.contains("bold"), "text survives: {out:?}");
        assert!(!out.contains("##") && !out.contains("**"), "markers stripped: {out:?}");
        assert!(!out.contains('\u{1b}'), "no escape colour-off: {out:?}");
        // Every non-empty line carries the gutter (there is no code run here).
        for line in out.lines() {
            assert!(
                line.starts_with('\u{258c}'),
                "pure-prose lines are all guttered: {line:?}"
            );
        }
    }

    // §14A.2 / §17.2 item 3 (FIXME 0556) — a ```lisp fence run renders with NO
    // `▌` gutter on any code line, and is byte-identical (colour-off) to
    // `pretty_print_str` for that form; the surrounding prose keeps its gutter.
    #[test]
    fn lisp_fence_code_lines_are_ungutter_and_byte_identical() {
        let out = render_agent_prose(
            "Here is a definition:\n```lisp\n(defn double [x] (add-i64 x x))\n```",
        );
        // The prose line is guttered (the split is code-only).
        assert!(
            out.lines()
                .any(|l| l.contains("Here is a definition") && l.starts_with('\u{258c}')),
            "prose line keeps its gutter: {out:?}"
        );
        // No code line carries the gutter — identify code lines by the code-only
        // token `add-i64` (never in the prose).
        assert!(
            !out.lines().any(|l| l.contains("add-i64") && l.contains('\u{258c}')),
            "code lines MUST be un-guttered (`▌`-free): {out:?}"
        );
        // Byte parity: every pretty-printer line for the form appears VERBATIM
        // (gutter-free, full-line) in the rendered block.
        let expect = crate::pretty::pretty_print_str("(defn double [x] (add-i64 x x))");
        for pl in expect.lines() {
            assert!(
                out.lines().any(|ol| ol == pl),
                "pretty-printer line {pl:?} MUST appear verbatim (nothing prepended) in: {out:?}"
            );
        }
    }

    // §14A.2 — a prose → ```lisp → prose sequence gutters the two prose halves
    // and leaves the code un-guttered (the code-only split).
    #[test]
    fn prose_fence_prose_gutters_only_the_prose() {
        let out = render_agent_prose(
            "Before the block.\n```lisp\n(add-i64 1 2)\n```\nAfter the block.",
        );
        assert!(
            out.lines()
                .any(|l| l.contains("Before the block") && l.starts_with('\u{258c}')),
            "leading prose guttered: {out:?}"
        );
        assert!(
            out.lines()
                .any(|l| l.contains("After the block") && l.starts_with('\u{258c}')),
            "trailing prose guttered: {out:?}"
        );
        assert!(
            !out.lines().any(|l| l.contains("add-i64") && l.contains('\u{258c}')),
            "code line un-guttered: {out:?}"
        );
    }

    // §14A.2 empty-run hygiene — a fence at buffer start (leading empty prose
    // run) emits no stray gutter-only line before the code.
    #[test]
    fn leading_fence_emits_no_stray_gutter_line() {
        let out = render_agent_prose("```lisp\n(add-i64 1 2)\n```");
        // No line is a bare gutter (gutter followed only by optional trailing
        // whitespace) — the empty prose run before the fence is guarded away.
        assert!(
            !out.lines().any(|l| l.trim_end() == "\u{258c}"),
            "no stray gutter-only line from an empty prose run: {out:?}"
        );
        // The code still rendered, un-guttered.
        assert!(
            out.lines().any(|l| l.contains("add-i64") && !l.contains('\u{258c}')),
            "code rendered un-guttered: {out:?}"
        );
    }

    // -----------------------------------------------------------------------
    // §14A.3 / §17.22 (FIXME 0555) — streaming render tests. The load-bearing
    // guard is the DIFFERENTIAL INVARIANT: whatever the `StreamingRenderer` emits
    // across arbitrary delta boundaries, concatenated, MUST equal the single-shot
    // `render_agent_prose` of the full text (colour-off). Because the two are the
    // SAME render core (render_agent_prose IS a one-delta drive of the renderer),
    // this pins the exact property at risk — partial-line / partial-fence buffering.
    // -----------------------------------------------------------------------

    /// Drive the `StreamingRenderer` with an ordered list of deltas, returning the
    /// concatenated rendered bytes as a `String`.
    fn stream_render(deltas: &[&str]) -> String {
        let mut out: Vec<u8> = Vec::new();
        let mut r = StreamingRenderer::new();
        for d in deltas {
            r.push(d, &mut out);
        }
        r.finish(&mut out);
        String::from_utf8(out).unwrap()
    }

    // §17.22 THE differential invariant (MUST): the streamed-then-concatenated
    // output is byte-identical to `render_agent_prose` over the same complete text,
    // for EVERY split boundary — including mid-line, mid-fence, and mid-span. The
    // fixture carries prose, a bullet list, and a ```lisp fence (the interesting
    // cases). ASCII ⇒ every byte index is a char boundary.
    #[test]
    fn streaming_concatenation_is_byte_identical_to_single_shot() {
        let full = "Here is the plan:\n\
                    - step one\n\
                    - step two\n\
                    ```lisp\n\
                    (defn double [x] (add-i64 x x))\n\
                    ```\n\
                    That defines it.";
        let reference = render_agent_prose(full);

        // Every two-way split at an arbitrary byte boundary must match.
        for split in 1..full.len() {
            let (a, b) = full.split_at(split);
            assert_eq!(
                stream_render(&[a, b]),
                reference,
                "a stream split at byte {split} must equal the single-shot render"
            );
        }

        // And the finest granularity: one character (= one delta) at a time.
        let mut out: Vec<u8> = Vec::new();
        let mut r = StreamingRenderer::new();
        for ch in full.chars() {
            r.push(&ch.to_string(), &mut out);
        }
        r.finish(&mut out);
        assert_eq!(
            String::from_utf8(out).unwrap(),
            reference,
            "a char-by-char stream must equal the single-shot render"
        );
    }

    // §17.22 — a ```lisp fence split across TWO deltas still flushes ONE whole
    // pretty-printed, un-guttered block at fence-close (never a raw half-fence).
    #[test]
    fn fence_split_across_deltas_flushes_one_whole_block() {
        let full = "```lisp\n(defn double [x] (add-i64 x x))\n```";
        let whole = stream_render(&[full]);
        // Split INSIDE the fence body (mid-form).
        let split = stream_render(&["```lisp\n(defn double [x]", " (add-i64 x x))\n```"]);
        assert_eq!(split, whole, "a fence split mid-body renders identically");
        assert_eq!(whole, render_agent_prose(full), "and equals the single-shot render");
        assert!(!whole.contains('\u{258c}'), "the fence block is un-guttered: {whole:?}");
        assert!(!whole.contains("```"), "no raw fence marker survives: {whole:?}");
        // Byte parity with the pretty-printer for the whole form.
        for pl in crate::pretty::pretty_print_str("(defn double [x] (add-i64 x x))").lines() {
            assert!(
                whole.lines().any(|ol| ol == pl),
                "pretty-printer line {pl:?} must appear verbatim: {whole:?}"
            );
        }
    }

    // §17.22 — a single prose line delivered across TWO deltas gutters EXACTLY
    // ONCE (the partial trailing line is withheld until its newline), not twice.
    #[test]
    fn prose_line_split_across_deltas_yields_one_gutter_line() {
        let out = stream_render(&["hello ", "world\n"]);
        let gutter_lines = out.lines().filter(|l| l.starts_with('\u{258c}')).count();
        assert_eq!(gutter_lines, 1, "one reassembled prose line ⇒ one gutter line: {out:?}");
        assert!(out.contains("hello world"), "the line reassembled: {out:?}");
        // Identical to the single-shot render of the reassembled text.
        assert_eq!(out, render_agent_prose("hello world"));
    }

    // §14.6 leaf guard over the STREAMING path: colour-off, a multi-delta answer
    // with a fence carries NO literal `\x1b` and no raw ```` ``` ```` marker.
    #[test]
    fn streaming_no_literal_escape_color_off() {
        let out = stream_render(&["Here is ", "**bold**\n```lisp\n", "(add-i64 1 2)\n```"]);
        assert!(!out.contains('\u{1b}'), "no ANSI escape under colour-off: {out:?}");
        assert!(!out.contains("```"), "no raw fence marker survives: {out:?}");
        assert!(out.contains("add-i64"), "the form rendered: {out:?}");
        assert!(out.contains('\u{258c}'), "prose is framed: {out:?}");
    }

    // §17.22 — an unterminated fence at end-of-stream still flushes its buffered
    // body formatted at `finish` (never left raw in the buffer).
    #[test]
    fn unterminated_fence_flushes_at_finish() {
        let out = stream_render(&["```lisp\n(add-i64 1 2)"]);
        assert!(out.contains("add-i64"), "the buffered fence body flushed: {out:?}");
        assert!(!out.contains("```"), "no raw fence marker: {out:?}");
        assert_eq!(out, render_agent_prose("```lisp\n(add-i64 1 2)"));
    }
}
