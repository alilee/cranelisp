// Terminal styling primitives.
//
// Layer 1 of the terminal styling system (design/int/terminal-styling.md).
// Provides a Style enum and styled() function for ANSI SGR escape sequences.
// TTY detection determines whether styling is enabled.

use std::sync::OnceLock;

/// ANSI style for a text span.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Style {
    /// Bold (SGR 1) — head position atoms, category headers, error keyword.
    Bold,
    /// Dim (SGR 2) — prompt, banner.
    Dim,
    /// Italic (SGR 3) — comments.
    Italic,
    /// Cyan (SGR 36) — type annotations (:Type).
    Cyan,
    /// Yellow (SGR 33) — integer, float, boolean literals; warning detail.
    Yellow,
    /// Green (SGR 32) — string literals.
    Green,
    /// Red (SGR 31) — error detail.
    Red,
    /// Bold Red (SGR 1;31) — error keyword.
    BoldRed,
    /// Bold Yellow (SGR 1;33) — warning keyword.
    BoldYellow,
    /// Bright Magenta (SGR 95) — the embedded-agent prose-frame gutter
    /// (`repl/spec.md §10.3` "Agent prose frame" role). Reserved exclusively for
    /// the agent's *prose* gutter marker; agent-issued commands + their results
    /// use their normal deterministic roles (§17.2). [S88]
    BrightMagenta,
}

impl Style {
    /// Return the SGR code string for this style.
    fn sgr_code(self) -> &'static str {
        match self {
            Style::Bold => "1",
            Style::Dim => "2",
            Style::Italic => "3",
            Style::Cyan => "36",
            Style::Yellow => "33",
            Style::Green => "32",
            Style::Red => "31",
            Style::BoldRed => "1;31",
            Style::BoldYellow => "1;33",
            Style::BrightMagenta => "95",
        }
    }
}

/// The agent prose-frame gutter marker (`repl/spec.md §10.3`, §17.2): a left
/// gutter `▌` prefixing each prose line.
const AGENT_GUTTER: &str = "\u{258c}"; // ▌ (U+258C LEFT FIVE EIGHTHS BLOCK)

/// Render agent *prose* in the reserved frame (`repl/spec.md §17.2`, §10.3).
///
/// Each prose line is prefixed with the `▌` gutter marker; when colour is
/// enabled the gutter is bright magenta (the body stays default). The frame
/// degrades gracefully: under `--no-color`, `NO_COLOR`, or a non-TTY (§10.1)
/// the gutter is still emitted as a plain-text prefix (so prose remains
/// visually distinguishable in piped output) but with no SGR codes — this is
/// the `styled()` short-circuit. The returned string ends with a newline.
///
/// WAVE-2 SCOPE: only the role/definition exists; the agent does not emit prose
/// until Wave 3. The frame applies ONLY to the agent's own words — agent-issued
/// commands and their results render in normal deterministic REPL style (§17.2)
/// and MUST NOT pass through here.
pub fn agent_prose(text: &str) -> String {
    use crate::styled::{Role, StyledDoc, render};
    let mut doc = StyledDoc::new();
    for line in text.lines() {
        doc.push(Role::AgentGutter, AGENT_GUTTER);
        doc.plain(" ");
        doc.plain(line);
        doc.plain("\n");
    }
    // An empty body still produces a single gutter line so the frame is visible.
    if text.lines().next().is_none() {
        doc.push(Role::AgentGutter, AGENT_GUTTER);
        doc.plain("\n");
    }
    render(&doc)
}

/// Render a REPL `Error: {message}` line through the §10.3 seam — R8 bold-red
/// `Error:` keyword + R9 red detail. Colour-off the bytes are `Error: {message}`,
/// byte-identical to the pre-Wave-D plain line (the non-TTY error contract).
pub fn error_line(message: &str) -> String {
    use crate::styled::{Role, StyledDoc, render};
    let mut doc = StyledDoc::new();
    doc.push(Role::ErrorKeyword, "Error:");
    doc.plain(" ");
    doc.push(Role::ErrorDetail, message.to_string());
    render(&doc)
}

/// Render a REPL structured-metadata `;` line (R6 dim) through the §10.3 seam —
/// e.g. the `; search index complete.` lifecycle note (FIXME 0561: REPL metadata
/// is dim, distinct from an italic source comment). Colour-off byte-identical.
pub fn repl_metadata_line(text: &str) -> String {
    use crate::styled::{Role, StyledDoc, render};
    render(&StyledDoc::span(Role::ReplMetadata, text.to_string()))
}

static COLOR_ENABLED: OnceLock<bool> = OnceLock::new();

/// Initialize colour detection. Must be called once at startup
/// with the parsed --no-color flag value.
pub fn init_color(no_color_flag: bool) {
    let enabled = detect_color(no_color_flag);
    let _ = COLOR_ENABLED.set(enabled);
}

/// Query whether colour output is enabled.
pub fn is_color_enabled() -> bool {
    // Test-only force seam: when a test has forced the colour gate (ON or OFF),
    // honour that over the `is_terminal()` auto-detect — the test process is a
    // non-TTY, so `COLOR_ENABLED` would otherwise always resolve OFF and the
    // colour-ON code paths (well-formed SGR) would be unreachable from a unit
    // test. nextest runs each test in its own process, so a process-global force
    // in one test cannot race another. This seam is `#[cfg(test)]`-only — the
    // production path below is byte-identical to the release binary.
    #[cfg(test)]
    if let Some(forced) = test_support::forced_color() {
        return forced;
    }
    *COLOR_ENABLED.get().unwrap_or(&false)
}

/// Detect whether colour should be enabled.
///
/// Priority order (spec section 10.1):
/// 1. --no-color flag (highest)
/// 2. NO_COLOR env var (any non-empty value suppresses)
/// 3. TTY check on stdout
/// 4. Otherwise: enabled
fn detect_color(no_color_flag: bool) -> bool {
    // 1. --no-color flag takes highest priority.
    if no_color_flag {
        return false;
    }
    // 2. NO_COLOR env var (any non-empty value suppresses).
    if let Ok(val) = std::env::var("NO_COLOR")
        && !val.is_empty()
    {
        return false;
    }
    // 3. TTY check on stdout.
    use std::io::IsTerminal;
    if !std::io::stdout().is_terminal() {
        return false;
    }
    // 4. Otherwise: enabled.
    true
}

/// Strip ANSI SGR escape sequences (`ESC [ … m`) from a string, leaving clean
/// plain text. Used where a styled REPL render must be fed to a NON-terminal
/// consumer that mangles or cannot interpret SGR — notably the embedded agent's
/// model feed (`agent/pull.rs`): a captured `/source`/`/sig`/… result is styled
/// when colour is on, and shipping the raw SGR to the model leaks mangled
/// `1m`/`0m` fragments back into the displayed reply (the ESC byte is dropped in
/// transport, leaving the bare `[`-less code). Stripping at the membrane keeps
/// the model's copy clean plain text while the user echo keeps its (well-formed)
/// colour on a TTY.
///
/// Robust to a truncated/orphan escape: a lone `ESC` (or `ESC [` without a
/// terminating `m`) is dropped along with the bytes up to end-of-string, so no
/// `\x1b`-fragment survives. Only the CSI-SGR form (`ESC [ params m`) is
/// recognised — the only sequence `styled` emits.
pub fn strip_ansi(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\x1b' {
            // A CSI sequence is `ESC [ <params> <final>`. Consume the optional
            // `[` introducer FIRST (it is itself in the `@`..`~` range, so it
            // must NOT be mistaken for the final byte), then the parameter run up
            // to and INCLUDING the final byte (`@`..`~`, e.g. `m` for an SGR), or
            // to end-of-string if the sequence is truncated.
            if chars.peek() == Some(&'[') {
                chars.next();
            }
            for d in chars.by_ref() {
                // The CSI final byte is in `@`..`~` (`m` for SGR).
                if ('@'..='~').contains(&d) {
                    break;
                }
            }
        } else {
            out.push(c);
        }
    }
    out
}

/// Wrap text in ANSI escape sequences for the given style.
///
/// When colour is disabled (via TTY detection), returns text unchanged.
/// Every styled span is self-contained with its own reset.
pub fn styled(text: &str, style: Style) -> String {
    if !is_color_enabled() {
        return text.to_string();
    }
    format!("\x1b[{}m{}\x1b[0m", style.sgr_code(), text)
}

/// Test-only colour-gate override seam (`#[cfg(test)]`).
///
/// The production gate is a `OnceLock<bool>` driven by `is_terminal()` — which
/// is always `false` in the (non-TTY) test process, so the colour-ON code paths
/// are otherwise unreachable from a unit test. `force_color(Some(true))` pins the
/// gate ON for the current process (nextest = one process per test ⇒ no
/// cross-test race); `force_color(None)` clears it. `is_color_enabled` consults
/// this before the real `OnceLock`. This module does NOT exist in a non-test
/// build, so the release binary's colour logic is byte-identical.
#[cfg(test)]
pub(crate) mod test_support {
    use std::sync::atomic::{AtomicU8, Ordering};

    // 0 = unset (fall through to the real OnceLock), 1 = forced OFF, 2 = forced ON.
    static FORCE: AtomicU8 = AtomicU8::new(0);

    /// Read the forced colour gate, if any. `None` ⇒ no force.
    pub(crate) fn forced_color() -> Option<bool> {
        match FORCE.load(Ordering::Relaxed) {
            1 => Some(false),
            2 => Some(true),
            _ => None,
        }
    }

    /// Force the colour gate to a value (`Some(true/false)`), or clear the force
    /// (`None`) so detection falls back to the real `OnceLock` auto-detect.
    pub(crate) fn force_color(value: Option<bool>) {
        let code = match value {
            None => 0,
            Some(false) => 1,
            Some(true) => 2,
        };
        FORCE.store(code, Ordering::Relaxed);
    }

    /// RAII guard that forces the colour gate and restores it on drop, so a test
    /// that forces colour ON cannot leak that state to a sibling test sharing the
    /// process (defensive — under nextest each test is its own process anyway).
    pub(crate) struct ColorGuard;

    impl ColorGuard {
        pub(crate) fn force(value: bool) -> Self {
            force_color(Some(value));
            ColorGuard
        }
    }

    impl Drop for ColorGuard {
        fn drop(&mut self) {
            force_color(None);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detect_color_no_color_flag() {
        assert!(!detect_color(true));
    }

    #[test]
    fn sgr_codes_are_correct() {
        assert_eq!(Style::Bold.sgr_code(), "1");
        assert_eq!(Style::Dim.sgr_code(), "2");
        assert_eq!(Style::Italic.sgr_code(), "3");
        assert_eq!(Style::Cyan.sgr_code(), "36");
        assert_eq!(Style::Yellow.sgr_code(), "33");
        assert_eq!(Style::Green.sgr_code(), "32");
        assert_eq!(Style::Red.sgr_code(), "31");
        assert_eq!(Style::BoldRed.sgr_code(), "1;31");
        assert_eq!(Style::BoldYellow.sgr_code(), "1;33");
        assert_eq!(Style::BrightMagenta.sgr_code(), "95");
    }

    // spec: repl/spec.md §17.2 — agent prose renders in the `▌`-gutter frame,
    // degrading to a plain-text gutter (no SGR) when colour is disabled (the
    // test process is not a TTY, so colour is off).
    #[test]
    fn agent_prose_gutters_each_line_plain_when_no_color() {
        let out = agent_prose("hello\nworld");
        assert_eq!(out, "\u{258c} hello\n\u{258c} world\n");
        // No SGR escapes when colour is disabled.
        assert!(!out.contains('\u{1b}'), "no ANSI codes expected: {out:?}");
    }

    // spec: repl/spec.md §17.2 — an empty prose body still emits a visible frame.
    #[test]
    fn agent_prose_empty_body_still_framed() {
        let out = agent_prose("");
        assert_eq!(out, "\u{258c}\n");
    }

    // The `#[cfg(test)]` colour-force seam overrides the non-TTY auto-detect.
    // Forcing ON makes `styled` emit a well-formed SGR; clearing restores the
    // non-TTY default (plain text). nextest = one process per test ⇒ no race.
    #[test]
    fn test_color_force_seam_toggles_gate() {
        // Default (non-TTY test process): colour off.
        assert!(!is_color_enabled());
        {
            let _g = test_support::ColorGuard::force(true);
            assert!(is_color_enabled(), "force(true) enables the gate");
            assert_eq!(styled("x", Style::Bold), "\x1b[1mx\x1b[0m");
        }
        // Guard dropped ⇒ force cleared ⇒ back to non-TTY default.
        assert!(!is_color_enabled(), "force cleared after guard drop");
        {
            let _g = test_support::ColorGuard::force(false);
            assert!(!is_color_enabled(), "force(false) disables the gate");
            assert_eq!(styled("x", Style::Bold), "x");
        }
    }

    // strip_ansi removes well-formed SGR sequences, leaving clean plain text —
    // and is robust to a truncated/orphan escape (no `\x1b`-fragment survives).
    #[test]
    fn strip_ansi_removes_sgr_and_handles_orphans() {
        // Well-formed SGR (what `styled` emits) is fully removed.
        assert_eq!(strip_ansi("\x1b[1mdefn\x1b[0m"), "defn");
        assert_eq!(
            strip_ansi("(\x1b[1mdefn\x1b[0m f [x] (\x1b[1mprimitives/add-i64\x1b[0m x x))"),
            "(defn f [x] (primitives/add-i64 x x))"
        );
        // Plain text passes through unchanged.
        assert_eq!(strip_ansi("(defn f [x] x)"), "(defn f [x] x)");
        // A truncated escape at EOF leaves no fragment.
        assert_eq!(strip_ansi("hello\x1b[1m"), "hello");
        assert_eq!(strip_ansi("hello\x1b"), "hello");
        // No `1m`/`0m` literal fragment survives, and no ESC byte remains.
        let out = strip_ansi("\x1b[1mx\x1b[0m");
        assert!(!out.contains('\u{1b}') && !out.contains("1m") && !out.contains("0m"));
    }

    // === §10.3 colour-ON byte-exact fixtures (Wave-D /dev obligation) =========

    // K8 — an error line: `Error:` is R8 bold-red, the detail R9 red.
    // spec: repl/spec.md §10.3 R8/R9 — error line.
    #[test]
    fn colour_on_k8_error_line() {
        let _g = test_support::ColorGuard::force(true);
        assert_eq!(
            error_line("undefined variable: foo"),
            "\x1b[1;31mError:\x1b[0m \x1b[31mundefined variable: foo\x1b[0m"
        );
    }

    // K8 colour-off: byte-identical to the plain `Error: …` line (non-TTY contract).
    #[test]
    fn colour_off_k8_error_line_is_plain() {
        let _g = test_support::ColorGuard::force(false);
        assert_eq!(
            error_line("undefined variable: foo"),
            "Error: undefined variable: foo"
        );
    }

    // K12 — the `; search index complete.` lifecycle note is R6 dim (FIXME 0561
    // resolves REPL metadata to dim, NOT the italic it used pre-Wave-D).
    // spec: repl/spec.md §10.3 R6 — lifecycle metadata note (0561 metadata half).
    #[test]
    fn colour_on_k12_lifecycle_note_dim() {
        let _g = test_support::ColorGuard::force(true);
        assert_eq!(
            repl_metadata_line("; search index complete."),
            "\x1b[2m; search index complete.\x1b[0m"
        );
    }

    // K10 — the startup banner is R13 dim (Prompt / Banner). This is the exact
    // doc `print_banner` renders.
    // spec: repl/spec.md §10.3 R13 — banner.
    #[test]
    fn colour_on_k10_banner_dim() {
        use crate::styled::{Role, StyledDoc, render};
        let _g = test_support::ColorGuard::force(true);
        let banner = render(&StyledDoc::span(
            Role::Prompt,
            "cranelisp REPL — type /help for help",
        ));
        assert_eq!(banner, "\x1b[2mcranelisp REPL — type /help for help\x1b[0m");
    }

    // K13 — the agent prose gutter `▌` is R14 bright magenta; the prose body is
    // Plain (§10.3 R14). The gutter mechanism is unchanged by Wave D (P9) but now
    // routes through the ONE render.
    // spec: repl/spec.md §10.3 R14 / §17.2 — agent prose frame.
    #[test]
    fn colour_on_k13_agent_gutter_bright_magenta() {
        let _g = test_support::ColorGuard::force(true);
        assert_eq!(agent_prose("hello"), "\x1b[95m\u{258c}\x1b[0m hello\n");
    }

    #[test]
    fn styled_with_color_disabled_returns_plain_text() {
        // Since OnceLock may not be initialized, and tests run with
        // stdout not being a TTY, colour should be disabled.
        let result = styled("hello", Style::Bold);
        // In test context (not a TTY), should be plain text.
        assert_eq!(result, "hello");
    }
}
