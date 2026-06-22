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
    let mut out = String::new();
    for line in text.lines() {
        out.push_str(&styled(AGENT_GUTTER, Style::BrightMagenta));
        out.push(' ');
        out.push_str(line);
        out.push('\n');
    }
    // An empty body still produces a single gutter line so the frame is visible.
    if out.is_empty() {
        out.push_str(&styled(AGENT_GUTTER, Style::BrightMagenta));
        out.push('\n');
    }
    out
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

    #[test]
    fn styled_with_color_disabled_returns_plain_text() {
        // Since OnceLock may not be initialized, and tests run with
        // stdout not being a TTY, colour should be disabled.
        let result = styled("hello", Style::Bold);
        // In test context (not a TTY), should be plain text.
        assert_eq!(result, "hello");
    }
}
