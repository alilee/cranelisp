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
        }
    }
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
