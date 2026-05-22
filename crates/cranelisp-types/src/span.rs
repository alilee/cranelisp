use serde::{Deserialize, Serialize};

/// Byte range in source text. Carried on every AST node and every error.
///
/// `Default` derives to `Span { start: 0, end: 0 }` — structurally identical
/// to `Span::SYNTHETIC`. Useful for `#[serde(default)]` on newly-added span
/// fields where the on-disk cache pre-dates the field (e.g. `FieldDef::span`,
/// added Submission 25 per Decision 39 per-field-span arc).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub const SYNTHETIC: Span = Span { start: 0, end: 0 };

    pub fn new(start: u32, end: u32) -> Self {
        Span { start, end }
    }

    pub fn merge(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}
