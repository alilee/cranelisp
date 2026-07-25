// syntax — the `/syntax` topic-indexed core-language cheat-sheet
// (design/int/agent.md §22, repl/spec.md §17.17).
//
// A static, token-dense, verified-compiling, topic-keyed core-language syntax
// reference. The asset (`syntax/cheatsheet.txt`) is `/docs`-owned content
// (`user/syntax-cheatsheet-plan.md`); the UX is `/repl`-owned (`repl/spec.md
// §17.17`); this module is the int wiring: a pure, order-preserving delimiter
// parser over the embedded asset.
//
// NOT feature-gated: the `/syntax` command works in the default build (only the
// *agent pull* of it rides the `agent` feature). No state on `CompilerSession` —
// the parse is a one-shot static cache (`LazyLock`).

use std::sync::LazyLock;

/// The embedded cheat-sheet asset (`/docs`' content contract). Each topic block
/// is introduced by a line of the exact form `=== topic: <name> ===`.
const CHEATSHEET_SRC: &str = include_str!("syntax/cheatsheet.txt");

/// The topic delimiter prefix (`/docs`' machine contract). A delimiter line is
/// exactly `=== topic: <name> ===` (trimmed).
const TOPIC_PREFIX: &str = "=== topic:";
const TOPIC_SUFFIX: &str = "===";

/// A parsed cheat-sheet: an order-preserving list of `(topic-name, content)`
/// blocks. Built once, lazily, over the `include_str!` constant.
pub(crate) struct Cheatsheet {
    /// `(name, content)` in the asset's authored order (= the bare-`/syntax`
    /// index order — deterministic, no sort).
    topics: Vec<(String, String)>,
}

impl Cheatsheet {
    /// Parse the cheat-sheet asset by the `=== topic: <name> ===` delimiter.
    /// Order-preserving; the content of a topic is every line after its
    /// delimiter up to the next delimiter (or end of asset).
    fn parse(src: &str) -> Self {
        let mut topics: Vec<(String, String)> = Vec::new();
        let mut current: Option<(String, String)> = None;
        for line in src.lines() {
            if let Some(name) = parse_delimiter(line) {
                // Flush the previous block, then open a new one.
                if let Some((n, c)) = current.take() {
                    topics.push((n, c));
                }
                current = Some((name, String::new()));
            } else if let Some((_, content)) = current.as_mut() {
                content.push_str(line);
                content.push('\n');
            }
            // Lines before the first delimiter (a preamble, if any) are ignored.
        }
        if let Some((n, c)) = current.take() {
            topics.push((n, c));
        }
        Self { topics }
    }

    /// The bare-`/syntax` index: topic names in authored order.
    pub(crate) fn topic_names(&self) -> Vec<&str> {
        self.topics.iter().map(|(n, _)| n.as_str()).collect()
    }

    /// `/syntax <topic>` content lookup; `None` for an unknown topic.
    pub(crate) fn topic_content(&self, name: &str) -> Option<&str> {
        let name = name.trim();
        self.topics
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, c)| c.as_str())
    }
}

/// Parse a `=== topic: <name> ===` delimiter line, returning the trimmed
/// `<name>`. `None` for any non-delimiter line.
fn parse_delimiter(line: &str) -> Option<String> {
    let l = line.trim();
    let inner = l.strip_prefix(TOPIC_PREFIX)?;
    let inner = inner.strip_suffix(TOPIC_SUFFIX)?;
    Some(inner.trim().to_string())
}

/// The one-shot static cheat-sheet cache (the asset never changes at runtime).
static CHEATSHEET: LazyLock<Cheatsheet> = LazyLock::new(|| Cheatsheet::parse(CHEATSHEET_SRC));

/// Access the parsed cheat-sheet (lazily built, then shared).
pub(crate) fn cheatsheet() -> &'static Cheatsheet {
    &CHEATSHEET
}

/// Render the bare-`/syntax` topic index: the ordered topic names plus the
/// drill-in hint (`repl/spec.md §17.17.1`). Deterministic plain text — it
/// carries no ANSI escapes, so it degrades cleanly under `--no-color` with no
/// new style role. An optional `note` prefixes a short "no such topic" line
/// (the unknown-topic re-list, §17.17.1 — never a dead end).
pub(crate) fn render_index(note: Option<&str>) -> String {
    let cs = cheatsheet();
    let mut out = String::new();
    if let Some(n) = note {
        out.push_str("; ");
        out.push_str(n);
        out.push('\n');
    }
    out.push_str("; core-language syntax topics:\n");
    for name in cs.topic_names() {
        out.push_str(";   ");
        out.push_str(name);
        out.push('\n');
    }
    out.push_str("; Use /syntax <topic> for detail.");
    out
}

/// The `/syntax` command handler over the static cheat-sheet (`repl/spec.md
/// §17.17.1`). A free fn (no session state):
///   - bare (empty arg) → the topic-name index.
///   - `<topic>` (known) → the topic's dense content block.
///   - `<unknown>` → the index, prefixed with a short "no such topic" note
///     (self-documenting; never an opaque error).
pub(crate) fn handle_syntax(arg: &str) -> String {
    let topic = arg.trim();
    if topic.is_empty() {
        return render_index(None);
    }
    match cheatsheet().topic_content(topic) {
        Some(content) => content.trim_end().to_string(),
        None => render_index(Some(&format!(
            "no such syntax topic '{topic}' — one of these:"
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // The shipped asset must parse into multiple topics via the delimiter.
    #[test]
    fn parses_asset_into_topics() {
        let cs = cheatsheet();
        assert!(
            cs.topic_names().len() >= 2,
            "the asset must declare multiple topics; got {:?}",
            cs.topic_names()
        );
    }

    // The parser splits on `=== topic: <name> ===` and trims the name.
    #[test]
    fn delimiter_split_keys_by_trimmed_name() {
        let src = "=== topic:  alpha  ===\nTOPIC alpha\nbody-a\n\
                   === topic: beta ===\nTOPIC beta\nbody-b\n";
        let cs = Cheatsheet::parse(src);
        assert_eq!(cs.topic_names(), vec!["alpha", "beta"]);
        assert!(cs.topic_content("alpha").unwrap().contains("body-a"));
        assert!(cs.topic_content("beta").unwrap().contains("body-b"));
    }

    // Index derivation preserves the asset's authored order (no sort).
    #[test]
    fn index_preserves_authored_order() {
        let src = "=== topic: zebra ===\nTOPIC zebra\n\
                   === topic: apple ===\nTOPIC apple\n";
        let cs = Cheatsheet::parse(src);
        // Authored order is zebra-then-apple, NOT alphabetical.
        assert_eq!(cs.topic_names(), vec!["zebra", "apple"]);
    }

    // A topic's content is every line after its delimiter up to the next.
    #[test]
    fn content_spans_to_next_delimiter() {
        let src = "=== topic: one ===\nline1\nline2\n=== topic: two ===\nline3\n";
        let cs = Cheatsheet::parse(src);
        let one = cs.topic_content("one").unwrap();
        assert!(one.contains("line1") && one.contains("line2"));
        assert!(
            !one.contains("line3"),
            "content must not bleed past the next delimiter"
        );
    }

    // Lines before the first delimiter (a preamble) are ignored, not crashed on.
    #[test]
    fn preamble_before_first_delimiter_is_ignored() {
        let src = "preamble line\n=== topic: a ===\nTOPIC a\nbody\n";
        let cs = Cheatsheet::parse(src);
        assert_eq!(cs.topic_names(), vec!["a"]);
    }

    // Unknown-topic lookup returns None (the re-list arm).
    #[test]
    fn unknown_topic_lookup_is_none() {
        let cs = cheatsheet();
        assert!(cs.topic_content("no-such-topic-xyzzy").is_none());
    }

    // The shipped asset includes a `match` topic with a SPEC cross-link.
    #[test]
    fn shipped_match_topic_has_content() {
        let content = handle_syntax("match");
        assert!(content.contains("TOPIC match"), "content={content}");
        assert!(content.contains("SPEC"), "content={content}");
    }

    // Bare `/syntax` lists the topic index + the drill-in hint, with no ANSI.
    #[test]
    fn bare_index_lists_topics_and_hint() {
        let out = handle_syntax("");
        let cs = cheatsheet();
        for name in cs.topic_names() {
            assert!(out.contains(name), "index must list {name:?}; out={out}");
        }
        assert!(
            out.contains("/syntax") && out.contains("topic"),
            "out={out}"
        );
        assert!(
            !out.contains('\u{1b}'),
            "index must carry no ANSI escape; out={out}"
        );
    }

    // Unknown topic re-lists the index with a "no such topic" note (never a
    // dead-end error).
    #[test]
    fn unknown_topic_relists_with_note() {
        let out = handle_syntax("no-such-topic-xyzzy");
        let cs = cheatsheet();
        assert!(out.contains(cs.topic_names()[0]), "must re-list; out={out}");
        assert!(
            out.contains("no such syntax topic"),
            "must note the miss; out={out}"
        );
        assert!(
            !out.to_lowercase().contains("unknown command"),
            "not a dead end; out={out}"
        );
    }
}
