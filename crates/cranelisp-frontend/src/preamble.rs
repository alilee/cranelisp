//! Module-preamble capture (spec `spec/08-modules.md §8.16`).
//!
//! A **module preamble** is the contiguous leading line-comment block at the
//! head of a `.cl` source file — module-level documentation, the module
//! analogue of a `defn` docstring (§5.12). This module implements the
//! frontend's slice of §8.16: a **pure** capture function that recognizes the
//! leading comment block, strips its comment markers, joins the lines, and
//! returns the stored preamble text (or `None`).
//!
//! # Why a dedicated line scan (Shape A)
//!
//! The implementation is a direct, line-oriented scan over the raw source
//! head — deliberately **not** layered on the `Sexp::Comment` stream produced
//! by [`crate::parse_preserving_comments`]. Per the design
//! (`design/frontend/module-preamble.md` §2.2/§2.3), the one subtlety of the
//! §8.16 boundary rule is the **blank-line break**: the reader's
//! whitespace-skipping silently consumes blank lines between comments, so two
//! `Sexp::Comment` nodes separated by a blank line are indistinguishable in
//! the stream from two adjacent comment lines. A physical-line scan works in
//! the same lexical units (lines) the spec's boundary rule is written in, so
//! the blank-line rule is encoded where it is least error-prone, and the
//! capture cannot be perturbed by reader changes to comment positioning.
//!
//! The function performs **no** symbol-table mutation and **no** I/O — it is a
//! pure `&str -> Option<String>`, unit-testable from a source string with no
//! session (frontend's syntactic-only posture;
//! `design/frontend/s76-syntactic-only.md`; Principle 5 — testability is
//! structural).

/// Capture the leading comment-block module preamble per spec
/// [`§8.16`](https://github.com/alilee/cranelisp/blob/main/spec/08-modules.md).
///
/// Returns the joined, marker-stripped preamble text, or `None` when the
/// source has no contiguous leading comment block (the common, valid case).
///
/// # Boundary rule (§8.16.1)
///
/// The preamble is the contiguous block of line comments that **begins on the
/// first line of the file** and runs up to (but not including) the first form,
/// terminated by the first of:
///
/// - a **blank line** (whitespace-only) — comments below the blank line are
///   ordinary, never preamble;
/// - the **first non-comment form** — comments after the first form are never
///   preamble;
/// - **EOF** — a file that is only a comment block (the whole block is the
///   preamble).
///
/// A file whose first non-whitespace line is **not** a `;` comment has no
/// preamble (`None`). Per the design's strict default
/// (`design/frontend/module-preamble.md` §2.4), a leading **blank line** before
/// the comment run also yields `None`: the block must begin on line 1.
///
/// # Text extraction (§8.16.2)
///
/// For each captured comment line: strip the leading comment marker — the
/// maximal run of `;` that forms the marker, i.e. `;;` if present else a
/// single `;` — then strip **one** immediately-following space if present.
/// (`;; Sudoku` → `Sudoku`; `;;Sudoku` → `Sudoku`; a bare `;;` → `""`.)
/// Interior whitespace beyond that one space is content and is preserved. The
/// stripped lines are joined with a single `\n`, with no trailing newline.
///
/// Pure: no symbol-table mutation, no I/O.
#[must_use]
pub fn capture_module_preamble(source: &str) -> Option<String> {
    let mut captured: Vec<&str> = Vec::new();

    // Physical-line scan from byte 0. `split_inclusive('\n')` keeps each line's
    // trailing newline so a final line without one is still a line; we trim the
    // line ending per-line below.
    for raw_line in source.split_inclusive('\n') {
        let line = raw_line.strip_suffix('\n').unwrap_or(raw_line);
        let line = line.strip_suffix('\r').unwrap_or(line);

        let trimmed = line.trim_start();

        if trimmed.is_empty() {
            // Blank line: terminates the run. If the run is empty (a blank line
            // before any comment, including a leading blank line on line 1),
            // there is no preamble per the strict default (§2.4).
            break;
        }

        if trimmed.starts_with(';') {
            captured.push(line);
        } else {
            // First non-comment, non-blank line is a form-start: terminates.
            break;
        }
    }

    if captured.is_empty() {
        return None;
    }

    let stored: Vec<String> = captured.iter().map(|line| strip_marker(line)).collect();
    Some(stored.join("\n"))
}

/// Strip the comment marker and one following space from a single comment line.
///
/// The marker is the maximal leading run of `;` that forms the comment marker:
/// `;;` if present, else a single `;`. After the marker, one immediately
/// following space is stripped if present. No further whitespace is stripped —
/// interior alignment after that one space is content (§8.16.2).
fn strip_marker(line: &str) -> String {
    // Leading whitespace before the marker is not content (the line was
    // classified by its first non-whitespace char being `;`).
    let trimmed = line.trim_start();

    // Strip the maximal run of leading `;` markers: `;;` if present, else `;`.
    let after_semis = trimmed.trim_start_matches(';');

    // Strip exactly one immediately-following space, if present.
    after_semis
        .strip_prefix(' ')
        .unwrap_or(after_semis)
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    // spec: spec/08-modules.md §8.16.1 — leading ;; block above (mod …) is captured
    #[test]
    fn block_above_mod_captured() {
        let src = ";; doc\n(mod m)\n";
        assert_eq!(capture_module_preamble(src), Some("doc".to_string()));
    }

    // spec: spec/08-modules.md §8.16.1 — blank line breaks the block; only the
    // pre-blank run is the preamble.
    #[test]
    fn blank_line_terminates_block() {
        let src = ";; doc\n\n;; section\n(mod m)\n";
        assert_eq!(capture_module_preamble(src), Some("doc".to_string()));
    }

    // spec: spec/08-modules.md §8.16.1 — comments after the first form are never
    // preamble.
    #[test]
    fn comment_after_first_form_is_none() {
        let src = "(defn f [] 0)\n;; not preamble\n";
        assert_eq!(capture_module_preamble(src), None);
    }

    // spec: spec/08-modules.md §8.16.1 — a leading comment that follows a form
    // (even with intervening blank) is not preamble.
    #[test]
    fn comment_below_first_form_after_blank_is_none() {
        let src = "(defn f [] 0)\n\n;; b\n";
        assert_eq!(capture_module_preamble(src), None);
    }

    // spec: spec/08-modules.md §8.16.2 — no leading comment block ⇒ None.
    #[test]
    fn no_leading_comment_is_none() {
        let src = "(defn f [] 0)\n";
        assert_eq!(capture_module_preamble(src), None);
    }

    // spec: spec/08-modules.md §8.16.1 — empty file has no preamble.
    #[test]
    fn empty_file_is_none() {
        assert_eq!(capture_module_preamble(""), None);
    }

    // spec: spec/08-modules.md §8.16.1 — strict default: a leading blank line
    // before the comment run ⇒ None (the block must begin on line 1).
    #[test]
    fn leading_blank_line_is_none() {
        let src = "\n;; doc\n(mod m)\n";
        assert_eq!(capture_module_preamble(src), None);
    }

    // spec: spec/08-modules.md §8.16.1 — multiple leading blank lines ⇒ None.
    #[test]
    fn multiple_leading_blank_lines_is_none() {
        let src = "\n\n;; doc\n(mod m)\n";
        assert_eq!(capture_module_preamble(src), None);
    }

    // spec: spec/08-modules.md §8.16.1 — EOF terminates a file that is only a
    // comment block; the whole block is the preamble.
    #[test]
    fn eof_terminates_comment_only_file() {
        let src = ";; doc\n;; more";
        assert_eq!(capture_module_preamble(src), Some("doc\nmore".to_string()));
    }

    // spec: spec/08-modules.md §8.16.2 — multi-line join preserves internal
    // line breaks with a single interior newline.
    #[test]
    fn multi_line_join_preserves_breaks() {
        let src = ";; line1\n;; line2\n(mod m)\n";
        assert_eq!(
            capture_module_preamble(src),
            Some("line1\nline2".to_string())
        );
    }

    // spec: spec/08-modules.md §8.16.2 — single-`;` marker is stripped (with one
    // following space).
    #[test]
    fn single_semicolon_marker_stripped() {
        let src = "; doc\n(mod m)\n";
        assert_eq!(capture_module_preamble(src), Some("doc".to_string()));
    }

    // spec: spec/08-modules.md §8.16.2 — `;;` double marker is stripped (with one
    // following space).
    #[test]
    fn double_semicolon_marker_stripped() {
        let src = ";; doc\n(mod m)\n";
        assert_eq!(capture_module_preamble(src), Some("doc".to_string()));
    }

    // spec: spec/08-modules.md §8.16.2 — no space after marker: marker stripped,
    // no content lost.
    #[test]
    fn marker_without_following_space() {
        let src = ";;Sudoku\n(mod m)\n";
        assert_eq!(capture_module_preamble(src), Some("Sudoku".to_string()));
    }

    // spec: spec/08-modules.md §8.16.2 — a bare `;;` line contributes the empty
    // string.
    #[test]
    fn bare_marker_yields_empty_string() {
        let src = ";; first\n;;\n;; third\n(mod m)\n";
        assert_eq!(
            capture_module_preamble(src),
            Some("first\n\nthird".to_string())
        );
    }

    // spec: spec/08-modules.md §8.16.2 — only ONE following space is stripped;
    // further indentation is preserved content.
    #[test]
    fn only_one_following_space_stripped() {
        let src = ";;   indented\n(mod m)\n";
        assert_eq!(capture_module_preamble(src), Some("  indented".to_string()));
    }

    // spec: spec/08-modules.md §8.16.1 — the first non-comment form terminates
    // the block regardless of what comment lines follow it (worked: a/b case).
    #[test]
    fn first_form_terminates_then_later_comment_ignored() {
        let src = ";; a\n(defn f [] 0)\n;; b\n";
        assert_eq!(capture_module_preamble(src), Some("a".to_string()));
    }

    // spec: spec/08-modules.md §8.16.1 — the spec's worked Sudoku example.
    #[test]
    fn sudoku_worked_example() {
        let src = ";; Sudoku solver: constraint propagation +\n\
                   ;; backtracking over a Vec-backed grid.\n\
                   (mod solver)\n\
                   (import [collections.vec [conj]])\n";
        assert_eq!(
            capture_module_preamble(src),
            Some(
                "Sudoku solver: constraint propagation +\nbacktracking over a Vec-backed grid."
                    .to_string()
            )
        );
    }
}
