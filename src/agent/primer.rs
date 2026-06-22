// agent/primer.rs — the always-on language primer (design/int/agent.md §7).
//
// Cranelisp is private — the model has ZERO of it in training
// (`repl-embedded-agent.md §6`), so the primer is mandatory grounding, not
// optional. It is a curated, distilled block of core syntax, the special forms,
// the `:Type` convention, the prelude surface, and canonical few-shot idioms
// (incl. the constrained-`(defn … Num …)` idiom the acceptance walk-through
// needs, §10). Human-curatable, version-controlled as a companion `.txt` asset
// (§7.1). Telemetry-driven curation is agentic-Phase-3 (R5, out of MVP scope).

#![cfg(feature = "agent")]

/// The always-on language primer, embedded at build time (§7.1). Included in
/// EVERY request as system content (`request.rs`), so the model is grounded in
/// Cranelisp on every turn regardless of what the harvest carries.
pub const LANGUAGE_PRIMER: &str = include_str!("primer.txt");

/// Borrow the primer text. A function (not just the const) so the call site
/// reads as an assembly step and the asset source stays swappable.
pub fn language_primer() -> &'static str {
    LANGUAGE_PRIMER
}

#[cfg(test)]
mod tests {
    use super::*;

    // S89 Phase-6: the always-on primer must instruct Build/Document mode, not
    // the stale S88 read-only framing. The scripted stub can't catch this — it
    // is scripted to emit `tool: submit` regardless of what the model is told;
    // this asserts the live model is INSTRUCTED to act, not merely propose.

    #[test]
    fn primer_instructs_build_mode_submit() {
        // The Build write capability (`submit`) must be named so the model
        // acts rather than telling the user to copy-paste a form.
        assert!(
            LANGUAGE_PRIMER.contains("submit"),
            "primer must mention the `submit` Build write tool"
        );
    }

    #[test]
    fn primer_instructs_document_mode_set_preamble() {
        // The Document write capability (`set-preamble`) must be named.
        assert!(
            LANGUAGE_PRIMER.contains("set-preamble"),
            "primer must mention the `set-preamble` Document write tool"
        );
    }

    #[test]
    fn primer_instructs_lisp_fence_convention() {
        // Multi-line code shown in prose must be fenced ```lisp so the REPL
        // pretty-printer (repl/spec.md §17.13.2) renders it.
        assert!(
            LANGUAGE_PRIMER.contains("```lisp"),
            "primer must instruct the ```lisp fenced-code convention"
        );
    }

    #[test]
    fn primer_has_no_stale_read_only_framing() {
        // Regression guard: the S88 read-only paragraph told the model NOT to
        // submit. Its presence is the live defect this fix removes.
        for stale in ["READ-ONLY", "cannot submit", "for the user to copy"] {
            assert!(
                !LANGUAGE_PRIMER.contains(stale),
                "primer still contains stale S88 read-only framing: {stale:?}"
            );
        }
    }
}
