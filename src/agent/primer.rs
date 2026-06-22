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
    fn primer_steers_off_clojure_recur_idiom() {
        // S89 Phase-6: the model was burning its validator-repair cap
        // translating mainstream-Lisp idioms (`recur`, `zero?`, `dec`) that
        // don't exist in Cranelisp. The primer must name `recur` in a "don't"
        // context so the steering can't silently regress.
        assert!(
            LANGUAGE_PRIMER.contains("NO `recur`"),
            "primer must steer the model off Clojure/CL `recur` (use self-recursion)"
        );
    }

    #[test]
    fn primer_has_multi_signature_defn_form() {
        // S89 Phase-6: asked for multi-dispatch, the model proposed two
        // clashing single-clause `defn`s instead of Cranelisp's real
        // multi-clause shape (spec/05-definitions.md §5.1.2). The primer must
        // carry the multi-signature `([params] body)` variant form so the
        // steering can't silently regress.
        assert!(
            LANGUAGE_PRIMER.contains("multi-signature"),
            "primer must name the multi-signature defn form"
        );
        assert!(
            LANGUAGE_PRIMER.contains("([p] b) ([p q] b)"),
            "primer must show the multi-clause variant syntax `([params] body)`"
        );
    }

    #[test]
    fn primer_favours_tail_recursion_tco() {
        // S89 Phase-6: the model wrote a NON-tail-recursive accumulator by
        // default (recursive call as a call ARGUMENT). Cranelisp guarantees
        // TCO (spec/12-runtime.md §12.5), so the primer must steer toward the
        // tail-recursive accumulator form (recursive call in tail position).
        assert!(
            LANGUAGE_PRIMER.contains("PREFER TAIL RECURSION"),
            "primer must steer the model toward tail recursion"
        );
        assert!(
            LANGUAGE_PRIMER.contains("TCO"),
            "primer must name TCO (tail-call optimization guarantee)"
        );
        assert!(
            LANGUAGE_PRIMER.contains("tail-recursive accumulator"),
            "primer must carry the canonical tail-recursive accumulator idiom"
        );
    }

    #[test]
    fn primer_has_recursion_idiom() {
        // The grounded few-shot recursive example (verified to type-check as
        // `(Fn [Int] Int)`, `(fib 10) = 55`) must be present so the model has
        // an idiomatic Cranelisp recursion to pattern-match against.
        assert!(
            LANGUAGE_PRIMER.contains("(defn fib [n]"),
            "primer must carry the canonical recursive-function idiom"
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
