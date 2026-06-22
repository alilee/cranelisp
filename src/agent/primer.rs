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
