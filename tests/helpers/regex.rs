//! Named regex library. Tests reference the helper, never embed the
//! raw pattern. Discipline rule: every check that matches compiler
//! output uses a helper from first occurrence (see
//! `tests/plan/helpers.md` §"Regex helper library").
//!
//! When the compiler's output format changes, ONE place updates and
//! every dependent test moves with it.

#![allow(dead_code)]

use once_cell::sync::Lazy;
use regex::Regex;

/// Compiler-output regexes. Each has documented capture groups.
pub mod compiler {
    use super::*;

    /// `/time` line. Matches: `elapsed: 1.234 ms` (or `µs`, `s`).
    /// Captures: (1) value, (2) unit.
    pub fn time_line() -> &'static Regex {
        static RE: Lazy<Regex> = Lazy::new(|| {
            Regex::new(r"(?m)^elapsed:\s+(\d+(?:\.\d+)?)\s+(ms|µs|s)\s*$").unwrap()
        });
        &RE
    }

    /// REPL prompt line — `<module> ` (no value).
    /// Captures: (1) module name.
    pub fn repl_prompt() -> &'static Regex {
        static RE: Lazy<Regex> =
            Lazy::new(|| Regex::new(r"(?m)^([a-zA-Z][a-zA-Z0-9._-]*)\s+$").unwrap());
        &RE
    }

    /// Compiler error: `error: <msg> at <file>:<line>:<col>`.
    /// Captures: (1) msg, (2) file, (3) line, (4) col.
    pub fn error_line() -> &'static Regex {
        static RE: Lazy<Regex> = Lazy::new(|| {
            Regex::new(r"(?m)^error:\s+(.+?)\s+at\s+([^:]+):(\d+):(\d+)\s*$").unwrap()
        });
        &RE
    }

    /// Hex pointer (any width). For golden masking out alloc addresses.
    /// Captures: (1) the hex literal.
    pub fn alloc_addr() -> &'static Regex {
        static RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"\b0x[0-9a-fA-F]+\b").unwrap());
        &RE
    }

    /// The per-turn timing stamp inside the REPL prompt: `NN+NNms`.
    /// For golden masking (the only nondeterministic bytes in a piped REPL
    /// transcript) and for answer-line prompt stripping (L-N1,
    /// tests/display_exact.rs).
    pub fn prompt_timing() -> &'static Regex {
        static RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"\d+\+\d+ms").unwrap());
        &RE
    }

    /// A full REPL prompt fragment (`NN+NNms; <module>> `), possibly
    /// repeated — prompts for input-only turns are emitted inline before the
    /// next answer line. For answer-line extraction (L-N1).
    pub fn prompt_fragment() -> &'static Regex {
        static RE: Lazy<Regex> =
            Lazy::new(|| Regex::new(r"(\d+\+\d+ms; [a-zA-Z][a-zA-Z0-9._-]*> )+").unwrap());
        &RE
    }
}

// =============================================================================
// Convenience masking primitives
// =============================================================================

/// Replace every hex pointer in `s` with `<ADDR>`.
pub fn mask_alloc_addrs(s: &str) -> String {
    compiler::alloc_addr().replace_all(s, "<ADDR>").into_owned()
}

/// Replace every `/time`-style line in `s` with `<TIME>`.
pub fn mask_timing(s: &str) -> String {
    compiler::time_line().replace_all(s, "<TIME>").into_owned()
}
