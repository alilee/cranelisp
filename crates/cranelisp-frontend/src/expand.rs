//! `ExpansionError` — typed error returned by frontend's macro expansion.
//!
//! Per FIXME 0098 Phase 2: the integration layer's `process_form` pattern-
//! matches on `ExpansionError::Gap(ResolutionGap)` to dispatch the gap-
//! orchestration retry loop. Other variants surface malformed macro syntax
//! and macro-body aborts.
//!
//! S66 Wave 2 Step 3 lands the type as a precondition for the Wave 3a
//! triad — frontend's full `expand` migration (today: lives at
//! `src/expander.rs::expand_sexp_recursive`) lands together with
//! typecheck's `check_form` shape pivot and int's `process_form` shape
//! pivot. This file authors the type so Wave 3a's wiring work is unblocked.

use cranelisp_types::{FQSymbol, ResolutionGap, Span};

/// Typed error returned by macro expansion.
///
/// `Gap(ResolutionGap)` is the dominant variant during Wave 3a's
/// gap-orchestration loop: when expansion needs an in-mem macro that
/// has not yet been JIT'd, it returns `Gap(ResolutionGap::MacroInMem)`
/// and `int::process_form` priority-boosts that fq + waits.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub enum ExpansionError {
    /// Cross-cutting "this dependency isn't ready yet" — typically
    /// `ResolutionGap::MacroInMem(fq)` from frontend's expand path.
    Gap(ResolutionGap),
    /// Macro syntax malformed (bad params, malformed body, etc.).
    Malformed { message: String, span: Span },
    /// Macro body raised an error during expansion (panic in clause body,
    /// type-failed clause).
    MacroAborted {
        fq: FQSymbol,
        message: String,
        span: Span,
    },
}

impl std::fmt::Display for ExpansionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExpansionError::Gap(g) => write!(f, "expansion gap: {g:?}"),
            ExpansionError::Malformed { message, span } => {
                write!(f, "malformed macro at {span}: {message}")
            }
            ExpansionError::MacroAborted { fq, message, span } => {
                write!(f, "macro `{fq:?}` aborted at {span}: {message}")
            }
        }
    }
}

impl std::error::Error for ExpansionError {}
