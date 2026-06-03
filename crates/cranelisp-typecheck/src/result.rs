//! Typecheck result types. Relocated from `cranelisp-types` per FIXME 0100
//! Phase 1 — single-consumer types live with their originating crate
//! (Principle 15). `CheckResult` originates in
//! `cranelisp-typecheck` and is consumed only by `int` downstream.
//!
//! `CheckError` (FIXME 0098 Phase 1) is the typed error returned by
//! `check_forms`; its `Gap(ResolutionGap)` arm is the integration-layer
//! pattern-match target for the gap-orchestration retry loop.

use cranelisp_types::{
    DisplayInfo, ErrorLocation, ResolutionGap, ResolveError, Warning,
};

/// Transient REPL/display payload assembled during `check_forms`.
///
/// NOT a boundary type — the durable typecheck output lives on `SymbolTable`
/// entries' `ast`, `scheme`, `callees`, `got_slot`, and `trait_origin` fields.
/// This struct carries only diagnostics and optional REPL display payload.
#[derive(Debug, Clone)]
pub struct CheckResult {
    /// Non-fatal warnings accumulated during checking.
    pub warnings: Vec<Warning>,
    /// Display info for REPL output (None in batch / module-load mode).
    pub display: Option<DisplayInfo>,
}

/// Typed error returned by `cranelisp_typecheck::check_forms`. Per
/// FIXME 0098 Phase 1: the integration-layer `process_cluster` pattern-matches
/// on `CheckError::Gap` to dispatch the gap-orchestration retry loop.
///
/// The `Gap` carrier is a `cranelisp_types::ResolutionGap` — a multi-consumer
/// boundary type retained in `cranelisp-types` per Principle 15 (originated by
/// both frontend and typecheck, consumed by `int`).
#[non_exhaustive]
#[derive(Debug, Clone)]
pub enum CheckError {
    /// Cross-cutting "this dependency isn't ready yet" signal.
    Gap(ResolutionGap),
    /// Conventional type error — message + location.
    TypeError {
        message: String,
        location: ErrorLocation,
    },
}

impl std::fmt::Display for CheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CheckError::Gap(g) => write!(f, "resolution gap: {g:?}"),
            CheckError::TypeError { message, location } => {
                write!(f, "type error at {}: {message}", location.span)
            }
        }
    }
}

impl std::error::Error for CheckError {}

/// Projection of the types-owned [`cranelisp_types::ResolveError`] into the
/// typecheck-owned [`CheckError`].
///
/// `CheckError` is typecheck-owned (single-consumer per Principle 15), so the
/// projection *into* it lives with the crate that owns the target — even
/// though the `ResolveError` it projects from is now a `cranelisp-types`
/// boundary type (relocated at S76, the W-Macro fold-in). The projection is a
/// thin re-projection of the same message + location the types crate's
/// `From<ResolveError> for CranelispError` produces (both read
/// `ResolveError::message()` / `ResolveError::span()`), so the two never drift.
impl From<ResolveError> for CheckError {
    fn from(e: ResolveError) -> CheckError {
        CheckError::TypeError {
            message: e.message(),
            location: ErrorLocation::from_span(e.span()),
        }
    }
}
