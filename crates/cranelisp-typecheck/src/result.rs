//! Typecheck result types. Relocated from `cranelisp-types` per FIXME 0100
//! Phase 1 — single-consumer types live with their originating crate
//! (Principle 15). `CheckResult` originates in
//! `cranelisp-typecheck` and is consumed only by `int` downstream.
//!
//! `CheckError` (FIXME 0098 Phase 1) is the typed error returned by
//! `check_forms`; its `Gap(ResolutionGap)` arm is the integration-layer
//! pattern-match target for the gap-orchestration retry loop.

use cranelisp_types::{
    DisplayInfo, ErrorLocation, ResolutionGap, ResolveError, Span, Symbol, Warning,
};

/// Why a return-type-polymorphic dispatch site is still unresolved at finalize
/// (`design/typecheck/return-poly-dispatch-signal.md` §5). Typecheck-local — no
/// `cranelisp-types` home, no cache-schema bump (the set is EMPTY for every
/// valid program, so nothing worth caching crosses the boundary).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DispatchGap {
    /// A nullary `Self`-returning trait method (`(zed)` with `zed [] self`)
    /// whose return-directed dispatch never selected an impl — no argument, no
    /// disambiguating context (spec §3.11, R16).
    ReturnTypePoly,
    /// The same unresolved return dispatch under a value-position trait
    /// CONSTRAINT (`:Zeroable (zed)`): the constraint is a satisfaction check,
    /// not a concrete type, so it does not disambiguate (spec §3.11, R17).
    ValuePositionConstraint,
}

/// A return-type-polymorphic dispatch site that remained UNRESOLVED after the
/// final substitution — its return-directed dispatch never selected an impl
/// (`dispatch.rs::method_return_dispatch_type` still `None`) and its
/// discriminating type is still a free `Type::Var`. Grounded in the dispatch
/// OUTCOME, not surface-type concreteness, so it is immune to the `(add2 3 4)`
/// false positive (an arg-directed dispatch resolves its impl and is never in
/// this set). See `design/typecheck/return-poly-dispatch-signal.md` §3.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnresolvedDispatchSite {
    /// The call site's span.
    pub span: Span,
    /// The unresolved trait method's name (`zed`).
    pub method: Symbol,
    /// Why it is unresolved (R16 vs R17).
    pub gap: DispatchGap,
}

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
    /// Return-type-polymorphic dispatch sites still UNRESOLVED at finalize
    /// (`design/typecheck/return-poly-dispatch-signal.md`; carrier (A), 0611
    /// ratified — `design/arch/bounded-contexts.md` §2). EMPTY for every valid
    /// program. int applies it at the ONE entry/eval-boundary it owns — the
    /// REPL `__expr` eval path and `src/exe.rs::validate_main` — emitting the
    /// §3.11 ambiguity error instead of letting the residual leak to the
    /// backend GOT-slot path (Principle 19: typecheck carries no entry
    /// designation, so it records the signal; int applies it).
    pub unresolved_dispatch: Vec<UnresolvedDispatchSite>,
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
