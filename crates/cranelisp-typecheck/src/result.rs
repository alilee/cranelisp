//! Typecheck result types. Relocated from `cranelisp-types` per FIXME 0100
//! Phase 1 — single-consumer types live with their originating crate
//! (Principle 15). `CheckResult` and `ReplSnapshot` originate in
//! `cranelisp-typecheck` and are consumed only by `int` downstream.
//!
//! `CheckError` (FIXME 0098 Phase 1) is the typed error returned by
//! `check_form`; its `Gap(ResolutionGap)` arm is the integration-layer
//! pattern-match target for the gap-orchestration retry loop.

use std::collections::HashSet;

use cranelisp_types::{DisplayInfo, ErrorLocation, ResolutionGap, Symbol, TypeId, Warning};

/// Transient output of `TypeChecker::check`.
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

/// Snapshot of typechecker state for REPL error recovery.
///
/// Before processing each REPL input, the typechecker takes a snapshot.
/// If type checking or codegen fails, the snapshot is restored so the
/// session remains in a consistent state.
///
/// The typechecker owns the snapshot/restore mechanism. The binary crate
/// calls `snapshot()` before and `restore()` on error. Fields are opaque
/// to the binary crate.
#[derive(Debug, Clone)]
pub struct ReplSnapshot {
    /// Next type variable ID at snapshot time
    pub next_type_id: TypeId,
    /// Symbol keys present in the current module's symbol table at snapshot time.
    /// On restore, any keys not in this set are removed.
    pub symbol_keys: HashSet<Symbol>,
    /// Substitution state at snapshot time
    pub subst_len: usize,
    /// Scope stack depth at snapshot time (number of frames).
    /// On restore, extra frames pushed during a failed check are popped.
    pub scope_depth: usize,
}

/// Typed error returned by `cranelisp_typecheck::check_form`. Per
/// FIXME 0098 Phase 1: the integration-layer `process_form` pattern-matches
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
