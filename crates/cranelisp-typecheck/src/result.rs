//! Typecheck result types. Relocated from `cranelisp-types` per FIXME 0100
//! Phase 1 — single-consumer types live with their originating crate
//! (Principle 15). `CheckResult` and `ReplSnapshot` originate in
//! `cranelisp-typecheck` and are consumed only by `int` downstream.
//!
//! `CheckError` (FIXME 0098 Phase 1) is the typed error returned by
//! `check_form`; its `Gap(ResolutionGap)` arm is the integration-layer
//! pattern-match target for the gap-orchestration retry loop.

use std::collections::HashSet;

use cranelisp_types::{
    DisplayInfo, ErrorLocation, ModuleFullPath, ResolutionGap, Span, Symbol, TraitName, TypeId,
    TypeName, Visibility, Warning,
};

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

/// Error type for the unified `resolve_*` family (Phase B Part 5).
///
/// Each variant carries enough context to produce a user-facing message
/// without further lookups: the name being resolved, the calling module
/// (so messages can say "from `<module>`"), and the source span.
///
/// Grounded in Principle 17 (module locality — resolution failures are
/// scoped to the calling module's import frontier) and Principle 2
/// (narrow interfaces — one Result-shaped surface per resolution kind).
///
/// `ResolveError` is typecheck-local (kept in `cranelisp-typecheck`, not
/// `cranelisp-types`) per Principle 15: one producer (typecheck), one
/// consumer that uses the typed form (typecheck). Downstream crates see
/// only `CheckError` via the `From` projection below.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub enum ResolveError {
    /// Trait name is not reachable from the calling module's import scope,
    /// nor anywhere on its chain-follow path.
    TraitNotFound {
        name: TraitName,
        from_module: ModuleFullPath,
        span: Span,
    },
    /// Type name is not reachable from the calling module's import scope.
    /// Includes the intrinsic short-names (`Int`/`Bool`/`Float`/`String`)
    /// post-Phase-B — there's no hardcoded fallback any more.
    TypeNotFound {
        name: TypeName,
        from_module: ModuleFullPath,
        span: Span,
    },
    /// Constructor name is not reachable, OR is reachable but is not a
    /// constructor entry (e.g., a regular `Def` of the same name shadows it).
    ConstructorNotFound {
        name: Symbol,
        from_module: ModuleFullPath,
        span: Span,
    },
    /// FQ reference like `module/name` where `module` doesn't exist or
    /// isn't loaded. Distinct from `*NotFound` because the failure is at
    /// module-resolution, not name-resolution.
    QualifiedModuleUnknown {
        module: ModuleFullPath,
        name: Symbol,
        span: Span,
    },
    /// Name exists in `defining_module` but its visibility forbids access
    /// from `from_module`. Lets the user-facing message say "X is private
    /// to module Y" instead of "X not found".
    PrivateInaccessible {
        name: Symbol,
        defining_module: ModuleFullPath,
        from_module: ModuleFullPath,
        visibility_found: Visibility,
        span: Span,
    },
}

impl std::fmt::Display for ResolveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let projected: CheckError = self.clone().into();
        std::fmt::Display::fmt(&projected, f)
    }
}

impl std::error::Error for ResolveError {}

impl From<ResolveError> for CheckError {
    fn from(e: ResolveError) -> CheckError {
        match e {
            ResolveError::TraitNotFound { name, from_module, span } => CheckError::TypeError {
                message: format!("unknown trait `{name}` (from module `{from_module}`)"),
                location: ErrorLocation::from_span(span),
            },
            ResolveError::TypeNotFound { name, from_module, span } => CheckError::TypeError {
                message: format!("unknown type `{name}` (from module `{from_module}`)"),
                location: ErrorLocation::from_span(span),
            },
            ResolveError::ConstructorNotFound { name, from_module, span } => CheckError::TypeError {
                message: format!(
                    "unknown constructor `{name}` (from module `{from_module}`)"
                ),
                location: ErrorLocation::from_span(span),
            },
            ResolveError::QualifiedModuleUnknown { module, name, span } => CheckError::TypeError {
                message: format!(
                    "module `{module}` referenced by `{module}/{name}` is not loaded"
                ),
                location: ErrorLocation::from_span(span),
            },
            ResolveError::PrivateInaccessible {
                name,
                defining_module,
                from_module,
                visibility_found: _,
                span,
            } => CheckError::TypeError {
                message: format!(
                    "`{name}` is private to module `{defining_module}`; not accessible from `{from_module}`"
                ),
                location: ErrorLocation::from_span(span),
            },
        }
    }
}

/// Convenience: a `ResolveError` projects to `CranelispError::TypeError`
/// via the same message + location used in `CheckError`. Used by call
/// sites still on the older `CranelispError` API (e.g., free functions
/// in `resolve.rs`).
impl From<ResolveError> for cranelisp_types::CranelispError {
    fn from(e: ResolveError) -> cranelisp_types::CranelispError {
        let CheckError::TypeError { message, location } = e.into() else {
            unreachable!("ResolveError never projects to CheckError::Gap");
        };
        cranelisp_types::CranelispError::TypeError { message, location }
    }
}
