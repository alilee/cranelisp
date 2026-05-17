use serde::{Deserialize, Serialize};
use std::path::PathBuf;

use crate::{FQSymbol, FQTypeName, Span, Symbol};

// ---------------------------------------------------------------------------
// Error location — Decision 39 / Decision 42
// ---------------------------------------------------------------------------

/// 1-based line + column, derived from byte offsets when source is in hand.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LineCol {
    pub line: u32,
    pub col: u32,
}

impl LineCol {
    pub fn new(line: u32, col: u32) -> Self {
        Self { line, col }
    }
}

/// Range across `LineCol` coordinates — start inclusive, end exclusive
/// (matches `Span`).
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LineColRange {
    pub start: LineCol,
    pub end: LineCol,
}

impl LineColRange {
    pub fn new(start: LineCol, end: LineCol) -> Self {
        Self { start, end }
    }
}

/// Permissive error-location carrier per Decision 39.
///
/// Producers populate the fields they have on hand at error-construction
/// time; the integration-layer formatter (`Sess::format_error`) selects
/// display strategy based on what's present.
///
/// - `span` is always populated — even synthetic forms use `Span::SYNTHETIC`.
/// - `file` set when the error originates in a file-based module.
/// - `fq` set for post-parse errors (lets formatter resolve via
///   `shared.introspection[fq].source` for inline snippets).
/// - `line_col` set when source was in hand at error-construction time.
/// - `context` set when producer captures inline source snippet (parse
///   errors always; typecheck/codegen typically defer to introspection).
///
/// See `design/arch/legacy/decisions/0039-per-defn-source-on-introspection.md`
/// for the operative rationale and `facades/types.md` §"Errors and warnings"
/// for the producer-side population matrix.
#[non_exhaustive]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorLocation {
    pub span: Span,
    pub file: Option<PathBuf>,
    pub fq: Option<FQSymbol>,
    pub line_col: Option<LineColRange>,
    pub context: Option<String>,
}

impl ErrorLocation {
    /// Synthetic location — used by callers that don't have any concrete
    /// coordinates yet (e.g., `cranelisp-platform::manifest_to_descriptors`
    /// constructs `LoadFailed` with `ErrorLocation::unknown()`; the caller
    /// rewrites at the call site). Span is `Span::SYNTHETIC`.
    pub fn unknown() -> Self {
        Self {
            span: Span::SYNTHETIC,
            file: None,
            fq: None,
            line_col: None,
            context: None,
        }
    }

    /// Construct from a span only — common for typecheck/codegen sites that
    /// have a span but defer file/fq/line_col resolution to the formatter.
    pub fn from_span(span: Span) -> Self {
        Self {
            span,
            file: None,
            fq: None,
            line_col: None,
            context: None,
        }
    }

    /// Construct from a span and file path.
    pub fn from_span_file(span: Span, file: Option<PathBuf>) -> Self {
        Self {
            span,
            file,
            fq: None,
            line_col: None,
            context: None,
        }
    }
}

// ---------------------------------------------------------------------------
// CranelispError — variant reshape (Decision 39)
// ---------------------------------------------------------------------------

/// All errors carry an `ErrorLocation` for source location data. The integration
/// layer formatter (`Sess::format_error`) decides how to display based on which
/// fields are populated.
#[non_exhaustive]
#[derive(Debug)]
pub enum CranelispError {
    ParseError {
        message: String,
        location: ErrorLocation,
    },
    TypeError {
        message: String,
        location: ErrorLocation,
    },
    CodegenError {
        message: String,
        location: ErrorLocation,
    },
    ModuleError {
        message: String,
        location: ErrorLocation,
    },
    MacroError {
        message: String,
        location: ErrorLocation,
    },
    /// Platform-origin failures — DLL load, manifest parse, ABI mismatch, dispatch.
    /// Per Decision 42; FIXME 0104 Phase 1.
    Platform(PlatformError),
}

impl CranelispError {
    /// Backwards-compatible accessor — returns the underlying span. Most
    /// variants always have a span on their location; the `Platform` variant
    /// delegates to its inner `PlatformError`.
    pub fn span(&self) -> Span {
        match self {
            CranelispError::ParseError { location, .. }
            | CranelispError::TypeError { location, .. }
            | CranelispError::CodegenError { location, .. }
            | CranelispError::ModuleError { location, .. }
            | CranelispError::MacroError { location, .. } => location.span,
            CranelispError::Platform(p) => p.location().span,
        }
    }

    pub fn message(&self) -> &str {
        match self {
            CranelispError::ParseError { message, .. }
            | CranelispError::TypeError { message, .. }
            | CranelispError::CodegenError { message, .. }
            | CranelispError::ModuleError { message, .. }
            | CranelispError::MacroError { message, .. } => message,
            CranelispError::Platform(p) => p.message_static(),
        }
    }

    /// Return the `ErrorLocation` for this error, if any.
    pub fn location(&self) -> Option<&ErrorLocation> {
        match self {
            CranelispError::ParseError { location, .. }
            | CranelispError::TypeError { location, .. }
            | CranelispError::CodegenError { location, .. }
            | CranelispError::ModuleError { location, .. }
            | CranelispError::MacroError { location, .. } => Some(location),
            CranelispError::Platform(p) => Some(p.location()),
        }
    }
}

impl std::fmt::Display for CranelispError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CranelispError::ParseError { message, location } => {
                write!(f, "parse error at {}: {message}", location.span)
            }
            CranelispError::TypeError { message, location } => {
                write!(f, "type error at {}: {message}", location.span)
            }
            CranelispError::CodegenError { message, location } => {
                write!(f, "codegen error at {}: {message}", location.span)
            }
            CranelispError::ModuleError { message, location } => {
                if let Some(path) = &location.file {
                    write!(
                        f,
                        "module error in {}: at {}: {message}",
                        path.display(),
                        location.span
                    )
                } else {
                    write!(f, "module error at {}: {message}", location.span)
                }
            }
            CranelispError::MacroError { message, location } => {
                write!(f, "macro error at {}: {message}", location.span)
            }
            CranelispError::Platform(p) => write!(f, "{p}"),
        }
    }
}

impl std::error::Error for CranelispError {}

impl From<PlatformError> for CranelispError {
    fn from(err: PlatformError) -> Self {
        CranelispError::Platform(err)
    }
}

// ---------------------------------------------------------------------------
// PlatformError — Decision 42 / FIXME 0104
// ---------------------------------------------------------------------------

/// Platform-origin failures — DLL load, manifest parse, ABI mismatch,
/// dispatch. Per Decision 42 — coordinates as data; `int`'s
/// `Sess::format_error` consumes via `CranelispError::Platform(PlatformError)`
/// and selects display strategy via Decision 39's mode-conditional source
/// resolution.
///
/// `cranelisp-platform`'s `manifest_to_descriptors` constructs the
/// `LoadFailed` variant with `ErrorLocation::unknown()`; the integration
/// layer (`int::load_platform_dll`) rewrites the `dll` path and
/// `location` fields at the call site so the user sees
/// `lib/main.cl:42:7: error: platform "stdio" not found in search path`
/// rather than a free-floating string.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub enum PlatformError {
    /// DLL could not be loaded from the search path.
    LoadFailed {
        dll: PathBuf,
        cause: String,
        location: ErrorLocation,
    },
    /// DLL was found but its manifest is missing or unreadable.
    ManifestNotFound {
        dll: PathBuf,
        location: ErrorLocation,
    },
    /// DLL's declared ABI version does not match the runtime's expected version.
    AbiVersionMismatch {
        dll: PathBuf,
        expected: u32,
        found: u32,
        location: ErrorLocation,
    },
    /// A platform-fn dispatch failed at runtime (e.g., null fn ptr,
    /// panic in callee).
    DispatchError {
        fn_name: Symbol,
        cause: String,
        location: ErrorLocation,
    },
}

impl PlatformError {
    /// Single accessor — every variant carries an `ErrorLocation`.
    pub fn location(&self) -> &ErrorLocation {
        match self {
            PlatformError::LoadFailed { location, .. }
            | PlatformError::ManifestNotFound { location, .. }
            | PlatformError::AbiVersionMismatch { location, .. }
            | PlatformError::DispatchError { location, .. } => location,
        }
    }

    /// Internal helper for `CranelispError::message()` — yields a static
    /// description per variant; the human-readable variant data is in `Display`.
    fn message_static(&self) -> &'static str {
        match self {
            PlatformError::LoadFailed { .. } => "platform DLL load failed",
            PlatformError::ManifestNotFound { .. } => "platform manifest not found",
            PlatformError::AbiVersionMismatch { .. } => "platform ABI version mismatch",
            PlatformError::DispatchError { .. } => "platform fn dispatch failed",
        }
    }
}

impl std::fmt::Display for PlatformError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PlatformError::LoadFailed { dll, cause, .. } => {
                write!(f, "failed to load DLL {}: {}", dll.display(), cause)
            }
            PlatformError::ManifestNotFound { dll, .. } => write!(
                f,
                "DLL {} has no `cranelisp_platform_manifest` symbol",
                dll.display()
            ),
            PlatformError::AbiVersionMismatch {
                dll,
                expected,
                found,
                ..
            } => write!(
                f,
                "DLL {} ABI version {} does not match expected {}",
                dll.display(),
                found,
                expected
            ),
            PlatformError::DispatchError { fn_name, cause, .. } => write!(
                f,
                "platform fn `{}` dispatch failed: {}",
                &**fn_name, cause
            ),
        }
    }
}

impl std::error::Error for PlatformError {}

// ---------------------------------------------------------------------------
// LinkerError — relocated to `cranelisp-backend` per Sprint 67 REV-4.
// See `crates/cranelisp-backend/src/error.rs` for the canonical enum and
// `design/arch/facades/backend.md` §"Errors" for the facade specification.
// `design/arch/facades/types.md` §"Errors and warnings" carries the cross-ref
// pointer authored at S67 Wave 0.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// ResolutionGap — FIXME 0098
// ---------------------------------------------------------------------------

/// Cross-cutting "this dependency isn't ready yet" signal.
///
/// Carried by both `cranelisp_frontend::ExpansionError::Gap` and
/// `cranelisp_typecheck::CheckError::Gap`. The integration layer's
/// `process_form` pattern-matches on the variant to decide what to wait
/// on — typecheck for symbol typing, JIT for in-mem macro code, typecheck
/// for an opaque type ref. Per FIXMEs 0092 / 0093 / 0098.
///
/// `ResolutionGap` is the sole multi-consumer exception that justifies
/// staying in `cranelisp-types` per Principle 15 — both frontend and
/// typecheck originate it, and `int` consumes from both. `CheckError`
/// and `ExpansionError` move to their originating crates per FIXME 0100.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolutionGap {
    /// Symbol's typecheck not yet complete — wait for
    /// `notify_symbol_typechecked(fq)`. Produced by
    /// `cranelisp_typecheck::check_form` for value references.
    SymbolTypechecked(FQSymbol),

    /// Macro target needs in-mem JIT — typecheck first, then
    /// `priority_boost_jit(fq)` + `wait_for_inmem(fq)`. Produced
    /// exclusively by `cranelisp_frontend::expand`; never raised
    /// from typecheck.
    MacroInMem(FQSymbol),

    /// Type reference needs typecheck — wait for
    /// `notify_type_resolved(fq)`. Produced by
    /// `cranelisp_typecheck::check_form` for FQ type references.
    Type(FQTypeName),
}

// ---------------------------------------------------------------------------
// Warnings (unchanged)
// ---------------------------------------------------------------------------

/// Classification of non-fatal diagnostics.
/// Enables filtering, counting by category, and future `-Werror=<kind>` support.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum WarningKind {
    /// A binding is defined but never referenced.
    UnusedBinding,
    /// A match arm can never be reached (dominated by earlier patterns).
    UnreachableArm,
    /// A binding shadows an existing binding in an outer scope.
    ShadowedName,
    /// A warning that does not fit a structured category.
    Other,
}

/// Non-fatal diagnostic accumulated during compilation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Warning {
    pub kind: WarningKind,
    pub message: String,
    pub span: Span,
}
