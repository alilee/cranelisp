// cranelisp-backend / src/error.rs — typed error DTOs for the backend public surface
//
// Per Decisions 37 + 41 and `design/arch/facades/backend.md` §"Errors":
//
// - `CompilationError` is the typed result of `compile_to_module`. Replaces
//   ad-hoc `CranelispError::CodegenError { message: "..." }` strings at the
//   backend boundary; callers (today: `int`) match on the variant rather
//   than parse messages. Per §2.7 of the facade — `SymbolNotCompilable` is
//   the typed signal for the Decision-37 failure mode (a caller passed a
//   `names` entry that does not satisfy `defined_symbols()` or was evicted
//   between schedule and call).
//
// - `LinkerError` is the typed result of `Linker::get_symbol` (Decision 36
//   — bare-name lookup) and other per-symbol cache-load operations. Per
//   Decision 37, asking for a symbol that isn't there is a typed error,
//   not a bare `Option<*const u8>`. The two-variant baseline is the
//   minimum surface acceptable at S67 close per the facade — additional
//   variants extend as evidence accrues (`MmapFailed`, `MachOParseError`,
//   `AbiMismatch` are foreseeable additions). The `#[non_exhaustive]`
//   attribute admits future additions without a public-API break.
//
// Placement (REV-4 of S67 Phase 2 review): both enums live in
// `cranelisp-backend` rather than `cranelisp-types` per Principle 15
// (single-consumer per error type). Backend is the sole constructor;
// `int` is the sole matcher. There is no multi-consumer pull that would
// justify hoisting these into `cranelisp-types`. `types.md` §"Errors and
// warnings" loses its `LinkerError` entry as part of the S67 close-out
// (see §"Errors" in `facades/backend.md` for the canonical definition).

use cranelisp_types::{ErrorLocation, LinkerSymbol, ModuleFullPath, Symbol};

/// Typed result of `compile_to_module`.
///
/// Replaces the pre-S67 ad-hoc `CranelispError::CodegenError { message: "..." }`
/// strings at the backend boundary. Per Decision 37, callers match on the
/// variant rather than parse messages.
///
/// Per facade `backend.md` §"Errors" — `#[non_exhaustive]` admits future
/// variants without breaking match exhaustiveness at the boundary.
#[non_exhaustive]
#[derive(Debug)]
pub enum CompilationError {
    /// A name passed in `names` does not resolve to a compilable entry in
    /// the symbol table. Indicates either a stale caller (the entry was
    /// evicted between `defined_symbols()` and the call) or a contract
    /// violation (caller passed a name that was never compilable —
    /// e.g., `kind == Overloaded` or `ast: None`).
    ///
    /// Per §2.7 of `facades/backend.md` — this is the typed signal for the
    /// Decision-37 failure mode.
    SymbolNotCompilable {
        module: ModuleFullPath,
        symbol: Symbol,
    },

    /// Cranelift codegen failed for a defined symbol. The `cause` is the
    /// underlying Cranelift verifier/builder message; `location` is the
    /// owning defn's `ErrorLocation` (per Decision 39 — coordinates as
    /// data; formatting downstream in `int`).
    CodegenFailed {
        module: ModuleFullPath,
        symbol: Symbol,
        cause: String,
        location: ErrorLocation,
    },

    /// `JITModule::define_function` or `Module::declare_function` returned
    /// an error. Distinct from `CodegenFailed` because this is a Cranelift
    /// `cranelift_module::ModuleError`, surfacing relocation or linkage
    /// failures rather than codegen-IR rejection.
    ModuleError {
        module: ModuleFullPath,
        symbol: Symbol,
        cause: String,
    },
}

/// Typed result of `Linker::get_symbol` (Decision 36 — bare-name lookup)
/// and other per-symbol cache-load operations.
///
/// Distinct from `CranelispError::LinkError` (process-level link failure):
/// `LinkerError` is per-symbol, surfaced by the cache `Linker` at the
/// boundary; `CranelispError::LinkError` is the system-linker invocation
/// failure surfaced by `int`'s `--link` orchestration.
///
/// Per Decision 37, asking for a symbol that's not there is a typed
/// result, not a bare `Option`. Per the facade — the two-variant baseline
/// is the minimum surface acceptable at S67 close; additional variants
/// extend as evidence accrues from production traces. `#[non_exhaustive]`
/// admits future additions (e.g., `MmapFailed`, `MachOParseError`,
/// `AbiMismatch`) without a public-API break.
#[non_exhaustive]
#[derive(Debug)]
pub enum LinkerError {
    /// The cache `Linker`'s symbol table does not contain the requested
    /// name. Usually indicates either: (a) the `.o` was produced from a
    /// different source state than the symbol-table consumer expects
    /// (cache mismatch); (b) the symbol's `Linkage::Local` bare name
    /// doesn't match what the caller asked for (Decision 36 contract
    /// violation).
    ///
    /// Pre-S58 silent-NULL regression net per Decision 37 — this variant
    /// is what the integration layer matches on at cache-hit failure.
    SymbolNotFound { name: LinkerSymbol },

    /// Object relocation pass produced an error during `load_object` or
    /// per-symbol resolution. Signals corruption, ABI mismatch, or
    /// unresolved external reference.
    RelocationFailed { name: LinkerSymbol, cause: String },
}

impl std::fmt::Display for CompilationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompilationError::SymbolNotCompilable { module, symbol } => write!(
                f,
                "symbol not compilable: {}/{}",
                module.as_ref(),
                symbol.as_ref()
            ),
            CompilationError::CodegenFailed {
                module,
                symbol,
                cause,
                ..
            } => write!(
                f,
                "codegen failed for {}/{}: {}",
                module.as_ref(),
                symbol.as_ref(),
                cause
            ),
            CompilationError::ModuleError {
                module,
                symbol,
                cause,
            } => write!(
                f,
                "module error for {}/{}: {}",
                module.as_ref(),
                symbol.as_ref(),
                cause
            ),
        }
    }
}

impl std::error::Error for CompilationError {}

/// Bridge `CranelispError` produced inside backend codegen to the typed
/// `CompilationError` at the boundary. Per Decision 37 + facade §"Errors":
/// callers match on `CompilationError` variants rather than parsing message
/// strings. Backend's internal flow still produces `CranelispError`
/// (workspace-wide error type); this `From` impl converts at the boundary.
///
/// Generic `CodegenError`/`ModuleError` shapes collapse into
/// `CompilationError::CodegenFailed` with the original message preserved
/// as `cause`. The `module` + `symbol` slots are best-effort; a follow-up
/// FIXME may file finer-grained conversions when the caller's match-arm
/// needs more precision than "something failed during codegen".
/// Reverse bridge: `CompilationError` flowing through internal call sites
/// that still produce `CranelispError`. Used at the few internal sites
/// (cache writer, exe link) that propagate codegen results upward through
/// a `CranelispError` channel. Preserves the message; loses the typed
/// discriminator (caller-side match becomes string-based again). Future
/// FIXMEs may lift those channels to typed errors.
impl From<CompilationError> for cranelisp_types::CranelispError {
    fn from(err: CompilationError) -> Self {
        let location = match &err {
            CompilationError::CodegenFailed { location, .. } => location.clone(),
            _ => cranelisp_types::ErrorLocation::from_span(cranelisp_types::Span::SYNTHETIC),
        };
        cranelisp_types::CranelispError::CodegenError {
            message: err.to_string(),
            location,
        }
    }
}

impl From<cranelisp_types::CranelispError> for CompilationError {
    fn from(err: cranelisp_types::CranelispError) -> Self {
        use cranelisp_types::CranelispError;
        let cause = err.to_string();
        let location = match &err {
            CranelispError::CodegenError { location, .. }
            | CranelispError::ModuleError { location, .. } => location.clone(),
            _ => cranelisp_types::ErrorLocation::from_span(cranelisp_types::Span::SYNTHETIC),
        };
        CompilationError::CodegenFailed {
            module: ModuleFullPath::from(""),
            symbol: Symbol::from(""),
            cause,
            location,
        }
    }
}

impl std::fmt::Display for LinkerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LinkerError::SymbolNotFound { name } => {
                write!(f, "symbol not found in cache linker: {}", name.as_ref())
            }
            LinkerError::RelocationFailed { name, cause } => {
                write!(f, "relocation failed for {}: {}", name.as_ref(), cause)
            }
        }
    }
}

impl std::error::Error for LinkerError {}
