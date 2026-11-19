// cranelisp-backend / src/error.rs — typed error DTOs for the backend public surface
//
// Per Decisions 37 + 41: callers match on typed variants rather than parse
// messages. `CompilationError` is the typed result of `compile_to_module`;
// `LinkerError` is the typed result of `Linker::get_symbol` (Decision 36 —
// bare-name lookup) and other per-symbol cache-load operations. Both are
// `#[non_exhaustive]`, so variants may be added without a public-API break.
//
// Placement: both enums live in `cranelisp-backend` rather than
// `cranelisp-types` per Principle 15 — backend is the sole constructor and
// `int` the sole matcher, so nothing justifies hoisting them.

use cranelisp_types::{ErrorLocation, LinkerSymbol, ModuleFullPath, Symbol};

/// Typed result of `compile_to_module`.
///
/// Per Decision 37, callers match on the variant rather than parse messages.
/// `#[non_exhaustive]` admits future variants without breaking match
/// exhaustiveness at the boundary.
#[non_exhaustive]
#[derive(Debug)]
pub enum CompilationError {
    /// A name passed in `names` does not resolve to a compilable entry in
    /// the symbol table. Indicates either a stale caller (the entry was
    /// evicted between `defined_symbols()` and the call) or a contract
    /// violation (caller passed a name that was never compilable —
    /// e.g., `kind == Overloaded` or `ast: None`). This is the typed signal
    /// for the Decision-37 failure mode.
    SymbolNotCompilable {
        module: ModuleFullPath,
        symbol: Symbol,
    },

    /// Cranelift codegen failed for a defined symbol: `module` and `symbol`
    /// name the failing target, and neither is empty. The `cause` is the
    /// underlying Cranelift verifier/builder message; `location` is the
    /// owning defn's `ErrorLocation` (per Decision 39 — coordinates as
    /// data; formatting downstream in `int`).
    CodegenFailed {
        module: ModuleFullPath,
        symbol: Symbol,
        cause: String,
        location: ErrorLocation,
    },

    /// The module's compilation failed outside any one target: a missing
    /// module table, a refused target during collection, a missing
    /// intrinsic, the glue fence or GOT emission. The module is the only
    /// subject; `cause` and `location` are the inner error's
    /// (`non-concrete-release-contract.md` §7.2.1, *Unattributed*).
    ModuleFailed {
        module: ModuleFullPath,
        cause: String,
        location: ErrorLocation,
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
/// result, not a bare `Option`. `#[non_exhaustive]` admits future variants
/// without a public-API break.
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
            // The symbol may already name a module (an instance key), so the
            // module is a separate noun, never a path prefix (§7.2.1 Rule 3).
            CompilationError::SymbolNotCompilable { module, symbol } => {
                write!(f, "symbol not compilable: {symbol} in {module}")
            }
            CompilationError::CodegenFailed {
                module,
                symbol,
                cause,
                ..
            } => write!(f, "codegen failed for {symbol} in {module}: {cause}"),
            CompilationError::ModuleFailed { module, cause, .. } => {
                write!(f, "codegen failed in {module}: {cause}")
            }
        }
    }
}

impl std::error::Error for CompilationError {}

/// Reverse bridge: `CompilationError` flowing through internal call sites
/// that still produce `CranelispError`. Used at the few internal sites
/// (cache writer, exe link) that propagate codegen results upward through
/// a `CranelispError` channel. Preserves the message; loses the typed
/// discriminator (caller-side match becomes string-based again). Future
/// FIXMEs may lift those channels to typed errors.
impl From<CompilationError> for cranelisp_types::CranelispError {
    fn from(err: CompilationError) -> Self {
        let location = match &err {
            CompilationError::CodegenFailed { location, .. }
            | CompilationError::ModuleFailed { location, .. } => location.clone(),
            _ => cranelisp_types::ErrorLocation::from_span(cranelisp_types::Span::SYNTHETIC),
        };
        cranelisp_types::CranelispError::CodegenError {
            message: err.to_string(),
            location,
        }
    }
}

/// `err` as the codegen failure of `symbol` in `module`. `cause` is the
/// inner message and `location` the inner location, so the only located
/// prefix is the one rendered at the boundary
/// (`non-concrete-release-contract.md` §7.2.1 Rule 1). A platform error keeps
/// its whole rendering, because its message alone drops the detail.
pub(crate) fn codegen_failed(
    module: ModuleFullPath,
    symbol: Symbol,
    err: cranelisp_types::CranelispError,
) -> CompilationError {
    let (cause, location) = cause_and_location(err);
    CompilationError::CodegenFailed {
        module,
        symbol,
        cause,
        location,
    }
}

/// `err` as a failure of `module`'s compilation with no failing target
/// (§7.2.1, *Unattributed*), under the same Rule 1 extraction as
/// [`codegen_failed`].
pub(crate) fn module_failed(
    module: ModuleFullPath,
    err: cranelisp_types::CranelispError,
) -> CompilationError {
    let (cause, location) = cause_and_location(err);
    CompilationError::ModuleFailed {
        module,
        cause,
        location,
    }
}

/// The one home of Rule 1: `cause` is the inner message and `location` the
/// inner location; a platform error keeps its whole rendering as `cause`.
fn cause_and_location(err: cranelisp_types::CranelispError) -> (String, ErrorLocation) {
    let cause = match &err {
        cranelisp_types::CranelispError::Platform(platform) => platform.to_string(),
        other => other.message().to_owned(),
    };
    (cause, err.location().clone())
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
