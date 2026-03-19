use crate::{CranelispError, Sexp, Span, Symbol};

/// Controls compilation strategy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompileMode {
    /// GOT-indirect calls for hot-reload. Used for REPL and module reloading.
    Interactive,
    /// Direct function calls, no GOT indirection. Used for batch compilation and testing.
    Batch,
    /// Whole-program optimisation, standalone binary. Ring 4+ / Phase H.
    Release,
}

/// Trait for expanding macros during AST building.
/// Defined in cranelisp-types (not cranelisp-frontend) for dependency inversion:
/// frontend depends on this trait, binary crate implements it.
///
/// Wave 1 decision: lives in cranelisp-types because it's used across crate boundaries
/// (frontend references the trait, binary crate provides the implementation).
pub trait MacroExpander {
    /// Expand a macro invocation, returning the expanded Sexp.
    fn expand(
        &mut self,
        name: &Symbol,
        args: &[Sexp],
        span: Span,
    ) -> Result<Sexp, CranelispError>;

    /// Check whether a name is a known macro.
    fn is_macro(&self, name: &str) -> bool;
}

/// No-op macro expander for Ring 0 (no macros).
/// Binary crate uses this until Ring 3 macro support is implemented.
pub struct NoOpExpander;

impl MacroExpander for NoOpExpander {
    fn expand(
        &mut self,
        _name: &Symbol,
        _args: &[Sexp],
        span: Span,
    ) -> Result<Sexp, CranelispError> {
        Err(CranelispError::ModuleError {
            message: "macros not available".into(),
            file: None,
            span,
        })
    }

    fn is_macro(&self, _name: &str) -> bool {
        false
    }
}

/// Result of compiling a single unit (returned by binary crate pipeline).
pub struct CompileResult {
    /// Updated symbol table entries
    pub symbols: Vec<(Symbol, crate::ModuleEntry)>,
    /// Codegen artifacts (DefCodegen lives in backend crate, so this uses a
    /// serializable summary — full DefCodegen is backend-internal)
    pub codegen_names: Vec<Symbol>,
    /// Accumulated warnings
    pub warnings: Vec<crate::Warning>,
}

// --- Backend types that live in cranelisp-backend, documented here for reference ---
// ModuleCodegenState, DefCodegen, CacheMetadata, NULLARY_TAG_THRESHOLD
// are NOT defined here — they live in cranelisp-backend because they contain runtime state.

/// Named constant for GOT table size. Shared between backend and runtime crates
/// so that GOT memcpy operations use the same size. Single source of truth.
pub const GOT_TABLE_SIZE: usize = 1024;

/// Named constant for nullary constructor tag threshold.
/// Values below this are nullary tags; values above are heap pointers.
/// Shared between typechecker (for ADT validation) and backend (for codegen).
pub const NULLARY_TAG_THRESHOLD: usize = 1024;
