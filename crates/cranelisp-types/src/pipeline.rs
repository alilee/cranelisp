use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::{CranelispError, ModuleFullPath, Sexp, Span, Symbol};

/// Which codegen queues receive work from `compile_unit`.
///
/// See design/arch/pipeline-v3.md §4 for the full design rationale.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CodegenBehaviour {
    /// Enqueue to both in-memory (JIT) and object (.o) queues.
    /// Used by REPL and --run. In-mem produces live function pointers
    /// in the GOT; object queue writes .o files in the background.
    InMemoryAndObject,

    /// Enqueue to object queue only. No JIT, no execution.
    /// Used by --link. Compiles directly to relocatable .o files.
    ObjectOnly,
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
        &self,
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
        &self,
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

// --- Module strategy and compile context ---

/// How definitions from a compilation unit integrate with existing module state.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ModuleStrategy {
    /// REPL mode: add to existing module state (definitions accumulate).
    Additive,
    /// File load mode: these forms ARE the module (replace prior state).
    Replace,
}

/// Context for a compilation unit — tells the pipeline which module definitions
/// land in and what codegen behaviour to use.
///
/// Per pipeline-v3.md §4, `ModuleStrategy` is a parameter on `compile_unit`,
/// not a field here, because the same context (same module, same codegen
/// behaviour) may be used with different strategies.
#[derive(Debug, Clone)]
pub struct CompileContext {
    /// Target module for definitions.
    pub module: ModuleFullPath,
    /// Which codegen queues receive work (in-mem+object vs object-only).
    pub codegen: CodegenBehaviour,
}

// --- Call graph types ---

/// An edge in the call graph from one function to another.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CallEdge {
    /// Name of the called function.
    pub callee: Symbol,
    /// Whether this call is in tail position.
    pub tail_position: bool,
    /// Source location of the call site.
    pub span: Span,
}

/// Call information for a single function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CallInfo {
    /// Outgoing call edges from this function.
    pub edges: Vec<CallEdge>,
}

/// Map from function name to its call information.
/// Populated during typecheck, consumed by codegen and analysis passes.
pub type CallGraph = HashMap<Symbol, CallInfo>;
