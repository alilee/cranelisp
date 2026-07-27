use serde::{Deserialize, Serialize};

use crate::ModuleFullPath;

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

// `CompileResult` DELETED (S119, FIXME 0918 — the S87 dead-surface class): a
// zero-consumer public type; the binary's pipeline returns its own internal
// shapes. The call-graph cluster (`CallEdge`/`CallInfo`/`CallGraph`) is
// likewise deleted — the LIVE call-graph mechanism is the per-entry
// `ModuleEntry::Def.callees: Vec<FQSymbol>` field (Decision 21), not a
// parallel map.

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
