// Backend-specific types that contain runtime state.
// These live in cranelisp-backend, not cranelisp-types, because they hold
// function pointers, durations, and other non-serializable data.

use cranelisp_types::{Defn, Sexp};

/// Named constant for GOT table size.
pub const GOT_TABLE_SIZE: usize = 1024;

// M-1 resolved: NULLARY_TAG_THRESHOLD imported from cranelisp-types (single source of truth).
pub use cranelisp_types::NULLARY_TAG_THRESHOLD;

/// Codegen artifacts for a single definition.
#[derive(Debug, Clone, Default)]
pub struct DefCodegen {
    pub got_slot: Option<usize>,
    pub code_ptr: Option<*const u8>,
    pub source: Option<String>,
    pub sexp: Option<Sexp>,
    pub defn: Option<Defn>,
    pub clif_ir: Option<String>,
    pub disasm: Option<String>,
    pub code_size: Option<usize>,
    pub compile_duration: Option<std::time::Duration>,
    pub param_count: Option<usize>,
}

// SAFETY: DefCodegen contains raw pointers that are only used from the JIT
// execution thread. The pointer values are stable after JIT finalization.
unsafe impl Send for DefCodegen {}
unsafe impl Sync for DefCodegen {}
