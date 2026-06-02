//! Module-level grouping of codegen size constants.
//!
//! Per Principle 15, `GOT_TABLE_SIZE` and `NULLARY_TAG_THRESHOLD` originate in
//! `cranelisp-types` (single source of truth); the re-exports here are a
//! convenience path for codegen sites that reach for them during CLIF
//! emission. (Originally framed as "backend-specific runtime-state types"; the
//! module now carries only these two re-exported size constants.)

/// Named constant for GOT table size — re-exported from cranelisp-types (single source of truth).
pub use cranelisp_types::GOT_TABLE_SIZE;

// M-1 resolved: NULLARY_TAG_THRESHOLD imported from cranelisp-types (single source of truth).
pub use cranelisp_types::NULLARY_TAG_THRESHOLD;
