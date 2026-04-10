// Backend-specific types that contain runtime state.
// These live in cranelisp-backend, not cranelisp-types, because they hold
// function pointers, durations, and other non-serializable data.

/// Named constant for GOT table size — re-exported from cranelisp-types (single source of truth).
pub use cranelisp_types::GOT_TABLE_SIZE;

// M-1 resolved: NULLARY_TAG_THRESHOLD imported from cranelisp-types (single source of truth).
pub use cranelisp_types::NULLARY_TAG_THRESHOLD;
