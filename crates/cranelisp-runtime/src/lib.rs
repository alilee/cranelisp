//! cranelisp-runtime: allocation, RC infrastructure, string runtime, and
//! type conversion primitives for JIT-compiled Cranelisp code.
//!
//! Ring 0: panic intrinsic for match exhaustiveness failure.
//! Ring 1: heap allocator, RC trace logging, opaque string runtime, type conversions.
//!
//! ## Base-pointer convention
//!
//! All heap pointers point to offset 0 of the allocation (where `alloc_size`
//! lives). This departs from the sketch's interior-pointer convention.
//! See `design/platform/runtime.md` for rationale.
//!
//! ## Module structure
//!
//! - `alloc` — heap allocator, dealloc, tracking counters, LIVE_ALLOCS
//! - `rc` — RC trace logging, underflow check
//! - `string` — HeapString layout, string allocation and operations
//! - `vec` — Vec runtime primitives (new, len, set-copy, push-copy, push-grow, drop)
//! - `primitives` — type conversion functions (int/float/bool to string, parse-int)
//! - `panic` — runtime panic handler for JIT code

pub mod alloc;
pub mod rc;
pub mod string;
pub mod vec;
pub mod primitives;
pub mod panic;
pub mod marshal;

// Re-export extern "C" functions. The JIT builder registers these by function
// pointer, not by symbol name — see src/CLAUDE.md §"JIT Symbol Names".

// Runtime infrastructure (registered as runtime/alloc, runtime/dealloc, etc.)
pub use alloc::{heap_alloc, heap_dealloc};
pub use panic::runtime_panic;
pub use rc::rc_underflow_check;

// String infrastructure (registered as runtime/alloc_string, runtime/string_read)
pub use string::{heap_alloc_string, string_read};

// Vec runtime primitives (registered as runtime/vec_new, vec-len, etc.)
pub use vec::{vec_new, vec_len, vec_set_copy, vec_push_copy, vec_push_grow, vec_drop};

// Extern primitives (registered by spec name: str-concat, str-eq, etc.)
pub use string::{str_concat, str_eq, str_len, string_identity};
pub use primitives::int::{int_to_string, parse_int};
pub use primitives::float::float_to_string;
pub use primitives::bool::bool_to_string;

// Marshal primitives (registered by spec name: sconcat, quote-sexp)
pub use marshal::{sconcat, quote_sexp};

// Re-export public Rust API for use by /qa integration tests and binary crate.
pub use alloc::{
    alloc_count, alloc_with_rc, bytes_allocated, bytes_current, bytes_peak, dealloc_count,
    reset_counts,
};
#[cfg(debug_assertions)]
pub use alloc::is_live;
pub use string::{alloc_string, read_string_as_str, HeapString};
pub use rc::is_rc_trace_enabled;
