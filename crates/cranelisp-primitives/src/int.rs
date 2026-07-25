//! Integer conversion primitives — user-callable.
//!
//! Per Decision 43 (see the crate-root `//!` and `bounded-contexts.md` §4a):
//! kebab-case JIT names (`int-to-string`, `parse-int`), registered in the
//! synthetic `primitives` module's symbol table; user-addressable.
//!
//! Wave 3b-2d.2b lifted the bodies from the pre-D43 runtime crate
//! (`primitives/int.rs`) into this crate. The
//! `cranelisp_op_*` operator-as-value wrappers that previously cohabited
//! that file are backend-emitted-call targets (not user-callable; backend
//! emits direct calls when an operator is referenced as a first-class
//! value) and migrated to `cranelisp-intrinsics::ops` instead.
//! (The pre-D43 runtime crate has since retired per FIXME 0150 Phase 5 —
//! its D43 split produced `cranelisp-primitives` + `cranelisp-intrinsics`.)

use cranelisp_intrinsics::alloc;
use cranelisp_intrinsics::heap_string;
use cranelisp_intrinsics::rc;

/// Convert an integer to its decimal string representation.
/// Returns a new HeapString (rc=1).
pub(crate) fn int_to_string(n: i64) -> i64 {
    let s = n.to_string();
    heap_string::alloc_string(s.as_bytes()) as i64
}

/// Parse an integer from a string. Returns an Option Int as a heap ADT.
///
/// Returns:
/// - `None`: bare i64 tag 0
/// - `Some(n)`: heap-allocated `[alloc_size | rc | tag=1 | n]`
///
/// Depends on Chunk B (Option type). The runtime constructs the ADT layout
/// directly — it does not need the type system.
/// Parse an integer from a string. Returns an Option Int as a heap ADT.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — dec the heap arg.
pub(crate) fn parse_int(s: i64) -> i64 {
    // SAFETY: s is a valid HeapString base pointer.
    let str_val = unsafe { heap_string::read_string_as_str(s) };

    let result = match str_val.trim().parse::<i64>() {
        Ok(n) => {
            // Some(n): allocate [tag=1 | n] as payload (16 bytes)
            let base = alloc::alloc_with_rc(16); // tag + 1 field
            // SAFETY: base is valid, has 16 bytes of payload.
            unsafe {
                // tag at HeapHeader::SIZE (offset 16)
                *(base.add(cranelisp_types::HeapHeader::SIZE) as *mut i64) = 1;
                // value at HeapHeader::SIZE + 8 (offset 24)
                *(base.add(cranelisp_types::HeapHeader::SIZE + 8) as *mut i64) = n;
            }
            base as i64
        }
        Err(_) => {
            // None: bare tag 0
            0
        }
    };
    // Consume the input string reference (Decision 24).
    rc::consume_shallow(s);
    result
}

#[cfg(test)]
mod tests;
