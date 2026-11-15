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
use cranelisp_intrinsics::handle::Owned;
use cranelisp_intrinsics::heap_string;
use cranelisp_intrinsics::rc;

use crate::abi_facts::adopt_produced_value;

/// Convert an integer to its decimal string representation.
/// Returns a new HeapString (rc=1).
pub(crate) fn int_to_string(n: i64) -> Owned {
    let s = n.to_string();
    // SAFETY: `alloc_string` returned a fully initialized fresh RC=1 String.
    unsafe { adopt_produced_value(heap_string::alloc_string(s.as_bytes()) as i64) }
}

/// Build an `Option Int` value: `None` is the bare nullary tag 0; `Some(n)` is
/// a fresh RC=1 node `[header | tag=1 | n]`.
fn option_int(value: Option<i64>) -> Owned {
    match value {
        Some(n) => {
            let base = alloc::alloc_with_rc(16);
            // SAFETY: `base` is a fresh allocation with 16 payload bytes after
            // the header: the tag word, then the single field.
            unsafe {
                *(base.add(cranelisp_types::HeapHeader::SIZE) as *mut i64) = 1;
                *(base.add(cranelisp_types::HeapHeader::SIZE + 8) as *mut i64) = n;
            }
            // SAFETY: `base` is now a fully initialized fresh RC=1 Some node.
            unsafe { adopt_produced_value(base as i64) }
        }
        // SAFETY: zero is the canonical produced `None` nullary tag.
        None => unsafe { adopt_produced_value(0) },
    }
}

/// Parse a decimal integer, ignoring surrounding whitespace; `None` on failure.
/// Consumes its String argument (Decision 24).
pub(crate) fn parse_int(s: Owned) -> Owned {
    // SAFETY: s is a valid HeapString base pointer.
    let str_val = unsafe { heap_string::read_string_as_str(s.raw_for_read()) };
    let result = option_int(str_val.trim().parse::<i64>().ok());
    rc::consume_shallow(s);
    result
}

/// `checked-quot` (spec §12.7.3): the quotient truncated toward zero, or
/// `None` for a zero divisor and for `i64::MIN / -1`. Never panics.
pub(crate) fn checked_quot(a: i64, b: i64) -> Owned {
    option_int(a.checked_div(b))
}

#[cfg(test)]
mod tests;
