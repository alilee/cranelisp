//! Runtime marshalling helpers for Sexp and SList ADT values.
//!
//! Provides `quote_sexp` and `sconcat` as extern "C" functions callable from
//! JIT-compiled code. These operate directly on i64 runtime representations
//! without the compiler's `Sexp` enum.
//!
//! Tag constants are imported from `cranelisp_types::marshal` (single source
//! of truth). See that module for constructor order documentation.

use crate::alloc::alloc_with_rc;
use crate::string::alloc_string;
use cranelisp_types::{
    TAG_SNIL, TAG_SCONS,
    TAG_SEXP_INT, TAG_SEXP_FLOAT, TAG_SEXP_BOOL, TAG_SEXP_STR,
    TAG_SEXP_SYM, TAG_SEXP_LIST, TAG_SEXP_BRACKET,
};

// Heap layout constants (base-pointer convention, Decision 10)
const PAYLOAD_OFFSET: usize = 16;
const FIELD0_OFFSET: usize = 24;
const FIELD1_OFFSET: usize = 32;

/// Threshold below which values are bare nullary tags, not heap pointers.
const NULLARY_THRESHOLD: i64 = cranelisp_types::NULLARY_TAG_THRESHOLD as i64;

// ---------------------------------------------------------------------------
// Heap allocation helpers
// ---------------------------------------------------------------------------

/// Allocate a 2-slot ADT cell: [tag, field].
fn alloc_adt_2(tag: i64, field: i64) -> i64 {
    let payload_size = 16; // tag(8) + field(8)
    let base = alloc_with_rc(payload_size) as i64;
    unsafe {
        write_i64(base, PAYLOAD_OFFSET, tag);
        write_i64(base, FIELD0_OFFSET, field);
    }
    base
}

/// Allocate a 3-slot ADT cell: [tag, field0, field1].
fn alloc_adt_3(tag: i64, field0: i64, field1: i64) -> i64 {
    let payload_size = 24; // tag(8) + field0(8) + field1(8)
    let base = alloc_with_rc(payload_size) as i64;
    unsafe {
        write_i64(base, PAYLOAD_OFFSET, tag);
        write_i64(base, FIELD0_OFFSET, field0);
        write_i64(base, FIELD1_OFFSET, field1);
    }
    base
}

/// Build a runtime SList from a slice of i64 values.
/// Right-folds into SCons chain: SCons(items[0], SCons(items[1], ... SNil)).
fn build_runtime_list(items: &[i64]) -> i64 {
    let mut list = TAG_SNIL;
    for &item in items.iter().rev() {
        list = alloc_adt_3(TAG_SCONS, item, list);
    }
    list
}

/// Read items from a runtime SList (SCons chain) into a Vec.
///
/// # Safety
/// `ptr` must be a valid SList value (SNil tag or heap pointer to SCons).
unsafe fn read_slist(mut ptr: i64) -> Vec<i64> {
    let mut result = Vec::new();
    unsafe {
        loop {
            if ptr < NULLARY_THRESHOLD {
                break;
            }
            let head = read_i64(ptr, FIELD0_OFFSET);
            let tail = read_i64(ptr, FIELD1_OFFSET);
            result.push(head);
            ptr = tail;
        }
    }
    result
}

/// Allocate a runtime string from bytes. Returns the base pointer as i64.
fn alloc_runtime_string(name: &str) -> i64 {
    alloc_string(name.as_bytes()) as i64
}

/// Build a runtime SexpSym with the given name.
fn make_sexp_sym(name: &str) -> i64 {
    let s = alloc_runtime_string(name);
    alloc_adt_2(TAG_SEXP_SYM, s)
}

// ---------------------------------------------------------------------------
// Raw memory access
// ---------------------------------------------------------------------------

unsafe fn read_i64(base: i64, offset: usize) -> i64 {
    unsafe { *((base as *const u8).add(offset) as *const i64) }
}

unsafe fn write_i64(base: i64, offset: usize, value: i64) {
    unsafe { *((base as *mut u8).add(offset) as *mut i64) = value }
}

// ---------------------------------------------------------------------------
// sconcat: concatenate two runtime SList values
// ---------------------------------------------------------------------------

/// Increment the reference count of a heap-allocated value (shallow).
///
/// No-op for nullary tags (bare values < NULLARY_TAG_THRESHOLD).
/// Used by `sconcat` to keep items alive when they are copied from `xs`
/// into a new SList (the original `xs` SCons chain may be freed by the
/// caller's drop glue after the call).
fn shallow_rc_inc(val: i64) {
    if val >= NULLARY_THRESHOLD {
        // SAFETY: val is a heap pointer; RC field is at offset 8 from base.
        unsafe {
            let rc_ptr = (val as *mut u8).add(8) as *mut i64; // rc: i64
            *rc_ptr += 1;
        }
    }
}

/// Deeply increment the reference count of a runtime SList and all its
/// elements. Used by `sconcat` to keep the `ys` chain alive when it is
/// embedded as the tail of the result.
fn deep_rc_inc_slist(mut slist: i64) {
    loop {
        if slist < NULLARY_THRESHOLD {
            break; // SNil (nullary tag) — no heap alloc to inc
        }
        shallow_rc_inc(slist); // inc the SCons node itself
        let head = unsafe { read_i64(slist, FIELD0_OFFSET) };
        let tail = unsafe { read_i64(slist, FIELD1_OFFSET) };
        shallow_rc_inc(head); // inc the Sexp element
        slist = tail;
    }
}

/// Concatenate two runtime SList values (xs ++ ys).
///
/// Reads all items from xs, then builds a new list prepending them onto ys.
/// This is the runtime backing for quasiquote `~@` (unquote-splicing).
///
/// **RC ownership**: The result shares data from both inputs:
/// - Items from `xs` are extracted and placed in new SCons nodes. Each item
///   gets a shallow RC inc so it survives if the caller frees the original
///   `xs` chain (via drop glue on temporaries).
/// - The `ys` chain is used directly as the tail of the result. It gets a
///   deep RC inc (every SCons node and every element) so it survives if the
///   caller's scope cleanup dec's the original `ys` variable.
///
/// Registered in the JIT as "sconcat" and in the `macros` module typechecker
/// so that `macros/sconcat` resolves correctly.
pub extern "C" fn sconcat(xs: i64, ys: i64) -> i64 {
    let items = unsafe { read_slist(xs) };
    if items.is_empty() {
        // No items from xs: result IS ys. Inc it so the caller can't free
        // the result by freeing ys.
        deep_rc_inc_slist(ys);
        return ys;
    }
    // Inc the ys chain so it survives scope cleanup of the original variable.
    deep_rc_inc_slist(ys);
    let mut result = ys;
    for &item in items.iter().rev() {
        // Inc each item so it survives if the original xs chain is freed.
        shallow_rc_inc(item);
        result = alloc_adt_3(TAG_SCONS, item, result);
    }
    result
}

// ---------------------------------------------------------------------------
// quote-sexp: convert a runtime Sexp into constructor source code
// ---------------------------------------------------------------------------

/// Quote a runtime Sexp value into constructor source code.
///
/// Takes a runtime Sexp ADT value and returns a new runtime Sexp ADT
/// that, when evaluated, would construct the original value.
///
/// Constructor names are module-qualified (`macros/SexpInt` etc.) so that
/// the generated code resolves without an explicit `(import [macros [*]])`.
///
/// Examples:
/// - `(SexpInt 42)` -> `(SexpList [(SexpSym "macros/SexpInt") (SexpInt 42)])`
/// - `(SexpSym "foo")` -> `(SexpList [(SexpSym "macros/SexpSym") (SexpStr "foo")])`
pub extern "C" fn quote_sexp(val: i64) -> i64 {
    // SAFETY: val is a valid heap pointer to a Sexp ADT cell.
    let tag = unsafe { read_i64(val, PAYLOAD_OFFSET) };
    let field0 = unsafe { read_i64(val, FIELD0_OFFSET) };

    match tag {
        TAG_SEXP_INT => {
            let ctor = make_sexp_sym("macros/SexpInt");
            let original = alloc_adt_2(TAG_SEXP_INT, field0);
            let items = build_runtime_list(&[ctor, original]);
            alloc_adt_2(TAG_SEXP_LIST, items)
        }
        TAG_SEXP_FLOAT => {
            let ctor = make_sexp_sym("macros/SexpFloat");
            let original = alloc_adt_2(TAG_SEXP_FLOAT, field0);
            let items = build_runtime_list(&[ctor, original]);
            alloc_adt_2(TAG_SEXP_LIST, items)
        }
        TAG_SEXP_BOOL => {
            let ctor = make_sexp_sym("macros/SexpBool");
            let original = alloc_adt_2(TAG_SEXP_BOOL, field0);
            let items = build_runtime_list(&[ctor, original]);
            alloc_adt_2(TAG_SEXP_LIST, items)
        }
        TAG_SEXP_STR => {
            let ctor = make_sexp_sym("macros/SexpStr");
            let original = alloc_adt_2(TAG_SEXP_STR, field0);
            let items = build_runtime_list(&[ctor, original]);
            alloc_adt_2(TAG_SEXP_LIST, items)
        }
        TAG_SEXP_SYM => {
            // Symbol name (string ptr) -> wrap as SexpStr for the argument
            let ctor = make_sexp_sym("macros/SexpSym");
            let str_val = alloc_adt_2(TAG_SEXP_STR, field0);
            let items = build_runtime_list(&[ctor, str_val]);
            alloc_adt_2(TAG_SEXP_LIST, items)
        }
        TAG_SEXP_LIST => {
            let ctor = make_sexp_sym("macros/SexpList");
            let quoted_list = quote_slist(field0);
            let items = build_runtime_list(&[ctor, quoted_list]);
            alloc_adt_2(TAG_SEXP_LIST, items)
        }
        TAG_SEXP_BRACKET => {
            let ctor = make_sexp_sym("macros/SexpBracket");
            let quoted_list = quote_slist(field0);
            let items = build_runtime_list(&[ctor, quoted_list]);
            alloc_adt_2(TAG_SEXP_LIST, items)
        }
        _ => {
            // Unknown tag — panic at runtime.
            let msg = "unknown Sexp tag in quote-sexp";
            crate::panic::runtime_panic(msg.as_ptr(), msg.len());
            0
        }
    }
}

/// Quote an SList into constructor source code.
///
/// SNil -> SexpSym("macros/SNil")
/// SCons(head, tail) -> SexpList([SexpSym("macros/SCons"), quote_sexp(head), quote_slist(tail)])
fn quote_slist(slist: i64) -> i64 {
    let items = unsafe { read_slist(slist) };
    let quoted: Vec<i64> = items.iter().map(|&item| quote_sexp(item)).collect();

    let nil = make_sexp_sym("macros/SNil");
    quoted.iter().rev().fold(nil, |acc, &item| {
        let scons_sym = make_sexp_sym("macros/SCons");
        let list_items = build_runtime_list(&[scons_sym, item, acc]);
        alloc_adt_2(TAG_SEXP_LIST, list_items)
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sconcat_empty_empty() {
        let result = sconcat(TAG_SNIL, TAG_SNIL);
        assert_eq!(result, TAG_SNIL);
    }

    #[test]
    fn test_sconcat_empty_nonempty() {
        let ys = alloc_adt_3(TAG_SCONS, 42, TAG_SNIL);
        let result = sconcat(TAG_SNIL, ys);
        // Result should be ys (since xs is empty).
        let items = unsafe { read_slist(result) };
        assert_eq!(items, vec![42]);
    }

    #[test]
    fn test_sconcat_nonempty_empty() {
        let xs = alloc_adt_3(TAG_SCONS, 1, alloc_adt_3(TAG_SCONS, 2, TAG_SNIL));
        let result = sconcat(xs, TAG_SNIL);
        let items = unsafe { read_slist(result) };
        assert_eq!(items, vec![1, 2]);
    }

    #[test]
    fn test_sconcat_both_nonempty() {
        let xs = alloc_adt_3(TAG_SCONS, 1, alloc_adt_3(TAG_SCONS, 2, TAG_SNIL));
        let ys = alloc_adt_3(TAG_SCONS, 3, TAG_SNIL);
        let result = sconcat(xs, ys);
        let items = unsafe { read_slist(result) };
        assert_eq!(items, vec![1, 2, 3]);
    }
}
