//! Runtime marshalling helpers for Sexp and SList ADT values.
//!
//! Operates directly on i64 runtime representations — no dependency on the
//! compiler's `Sexp` enum. Used by both the JIT and standalone executables.

use crate::intrinsics::alloc_with_rc;
use crate::primitives::alloc_string;

// Sexp ADT constructor tags (by definition order in prelude)
pub const TAG_SEXP_SYM: i64 = 0;
pub const TAG_SEXP_INT: i64 = 1;
pub const TAG_SEXP_FLOAT: i64 = 2;
pub const TAG_SEXP_BOOL: i64 = 3;
pub const TAG_SEXP_STR: i64 = 4;
pub const TAG_SEXP_LIST: i64 = 5;
pub const TAG_SEXP_BRACKET: i64 = 6;

// SList ADT constructor tags
pub const TAG_SNIL: i64 = 0;
pub const TAG_SCONS: i64 = 1;

/// Allocate a heap ADT cell: `[tag, fields...]`.
/// Returns the payload pointer as i64.
pub fn alloc_adt(tag: i64, fields: &[i64]) -> i64 {
    let n_slots = 1 + fields.len(); // tag + fields
    let size = n_slots * 8;
    let ptr = alloc_with_rc(size);
    unsafe {
        *(ptr as *mut i64) = tag;
        for (i, &field) in fields.iter().enumerate() {
            *((ptr as *mut i64).add(1 + i)) = field;
        }
    }
    ptr as i64
}

/// Build a runtime SList from a slice of already-marshalled i64 values.
/// Right-folds into a SCons chain: `SCons(items[0], SCons(items[1], ... SNil))`.
pub fn build_runtime_list(items: &[i64]) -> i64 {
    let mut list = TAG_SNIL; // SNil = bare 0
    for &item in items.iter().rev() {
        list = alloc_adt(TAG_SCONS, &[item, list]);
    }
    list
}

/// Read items from a runtime SList (SCons chain).
unsafe fn read_slist(mut ptr: i64) -> Vec<i64> {
    unsafe {
        let mut result = Vec::new();
        loop {
            if ptr == TAG_SNIL {
                break;
            }
            let head = *((ptr as *const i64).add(1));
            let tail = *((ptr as *const i64).add(2));
            result.push(head);
            ptr = tail;
        }
        result
    }
}

/// Build a runtime SexpSym with the given name.
fn make_sexp_sym(name: &str) -> i64 {
    let s = alloc_string(name.as_bytes());
    alloc_adt(TAG_SEXP_SYM, &[s])
}

/// Quote a runtime Sexp value into constructor source code.
/// Operates directly on i64 runtime values without the Sexp enum.
///
/// Takes a runtime Sexp ADT value and returns a new runtime Sexp ADT
/// that, when evaluated, would construct the original value.
///
/// Examples:
/// - `(SexpInt 42)` -> `(SexpList [(SexpSym "SexpInt") (SexpInt 42)])`
/// - `(SexpSym "foo")` -> `(SexpList [(SexpSym "SexpSym") (SexpStr "foo")])`
#[unsafe(export_name = "quote-sexp")]
pub extern "C" fn quote_sexp(val: i64) -> i64 {
    let tag = unsafe { *(val as *const i64) };
    let field0 = unsafe { *((val as *const i64).add(1)) };

    match tag {
        TAG_SEXP_INT => {
            let ctor = make_sexp_sym("SexpInt");
            let original = alloc_adt(TAG_SEXP_INT, &[field0]);
            let items = build_runtime_list(&[ctor, original]);
            alloc_adt(TAG_SEXP_LIST, &[items])
        }
        TAG_SEXP_FLOAT => {
            let ctor = make_sexp_sym("SexpFloat");
            let original = alloc_adt(TAG_SEXP_FLOAT, &[field0]);
            let items = build_runtime_list(&[ctor, original]);
            alloc_adt(TAG_SEXP_LIST, &[items])
        }
        TAG_SEXP_BOOL => {
            let ctor = make_sexp_sym("SexpBool");
            let original = alloc_adt(TAG_SEXP_BOOL, &[field0]);
            let items = build_runtime_list(&[ctor, original]);
            alloc_adt(TAG_SEXP_LIST, &[items])
        }
        TAG_SEXP_STR => {
            let ctor = make_sexp_sym("SexpStr");
            let original = alloc_adt(TAG_SEXP_STR, &[field0]);
            let items = build_runtime_list(&[ctor, original]);
            alloc_adt(TAG_SEXP_LIST, &[items])
        }
        TAG_SEXP_SYM => {
            // Symbol name (string ptr) -> wrap as SexpStr
            let ctor = make_sexp_sym("SexpSym");
            let str_val = alloc_adt(TAG_SEXP_STR, &[field0]);
            let items = build_runtime_list(&[ctor, str_val]);
            alloc_adt(TAG_SEXP_LIST, &[items])
        }
        TAG_SEXP_LIST => {
            let ctor = make_sexp_sym("SexpList");
            let quoted_list = quote_slist(field0);
            let items = build_runtime_list(&[ctor, quoted_list]);
            alloc_adt(TAG_SEXP_LIST, &[items])
        }
        TAG_SEXP_BRACKET => {
            let ctor = make_sexp_sym("SexpBracket");
            let quoted_list = quote_slist(field0);
            let items = build_runtime_list(&[ctor, quoted_list]);
            alloc_adt(TAG_SEXP_LIST, &[items])
        }
        _ => {
            eprintln!("panic: unknown Sexp tag in quote_sexp: {}", tag);
            std::process::exit(1);
        }
    }
}

/// Quote an SList into constructor source code.
/// SNil -> SexpSym("SNil")
/// SCons(head, tail) -> SexpList([SexpSym("SCons"), quote_sexp(head), quote_slist(tail)])
fn quote_slist(slist: i64) -> i64 {
    let items = unsafe { read_slist(slist) };
    let quoted: Vec<i64> = items.iter().map(|&item| quote_sexp(item)).collect();

    let nil = make_sexp_sym("SNil");
    quoted.iter().rev().fold(nil, |acc, &item| {
        let scons_sym = make_sexp_sym("SCons");
        let list_items = build_runtime_list(&[scons_sym, item, acc]);
        alloc_adt(TAG_SEXP_LIST, &[list_items])
    })
}
