//! Runtime marshalling helpers for Sexp and SList ADT values.
//!
//! Provides `quote_sexp` and `sconcat` as extern "C" functions callable from
//! JIT-compiled code. These operate directly on i64 runtime representations
//! without the compiler's `Sexp` enum.
//!
//! Tag constants are imported from `cranelisp_types::marshal` (single source
//! of truth). See that module for constructor order documentation.
//!
//! ## Heap-layout offsets — single source of truth
//!
//! The payload base and the RC offset derive from
//! [`cranelisp_types::HeapHeader`] (`SIZE` / `RC_OFFSET`, whose const rustdoc
//! +static asserts are the canonical statement) — never local copies (single
//! source of truth, Principle 7). The ADT field offsets (`FIELD0`/`FIELD1`)
//! are derived from `HeapHeader::SIZE` plus the local i64 field stride, so the
//! payload base stays single-sourced and only the stride is local. This is the
//! pattern `string.rs`/`vec.rs`/`int.rs` already follow; a `HeapHeader` layout
//! change is now caught here at compile time (the `const _` asserts below)
//! rather than silently corrupting the raw `read_i64`/`write_i64` accesses.
//!
//! Per Decision 43 (see the crate-root `//!` and `bounded-contexts.md` §4a):
//! these are user-callable primitives (kebab-case JIT names `sconcat` /
//! `quote-sexp`, registered in the synthetic `primitives` module's symbol
//! table). The bodies were lifted from the pre-D43 runtime crate.

use cranelisp_intrinsics::alloc::alloc_with_rc;
use cranelisp_intrinsics::drop::{consume_sexp, consume_slist};
use cranelisp_intrinsics::heap_string::alloc_string;
use cranelisp_types::HeapHeader;
use cranelisp_types::{
    TAG_SNIL, TAG_SCONS,
    TAG_SEXP_INT, TAG_SEXP_FLOAT, TAG_SEXP_BOOL, TAG_SEXP_STR,
    TAG_SEXP_SYM, TAG_SEXP_LIST, TAG_SEXP_BRACKET,
};

// Heap-layout offsets (base-pointer convention, Decision 10), single-sourced
// from `cranelisp_types::HeapHeader` (Principle 7). The payload (first ADT
// slot, the tag) sits immediately after the header; subsequent i64 fields are
// strided by `FIELD_STRIDE`.
const FIELD_STRIDE: usize = core::mem::size_of::<i64>(); // 8
/// Offset of the ADT payload (tag) — first slot after the heap header.
const PAYLOAD_OFFSET: usize = HeapHeader::SIZE; // 16
/// Offset of ADT field 0 (one i64 past the tag).
const FIELD0_OFFSET: usize = PAYLOAD_OFFSET + FIELD_STRIDE; // 24
/// Offset of ADT field 1 (two i64s past the tag).
const FIELD1_OFFSET: usize = PAYLOAD_OFFSET + 2 * FIELD_STRIDE; // 32

// Compile-time assertions mirroring the sibling files — fail the build if the
// derived offsets ever diverge from the layout these bodies were written for.
const _: () = assert!(PAYLOAD_OFFSET == 16);
const _: () = assert!(FIELD0_OFFSET == 24);
const _: () = assert!(FIELD1_OFFSET == 32);

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
///
/// Routes through the blessed `cranelisp_intrinsics::rc::rc_inc` entry point —
/// the single owner of the shallow-inc discipline (Principle 7). The
/// nullary-tag skip lives inside `rc_inc`. This replaces the former *non-atomic*
/// `*rc_ptr += 1` (audit MED-1), which became a genuine data race once the S85
/// auto-IO wiring let a spark fork a callee sharing a value inc'd here.
fn shallow_rc_inc(val: i64) {
    cranelisp_intrinsics::rc::rc_inc(val);
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
///   `xs` chain.
/// - The `ys` chain is used directly as the tail of the result. It gets a
///   deep RC inc (every SCons node and every element) so it survives if the
///   caller's scope cleanup dec's the original `ys` variable.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention. `sconcat` inc's
/// the items of `xs` into new SCons nodes, inc's the `ys` chain deeply so
/// the result can use it as a tail, then releases the original `xs` and
/// `ys` via `consume_slist` (runtime-side recursive drop glue). Callers
/// compile args through `compile_consuming_arg_list` (heap-typed Vars are
/// inc'd at the call site so the caller's binding survives our dec).
///
/// Registered in the JIT as "sconcat" and in the `macros` module typechecker
/// so that `macros/sconcat` resolves correctly.
#[unsafe(export_name = "sconcat")]
pub(crate) extern "C" fn sconcat(xs: i64, ys: i64) -> i64 {
    let items = unsafe { read_slist(xs) };
    let result = if items.is_empty() {
        // No items from xs: result IS ys. Inc it so the caller can't free
        // the result by freeing ys.
        deep_rc_inc_slist(ys);
        ys
    } else {
        // Inc the ys chain so it survives consumption of the original variable.
        deep_rc_inc_slist(ys);
        let mut acc = ys;
        for &item in items.iter().rev() {
            // Inc each item so it survives when the original xs chain is freed.
            shallow_rc_inc(item);
            acc = alloc_adt_3(TAG_SCONS, item, acc);
        }
        acc
    };
    // Decision 24: consume the heap arguments we did not return.
    consume_slist(xs);
    consume_slist(ys);
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
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention. The extern entry
/// point builds the quoted result (sharing field pointers with appropriate
/// incs) and then releases the input via `consume_sexp` (runtime-side
/// recursive drop glue). Callers compile args through
/// `compile_consuming_arg_list`.
#[unsafe(export_name = "quote-sexp")]
pub(crate) extern "C" fn quote_sexp(val: i64) -> i64 {
    let result = quote_sexp_build(val);
    // Decision 24: consume the heap argument we did not return.
    consume_sexp(val);
    result
}

/// Build the quoted-form Sexp without consuming `val`. Shared between the
/// extern entry and `quote_slist` (which feeds items that are still owned
/// by the parent SList).
fn quote_sexp_build(val: i64) -> i64 {
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
            // The cloned ADT reuses field0 (a String pointer) — inc it so
            // both the input and the new wrapper own a reference.
            shallow_rc_inc(field0);
            let ctor = make_sexp_sym("macros/SexpStr");
            let original = alloc_adt_2(TAG_SEXP_STR, field0);
            let items = build_runtime_list(&[ctor, original]);
            alloc_adt_2(TAG_SEXP_LIST, items)
        }
        TAG_SEXP_SYM => {
            // Symbol name (string ptr) -> wrap as SexpStr for the argument.
            // Inc so the new SexpStr owns an independent reference.
            shallow_rc_inc(field0);
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
            cranelisp_intrinsics::panic::runtime_panic(msg.as_ptr(), msg.len());
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
    // Use the non-consuming builder for sub-items: ownership of each item
    // stays with the parent SList, which the caller will eventually
    // release via `consume_sexp` at the top-level quote_sexp.
    let quoted: Vec<i64> = items.iter().map(|&item| quote_sexp_build(item)).collect();

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
mod tests;
