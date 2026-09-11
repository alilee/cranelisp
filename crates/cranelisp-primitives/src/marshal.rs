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
use cranelisp_intrinsics::handle::{Borrowed, Owned};
use cranelisp_intrinsics::heap_string::alloc_string;
use cranelisp_types::HeapHeader;
use cranelisp_types::{
    TAG_SCONS, TAG_SEXP_BOOL, TAG_SEXP_BRACKET, TAG_SEXP_FLOAT, TAG_SEXP_INT, TAG_SEXP_LIST,
    TAG_SEXP_STR, TAG_SEXP_SYM, TAG_SNIL,
};

use crate::abi_facts::adopt_produced_value;

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
enum StoredField {
    Scalar(i64),
    Owned(Owned),
}

fn alloc_adt_2(tag: i64, field: StoredField) -> Owned {
    let payload_size = 16; // tag(8) + field(8)
    let base = alloc_with_rc(payload_size) as i64;
    unsafe {
        write_i64(base, PAYLOAD_OFFSET, tag);
        match field {
            StoredField::Scalar(value) => write_i64(base, FIELD0_OFFSET, value),
            StoredField::Owned(owner) => write_i64(base, FIELD0_OFFSET, owner.into_raw()),
        }
    }
    // SAFETY: both slots are initialized and `base` is a fresh RC=1 ADT.
    unsafe { adopt_produced_value(base) }
}

/// Allocate a 3-slot ADT cell: [tag, field0, field1].
fn alloc_adt_3(tag: i64, field0: Owned, field1: Owned) -> Owned {
    let payload_size = 24; // tag(8) + field0(8) + field1(8)
    let base = alloc_with_rc(payload_size) as i64;
    unsafe {
        write_i64(base, PAYLOAD_OFFSET, tag);
        write_i64(base, FIELD0_OFFSET, field0.into_raw());
        write_i64(base, FIELD1_OFFSET, field1.into_raw());
    }
    // SAFETY: all three slots are initialized and `base` is a fresh RC=1 ADT.
    unsafe { adopt_produced_value(base) }
}

/// Build a runtime SList from a fixed array of owned values.
/// Right-folds into SCons chain: SCons(items[0], SCons(items[1], ... SNil)).
fn build_runtime_list<const N: usize>(items: [Owned; N]) -> Owned {
    // SAFETY: `TAG_SNIL` is the canonical produced nullary list value.
    let mut list = unsafe { adopt_produced_value(TAG_SNIL) };
    for item in items.into_iter().rev() {
        list = alloc_adt_3(TAG_SCONS, item, list);
    }
    list
}

/// Read items from a runtime SList (SCons chain) into a Vec.
///
/// # Safety
/// `ptr` must be a valid SList value (SNil tag or heap pointer to SCons).
unsafe fn read_slist<'a>(mut list: Borrowed<'a>) -> Vec<Borrowed<'a>> {
    let mut result = Vec::new();
    loop {
        if list.raw_for_read() < NULLARY_THRESHOLD {
            break;
        }
        // SAFETY: the loop guard establishes the current node is an SCons;
        // its closed layout carries reference-bearing head and tail fields.
        let head = unsafe { borrowed_field(list, FIELD0_OFFSET) };
        // SAFETY: same live SCons parent and closed layout as the head.
        let tail = unsafe { borrowed_field(list, FIELD1_OFFSET) };
        result.push(head);
        list = tail;
    }
    result
}

/// Allocate a runtime string from bytes. Returns the base pointer as i64.
fn alloc_runtime_string(name: &str) -> Owned {
    // SAFETY: `alloc_string` returned a fully initialized fresh RC=1 String.
    unsafe { adopt_produced_value(alloc_string(name.as_bytes()) as i64) }
}

/// Build a runtime SexpSym with the given name.
fn make_sexp_sym(name: &str) -> Owned {
    let s = alloc_runtime_string(name);
    alloc_adt_2(TAG_SEXP_SYM, StoredField::Owned(s))
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

/// Project a reference-bearing child through its live parent borrow.
///
/// # Safety
///
/// `offset` must identify a live reference-bearing field in the parent's
/// established ADT layout.
unsafe fn borrowed_field<'a>(parent: Borrowed<'a>, offset: usize) -> Borrowed<'a> {
    let raw = unsafe { read_i64(parent.raw_for_read(), offset) };
    // SAFETY: the caller established the field's retained-reference contract;
    // the return type narrows the raw assertion to the parent lifetime.
    unsafe { Borrowed::from_abi(raw) }
}

// ---------------------------------------------------------------------------
// sconcat: concatenate two runtime SList values
// ---------------------------------------------------------------------------

/// Increment the reference count of a heap-allocated value (shallow).
///
/// No-op for nullary tags (bare values < NULLARY_TAG_THRESHOLD).
///
/// This is the ONLY inc these bodies perform, in both of the two roles the
/// producers have (`design/runtime/s118-structural-embedding-ownership.md`
/// §2, RE-3): one inc per **copied** reference (`sconcat`'s `xs` items, each
/// stored into a fresh `SCons`; `quote_sexp_build`'s re-used `String`
/// pointers), and exactly one inc on the node **shared** by a structural
/// embed (`sconcat`'s `ys` tail, RE-1).
///
/// Routes through the blessed `cranelisp_intrinsics::rc::rc_inc` entry point —
/// the single owner of the shallow-inc discipline (Principle 7). The
/// nullary-tag skip lives inside `rc_inc`, which is what makes it safe to
/// call on a `ys` that is `SNil`. This replaces the former *non-atomic*
/// `*rc_ptr += 1` (audit MED-1), which became a genuine data race once the S85
/// auto-IO wiring let a spark fork a callee sharing a value inc'd here.
fn shallow_rc_inc(val: Borrowed<'_>) -> Owned {
    val.to_owned()
}

/// Concatenate two runtime SList values (xs ++ ys).
///
/// Reads all items from xs, then builds a new list prepending them onto ys.
/// This is the runtime backing for quasiquote `~@` (unquote-splicing).
///
/// **RC ownership** — the result shares data from both inputs, and the two
/// halves are different producer choices with different reference rules
/// (`design/runtime/s118-structural-embedding-ownership.md` §2; the
/// primitives invariant table, `design/primitives/primitives.md` §4 #13):
///
/// - Items from `xs` are **copied**: each is stored into a fresh `SCons`
///   node, so each takes one inc — one new owner, one reference (RE-3).
/// - The `ys` chain is **shared**: it is embedded by pointer as the tail of
///   the result, so it takes exactly **ONE** inc, on the node stored (RE-1).
///   Its interior nodes are owned by their parent node and its elements by
///   the node holding them; embedding does not change those owners, so
///   re-counting them would mint references no owner holds — and tree-
///   ownership drop glue (`consume_slist`, RE-2) is structurally incapable
///   of discharging them. The inc count for the embed is 1 whatever the size
///   and depth of `ys`.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention. `sconcat` inc's
/// the items of `xs` into new SCons nodes, takes the single embed inc on
/// `ys`, then releases the original `xs` and `ys` via `consume_slist`
/// (runtime-side recursive drop glue). Callers compile args through
/// `compile_consuming_arg_list` (heap-typed Vars are inc'd at the call site
/// so the caller's binding survives our dec). The inc/consume pair is kept
/// unconditional and explicit rather than cancelled into a move: it keeps
/// the epilogue uniform with every sibling complex-heap extern and states
/// the reference taken locally at the embed site (Principle 18).
///
/// Registered in the JIT as "sconcat" and in the `macros` module typechecker
/// so that `macros/sconcat` resolves correctly.
pub(crate) fn sconcat(xs: Owned, ys: Owned) -> Owned {
    let items = unsafe { read_slist(xs.as_borrowed()) };
    let ys_borrowed = ys.as_borrowed();
    let result = if items.is_empty() {
        // No items from xs: the result IS ys. One inc on the node returned —
        // nullary-safe, so an SNil `ys` is skipped inside `rc_inc`.
        shallow_rc_inc(ys_borrowed)
    } else {
        // RE-1: one inc on the node embedded as the tail. Not a walk — the
        // interior nodes and elements already have owners, unchanged by the
        // embed.
        let mut acc = shallow_rc_inc(ys_borrowed);
        for item in items.into_iter().rev() {
            // Inc each item so it survives when the original xs chain is freed.
            let item = shallow_rc_inc(item);
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
pub(crate) fn quote_sexp(val: Owned) -> Owned {
    let result = quote_sexp_build(val.as_borrowed());
    // Decision 24: consume the heap argument we did not return.
    consume_sexp(val);
    result
}

/// Build the quoted-form Sexp without consuming `val`. Shared between the
/// extern entry and `quote_slist` (which feeds items that are still owned
/// by the parent SList).
fn quote_sexp_build(val: Borrowed<'_>) -> Owned {
    // SAFETY: val is a valid heap pointer to a Sexp ADT cell.
    let tag = unsafe { read_i64(val.raw_for_read(), PAYLOAD_OFFSET) };

    match tag {
        TAG_SEXP_INT => {
            let field0 = unsafe { read_i64(val.raw_for_read(), FIELD0_OFFSET) };
            let ctor = make_sexp_sym("macros/SexpInt");
            let original = alloc_adt_2(TAG_SEXP_INT, StoredField::Scalar(field0));
            let items = build_runtime_list([ctor, original]);
            alloc_adt_2(TAG_SEXP_LIST, StoredField::Owned(items))
        }
        TAG_SEXP_FLOAT => {
            let field0 = unsafe { read_i64(val.raw_for_read(), FIELD0_OFFSET) };
            let ctor = make_sexp_sym("macros/SexpFloat");
            let original = alloc_adt_2(TAG_SEXP_FLOAT, StoredField::Scalar(field0));
            let items = build_runtime_list([ctor, original]);
            alloc_adt_2(TAG_SEXP_LIST, StoredField::Owned(items))
        }
        TAG_SEXP_BOOL => {
            let field0 = unsafe { read_i64(val.raw_for_read(), FIELD0_OFFSET) };
            let ctor = make_sexp_sym("macros/SexpBool");
            let original = alloc_adt_2(TAG_SEXP_BOOL, StoredField::Scalar(field0));
            let items = build_runtime_list([ctor, original]);
            alloc_adt_2(TAG_SEXP_LIST, StoredField::Owned(items))
        }
        TAG_SEXP_STR => {
            // The cloned ADT reuses field0 (a String pointer) — inc it so
            // both the input and the new wrapper own a reference.
            // SAFETY: this tag's field 0 is a retained String reference.
            let field0 = unsafe { borrowed_field(val, FIELD0_OFFSET) };
            let ctor = make_sexp_sym("macros/SexpStr");
            let original = alloc_adt_2(TAG_SEXP_STR, StoredField::Owned(field0.to_owned()));
            let items = build_runtime_list([ctor, original]);
            alloc_adt_2(TAG_SEXP_LIST, StoredField::Owned(items))
        }
        TAG_SEXP_SYM => {
            // Symbol name (string ptr) -> wrap as SexpStr for the argument.
            // Inc so the new SexpStr owns an independent reference.
            // SAFETY: this tag's field 0 is a retained String reference.
            let field0 = unsafe { borrowed_field(val, FIELD0_OFFSET) };
            let ctor = make_sexp_sym("macros/SexpSym");
            let str_val = alloc_adt_2(TAG_SEXP_STR, StoredField::Owned(field0.to_owned()));
            let items = build_runtime_list([ctor, str_val]);
            alloc_adt_2(TAG_SEXP_LIST, StoredField::Owned(items))
        }
        TAG_SEXP_LIST => {
            // SAFETY: this tag's field 0 is a retained SList reference.
            let field0 = unsafe { borrowed_field(val, FIELD0_OFFSET) };
            let ctor = make_sexp_sym("macros/SexpList");
            let quoted_list = quote_slist(field0);
            let items = build_runtime_list([ctor, quoted_list]);
            alloc_adt_2(TAG_SEXP_LIST, StoredField::Owned(items))
        }
        TAG_SEXP_BRACKET => {
            // SAFETY: this tag's field 0 is a retained SList reference.
            let field0 = unsafe { borrowed_field(val, FIELD0_OFFSET) };
            let ctor = make_sexp_sym("macros/SexpBracket");
            let quoted_list = quote_slist(field0);
            let items = build_runtime_list([ctor, quoted_list]);
            alloc_adt_2(TAG_SEXP_LIST, StoredField::Owned(items))
        }
        _ => {
            // Unknown tag — panic at runtime.
            let msg = "unknown Sexp tag in quote-sexp";
            cranelisp_intrinsics::panic::runtime_panic(msg.as_ptr(), msg.len());
            // SAFETY: this is the existing no-reference error sentinel after
            // `runtime_panic` has recorded the unknown-tag failure.
            unsafe { adopt_produced_value(0) }
        }
    }
}

/// Quote an SList into constructor source code.
///
/// SNil -> SexpSym("macros/SNil")
/// SCons(head, tail) -> SexpList([SexpSym("macros/SCons"), quote_sexp(head), quote_slist(tail)])
fn quote_slist(slist: Borrowed<'_>) -> Owned {
    let items = unsafe { read_slist(slist) };
    // Use the non-consuming builder for sub-items: ownership of each item
    // stays with the parent SList, which the caller will eventually
    // release via `consume_sexp` at the top-level quote_sexp.
    let quoted: Vec<Owned> = items.into_iter().map(quote_sexp_build).collect();

    let nil = make_sexp_sym("macros/SNil");
    quoted.into_iter().rev().fold(nil, |acc, item| {
        let scons_sym = make_sexp_sym("macros/SCons");
        let list_items = build_runtime_list([scons_sym, item, acc]);
        alloc_adt_2(TAG_SEXP_LIST, StoredField::Owned(list_items))
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
