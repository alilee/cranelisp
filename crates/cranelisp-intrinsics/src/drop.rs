//! Full-dec primitives with recursive drop glue for complex heap types.
//!
//! Under Decision 24 (Sprint 56 Step 2c) every extern must dec its heap
//! arguments before returning. `rc::consume_shallow` handles simple types
//! (String, plain ADTs) but is unsafe for types that embed heap-typed
//! sub-references because it only dec's the outermost allocation.
//!
//! This module provides consume functions that match the backend's inline
//! drop glue (see `emit_rc_dec_with_inline_drop_glue` in
//! `cranelisp-backend::compiler::mod::rs`). Each function:
//!
//! 1. Skips if `ptr` is a bare nullary tag (< NULLARY_TAG_THRESHOLD).
//! 2. Atomically dec's the RC with Release ordering.
//! 3. If the old RC was 1 (sole reference): issues an Acquire fence, walks
//!    the heap-typed fields of the value, dec's each via the appropriate
//!    consume function, then frees the allocation.
//!
//! Supported types:
//!
//! - `consume_slist` — SList (SCons chain; SNil is a nullary tag)
//! - `consume_sexp` — Sexp ADT (tag-dispatched: SexpInt/Float/Bool have no
//!   heap sub-refs; SexpStr/Sym have a String field; SexpList/Bracket have
//!   an SList field)
//! - `consume_vec_of_heap` — Vec whose elements are heap-typed String
//!   pointers (walks elements, dec's each, frees data buffer, frees Vec)
//! - `consume_io_tree` — IO ADT (tag-dispatched: Pure has a payload (may
//!   be heap-typed by context); Effect holds a thunk + token; Bind has
//!   inner IO + continuation closure; Par has N branches)
//!
//! Integration: each complex-heap extern (`sconcat`, `quote_sexp`,
//! `str_join`, `cranelisp_run_io`) calls the appropriate consume function
//! on its heap arguments before returning. The TraceCall consumer
//! (`consume_trace_call`) lives in this crate's [`crate::trace`] module
//! (S76 trace ruling — the `(trace ...)` runtime is intrinsics-hosted, BC §4b
//! invariant 12). It is a LEAF consumer of this module's generic
//! `consume_shallow` / SList glue; this module does NOT reference it (no
//! re-coupling — `tracing.md` §4.1).
//! Callers compile those args through `compile_consuming_arg_list`, incing
//! heap-typed Vars. See `design/backend/ring2-rc.md` §3.3.

use std::sync::atomic::{AtomicI64, Ordering};

use cranelisp_platform::{IO_TAG_BIND, IO_TAG_EFFECT, IO_TAG_PAR, IO_TAG_PURE};
use cranelisp_types::{
    HeapHeader, NULLARY_TAG_THRESHOLD, TAG_SEXP_BRACKET, TAG_SEXP_LIST, TAG_SEXP_STR, TAG_SEXP_SYM,
};

use crate::alloc;
use crate::rc;

/// NULLARY_TAG_THRESHOLD as i64 for comparison with pointer values.
const NULLARY_THRESHOLD: i64 = NULLARY_TAG_THRESHOLD as i64;

// ---------------------------------------------------------------------------
// Heap field access
// ---------------------------------------------------------------------------

const TAG_OFFSET: usize = 16; // HeapHeader::SIZE
const FIELD0_OFFSET: usize = 24;
const FIELD1_OFFSET: usize = 32;

/// Read an i64 at `base + offset`.
///
/// # Safety
/// `base` must be a valid heap pointer with at least `offset + 8` readable bytes.
#[inline]
unsafe fn read_i64(base: i64, offset: usize) -> i64 {
    unsafe { *((base as *const u8).add(offset) as *const i64) }
}

/// Atomically decrement the RC at `ptr` with Release ordering.
/// Returns the OLD RC value.
///
/// # Safety
/// `ptr` must be a valid heap pointer with `rc > 0`.
#[inline]
unsafe fn atomic_dec_rc(ptr: i64) -> i64 {
    let rc_ptr = unsafe {
        &*((ptr as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const AtomicI64)
    };
    let old = rc_ptr.fetch_sub(1, Ordering::Release);
    debug_assert!(
        old > 0,
        "RC underflow in drop glue: ptr={ptr:#x} had rc={old} before decrement"
    );
    rc::rc_trace("dec", ptr, old - 1);
    old
}

// ---------------------------------------------------------------------------
// SList consumption
// ---------------------------------------------------------------------------

/// Consume an SList (SCons chain with heap-typed Sexp heads).
///
/// SNil (tag 0) is a bare nullary tag — skipped.
/// SCons(head, tail): dec each SCons node; if last reference, consume head
/// as a Sexp and consume tail recursively.
///
/// # Safety
/// `ptr` must be a valid SList pointer (SCons with rc > 0) or a bare SNil tag.
pub fn consume_slist(mut ptr: i64) {
    loop {
        if ptr < NULLARY_THRESHOLD {
            return; // SNil or bare tag
        }
        // Read fields BEFORE dec so we can recurse on the last-ref path.
        let head = unsafe { read_i64(ptr, FIELD0_OFFSET) };
        let tail = unsafe { read_i64(ptr, FIELD1_OFFSET) };

        let old_rc = unsafe { atomic_dec_rc(ptr) };
        if old_rc != 1 {
            return; // not last ref — head/tail stay owned by siblings
        }
        std::sync::atomic::fence(Ordering::Acquire);

        // Last ref: recursively release head (Sexp), then dealloc this node,
        // then iterate to tail to avoid unbounded recursion on long chains.
        consume_sexp(head);
        unsafe { alloc::dealloc(ptr as *mut u8) };
        ptr = tail;
    }
}

// ---------------------------------------------------------------------------
// Sexp consumption
// ---------------------------------------------------------------------------

/// Consume a Sexp ADT (tag-dispatched; dec's heap-typed fields on last ref).
///
/// - SexpInt/Float/Bool (tags 0/1/2): no heap sub-refs.
/// - SexpStr (tag 3): field0 is a String heap pointer.
/// - SexpSym (tag 4): field0 is a String heap pointer (the symbol name).
/// - SexpList (tag 5): field0 is an `SList<Sexp>`.
/// - SexpBracket (tag 6): field0 is an `SList<Sexp>`.
///
/// # Safety
/// `ptr` must be a valid Sexp heap pointer (rc > 0) or a bare nullary tag.
pub fn consume_sexp(ptr: i64) {
    if ptr < NULLARY_THRESHOLD {
        return;
    }
    // Read tag + field0 before dec so the recursive step has them on the
    // last-ref path.
    let tag = unsafe { read_i64(ptr, TAG_OFFSET) };
    let field0 = unsafe { read_i64(ptr, FIELD0_OFFSET) };

    let old_rc = unsafe { atomic_dec_rc(ptr) };
    if old_rc != 1 {
        return;
    }
    std::sync::atomic::fence(Ordering::Acquire);

    // Last ref — release heap sub-refs according to tag.
    match tag {
        TAG_SEXP_STR | TAG_SEXP_SYM => {
            // field0 is a String pointer.
            rc::consume_shallow(field0);
        }
        TAG_SEXP_LIST | TAG_SEXP_BRACKET => {
            // field0 is an SList<Sexp>.
            consume_slist(field0);
        }
        _ => {
            // SexpInt/Float/Bool (tags 0/1/2) — field0 is a scalar, no RC.
        }
    }
    unsafe { alloc::dealloc(ptr as *mut u8) };
}

// ---------------------------------------------------------------------------
// Vec consumption
// ---------------------------------------------------------------------------

/// Vec layout offsets (must match `crate::vec`).
const VEC_LEN_OFFSET: usize = 16;
const VEC_CAP_OFFSET: usize = 24;
const VEC_DATA_PTR_OFFSET: usize = 32;

/// Per-element consume callback pointer.
type ElemConsumeFn = fn(i64);

/// Consume a Vec whose elements are released via `elem_consume`.
///
/// On last ref: walk `len` live elements, call `elem_consume` on each;
/// free the data buffer with the stdlib allocator; dealloc the Vec struct.
///
/// # Safety
/// `ptr` must be a valid Vec struct base pointer (rc > 0) or bare nullary
/// tag. The element consume function must be safe to call on the in-Vec
/// i64 values.
pub fn consume_vec_with(ptr: i64, elem_consume: ElemConsumeFn) {
    if ptr < NULLARY_THRESHOLD {
        return;
    }
    let old_rc = unsafe { atomic_dec_rc(ptr) };
    if old_rc != 1 {
        return;
    }
    std::sync::atomic::fence(Ordering::Acquire);

    unsafe {
        let base = ptr as *mut u8;
        let len = *(base.add(VEC_LEN_OFFSET) as *const i64);
        let cap = *(base.add(VEC_CAP_OFFSET) as *const i64);
        let data = *(base.add(VEC_DATA_PTR_OFFSET) as *const *mut i64);

        for i in 0..len as usize {
            let elem = *data.add(i);
            elem_consume(elem);
        }

        // Free the data buffer (plain allocation, not tracked by alloc_with_rc).
        if !data.is_null() && cap > 0 {
            let byte_size = cap as usize * 8;
            let layout = std::alloc::Layout::from_size_align(byte_size, 8)
                .unwrap_or_else(|_| unreachable!("invariant: valid layout for size {byte_size}"));
            std::alloc::dealloc(data as *mut u8, layout);
        }

        alloc::dealloc(base);
    }
}

/// Consume a Vec of heap Strings (elements are consumed via `rc::consume_shallow`).
pub fn consume_vec_of_string(ptr: i64) {
    consume_vec_with(ptr, rc::consume_shallow);
}

// ---------------------------------------------------------------------------
// IO tree consumption
// ---------------------------------------------------------------------------

/// Consume an IO ADT tree.
///
/// - Pure (tag 0): field0 is the payload — may or may not be heap-typed;
///   we conservatively treat it as opaque scalar (Pure-over-heap requires
///   the caller to release the payload separately, matching the sketch's
///   behavior where the trampoline returns the payload's ownership to
///   the caller).
/// - Effect (tag 1): field0 is the thunk pointer (opaque), field1 is the
///   resource token (Int). Neither is a Cranelisp heap allocation.
/// - Bind (tag 2): field0 is the inner IO tree, field1 is a continuation
///   closure (HeapClosure).
/// - Par (tag 3): field0 is the count (Int), field1..N are branch IO
///   pointers.
///
/// # Safety
/// `ptr` must be a valid IO tree root pointer (rc > 0) or bare nullary tag.
pub fn consume_io_tree(ptr: i64) {
    if ptr < NULLARY_THRESHOLD {
        return;
    }
    let tag = unsafe { read_i64(ptr, TAG_OFFSET) };

    // Snapshot fields needed for recursion on the last-ref path.
    let field0 = unsafe { read_i64(ptr, FIELD0_OFFSET) };

    // For Bind/Par we also need field1/branches.
    let field1 = if tag == IO_TAG_BIND {
        unsafe { read_i64(ptr, FIELD1_OFFSET) }
    } else {
        0
    };

    // Par branches snapshot (count + pointers).
    let par_branches: Vec<i64> = if tag == IO_TAG_PAR {
        let count = field0 as usize;
        let mut v = Vec::with_capacity(count);
        for i in 0..count {
            // Branches live at FIELD1_OFFSET + i*8.
            let p = unsafe { read_i64(ptr, FIELD1_OFFSET + i * 8) };
            v.push(p);
        }
        v
    } else {
        Vec::new()
    };

    let old_rc = unsafe { atomic_dec_rc(ptr) };
    if old_rc != 1 {
        return;
    }
    std::sync::atomic::fence(Ordering::Acquire);

    match tag {
        t if t == IO_TAG_PURE => {
            // Pure's payload is opaque — the trampoline returns it to the
            // caller as the final value. No action here.
            let _ = field0;
        }
        t if t == IO_TAG_EFFECT => {
            // field0 is a raw thunk pointer (Box<Box<dyn FnOnce>>) which
            // the trampoline consumes on invocation; field1 is the resource
            // token (Int). Neither is a Cranelisp heap alloc.
            let _ = field0;
        }
        t if t == IO_TAG_BIND => {
            consume_io_tree(field0);
            // field1 is a continuation closure. Closure drop glue lives in
            // the backend (embedded drop_glue_ptr at offset 24). From the
            // runtime side we can only do a shallow consume — the closure's
            // inline drop-glue function pointer is not invokable without
            // the JIT context. Call the closure's embedded drop glue if
            // present, then dec-and-free the closure struct.
            consume_closure(field1);
        }
        t if t == IO_TAG_PAR => {
            for branch in par_branches {
                consume_io_tree(branch);
            }
        }
        _ => {
            // Unknown IO tag — treat conservatively as scalar fields.
        }
    }
    unsafe { alloc::dealloc(ptr as *mut u8) };
}

// ---------------------------------------------------------------------------
// Shallow IO-node dec (Decision 29; design/backend/ring2-rc.md §3.5.4)
// ---------------------------------------------------------------------------

/// Shallow dec of a single IO ADT node — atomically dec's the RC and, on
/// last-ref, frees the outer allocation ONLY without walking fields.
///
/// This is the IO-trampoline dual of the transitive `consume_io_tree`
/// (§3.5.4): used when the trampoline releases its reference to a
/// Pure/Effect/Bind/Par node whose field pointers have already been re-owned
/// by other holders (Bind's inner → new `current`; Bind's continuation →
/// `cont_stack`; Par's branches → consumed by rayon dispatch). A transitive
/// walk here would double-dec those sub-references.
///
/// Semantically equivalent to `rc::consume_shallow` (both perform a shallow
/// last-ref dec + dealloc); this helper is exposed as a distinct primitive
/// because the caller's ownership story is specific to tree-walking state
/// machines where fields are transferred elsewhere before the outer node is
/// released (Decision 29). Reusing `consume_shallow` would work
/// operationally, but naming it `dec_shallow_io` documents the
/// ownership-transfer-then-drop pattern at the call site.
///
/// Also safe to call on SNil-style bare nullary tags — returns without
/// touching memory for values below `NULLARY_TAG_THRESHOLD`.
///
/// # Safety
/// `ptr` must be either a valid IO ADT heap pointer with `rc > 0`, or a
/// bare nullary tag. Fields at offsets 24/32/… must NOT still be owned
/// solely through this pointer — the caller is asserting that every
/// heap-typed field has already been re-owned elsewhere.
pub fn dec_shallow_io(ptr: i64) {
    if ptr < NULLARY_THRESHOLD {
        return;
    }
    // SAFETY: caller guarantees `ptr` is a valid heap base with rc > 0.
    let old_rc = unsafe { atomic_dec_rc(ptr) };
    if old_rc != 1 {
        return; // other references remain; outer allocation stays live.
    }
    std::sync::atomic::fence(Ordering::Acquire);
    // Last ref — free the outer allocation only. Fields are intentionally
    // NOT walked; the caller has transferred ownership of every heap-typed
    // field to another holder (see §3.5.4).
    unsafe { alloc::dealloc(ptr as *mut u8) };
}

// ---------------------------------------------------------------------------
// Closure consumption
// ---------------------------------------------------------------------------

/// HeapClosure layout: `[header(16) | code_ptr(16) | drop_glue_ptr(24) | captures(32..)]`
const CLOSURE_DROP_GLUE_OFFSET: usize = 24;

/// Consume a closure: atomically dec RC, and if last ref invoke the
/// embedded drop glue function pointer (which dec's each heap-typed
/// capture) before deallocating.
///
/// This mirrors the backend's `emit_closure_dec_inline`.
///
/// # Safety
/// `ptr` must be a valid closure heap pointer (rc > 0) or bare nullary tag.
pub fn consume_closure(ptr: i64) {
    if ptr < NULLARY_THRESHOLD {
        return;
    }
    let drop_glue_ptr = unsafe { read_i64(ptr, CLOSURE_DROP_GLUE_OFFSET) };

    let old_rc = unsafe { atomic_dec_rc(ptr) };
    if old_rc != 1 {
        return;
    }
    std::sync::atomic::fence(Ordering::Acquire);

    // If the closure has captures, call the backend-generated drop-glue
    // function (signature: fn(closure_ptr) -> ()).
    if drop_glue_ptr != 0 {
        let drop_fn: extern "C" fn(i64) =
            unsafe { std::mem::transmute(drop_glue_ptr as *const ()) };
        drop_fn(ptr);
    }
    unsafe { alloc::dealloc(ptr as *mut u8) };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::alloc::{alloc_count, alloc_with_rc, dealloc_count};
    use crate::heap_string::alloc_string;
    use cranelisp_types::TAG_SCONS;

    // Helpers -----------------------------------------------------------------

    fn alloc_slot(payload: usize) -> i64 {
        alloc_with_rc(payload) as i64
    }

    fn write_field(base: i64, offset: usize, value: i64) {
        unsafe {
            *((base as *mut u8).add(offset) as *mut i64) = value;
        }
    }

    fn make_scons(head: i64, tail: i64) -> i64 {
        let base = alloc_slot(24); // tag + head + tail = 24
        write_field(base, TAG_OFFSET, TAG_SCONS);
        write_field(base, FIELD0_OFFSET, head);
        write_field(base, FIELD1_OFFSET, tail);
        base
    }

    fn make_sexp_str(s_ptr: i64) -> i64 {
        let base = alloc_slot(16); // tag + sval = 16
        write_field(base, TAG_OFFSET, TAG_SEXP_STR);
        write_field(base, FIELD0_OFFSET, s_ptr);
        base
    }

    fn make_sexp_sym(s_ptr: i64) -> i64 {
        let base = alloc_slot(16);
        write_field(base, TAG_OFFSET, TAG_SEXP_SYM);
        write_field(base, FIELD0_OFFSET, s_ptr);
        base
    }

    fn make_sexp_list(items: i64) -> i64 {
        let base = alloc_slot(16);
        write_field(base, TAG_OFFSET, TAG_SEXP_LIST);
        write_field(base, FIELD0_OFFSET, items);
        base
    }

    fn make_vec_struct(cap: i64) -> (i64, *mut i64) {
        let base = alloc_slot(24); // len + cap + data_ptr
        write_field(base, VEC_LEN_OFFSET, 0);
        write_field(base, VEC_CAP_OFFSET, cap);
        let data: *mut i64 = if cap > 0 {
            let byte_size = cap as usize * 8;
            let layout = std::alloc::Layout::from_size_align(byte_size, 8).unwrap();
            unsafe { std::alloc::alloc_zeroed(layout) as *mut i64 }
        } else {
            std::ptr::null_mut()
        };
        write_field(base, VEC_DATA_PTR_OFFSET, data as i64);
        (base, data)
    }

    // Tests -----------------------------------------------------------------

    // spec: design/arch/CLAUDE.md Decision 24 — consume_slist frees a shallow chain
    #[test]
    fn decision24_consume_slist_frees_chain() {
        let allocs = alloc_count();
        let deallocs = dealloc_count();

        // Build SCons(SexpInt-style scalar, SCons(SexpInt, SNil)). We use
        // SexpInt because it has no heap sub-refs.
        let int0 = alloc_slot(16);
        write_field(int0, TAG_OFFSET, 0); // TAG_SEXP_INT
        write_field(int0, FIELD0_OFFSET, 10);

        let int1 = alloc_slot(16);
        write_field(int1, TAG_OFFSET, 0);
        write_field(int1, FIELD0_OFFSET, 20);

        let list = make_scons(int0, make_scons(int1, 0));

        consume_slist(list);

        assert_eq!(alloc_count() - allocs, 4); // 2 SCons + 2 SexpInt
        assert_eq!(dealloc_count() - deallocs, 4);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consume_sexp frees heap fields
    #[test]
    fn decision24_consume_sexp_sym_frees_string() {
        let allocs = alloc_count();
        let deallocs = dealloc_count();

        let name = alloc_string(b"hello") as i64;
        let sym = make_sexp_sym(name);
        consume_sexp(sym);

        assert_eq!(alloc_count() - allocs, 2); // string + sym
        assert_eq!(dealloc_count() - deallocs, 2);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consume_sexp of SexpList recurses
    #[test]
    fn decision24_consume_sexp_list_recurses() {
        let allocs = alloc_count();
        let deallocs = dealloc_count();

        let s1 = alloc_string(b"foo") as i64;
        let sym1 = make_sexp_sym(s1);
        let s2 = alloc_string(b"bar") as i64;
        let sym2 = make_sexp_str(s2);
        let list = make_scons(sym1, make_scons(sym2, 0));
        let sexp_list = make_sexp_list(list);

        consume_sexp(sexp_list);
        // 2 strings + 2 Sexp wrappers + 2 SCons + 1 SexpList = 7
        assert_eq!(alloc_count() - allocs, 7);
        assert_eq!(dealloc_count() - deallocs, 7);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consume_sexp preserves shared refs
    #[test]
    fn decision24_consume_sexp_preserves_shared_ref() {
        let allocs = alloc_count();
        let deallocs = dealloc_count();

        let s = alloc_string(b"shared") as i64;
        let sym = make_sexp_sym(s);

        // Simulate a second reference (rc 1 -> 2).
        unsafe {
            let rc_ptr = &*((sym as *const u8).add(HeapHeader::RC_OFFSET as usize)
                as *const AtomicI64);
            rc_ptr.fetch_add(1, Ordering::Release);
        }

        consume_sexp(sym); // dec rc to 1 — must NOT free

        assert_eq!(alloc_count() - allocs, 2);
        assert_eq!(dealloc_count() - deallocs, 0, "shared ref must not be freed");

        // Clean up manually.
        consume_sexp(sym);
        assert_eq!(dealloc_count() - deallocs, 2);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consume_vec_of_string frees elements
    #[test]
    fn decision24_consume_vec_of_string_frees_elements() {
        let allocs = alloc_count();
        let deallocs = dealloc_count();

        let (vec, data) = make_vec_struct(3);
        unsafe {
            *data = alloc_string(b"a") as i64;
            *data.add(1) = alloc_string(b"b") as i64;
            *data.add(2) = alloc_string(b"c") as i64;
        }
        write_field(vec, VEC_LEN_OFFSET, 3);

        consume_vec_of_string(vec);
        assert_eq!(alloc_count() - allocs, 4); // vec struct + 3 strings
        assert_eq!(dealloc_count() - deallocs, 4);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consume_io_tree Pure is scalar
    #[test]
    fn decision24_consume_io_pure_frees_node() {
        let allocs = alloc_count();
        let deallocs = dealloc_count();
        let base = alloc_slot(16); // tag + payload
        write_field(base, TAG_OFFSET, IO_TAG_PURE);
        write_field(base, FIELD0_OFFSET, 42);
        consume_io_tree(base);
        assert_eq!(alloc_count() - allocs, 1);
        assert_eq!(dealloc_count() - deallocs, 1);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consume_io_tree Bind recurses
    #[test]
    fn decision24_consume_io_bind_recurses_into_inner() {
        let allocs = alloc_count();
        let deallocs = dealloc_count();

        // Inner Pure node.
        let inner = alloc_slot(16);
        write_field(inner, TAG_OFFSET, IO_TAG_PURE);
        write_field(inner, FIELD0_OFFSET, 42);

        // Continuation closure: [header | code_ptr | drop_glue_ptr=0]
        let cont = alloc_slot(16);
        write_field(cont, 16, 0); // code_ptr (not invoked)
        write_field(cont, 24, 0); // drop_glue_ptr = 0

        // Bind node.
        let bind = alloc_slot(24); // tag + inner + cont
        write_field(bind, TAG_OFFSET, IO_TAG_BIND);
        write_field(bind, FIELD0_OFFSET, inner);
        write_field(bind, FIELD1_OFFSET, cont);

        consume_io_tree(bind);
        assert_eq!(alloc_count() - allocs, 3);
        assert_eq!(dealloc_count() - deallocs, 3);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consume_io_tree Par dec's each branch
    #[test]
    fn decision24_consume_io_par_walks_branches() {
        let allocs = alloc_count();
        let deallocs = dealloc_count();

        // Build two Pure branches.
        let b0 = alloc_slot(16);
        write_field(b0, TAG_OFFSET, IO_TAG_PURE);
        write_field(b0, FIELD0_OFFSET, 1);
        let b1 = alloc_slot(16);
        write_field(b1, TAG_OFFSET, IO_TAG_PURE);
        write_field(b1, FIELD0_OFFSET, 2);

        // Par node: tag + count + 2 branches = 32 bytes payload.
        let par = alloc_slot(32);
        write_field(par, TAG_OFFSET, IO_TAG_PAR);
        write_field(par, FIELD0_OFFSET, 2); // count
        write_field(par, FIELD1_OFFSET, b0);
        write_field(par, FIELD1_OFFSET + 8, b1);

        consume_io_tree(par);
        assert_eq!(alloc_count() - allocs, 3);
        assert_eq!(dealloc_count() - deallocs, 3);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consume_closure frees bare closure
    #[test]
    fn decision24_consume_closure_bare() {
        let allocs = alloc_count();
        let deallocs = dealloc_count();
        // Bare closure: no captures, drop_glue_ptr=0.
        let c = alloc_slot(16); // code_ptr + drop_glue_ptr
        write_field(c, 16, 0);
        write_field(c, 24, 0);
        consume_closure(c);
        assert_eq!(alloc_count() - allocs, 1);
        assert_eq!(dealloc_count() - deallocs, 1);
    }

    // spec: design/arch/CLAUDE.md Decision 29 — dec_shallow_io frees outer only
    #[test]
    fn dec_shallow_io_frees_outer_only() {
        let allocs = alloc_count();
        let deallocs = dealloc_count();

        // Build a Bind node that points at an inner Pure and a continuation
        // closure. `dec_shallow_io` must free ONLY the Bind node, leaving the
        // inner Pure and the continuation untouched (they are the
        // transferred-out subfields, still held by other logical owners).
        let inner = alloc_slot(16);
        write_field(inner, TAG_OFFSET, IO_TAG_PURE);
        write_field(inner, FIELD0_OFFSET, 42);

        let cont = alloc_slot(16);
        write_field(cont, 16, 0); // code_ptr placeholder
        write_field(cont, 24, 0); // drop_glue_ptr = 0

        let bind = alloc_slot(24);
        write_field(bind, TAG_OFFSET, IO_TAG_BIND);
        write_field(bind, FIELD0_OFFSET, inner);
        write_field(bind, FIELD1_OFFSET, cont);

        dec_shallow_io(bind);

        // Exactly one alloc was deallocated (the Bind node); inner + cont are
        // still live and owned by the test.
        assert_eq!(alloc_count() - allocs, 3, "three allocs expected");
        assert_eq!(
            dealloc_count() - deallocs,
            1,
            "dec_shallow_io must not walk fields"
        );

        // Clean up the leftover allocations so the test doesn't leak.
        unsafe {
            alloc::dealloc(inner as *mut u8);
            alloc::dealloc(cont as *mut u8);
        }
        assert_eq!(dealloc_count() - deallocs, 3);
    }

    // spec: design/arch/CLAUDE.md Decision 29 — dec_shallow_io skips nullary tags
    #[test]
    fn dec_shallow_io_skips_nullary() {
        let allocs = alloc_count();
        let deallocs = dealloc_count();
        dec_shallow_io(0);
        dec_shallow_io(1);
        dec_shallow_io(NULLARY_THRESHOLD - 1);
        assert_eq!(alloc_count() - allocs, 0);
        assert_eq!(dealloc_count() - deallocs, 0);
    }

    // spec: design/arch/CLAUDE.md Decision 29 — dec_shallow_io preserves shared refs
    #[test]
    fn dec_shallow_io_preserves_shared_reference() {
        let allocs = alloc_count();
        let deallocs = dealloc_count();

        let node = alloc_slot(16);
        write_field(node, TAG_OFFSET, IO_TAG_PURE);
        write_field(node, FIELD0_OFFSET, 99);

        // Simulate a second reference (rc: 1 -> 2).
        unsafe {
            let rc_ptr = &*((node as *const u8).add(HeapHeader::RC_OFFSET as usize)
                as *const AtomicI64);
            rc_ptr.fetch_add(1, Ordering::Release);
        }

        dec_shallow_io(node); // rc: 2 -> 1, no free
        assert_eq!(alloc_count() - allocs, 1);
        assert_eq!(
            dealloc_count() - deallocs,
            0,
            "dec_shallow_io must not free when other refs exist"
        );

        // Clean up the remaining reference.
        dec_shallow_io(node);
        assert_eq!(dealloc_count() - deallocs, 1);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — nullary tag is a no-op
    #[test]
    fn decision24_consume_slist_skips_nullary() {
        let allocs = alloc_count();
        let deallocs = dealloc_count();
        consume_slist(0); // SNil
        consume_sexp(0);
        consume_vec_of_string(0);
        consume_io_tree(0);
        consume_closure(0);
        assert_eq!(alloc_count() - allocs, 0);
        assert_eq!(dealloc_count() - deallocs, 0);
    }
}

// ---------------------------------------------------------------------------
// RC-balance harvest (FIXME 0129 — ports tests/legacy/rc_alloc_trace.rs)
// ---------------------------------------------------------------------------
//
// Harvested from `tests/legacy/rc_alloc_trace.rs` (Sprint 64 quarantine,
// FIXME 0129). The quarantined file's 38 `assert_rc_balanced` tests ran a
// whole compiled program under `CRANELISP_RC_TRACE=1` and parsed stderr
// alloc/free trace lines to assert the counter pair was balanced. That whole-
// program path is the e2e tier (the language-observable "heap-using bodies run
// cleanly" property is preserved in `tests/spec_12_runtime.rs`); the Rust-
// internal slice 0129 names — "alloc count == dealloc count for every category
// of heap value" at the runtime allocator — is ported HERE, where the counters
// (`crate::alloc`) and the drop glue (this module) actually live.
//
// These tests assemble each named heap-value category with the real runtime
// alloc + the real drop-glue consumers, then assert EXACT parity through the
// shared `assert_balanced` helper — the crate-internal analogue of the legacy
// `assert_rc_balanced`. They are stronger than the legacy `>=` checks: a leak
// (alloc without matching dealloc) OR a double-free (extra dealloc) fails the
// equality. Representatives per FIXME 0129's invariant-cluster list:
//
//   - ADT heap field freed with container (product + sum)         [rc_balance_adt_*]
//   - String alloc/dealloc balance (via the Sexp/SList carriers)  [rc_balance_string_*]
//   - Closure environment freed (single + multiple capture)       [rc_balance_closure_*]
//   - Vec COW preserves alloc count when both buffers freed        [rc_balance_vec_cow]
//   - Nested ADT (Sexp-list-of-Sexp) recursive RC                 [rc_balance_nested]
//   - Lambda unused-heap-param freed (consuming convention)       [rc_balance_consume_*]
#[cfg(test)]
mod rc_balance {
    use super::*;
    use crate::alloc::{alloc_count, alloc_with_rc, dealloc_count};
    use crate::heap_string::alloc_string;
    use crate::vec_runtime::{vec_drop, vec_new, vec_set_copy};
    use cranelisp_types::{TAG_SCONS, TAG_SEXP_LIST, TAG_SEXP_STR};

    const TAG_OFF: usize = TAG_OFFSET;
    const F0_OFF: usize = FIELD0_OFFSET;
    const F1_OFF: usize = FIELD1_OFFSET;

    /// Run `build`, capture the allocations it produced, run `release`, and
    /// assert the runtime allocator saw exactly as many deallocs as allocs.
    /// This is the crate-internal stand-in for the legacy `assert_rc_balanced`.
    fn assert_balanced<T>(build: impl FnOnce() -> T, release: impl FnOnce(T)) {
        let allocs_before = alloc_count();
        let deallocs_before = dealloc_count();
        let handle = build();
        let allocated = alloc_count() - allocs_before;
        assert!(allocated > 0, "harness error: build allocated nothing to balance");
        release(handle);
        let deallocated = dealloc_count() - deallocs_before;
        assert_eq!(
            allocated, deallocated,
            "RC imbalance: {allocated} allocs but {deallocated} deallocs"
        );
    }

    fn write_field(base: i64, offset: usize, value: i64) {
        // SAFETY: `base` is a live alloc with room for the offset (asserted by
        // the payload size each builder requests).
        unsafe { *((base as *mut u8).add(offset) as *mut i64) = value };
    }

    /// `extern "C" fn(i64) -> i64` element-dec for `vec_drop`, which transmutes
    /// `elem_dec_fn` to exactly this ABI. `rc::consume_shallow` is a Rust-ABI
    /// `fn(i64)` and cannot be passed directly — this is the ABI-correct shim.
    extern "C" fn consume_string_elem(ptr: i64) -> i64 {
        rc::consume_shallow(ptr);
        0
    }

    fn make_sexp_str(s_ptr: i64) -> i64 {
        let base = alloc_with_rc(16) as i64; // tag + sval
        write_field(base, TAG_OFF, TAG_SEXP_STR);
        write_field(base, F0_OFF, s_ptr);
        base
    }

    fn make_scons(head: i64, tail: i64) -> i64 {
        let base = alloc_with_rc(24) as i64; // tag + head + tail
        write_field(base, TAG_OFF, TAG_SCONS);
        write_field(base, F0_OFF, head);
        write_field(base, F1_OFF, tail);
        base
    }

    // spec: spec/12-runtime.md §12.3 — ADT sum (Some "x") frees its String
    // field with the container. Legacy `rc_mixed_adt_some_drop_balanced`.
    #[test]
    fn rc_balance_adt_sum_with_string_field() {
        assert_balanced(
            || make_sexp_str(alloc_string(b"hello") as i64),
            consume_sexp,
        );
    }

    // spec: spec/12-runtime.md §12.3 — product ADT with two String fields:
    // both fields freed with the container. Legacy `rc_u1_3_pair_of_strings`.
    #[test]
    fn rc_balance_adt_product_two_string_fields() {
        // Model a 2-field product as a SexpList over an SList of two SexpStr
        // wrappers — both String fields and both wrappers must be released.
        assert_balanced(
            || {
                let s1 = make_sexp_str(alloc_string(b"hello") as i64);
                let s2 = make_sexp_str(alloc_string(b"world") as i64);
                let list = make_scons(s1, make_scons(s2, 0));
                let base = alloc_with_rc(16) as i64; // SexpList: tag + items
                write_field(base, TAG_OFF, TAG_SEXP_LIST);
                write_field(base, F0_OFF, list);
                base
            },
            consume_sexp,
        );
    }

    // spec: spec/12-runtime.md §12.3 — nested ADT (list of two heap Sexps):
    // recursive RC walk frees every node. Legacy `rc_adt_nested_option` /
    // `rc_u1_3_*` recursive-RC cohort.
    #[test]
    fn rc_balance_nested_recursive() {
        assert_balanced(
            || {
                let a = make_sexp_str(alloc_string(b"a") as i64);
                let b = make_sexp_str(alloc_string(b"b") as i64);
                let c = make_sexp_str(alloc_string(b"c") as i64);
                make_scons(a, make_scons(b, make_scons(c, 0)))
            },
            consume_slist,
        );
    }

    // spec: spec/12-runtime.md §12.3 — closure environment freed on drop. A
    // bare (capture-less) closure: env struct is released. Legacy
    // `rc_closure_no_capture` / `rc_closure_env_alloc`.
    #[test]
    fn rc_balance_closure_env() {
        assert_balanced(
            || {
                let c = alloc_with_rc(16) as i64; // code_ptr + drop_glue_ptr
                write_field(c, 16, 0); // code_ptr
                write_field(c, 24, 0); // drop_glue_ptr = 0 (no captures)
                c
            },
            consume_closure,
        );
    }

    // spec: spec/12-runtime.md §12.3 — closure capturing a heap String, with
    // backend-style inline drop glue that dec's the capture, frees both the
    // env and the captured String. Legacy `rc_closure_captures_string_balanced`.
    #[test]
    fn rc_balance_closure_captures_string() {
        // Drop glue mirrors the backend's emitted glue: dec the capture at
        // offset 32 (first capture slot), then return.
        extern "C" fn drop_glue_one_string_capture(closure_ptr: i64) {
            // SAFETY: closure_ptr is the live env; the capture i64 lives at +32.
            let capture = unsafe { read_i64(closure_ptr, 32) };
            rc::consume_shallow(capture);
        }
        assert_balanced(
            || {
                let s = alloc_string(b"captured") as i64;
                let c = alloc_with_rc(24) as i64; // code_ptr + drop_glue + 1 capture
                write_field(c, 16, 0); // code_ptr
                write_field(c, 24, drop_glue_one_string_capture as *const () as i64);
                write_field(c, 32, s); // capture slot 0
                c
            },
            consume_closure,
        );
    }

    // spec: spec/12-runtime.md §12.3 — closure capturing two heap Strings:
    // both captures freed by the glue. Legacy
    // `rc_u1_5_closure_captures_multiple_heap_values`.
    #[test]
    fn rc_balance_closure_multiple_captures() {
        extern "C" fn drop_glue_two_string_captures(closure_ptr: i64) {
            // SAFETY: two captures at +32 and +40.
            let c0 = unsafe { read_i64(closure_ptr, 32) };
            let c1 = unsafe { read_i64(closure_ptr, 40) };
            rc::consume_shallow(c0);
            rc::consume_shallow(c1);
        }
        assert_balanced(
            || {
                let a = alloc_string(b"hello") as i64;
                let b = alloc_string(b"world") as i64;
                let c = alloc_with_rc(32) as i64; // code + glue + 2 captures
                write_field(c, 16, 0);
                write_field(c, 24, drop_glue_two_string_captures as *const () as i64);
                write_field(c, 32, a);
                write_field(c, 40, b);
                c
            },
            consume_closure,
        );
    }

    /// Write the three Vec struct fields directly: len, cap, data_ptr. Element
    /// payloads are written through the data buffer `vec_new` already allocated.
    fn fill_int_vec(v: i64, elems: &[i64]) {
        // SAFETY: `v` is a live Vec struct from `vec_new(cap)` with cap >= len;
        // the data buffer it owns has room for `elems.len()` i64s.
        unsafe {
            let data = read_i64(v, VEC_DATA_PTR_OFFSET) as *mut i64;
            for (i, e) in elems.iter().enumerate() {
                *data.add(i) = *e;
            }
            *((v as *mut u8).add(VEC_LEN_OFFSET) as *mut i64) = elems.len() as i64;
        }
    }

    // spec: spec/12-runtime.md §12.3.3 — Vec copy-on-write: after vec-set-copy
    // the original and the copied Vec are distinct STRUCT allocations and BOTH
    // must be freed (no shared-buffer double-free, no leak). Only the two Vec
    // structs are RC-tracked; the data buffers use the untracked plain
    // allocator. Legacy `rc_vec_set_copy`.
    #[test]
    fn rc_balance_vec_cow_set() {
        let allocs_before = alloc_count();
        let deallocs_before = dealloc_count();

        // Build a 3-element Int Vec, then vec-set-copy produces a second,
        // independent Vec (COW). Int elements are NeverHeap (null elem fns).
        let v = vec_new(3); // 1 tracked struct alloc
        fill_int_vec(v, &[1, 2, 3]);
        let allocs_after_first = alloc_count();
        let v2 = vec_set_copy(v, 1, 99, 0); // 1 more tracked struct alloc
        assert_ne!(v, v2, "vec-set-copy must produce a distinct allocation (COW)");
        assert_eq!(
            alloc_count() - allocs_after_first,
            1,
            "vec-set-copy must allocate exactly one new Vec struct"
        );

        // Both Vecs are live and independent. Free both — exact struct balance.
        vec_drop(v, 0);
        vec_drop(v2, 0);

        let allocated = alloc_count() - allocs_before;
        let deallocated = dealloc_count() - deallocs_before;
        assert_eq!(
            allocated, deallocated,
            "Vec COW imbalance: {allocated} struct allocs but {deallocated} struct deallocs"
        );
    }

    // spec: spec/12-runtime.md §12.3 — Vec of heap Strings: element Strings are
    // freed with the Vec. The Vec struct + 3 Strings are RC-tracked; the data
    // buffer is not. Legacy `rc_vec_of_strings`.
    #[test]
    fn rc_balance_vec_of_strings() {
        let allocs_before = alloc_count();
        let deallocs_before = dealloc_count();

        let v = vec_new(3); // 1 tracked struct alloc
        let strs = [
            alloc_string(b"a") as i64,
            alloc_string(b"b") as i64,
            alloc_string(b"c") as i64,
        ]; // 3 tracked string allocs
        fill_int_vec(v, &strs);
        // Drop the Vec with the String element-dec fn so each element is freed.
        vec_drop(v, consume_string_elem as *const () as i64);

        let allocated = alloc_count() - allocs_before;
        let deallocated = dealloc_count() - deallocs_before;
        assert_eq!(
            allocated, deallocated,
            "Vec-of-strings imbalance: {allocated} allocs (struct + 3 strings) but {deallocated} deallocs"
        );
    }

    // spec: spec/12-runtime.md §12.3 — consuming convention: an extern that
    // receives a heap arg it does not return MUST release it (callee owns heap
    // params). Legacy `rc_lambda_unused_string_param_freed` /
    // `rc_defn_unused_string_param_freed`.
    #[test]
    fn rc_balance_consume_unused_string_param() {
        assert_balanced(
            || alloc_string(b"hello") as i64,
            rc::consume_shallow,
        );
    }

    // spec: spec/12-runtime.md §12.3 — multiple unused heap params each freed.
    // Legacy `rc_lambda_multiple_unused_heap_params_freed`.
    #[test]
    fn rc_balance_consume_multiple_unused_params() {
        let allocs_before = alloc_count();
        let deallocs_before = dealloc_count();
        let a = alloc_string(b"x") as i64;
        let b = alloc_string(b"y") as i64;
        rc::consume_shallow(a);
        rc::consume_shallow(b);
        assert_eq!(alloc_count() - allocs_before, 2);
        assert_eq!(dealloc_count() - deallocs_before, 2);
    }
}
