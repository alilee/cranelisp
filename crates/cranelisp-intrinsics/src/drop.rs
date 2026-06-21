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
mod tests;

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
mod rc_balance;
