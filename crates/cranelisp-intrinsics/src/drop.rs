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
//!   an SList field; SexpAnnotated has two Sexp fields)
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

use cranelisp_platform::{
    IO_PURE_GLUE_OFFSET, IO_TAG_BIND, IO_TAG_EFFECT, IO_TAG_EFFECT_POLL, IO_TAG_LAUNCH, IO_TAG_PAR,
    IO_TAG_PURE, IO_TAG_SELECT,
};
use cranelisp_types::{
    HeapHeader, NULLARY_TAG_THRESHOLD, TAG_SEXP_ANNOTATED, TAG_SEXP_BOOL, TAG_SEXP_BRACKET,
    TAG_SEXP_FLOAT, TAG_SEXP_INT, TAG_SEXP_LIST, TAG_SEXP_STR, TAG_SEXP_SYM,
};

use crate::alloc;
use crate::heap_access;
use crate::rc;
// Vec layout authority — the blessed, `const _: () = assert!(…)`-locked offsets
// (FIXME 0245). This module reads them; it does not restate them.
use crate::vec_runtime::{CAP_OFFSET, DATA_PTR_OFFSET, LEN_OFFSET};

/// NULLARY_TAG_THRESHOLD as i64 for comparison with pointer values.
const NULLARY_THRESHOLD: i64 = NULLARY_TAG_THRESHOLD as i64;

// ---------------------------------------------------------------------------
// Heap field access
// ---------------------------------------------------------------------------

// ADT field geometry (NOT Vec layout — that is `vec_runtime`'s). Derived from
// the header-layout authority `cranelisp_types::HeapHeader` rather than
// restating `16` (Principle 7 — this file had the third magic-number copy of the
// header size). `isize` so they feed `heap_access`'s offset type directly, so
// the `usize`→`isize` adaptation happens ONCE, here, not at thirteen call sites.
const TAG_OFFSET: isize = HeapHeader::SIZE as isize;
const FIELD0_OFFSET: isize = TAG_OFFSET + 8;
const FIELD1_OFFSET: isize = TAG_OFFSET + 16;
const PURE_STATE_OFFSET: isize = HeapHeader::SIZE as isize + IO_PURE_GLUE_OFFSET as isize;
const _: () = assert!(PURE_STATE_OFFSET == FIELD1_OFFSET);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum PurePayloadState {
    Scalar,
    Claimed,
    Owned(i64),
}

impl PurePayloadState {
    fn decode(raw: i64) -> Self {
        match raw {
            0 => Self::Scalar,
            1 => Self::Claimed,
            glue => Self::Owned(glue),
        }
    }
}

/// Atomically replace a published Pure node's payload witness with `Claimed`.
///
/// # Safety
/// `ptr` must be a live `IO_TAG_PURE` node using the ABI-10 three-word payload.
pub(crate) unsafe fn swap_pure_payload_to_claimed(ptr: i64) -> PurePayloadState {
    // SAFETY: the caller establishes the Pure shape before this offset is
    // formed. ABI 10 makes the field an aligned i64 at absolute offset 32, and
    // every post-publication access to it is atomic.
    let state =
        unsafe { &*((ptr as *const u8).add(PURE_STATE_OFFSET as usize) as *const AtomicI64) };
    PurePayloadState::decode(state.swap(1, Ordering::AcqRel))
}

/// Read a published Pure node's payload-witness state without changing it.
///
/// # Safety
/// `ptr` must be a live `IO_TAG_PURE` node using the ABI-10 three-word payload.
unsafe fn load_pure_payload_state(ptr: i64) -> PurePayloadState {
    // SAFETY: same ABI-10 shape and alignment contract as the swap helper.
    let state =
        unsafe { &*((ptr as *const u8).add(PURE_STATE_OFFSET as usize) as *const AtomicI64) };
    PurePayloadState::decode(state.load(Ordering::Acquire))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum IoTag {
    Pure,
    Effect,
    Bind,
    Par,
    EffectPoll,
    Launch,
    Select,
    Unknown(i64),
}

impl IoTag {
    fn decode(raw: i64) -> Self {
        match raw {
            IO_TAG_PURE => Self::Pure,
            IO_TAG_EFFECT => Self::Effect,
            IO_TAG_BIND => Self::Bind,
            IO_TAG_PAR => Self::Par,
            IO_TAG_EFFECT_POLL => Self::EffectPoll,
            IO_TAG_LAUNCH => Self::Launch,
            IO_TAG_SELECT => Self::Select,
            other => Self::Unknown(other),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SexpTag {
    Int,
    Float,
    Bool,
    Str,
    Sym,
    List,
    Bracket,
    Annotated,
    Unknown(i64),
}

impl SexpTag {
    fn decode(raw: i64) -> Self {
        match raw {
            TAG_SEXP_INT => Self::Int,
            TAG_SEXP_FLOAT => Self::Float,
            TAG_SEXP_BOOL => Self::Bool,
            TAG_SEXP_STR => Self::Str,
            TAG_SEXP_SYM => Self::Sym,
            TAG_SEXP_LIST => Self::List,
            TAG_SEXP_BRACKET => Self::Bracket,
            TAG_SEXP_ANNOTATED => Self::Annotated,
            other => Self::Unknown(other),
        }
    }
}

#[derive(Clone, Copy)]
enum SexpFieldKind {
    Shallow,
    SList,
    Sexp,
}

#[derive(Clone, Copy)]
struct SexpField {
    offset: isize,
    kind: SexpFieldKind,
}

const NO_SEXP_FIELDS: &[SexpField] = &[];
const SHALLOW_SEXP_FIELD: &[SexpField] = &[SexpField {
    offset: FIELD0_OFFSET,
    kind: SexpFieldKind::Shallow,
}];
const SLIST_SEXP_FIELD: &[SexpField] = &[SexpField {
    offset: FIELD0_OFFSET,
    kind: SexpFieldKind::SList,
}];
const ANNOTATED_SEXP_FIELDS: &[SexpField] = &[
    SexpField {
        offset: FIELD0_OFFSET,
        kind: SexpFieldKind::Sexp,
    },
    SexpField {
        offset: FIELD1_OFFSET,
        kind: SexpFieldKind::Sexp,
    },
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum IoDisposition {
    Structural,
    SpineTransferred,
}

#[derive(Clone, Copy)]
enum IoFieldKind {
    IoTree,
    NonZeroIoTree,
    Closure,
    InlineIoBranches,
    IoBranchVec,
}

#[derive(Clone, Copy)]
struct IoField {
    offset: isize,
    kind: IoFieldKind,
}

const NO_IO_FIELDS: &[IoField] = &[];
const BIND_FIELDS: &[IoField] = &[
    IoField {
        offset: FIELD0_OFFSET,
        kind: IoFieldKind::IoTree,
    },
    IoField {
        offset: FIELD1_OFFSET,
        kind: IoFieldKind::Closure,
    },
];
const PAR_FIELDS: &[IoField] = &[IoField {
    offset: FIELD0_OFFSET,
    kind: IoFieldKind::InlineIoBranches,
}];
const POLL_FIELDS: &[IoField] = &[IoField {
    offset: FIELD0_OFFSET,
    kind: IoFieldKind::Closure,
}];
const LAUNCH_FIELDS: &[IoField] = &[IoField {
    offset: FIELD0_OFFSET,
    kind: IoFieldKind::NonZeroIoTree,
}];
const SELECT_FIELDS: &[IoField] = &[IoField {
    offset: FIELD0_OFFSET,
    kind: IoFieldKind::IoBranchVec,
}];

// The raw `*(base + off)` primitive is `heap_access::{read_i64, write_i64}` —
// the single mechanical owner (MED-1 / FIXME 0370 / 0850). This module used to
// carry a private `read_i64` twin with a `usize` offset; it is deleted, and
// every read below goes through the owner the crate's `CLAUDE.md` already
// declared. `heap_access` does NOT own the header layout (`HeapHeader`) nor the
// Vec layout (`vec_runtime`) nor the consuming dec sequences (per-module by
// design) — only the accessor.

/// Atomically decrement the RC at `ptr` with Release ordering.
/// Returns the OLD RC value.
///
/// # Safety
/// `ptr` must be a valid heap pointer with `rc > 0`.
#[inline]
unsafe fn atomic_dec_rc(ptr: i64) -> i64 {
    // A3 PREcheck (design §7.5): the env-gated seam validation runs FIRST — before
    // the `fetch_sub` below and before the always-on debug twin. This is the funnel
    // every recursive drop-glue leaf routes through, so the 0633/0638 recursive-free
    // seams inherit validation-before-mutation. Callers have already applied the
    // nullary-tag guard. Off ⇒ one cached bool load (byte-identical-off).
    crate::diagnostics::seam_precheck(ptr, "atomic_dec_rc (drop glue)");
    // FIXME 0494 localization: a dec of an already-freed (stale) heap pointer writes
    // into reclaimed/reused memory (the atomic fetch_sub clobbers a smallbin chunk's
    // freelist pointer) — the UAF-write that surfaces later as `free(): chunks in
    // smallbin corrupted`. Validate liveness at the dec point so we abort AT the
    // stale dec, not tens of allocations later. Layout-neutral (side-table read).
    #[cfg(debug_assertions)]
    debug_assert!(
        alloc::is_live(ptr as usize),
        "STALE RC DEC (drop glue): dec of non-live heap pointer {ptr:#x} — this heap \
         value was already freed and its memory reclaimed; the dec corrupts the \
         reused chunk. (FIXME 0494 bug #2 — free-ownership defect on launched teardown.)"
    );
    // S99 Wave 0 instrumentation + non-atomic-RC probe (byte-identical-off).
    // See `crate::rc` for the switch contract; both gates are cached env reads.
    if rc::rc_stats_enabled() {
        rc::tally_rc_dec();
    }
    let old = if rc::nonatomic_rc_enabled() {
        // S99 measurement-only: NON-ATOMIC dec — UNSOUND above one worker.
        // SAFETY: caller guarantees ptr is a valid heap base with rc > 0.
        unsafe { rc::nonatomic_rc_rmw(ptr, -1) }
    } else {
        // SAFETY: this fn's `# Safety` contract requires `ptr` be a valid heap
        // base with `rc > 0`, and every caller below applies the nullary-tag
        // guard first, so `ptr` is a real allocation base. `RC_OFFSET` (8) lies
        // inside the 16-byte header that `alloc::alloc_with_rc` writes on every
        // allocation, and the base is 8-aligned, so the cell is a valid,
        // correctly-aligned `AtomicI64`. The borrow lives only for the
        // `fetch_sub` below — no other reference to the cell is created here,
        // and concurrent decs go through the same atomic.
        let rc_ptr = unsafe {
            &*((ptr as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const AtomicI64)
        };
        rc_ptr.fetch_sub(1, Ordering::Release)
    };
    debug_assert!(
        old > 0,
        "RC underflow in drop glue: ptr={ptr:#x} had rc={old} before decrement"
    );
    // A3 release-gate (safety-invariants §5): the underflow half fires in the
    // release/`--link` lane too — this is the funnel every recursive drop-glue
    // leaf routes through, so the 0633/0638 recursive-free seams inherit it.
    // Under M2 scrub a stale dec reads a poisoned (wild-negative) rc.
    if crate::diagnostics::rc_check_release_enabled() && old <= 0 {
        crate::diagnostics::seam_hard_fail(&format!(
            "atomic_dec_rc (drop glue): dec of ptr {ptr:#x} with rc={old} <= 0 (stale/poisoned dec)"
        ));
    }
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
        // SAFETY: `ptr` cleared the nullary-tag guard immediately above, so per
        // this fn's `# Safety` contract it is a live SCons base — and the dec
        // below has not run yet, so the reference that brought us here still
        // holds the allocation. An SCons node is `[header | tag@16 | head@24 |
        // tail@32]`, so `FIELD0_OFFSET` (24) is an 8-aligned cell inside it.
        let head = unsafe { heap_access::read_i64(ptr, FIELD0_OFFSET) };
        // SAFETY: same still-owned, pre-dec SCons base as the read above (no
        // mutation between them), and `FIELD1_OFFSET` (32) is that node's tail
        // cell — the last field of the two-field SCons allocation, so also in
        // bounds and 8-aligned. Reading both fields before the dec is what makes
        // the last-ref path sound: the values are in registers by the time the
        // node is freed below.
        let tail = unsafe { heap_access::read_i64(ptr, FIELD1_OFFSET) };

        // SAFETY: `atomic_dec_rc` requires a valid heap base with `rc > 0`.
        // `ptr` passed the nullary-tag guard and, per this fn's `# Safety`
        // contract, names a live SCons node; this call releases exactly the one
        // reference the caller handed us.
        let old_rc = unsafe { atomic_dec_rc(ptr) };
        if old_rc != 1 {
            return; // not last ref — head/tail stay owned by siblings
        }
        std::sync::atomic::fence(Ordering::Acquire);

        // Last ref: recursively release head (Sexp), then dealloc this node,
        // then iterate to tail to avoid unbounded recursion on long chains.
        consume_sexp(head);
        // SAFETY: `old_rc == 1` means this thread just dropped the final
        // reference, so no other holder can observe the node; the Acquire fence
        // above orders every prior owner's writes before this free. The dec does
        // not free, so `ptr` is still the un-freed `alloc_with_rc` base this
        // frame owns — exactly `dealloc`'s contract — and `head`/`tail` were
        // copied out before the free.
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
/// - SexpAnnotated (tag 7): field0 and field1 are both `Sexp` values.
///
/// # Safety
/// `ptr` must be a valid Sexp heap pointer (rc > 0) or a bare nullary tag.
pub fn consume_sexp(ptr: i64) {
    if ptr < NULLARY_THRESHOLD {
        return;
    }
    // SAFETY: `atomic_dec_rc` requires a valid heap base with `rc > 0`; `ptr`
    // passed the nullary-tag guard and is a live Sexp node per this fn's
    // `# Safety` contract. This call releases the caller's one reference.
    let old_rc = unsafe { atomic_dec_rc(ptr) };
    if old_rc != 1 {
        return;
    }
    std::sync::atomic::fence(Ordering::Acquire);

    // SAFETY: the zero-observing decrement and Acquire fence make this frame
    // the sole owner of the still-allocated node. Every Sexp node carries its
    // tag directly after the header.
    let tag = SexpTag::decode(unsafe { heap_access::read_i64(ptr, TAG_OFFSET) });
    if let SexpTag::Unknown(unknown) = tag {
        if crate::diagnostics::rc_check_release_enabled() {
            crate::diagnostics::seam_hard_fail(&format!(
                "consume_sexp: unknown Sexp tag {unknown} at ptr {ptr:#x}"
            ));
        }
    }

    for field in sexp_fields(tag) {
        discharge_sexp_field(ptr, *field);
    }

    // SAFETY: reached only with `old_rc == 1`, i.e. this thread dropped the last
    // reference and no other holder can observe the node; the Acquire fence
    // above orders prior owners' writes before the free. Every field declared
    // by the decoded tag has been discharged; unknown tags declare none.
    unsafe { alloc::dealloc(ptr as *mut u8) };
}

fn sexp_fields(tag: SexpTag) -> &'static [SexpField] {
    match tag {
        SexpTag::Int | SexpTag::Float | SexpTag::Bool | SexpTag::Unknown(_) => NO_SEXP_FIELDS,
        SexpTag::Str | SexpTag::Sym => SHALLOW_SEXP_FIELD,
        SexpTag::List | SexpTag::Bracket => SLIST_SEXP_FIELD,
        SexpTag::Annotated => ANNOTATED_SEXP_FIELDS,
    }
}

fn discharge_sexp_field(ptr: i64, field: SexpField) {
    // SAFETY: the closed tag-to-field table names an in-bounds word for the
    // decoded node shape; the last-reference fence has completed.
    let value = unsafe { heap_access::read_i64(ptr, field.offset) };
    match field.kind {
        SexpFieldKind::Shallow => rc::consume_shallow(value),
        SexpFieldKind::SList => consume_slist(value),
        SexpFieldKind::Sexp => consume_sexp(value),
    }
}

// ---------------------------------------------------------------------------
// Vec consumption
// ---------------------------------------------------------------------------

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
    // SAFETY: `atomic_dec_rc` requires a valid heap base with `rc > 0`; `ptr`
    // passed the nullary-tag guard above and, per this fn's `# Safety` contract,
    // is a live Vec-struct base. This call releases the caller's reference.
    let old_rc = unsafe { atomic_dec_rc(ptr) };
    if old_rc != 1 {
        return;
    }
    std::sync::atomic::fence(Ordering::Acquire);

    // SAFETY (whole block): reached only on the last-ref path (`old_rc == 1`),
    // so this thread is the sole owner of a still-allocated Vec struct — the dec
    // does not free; the `alloc::dealloc` at the foot of this block is the one
    // free — and the Acquire fence above orders every prior owner's stores
    // before the reads. Per this fn's `# Safety` contract the base is a Vec
    // struct `[header | len@16 | cap@24 | data_ptr@32]` (`vec_runtime`'s locked
    // offsets), so the three reads are in bounds and 8-aligned. `data` is the
    // `cap * 8` element buffer that struct exclusively owns, so `data.add(i)`
    // for `i < len <= cap` stays inside it; the caller's contract makes
    // `elem_consume` safe on those in-Vec i64s. Both frees are the matching
    // deallocations for the Vec's two allocations (`free_data_buffer` takes the
    // same `data`/`cap` pair just read from the struct; `dealloc` takes the
    // `alloc_with_rc` base), each executed exactly once on this sole-owner path.
    unsafe {
        let base = ptr as *mut u8;
        // Layout authority: `vec_runtime`'s locked offsets. Mechanical access:
        // `heap_access`. Neither is restated here (0850).
        let len = heap_access::read_i64(ptr, LEN_OFFSET as isize);
        let cap = heap_access::read_i64(ptr, CAP_OFFSET as isize);
        let data = heap_access::read_i64(ptr, DATA_PTR_OFFSET as isize) as *mut i64;
        crate::vec_runtime::debug_assert_live_buffer(data as *const i64, cap, "consume_vec_with");

        for i in 0..len as usize {
            let elem = *data.add(i);
            elem_consume(elem);
        }

        // Free the data buffer (plain allocation, not tracked by alloc_with_rc)
        // through the SINGLE vec-data-buffer free path (Principle 7), so the debug
        // untracked-buffer double-free guard sees this crossing too (FIXME 0494).
        crate::vec_runtime::free_data_buffer(data, cap, "consume_vec_with");

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
    // SAFETY: `atomic_dec_rc` requires a valid heap base with `rc > 0`; `ptr`
    // passed the nullary-tag guard and is a live IO node per this fn's
    // `# Safety` contract. This call releases the caller's one reference.
    let old_rc = unsafe { atomic_dec_rc(ptr) };
    if old_rc != 1 {
        return;
    }
    std::sync::atomic::fence(Ordering::Acquire);
    free_io_node_with_disposition(ptr, IoDisposition::Structural);
}

fn io_fields(tag: IoTag, disposition: IoDisposition) -> &'static [IoField] {
    match (tag, disposition) {
        (IoTag::Pure | IoTag::Effect | IoTag::Unknown(_), _) => NO_IO_FIELDS,
        (IoTag::Bind, IoDisposition::Structural) => BIND_FIELDS,
        (IoTag::Bind, IoDisposition::SpineTransferred) => NO_IO_FIELDS,
        (IoTag::Par, _) => PAR_FIELDS,
        (IoTag::EffectPoll, _) => POLL_FIELDS,
        (IoTag::Launch, _) => LAUNCH_FIELDS,
        (IoTag::Select, _) => SELECT_FIELDS,
    }
}

fn discharge_io_field(ptr: i64, field: IoField) {
    match field.kind {
        IoFieldKind::IoTree => {
            // SAFETY: the closed tag-to-field table names an in-bounds word for
            // the decoded node shape; the last-reference fence has completed.
            let value = unsafe { heap_access::read_i64(ptr, field.offset) };
            consume_io_tree(value);
        }
        IoFieldKind::NonZeroIoTree => {
            // SAFETY: same table-owned shape guarantee as the `IoTree` arm.
            let value = unsafe { heap_access::read_i64(ptr, field.offset) };
            if value != 0 {
                consume_io_tree(value);
            }
        }
        IoFieldKind::Closure => {
            // SAFETY: same table-owned shape guarantee as the `IoTree` arm.
            let value = unsafe { heap_access::read_i64(ptr, field.offset) };
            consume_closure(value);
        }
        IoFieldKind::InlineIoBranches => {
            // SAFETY: this kind is declared only for Par: `field.offset` is its
            // count word and the allocation carries exactly that many
            // `(branch, result-disposer)` pairs from `FIELD1_OFFSET`.
            let count = unsafe { heap_access::read_i64(ptr, field.offset) } as usize;
            for index in 0..count {
                // SAFETY: `index < count`; see the Par layout guarantee above.
                let branch =
                    unsafe { heap_access::read_i64(ptr, FIELD1_OFFSET + (index as isize) * 16) };
                consume_io_tree(branch);
            }
        }
        IoFieldKind::IoBranchVec => {
            // SAFETY: this kind is declared only for Select, whose field 0 is
            // the branch-carrier `Vec (IO a)`.
            let value = unsafe { heap_access::read_i64(ptr, field.offset) };
            consume_vec_with(value, consume_io_tree);
        }
    }
}

/// Release the fields and allocation of an IO node whose RC has reached zero.
///
/// The caller must have completed the Release decrement and Acquire fence. This
/// is the sole IO-node teardown tail; it performs no RC operation on `ptr`.
fn free_io_node_with_disposition(ptr: i64, disposition: IoDisposition) {
    // SAFETY: the caller guarantees `ptr` is the still-allocated, solely-owned
    // IO node after the zero-observing decrement and Acquire fence. Every node
    // has the tag word directly after its heap header.
    let raw_tag = unsafe { heap_access::read_i64(ptr, TAG_OFFSET) };
    let tag = IoTag::decode(raw_tag);

    if let IoTag::Unknown(unknown) = tag {
        if crate::diagnostics::rc_check_release_enabled() {
            crate::diagnostics::seam_hard_fail(&format!(
                "free_io_node: unknown IO tag {unknown} at ptr {ptr:#x}"
            ));
        }
    }

    if tag == IoTag::Pure {
        discharge_pure_payload(ptr, disposition);
    }

    for field in io_fields(tag, disposition) {
        discharge_io_field(ptr, *field);
    }

    if tag == IoTag::Pure {
        crate::diagnostics::forget_pure_claim(ptr);
    }

    // SAFETY: `ptr` is still allocated and solely owned; every declared field
    // has now been discharged. Unknown tags retain the conservative historical
    // direction: no field is touched before the outer node is freed.
    unsafe { alloc::dealloc(ptr as *mut u8) };
}

fn discharge_pure_payload(ptr: i64, disposition: IoDisposition) {
    match disposition {
        IoDisposition::Structural => {
            // SAFETY: the caller decoded a live ABI-10 Pure node and owns its
            // zero-count teardown. Competing force and teardown paths use this
            // same exchange, so exactly one can acquire the payload obligation.
            let prior = unsafe { swap_pure_payload_to_claimed(ptr) };
            if let PurePayloadState::Owned(glue) = prior {
                // Read payload only after this teardown won the obligation.
                // SAFETY: field 0 is present on every Pure node and the caller's
                // Acquire fence completed before dispatch.
                let payload = unsafe { heap_access::read_i64(ptr, FIELD0_OFFSET) };
                // SAFETY: every non-zero/non-tombstone witness is the canonical
                // backend-generated `drop<T>` entry with ABI `(i64) -> ()`.
                let drop_payload: extern "C" fn(i64) =
                    unsafe { std::mem::transmute(glue as *const ()) };
                drop_payload(payload);
            }
        }
        IoDisposition::SpineTransferred => {
            // SAFETY: the caller decoded a live ABI-10 Pure node. This path does
            // not mutate the state: only the force path may have transferred it.
            let state = unsafe { load_pure_payload_state(ptr) };
            if state != PurePayloadState::Claimed {
                if crate::diagnostics::rc_check_release_enabled() {
                    crate::diagnostics::seam_hard_fail(&format!(
                        "dec_shallow_io: Pure payload reached SpineTransferred in state {state:?} at ptr {ptr:#x}"
                    ));
                }
                debug_assert!(
                    false,
                    "dec_shallow_io: Pure payload reached SpineTransferred in state {state:?} at ptr {ptr:#x}"
                );
            }
        }
    }
}

/// Backend-callable structural teardown tail for an IO node at RC zero.
///
/// # Safety
/// The caller must have decremented `ptr` from RC 1 to 0 and completed an
/// Acquire fence. `ptr` must still name the allocated IO node.
#[unsafe(export_name = "runtime/free_io_node")]
pub(crate) extern "C" fn free_io_node(ptr: i64) {
    free_io_node_with_disposition(ptr, IoDisposition::Structural);
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
    // SAFETY: `atomic_dec_rc` requires a valid heap base with `rc > 0`; `ptr`
    // passed the nullary-tag guard and is a live IO node per this fn's
    // `# Safety` contract. This call releases the caller's one reference.
    let old_rc = unsafe { atomic_dec_rc(ptr) };
    if old_rc != 1 {
        return; // other references remain; outer allocation stays live.
    }
    std::sync::atomic::fence(Ordering::Acquire);
    free_io_node_with_disposition(ptr, IoDisposition::SpineTransferred);
}

// ---------------------------------------------------------------------------
// Closure consumption
// ---------------------------------------------------------------------------

/// HeapClosure layout: `[header(16) | code_ptr(16) | drop_glue_ptr(24) | captures(32..)]`
/// (backend-emitted, Decision 11). The SINGLE home for this offset: `ivar.rs`
/// imports it rather than keeping the second copy it carried until S118 (0850
/// §9.3 — folded because the two spellings were byte-identical, `24` as `isize`).
/// Derived from the header-layout authority, like the ADT offsets above.
pub(crate) const CLOSURE_DROP_GLUE_OFFSET: isize = HeapHeader::SIZE as isize + 8;

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
    // SAFETY: `ptr` cleared the nullary-tag guard above, so per this fn's
    // `# Safety` contract it is a live closure base, and the dec below has not
    // run — the caller's reference still holds the allocation. A backend-emitted
    // HeapClosure is `[header | code_ptr@16 | drop_glue_ptr@24 | captures@32…]`
    // (Decision 11), so `CLOSURE_DROP_GLUE_OFFSET` (24) is an in-bounds,
    // 8-aligned cell present on every closure, capture-carrying or not. Reading
    // it before the dec is what leaves the glue pointer available on the
    // last-ref path, after the allocation is freed below.
    let drop_glue_ptr = unsafe { heap_access::read_i64(ptr, CLOSURE_DROP_GLUE_OFFSET) };

    // SAFETY: `atomic_dec_rc` requires a valid heap base with `rc > 0`; `ptr`
    // passed the nullary-tag guard and is a live closure per this fn's
    // `# Safety` contract. This call releases the caller's one reference.
    let old_rc = unsafe { atomic_dec_rc(ptr) };
    if old_rc != 1 {
        return;
    }
    std::sync::atomic::fence(Ordering::Acquire);

    // If the closure has captures, call the backend-generated drop-glue
    // function (signature: fn(closure_ptr) -> ()).
    if drop_glue_ptr != 0 {
        // SAFETY: a non-zero `drop_glue_ptr` at offset 24 is, by the Decision-11
        // closure layout the `# Safety` contract assumes, a pointer to a
        // backend-generated drop-glue function with signature
        // `extern "C" fn(i64)` — the same shape being transmuted to, so the call
        // ABI matches. The code it points at is JIT- or object-resident for the
        // lifetime of the module that emitted the closure, which outlives this
        // closure instance, and we are on the last-ref path so the captures it
        // decs are still live and solely ours.
        let drop_fn: extern "C" fn(i64) =
            unsafe { std::mem::transmute(drop_glue_ptr as *const ()) };
        drop_fn(ptr);
    }
    // SAFETY: reached only with `old_rc == 1` — this thread dropped the last
    // reference, so no other holder can observe the closure, and the Acquire
    // fence above orders prior owners' writes before the free. `atomic_dec_rc`
    // does not free, so `ptr` is still the un-freed `alloc_with_rc` base, and
    // the drop glue (which reads the captures through `ptr`) has already run.
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
