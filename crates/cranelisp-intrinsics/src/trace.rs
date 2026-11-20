//! Runtime execution tracing for the `(trace ...)` special form.
//!
//! This is the intrinsics-hosted home for the 12 `cranelisp_trace_*`
//! backend-emitted-call function bodies, the trace stack, the GOT-swap
//! machinery, the `Trace` ADT field accessors, and the descriptor-driven value
//! formatter ([`cranelisp_trace_format`]), whose descriptor walk is pure.
//!
//! Per the 2026-06-04 user ruling (canonical: `design/arch/tracing.md`,
//! TARGET STATE; BC §4b invariant 12) the `(trace ...)` runtime lives here,
//! NOT in int. D40's trace-relocation-to-int is retracted. The 12 bodies
//! publish through [`crate::catalog::intrinsics_table`] like every other
//! intrinsic, so they resolve identically in JIT, cache-hit, and `--link`
//! modes (trace works in all modes including `--link`).
//!
//! When a `(trace ...)` expression is evaluated, the runtime:
//! 1. Swaps the per-module GOT entries to thin wrapper functions
//!    ([`cranelisp_trace_swap_got`]).
//! 2. Maintains a `TRACE_STACK` that mirrors the call stack.
//! 3. After the body finishes, marshals the stack into a `Trace` ADT heap tree
//!    ([`cranelisp_collect_trace`]).
//!
//! Thread safety: `TRACE_THREAD_ID` ensures only one thread owns the trace
//! role at a time, and only the role holder pushes or pops `TRACE_STACK`. A
//! form whose thread finds the role held elsewhere is skipped as a whole: its
//! thread's skip mark is set and it touches neither the GOT nor the stack. A
//! *same-thread* re-entrant `(trace (trace ...))` is a runtime ERROR — see the
//! nested-trace guard below.
//!
//! Heap layout uses the base-pointer convention (Decision 10):
//! `[alloc_size(+0) | rc=1(+8) | tag(+16) | field0(+24) | field1(+32) | ...]`
//!
//! `consume_trace_call` (the per-type drop helper that walks `Trace` ADT
//! sub-refs) lives here — the `TraceCall` ADT layout is owned by intrinsics
//! with the rest of the trace machinery. It is a **leaf consumer** of the
//! generic `consume_shallow` (Strings) + `crate::alloc`/`crate::rc` drop glue;
//! intrinsics' `drop` module does NOT reference `consume_trace_call` (no
//! re-coupling — `tracing.md` §4.1).
//!
//! # The nested-trace runtime guard (`tracing.md` §6)
//!
//! Same-thread re-entrant `(trace (trace e))` is disallowed. The guard lives in
//! [`cranelisp_trace_swap_got`]'s `current_owner == my_tid` branch and uses the
//! thread-local `TRACE_BODY_RUNNING` boundary flag to distinguish:
//!
//! - **legitimate multi-module swap within one trace** — `compile_trace` emits
//!   one `swap_got` per GOT group, all *before* the body runs. At that point no
//!   wrapper has fired and `TRACE_BODY_RUNNING == false`. ⇒ allowed.
//! - **re-entrant `(trace (trace e))`** — the inner form's first `swap_got`
//!   runs *while the outer body is executing*. By then a wrapper has fired and
//!   set `TRACE_BODY_RUNNING == true`. ⇒ raises through `runtime/panic`.
//!
//! **Flag lifecycle — no codegen touch-point required (the chosen placement).**
//! Rather than asking backend to emit an explicit set/clear around the body
//! (`tracing.md` §6 left this as the /dev call), the flag is driven entirely
//! from inside the intrinsic bodies that backend already calls:
//!
//! - `TRACE_BODY_RUNNING` is raised by the **first `cranelisp_trace_enter`**
//!   that runs after role-acquire (the first wrapper to fire — i.e. the first
//!   instrumented call inside the body). All `compile_trace`-emitted
//!   `swap_got` calls for one trace form precede any wrapper call, so they
//!   observe the flag still `false`.
//! - It is cleared by [`cranelisp_collect_trace`] (which backend always emits
//!   as the final trace operation), alongside the role release.
//!
//! This means **backend needs NO new emit for the guard** — the existing
//! enter/collect calls drive it. A trace form whose body makes no instrumented
//! call never raises the flag, but such a body also cannot contain a reachable
//! inner `(trace ...)` that fires a wrapper before the outer one does, so the
//! guard is not weakened: the inner trace's own `swap_got` is itself preceded
//! by the inner body's wrappers only, and the *outer* trace's first wrapper —
//! the one wrapping the call that reaches the inner `(trace ...)` — fires
//! before the inner `swap_got`, raising the flag in time. (Backend, FIXME 0255,
//! relies on this: it must NOT clear `TRACE_BODY_RUNNING` itself, and must emit
//! `cranelisp_collect_trace` exactly once per trace form, last.)

use std::alloc::{self as alloc_mod, Layout};
use std::cell::Cell;
use std::ptr;
use std::sync::Mutex;
use std::sync::atomic::{AtomicI64, AtomicU64, Ordering};
use std::time::Instant;

use cranelisp_types::HeapHeader;

use crate::alloc::{HeapAdt, alloc_with_rc};
use crate::handle::Owned;
use crate::heap_string::alloc_string;
use crate::{alloc as intrinsics_alloc, rc as intrinsics_rc};

// The pure descriptor formatter moved to `crate::trace_format` (HIGH-3, FIXME
// 0370). Re-export its public surface under the `trace::` path so the
// cross-crate API (`cranelisp_intrinsics::trace::{DisplayDescriptor,
// DescriptorKind, cranelisp_trace_format}` — read by backend `trace_codegen.rs`
// and named in `catalog.rs`) is unchanged after the split.
pub use crate::trace_format::{DescriptorKind, DisplayDescriptor, cranelisp_trace_format};

/// Lock the trace stack, recovering from mutex poisoning.
/// Poisoning can occur if a JIT-compiled function panics while the lock is
/// held. Recovery is safe because the trace stack is append-only during
/// tracing and a poisoned state just means a frame was partially built.
fn lock_trace_stack() -> std::sync::MutexGuard<'static, Vec<TraceFrame>> {
    TRACE_STACK.lock().unwrap_or_else(|e| e.into_inner())
}

use cranelisp_types::GOT_TABLE_SIZE;
const GOT_BYTES: usize = GOT_TABLE_SIZE * 8;

// ADT offsets as this module's `usize` reads take them (`alloc::HeapAdt`).
const TAG_OFFSET: usize = HeapAdt::TAG_OFFSET as usize;
const FIELD0_OFFSET: usize = HeapAdt::field_offset(0) as usize;
const FIELD1_OFFSET: usize = HeapAdt::field_offset(1) as usize;

/// Threshold below which values are bare nullary tags, not heap pointers.
const NULLARY_THRESHOLD: i64 = cranelisp_types::NULLARY_TAG_THRESHOLD as i64;

// TraceCall ADT constructor tag (single constructor)
const TAG_TRACE_CALL: i64 = 0;

// SList constructor tags (from cranelisp_types)
const TAG_SNIL: i64 = cranelisp_types::TAG_SNIL;
const TAG_SCONS: i64 = cranelisp_types::TAG_SCONS;

// ── Thread ownership ─────────────────────────────────────────────────────────

/// ID of the thread currently owning the trace role. 0 = no active trace.
static TRACE_THREAD_ID: AtomicU64 = AtomicU64::new(0);

/// Sentinel returned when the swap is skipped (another trace is active on a
/// different thread).
const SENTINEL_SAVED_GOT: i64 = 1;

/// Counter used to assign unique IDs to threads.
/// Starts at 1 so that 0 means "no owner".
static THREAD_ID_COUNTER: AtomicU64 = AtomicU64::new(1);

thread_local! {
    /// Stable, unique ID for the current thread. Assigned once on first
    /// access. CRITICAL: Must use a counter, NOT stack address (stack
    /// addresses differ across call depths on the same thread, causing CAS
    /// failures).
    static THIS_THREAD_ID: u64 = THREAD_ID_COUNTER.fetch_add(1, Ordering::Relaxed);

    /// Nested-trace boundary flag (`tracing.md` §6). `true` while a trace
    /// body is actively executing on this thread (i.e. at least one wrapper
    /// has fired since role-acquire and `collect_trace` has not yet run).
    /// A `swap_got` that finds `current_owner == my_tid && TRACE_BODY_RUNNING`
    /// is a re-entrant `(trace (trace ...))` reached DYNAMICALLY (through a
    /// wrapped call) and raises a runtime error.
    static TRACE_BODY_RUNNING: Cell<bool> = const { Cell::new(false) };

    /// GOT bases currently swapped by the active trace form on this thread
    /// (`tracing.md` §6 — the LEXICAL nested-trace distinguisher, FIXME 0283).
    ///
    /// `cranelisp_trace_swap_got` emits one swap per GOT group (one distinct
    /// `got_base` per module) for a SINGLE `(trace ...)` form, so within one
    /// form every `got_base` is unique. A re-entrant `(trace (trace ...))`
    /// re-swaps a `got_base` the enclosing form ALREADY swapped — including the
    /// pure-LEXICAL case where the inner form's first swap runs before any
    /// wrapper has fired (so `TRACE_BODY_RUNNING` is still false). Seeing a
    /// `got_base` already in this set (while `current_owner == my_tid`) is
    /// therefore an unambiguous nested-trace signal that the boundary flag
    /// misses. Cleared by `cranelisp_collect_trace` and the panic-unwind
    /// cleanup. `restore_got` removes the base it restores.
    static SWAPPED_GOT_BASES: std::cell::RefCell<Vec<i64>> =
        const { std::cell::RefCell::new(Vec::new()) };

    /// The skip mark (`trace-runtime.md` §7.2): set, with that swap's start
    /// time, by the first swap of a form that finds the role held by another
    /// thread. While set, every swap on this thread skips without arbitrating,
    /// so a form is wholly recorded or wholly skipped. The form's collect
    /// takes it.
    static SKIP_MARK: Cell<Option<Instant>> = const { Cell::new(None) };
}

fn current_thread_id() -> u64 {
    THIS_THREAD_ID.with(|&id| id)
}

/// Whether the calling thread holds the trace role, and so records
/// (`tracing.md` §4.2). The one reader of the role word for the formatting
/// entry, enter, exit and spark admission.
///
/// A relaxed load suffices: only this thread writes its own id into the word
/// or clears it, and a stale view of another thread's change reads 0 or a
/// foreign id, both "not recording".
pub(crate) fn this_thread_records() -> bool {
    TRACE_THREAD_ID.load(Ordering::Relaxed) == current_thread_id()
}

// ── Trace stack ───────────────────────────────────────────────────────────────

struct TraceFrame {
    name: String,
    /// Pre-formatted parameter String heap ptrs (RC=1 each), stored during enter.
    params: Vec<i64>,
    /// Pre-formatted result String heap ptr (0 = not yet set), stored during exit.
    result: i64,
    start: Instant,
    children: Vec<i64>, // Trace ADT heap pointers, in call order
}

impl TraceFrame {
    /// A frame with no parameters, result or children: a root, or a call frame
    /// before its wrapper's exit.
    fn bare(name: &str, start: Instant) -> Self {
        TraceFrame {
            name: name.to_string(),
            params: vec![],
            result: 0,
            start,
            children: vec![],
        }
    }
}

static TRACE_STACK: Mutex<Vec<TraceFrame>> = Mutex::new(Vec::new());

// ── GOT swap helpers ──────────────────────────────────────────────────────────

fn got_layout() -> Layout {
    Layout::from_size_align(GOT_BYTES, 8).expect("GOT layout")
}

// ── Heap allocation helpers ──────────────────────────────────────────────────

/// Write an i64 value at a byte offset from a base pointer.
///
/// Thin `usize`-offset adapter over the single-source [`crate::heap_access`]
/// accessor (MED-1, FIXME 0370) so the trace machinery's `usize` call sites are
/// unchanged while the raw-pointer arithmetic lives in one module.
///
/// # Safety
/// `base` must be a valid pointer with at least `offset + 8` bytes available.
unsafe fn write_i64(base: i64, offset: usize, value: i64) {
    unsafe { crate::heap_access::write_i64(base, offset as isize, value) }
}

/// Read an i64 value at a byte offset from a base pointer.
///
/// Thin `usize`-offset adapter over the single-source [`crate::heap_access`]
/// accessor (MED-1, FIXME 0370).
///
/// # Safety
/// `base` must be a valid pointer with at least `offset + 8` bytes readable.
unsafe fn read_i64(base: i64, offset: usize) -> i64 {
    unsafe { crate::heap_access::read_i64(base, offset as isize) }
}

/// Allocate an ADT cell with N fields using the base-pointer convention.
///
/// Layout: `[alloc_size | rc=1 | tag | field0 | field1 | ... | fieldN-1]`
///
/// Returns the base pointer as i64.
fn alloc_adt(tag: i64, fields: &[i64]) -> i64 {
    let base = alloc_with_rc(HeapAdt::payload_size(fields.len())) as i64;
    // SAFETY: `base` was just allocated by `alloc_with_rc` with room for the
    // tag and every field.
    unsafe {
        write_i64(base, TAG_OFFSET, tag);
        for (i, &field) in fields.iter().enumerate() {
            write_i64(base, HeapAdt::field_offset(i) as usize, field);
        }
    }
    base
}

/// Allocate a 3-slot ADT cell: [tag, field0, field1].
fn alloc_adt_3(tag: i64, field0: i64, field1: i64) -> i64 {
    let base = alloc_with_rc(HeapAdt::payload_size(2)) as i64;
    // SAFETY: `base` was just allocated by `alloc_with_rc` with room for the
    // tag and two fields.
    unsafe {
        write_i64(base, TAG_OFFSET, tag);
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

// ── ADT construction ─────────────────────────────────────────────────────────

/// Build a 5-field TraceCall ADT from a completed TraceFrame.
///
/// TraceCall layout (base-pointer convention):
/// `[alloc_size | rc=1 | tag=0 | tname | tparams | tresult | tchildren | tnanos]`
///
/// - tname: heap String pointer (function name)
/// - tparams: SList of heap String pointers (formatted params)
/// - tresult: heap String pointer (formatted result)
/// - tchildren: SList of TraceCall heap pointers (child calls)
/// - tnanos: i64 nanoseconds
fn build_trace_call(frame: TraceFrame, nanos: i64) -> i64 {
    let name_heap = alloc_string(frame.name.as_bytes()) as i64;
    let params_slist = build_runtime_list(&frame.params);
    let result_str = if frame.result != 0 {
        frame.result
    } else {
        alloc_string(b"") as i64
    };
    let children_slist = build_runtime_list(&frame.children);
    alloc_adt(
        TAG_TRACE_CALL,
        &[name_heap, params_slist, result_str, children_slist, nanos],
    )
}

// ── swap_got role arbitration + GOT install (decomposed from
//    cranelisp_trace_swap_got, HIGH-3 / FIXME 0370) ─────────────────────────────

const ROOT_NAME: &str = "::trace::";
const SKIPPED_NAME: &str = "::skipped::";

/// What [`cranelisp_trace_swap_got`] should do after arbitrating the trace role.
enum SwapDecision {
    /// This thread holds (or just claimed) the role for a legitimate swap —
    /// proceed to install the wrapper GOT.
    Proceed,
    /// This thread's form is skipped (its skip mark is set); the caller returns
    /// `SENTINEL_SAVED_GOT` without swapping.
    Skip,
}

/// Mark this thread's form as skipped, from this swap's start.
fn mark_skipped() -> SwapDecision {
    SKIP_MARK.with(|m| m.set(Some(Instant::now())));
    SwapDecision::Skip
}

/// Arbitrate the trace role for one `swap_got` call (the nested-trace guard,
/// `tracing.md` §6, FIXME 0283).
///
/// A thread whose skip mark is set skips without arbitrating. On a successful
/// first claim, pushes the synthetic root frame and records `got_base`; on a
/// legitimate same-thread multi-module swap, records the new base; on
/// contention, sets the skip mark and pushes nothing; on re-entrancy, raises
/// the nested-trace panic, which ends the process. Returns the
/// [`SwapDecision`] the caller acts on.
fn arbitrate_trace_role(got_base: i64) -> SwapDecision {
    if SKIP_MARK.with(Cell::get).is_some() {
        return SwapDecision::Skip;
    }
    let my_tid = current_thread_id();
    let current_owner = TRACE_THREAD_ID.load(Ordering::Relaxed);

    if current_owner == 0 {
        // Try to claim the trace role (CAS 0 -> my_tid).
        if TRACE_THREAD_ID
            .compare_exchange(0, my_tid, Ordering::SeqCst, Ordering::Relaxed)
            .is_err()
        {
            // Race: another thread just claimed it.
            return mark_skipped();
        }
        // Successfully claimed. Push the synthetic root frame.
        lock_trace_stack().push(TraceFrame::bare(ROOT_NAME, Instant::now()));
        // Record this form's first swapped GOT base (the LEXICAL nested-trace
        // distinguisher, FIXME 0283).
        SWAPPED_GOT_BASES.with(|s| s.borrow_mut().push(got_base));
        SwapDecision::Proceed
    } else if current_owner != my_tid {
        // A different thread owns the trace role -> skip (concurrent trace).
        mark_skipped()
    } else {
        // current_owner == my_tid. Distinguish:
        //   - legitimate multi-module swap (a second GOT group of the SAME
        //     trace form) => proceed
        //   - re-entrant (trace (trace ...))                       => ERROR
        //
        // TWO signals catch the two re-entrancy shapes (`tracing.md` §6,
        // FIXME 0283):
        //
        //   (1) DYNAMIC nesting — `(trace (g))` where g's body reaches an
        //       inner `(trace ...)` after an instrumented call has fired. By
        //       then `TRACE_BODY_RUNNING` is true (the first wrapper raised it).
        //
        //   (2) LEXICAL nesting — `(trace (trace e))`. The inner form's first
        //       swap runs BEFORE any wrapper fires, so `TRACE_BODY_RUNNING` is
        //       still false and signal (1) misses it. But the inner form
        //       re-swaps a `got_base` the enclosing form ALREADY swapped (each
        //       form swaps each module's GOT base exactly once), so the
        //       already-swapped-base check catches it.
        //
        // A legitimate multi-module swap of the SAME form contributes a NEW
        // `got_base` each call (one per module), so it trips neither signal.
        let already_swapped = SWAPPED_GOT_BASES.with(|s| s.borrow().contains(&got_base));
        if TRACE_BODY_RUNNING.with(Cell::get) || already_swapped {
            let msg = "nested trace is not supported: (trace ...) may not appear \
                       inside an actively-tracing (trace ...)";
            crate::panic::runtime_panic(msg.as_ptr(), msg.len());
        }
        // Legitimate multi-module swap: record this group's base too.
        SWAPPED_GOT_BASES.with(|s| s.borrow_mut().push(got_base));
        SwapDecision::Proceed
    }
}

/// Save the module's current GOT, build a wrapper-substituted copy, and install
/// it over the real GOT in one memcpy. Returns the saved-GOT heap pointer (to be
/// passed to `cranelisp_trace_restore_got`).
///
/// # Safety
/// `got_base` must point to the module's `GOT_BYTES`-sized, 8-byte-aligned GOT
/// table. `slots_ptr` / `wrappers_ptr` must point to `n_slots`-long arrays of
/// `u32` GOT indices / `i64` wrapper code pointers respectively (program-lifetime
/// leaked allocations).
unsafe fn install_wrapper_got(
    got_base: i64,
    n_slots: i64,
    slots_ptr: i64,
    wrappers_ptr: i64,
) -> i64 {
    let layout = got_layout();

    // 1. Allocate saved_got and copy the current GOT into it.
    // SAFETY: `got_layout()` returns a valid layout for GOT_BYTES with 8-byte
    // alignment.
    let saved_got = unsafe { alloc_mod::alloc(layout) };
    // SAFETY: `got_base` points to the module's GOT table (GOT_BYTES bytes,
    // 8-byte aligned). `saved_got` was just allocated with the same layout.
    unsafe {
        ptr::copy_nonoverlapping(got_base as *const u8, saved_got, GOT_BYTES);
    }

    // 2. Build debug_got: clone saved_got then substitute wrapper ptrs.
    // SAFETY: same layout as saved_got allocation above.
    let debug_got = unsafe { alloc_mod::alloc(layout) };
    // SAFETY: both `saved_got` and `debug_got` are valid GOT_BYTES allocations.
    unsafe {
        ptr::copy_nonoverlapping(saved_got, debug_got, GOT_BYTES);
    }
    // SAFETY: `slots_ptr` points to a caller-allocated array of `n_slots` u32
    // values (GOT slot indices). `wrappers_ptr` points to a caller-allocated
    // array of `n_slots` i64 values (wrapper code pointers). Both arrays are
    // leaked Box allocations that remain valid for the program lifetime.
    let slots = unsafe { std::slice::from_raw_parts(slots_ptr as *const u32, n_slots as usize) };
    let wrappers =
        unsafe { std::slice::from_raw_parts(wrappers_ptr as *const i64, n_slots as usize) };
    for (&slot, &wrapper) in slots.iter().zip(wrappers.iter()) {
        // SAFETY: `slot` is a valid GOT index (< GOT_TABLE_SIZE), so the
        // offset is within the `debug_got` allocation.
        unsafe {
            let entry_ptr = (debug_got as *mut i64).add(slot as usize);
            *entry_ptr = wrapper;
        }
    }

    // 3. Install: copy debug_got over the real GOT in one memcpy.
    // SAFETY: `debug_got` and `got_base` are both GOT_BYTES-sized,
    // non-overlapping buffers. `debug_got` is deallocated with the same
    // layout it was allocated with.
    unsafe {
        ptr::copy_nonoverlapping(debug_got, got_base as *mut u8, GOT_BYTES);
        alloc_mod::dealloc(debug_got, layout);
    }

    saved_got as i64
}

// ── Public extern API ─────────────────────────────────────────────────────────

/// Save the GOT, install wrapper pointers, and (on first call) push a synthetic
/// root trace frame.
///
/// Parameters:
/// - `got_base`:     pointer to the module's `got_table[0]`
/// - `n_slots`:      number of functions being wrapped
/// - `slots_ptr`:    `*const u32` -- GOT slot indices for each wrapped function
/// - `wrappers_ptr`: `*const i64` -- wrapper code pointers
///
/// Returns the saved-GOT heap pointer (pass to `cranelisp_trace_restore_got`),
/// or `SENTINEL_SAVED_GOT` if the form is skipped: the trace role was taken by
/// another thread at this form's first swap. A skipped swap touches neither the
/// GOT nor the trace stack.
///
/// **Nested-trace guard (`tracing.md` §6).** When the calling thread already
/// owns the trace role (`current_owner == my_tid`) AND a trace body is running
/// (`TRACE_BODY_RUNNING` is `true`), this is a re-entrant
/// `(trace (trace ...))` and raises a language panic via
/// `crate::panic::runtime_panic`, which ends the process. A same-thread swap with the body NOT yet
/// running is a legitimate multi-module swap and proceeds.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_swap_got(
    got_base: i64,
    n_slots: i64,
    slots_ptr: i64,
    wrappers_ptr: i64,
) -> i64 {
    // Arbitrate the trace role + nested-trace guard (`tracing.md` §6). On Skip
    // we return without touching the GOT.
    match arbitrate_trace_role(got_base) {
        SwapDecision::Proceed => {}
        SwapDecision::Skip => return SENTINEL_SAVED_GOT,
    }

    // SAFETY: `got_base` is the module's GOT table; `slots_ptr`/`wrappers_ptr`
    // are the caller's leaked, program-lifetime slot-index / wrapper arrays.
    unsafe { install_wrapper_got(got_base, n_slots, slots_ptr, wrappers_ptr) }
}

/// Restore the GOT from the saved copy, then free it.
/// If `saved_got` is `SENTINEL_SAVED_GOT` this is a no-op.
/// Does NOT release `TRACE_THREAD_ID` -- that is done by
/// `cranelisp_collect_trace`.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_restore_got(got_base: i64, saved_got: i64) {
    if saved_got == SENTINEL_SAVED_GOT {
        return;
    }
    let layout = got_layout();
    // SAFETY: `saved_got` was allocated by `cranelisp_trace_swap_got` with
    // `got_layout()`. `got_base` points to the module's GOT table (same size).
    // Both are valid and non-overlapping. The saved copy is deallocated with
    // the same layout.
    unsafe {
        ptr::copy_nonoverlapping(saved_got as *const u8, got_base as *mut u8, GOT_BYTES);
        alloc_mod::dealloc(saved_got as *mut u8, layout);
    }
    // Drop this base from the swapped-set (FIXME 0283). Remove only the first
    // matching occurrence so the set tracks live swaps precisely.
    SWAPPED_GOT_BASES.with(|s| {
        let mut v = s.borrow_mut();
        if let Some(i) = v.iter().position(|&b| b == got_base) {
            v.swap_remove(i);
        }
    });
}

/// Called by wrapper functions at the entry of each traced call.
/// No-op if the calling thread is not the trace thread; there every parameter
/// String word is 0, because [`cranelisp_trace_format`] formats nothing off the
/// recording thread.
///
/// Raises `TRACE_BODY_RUNNING` (the nested-trace boundary flag) — the first
/// enter after role-acquire marks the body as actively executing.
///
/// Parameters:
/// - `name_ptr`/`name_len`: raw UTF-8 function name (not a cranelisp heap String)
/// - `params_count`: number of parameter String heap ptrs in the array
/// - `params_array_ptr`: `*const i64` -- array of cranelisp String heap ptrs
///   (RC=1 each)
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_enter(
    name_ptr: i64,
    name_len: i64,
    params_count: i64,
    params_array_ptr: i64,
) {
    if !this_thread_records() {
        return;
    }
    // The body is now actively executing on this thread; a subsequent swap_got
    // by the same thread is a re-entrant (trace (trace ...)) (tracing.md §6).
    TRACE_BODY_RUNNING.with(|f| f.set(true));
    // SAFETY: `name_ptr` and `name_len` come from a leaked `Box<[u8]>` in the
    // wrapper function (valid for program lifetime). The slice covers exactly
    // `name_len` bytes of valid UTF-8 function name data.
    let name = unsafe {
        let bytes = std::slice::from_raw_parts(name_ptr as *const u8, name_len as usize);
        String::from_utf8_lossy(bytes).into_owned()
    };
    // Read the pre-formatted param String heap ptrs from the stack array.
    let params: Vec<i64> = if params_count > 0 && params_array_ptr != 0 {
        // SAFETY: `params_array_ptr` points to a Cranelift stack slot
        // containing `params_count` i64 values (heap String pointers). The
        // slot is valid for the duration of the wrapper function call.
        unsafe {
            std::slice::from_raw_parts(params_array_ptr as *const i64, params_count as usize)
                .to_vec()
        }
    } else {
        vec![]
    };
    lock_trace_stack().push(TraceFrame {
        params,
        ..TraceFrame::bare(&name, Instant::now())
    });
}

/// Called by wrapper functions at the exit of each traced call.
/// Pops the current frame, builds a TraceCall ADT, and pushes it into the
/// parent frame.
/// Returns `result` unchanged.
/// No-op (returns `result`) if the calling thread is not the trace thread;
/// there `result_str_ptr` is 0.
///
/// Parameters:
/// - `result`: the original return value (passed through unchanged)
/// - `result_str_ptr`: cranelisp String heap ptr for the formatted result (RC=1)
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_exit(result: i64, result_str_ptr: i64) -> i64 {
    if !this_thread_records() {
        return result;
    }
    let mut stack = lock_trace_stack();
    if let Some(mut frame) = stack.pop() {
        let nanos = frame.start.elapsed().as_nanos() as i64;
        frame.result = result_str_ptr;
        let trace_adt = build_trace_call(frame, nanos);
        if let Some(parent) = stack.last_mut() {
            parent.children.push(trace_adt);
        }
    }
    result
}

/// Close a trace form: return the `Trace` node it evaluates to, whose result is
/// the display of the body's value (`tracing.md` §3.6).
///
/// Emitted once per trace form, last, after every
/// [`cranelisp_trace_restore_got`] of the form.
///
/// - `value` is the body's value, **borrowed**: the entry neither consumes nor
///   retains it, and the caller releases it after the call.
/// - `descriptor_ptr` is the blob root for the value's static type, under
///   [`cranelisp_trace_format`]'s descriptor contract; 0 renders the bare word.
///
/// Returns a fresh `TraceCall` (RC=1) owned by the caller:
///
/// - **recorded** (this thread holds the role): `::trace::`, the recorded
///   children, the elapsed time since the role was acquired, and the value's
///   display as its result. The entry ends the role, clearing the nested-trace
///   boundary flag.
/// - **skipped** (the form's first swap found the role held elsewhere):
///   `::skipped::` with no children and an empty result. The skip mark clears.
/// - **unswapped** (the form swapped no slot): `::trace::` with no children,
///   elapsed 0, and the value's display as its result.
///
/// Off the recording thread the entry touches no shared state.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_collect_trace(value: i64, descriptor_ptr: i64) -> i64 {
    let (mut root, nanos) = if this_thread_records() {
        close_recorded_form()
    } else if let Some(start) = SKIP_MARK.with(Cell::take) {
        let nanos = start.elapsed().as_nanos() as i64;
        return build_trace_call(TraceFrame::bare(SKIPPED_NAME, start), nanos);
    } else {
        (TraceFrame::bare(ROOT_NAME, Instant::now()), 0)
    };
    let display = crate::trace_format::format_with_descriptor(value, descriptor_ptr);
    root.result = alloc_string(display.as_bytes()) as i64;
    build_trace_call(root, nanos)
}

/// End the role on the recording thread: stamp the root's elapsed time, pop it
/// while the role is still held, then release the role and the form's
/// thread-local guard state. Rendering follows, outside the role.
fn close_recorded_form() -> (TraceFrame, i64) {
    let root = lock_trace_stack().pop();
    debug_assert!(
        root.is_some(),
        "the role holder's root frame is on the stack"
    );
    let root = root.unwrap_or_else(|| TraceFrame::bare(ROOT_NAME, Instant::now()));
    let nanos = root.start.elapsed().as_nanos() as i64;
    TRACE_THREAD_ID.store(0, Ordering::SeqCst);
    TRACE_BODY_RUNNING.with(|f| f.set(false));
    SWAPPED_GOT_BASES.with(|s| s.borrow_mut().clear());
    (root, nanos)
}

// ── Field accessor extern API ─────────────────────────────────────────────────
//
// These implement the Trace ADT field accessors registered as extern
// primitives in the typechecker. Each reads a field at the appropriate offset
// from a TraceCall heap pointer.
//
// TraceCall layout (base-pointer convention):
// [alloc_size(+0) | rc(+8) | tag=0(+16) | tname(+24) | tparams(+32) | tresult(+40) | tchildren(+48) | tnanos(+56)]

const TRACE_TNAME_OFFSET: usize = HeapAdt::field_offset(0) as usize;
const TRACE_TPARAMS_OFFSET: usize = HeapAdt::field_offset(1) as usize;
const TRACE_TRESULT_OFFSET: usize = HeapAdt::field_offset(2) as usize;
const TRACE_TCHILDREN_OFFSET: usize = HeapAdt::field_offset(3) as usize;
const TRACE_TNANOS_OFFSET: usize = HeapAdt::field_offset(4) as usize;

/// RC-inc a heap value via the blessed `rc::rc_inc` entry point.
///
/// Thin delegate to [`crate::rc::rc_inc`] — the single owner of the shallow-inc
/// discipline (Principle 7). The nullary-tag skip lives inside `rc_inc`. This
/// is the SeqCst→Release downgrade ruled by `/arch` (FIXME 0397; BC §4b
/// invariant 3, table row `trace.rs::rc_inc_if_heap`): the field-accessor inc
/// carries no cross-variable ordering obligation, so the formerly open-coded
/// SeqCst `fetch_add` was gratuitous; Release is the correct NFR C.4.1 floor.
fn rc_inc_if_heap(val: i64) {
    crate::rc::rc_inc(val);
}

/// Return the `tname` field (String heap ptr) of a TraceCall ADT.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention. The returned
/// field is inc'd (it gets its own reference independent of the parent)
/// then the TraceCall ADT is released via `consume_trace_call` (which
/// runs recursive drop glue for the Trace ADT's sub-refs if the Trace
/// itself reaches rc=0).
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_name(trace_ptr: i64) -> i64 {
    // SAFETY: trace_ptr is a valid TraceCall heap pointer.
    let val = unsafe { read_i64(trace_ptr, TRACE_TNAME_OFFSET) };
    rc_inc_if_heap(val);
    // SAFETY: this consuming extern received one transferred Trace owner.
    consume_trace_call(unsafe { Owned::from_abi(trace_ptr) });
    val
}

/// Return the `tparams` field (SList of String heap ptrs) of a TraceCall ADT.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — see
/// `cranelisp_trace_name`.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_params(trace_ptr: i64) -> i64 {
    let val = unsafe { read_i64(trace_ptr, TRACE_TPARAMS_OFFSET) };
    rc_inc_if_heap(val);
    // SAFETY: this consuming extern received one transferred Trace owner.
    consume_trace_call(unsafe { Owned::from_abi(trace_ptr) });
    val
}

/// Return the `tresult` field (String heap ptr) of a TraceCall ADT.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — see
/// `cranelisp_trace_name`.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_result(trace_ptr: i64) -> i64 {
    let val = unsafe { read_i64(trace_ptr, TRACE_TRESULT_OFFSET) };
    rc_inc_if_heap(val);
    // SAFETY: this consuming extern received one transferred Trace owner.
    consume_trace_call(unsafe { Owned::from_abi(trace_ptr) });
    val
}

/// Return the `tchildren` field (SList of TraceCall heap ptrs) of a
/// TraceCall ADT.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — see
/// `cranelisp_trace_name`.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_children(trace_ptr: i64) -> i64 {
    let val = unsafe { read_i64(trace_ptr, TRACE_TCHILDREN_OFFSET) };
    rc_inc_if_heap(val);
    // SAFETY: this consuming extern received one transferred Trace owner.
    consume_trace_call(unsafe { Owned::from_abi(trace_ptr) });
    val
}

/// Return the `tnanos` field (i64 nanoseconds) of a TraceCall ADT.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — Int payload is
/// not heap-typed, but the Trace ADT containing it is. Consume the Trace.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_nanos(trace_ptr: i64) -> i64 {
    // SAFETY: same as cranelisp_trace_name — offset 56 is within payload
    // bounds.
    let val = unsafe { read_i64(trace_ptr, TRACE_TNANOS_OFFSET) };
    // SAFETY: this consuming extern received one transferred Trace owner.
    consume_trace_call(unsafe { Owned::from_abi(trace_ptr) });
    val
}

// ════════════════════════════════════════════════════════════════════════════
// DisplayDescriptor — the codegen-baked, self-contained value-render contract
// ════════════════════════════════════════════════════════════════════════════
//
// The pure `DisplayDescriptor` ABI + the `cranelisp_trace_format` formatter were
// split out into `crate::trace_format` (HIGH-3, FIXME 0370): they share ZERO
// state with the GOT-swap / trace-stack / drop-glue machinery here, so they live
// in their own module. See `crate::trace_format` for the descriptor encoding and
// the pure value formatter.
// ── TraceCall drop glue ────────────────────────────────────────────────────────
//
// The TraceCall ADT layout is owned by intrinsics with the rest of the trace
// machinery; the per-type consumer fn lives with the layout it walks. The
// generic `consume_shallow` (Strings) helper lives in `crate::rc` and is called
// by name below. `consume_trace_call` is a LEAF consumer — intrinsics' `drop`
// module does NOT reference it (no re-coupling; `tracing.md` §4.1).

/// Atomically decrement the RC at `ptr` with Release ordering.
/// Returns the OLD RC value.
///
/// # Safety
/// `ptr` must be a valid heap pointer with `rc > 0`.
#[inline]
unsafe fn trace_atomic_dec_rc(ptr: i64) -> i64 {
    let rc_ptr =
        unsafe { &*((ptr as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const AtomicI64) };
    let old = rc_ptr.fetch_sub(1, Ordering::Release);
    debug_assert!(
        old > 0,
        "RC underflow in trace drop glue: ptr={ptr:#x} had rc={old} before decrement"
    );
    intrinsics_rc::rc_trace("dec", ptr, old - 1);
    old
}

/// Consume an SList whose elements are heap Strings (TraceCall's `tparams`
/// field). On last ref: walks the SCons chain, calling
/// `intrinsics_rc::consume_shallow` on each head, and frees each SCons node.
fn consume_slist_of_string(handle: Owned) {
    let mut ptr = handle.into_raw();
    loop {
        if ptr < NULLARY_THRESHOLD {
            return;
        }
        let old_rc = unsafe { trace_atomic_dec_rc(ptr) };
        if old_rc != 1 {
            return;
        }
        std::sync::atomic::fence(Ordering::Acquire);
        let head = unsafe { Owned::from_abi(read_i64(ptr, FIELD0_OFFSET)) };
        let tail = unsafe { Owned::from_abi(read_i64(ptr, FIELD1_OFFSET)) };
        intrinsics_rc::consume_shallow(head);
        unsafe { intrinsics_alloc::dealloc(ptr as *mut u8) };
        ptr = tail.into_raw();
    }
}

/// Consume an SList whose elements are TraceCall ADTs (TraceCall's
/// `tchildren` field). On last ref: walks the SCons chain, recursively
/// consuming each head TraceCall, and frees each SCons node.
fn consume_slist_of_trace(handle: Owned) {
    let mut ptr = handle.into_raw();
    loop {
        if ptr < NULLARY_THRESHOLD {
            return;
        }
        let old_rc = unsafe { trace_atomic_dec_rc(ptr) };
        if old_rc != 1 {
            return;
        }
        std::sync::atomic::fence(Ordering::Acquire);
        let head = unsafe { Owned::from_abi(read_i64(ptr, FIELD0_OFFSET)) };
        let tail = unsafe { Owned::from_abi(read_i64(ptr, FIELD1_OFFSET)) };
        consume_trace_call(head);
        unsafe { intrinsics_alloc::dealloc(ptr as *mut u8) };
        ptr = tail.into_raw();
    }
}

/// Consume a TraceCall ADT (Decision 24 — consuming convention).
///
/// On last ref: dec tname (String), tparams (`SList<String>`), tresult
/// (String), tchildren (`SList<TraceCall>`), then dealloc.
///
/// TraceCall layout (single constructor, tag 0):
/// `[header(16) | tag(16) | tname(24) | tparams(32) | tresult(40) | tchildren(48) | tnanos(56)]`
///
/// Leaf consumer of `crate::rc::consume_shallow` + `crate::alloc::dealloc`;
/// intrinsics' `drop` module does NOT reference this fn (`tracing.md` §4.1).
pub fn consume_trace_call(handle: Owned) {
    let ptr = handle.into_raw();
    if ptr < NULLARY_THRESHOLD {
        return;
    }
    let old_rc = unsafe { trace_atomic_dec_rc(ptr) };
    if old_rc != 1 {
        return;
    }
    std::sync::atomic::fence(Ordering::Acquire);

    let tname = unsafe { Owned::from_abi(read_i64(ptr, TRACE_TNAME_OFFSET)) };
    let tparams = unsafe { Owned::from_abi(read_i64(ptr, TRACE_TPARAMS_OFFSET)) };
    let tresult = unsafe { Owned::from_abi(read_i64(ptr, TRACE_TRESULT_OFFSET)) };
    let tchildren = unsafe { Owned::from_abi(read_i64(ptr, TRACE_TCHILDREN_OFFSET)) };
    intrinsics_rc::consume_shallow(tname);
    consume_slist_of_string(tparams);
    intrinsics_rc::consume_shallow(tresult);
    consume_slist_of_trace(tchildren);
    unsafe { intrinsics_alloc::dealloc(ptr as *mut u8) };
}

/// The trace role held by the calling thread for a test's extent, acquired
/// and released through the same entries a trace form calls: a swap of a GOT
/// buffer the guard owns, then restore and collect.
#[cfg(test)]
pub(crate) struct RecordingRole {
    got: Box<[i64]>,
    saved: i64,
    open: bool,
}

#[cfg(test)]
impl RecordingRole {
    pub(crate) fn acquire() -> Self {
        let mut got = vec![0i64; GOT_TABLE_SIZE].into_boxed_slice();
        let no_slots = ptr::NonNull::<u32>::dangling().as_ptr() as i64;
        let no_wrappers = ptr::NonNull::<i64>::dangling().as_ptr() as i64;
        let saved = cranelisp_trace_swap_got(got.as_mut_ptr() as i64, 0, no_slots, no_wrappers);
        assert_ne!(saved, SENTINEL_SAVED_GOT, "the trace role was free");
        Self {
            got,
            saved,
            open: true,
        }
    }

    /// Close the form as emitted code does, with the body's `value` and its
    /// descriptor, and return the node the collect entry built.
    pub(crate) fn close(mut self, value: i64, descriptor_ptr: i64) -> i64 {
        self.end(value, descriptor_ptr)
    }

    fn end(&mut self, value: i64, descriptor_ptr: i64) -> i64 {
        self.open = false;
        cranelisp_trace_restore_got(self.got.as_mut_ptr() as i64, self.saved);
        cranelisp_collect_trace(value, descriptor_ptr)
    }
}

#[cfg(test)]
impl Drop for RecordingRole {
    fn drop(&mut self) {
        if self.open {
            consume_trace_call(crate::handle::test_owned(self.end(0, 0)));
        }
    }
}

#[cfg(test)]
mod tests;
