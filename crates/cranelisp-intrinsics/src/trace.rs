//! Runtime execution tracing for the `(trace ...)` special form.
//!
//! This is the intrinsics-hosted home for the 12 `cranelisp_trace_*`
//! backend-emitted-call function bodies, the trace stack, the GOT-swap
//! machinery, the `Trace` ADT field accessors, and the **pure
//! descriptor-driven value formatter** ([`cranelisp_trace_format`]).
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
//! role at a time. A different thread evaluating concurrently returns a
//! sentinel / skips tracing. A *same-thread* re-entrant `(trace (trace ...))`
//! is a runtime ERROR — see the nested-trace guard below.
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
use std::sync::atomic::{AtomicI64, AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Instant;

use cranelisp_types::HeapHeader;

use crate::alloc::alloc_with_rc;
use crate::heap_string::alloc_string;
use crate::{alloc as intrinsics_alloc, rc as intrinsics_rc};

// The pure descriptor formatter moved to `crate::trace_format` (HIGH-3, FIXME
// 0370). Re-export its public surface under the `trace::` path so the
// cross-crate API (`cranelisp_intrinsics::trace::{DisplayDescriptor,
// DescriptorKind, cranelisp_trace_format}` — read by backend `trace_codegen.rs`
// and named in `catalog.rs`) is unchanged after the split.
pub use crate::trace_format::{cranelisp_trace_format, DescriptorKind, DisplayDescriptor};

/// Lock the trace stack, recovering from mutex poisoning.
/// Poisoning can occur if a JIT-compiled function panics while the lock is
/// held. Recovery is safe because the trace stack is append-only during
/// tracing and a poisoned state just means a frame was partially built.
fn lock_trace_stack() -> std::sync::MutexGuard<'static, Vec<TraceFrame>> {
    TRACE_STACK.lock().unwrap_or_else(|e| e.into_inner())
}

use cranelisp_types::GOT_TABLE_SIZE;
const GOT_BYTES: usize = GOT_TABLE_SIZE * 8;

// Heap layout constants (base-pointer convention, Decision 10)
const PAYLOAD_OFFSET: usize = 16;
const FIELD0_OFFSET: usize = 24;
const FIELD1_OFFSET: usize = 32;

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
}

fn current_thread_id() -> u64 {
    THIS_THREAD_ID.with(|&id| id)
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
    let n_slots = 1 + fields.len(); // tag + fields
    let payload_size = n_slots * 8;
    let base = alloc_with_rc(payload_size) as i64;
    // SAFETY: `base` was just allocated by `alloc_with_rc` with enough space
    // for the payload header (16 bytes) plus `n_slots * 8` bytes of fields.
    unsafe {
        write_i64(base, PAYLOAD_OFFSET, tag);
        for (i, &field) in fields.iter().enumerate() {
            write_i64(base, FIELD0_OFFSET + i * 8, field);
        }
    }
    base
}

/// Allocate a 3-slot ADT cell: [tag, field0, field1].
fn alloc_adt_3(tag: i64, field0: i64, field1: i64) -> i64 {
    let payload_size = 24; // tag(8) + field0(8) + field1(8)
    let base = alloc_with_rc(payload_size) as i64;
    // SAFETY: `base` was just allocated by `alloc_with_rc` with 24 bytes of
    // payload, sufficient for tag + 2 fields at offsets 16, 24, and 32.
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

/// Push a placeholder trace frame with a fixed `name`. Used for the synthetic
/// root frame (`"::trace::"`) and the concurrent-skip sentinel (`"::skipped::"`).
fn push_trace_frame(name: &str) {
    lock_trace_stack().push(TraceFrame {
        name: name.to_string(),
        params: vec![],
        result: 0,
        start: Instant::now(),
        children: vec![],
    });
}

/// What [`cranelisp_trace_swap_got`] should do after arbitrating the trace role.
enum SwapDecision {
    /// This thread holds (or just claimed) the role for a legitimate swap —
    /// proceed to install the wrapper GOT.
    Proceed,
    /// Another thread owns the role (or won the claim race) — a sentinel frame
    /// was pushed; the caller returns `SENTINEL_SAVED_GOT` without swapping.
    Skip,
    /// A re-entrant `(trace (trace …))` was detected — a runtime error has
    /// already been raised; the caller returns `SENTINEL_SAVED_GOT`.
    NestedError,
}

/// Arbitrate the trace role for one `swap_got` call (the nested-trace guard,
/// `tracing.md` §6, FIXME 0283).
///
/// On a successful first claim, pushes the synthetic root frame and records
/// `got_base`; on a legitimate same-thread multi-module swap, records the new
/// base; on contention or re-entrancy, pushes the appropriate sentinel / raises
/// the runtime error. Returns the [`SwapDecision`] the caller acts on.
fn arbitrate_trace_role(got_base: i64) -> SwapDecision {
    let my_tid = current_thread_id();
    let current_owner = TRACE_THREAD_ID.load(Ordering::Relaxed);

    if current_owner == 0 {
        // Try to claim the trace role (CAS 0 -> my_tid).
        if TRACE_THREAD_ID
            .compare_exchange(0, my_tid, Ordering::SeqCst, Ordering::Relaxed)
            .is_err()
        {
            // Race: another thread just claimed it -> push sentinel frame, skip.
            push_trace_frame("::skipped::");
            return SwapDecision::Skip;
        }
        // Successfully claimed. Push the synthetic root frame.
        push_trace_frame("::trace::");
        // Record this form's first swapped GOT base (the LEXICAL nested-trace
        // distinguisher, FIXME 0283).
        SWAPPED_GOT_BASES.with(|s| s.borrow_mut().push(got_base));
        SwapDecision::Proceed
    } else if current_owner != my_tid {
        // A different thread owns the trace role -> skip (concurrent trace).
        push_trace_frame("::skipped::");
        SwapDecision::Skip
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
        let already_swapped =
            SWAPPED_GOT_BASES.with(|s| s.borrow().contains(&got_base));
        if TRACE_BODY_RUNNING.with(Cell::get) || already_swapped {
            let msg = "nested trace is not supported: (trace ...) may not appear \
                       inside an actively-tracing (trace ...)";
            crate::panic::runtime_panic(msg.as_ptr(), msg.len());
            return SwapDecision::NestedError;
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
    let slots =
        unsafe { std::slice::from_raw_parts(slots_ptr as *const u32, n_slots as usize) };
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
/// or `SENTINEL_SAVED_GOT` if the trace role is already taken by another
/// thread.
///
/// **Nested-trace guard (`tracing.md` §6).** When the calling thread already
/// owns the trace role (`current_owner == my_tid`) AND a trace body is running
/// (`TRACE_BODY_RUNNING` is `true`), this is a re-entrant
/// `(trace (trace ...))` and is reported as a runtime error via
/// `crate::panic::runtime_panic`. A same-thread swap with the body NOT yet
/// running is a legitimate multi-module swap and proceeds.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_swap_got(
    got_base: i64,
    n_slots: i64,
    slots_ptr: i64,
    wrappers_ptr: i64,
) -> i64 {
    // Arbitrate the trace role + nested-trace guard (`tracing.md` §6). On Skip /
    // NestedError the sentinel frame is pushed (or the runtime error raised)
    // inside the helper, and we return without touching the GOT.
    match arbitrate_trace_role(got_base) {
        SwapDecision::Proceed => {}
        SwapDecision::Skip | SwapDecision::NestedError => return SENTINEL_SAVED_GOT,
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
/// No-op if the calling thread is not the trace thread.
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
    if TRACE_THREAD_ID.load(Ordering::Relaxed) != current_thread_id() {
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
        name,
        params,
        result: 0,
        start: Instant::now(),
        children: vec![],
    });
}

/// Called by wrapper functions at the exit of each traced call.
/// Pops the current frame, builds a TraceCall ADT, and pushes it into the
/// parent frame.
/// Returns `result` unchanged.
/// No-op (returns `result`) if the calling thread is not the trace thread.
///
/// Parameters:
/// - `result`: the original return value (passed through unchanged)
/// - `result_str_ptr`: cranelisp String heap ptr for the formatted result (RC=1)
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_exit(result: i64, result_str_ptr: i64) -> i64 {
    if TRACE_THREAD_ID.load(Ordering::Relaxed) != current_thread_id() {
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

/// Extract the `tnanos` field of the first child of the root Trace frame.
/// Used by the `/run-tests` slash command and user-level test runners
/// (composed from `discover-tests` + `run-test` builtins) to report per-test
/// execution time. Returns 0 if the trace has no children.
///
/// TraceCall heap layout (base-pointer convention):
/// `[alloc_size(+0) | rc(+8) | tag(+16) | tname(+24) | tparams(+32) | tresult(+40) | tchildren(+48) | tnanos(+56)]`
///
/// SList SCons layout: `[alloc_size(+0) | rc(+8) | tag=1(+16) | head(+24) | tail(+32)]`
/// SNil = bare 0 (nullary tag).
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_first_child_nanos(trace_adt: i64) -> i64 {
    if trace_adt == 0 || (trace_adt as usize) < cranelisp_types::NULLARY_TAG_THRESHOLD {
        return 0;
    }
    // SAFETY for all read_i64 calls below: `trace_adt` was verified above to
    // be a heap pointer (above NULLARY_TAG_THRESHOLD). It was allocated by
    // `build_trace_call` with the 5-field TraceCall layout, so offsets 48
    // and 56 are within bounds. Intermediate pointers (tchildren,
    // first_child) are checked against NULLARY_THRESHOLD before
    // dereferencing.

    // tchildren is at offset 48 (FIELD0_OFFSET + 3*8 = 24 + 24)
    let tchildren = unsafe { read_i64(trace_adt, 48) };
    let result = if tchildren < NULLARY_THRESHOLD {
        0 // SNil
    } else {
        let scons_tag = unsafe { read_i64(tchildren, PAYLOAD_OFFSET) };
        if scons_tag != TAG_SCONS {
            0 // not SCons
        } else {
            // head is at FIELD0_OFFSET (24) of the SCons
            let first_child = unsafe { read_i64(tchildren, FIELD0_OFFSET) };
            if first_child < NULLARY_THRESHOLD {
                0
            } else {
                // tnanos is at offset 56 (FIELD0_OFFSET + 4*8 = 24 + 32)
                unsafe { read_i64(first_child, 56) }
            }
        }
    };
    // Decision 24 (Sprint 56 Step 2c): consuming convention — release the
    // Trace ADT (walks sub-refs if this was the last reference).
    consume_trace_call(trace_adt);
    result
}

/// Collect the root trace frame, release the trace role, and return the trace
/// as a `Trace` ADT heap pointer.
/// Must be called after all `cranelisp_trace_restore_got` calls for this
/// trace expression.
///
/// Clears `TRACE_BODY_RUNNING` (the nested-trace boundary flag) alongside the
/// role release — this is the end of the trace body for guard purposes
/// (`tracing.md` §6).
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_collect_trace() -> i64 {
    // Release the trace role (only if we own it) and lower the body-running
    // boundary flag.
    let my_tid = current_thread_id();
    TRACE_THREAD_ID
        .compare_exchange(my_tid, 0, Ordering::SeqCst, Ordering::Relaxed)
        .ok();
    TRACE_BODY_RUNNING.with(|f| f.set(false));
    // End of trace form: clear the swapped-base set (FIXME 0283). All
    // restore_got calls have already removed their bases; this drains any
    // residue defensively so the next trace form starts clean.
    SWAPPED_GOT_BASES.with(|s| s.borrow_mut().clear());

    let mut stack = lock_trace_stack();
    if let Some(frame) = stack.pop() {
        let nanos = frame.start.elapsed().as_nanos() as i64;
        build_trace_call(frame, nanos)
    } else {
        // Empty stack -- return a minimal TraceCall with empty params/result
        let name_heap = alloc_string(b"::trace::") as i64;
        let empty_slist = TAG_SNIL;
        let empty_str = alloc_string(b"") as i64;
        alloc_adt(
            TAG_TRACE_CALL,
            &[name_heap, empty_slist, empty_str, empty_slist, 0i64],
        )
    }
}

/// Panic-unwind trace-guard cleanup (`design/arch/test-discovery.md` §5 scope
/// item 5; 0258 NOTE-2).
///
/// When a runtime panic crosses an actively-tracing `(trace …)` bracket, the
/// backend may not reach `cranelisp_collect_trace` (the normal guard-clear +
/// role-release site), leaving `TRACE_BODY_RUNNING` set and the trace role held
/// by this thread. The next same-thread `(trace …)` would then spuriously raise
/// "nested trace". This clears the boundary flag and releases the role (only if
/// this thread owns it) so a subsequent trace starts clean.
///
/// Called by [`crate::panic::catch_runtime_error`] when it observes a captured
/// error (a panic crossed the bracket) — both are intrinsics-owned thread-locals,
/// so the cleanup is wholly in-crate. Idempotent and safe to call when no trace
/// is active (the role CAS no-ops and the flag is already false).
pub(crate) fn clear_trace_guard_on_panic() {
    let my_tid = current_thread_id();
    // Release the role only if we own it (pre-existing stuck-owner class — the
    // role CAS had the same hole; repaired here alongside the flag).
    TRACE_THREAD_ID
        .compare_exchange(my_tid, 0, Ordering::SeqCst, Ordering::Relaxed)
        .ok();
    TRACE_BODY_RUNNING.with(|f| f.set(false));
    // Also drain the swapped-base set so a post-panic trace form starts clean
    // (FIXME 0283 — parallel to the boundary-flag reset above).
    SWAPPED_GOT_BASES.with(|s| s.borrow_mut().clear());
}

// ── Field accessor extern API ─────────────────────────────────────────────────
//
// These implement the Trace ADT field accessors registered as extern
// primitives in the typechecker. Each reads a field at the appropriate offset
// from a TraceCall heap pointer.
//
// TraceCall layout (base-pointer convention):
// [alloc_size(+0) | rc(+8) | tag=0(+16) | tname(+24) | tparams(+32) | tresult(+40) | tchildren(+48) | tnanos(+56)]

const TRACE_TNAME_OFFSET: usize = FIELD0_OFFSET;            // 24
const TRACE_TPARAMS_OFFSET: usize = FIELD0_OFFSET + 8;      // 32
const TRACE_TRESULT_OFFSET: usize = FIELD0_OFFSET + 16;     // 40
const TRACE_TCHILDREN_OFFSET: usize = FIELD0_OFFSET + 24;   // 48
const TRACE_TNANOS_OFFSET: usize = FIELD0_OFFSET + 32;      // 56

/// RC-inc a heap value (atomic, matching the compiler's `emit_rc_inc`).
/// No-op for nullary tags (bare integers below NULLARY_TAG_THRESHOLD).
fn rc_inc_if_heap(val: i64) {
    if (val as usize) >= cranelisp_types::NULLARY_TAG_THRESHOLD {
        // SAFETY: val is a heap pointer; RC field is at offset 8 from base.
        unsafe {
            let rc_ptr = (val as *mut u8).add(8) as *mut AtomicI64;
            (*rc_ptr).fetch_add(1, Ordering::SeqCst);
        }
    }
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
    consume_trace_call(trace_ptr);
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
    consume_trace_call(trace_ptr);
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
    consume_trace_call(trace_ptr);
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
    consume_trace_call(trace_ptr);
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
    consume_trace_call(trace_ptr);
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
    let rc_ptr = unsafe {
        &*((ptr as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const AtomicI64)
    };
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
fn consume_slist_of_string(mut ptr: i64) {
    loop {
        if ptr < NULLARY_THRESHOLD {
            return;
        }
        let head = unsafe { read_i64(ptr, FIELD0_OFFSET) };
        let tail = unsafe { read_i64(ptr, FIELD1_OFFSET) };
        let old_rc = unsafe { trace_atomic_dec_rc(ptr) };
        if old_rc != 1 {
            return;
        }
        std::sync::atomic::fence(Ordering::Acquire);
        intrinsics_rc::consume_shallow(head);
        unsafe { intrinsics_alloc::dealloc(ptr as *mut u8) };
        ptr = tail;
    }
}

/// Consume an SList whose elements are TraceCall ADTs (TraceCall's
/// `tchildren` field). On last ref: walks the SCons chain, recursively
/// consuming each head TraceCall, and frees each SCons node.
fn consume_slist_of_trace(mut ptr: i64) {
    loop {
        if ptr < NULLARY_THRESHOLD {
            return;
        }
        let head = unsafe { read_i64(ptr, FIELD0_OFFSET) };
        let tail = unsafe { read_i64(ptr, FIELD1_OFFSET) };
        let old_rc = unsafe { trace_atomic_dec_rc(ptr) };
        if old_rc != 1 {
            return;
        }
        std::sync::atomic::fence(Ordering::Acquire);
        consume_trace_call(head);
        unsafe { intrinsics_alloc::dealloc(ptr as *mut u8) };
        ptr = tail;
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
pub fn consume_trace_call(ptr: i64) {
    if ptr < NULLARY_THRESHOLD {
        return;
    }
    let tname = unsafe { read_i64(ptr, TRACE_TNAME_OFFSET) };
    let tparams = unsafe { read_i64(ptr, TRACE_TPARAMS_OFFSET) };
    let tresult = unsafe { read_i64(ptr, TRACE_TRESULT_OFFSET) };
    let tchildren = unsafe { read_i64(ptr, TRACE_TCHILDREN_OFFSET) };

    let old_rc = unsafe { trace_atomic_dec_rc(ptr) };
    if old_rc != 1 {
        return;
    }
    std::sync::atomic::fence(Ordering::Acquire);

    intrinsics_rc::consume_shallow(tname);
    consume_slist_of_string(tparams);
    intrinsics_rc::consume_shallow(tresult);
    consume_slist_of_trace(tchildren);
    unsafe { intrinsics_alloc::dealloc(ptr as *mut u8) };
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── Trace machinery basics (relocated from int) ──────────────────────────

    #[test]
    fn test_current_thread_id_stable() {
        let id1 = current_thread_id();
        let id2 = current_thread_id();
        assert_eq!(id1, id2, "thread ID must be stable across calls");
    }

    #[test]
    fn test_alloc_adt_creates_valid_heap() {
        let adt = alloc_adt(TAG_TRACE_CALL, &[100, 200, 300, 400, 500]);
        assert!(adt != 0, "allocation must return non-null");
        let tag = unsafe { read_i64(adt, PAYLOAD_OFFSET) };
        assert_eq!(tag, TAG_TRACE_CALL);
        let f0 = unsafe { read_i64(adt, FIELD0_OFFSET) };
        assert_eq!(f0, 100);
        let f4 = unsafe { read_i64(adt, FIELD0_OFFSET + 4 * 8) };
        assert_eq!(f4, 500);
    }

    #[test]
    fn test_build_runtime_list_empty() {
        let list = build_runtime_list(&[]);
        assert_eq!(list, TAG_SNIL);
    }

    #[test]
    fn test_build_runtime_list_items() {
        let list = build_runtime_list(&[10, 20, 30]);
        assert!(list >= NULLARY_THRESHOLD, "list head should be heap pointer");
        let tag = unsafe { read_i64(list, PAYLOAD_OFFSET) };
        assert_eq!(tag, TAG_SCONS);
        let head = unsafe { read_i64(list, FIELD0_OFFSET) };
        assert_eq!(head, 10);
    }

    // ── Nested-trace guard state machine (testable without JIT) ───────────────

    #[test]
    fn nested_guard_multi_module_swap_allowed() {
        // Simulate role-acquire on this thread, then a SECOND swap by the same
        // thread BEFORE any wrapper fires (TRACE_BODY_RUNNING == false). The
        // second swap must NOT raise (it returns a real saved-GOT, not the
        // sentinel-on-panic path).
        let my_tid = current_thread_id();
        // Acquire the role directly (mimicking a successful first swap).
        TRACE_THREAD_ID.store(my_tid, Ordering::SeqCst);
        TRACE_BODY_RUNNING.with(|f| f.set(false));

        // A real swap needs a GOT + slot/wrapper arrays; build minimal ones.
        let mut got = vec![0i64; GOT_TABLE_SIZE];
        let slots: Vec<u32> = vec![0];
        let wrappers: Vec<i64> = vec![0xdead];
        let saved = cranelisp_trace_swap_got(
            got.as_mut_ptr() as i64,
            1,
            slots.as_ptr() as i64,
            wrappers.as_ptr() as i64,
        );
        // Legitimate multi-module swap returns a real (non-sentinel) saved-GOT.
        assert_ne!(saved, SENTINEL_SAVED_GOT, "multi-module swap must proceed");
        cranelisp_trace_restore_got(got.as_mut_ptr() as i64, saved);

        // Cleanup: release role + flag.
        TRACE_THREAD_ID.store(0, Ordering::SeqCst);
        TRACE_BODY_RUNNING.with(|f| f.set(false));
        let _ = crate::panic::take_runtime_error();
    }

    #[test]
    fn nested_guard_reentrant_raises() {
        // Simulate role-acquired + body running (a wrapper has fired), then an
        // inner swap by the SAME thread. This is (trace (trace ...)) and must
        // raise via runtime_panic (returning the sentinel).
        let my_tid = current_thread_id();
        TRACE_THREAD_ID.store(my_tid, Ordering::SeqCst);
        TRACE_BODY_RUNNING.with(|f| f.set(true));
        let _ = crate::panic::take_runtime_error(); // clear any prior

        let mut got = vec![0i64; GOT_TABLE_SIZE];
        let slots: Vec<u32> = vec![0];
        let wrappers: Vec<i64> = vec![0xbeef];
        let saved = cranelisp_trace_swap_got(
            got.as_mut_ptr() as i64,
            1,
            slots.as_ptr() as i64,
            wrappers.as_ptr() as i64,
        );
        assert_eq!(saved, SENTINEL_SAVED_GOT, "re-entrant swap must not proceed");
        let err = crate::panic::take_runtime_error();
        assert!(err.is_some(), "re-entrant swap must raise a runtime error");
        assert!(
            err.unwrap().contains("nested trace is not supported"),
            "guard message must name nested trace"
        );

        // Cleanup.
        TRACE_THREAD_ID.store(0, Ordering::SeqCst);
        TRACE_BODY_RUNNING.with(|f| f.set(false));
    }

    // spec: spec/04-expressions.md §4.12.5 — LEXICAL nested trace
    // `(trace (trace e))` must raise even though no wrapper has fired (so
    // TRACE_BODY_RUNNING is still false). FIXME 0283. The inner form re-swaps a
    // GOT base the outer form already swapped; the already-swapped-base check
    // catches it where the boundary flag misses it.
    #[test]
    fn nested_guard_lexical_reentrant_raises() {
        // Start clean on this thread.
        TRACE_THREAD_ID.store(0, Ordering::SeqCst);
        TRACE_BODY_RUNNING.with(|f| f.set(false));
        SWAPPED_GOT_BASES.with(|s| s.borrow_mut().clear());
        let _ = crate::panic::take_runtime_error();

        let mut got = vec![0i64; GOT_TABLE_SIZE];
        let base = got.as_mut_ptr() as i64;
        let slots: Vec<u32> = vec![0];
        let wrappers: Vec<i64> = vec![0xfeed];

        // Outer form's swap: claims the role, records `base`.
        let outer_saved = cranelisp_trace_swap_got(
            base,
            1,
            slots.as_ptr() as i64,
            wrappers.as_ptr() as i64,
        );
        assert_ne!(outer_saved, SENTINEL_SAVED_GOT, "outer swap must proceed");
        // CRITICAL: no wrapper has fired, so the boundary flag is still false —
        // this is exactly the lexical-nesting condition the old guard missed.
        assert!(
            !TRACE_BODY_RUNNING.with(Cell::get),
            "precondition: lexical case has body_running == false"
        );

        // Inner form's swap of the SAME base while the role is held: re-entrant.
        let inner_saved = cranelisp_trace_swap_got(
            base,
            1,
            slots.as_ptr() as i64,
            wrappers.as_ptr() as i64,
        );
        assert_eq!(
            inner_saved, SENTINEL_SAVED_GOT,
            "lexical re-entrant swap must NOT proceed"
        );
        let err = crate::panic::take_runtime_error();
        assert!(
            err.as_deref()
                .is_some_and(|m| m.contains("nested trace is not supported")),
            "lexical nested trace must raise the nested-trace error; got {err:?}"
        );

        // Cleanup: restore the outer swap + release role/flag/set.
        cranelisp_trace_restore_got(base, outer_saved);
        TRACE_THREAD_ID.store(0, Ordering::SeqCst);
        TRACE_BODY_RUNNING.with(|f| f.set(false));
        SWAPPED_GOT_BASES.with(|s| s.borrow_mut().clear());
    }

    // A legitimate two-MODULE swap of ONE form uses two DISTINCT got bases and
    // must proceed for both (the multi-module case the lexical guard must not
    // false-positive on). FIXME 0283.
    #[test]
    fn nested_guard_two_distinct_bases_allowed() {
        TRACE_THREAD_ID.store(0, Ordering::SeqCst);
        TRACE_BODY_RUNNING.with(|f| f.set(false));
        SWAPPED_GOT_BASES.with(|s| s.borrow_mut().clear());
        let _ = crate::panic::take_runtime_error();

        let mut got_a = vec![0i64; GOT_TABLE_SIZE];
        let mut got_b = vec![0i64; GOT_TABLE_SIZE];
        let base_a = got_a.as_mut_ptr() as i64;
        let base_b = got_b.as_mut_ptr() as i64;
        let slots: Vec<u32> = vec![0];
        let wrappers: Vec<i64> = vec![0xcafe];

        let saved_a = cranelisp_trace_swap_got(
            base_a, 1, slots.as_ptr() as i64, wrappers.as_ptr() as i64,
        );
        let saved_b = cranelisp_trace_swap_got(
            base_b, 1, slots.as_ptr() as i64, wrappers.as_ptr() as i64,
        );
        assert_ne!(saved_a, SENTINEL_SAVED_GOT, "first module swap must proceed");
        assert_ne!(saved_b, SENTINEL_SAVED_GOT, "second module swap must proceed");
        assert!(
            crate::panic::take_runtime_error().is_none(),
            "distinct-base multi-module swap must NOT raise"
        );

        cranelisp_trace_restore_got(base_b, saved_b);
        cranelisp_trace_restore_got(base_a, saved_a);
        TRACE_THREAD_ID.store(0, Ordering::SeqCst);
        TRACE_BODY_RUNNING.with(|f| f.set(false));
        SWAPPED_GOT_BASES.with(|s| s.borrow_mut().clear());
    }

    #[test]
    fn enter_sets_body_running_collect_clears() {
        // enter (when we own the role) raises TRACE_BODY_RUNNING;
        // collect_trace clears it.
        let my_tid = current_thread_id();
        TRACE_THREAD_ID.store(my_tid, Ordering::SeqCst);
        TRACE_BODY_RUNNING.with(|f| f.set(false));
        // Push a root frame so collect has something to pop.
        lock_trace_stack().push(TraceFrame {
            name: "::trace::".to_string(),
            params: vec![],
            result: 0,
            start: Instant::now(),
            children: vec![],
        });

        let name = "f";
        cranelisp_trace_enter(name.as_ptr() as i64, name.len() as i64, 0, 0);
        assert!(TRACE_BODY_RUNNING.with(Cell::get), "enter must raise the flag");
        // Pop the frame enter pushed.
        let _ = cranelisp_trace_exit(0, alloc_string(b"") as i64);

        let t = cranelisp_collect_trace();
        assert!(!TRACE_BODY_RUNNING.with(Cell::get), "collect must clear the flag");
        consume_trace_call(t);

        TRACE_THREAD_ID.store(0, Ordering::SeqCst);
    }

    // ── 0340 capture-fidelity durable guard (intrinsics-side; FIXME 0340) ─────
    //
    // The 0340 "degenerate capture" symptom — `(Trace.TraceCall "::trace::" SNil
    // …)` — is a NON-DEFECT in intrinsics. It was reproduced tracing `add-i64`,
    // an inline-CLIF primitive with NO GOT slot: it is never wrapped, so its
    // enter/exit wrappers never fire, the trace body adds no child frame, and
    // `cranelisp_collect_trace` over the bare synthetic root yields the faithful
    // empty shape. The 12 trace bodies capture name+operands CORRECTLY whenever
    // a wrapper fires; this guard pins that fact at the enter→exit→collect seam
    // so a future refactor cannot silently regress correct capture into the
    // degenerate shape and re-attribute 0340 to intrinsics.
    //
    // Driven directly (no codegen) for a SIMULATED GOT-slotted callee: we play
    // the exact sequence backend's wrapper emits — claim the role + push the
    // synthetic root (as the first `swap_got` does), then `enter` with a real
    // name + pre-formatted param Strings, then `exit` with a result String, then
    // `collect`. The marshalled root must carry ONE child whose TraceCall NAMES
    // the call (not "::trace::") and whose `tparams` is a non-empty SList (not
    // SNil) — the load-bearing facts the degenerate shape lacks.
    //
    // spec: spec/04-expressions.md §4.12.3 — `(trace expr)` captures the traced
    // call's name + operands.
    #[test]
    fn capture_fidelity_got_slotted_callee_names_call_and_carries_operands() {
        let my_tid = current_thread_id();
        // Clean start.
        TRACE_THREAD_ID.store(0, Ordering::SeqCst);
        TRACE_BODY_RUNNING.with(|f| f.set(false));
        let _ = crate::panic::take_runtime_error();

        // Claim the role + push the synthetic root frame exactly as the first
        // `cranelisp_trace_swap_got` does for a GOT-slotted module.
        TRACE_THREAD_ID.store(my_tid, Ordering::SeqCst);
        lock_trace_stack().push(TraceFrame {
            name: "::trace::".to_string(),
            params: vec![],
            result: 0,
            start: Instant::now(),
            children: vec![],
        });

        // The wrapper for a GOT-slotted callee fires `enter` with the call's
        // real name and its pre-formatted operand Strings, then `exit` with the
        // pre-formatted result String. Simulate tracing `(user/add 2 3) => 5`.
        let name = "user/add";
        let p0 = alloc_string(b"2") as i64;
        let p1 = alloc_string(b"3") as i64;
        let params_array: [i64; 2] = [p0, p1];
        cranelisp_trace_enter(
            name.as_ptr() as i64,
            name.len() as i64,
            2,
            params_array.as_ptr() as i64,
        );
        let result_str = alloc_string(b"5") as i64;
        let _ = cranelisp_trace_exit(0, result_str);

        // Collect the root: it should now hold the child TraceCall the wrapper
        // produced.
        let root = cranelisp_collect_trace();

        // The ROOT names "::trace::" with no operands (that's the synthetic
        // root — faithful), but its tchildren must hold the captured call.
        let root_children = unsafe { read_i64(root, TRACE_TCHILDREN_OFFSET) };
        assert!(
            root_children >= NULLARY_THRESHOLD,
            "root must have a child (the GOT-slotted callee was captured)"
        );
        let scons_tag = unsafe { read_i64(root_children, PAYLOAD_OFFSET) };
        assert_eq!(scons_tag, TAG_SCONS, "tchildren must be a non-empty SList");
        let child = unsafe { read_i64(root_children, FIELD0_OFFSET) };

        // FIDELITY 1: the child NAMES the call — NOT the "::trace::" placeholder.
        let child_name_heap = unsafe { read_i64(child, TRACE_TNAME_OFFSET) };
        let child_name =
            unsafe { crate::heap_string::read_string_as_str(child_name_heap) };
        assert_eq!(
            child_name, "user/add",
            "captured TraceCall must name the traced call, not the placeholder"
        );
        assert_ne!(
            child_name, "::trace::",
            "captured call name must NOT be the degenerate placeholder"
        );

        // FIDELITY 2: operands captured — tparams is a non-empty SList, NOT SNil.
        let child_params = unsafe { read_i64(child, TRACE_TPARAMS_OFFSET) };
        assert!(
            child_params >= NULLARY_THRESHOLD,
            "captured tparams must be a heap SList, not SNil (operands captured)"
        );
        assert_ne!(
            child_params, TAG_SNIL,
            "captured tparams must NOT be the degenerate empty SNil"
        );
        let params_tag = unsafe { read_i64(child_params, PAYLOAD_OFFSET) };
        assert_eq!(params_tag, TAG_SCONS, "tparams SList must have an operand");
        let first_param = unsafe { read_i64(child_params, FIELD0_OFFSET) };
        let first_param_str =
            unsafe { crate::heap_string::read_string_as_str(first_param) };
        assert_eq!(first_param_str, "2", "first operand must be captured verbatim");

        // Release ownership (consume the marshalled tree).
        consume_trace_call(root);
        TRACE_THREAD_ID.store(0, Ordering::SeqCst);
        TRACE_BODY_RUNNING.with(|f| f.set(false));
    }

    // Companion guard: `cranelisp_collect_trace` over an EMPTY stack returns the
    // `::trace::` / SNil node. This is the INTENDED faithful shape for a trace
    // whose body fired no wrapper (e.g. tracing an inline-CLIF primitive with no
    // GOT slot, like `add-i64` — the exact shape 0340 mistook for a defect). An
    // empty trace is NOT a bug: with no wrapped call there is nothing to name or
    // capture, so the synthetic-root placeholder + empty operands is correct.
    //
    // spec: spec/04-expressions.md §4.12.3 — a trace over an un-wrappable call
    // faithfully captures nothing.
    #[test]
    fn empty_trace_yields_faithful_placeholder_not_a_defect() {
        // Ensure a clean (empty) stack + no role held on this thread.
        TRACE_THREAD_ID.store(0, Ordering::SeqCst);
        TRACE_BODY_RUNNING.with(|f| f.set(false));
        {
            // Drain any residue so collect hits the empty-stack fallback.
            lock_trace_stack().clear();
        }

        let root = cranelisp_collect_trace();

        // Name is the synthetic placeholder — faithful, NOT degenerate-by-bug.
        let name_heap = unsafe { read_i64(root, TRACE_TNAME_OFFSET) };
        let name = unsafe { crate::heap_string::read_string_as_str(name_heap) };
        assert_eq!(
            name, "::trace::",
            "empty-stack collect intentionally yields the synthetic placeholder"
        );
        // Operands + children are empty SNil — the faithful shape for a trace
        // that wrapped nothing. (This is the 0340 symptom shape; it is CORRECT
        // here because no GOT-slotted call was traced.)
        let params = unsafe { read_i64(root, TRACE_TPARAMS_OFFSET) };
        assert_eq!(params, TAG_SNIL, "empty-trace operands are faithfully SNil");
        let children = unsafe { read_i64(root, TRACE_TCHILDREN_OFFSET) };
        assert_eq!(children, TAG_SNIL, "empty-trace children are faithfully SNil");

        consume_trace_call(root);
    }

    // spec: spec/04-expressions.md §4.12.5 — panic-unwind trace-guard cleanup
    // (0258 NOTE-2 / test-discovery.md §5 item 5). Simulate a panic crossing an
    // actively-tracing body: role held + TRACE_BODY_RUNNING set. The cleanup
    // must clear the flag AND release the role so the next trace starts clean.
    #[test]
    fn panic_clears_stuck_trace_guard() {
        let my_tid = current_thread_id();
        TRACE_THREAD_ID.store(my_tid, Ordering::SeqCst);
        TRACE_BODY_RUNNING.with(|f| f.set(true));

        clear_trace_guard_on_panic();

        assert!(
            !TRACE_BODY_RUNNING.with(Cell::get),
            "cleanup must clear TRACE_BODY_RUNNING after a mid-trace panic"
        );
        assert_eq!(
            TRACE_THREAD_ID.load(Ordering::Relaxed),
            0,
            "cleanup must release the trace role after a mid-trace panic"
        );
    }

    // The cleanup must NOT steal a role owned by another thread: if this thread
    // does not own the role, the CAS no-ops and the foreign owner is preserved.
    #[test]
    fn panic_cleanup_does_not_steal_foreign_role() {
        // A foreign owner id distinct from this thread's id.
        let foreign = current_thread_id() + 100_000;
        TRACE_THREAD_ID.store(foreign, Ordering::SeqCst);
        TRACE_BODY_RUNNING.with(|f| f.set(false));

        clear_trace_guard_on_panic();

        assert_eq!(
            TRACE_THREAD_ID.load(Ordering::Relaxed),
            foreign,
            "cleanup must not release a role owned by another thread"
        );
        // Restore for other tests.
        TRACE_THREAD_ID.store(0, Ordering::SeqCst);
    }

    // ── 0130 harvest: Trace ADT field-accessor offset + RC fidelity ───────────
    //
    // These are the intrinsics-owned trace-body-runtime slice of the legacy
    // `ring4_trace_taxonomy.rs` GAPs (FIXME 0130). The legacy file asserted the
    // *type-shape* of each accessor (`name : String`, `params : (SList String)`,
    // …) — that slice is typecheck's (done). The RUNTIME behaviour of the five
    // `cranelisp_trace_*` accessor bodies — that each reads its field at the
    // correct TraceCall offset, returns the stored field value, RC-incs heap
    // fields (so the returned reference is independent of the parent), and
    // consumes the TraceCall under the Decision-24 convention — lives here and
    // was not exercised by any prior unit (the W2 guards cover swap/guard/empty,
    // not the accessors) nor by `tests/trace.rs` (the e2e witnesses the unwrapped
    // value, not the offset/RC fidelity of the accessor body).

    /// Read the RC field (offset 8) of a heap value.
    fn read_rc(ptr: i64) -> i64 {
        unsafe { read_i64(ptr, HeapHeader::RC_OFFSET as usize) }
    }

    /// Build a fully-populated TraceCall ADT (heap String name, two-operand
    /// String SList, String result, one-child SList, nanos) and return its base
    /// pointer plus the heap field pointers the accessors should read back.
    fn build_populated_trace_call() -> (i64, i64, i64, i64, i64, i64) {
        let p0 = alloc_string(b"2") as i64;
        let p1 = alloc_string(b"3") as i64;
        let result = alloc_string(b"5") as i64;
        // One child TraceCall so tchildren is a non-empty SList.
        let child = build_trace_call(
            TraceFrame {
                name: "child".to_string(),
                params: vec![],
                result: 0,
                start: Instant::now(),
                children: vec![],
            },
            7,
        );
        let frame = TraceFrame {
            name: "user/add".to_string(),
            params: vec![p0, p1],
            result,
            start: Instant::now(),
            children: vec![child],
        };
        let trace = build_trace_call(frame, 4242);
        // Read back the stored heap field ptrs the accessors must return.
        let name = unsafe { read_i64(trace, TRACE_TNAME_OFFSET) };
        let params = unsafe { read_i64(trace, TRACE_TPARAMS_OFFSET) };
        let res = unsafe { read_i64(trace, TRACE_TRESULT_OFFSET) };
        let children = unsafe { read_i64(trace, TRACE_TCHILDREN_OFFSET) };
        let nanos = unsafe { read_i64(trace, TRACE_TNANOS_OFFSET) };
        (trace, name, params, res, children, nanos)
    }

    // spec: spec/04-expressions.md §4.12.4 — `name` reads the tname field at the
    // correct offset, returns it, RC-incs it (Decision 24), and consumes the
    // TraceCall.
    #[test]
    fn accessor_name_reads_offset_and_rc_incs_field() {
        let (trace, name, params, result, children, _nanos) =
            build_populated_trace_call();
        let rc_before = read_rc(name);

        let got = cranelisp_trace_name(trace);

        // Correct offset: the returned value IS the stored tname ptr.
        assert_eq!(got, name, "name must read the tname field at offset 24");
        // Decision-24 consuming convention: the accessor RC-incs the field (so
        // the returned reference is independent of the parent) and THEN consumes
        // the TraceCall — whose last-ref drop dec's the field. Net field rc is
        // unchanged (+1 inc, -1 parent-drop), and the returned reference is now
        // the sole live owner (the value is NOT freed).
        assert_eq!(
            read_rc(got),
            rc_before,
            "field rc net-unchanged: +1 accessor inc, -1 parent consume (Decision 24)"
        );
        // Content fidelity.
        assert_eq!(unsafe { crate::heap_string::read_string_as_str(got) }, "user/add");

        // The TraceCall was consumed (rc 1 -> 0 -> freed); the returned name
        // survives because of the inc. Drop the remaining fields + the name's
        // extra ref to balance.
        unsafe { crate::alloc::dealloc(got as *mut u8) }; // the inc'd ref
        // params/result/children were dropped by consume_trace_call; nothing
        // else to free.
        let _ = (params, result, children);
    }

    // spec: spec/04-expressions.md §4.12.4 — `params` reads tparams (offset 32),
    // RC-incs the SList head, consumes the TraceCall.
    #[test]
    fn accessor_params_reads_offset_and_rc_incs_field() {
        let (trace, name, params, result, children, _nanos) =
            build_populated_trace_call();
        let rc_before = read_rc(params);

        let got = cranelisp_trace_params(trace);

        assert_eq!(got, params, "params must read the tparams field at offset 32");
        assert_eq!(
            read_rc(got),
            rc_before,
            "SList-head rc net-unchanged: +1 accessor inc, -1 parent consume"
        );
        // It is a non-empty SList (SCons).
        assert_eq!(unsafe { read_i64(got, PAYLOAD_OFFSET) }, TAG_SCONS);

        // Balance: consume the inc'd SList ref (the TraceCall consumed the
        // original). The SList holds two String heads.
        consume_slist_of_string(got);
        let _ = (name, result, children);
    }

    // spec: spec/04-expressions.md §4.12.4 — `result` reads tresult (offset 40),
    // RC-incs it, consumes the TraceCall.
    #[test]
    fn accessor_result_reads_offset_and_rc_incs_field() {
        let (trace, name, params, result, children, _nanos) =
            build_populated_trace_call();
        let rc_before = read_rc(result);

        let got = cranelisp_trace_result(trace);

        assert_eq!(got, result, "result must read the tresult field at offset 40");
        assert_eq!(
            read_rc(got),
            rc_before,
            "heap-String rc net-unchanged: +1 accessor inc, -1 parent consume"
        );
        assert_eq!(unsafe { crate::heap_string::read_string_as_str(got) }, "5");

        unsafe { crate::alloc::dealloc(got as *mut u8) }; // the inc'd ref
        let _ = (name, params, children);
    }

    // spec: spec/04-expressions.md §4.12.4 — `children` reads tchildren
    // (offset 48), RC-incs the SList head, consumes the TraceCall.
    #[test]
    fn accessor_children_reads_offset_and_rc_incs_field() {
        let (trace, name, params, result, children, _nanos) =
            build_populated_trace_call();
        let rc_before = read_rc(children);

        let got = cranelisp_trace_children(trace);

        assert_eq!(
            got, children,
            "children must read the tchildren field at offset 48"
        );
        assert_eq!(
            read_rc(got),
            rc_before,
            "SList-head rc net-unchanged: +1 accessor inc, -1 parent consume"
        );
        assert_eq!(unsafe { read_i64(got, PAYLOAD_OFFSET) }, TAG_SCONS);

        consume_slist_of_trace(got); // balance the inc'd ref
        let _ = (name, params, result);
    }

    // spec: spec/04-expressions.md §4.12.4 — `nanos` reads tnanos (offset 56) as
    // a bare Int (no RC-inc — payload is not heap-typed) and consumes the
    // TraceCall.
    #[test]
    fn accessor_nanos_reads_offset_no_rc_inc() {
        let (trace, _name, _params, _result, _children, nanos) =
            build_populated_trace_call();
        assert_eq!(nanos, 4242, "tnanos stored at offset 56");

        let got = cranelisp_trace_nanos(trace);

        assert_eq!(got, 4242, "nanos must read the tnanos Int field at offset 56");
        // The TraceCall was consumed; all heap fields freed. Nothing survives
        // (nanos is a bare Int, not RC-managed).
    }

    // spec: spec/04-expressions.md §4.12.4 + appendix-a-builtins — the /run-tests
    // helper `cranelisp_trace_first_child_nanos` walks tchildren -> first SCons
    // head -> that child's tnanos (offset 56), then consumes the root under the
    // Decision-24 convention. Build a root whose single child carries a known
    // nanos value.
    #[test]
    fn first_child_nanos_walks_slist_to_child_tnanos() {
        let child = build_trace_call(
            TraceFrame {
                name: "child".to_string(),
                params: vec![],
                result: 0,
                start: Instant::now(),
                children: vec![],
            },
            999,
        );
        let root = build_trace_call(
            TraceFrame {
                name: "::trace::".to_string(),
                params: vec![],
                result: 0,
                start: Instant::now(),
                children: vec![child],
            },
            1,
        );

        let got = cranelisp_trace_first_child_nanos(root);
        assert_eq!(got, 999, "must return the first child's tnanos");
        // Root (and its child) consumed by the accessor.
    }

    // spec: spec/04-expressions.md §4.12.4 — first_child_nanos over a childless
    // root returns 0 (SNil tchildren) and still consumes the root.
    #[test]
    fn first_child_nanos_empty_children_returns_zero() {
        let root = build_trace_call(
            TraceFrame {
                name: "::trace::".to_string(),
                params: vec![],
                result: 0,
                start: Instant::now(),
                children: vec![],
            },
            1,
        );
        assert_eq!(
            cranelisp_trace_first_child_nanos(root),
            0,
            "no children -> 0"
        );
    }

    // ── 0130 harvest: ::skipped:: concurrent-skip sentinel ────────────────────
    //
    // `tracing.md` §thread-safety: when a DIFFERENT thread already owns the trace
    // role, `cranelisp_trace_swap_got` does NOT swap — it pushes a `::skipped::`
    // sentinel frame and returns SENTINEL_SAVED_GOT (the concurrent-trace skip).
    // This is the `current_owner != my_tid` branch; the W2 guards cover only the
    // same-thread (`current_owner == my_tid`) branches. Simulate a foreign owner
    // and assert the skip path. `restore_got` on the sentinel is a no-op.
    //
    // spec: spec/04-expressions.md §4.12.5 — concurrent trace on another thread
    // is skipped, not nested.
    #[test]
    fn concurrent_foreign_owner_skips_with_sentinel() {
        // Install a FOREIGN owner (distinct from this thread's id).
        let foreign = current_thread_id() + 100_000;
        TRACE_THREAD_ID.store(foreign, Ordering::SeqCst);
        TRACE_BODY_RUNNING.with(|f| f.set(false));
        let stack_depth_before = lock_trace_stack().len();
        let _ = crate::panic::take_runtime_error();

        let mut got = vec![0i64; GOT_TABLE_SIZE];
        let base = got.as_mut_ptr() as i64;
        let slots: Vec<u32> = vec![0];
        let wrappers: Vec<i64> = vec![0xabcd];

        let saved = cranelisp_trace_swap_got(
            base,
            1,
            slots.as_ptr() as i64,
            wrappers.as_ptr() as i64,
        );

        // Skipped: returns the sentinel, does NOT touch the GOT, does NOT raise.
        assert_eq!(
            saved, SENTINEL_SAVED_GOT,
            "concurrent foreign-owned trace must return the skip sentinel"
        );
        assert_eq!(got[0], 0, "skipped swap must NOT install a wrapper into the GOT");
        assert!(
            crate::panic::take_runtime_error().is_none(),
            "concurrent skip is NOT an error (distinct from same-thread nesting)"
        );

        // A `::skipped::` sentinel frame was pushed.
        let mut stack = lock_trace_stack();
        assert_eq!(
            stack.len(),
            stack_depth_before + 1,
            "skip must push exactly one sentinel frame"
        );
        assert_eq!(
            stack.last().map(|f| f.name.as_str()),
            Some("::skipped::"),
            "the pushed sentinel frame must be named ::skipped::"
        );
        stack.pop(); // remove our sentinel
        drop(stack);

        // restore_got on the sentinel is a no-op (does not touch the GOT).
        cranelisp_trace_restore_got(base, SENTINEL_SAVED_GOT);
        assert_eq!(got[0], 0, "restore on sentinel must be a no-op");

        // Restore global state.
        TRACE_THREAD_ID.store(0, Ordering::SeqCst);
    }

    // spec: spec/04-expressions.md §4.12.2 — the synthetic ROOT frame on
    // role-acquire is named `::trace::` (distinct from the `::skipped::`
    // sentinel). First swap by an unowned thread claims the role and pushes the
    // `::trace::` root.
    #[test]
    fn first_swap_pushes_trace_root_frame() {
        TRACE_THREAD_ID.store(0, Ordering::SeqCst);
        TRACE_BODY_RUNNING.with(|f| f.set(false));
        SWAPPED_GOT_BASES.with(|s| s.borrow_mut().clear());
        lock_trace_stack().clear();
        let _ = crate::panic::take_runtime_error();

        let mut got = vec![0i64; GOT_TABLE_SIZE];
        let base = got.as_mut_ptr() as i64;
        let slots: Vec<u32> = vec![0];
        let wrappers: Vec<i64> = vec![0x1234];

        let saved = cranelisp_trace_swap_got(
            base,
            1,
            slots.as_ptr() as i64,
            wrappers.as_ptr() as i64,
        );
        assert_ne!(saved, SENTINEL_SAVED_GOT, "first swap claims the role");
        assert_eq!(
            got[0], 0x1234,
            "first swap installs the wrapper into the GOT slot"
        );
        // The synthetic root frame is named ::trace:: (NOT ::skipped::).
        {
            let stack = lock_trace_stack();
            assert_eq!(
                stack.last().map(|f| f.name.as_str()),
                Some("::trace::"),
                "role-acquire pushes the ::trace:: synthetic root"
            );
        }

        // Cleanup.
        cranelisp_trace_restore_got(base, saved);
        lock_trace_stack().clear();
        TRACE_THREAD_ID.store(0, Ordering::SeqCst);
        SWAPPED_GOT_BASES.with(|s| s.borrow_mut().clear());
    }
}
