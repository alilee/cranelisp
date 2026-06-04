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
    /// is a re-entrant `(trace (trace ...))` and raises a runtime error.
    static TRACE_BODY_RUNNING: Cell<bool> = const { Cell::new(false) };
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
/// # Safety
/// `base` must be a valid pointer with at least `offset + 8` bytes available.
unsafe fn write_i64(base: i64, offset: usize, value: i64) {
    unsafe { *((base as *mut u8).add(offset) as *mut i64) = value }
}

/// Read an i64 value at a byte offset from a base pointer.
///
/// # Safety
/// `base` must be a valid pointer with at least `offset + 8` bytes readable.
unsafe fn read_i64(base: i64, offset: usize) -> i64 {
    unsafe { *((base as *const u8).add(offset) as *const i64) }
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
    let my_tid = current_thread_id();
    let current_owner = TRACE_THREAD_ID.load(Ordering::Relaxed);

    if current_owner == 0 {
        // Try to claim the trace role (CAS 0 -> my_tid).
        if TRACE_THREAD_ID
            .compare_exchange(0, my_tid, Ordering::SeqCst, Ordering::Relaxed)
            .is_err()
        {
            // Race: another thread just claimed it -> push sentinel frame, skip.
            lock_trace_stack().push(TraceFrame {
                name: "::skipped::".to_string(),
                params: vec![],
                result: 0,
                start: Instant::now(),
                children: vec![],
            });
            return SENTINEL_SAVED_GOT;
        }
        // Successfully claimed. Push the synthetic root frame.
        lock_trace_stack().push(TraceFrame {
            name: "::trace::".to_string(),
            params: vec![],
            result: 0,
            start: Instant::now(),
            children: vec![],
        });
    } else if current_owner != my_tid {
        // A different thread owns the trace role -> skip (concurrent trace).
        lock_trace_stack().push(TraceFrame {
            name: "::skipped::".to_string(),
            params: vec![],
            result: 0,
            start: Instant::now(),
            children: vec![],
        });
        return SENTINEL_SAVED_GOT;
    } else {
        // current_owner == my_tid. Distinguish:
        //   - legitimate multi-module swap (body not yet running)  => proceed
        //   - re-entrant (trace (trace ...)) (body running)        => ERROR
        // The boundary flag is raised by the first `cranelisp_trace_enter`
        // after role-acquire (the first wrapper to fire). All swap_got calls
        // for one trace form precede any wrapper, so a legitimate multi-module
        // swap sees the flag still false; an inner form's swap_got runs while
        // an outer wrapper is on the stack, so it sees the flag true.
        if TRACE_BODY_RUNNING.with(Cell::get) {
            let msg = "nested trace is not supported: (trace ...) may not appear \
                       inside an actively-tracing (trace ...)";
            crate::panic::runtime_panic(msg.as_ptr(), msg.len());
            return SENTINEL_SAVED_GOT;
        }
    }

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
// This is the cross-crate ABI between backend (the emitter — FIXME 0255) and
// intrinsics (the reader — `cranelisp_trace_format`, below). Backend bakes one
// descriptor tree per traced param/result; `cranelisp_trace_format` walks it
// against the runtime heap value with ZERO symbol-table access and NO
// thread-local state. The full layout contract is documented on the types
// below — read it before touching either side.

/// Kind tag for a [`DisplayDescriptor`] (the `kind` field, an `i32`).
///
/// One discriminant per renderable value shape, mirroring `int`'s
/// `format_field_value` match. The numeric values are part of the cross-crate
/// ABI — backend bakes these integers; do not renumber without a coordinated
/// backend change (FIXME 0255).
///
/// # ABI: stable discriminants
/// `#[repr(i32)]` so the discriminant is a fixed-width field backend can emit
/// as a plain `iconst`.
#[repr(i32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DescriptorKind {
    /// Decimal integer. No children, no payload.
    Int = 0,
    /// `true` / `false`. No children, no payload.
    Bool = 1,
    /// `d.d` float (mandatory `.0`). No children, no payload.
    Float = 2,
    /// Quoted string (`"…"`). Value is a `HeapString` pointer. No children.
    String = 3,
    /// `<closure>`. No children, no payload.
    Fn = 4,
    /// `[e1 e2 …]`. Exactly ONE child descriptor (the element renderer);
    /// `child0` is its self-relative offset. Value is a `HeapVec` pointer.
    Vec = 5,
    /// `Type.Ctor` (nullary) / `(Type.Ctor f1 f2 …)` (data) per spec §1.5.
    /// Carries the type-name string + a per-constructor table baked into the
    /// blob; see [`DisplayDescriptor`] for the Adt encoding.
    Adt = 6,
    /// Residual type variable — bare `value` fallback. A monomorphic trace
    /// should not hit this (backend bakes the substituted concrete descriptor);
    /// it exists as a defensive default. No children.
    TypeVar = 7,
}

/// One node in a baked display descriptor (the `#[repr(C)]` cross-crate ABI).
///
/// # Encoding overview — ONE encoding for BOTH modes
///
/// A descriptor TREE is laid out as a flat, **position-independent arena blob**:
/// a contiguous byte buffer holding descriptor records and the variable-length
/// data they reference (string bytes, constructor tables). Every cross-reference
/// inside the blob is a **self-relative byte offset** — an `i32` measured from
/// the address of the offset field itself — NOT an absolute pointer. The blob
/// therefore contains no absolute addresses and needs **no intra-blob
/// relocations**; it is identical in JIT mode (leaked `Box<[u8]>`, address
/// embedded as an `iconst`) and object mode (a `.rodata` data symbol, one
/// relocation for the wrapper's reference to the blob root). This is the single
/// encoding `/arch` blessed (`tracing.md` §3.4 "arena blob with offset-relative
/// child links"). `cranelisp_trace_format` receives a pointer to ONE
/// `DisplayDescriptor` record (the blob root for that value) and follows the
/// self-relative offsets to reach children/strings/ctor-tables.
///
/// **Self-relative offset convention (the single rule).** A field of type
/// "self-relative offset" holds an `i32`. The referent address is
/// `(&field as *const i32 as isize + offset as isize) as *const T`. A `0`
/// offset means "absent" (no child / no string / empty table). Because the
/// offset is measured from the field's own address, the same encoded blob
/// works no matter where the blob is loaded — JIT heap or `.rodata`.
///
/// # Record layout (`#[repr(C)]`, all fields naturally aligned)
///
/// | Offset | Field        | Type  | Meaning |
/// |-------:|--------------|-------|---------|
/// | 0      | `kind`       | `i32` | [`DescriptorKind`] discriminant. |
/// | 4      | `_pad`       | `i32` | Reserved (zero); keeps `name_off` 8-aligned-friendly and the record a round 24 bytes. |
/// | 8      | `name_off`   | `i32` | Self-relative offset to a `BlobStr` (the type name, Adt only; `0` otherwise). |
/// | 12     | `child0_off` | `i32` | Self-relative offset to the first/only child descriptor (`Vec` element; `0` otherwise). |
/// | 16     | `ctors_off`  | `i32` | Self-relative offset to a `CtorTable` (Adt only; `0` otherwise). |
/// | 20     | `_pad2`      | `i32` | Reserved (zero). |
///
/// `size_of::<DisplayDescriptor>() == 24`, `align_of == 4`. Backend MUST emit
/// records at 4-byte-aligned blob offsets.
///
/// # `BlobStr` — a length-prefixed byte string inside the blob
///
/// A `BlobStr` is `[ len: i32 | bytes: [u8; len] ]` (NOT NUL-terminated —
/// length-prefixed, so embedded NULs and exact byte counts are safe). It is
/// referenced by a self-relative offset (to the `len` field). The bytes are
/// raw UTF-8.
///
/// # `CtorTable` — the Adt per-constructor table inside the blob
///
/// Referenced from `ctors_off`. Layout:
/// `[ n_ctors: i32 | single_match: i32 | CtorEntry[n_ctors] ]` where
/// `single_match` is `1` iff the type has exactly one constructor whose name
/// equals the type name (the `Type.` prefix is suppressed per spec §1.5), else
/// `0`. Each `CtorEntry` is:
/// `[ tag: i32 | n_fields: i32 | name_off: i32 | fields_off: i32 ]`
/// — `tag` is the runtime constructor tag, `name_off` is a self-relative offset
/// (from the `CtorEntry`'s `name_off` field) to a `BlobStr` (ctor name), and
/// `fields_off` is a self-relative offset (from the `CtorEntry`'s `fields_off`
/// field) to an array of `n_fields` self-relative `i32` offsets, each pointing
/// to that field's child [`DisplayDescriptor`]. (The two-level indirection
/// keeps every cross-link a self-relative `i32`.)
///
/// # Lifetime
///
/// Descriptors are program-lifetime (JIT: leaked; object: static `.rodata`),
/// never freed. `cranelisp_trace_format` only reads them.
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct DisplayDescriptor {
    /// [`DescriptorKind`] discriminant.
    pub kind: i32,
    /// Reserved (zero).
    pub _pad: i32,
    /// Self-relative offset to the type-name `BlobStr` (Adt only; else 0).
    pub name_off: i32,
    /// Self-relative offset to the first/only child descriptor (Vec element;
    /// else 0).
    pub child0_off: i32,
    /// Self-relative offset to the `CtorTable` (Adt only; else 0).
    pub ctors_off: i32,
    /// Reserved (zero).
    pub _pad2: i32,
}

const _: () = assert!(std::mem::size_of::<DisplayDescriptor>() == 24);
const _: () = assert!(std::mem::align_of::<DisplayDescriptor>() == 4);

// ── Self-relative-offset readers (the blob-walk primitives) ────────────────────

/// Resolve a self-relative offset stored at `field_ptr` to a typed pointer.
/// Returns `None` when the offset is 0 ("absent").
///
/// # Safety
/// `field_ptr` must point to a valid `i32` inside a descriptor blob, and the
/// referent (if the offset is non-zero) must be a valid `T` inside the same
/// blob.
unsafe fn follow_self_rel<T>(field_ptr: *const i32) -> Option<*const T> {
    let off = unsafe { *field_ptr };
    if off == 0 {
        return None;
    }
    let base = field_ptr as isize;
    Some((base + off as isize) as *const T)
}

/// Read a `BlobStr` (`[len:i32 | bytes]`) at `ptr` as a `&str`.
///
/// # Safety
/// `ptr` must point to a valid `BlobStr` inside a descriptor blob.
unsafe fn read_blob_str<'a>(ptr: *const i32) -> &'a str {
    let len = unsafe { *ptr } as usize;
    let bytes = unsafe { std::slice::from_raw_parts(ptr.add(1) as *const u8, len) };
    // Backend bakes valid UTF-8 (type/constructor names are Rust strings).
    std::str::from_utf8(bytes).unwrap_or("<bad-utf8>")
}

// ── The pure descriptor-driven formatter ───────────────────────────────────────

/// Format a runtime value as a cranelisp heap String, driven entirely by a
/// backend-baked [`DisplayDescriptor`].
///
/// `value` is the runtime value (an `i64` scalar or a heap pointer);
/// `descriptor_ptr` is a `*const DisplayDescriptor` (the blob root for this
/// value's static type). Returns a heap `String` (alloc-base pointer, RC=1) —
/// the same shape `alloc_string` produces.
///
/// **Purity (BC §4b invariant 12).** This intrinsic performs ZERO symbol-table
/// access and holds NO thread-local state. Everything `format_value` used to
/// resolve from the live `symbol_tables` (ADT constructor names, field layouts,
/// single-ctor suppression) is baked into the descriptor at codegen. It reuses
/// only the heap-layout reads intrinsics already owns (`HeapString` len/bytes,
/// `HeapVec` len/data, the base-pointer ADT tag/field offsets).
///
/// Arity is `(2, true)` — backend's `declare_trace_extern("cranelisp_trace_format",
/// 2, true)` is unchanged.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_format(value: i64, descriptor_ptr: i64) -> i64 {
    let s = if descriptor_ptr == 0 {
        // Defensive: no descriptor -> bare value.
        format!("{value}")
    } else {
        // SAFETY: backend guarantees descriptor_ptr is a valid blob-root
        // DisplayDescriptor for the static type of `value`.
        unsafe { render_value(value, descriptor_ptr as *const DisplayDescriptor) }
    };
    alloc_string(s.as_bytes()) as i64
}

/// Render `value` per `desc` to a Rust `String` (no `:Type` prefix).
///
/// # Safety
/// `desc` must point to a valid [`DisplayDescriptor`] blob root, and `value`
/// must be consistent with that descriptor's kind (scalar or the right heap
/// shape).
unsafe fn render_value(value: i64, desc: *const DisplayDescriptor) -> String {
    let kind = unsafe { (*desc).kind };
    match kind {
        k if k == DescriptorKind::Int as i32 => format!("{value}"),
        k if k == DescriptorKind::Bool as i32 => {
            if value != 0 { "true".to_string() } else { "false".to_string() }
        }
        k if k == DescriptorKind::Float as i32 => {
            let f = f64::from_bits(value as u64);
            let s = format!("{f}");
            if s.contains('.') { s } else { format!("{s}.0") }
        }
        k if k == DescriptorKind::String as i32 => {
            if value == 0 || (value as usize) < cranelisp_types::NULLARY_TAG_THRESHOLD {
                format!("<invalid-string:{value}>")
            } else {
                // SAFETY: value is a heap HeapString pointer (guarded above).
                let s = unsafe { crate::heap_string::read_string_as_str(value) };
                format!("\"{s}\"")
            }
        }
        k if k == DescriptorKind::Fn as i32 => "<closure>".to_string(),
        k if k == DescriptorKind::Vec as i32 => unsafe { render_vec(value, desc) },
        k if k == DescriptorKind::Adt as i32 => unsafe { render_adt(value, desc) },
        // TypeVar (residual) and any unknown kind: bare value fallback.
        _ => format!("{value}"),
    }
}

/// Render a `HeapVec` value as `[e1 e2 …]` using the single child descriptor.
///
/// # Safety
/// `desc.kind == Vec`; `value` is a `HeapVec` pointer or nullary.
unsafe fn render_vec(value: i64, desc: *const DisplayDescriptor) -> String {
    if value == 0 || (value as usize) < cranelisp_types::NULLARY_TAG_THRESHOLD {
        return "[]".to_string();
    }
    let base = value as *const u8;
    // SAFETY: value is a heap HeapVec pointer (guarded above).
    let len = unsafe {
        *(base.add(crate::vec_runtime::LEN_OFFSET) as *const i64)
    } as usize;
    if len == 0 {
        return "[]".to_string();
    }
    let data_ptr = unsafe {
        *(base.add(crate::vec_runtime::DATA_PTR_OFFSET) as *const *const i64)
    };
    if data_ptr.is_null() {
        return "[]".to_string();
    }
    // Resolve the element child descriptor (self-relative from child0_off).
    let child0_field = unsafe { ptr::addr_of!((*desc).child0_off) };
    let elem_desc: Option<*const DisplayDescriptor> =
        unsafe { follow_self_rel(child0_field) };
    let mut elems = Vec::with_capacity(len);
    for i in 0..len {
        let elem_val = unsafe { *data_ptr.add(i) };
        let formatted = match elem_desc {
            Some(ed) => unsafe { render_value(elem_val, ed) },
            None => format!("{elem_val}"),
        };
        elems.push(formatted);
    }
    format!("[{}]", elems.join(" "))
}

/// Render an Adt value per spec §1.5 using the baked constructor table.
///
/// Nullary: `Type.Ctor` (or bare `Ctor` if single-match). Data:
/// `(Type.Ctor f1 f2 …)` (or `(Ctor …)` if single-match).
///
/// # Safety
/// `desc.kind == Adt`; `value` is a nullary tag or a `HeapAdt` pointer.
unsafe fn render_adt(value: i64, desc: *const DisplayDescriptor) -> String {
    // Type name (for the Type.Ctor prefix). May be absent defensively.
    let name_field = unsafe { ptr::addr_of!((*desc).name_off) };
    let type_name: &str = match unsafe { follow_self_rel::<i32>(name_field) } {
        Some(p) => unsafe { read_blob_str(p) },
        None => "",
    };

    // Constructor table.
    let ctors_field = unsafe { ptr::addr_of!((*desc).ctors_off) };
    let Some(ctab) = (unsafe { follow_self_rel::<i32>(ctors_field) }) else {
        // No ctor table -> bare value fallback.
        return format!("{value}");
    };
    // CtorTable: [ n_ctors:i32 | single_match:i32 | CtorEntry[n] ]
    let n_ctors = unsafe { *ctab } as usize;
    let single_match = unsafe { *ctab.add(1) } != 0;
    // CtorEntry stride = 4 i32s (tag, n_fields, name_off, fields_off).
    let entries_base = unsafe { ctab.add(2) };

    let is_nullary = (value as usize) < cranelisp_types::NULLARY_TAG_THRESHOLD;
    let runtime_tag: i64 = if is_nullary {
        value
    } else {
        // Heap ADT: tag at PAYLOAD_OFFSET (16).
        unsafe { *((value as *const u8).add(PAYLOAD_OFFSET) as *const i64) }
    };

    // Find the CtorEntry whose tag matches.
    let mut found: Option<*const i32> = None;
    for i in 0..n_ctors {
        let entry = unsafe { entries_base.add(i * 4) };
        let tag = unsafe { *entry } as i64;
        if tag == runtime_tag {
            found = Some(entry);
            break;
        }
    }
    let Some(entry) = found else {
        return format!("<unknown-tag:{runtime_tag}>");
    };
    let n_fields = unsafe { *entry.add(1) } as usize;
    let ctor_name_field = unsafe { entry.add(2) };
    let ctor_name: &str = match unsafe { follow_self_rel::<i32>(ctor_name_field) } {
        Some(p) => unsafe { read_blob_str(p) },
        None => "<ctor>",
    };

    let ctor_display = if single_match {
        ctor_name.to_string()
    } else {
        format!("{type_name}.{ctor_name}")
    };

    if n_fields == 0 || is_nullary {
        // Nullary constructor: just the constructor display.
        return ctor_display;
    }

    // Data constructor: read each field + its child descriptor.
    let fields_off_field = unsafe { entry.add(3) };
    let Some(field_offs) = (unsafe { follow_self_rel::<i32>(fields_off_field) }) else {
        return ctor_display;
    };
    let mut field_strs = Vec::with_capacity(n_fields);
    for i in 0..n_fields {
        // field_offs[i] is a self-relative offset (from its own address) to the
        // field's child DisplayDescriptor.
        let off_field = unsafe { field_offs.add(i) };
        let field_desc: Option<*const DisplayDescriptor> =
            unsafe { follow_self_rel(off_field) };
        // Field value at FIELD0_OFFSET + i*8 of the heap ADT.
        let field_val = unsafe {
            *((value as *const u8).add(FIELD0_OFFSET + i * 8) as *const i64)
        };
        let s = match field_desc {
            Some(fd) => unsafe { render_value(field_val, fd) },
            None => format!("{field_val}"),
        };
        field_strs.push(s);
    }
    format!("({ctor_display} {})", field_strs.join(" "))
}

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

    // ── DisplayDescriptor — blob-building helpers for tests ───────────────────
    //
    // These build descriptor blobs *by hand* into a Vec<u8>, exactly as backend
    // (FIXME 0255) will, then exercise `cranelisp_trace_format` against them.
    // The builder mirrors the documented arena-blob encoding: records and data
    // packed contiguously, cross-links as self-relative i32 offsets.

    /// A tiny arena-blob builder. All cross-links use self-relative i32 offsets.
    struct BlobBuilder {
        buf: Vec<u8>,
    }

    impl BlobBuilder {
        fn new() -> Self {
            BlobBuilder { buf: Vec::new() }
        }

        fn align4(&mut self) {
            while !self.buf.len().is_multiple_of(4) {
                self.buf.push(0);
            }
        }

        fn pos(&self) -> usize {
            self.buf.len()
        }

        /// Reserve a 24-byte descriptor record, return its offset.
        fn reserve_desc(&mut self) -> usize {
            self.align4();
            let at = self.buf.len();
            self.buf.extend_from_slice(&[0u8; 24]);
            at
        }

        fn write_i32(&mut self, at: usize, v: i32) {
            self.buf[at..at + 4].copy_from_slice(&v.to_le_bytes());
        }

        /// Set a descriptor field to a self-relative offset pointing at `target`.
        /// `field_index` is 0=kind,1=_pad,2=name_off,3=child0_off,4=ctors_off,5=_pad2.
        fn set_desc_kind(&mut self, desc_at: usize, kind: DescriptorKind) {
            self.write_i32(desc_at, kind as i32);
        }

        fn set_self_rel(&mut self, field_at: usize, target_at: usize) {
            let rel = target_at as isize - field_at as isize;
            self.write_i32(field_at, rel as i32);
        }

        /// Append a BlobStr ([len:i32 | bytes]); return its offset.
        fn append_str(&mut self, s: &str) -> usize {
            self.align4();
            let at = self.buf.len();
            self.buf.extend_from_slice(&(s.len() as i32).to_le_bytes());
            self.buf.extend_from_slice(s.as_bytes());
            at
        }

        /// Pointer to the blob root (after building). The Vec must outlive use.
        fn root_ptr(&self) -> *const DisplayDescriptor {
            self.buf.as_ptr() as *const DisplayDescriptor
        }

        fn ptr_at(&self, at: usize) -> *const DisplayDescriptor {
            unsafe { self.buf.as_ptr().add(at) as *const DisplayDescriptor }
        }
    }

    /// Read back the heap String produced by `cranelisp_trace_format`.
    fn read_format_result(value: i64, desc_ptr: i64) -> String {
        let s_heap = cranelisp_trace_format(value, desc_ptr);
        let s = unsafe { crate::heap_string::read_string_as_str(s_heap) }.to_string();
        unsafe { crate::alloc::dealloc(s_heap as *mut u8) };
        s
    }

    // spec: spec/04-expressions.md §4.12.2 / §12.9 — scalar trace formatting
    #[test]
    fn descriptor_int() {
        let mut b = BlobBuilder::new();
        let d = b.reserve_desc();
        b.set_desc_kind(d, DescriptorKind::Int);
        assert_eq!(read_format_result(42, b.root_ptr() as i64), "42");
        assert_eq!(read_format_result(-7, b.root_ptr() as i64), "-7");
    }

    #[test]
    fn descriptor_bool() {
        let mut b = BlobBuilder::new();
        let d = b.reserve_desc();
        b.set_desc_kind(d, DescriptorKind::Bool);
        assert_eq!(read_format_result(1, b.root_ptr() as i64), "true");
        assert_eq!(read_format_result(0, b.root_ptr() as i64), "false");
    }

    #[test]
    fn descriptor_float() {
        let mut b = BlobBuilder::new();
        let d = b.reserve_desc();
        b.set_desc_kind(d, DescriptorKind::Float);
        let bits = 1.0_f64.to_bits() as i64;
        assert_eq!(read_format_result(bits, b.root_ptr() as i64), "1.0");
        let bits2 = 3.5_f64.to_bits() as i64;
        assert_eq!(read_format_result(bits2, b.root_ptr() as i64), "3.5");
    }

    #[test]
    fn descriptor_string() {
        let mut b = BlobBuilder::new();
        let d = b.reserve_desc();
        b.set_desc_kind(d, DescriptorKind::String);
        let heap_s = alloc_string(b"hello") as i64;
        assert_eq!(read_format_result(heap_s, b.root_ptr() as i64), "\"hello\"");
        unsafe { crate::alloc::dealloc(heap_s as *mut u8) };
    }

    #[test]
    fn descriptor_fn() {
        let mut b = BlobBuilder::new();
        let d = b.reserve_desc();
        b.set_desc_kind(d, DescriptorKind::Fn);
        assert_eq!(read_format_result(0, b.root_ptr() as i64), "<closure>");
    }

    #[test]
    fn descriptor_typevar_fallback() {
        let mut b = BlobBuilder::new();
        let d = b.reserve_desc();
        b.set_desc_kind(d, DescriptorKind::TypeVar);
        assert_eq!(read_format_result(99, b.root_ptr() as i64), "99");
    }

    // spec: spec/04-expressions.md §12.9 — Vec element formatting
    #[test]
    fn descriptor_vec_of_int() {
        // Build blob: [ root(Vec) | child(Int) ].
        let mut b = BlobBuilder::new();
        let root = b.reserve_desc();
        let child = b.reserve_desc();
        b.set_desc_kind(root, DescriptorKind::Vec);
        b.set_desc_kind(child, DescriptorKind::Int);
        // child0_off is field index 3 -> byte offset root + 12.
        b.set_self_rel(root + 12, child);

        // Build a HeapVec of [1, 2, 3].
        let vec_ptr = crate::vec_runtime::vec_new(3);
        let v = crate::vec_runtime::vec_push_grow(vec_ptr, 1);
        let v = crate::vec_runtime::vec_push_grow(v, 2);
        let v = crate::vec_runtime::vec_push_grow(v, 3);

        let out = read_format_result(v, b.ptr_at(root) as i64);
        assert_eq!(out, "[1 2 3]");
        crate::vec_runtime::vec_drop(v, 0);
    }

    #[test]
    fn descriptor_vec_empty() {
        let mut b = BlobBuilder::new();
        let root = b.reserve_desc();
        let child = b.reserve_desc();
        b.set_desc_kind(root, DescriptorKind::Vec);
        b.set_desc_kind(child, DescriptorKind::Int);
        b.set_self_rel(root + 12, child);
        let vec_ptr = crate::vec_runtime::vec_new(0);
        assert_eq!(read_format_result(vec_ptr, b.ptr_at(root) as i64), "[]");
        crate::vec_runtime::vec_drop(vec_ptr, 0);
    }

    // spec: spec/04-expressions.md §1.5 — ADT constructor dot notation
    //
    // Builds a `(deftype Color Red Green Blue)`-style nullary enum descriptor
    // plus a `(deftype (Option a) None (Some [:a val]))`-style nested data ADT
    // to exercise both the nullary and data paths + nesting.
    #[test]
    fn descriptor_adt_nullary_enum() {
        // type Color { Red=0, Green=1, Blue=2 } — multi-ctor, no single-match.
        let mut b = BlobBuilder::new();
        let root = b.reserve_desc();
        b.set_desc_kind(root, DescriptorKind::Adt);
        let type_name = b.append_str("Color");
        // CtorTable: [n_ctors=3 | single_match=0 | 3 x CtorEntry(4 i32)].
        b.align4();
        let ctab = b.pos();
        b.buf.extend_from_slice(&3i32.to_le_bytes()); // n_ctors
        b.buf.extend_from_slice(&0i32.to_le_bytes()); // single_match
        // Reserve 3 entries (4 i32 each).
        let entries_at = b.pos();
        b.buf.extend_from_slice(&[0u8; 3 * 16]);
        // Names.
        let red = b.append_str("Red");
        let green = b.append_str("Green");
        let blue = b.append_str("Blue");
        // Fill entries: tag, n_fields=0, name_off (self-rel), fields_off=0.
        for (i, (tag, name_at)) in [(0, red), (1, green), (2, blue)].iter().enumerate() {
            let e = entries_at + i * 16;
            b.write_i32(e, *tag); // tag
            b.write_i32(e + 4, 0); // n_fields
            b.set_self_rel(e + 8, *name_at); // name_off
            b.write_i32(e + 12, 0); // fields_off
        }
        // Link root.name_off (offset root+8) and root.ctors_off (offset root+16).
        b.set_self_rel(root + 8, type_name);
        b.set_self_rel(root + 16, ctab);

        assert_eq!(read_format_result(0, b.ptr_at(root) as i64), "Color.Red");
        assert_eq!(read_format_result(1, b.ptr_at(root) as i64), "Color.Green");
        assert_eq!(read_format_result(2, b.ptr_at(root) as i64), "Color.Blue");
    }

    #[test]
    fn descriptor_adt_nested_data() {
        // type Option a { None=0, Some(a)=1 }, instantiated at Int.
        // We render `(Some 42)`.
        let mut b = BlobBuilder::new();
        let root = b.reserve_desc();
        let int_field = b.reserve_desc(); // descriptor for the Some field (Int)
        b.set_desc_kind(root, DescriptorKind::Adt);
        b.set_desc_kind(int_field, DescriptorKind::Int);
        let type_name = b.append_str("Option");
        // CtorTable: [n=2 | single_match=0 | 2 entries].
        b.align4();
        let ctab = b.pos();
        b.buf.extend_from_slice(&2i32.to_le_bytes());
        b.buf.extend_from_slice(&0i32.to_le_bytes());
        let entries_at = b.pos();
        b.buf.extend_from_slice(&[0u8; 2 * 16]);
        let none_name = b.append_str("None");
        let some_name = b.append_str("Some");
        // Some has 1 field -> a fields_off array of 1 self-rel i32.
        b.align4();
        let some_fields = b.pos();
        b.buf.extend_from_slice(&0i32.to_le_bytes()); // placeholder for field0 off
        // field0 self-rel -> int_field descriptor.
        b.set_self_rel(some_fields, int_field);

        // Entry 0: None tag=0 n_fields=0.
        let e0 = entries_at;
        b.write_i32(e0, 0);
        b.write_i32(e0 + 4, 0);
        b.set_self_rel(e0 + 8, none_name);
        b.write_i32(e0 + 12, 0);
        // Entry 1: Some tag=1 n_fields=1.
        let e1 = entries_at + 16;
        b.write_i32(e1, 1);
        b.write_i32(e1 + 4, 1);
        b.set_self_rel(e1 + 8, some_name);
        b.set_self_rel(e1 + 12, some_fields);

        b.set_self_rel(root + 8, type_name);
        b.set_self_rel(root + 16, ctab);

        // None is nullary tag 0.
        assert_eq!(read_format_result(0, b.ptr_at(root) as i64), "Option.None");

        // Build a heap (Some 42): [hdr | tag=1 | field0=42].
        let some_val = alloc_adt(1, &[42]);
        assert_eq!(
            read_format_result(some_val, b.ptr_at(root) as i64),
            "(Option.Some 42)"
        );
        // The Some cell holds an Int field (not heap), free the cell directly.
        unsafe { crate::alloc::dealloc(some_val as *mut u8) };
    }

    #[test]
    fn descriptor_adt_single_match_product() {
        // type Point { Point(Int, Int) } — single ctor whose name == type name.
        // single_match=1 suppresses the `Point.` prefix -> `(Point 3 4)`.
        let mut b = BlobBuilder::new();
        let root = b.reserve_desc();
        let f0 = b.reserve_desc();
        let f1 = b.reserve_desc();
        b.set_desc_kind(root, DescriptorKind::Adt);
        b.set_desc_kind(f0, DescriptorKind::Int);
        b.set_desc_kind(f1, DescriptorKind::Int);
        let type_name = b.append_str("Point");
        b.align4();
        let ctab = b.pos();
        b.buf.extend_from_slice(&1i32.to_le_bytes()); // n_ctors
        b.buf.extend_from_slice(&1i32.to_le_bytes()); // single_match = 1
        let entries_at = b.pos();
        b.buf.extend_from_slice(&[0u8; 16]);
        let point_name = b.append_str("Point");
        b.align4();
        let fields = b.pos();
        b.buf.extend_from_slice(&[0u8; 8]); // 2 field offsets
        b.set_self_rel(fields, f0);
        b.set_self_rel(fields + 4, f1);
        // Entry 0: Point tag=0 n_fields=2.
        b.write_i32(entries_at, 0);
        b.write_i32(entries_at + 4, 2);
        b.set_self_rel(entries_at + 8, point_name);
        b.set_self_rel(entries_at + 12, fields);
        b.set_self_rel(root + 8, type_name);
        b.set_self_rel(root + 16, ctab);

        let pt = alloc_adt(0, &[3, 4]);
        assert_eq!(read_format_result(pt, b.ptr_at(root) as i64), "(Point 3 4)");
        unsafe { crate::alloc::dealloc(pt as *mut u8) };
    }

    // ── Self-relative offset round-trip ───────────────────────────────────────

    #[test]
    fn self_rel_offset_round_trip() {
        // Two descriptors; parent's child0_off self-rel-points to child.
        let mut b = BlobBuilder::new();
        let parent = b.reserve_desc();
        let child = b.reserve_desc();
        b.set_desc_kind(parent, DescriptorKind::Vec);
        b.set_desc_kind(child, DescriptorKind::Int);
        b.set_self_rel(parent + 12, child); // child0_off

        let parent_ptr = b.ptr_at(parent);
        let child0_field = unsafe { ptr::addr_of!((*parent_ptr).child0_off) };
        let resolved: Option<*const DisplayDescriptor> =
            unsafe { follow_self_rel(child0_field) };
        let resolved = resolved.expect("child0 offset must resolve");
        // Resolved pointer must equal the child descriptor's address, and have
        // kind Int.
        assert_eq!(resolved as usize, b.ptr_at(child) as usize);
        assert_eq!(unsafe { (*resolved).kind }, DescriptorKind::Int as i32);
    }

    #[test]
    fn self_rel_zero_is_absent() {
        let mut b = BlobBuilder::new();
        let d = b.reserve_desc();
        b.set_desc_kind(d, DescriptorKind::Vec);
        // child0_off left 0.
        let dptr = b.ptr_at(d);
        let field = unsafe { ptr::addr_of!((*dptr).child0_off) };
        let resolved: Option<*const DisplayDescriptor> =
            unsafe { follow_self_rel(field) };
        assert!(resolved.is_none(), "zero offset means absent");
    }

    #[test]
    fn descriptor_repr_is_24_bytes() {
        // Pins the cross-crate ABI record size + alignment (backend reads it).
        assert_eq!(std::mem::size_of::<DisplayDescriptor>(), 24);
        assert_eq!(std::mem::align_of::<DisplayDescriptor>(), 4);
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
}
