//! Runtime execution tracing for the `(trace ...)` special form.
//!
//! When a `trace` expression is evaluated the runtime:
//! 1. Swaps the per-module GOT entries to thin wrapper functions.
//! 2. Maintains a `TRACE_STACK` that mirrors the call stack.
//! 3. After the body finishes, marshals the stack into a `Trace` ADT heap tree.
//!
//! Thread safety: `TRACE_THREAD_ID` ensures only one thread owns the trace role at
//! a time. The same thread may call `cranelisp_trace_swap_got` multiple times (once
//! per GOT table when tracing across multiple modules). A different thread or a nested
//! `trace` expression returns a sentinel / skips tracing.
//!
//! Phase 2: `cranelisp_trace_enter` accepts pre-formatted parameter String heap ptrs
//! and `cranelisp_trace_exit` accepts a pre-formatted result String heap ptr.
//! The Trace ADT now has 5 fields: tname, tparams, tresult, tchildren, tnanos.
//! Heap indices: tag=0, tname=1, tparams=2, tresult=3, tchildren=4, tnanos=5.

use std::alloc::{Layout, alloc, dealloc};
use std::ptr;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Instant;

use crate::marshal::{TAG_SNIL, TAG_TRACE_CALL, alloc_adt, build_runtime_list};
use crate::primitives::alloc_string;

// Must match `GOT_TABLE_SIZE` in `src/module.rs`.
const GOT_TABLE_SIZE: usize = 1024;
const GOT_BYTES: usize = GOT_TABLE_SIZE * 8;

// ── Thread ownership ─────────────────────────────────────────────────────────

/// ID of the thread currently owning the trace role. 0 = no active trace.
static TRACE_THREAD_ID: AtomicU64 = AtomicU64::new(0);

/// Sentinel returned when the swap is skipped (another trace is active on a different
/// thread, or this is a nested `trace` expression).
const SENTINEL_SAVED_GOT: i64 = 1;

/// Counter used to assign unique IDs to threads.
static THREAD_ID_COUNTER: AtomicU64 = AtomicU64::new(1);

thread_local! {
    /// Stable, unique ID for the current thread. Assigned once on first access.
    static THIS_THREAD_ID: u64 = THREAD_ID_COUNTER.fetch_add(1, Ordering::Relaxed);
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

// ── ADT allocation helper ─────────────────────────────────────────────────────

/// Build a 5-field TraceCall ADT from a completed TraceFrame.
/// Layout: [tag=0, name, params_slist, result_str, children_slist, nanos]
fn build_trace_call(frame: TraceFrame, nanos: i64) -> i64 {
    let name_heap = alloc_string(frame.name.as_bytes());
    let params_slist = build_runtime_list(&frame.params);
    let result_str = if frame.result != 0 {
        frame.result
    } else {
        alloc_string(b"")
    };
    let children_slist = build_runtime_list(&frame.children);
    alloc_adt(TAG_TRACE_CALL, &[name_heap, params_slist, result_str, children_slist, nanos])
}

// ── Public extern API ─────────────────────────────────────────────────────────

/// Save the GOT, install wrapper pointers, and (on first call) push a synthetic root
/// trace frame.
///
/// Parameters:
/// - `got_base`:     pointer to the module's `got_table[0]`
/// - `n_slots`:      number of functions being wrapped
/// - `slots_ptr`:    `*const u32` — GOT slot indices for each wrapped function
/// - `wrappers_ptr`: `*const i64` — wrapper code pointers
///
/// Returns the saved-GOT heap pointer (pass to `cranelisp_trace_restore_got`),
/// or `SENTINEL_SAVED_GOT` if a different thread owns the trace role (concurrent trace)
/// or this is a nested `trace` from a different expression on the same thread.
///
/// When called multiple times by the same thread (multi-module tracing), the root
/// frame is only pushed once; subsequent calls just swap the additional GOT tables.
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
        // Try to claim the trace role (CAS 0 → my_tid).
        if TRACE_THREAD_ID
            .compare_exchange(0, my_tid, Ordering::SeqCst, Ordering::Relaxed)
            .is_err()
        {
            // Race: another thread just claimed it → push sentinel frame, skip.
            TRACE_STACK.lock().unwrap().push(TraceFrame {
                name: "::skipped::".to_string(),
                params: vec![],
                result: 0,
                start: Instant::now(),
                children: vec![],
            });
            return SENTINEL_SAVED_GOT;
        }
        // Successfully claimed. Push the synthetic root frame.
        TRACE_STACK.lock().unwrap().push(TraceFrame {
            name: "::trace::".to_string(),
            params: vec![],
            result: 0,
            start: Instant::now(),
            children: vec![],
        });
    } else if current_owner != my_tid {
        // A different thread owns the trace role → skip (concurrent trace).
        TRACE_STACK.lock().unwrap().push(TraceFrame {
            name: "::skipped::".to_string(),
            params: vec![],
            result: 0,
            start: Instant::now(),
            children: vec![],
        });
        return SENTINEL_SAVED_GOT;
    }
    // else: current_owner == my_tid.
    // Same thread calling swap_got again (multi-module tracing within the same trace
    // expression). Do NOT push a new root frame; just swap this GOT table.

    let layout = got_layout();

    // 1. Allocate saved_got and copy the current GOT into it.
    let saved_got = unsafe { alloc(layout) };
    unsafe {
        ptr::copy_nonoverlapping(got_base as *const u8, saved_got, GOT_BYTES);
    }

    // 2. Build debug_got: clone saved_got then substitute wrapper ptrs.
    let debug_got = unsafe { alloc(layout) };
    unsafe {
        ptr::copy_nonoverlapping(saved_got, debug_got, GOT_BYTES);
    }
    let slots =
        unsafe { std::slice::from_raw_parts(slots_ptr as *const u32, n_slots as usize) };
    let wrappers =
        unsafe { std::slice::from_raw_parts(wrappers_ptr as *const i64, n_slots as usize) };
    for (&slot, &wrapper) in slots.iter().zip(wrappers.iter()) {
        unsafe {
            let entry_ptr = (debug_got as *mut i64).add(slot as usize);
            *entry_ptr = wrapper;
        }
    }

    // 3. Install: copy debug_got over the real GOT in one memcpy.
    unsafe {
        ptr::copy_nonoverlapping(debug_got, got_base as *mut u8, GOT_BYTES);
        dealloc(debug_got, layout);
    }

    saved_got as i64
}

/// Restore the GOT from the saved copy, then free it.
/// If `saved_got` is `SENTINEL_SAVED_GOT` this is a no-op.
/// Does NOT release `TRACE_THREAD_ID` — that is done by `cranelisp_collect_trace`.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_restore_got(got_base: i64, saved_got: i64) {
    if saved_got == SENTINEL_SAVED_GOT {
        return;
    }
    let layout = got_layout();
    unsafe {
        ptr::copy_nonoverlapping(saved_got as *const u8, got_base as *mut u8, GOT_BYTES);
        dealloc(saved_got as *mut u8, layout);
    }
}

/// Called by wrapper functions at the entry of each traced call.
/// No-op if the calling thread is not the trace thread.
///
/// Parameters:
/// - `name_ptr`/`name_len`: raw UTF-8 function name (not a cranelisp heap String)
/// - `params_count`: number of parameter String heap ptrs in the array
/// - `params_array_ptr`: `*const i64` — array of cranelisp String heap ptrs (RC=1 each)
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
    let name = unsafe {
        let bytes = std::slice::from_raw_parts(name_ptr as *const u8, name_len as usize);
        String::from_utf8_lossy(bytes).into_owned()
    };
    // Read the pre-formatted param String heap ptrs from the stack array.
    let params: Vec<i64> = if params_count > 0 && params_array_ptr != 0 {
        unsafe {
            std::slice::from_raw_parts(params_array_ptr as *const i64, params_count as usize)
                .to_vec()
        }
    } else {
        vec![]
    };
    TRACE_STACK.lock().unwrap().push(TraceFrame {
        name,
        params,
        result: 0,
        start: Instant::now(),
        children: vec![],
    });
}

/// Called by wrapper functions at the exit of each traced call.
/// Pops the current frame, builds a TraceCall ADT, and pushes it into the parent frame.
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
    let mut stack = TRACE_STACK.lock().unwrap();
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
/// Used by `run-tests` to report per-test execution time.
/// Returns 0 if the trace has no children (e.g. batch-mode empty trace).
///
/// Heap layout: TraceCall has fields [tag, tname, tparams, tresult, tchildren, tnanos].
/// SList SCons: [tag=1, head, tail]; SNil = bare 0.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_first_child_nanos(trace_adt: i64) -> i64 {
    if trace_adt == 0 {
        return 0;
    }
    let root = trace_adt as *const i64;
    // tchildren is field index 3 → offset 4 (after tag at 0, tname at 1, tparams at 2, tresult at 3)
    let tchildren = unsafe { *root.add(4) };
    if tchildren == 0 {
        return 0; // SNil
    }
    let scons = tchildren as *const i64;
    let scons_tag = unsafe { *scons };
    if scons_tag != 1 {
        return 0; // not SCons
    }
    // head is field 0 of SCons → offset 1
    let first_child = unsafe { *scons.add(1) } as *const i64;
    // tnanos is field index 4 → offset 5
    unsafe { *first_child.add(5) }
}

/// Collect the root trace frame, release the trace role, and return the trace as a
/// `Trace` ADT heap pointer.
/// Must be called after all `cranelisp_trace_restore_got` calls for this trace expression.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_collect_trace() -> i64 {
    // Release the trace role (only if we own it).
    let my_tid = current_thread_id();
    TRACE_THREAD_ID
        .compare_exchange(my_tid, 0, Ordering::SeqCst, Ordering::Relaxed)
        .ok();

    let mut stack = TRACE_STACK.lock().unwrap();
    if let Some(frame) = stack.pop() {
        let nanos = frame.start.elapsed().as_nanos() as i64;
        build_trace_call(frame, nanos)
    } else {
        // Empty stack — return a minimal TraceCall with empty params/result
        let name_heap = alloc_string(b"::trace::");
        let empty_slist = TAG_SNIL;
        let empty_str = alloc_string(b"");
        alloc_adt(TAG_TRACE_CALL, &[name_heap, empty_slist, empty_str, empty_slist, 0i64])
    }
}
