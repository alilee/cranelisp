//! Runtime execution tracing for the `(trace ...)` special form.
//!
//! When a `trace` expression is evaluated the runtime:
//! 1. Swaps the per-module GOT entries to thin wrapper functions.
//! 2. Maintains a `TRACE_STACK` that mirrors the call stack.
//! 3. After the body finishes, marshals the stack into a `Trace` ADT heap tree.
//!
//! Thread safety: `TRACE_THREAD_ID` ensures only one thread owns the trace role at
//! a time. A different thread or a nested `trace` expression returns a sentinel /
//! skips tracing.
//!
//! Heap layout uses the base-pointer convention (Decision 10):
//! `[alloc_size(+0) | rc=1(+8) | tag(+16) | field0(+24) | field1(+32) | ...]`

use std::alloc::{self as alloc_mod, Layout};
use std::ptr;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Instant;

use crate::alloc::alloc_with_rc;
use crate::string::alloc_string;

/// Lock the trace stack, recovering from mutex poisoning.
/// Poisoning can occur if a JIT-compiled function panics while the lock is held.
/// Recovery is safe because the trace stack is append-only during tracing and
/// a poisoned state just means a frame was partially built.
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

/// Sentinel returned when the swap is skipped (another trace is active on a different
/// thread, or this is a nested `trace` expression).
const SENTINEL_SAVED_GOT: i64 = 1;

/// Counter used to assign unique IDs to threads.
/// Starts at 1 so that 0 means "no owner".
static THREAD_ID_COUNTER: AtomicU64 = AtomicU64::new(1);

thread_local! {
    /// Stable, unique ID for the current thread. Assigned once on first access.
    /// CRITICAL: Must use a counter, NOT stack address (stack addresses differ
    /// across call depths on the same thread, causing CAS failures).
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
    // SAFETY: `base` was just allocated by `alloc_with_rc` with enough space for
    // the payload header (16 bytes) plus `n_slots * 8` bytes of fields.
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
    // SAFETY: `base` was just allocated by `alloc_with_rc` with 24 bytes of payload,
    // sufficient for tag + 2 fields at offsets 16, 24, and 32.
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

/// Save the GOT, install wrapper pointers, and (on first call) push a synthetic root
/// trace frame.
///
/// Parameters:
/// - `got_base`:     pointer to the module's `got_table[0]`
/// - `n_slots`:      number of functions being wrapped
/// - `slots_ptr`:    `*const u32` -- GOT slot indices for each wrapped function
/// - `wrappers_ptr`: `*const i64` -- wrapper code pointers
///
/// Returns the saved-GOT heap pointer (pass to `cranelisp_trace_restore_got`),
/// or `SENTINEL_SAVED_GOT` if the trace role is already taken.
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
    }
    // else: current_owner == my_tid.
    // Same thread calling swap_got again (multi-module tracing). Do NOT push
    // a new root frame; just swap this GOT table.

    let layout = got_layout();

    // 1. Allocate saved_got and copy the current GOT into it.
    // SAFETY: `got_layout()` returns a valid layout for GOT_BYTES with 8-byte alignment.
    let saved_got = unsafe { alloc_mod::alloc(layout) };
    // SAFETY: `got_base` points to the module's GOT table (GOT_BYTES bytes, 8-byte aligned).
    // `saved_got` was just allocated with the same layout.
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
    // SAFETY: `slots_ptr` points to a caller-allocated array of `n_slots` u32 values
    // (GOT slot indices). `wrappers_ptr` points to a caller-allocated array of `n_slots`
    // i64 values (wrapper code pointers). Both arrays are leaked Box allocations that
    // remain valid for the program lifetime.
    let slots =
        unsafe { std::slice::from_raw_parts(slots_ptr as *const u32, n_slots as usize) };
    let wrappers =
        unsafe { std::slice::from_raw_parts(wrappers_ptr as *const i64, n_slots as usize) };
    for (&slot, &wrapper) in slots.iter().zip(wrappers.iter()) {
        // SAFETY: `slot` is a valid GOT index (< GOT_TABLE_SIZE), so the offset
        // is within the `debug_got` allocation.
        unsafe {
            let entry_ptr = (debug_got as *mut i64).add(slot as usize);
            *entry_ptr = wrapper;
        }
    }

    // 3. Install: copy debug_got over the real GOT in one memcpy.
    // SAFETY: `debug_got` and `got_base` are both GOT_BYTES-sized, non-overlapping buffers.
    // `debug_got` is deallocated with the same layout it was allocated with.
    unsafe {
        ptr::copy_nonoverlapping(debug_got, got_base as *mut u8, GOT_BYTES);
        alloc_mod::dealloc(debug_got, layout);
    }

    saved_got as i64
}

/// Restore the GOT from the saved copy, then free it.
/// If `saved_got` is `SENTINEL_SAVED_GOT` this is a no-op.
/// Does NOT release `TRACE_THREAD_ID` -- that is done by `cranelisp_collect_trace`.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_restore_got(got_base: i64, saved_got: i64) {
    if saved_got == SENTINEL_SAVED_GOT {
        return;
    }
    let layout = got_layout();
    // SAFETY: `saved_got` was allocated by `cranelisp_trace_swap_got` with `got_layout()`.
    // `got_base` points to the module's GOT table (same size). Both are valid and
    // non-overlapping. The saved copy is deallocated with the same layout.
    unsafe {
        ptr::copy_nonoverlapping(saved_got as *const u8, got_base as *mut u8, GOT_BYTES);
        alloc_mod::dealloc(saved_got as *mut u8, layout);
    }
}

/// Called by wrapper functions at the entry of each traced call.
/// No-op if the calling thread is not the trace thread.
///
/// Parameters:
/// - `name_ptr`/`name_len`: raw UTF-8 function name (not a cranelisp heap String)
/// - `params_count`: number of parameter String heap ptrs in the array
/// - `params_array_ptr`: `*const i64` -- array of cranelisp String heap ptrs (RC=1 each)
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
    // SAFETY: `name_ptr` and `name_len` come from a leaked `Box<[u8]>` in the
    // wrapper function (valid for program lifetime). The slice covers exactly
    // `name_len` bytes of valid UTF-8 function name data.
    let name = unsafe {
        let bytes = std::slice::from_raw_parts(name_ptr as *const u8, name_len as usize);
        String::from_utf8_lossy(bytes).into_owned()
    };
    // Read the pre-formatted param String heap ptrs from the stack array.
    let params: Vec<i64> = if params_count > 0 && params_array_ptr != 0 {
        // SAFETY: `params_array_ptr` points to a Cranelift stack slot containing
        // `params_count` i64 values (heap String pointers). The slot is valid for
        // the duration of the wrapper function call.
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
    // SAFETY for all read_i64 calls below: `trace_adt` was verified above to be
    // a heap pointer (above NULLARY_TAG_THRESHOLD). It was allocated by
    // `build_trace_call` with the 5-field TraceCall layout, so offsets 48 and 56
    // are within bounds. Intermediate pointers (tchildren, first_child) are
    // checked against NULLARY_THRESHOLD before dereferencing.

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
    crate::drop::consume_trace_call(trace_adt);
    result
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
// These implement the Trace ADT field accessors registered as extern primitives
// in the typechecker. Each reads a field at the appropriate offset from a
// TraceCall heap pointer.
//
// TraceCall layout (base-pointer convention):
// [alloc_size(+0) | rc(+8) | tag=0(+16) | tname(+24) | tparams(+32) | tresult(+40) | tchildren(+48) | tnanos(+56)]

const TRACE_TNAME_OFFSET: usize = FIELD0_OFFSET;          // 24
const TRACE_TPARAMS_OFFSET: usize = FIELD0_OFFSET + 8;    // 32
const TRACE_TRESULT_OFFSET: usize = FIELD0_OFFSET + 16;   // 40
const TRACE_TCHILDREN_OFFSET: usize = FIELD0_OFFSET + 24;  // 48
const TRACE_TNANOS_OFFSET: usize = FIELD0_OFFSET + 32;     // 56

/// RC-inc a heap value (atomic, matching the compiler's `emit_rc_inc`).
/// No-op for nullary tags (bare integers below NULLARY_TAG_THRESHOLD).
fn rc_inc_if_heap(val: i64) {
    use std::sync::atomic::{AtomicI64, Ordering};
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
    crate::drop::consume_trace_call(trace_ptr);
    val
}

/// Return the `tparams` field (SList of String heap ptrs) of a TraceCall ADT.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — see `cranelisp_trace_name`.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_params(trace_ptr: i64) -> i64 {
    let val = unsafe { read_i64(trace_ptr, TRACE_TPARAMS_OFFSET) };
    rc_inc_if_heap(val);
    crate::drop::consume_trace_call(trace_ptr);
    val
}

/// Return the `tresult` field (String heap ptr) of a TraceCall ADT.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — see `cranelisp_trace_name`.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_result(trace_ptr: i64) -> i64 {
    let val = unsafe { read_i64(trace_ptr, TRACE_TRESULT_OFFSET) };
    rc_inc_if_heap(val);
    crate::drop::consume_trace_call(trace_ptr);
    val
}

/// Return the `tchildren` field (SList of TraceCall heap ptrs) of a TraceCall ADT.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — see `cranelisp_trace_name`.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_children(trace_ptr: i64) -> i64 {
    let val = unsafe { read_i64(trace_ptr, TRACE_TCHILDREN_OFFSET) };
    rc_inc_if_heap(val);
    crate::drop::consume_trace_call(trace_ptr);
    val
}

/// Return the `tnanos` field (i64 nanoseconds) of a TraceCall ADT.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — Int payload is
/// not heap-typed, but the Trace ADT containing it is. Consume the Trace.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_nanos(trace_ptr: i64) -> i64 {
    // SAFETY: same as cranelisp_trace_name — offset 56 is within payload bounds.
    let val = unsafe { read_i64(trace_ptr, TRACE_TNANOS_OFFSET) };
    crate::drop::consume_trace_call(trace_ptr);
    val
}

/// Format a runtime value as a cranelisp heap String using the display module.
///
/// This function is registered as a JIT symbol but the actual formatting logic
/// lives in `cranelisp-backend::display::format_value` which requires a TypeChecker
/// reference. The integration layer (`src/`) sets `TRACE_FORMAT_FN` before evaluation.
///
/// Parameters:
/// - `val`: the runtime value to format
/// - `type_ptr`: pointer to a leaked `Box<Type>` describing the value's type
///
/// Returns a heap String pointer (RC=1), or a fallback "?" string if the
/// format function has not been set.
///
/// NOTE: This is a placeholder. The actual `cranelisp_trace_format` function
/// must be registered by the integration layer (`src/`) because it needs access
/// to the TypeChecker (which lives in cranelisp-typecheck, not accessible from
/// the runtime crate). The integration layer registers its own implementation
/// as a JIT symbol that overrides this one.
///
/// For now, this provides a minimal fallback that formats scalars inline.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_format(val: i64, _type_ptr: i64) -> i64 {
    // Minimal fallback: format the raw i64 value as a string.
    // The real implementation is provided by src/ (integration layer) which
    // has access to the TypeChecker for proper format_result_value dispatch.
    let s = format!("{val}");
    alloc_string(s.as_bytes()) as i64
}

#[cfg(test)]
mod tests {
    use super::*;

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
        // Read back the tag
        let tag = unsafe { read_i64(adt, PAYLOAD_OFFSET) };
        assert_eq!(tag, TAG_TRACE_CALL);
        // Read back fields
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
        // Should be SCons(10, SCons(20, SCons(30, SNil)))
        assert!(list >= NULLARY_THRESHOLD, "list head should be heap pointer");
        let tag = unsafe { read_i64(list, PAYLOAD_OFFSET) };
        assert_eq!(tag, TAG_SCONS);
        let head = unsafe { read_i64(list, FIELD0_OFFSET) };
        assert_eq!(head, 10);
    }

    #[test]
    fn test_trace_collect_empty_stack() {
        // Ensure the trace stack is empty and we are not the owner.
        let result = cranelisp_collect_trace();
        // Should return a valid TraceCall ADT
        assert!(result != 0);
        let tag = unsafe { read_i64(result, PAYLOAD_OFFSET) };
        assert_eq!(tag, TAG_TRACE_CALL);
    }

    #[test]
    fn test_trace_enter_exit_basic() {
        // Simulate a simple trace enter/exit sequence.
        // First claim the trace role.
        let my_tid = current_thread_id();
        TRACE_THREAD_ID.store(my_tid, Ordering::SeqCst);
        TRACE_STACK.lock().unwrap().push(TraceFrame {
            name: "::trace::".to_string(),
            params: vec![],
            result: 0,
            start: Instant::now(),
            children: vec![],
        });

        let name = "test-fn";
        cranelisp_trace_enter(
            name.as_ptr() as i64,
            name.len() as i64,
            0,
            0,
        );

        let result = cranelisp_trace_exit(42, 0);
        assert_eq!(result, 42, "trace_exit must return the original result");

        // Collect should return a TraceCall with one child.
        let trace = cranelisp_collect_trace();
        assert!(trace != 0);
        let tag = unsafe { read_i64(trace, PAYLOAD_OFFSET) };
        assert_eq!(tag, TAG_TRACE_CALL);
    }

    // ---------------------------------------------------------------------
    // Decision 24 extern-consumption tests (Sprint 56 Step 2c)
    //
    // Each accessor inc's the returned heap field (so the caller gets an
    // independent reference) and then consumes the TraceCall via
    // `consume_trace_call`. If the Trace's rc reaches 0, drop glue walks
    // the remaining heap sub-refs (tname/tparams/tresult/tchildren).
    // ---------------------------------------------------------------------

    /// Build a minimal TraceCall heap value with bare-tag params and children
    /// (so we isolate name + result as the only heap sub-refs besides the
    /// TraceCall node itself). Returns the TraceCall base pointer.
    fn make_minimal_trace_call(name_bytes: &[u8], result_bytes: &[u8]) -> (i64, i64, i64) {
        let name = alloc_string(name_bytes) as i64; // rc=1
        let result = alloc_string(result_bytes) as i64; // rc=1
        let trace = alloc_adt(
            TAG_TRACE_CALL,
            &[
                name,
                TAG_SNIL,   // tparams: bare SNil, no heap
                result,
                TAG_SNIL,   // tchildren: bare SNil, no heap
                0i64,       // tnanos: scalar
            ],
        );
        (trace, name, result)
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consuming convention, extern cranelisp_trace_name
    #[test]
    fn decision24_trace_name_rc_balanced() {
        let allocs_before = crate::alloc::alloc_count();
        let deallocs_before = crate::alloc::dealloc_count();

        let (trace, _name, _result) = make_minimal_trace_call(b"my-fn", b"42");
        // Accessor: inc's name (rc 1→2), consumes Trace (rc 1→0 last ref →
        // walks sub-refs: dec tname (2→1), consume SNil params no-op,
        // consume result (rc 1→0, freed), consume SNil children no-op,
        // dealloc Trace).
        let returned_name = cranelisp_trace_name(trace);
        // Caller now owns name at rc=1. Release it.
        crate::rc::consume_shallow(returned_name);

        // allocs: name + result + trace = 3
        // deallocs: name + result + trace = 3
        assert_eq!(crate::alloc::alloc_count() - allocs_before, 3, "alloc count mismatch");
        assert_eq!(
            crate::alloc::dealloc_count() - deallocs_before,
            3,
            "dealloc count mismatch (leak or double-free)"
        );
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consuming convention, extern cranelisp_trace_result
    #[test]
    fn decision24_trace_result_rc_balanced() {
        let allocs_before = crate::alloc::alloc_count();
        let deallocs_before = crate::alloc::dealloc_count();

        let (trace, _name, _result) = make_minimal_trace_call(b"g", b"7");
        // Accessor: inc's result, consumes Trace — on last ref, dec'd name
        // (1→0 freed), SNil params no-op, result (2→1 via dec), SNil
        // children no-op, dealloc Trace.
        let returned = cranelisp_trace_result(trace);
        crate::rc::consume_shallow(returned);

        assert_eq!(crate::alloc::alloc_count() - allocs_before, 3);
        assert_eq!(crate::alloc::dealloc_count() - deallocs_before, 3);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consuming convention, extern cranelisp_trace_nanos
    // (Int return — no inc on return value; Trace is still consumed.)
    #[test]
    fn decision24_trace_nanos_rc_balanced() {
        let allocs_before = crate::alloc::alloc_count();
        let deallocs_before = crate::alloc::dealloc_count();

        let (trace, _name, _result) = make_minimal_trace_call(b"h", b"ok");
        let nanos = cranelisp_trace_nanos(trace);
        assert_eq!(nanos, 0, "tnanos field was set to 0 in the fixture");

        // allocs: name + result + trace = 3
        // deallocs: name + result + trace = 3 (all freed by consume_trace_call)
        assert_eq!(crate::alloc::alloc_count() - allocs_before, 3);
        assert_eq!(crate::alloc::dealloc_count() - deallocs_before, 3);
    }
}
