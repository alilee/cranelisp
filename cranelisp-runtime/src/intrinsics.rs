//! Language-internal builtin functions exposed to JIT-compiled code via `extern "C"`.
//! These are implementation details invisible to user code — no IO types.
//!
//! ## Heap layout
//! ```text
//! [size: i64 | rc: i64 | payload...]
//!                        ^-- returned pointer (base + 16)
//! ```
//! `size` at `ptr - 16` stores the total allocation size (for dealloc layout).
//! `rc` at `ptr - 8` stores the reference count.

use std::alloc::Layout;
use std::collections::HashSet;
use std::sync::atomic::{AtomicBool, AtomicI64, AtomicUsize, Ordering};
use std::sync::Mutex;

/// RC trace logging. Enabled by CRANELISP_RC_TRACE=1 env var in debug builds.
/// Logs every alloc, free, inc, and dec to stderr with pointer address and RC value.
#[cfg(debug_assertions)]
static RC_TRACE_ENABLED: std::sync::LazyLock<AtomicBool> = std::sync::LazyLock::new(|| {
    AtomicBool::new(std::env::var("CRANELISP_RC_TRACE").map_or(false, |v| v == "1"))
});

#[cfg(debug_assertions)]
fn rc_trace(op: &str, ptr: i64, rc: i64) {
    if RC_TRACE_ENABLED.load(Ordering::Relaxed) {
        eprintln!("[rc] {} ptr={:#x} rc={}", op, ptr as u64, rc);
    }
}

#[cfg(not(debug_assertions))]
fn rc_trace(_op: &str, _ptr: i64, _rc: i64) {}

/// Monotonic allocation counter (incremented on every alloc).
static ALLOC_COUNT: AtomicUsize = AtomicUsize::new(0);
/// Monotonic deallocation counter (incremented on every free).
static DEALLOC_COUNT: AtomicUsize = AtomicUsize::new(0);
/// Monotonic total bytes allocated (payload bytes, excluding headers).
static BYTES_ALLOCATED: AtomicUsize = AtomicUsize::new(0);
/// Net bytes currently live (payload bytes, excluding headers).
static BYTES_CURRENT: AtomicUsize = AtomicUsize::new(0);
/// High-water mark of BYTES_CURRENT.
static BYTES_PEAK: AtomicUsize = AtomicUsize::new(0);

/// Set of currently live allocation pointers (payload pointers, not base).
/// Used for double-free detection at runtime.
static LIVE_ALLOCS: std::sync::LazyLock<Mutex<HashSet<usize>>> =
    std::sync::LazyLock::new(|| Mutex::new(HashSet::new()));

pub fn alloc_count() -> usize {
    ALLOC_COUNT.load(Ordering::Relaxed)
}
pub fn dealloc_count() -> usize {
    DEALLOC_COUNT.load(Ordering::Relaxed)
}
pub fn bytes_allocated() -> usize {
    BYTES_ALLOCATED.load(Ordering::Relaxed)
}
pub fn bytes_current() -> usize {
    BYTES_CURRENT.load(Ordering::Relaxed)
}
pub fn bytes_peak() -> usize {
    BYTES_PEAK.load(Ordering::Relaxed)
}
pub fn is_live(ptr: usize) -> bool {
    LIVE_ALLOCS.lock().unwrap().contains(&ptr)
}

pub fn reset_counts() {
    ALLOC_COUNT.store(0, Ordering::Relaxed);
    DEALLOC_COUNT.store(0, Ordering::Relaxed);
    BYTES_ALLOCATED.store(0, Ordering::Relaxed);
    BYTES_CURRENT.store(0, Ordering::Relaxed);
    BYTES_PEAK.store(0, Ordering::Relaxed);
    LIVE_ALLOCS.lock().unwrap().clear();
}

/// Allocate `size` bytes with a 16-byte header prepended (size + rc).
/// Returns pointer to payload (past the header). RC initialized to 1.
/// Used by both `alloc` (JIT entry point) and Rust primitives that allocate heap objects.
pub fn alloc_with_rc(size: usize) -> *mut u8 {
    let total = size + 16;
    let layout = Layout::from_size_align(total, 8).expect("invalid alloc layout");
    ALLOC_COUNT.fetch_add(1, Ordering::Relaxed);
    BYTES_ALLOCATED.fetch_add(size, Ordering::Relaxed);
    let current = BYTES_CURRENT.fetch_add(size, Ordering::Relaxed) + size;
    BYTES_PEAK.fetch_max(current, Ordering::Relaxed);
    unsafe {
        let base = std::alloc::alloc(layout);
        *(base as *mut i64) = total as i64; // size field
        *((base as *mut i64).add(1)) = 1; // rc = 1
        let payload = base.add(16);
        LIVE_ALLOCS.lock().unwrap().insert(payload as usize);
        rc_trace("alloc", payload as i64, 1);
        payload // return pointer past header
    }
}

/// Allocate `size` bytes of memory with an rc=1 header. Returns pointer to payload as i64.
/// The rc header lives at `ptr - 8`, invisible to callers.
#[unsafe(export_name = "cranelisp_alloc")]
pub extern "C" fn alloc(size: i64) -> i64 {
    alloc_with_rc(size as usize) as i64
}

/// Free a heap object whose refcount has reached zero.
/// Reads total_size from `ptr - 16`, computes layout, and deallocates.
#[unsafe(export_name = "cranelisp_free")]
pub extern "C" fn free(ptr: i64) -> i64 {
    if !LIVE_ALLOCS.lock().unwrap().remove(&(ptr as usize)) {
        panic!("double free detected at 0x{:x}", ptr);
    }
    rc_trace("free", ptr, 0);
    DEALLOC_COUNT.fetch_add(1, Ordering::Relaxed);
    unsafe {
        let payload = ptr as *mut u8;
        let base = payload.sub(16);
        let total_size = *(base as *const i64) as usize;
        let payload_size = total_size - 16;
        BYTES_CURRENT.fetch_sub(payload_size, Ordering::Relaxed);
        let layout = Layout::from_size_align(total_size, 8).expect("invalid free layout");
        std::alloc::dealloc(base, layout);
    }
    0
}

/// Guarded decrement: if `val == guard`, skip (prevents freeing a return value).
/// Otherwise, atomically dec rc. If rc reaches 0, call `drop_fn(val)` if non-null,
/// else call `cranelisp_free(val)`.
///
/// This is the out-of-line version of emit_dec_guarded — reduces IR block count
/// by replacing 4-6 inline blocks per call site with a single function call.
#[unsafe(export_name = "cranelisp_dec_guarded")]
pub extern "C" fn dec_guarded(val: i64, guard: i64, drop_fn_ptr: i64) -> i64 {
    if val == guard || (val as u64) < 1024 {
        return 0;
    }
    unsafe {
        let rc_addr = (val as *mut i64).sub(1);
        let old_rc = (rc_addr as *const std::sync::atomic::AtomicI64)
            .as_ref()
            .unwrap()
            .fetch_sub(1, Ordering::Release);
        debug_assert!(
            old_rc > 0,
            "RC underflow: dec_guarded on val={:#x} with old_rc={} (already freed?)",
            val as u64,
            old_rc
        );
        rc_trace("dec_guarded", val, old_rc - 1);
        if old_rc == 1 {
            // RC reached 0 — free the object
            std::sync::atomic::fence(Ordering::Acquire);
            if drop_fn_ptr != 0 {
                let drop_fn: extern "C" fn(i64) -> i64 =
                    std::mem::transmute(drop_fn_ptr as *const ());
                drop_fn(val);
            } else {
                free(val);
            }
        }
    }
    0
}

/// Guarded decrement for closures: if `val == guard`, skip.
/// Otherwise, atomically dec rc. If rc reaches 0, load drop_ptr from closure[1],
/// call it if non-null, else call `cranelisp_free(val)`.
#[unsafe(export_name = "cranelisp_dec_closure_guarded")]
pub extern "C" fn dec_closure_guarded(val: i64, guard: i64) -> i64 {
    if val == guard || (val as u64) < 1024 {
        return 0;
    }
    unsafe {
        let rc_addr = (val as *mut i64).sub(1);
        let old_rc = (rc_addr as *const std::sync::atomic::AtomicI64)
            .as_ref()
            .unwrap()
            .fetch_sub(1, Ordering::Release);
        debug_assert!(
            old_rc > 0,
            "RC underflow: dec_closure_guarded on val={:#x} with old_rc={}",
            val as u64,
            old_rc
        );
        rc_trace("dec_closure_guarded", val, old_rc - 1);
        if old_rc == 1 {
            std::sync::atomic::fence(Ordering::Acquire);
            let drop_ptr = *((val as *const i64).add(1));
            if drop_ptr != 0 {
                let drop_fn: extern "C" fn(i64) -> i64 =
                    std::mem::transmute(drop_ptr as *const ());
                drop_fn(val);
            } else {
                free(val);
            }
        }
    }
    0
}

/// Guarded decrement for mixed (nullary/data) ADTs: if `val == guard` or `val < 1024`
/// (nullary tag), skip. Otherwise, atomically dec rc and free if rc reaches 0.
#[unsafe(export_name = "cranelisp_dec_mixed_guarded")]
pub extern "C" fn dec_mixed_guarded(val: i64, guard: i64, drop_fn_ptr: i64) -> i64 {
    if val == guard || (val as u64) < 1024 {
        return 0;
    }
    unsafe {
        let rc_addr = (val as *mut i64).sub(1);
        let old_rc = (rc_addr as *const std::sync::atomic::AtomicI64)
            .as_ref()
            .unwrap()
            .fetch_sub(1, Ordering::Release);
        debug_assert!(
            old_rc > 0,
            "RC underflow: dec_mixed_guarded on val={:#x} with old_rc={}",
            val as u64,
            old_rc
        );
        rc_trace("dec_mixed_guarded", val, old_rc - 1);
        if old_rc == 1 {
            std::sync::atomic::fence(Ordering::Acquire);
            if drop_fn_ptr != 0 {
                let drop_fn: extern "C" fn(i64) -> i64 =
                    std::mem::transmute(drop_fn_ptr as *const ());
                drop_fn(val);
            } else {
                free(val);
            }
        }
    }
    0
}

/// Force an IO task tree to completion via trampoline.
/// Called by the standalone exe startup stub.
///
/// Walks the deferred computation tree (Pure/Effect/Bind), executing effects
/// and applying continuations. Uses an explicit stack for O(1) call depth.
#[unsafe(export_name = "cranelisp_run_io")]
pub extern "C" fn run_io(io_ptr: i64) -> i64 {
    use cranelisp_platform::{IO_TAG_BIND, IO_TAG_EFFECT, IO_TAG_PURE};

    let mut cont_stack: Vec<i64> = Vec::new();
    let mut current = io_ptr;

    loop {
        let tag = unsafe { *(current as *const i64) };
        match tag {
            IO_TAG_PURE => {
                let val = unsafe { *((current as *const i64).add(1)) };
                match cont_stack.pop() {
                    Some(cont) => current = call_continuation(cont, val),
                    None => return val,
                }
            }
            IO_TAG_EFFECT => {
                let thunk_ptr = unsafe { *((current as *const i64).add(1)) };
                let result = unsafe { cranelisp_platform::call_effect_thunk(thunk_ptr) };
                match cont_stack.pop() {
                    Some(cont) => current = call_continuation(cont, result),
                    None => return result,
                }
            }
            IO_TAG_BIND => {
                let inner = unsafe { *((current as *const i64).add(1)) };
                let cont = unsafe { *((current as *const i64).add(2)) };
                cont_stack.push(cont);
                current = inner;
            }
            cranelisp_platform::IO_TAG_PAR => {
                use rayon::prelude::*;

                let count = unsafe { *((current as *const i64).add(1)) } as usize;
                let io_ptrs: Vec<i64> = (0..count)
                    .map(|i| unsafe { *((current as *const i64).add(2 + i)) })
                    .collect();

                // Run each IO branch concurrently (each gets its own trampoline)
                let results: Vec<i64> = io_ptrs
                    .par_iter()
                    .map(|&io_ptr| run_io(io_ptr))
                    .collect();

                // Allocate results array
                let results_ptr = alloc_with_rc(count * 8) as i64;
                for (i, &val) in results.iter().enumerate() {
                    unsafe {
                        *((results_ptr as *mut i64).add(i)) = val;
                    }
                }

                // Pop continuation and call with results array
                match cont_stack.pop() {
                    Some(cont) => current = call_continuation(cont, results_ptr),
                    None => return results_ptr,
                }
            }
            _ => {
                eprintln!("cranelisp_run_io: unknown IO tag {}", tag);
                std::process::exit(1);
            }
        }
    }
}

/// Call a cranelisp closure as an IO continuation.
/// Closure layout: [code_ptr: i64, captures...]
fn call_continuation(cont: i64, val: i64) -> i64 {
    unsafe {
        let code_ptr = *(cont as *const i64);
        let call: extern "C" fn(i64, i64) -> i64 =
            std::mem::transmute(code_ptr as *const ());
        call(cont, val)
    }
}

/// Evaluate N thunks (zero-arg closures) in parallel using rayon.
/// `thunks_ptr` points to a heap array of N closure pointers.
/// Returns a heap array of N result values.
#[unsafe(export_name = "cranelisp_par_eval")]
pub extern "C" fn par_eval(thunks_ptr: i64, count: i64) -> i64 {
    use rayon::prelude::*;

    let n = count as usize;

    // Read thunk closure pointers from the array
    let thunks: Vec<i64> = (0..n)
        .map(|i| unsafe { *((thunks_ptr as *const i64).add(i)) })
        .collect();

    // Execute each thunk in parallel: read code_ptr from closure, call(closure_ptr) -> result
    let results: Vec<i64> = thunks
        .par_iter()
        .map(|&closure_ptr| unsafe {
            let code_ptr = *(closure_ptr as *const i64);
            let call: extern "C" fn(i64) -> i64 =
                std::mem::transmute(code_ptr as *const ());
            call(closure_ptr)
        })
        .collect();

    // Allocate results array and store
    let results_ptr = alloc_with_rc(n * 8) as i64;
    for (i, &val) in results.iter().enumerate() {
        unsafe {
            *((results_ptr as *mut i64).add(i)) = val;
        }
    }
    results_ptr
}

// ── IVar (write-once synchronisation cell) for lenient evaluation ─────────
//
// Heap layout: [total_size: i64 | rc: i64 | state: i64 | value: i64 | thunk: i64]
//                                           ^-- payload pointer (returned by alloc)
//
// state (offset 0): atomic i64 — 0 = PENDING, 1 = EVALUATING, 2 = RESOLVED
// value (offset 8): result i64, valid when state = RESOLVED
// thunk (offset 16): closure pointer (zero-arg thunk)

const IVAR_PENDING: i64 = 0;
const IVAR_EVALUATING: i64 = 1;
const IVAR_RESOLVED: i64 = 2;

/// Allocate an IVar cell with a thunk closure. Sets state=PENDING, stores thunk.
/// Returns pointer to the IVar payload (past RC header).
#[unsafe(export_name = "cranelisp_ivar_create")]
pub extern "C" fn ivar_create(thunk: i64) -> i64 {
    // 24 bytes payload: [state, value, thunk]
    let ptr = alloc_with_rc(24) as i64;
    unsafe {
        *(ptr as *mut i64) = IVAR_PENDING; // state
        *((ptr as *mut i64).add(1)) = 0; // value (unused until resolved)
        *((ptr as *mut i64).add(2)) = thunk; // thunk closure pointer
    }
    ptr
}

/// Submit an IVar for evaluation on the rayon thread pool.
/// Atomically increments the IVar's RC (spark holds a reference), then spawns
/// a task that forces the IVar and decrements RC when done.
#[unsafe(export_name = "cranelisp_ivar_spark")]
pub extern "C" fn ivar_spark(ivar: i64) -> i64 {
    // Inc IVar RC: spark holds a reference
    unsafe {
        let rc_addr = (ivar as *mut i64).sub(1);
        let rc_atomic = &*(rc_addr as *const AtomicI64);
        rc_atomic.fetch_add(1, Ordering::Relaxed);
        rc_trace("ivar_spark_inc", ivar, rc_atomic.load(Ordering::Relaxed));
    }

    rayon::spawn(move || {
        // Force the IVar (evaluate thunk if still pending)
        ivar_force(ivar);

        // Dec IVar RC (spark's reference)
        unsafe {
            let rc_addr = (ivar as *mut i64).sub(1);
            let rc_atomic = &*(rc_addr as *const AtomicI64);
            let old_rc = rc_atomic.fetch_sub(1, Ordering::Release);
            rc_trace("ivar_spark_dec", ivar, old_rc - 1);
            if old_rc == 1 {
                std::sync::atomic::fence(Ordering::Acquire);
                free(ivar);
            }
        }
    });
    0
}

/// Force an IVar: if PENDING, atomically transition to EVALUATING, call thunk,
/// store result, set RESOLVED. If EVALUATING (another thread is working), spin-wait.
/// If RESOLVED, return value immediately.
#[unsafe(export_name = "cranelisp_ivar_force")]
pub extern "C" fn ivar_force(ivar: i64) -> i64 {
    unsafe {
        let state_addr = ivar as *const AtomicI64;
        let state_atomic = &*state_addr;

        // Fast path: already resolved
        let current = state_atomic.load(Ordering::Acquire);
        if current == IVAR_RESOLVED {
            return *((ivar as *const i64).add(1));
        }

        // Try to claim: CAS PENDING → EVALUATING
        match state_atomic.compare_exchange(
            IVAR_PENDING,
            IVAR_EVALUATING,
            Ordering::AcqRel,
            Ordering::Acquire,
        ) {
            Ok(_) => {
                // We won the race — evaluate the thunk
                let thunk_ptr = *((ivar as *const i64).add(2));
                let code_ptr = *(thunk_ptr as *const i64);
                let call: extern "C" fn(i64) -> i64 =
                    std::mem::transmute(code_ptr as *const ());
                let result = call(thunk_ptr);

                // Store result and publish
                *((ivar as *mut i64).add(1)) = result;
                state_atomic.store(IVAR_RESOLVED, Ordering::Release);
                result
            }
            Err(_) => {
                // Another thread is evaluating — spin-wait until resolved
                loop {
                    let s = state_atomic.load(Ordering::Acquire);
                    if s == IVAR_RESOLVED {
                        return *((ivar as *const i64).add(1));
                    }
                    std::hint::spin_loop();
                }
            }
        }
    }
}

/// Check for RC underflow after an atomic dec. Called from inline emit_dec_inline
/// in JIT-generated code. In debug builds, panics on underflow. In release, no-op.
/// Also logs the dec operation when RC tracing is enabled.
#[unsafe(export_name = "cranelisp_rc_underflow_check")]
pub extern "C" fn rc_underflow_check(val: i64, old_rc: i64) -> i64 {
    debug_assert!(
        old_rc > 0,
        "RC underflow: inline dec on val={:#x} with old_rc={} (double-dec?)",
        val as u64,
        old_rc
    );
    rc_trace("dec_inline", val, old_rc - 1);
    0
}

/// Panic with a cranelisp string message (heap pointer to [i64 len][u8 bytes...]).
/// Used for match exhaustiveness failures at runtime.
#[unsafe(export_name = "cranelisp_panic")]
pub extern "C" fn panic(msg_ptr: i64) -> i64 {
    let len = unsafe { *(msg_ptr as *const i64) } as usize;
    let bytes = unsafe { std::slice::from_raw_parts((msg_ptr as *const u8).add(8), len) };
    let msg = std::str::from_utf8(bytes).unwrap_or("unknown error");
    eprintln!("panic: {}", msg);
    std::process::exit(1);
}
