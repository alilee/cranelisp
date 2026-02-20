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
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

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
