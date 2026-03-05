//! Heap allocator for JIT-compiled Cranelisp code.
//!
//! Base-pointer convention: `heap_alloc` returns the start of the allocation
//! (offset 0 = alloc_size, offset 8 = rc). All field accesses use positive offsets.
//! This departs from the sketch's interior-pointer convention.

use std::alloc::{self, Layout};
use std::collections::HashSet;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{LazyLock, Mutex};

use cranelisp_types::HeapHeader;

use crate::rc;

// ---------------------------------------------------------------------------
// Allocation tracking counters (atomic, thread-safe)
// ---------------------------------------------------------------------------

static ALLOC_COUNT: AtomicUsize = AtomicUsize::new(0);
static DEALLOC_COUNT: AtomicUsize = AtomicUsize::new(0);
static BYTES_ALLOCATED: AtomicUsize = AtomicUsize::new(0);
static BYTES_CURRENT: AtomicUsize = AtomicUsize::new(0);
static BYTES_PEAK: AtomicUsize = AtomicUsize::new(0);

/// Live allocation set for double-free detection. Debug builds only.
#[cfg(debug_assertions)]
static LIVE_ALLOCS: LazyLock<Mutex<HashSet<usize>>> =
    LazyLock::new(|| Mutex::new(HashSet::new()));

// ---------------------------------------------------------------------------
// Public Rust API for tracking (used by /qa integration tests)
// ---------------------------------------------------------------------------

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

/// Check if a pointer is currently live (debug builds only).
#[cfg(debug_assertions)]
pub fn is_live(ptr: usize) -> bool {
    LIVE_ALLOCS.lock().unwrap_or_else(|e| e.into_inner()).contains(&ptr)
}

/// Reset all counters. Called between tests for isolation.
pub fn reset_counts() {
    ALLOC_COUNT.store(0, Ordering::Relaxed);
    DEALLOC_COUNT.store(0, Ordering::Relaxed);
    BYTES_ALLOCATED.store(0, Ordering::Relaxed);
    BYTES_CURRENT.store(0, Ordering::Relaxed);
    BYTES_PEAK.store(0, Ordering::Relaxed);
    #[cfg(debug_assertions)]
    {
        LIVE_ALLOCS.lock().unwrap_or_else(|e| e.into_inner()).clear();
    }
}

// ---------------------------------------------------------------------------
// Core allocator
// ---------------------------------------------------------------------------

/// Allocate a heap object with RC header. Returns the **base pointer**.
///
/// Layout: `[alloc_size: i64 | rc: i64 | ... payload_size bytes ...]`
///
/// The returned pointer points to offset 0 (alloc_size field).
/// RC is initialised to 1.
pub fn alloc_with_rc(payload_size: usize) -> *mut u8 {
    let total_size = HeapHeader::SIZE + payload_size;
    let layout = Layout::from_size_align(total_size, 8)
        .unwrap_or_else(|_| unreachable!("invariant: valid layout for size {total_size}"));

    // SAFETY: layout has non-zero size (HeapHeader::SIZE >= 16).
    let base = unsafe { alloc::alloc_zeroed(layout) };
    if base.is_null() {
        alloc::handle_alloc_error(layout);
    }

    // Write header fields.
    // SAFETY: base is valid, aligned, and points to total_size bytes.
    unsafe {
        // alloc_size at offset 0
        *(base as *mut i64) = total_size as i64;
        // rc at offset 8
        *(base.add(HeapHeader::RC_OFFSET as usize) as *mut i64) = 1;
    }

    // Update tracking counters.
    ALLOC_COUNT.fetch_add(1, Ordering::Relaxed);
    BYTES_ALLOCATED.fetch_add(total_size, Ordering::Relaxed);
    let current = BYTES_CURRENT.fetch_add(total_size, Ordering::Relaxed) + total_size;
    // Update peak (relaxed CAS loop).
    let mut peak = BYTES_PEAK.load(Ordering::Relaxed);
    while current > peak {
        match BYTES_PEAK.compare_exchange_weak(peak, current, Ordering::Relaxed, Ordering::Relaxed)
        {
            Ok(_) => break,
            Err(actual) => peak = actual,
        }
    }

    #[cfg(debug_assertions)]
    {
        LIVE_ALLOCS.lock().unwrap_or_else(|e| e.into_inner()).insert(base as usize);
    }

    rc::rc_trace("alloc", base as i64, 1);

    base
}

/// Deallocate a heap object. Reads alloc_size from the base pointer.
///
/// # Safety
///
/// `base` must be a pointer returned by `alloc_with_rc` that has not been freed.
pub unsafe fn dealloc(base: *mut u8) {
    debug_assert!(!base.is_null(), "dealloc called with null pointer");

    #[cfg(debug_assertions)]
    {
        let addr = base as usize;
        let mut live = LIVE_ALLOCS.lock().unwrap_or_else(|e| e.into_inner());
        debug_assert!(
            live.remove(&addr),
            "double free or invalid free at {addr:#x}"
        );
    }

    // SAFETY: caller guarantees base is valid and was returned by alloc_with_rc.
    let total_size = unsafe { *(base as *const i64) } as usize;
    debug_assert!(
        total_size >= HeapHeader::SIZE,
        "invalid alloc_size {total_size} at {:#x}",
        base as usize
    );

    let layout = Layout::from_size_align(total_size, 8)
        .unwrap_or_else(|_| unreachable!("invariant: valid layout for size {total_size}"));

    rc::rc_trace("free", base as i64, 0);

    // SAFETY: base was allocated with this layout by alloc_with_rc.
    unsafe { alloc::dealloc(base, layout) };

    DEALLOC_COUNT.fetch_add(1, Ordering::Relaxed);
    BYTES_CURRENT.fetch_sub(total_size, Ordering::Relaxed);
}

// ---------------------------------------------------------------------------
// Extern C interface (called from JIT code)
// ---------------------------------------------------------------------------

/// Allocate a heap object. Writes HeapHeader (alloc_size, rc=1). Returns base pointer.
///
/// `payload_size`: bytes needed after the header.
#[unsafe(no_mangle)]
pub extern "C" fn heap_alloc(payload_size: i64) -> i64 {
    alloc_with_rc(payload_size as usize) as i64
}

/// Deallocate a heap object. Reads alloc_size from HeapHeader at base pointer.
#[unsafe(no_mangle)]
pub extern "C" fn heap_dealloc(base_ptr: i64) -> i64 {
    // SAFETY: JIT code guarantees base_ptr was returned by heap_alloc
    // and the object's RC has reached zero.
    unsafe { dealloc(base_ptr as *mut u8) };
    0
}

#[cfg(test)]
mod tests {
    use super::*;

    // Tests use delta-based assertions (snapshot before/after) because
    // global counters are shared across parallel tests.

    #[test]
    fn test_alloc_and_dealloc_round_trip() {
        let allocs_before = alloc_count();
        let deallocs_before = dealloc_count();

        let base = alloc_with_rc(32);
        assert!(!base.is_null());

        // Check header.
        unsafe {
            let alloc_size = *(base as *const i64);
            assert_eq!(alloc_size, 48); // 16 header + 32 payload
            let rc = *(base.add(8) as *const i64);
            assert_eq!(rc, 1);
        }

        assert!(alloc_count() - allocs_before >= 1);

        unsafe { dealloc(base) };

        assert!(dealloc_count() - deallocs_before >= 1);
    }

    #[test]
    fn test_tracking_counters() {
        let allocs_before = alloc_count();
        let deallocs_before = dealloc_count();
        let allocated_before = bytes_allocated();

        let a = alloc_with_rc(8);
        let b = alloc_with_rc(16);
        assert!(alloc_count() - allocs_before >= 2);
        assert!(bytes_allocated() - allocated_before >= 24 + 32); // (16+8) + (16+16)

        unsafe { dealloc(a) };
        assert!(dealloc_count() - deallocs_before >= 1);

        unsafe { dealloc(b) };
        assert!(dealloc_count() - deallocs_before >= 2);
    }

    #[cfg(debug_assertions)]
    #[test]
    fn test_live_allocs_tracking() {
        let base = alloc_with_rc(16);
        assert!(is_live(base as usize));

        unsafe { dealloc(base) };
        assert!(!is_live(base as usize));
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "double free")]
    fn test_double_free_detected() {
        let base = alloc_with_rc(16);
        unsafe {
            dealloc(base);
            dealloc(base); // should panic
        }
    }

    #[test]
    fn test_extern_c_interface() {
        let allocs_before = alloc_count();
        let deallocs_before = dealloc_count();

        let ptr = heap_alloc(24);
        assert_ne!(ptr, 0);

        // Check header via the returned base pointer.
        unsafe {
            let alloc_size = *(ptr as *const i64);
            assert_eq!(alloc_size, 40); // 16 + 24
            let rc = *((ptr as *const u8).add(8) as *const i64);
            assert_eq!(rc, 1);
        }

        assert!(alloc_count() - allocs_before >= 1);
        heap_dealloc(ptr);
        assert!(dealloc_count() - deallocs_before >= 1);
    }

    #[test]
    fn test_zero_payload() {
        // Zero payload is valid — just a bare header (alloc_size + rc).
        let base = alloc_with_rc(0);
        unsafe {
            let alloc_size = *(base as *const i64);
            assert_eq!(alloc_size, 16); // header only
        }
        unsafe { dealloc(base) };
    }
}
