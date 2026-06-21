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

/// Total allocations since the last [`reset_counts`] (process-global stat;
/// read by int's `/mem` slash command). No state across sessions — test
/// contexts call [`reset_counts`] at session start.
pub fn alloc_count() -> usize {
    ALLOC_COUNT.load(Ordering::Relaxed)
}

/// Total deallocations since the last [`reset_counts`] (process-global stat).
pub fn dealloc_count() -> usize {
    DEALLOC_COUNT.load(Ordering::Relaxed)
}

/// Cumulative bytes ever allocated since the last [`reset_counts`].
pub fn bytes_allocated() -> usize {
    BYTES_ALLOCATED.load(Ordering::Relaxed)
}

/// Bytes currently live (allocated minus freed) since the last [`reset_counts`].
pub fn bytes_current() -> usize {
    BYTES_CURRENT.load(Ordering::Relaxed)
}

/// High-water mark of live bytes since the last [`reset_counts`].
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
///
/// Linker symbol is `runtime/alloc` (per src/CLAUDE.md "Runtime infrastructure
/// uses `runtime/name`" convention) so codegen's `declare_function("runtime/alloc",
/// Linkage::Import, ...)` in object/link mode resolves cleanly against the bundle.
/// JIT mode is unaffected — it registers the function pointer by Rust path
/// (`cranelisp_runtime::heap_alloc`), not by linker name.
#[unsafe(export_name = "runtime/alloc")]
pub extern "C" fn heap_alloc(payload_size: i64) -> i64 {
    alloc_with_rc(payload_size as usize) as i64
}

/// Allocate a heap object. Returns **payload pointer** (base + HeapHeader::SIZE).
///
/// Used as `HostCallbacks.alloc` for platform DLLs, which write fields
/// starting at payload offset 0. The DLL code then subtracts HEAP_HEADER_SIZE
/// to get the base pointer for return values.
#[unsafe(no_mangle)]
pub extern "C" fn heap_alloc_payload(payload_size: i64) -> i64 {
    let base = alloc_with_rc(payload_size as usize);
    base as i64 + cranelisp_types::HeapHeader::SIZE as i64
}

/// Allocate a tagged heap ADT and write its variant tag + fields. Returns the
/// **alloc base pointer** as i64.
///
/// This is the wired implementation of `cranelisp_platform::HostCallbacks::
/// alloc_with_tag` (FIXME 0229 step 1 / `design/platform/host-wiring-s76.md` §2).
/// `int`'s host wiring writes this fn pointer into both `HostCallbacks`
/// construction sites (the JIT path and the `--link` path), replacing
/// `cranelisp_platform::null_alloc_with_tag` and removing the R1 gate. It is a
/// **Rust-path host-callback provider** — reached by the `cranelisp_intrinsics::
/// cranelisp_alloc_with_tag` path, NOT a backend-emitted call. It is therefore
/// deliberately **absent from [`crate::catalog::intrinsics_table`]** (which
/// catalogs only the string-named, `Linkage::Import`-resolved targets the
/// backend emits); a plain `extern "C" fn` is the minimum mechanism (Principle
/// 6). It is a sibling of [`heap_alloc_payload`], the provider for the
/// `HostCallbacks::alloc` field.
///
/// # Layout produced (the platform↔intrinsics↔int three-way ABI)
///
/// Identical to the backend's `ConstrADT` data-constructor emission
/// (`cranelisp-backend` `HeapAdt`: header | tag@16 | field_0@24 | …) so a host-
/// constructed ADT value is indistinguishable from a JIT-constructed one:
///
/// ```text
/// total_size = 16 (HeapHeader) + 8 (tag) + 8 * field_count
/// [total_size: i64][rc: i64 = 1]   ; HeapHeader, written by alloc_with_rc
/// [tag: u32][pad: u32]             ; payload + 0  (alloc_base + 16)
/// [field_0: i64][field_1: i64]…    ; payload + 8, +16, …
/// return: alloc BASE pointer       ; matches CLString / CLAdt::from_raw
/// ```
///
/// The `tag` is the variant discriminant; `field_count` `i64` values are copied
/// verbatim from `fields_ptr`. The tag is written as a full zeroed 8-byte slot
/// (u32 tag + 4 bytes pad), which reads back identically to the backend's i64
/// tag store for the in-range tag values ADT discrimination uses
/// (little-endian). `alloc_with_rc` zero-initialises the allocation, so the pad
/// bytes are zero. The data-constructor (non-nullary) layout only — nullary
/// constructors are bare i64 tags and are never constructed through this path.
///
/// # Safety
///
/// `fields_ptr` must point to at least `field_count` contiguous `i64` values.
/// `extern "C"` so it can be stored as a `HostCallbacks` callback fn pointer and
/// invoked across the platform FFI boundary.
// The fn must match `cranelisp_platform::HostCallbacks::alloc_with_tag`, which
// is a *safe* `extern "C" fn(u32, u32, *const i64) -> i64` callback-pointer
// type. It cannot be `unsafe` without diverging from that ABI signature, so the
// raw-pointer-deref lint is suppressed with the safety contract stated in the
// `# Safety` doc section above (caller guarantees `fields_ptr` validity).
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_alloc_with_tag(
    tag: u32,
    field_count: u32,
    fields_ptr: *const i64,
) -> i64 {
    let field_count = field_count as usize;
    // Payload = tag slot (8 bytes) + one i64 per field. Mirrors the backend's
    // `HeapAdt::payload_size(field_count)` (`1 + field_count` i64 slots).
    let payload_size = (1 + field_count) * std::mem::size_of::<i64>();
    let base = alloc_with_rc(payload_size);

    // SAFETY: `base` was just allocated with HeapHeader::SIZE + payload_size
    // bytes (alloc_with_rc never returns null — it calls handle_alloc_error).
    // The tag goes at the payload start (base + HeapHeader::SIZE); fields follow
    // at 8-byte strides. The caller guarantees `fields_ptr` addresses
    // `field_count` i64s.
    unsafe {
        let payload = base.add(HeapHeader::SIZE);
        // Write the 4-byte tag at payload+0; the surrounding 8-byte slot is
        // already zeroed by alloc_with_rc, so the 4 pad bytes are zero and the
        // slot reads back as `tag as i64`.
        *(payload as *mut u32) = tag;
        let fields = payload.add(std::mem::size_of::<i64>()) as *mut i64;
        for i in 0..field_count {
            *fields.add(i) = *fields_ptr.add(i);
        }
    }

    base as i64
}

/// Deallocate a heap object. Reads alloc_size from HeapHeader at base pointer.
///
/// Linker symbol: `runtime/dealloc` (per runtime/* JIT-name convention).
#[unsafe(export_name = "runtime/dealloc")]
pub extern "C" fn heap_dealloc(base_ptr: i64) -> i64 {
    // SAFETY: JIT code guarantees base_ptr was returned by heap_alloc
    // and the object's RC has reached zero.
    unsafe { dealloc(base_ptr as *mut u8) };
    0
}

#[cfg(test)]
mod tests;
