//! Heap allocator for JIT-compiled Cranelisp code.
//!
//! Base-pointer convention: `heap_alloc` returns the start of the allocation
//! (offset 0 = alloc_size, offset 8 = rc). All field accesses use positive offsets.
//! This departs from the sketch's interior-pointer convention.

use std::alloc::{self, Layout};
use std::sync::atomic::{AtomicUsize, Ordering};
// Debug-only: the `LIVE_ALLOCS` / `FREED_TRACKED` databuf-liveness guards and the
// `CRANELISP_HEAP_SCAN` gate below are all `#[cfg(debug_assertions)]`, so these
// imports are unused in release. Gate the import to match (a plain `use` warns
// unused in release; deleting it breaks the debug build — the two-profile trap).
#[cfg(debug_assertions)]
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

/// Live allocation map for double-free + header-integrity detection. Debug builds
/// only. Maps base pointer → the `total_size` written into its header at alloc, so
/// `dealloc` can verify the header was not clobbered by an adjacent overrun (a
/// wrong-size free is what glibc reports as `chunks in smallbin corrupted`).
#[cfg(debug_assertions)]
static LIVE_ALLOCS: LazyLock<Mutex<std::collections::HashMap<usize, usize>>> =
    LazyLock::new(|| Mutex::new(std::collections::HashMap::new()));

/// FIXME 0494: freed tracked allocations → (total_size, payload word @+16) captured
/// at free. Lets `rc::rc_dec_check` report the TYPE/identity of a stale-dec'd value
/// (size discriminates closure / String / ADT / Vec-struct; the payload word is the
/// tag / len / code-ptr). Cleared on re-alloc at the same address.
#[cfg(debug_assertions)]
static FREED_TRACKED: LazyLock<Mutex<std::collections::HashMap<usize, (usize, i64)>>> =
    LazyLock::new(|| Mutex::new(std::collections::HashMap::new()));

/// Report `(total_size, payload_word@16)` recorded at the last free of `ptr`, if it
/// is a freed-and-not-reallocated tracked allocation. The payload word (the ADT
/// tag / String len / closure code-ptr) helps identify the TYPE of a stale-dec'd
/// value. Debug-only diagnostic used by [`crate::rc::rc_dec_check`].
#[cfg(debug_assertions)]
pub(crate) fn freed_info(ptr: usize) -> Option<(usize, i64)> {
    FREED_TRACKED
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .get(&ptr)
        .copied()
}

// ---------------------------------------------------------------------------
// Public Rust API for tracking (used by /qa integration tests)
// ---------------------------------------------------------------------------

// The four counter accessors are **process-lifetime evidence, with no reset
// seam** (S118 ruling 7 / S116 ruling 5; `bounded-contexts.md` §4b invariant 8).
// The absence of a public reset is load-bearing, not an omission: the M3
// alloc/free-parity check's ONLY evidence is these counters, so an API that can
// zero them is an API that can break the instrument (Principle 18 — the ledger
// is trustworthy because no way exists to falsify it). A consumer needing a
// per-window delta snapshots and subtracts.

/// Total allocations this process (monotonic, process-global; read by int's
/// `/mem` slash command).
pub fn alloc_count() -> usize {
    ALLOC_COUNT.load(Ordering::Relaxed)
}

/// Total deallocations this process (monotonic, process-global).
pub fn dealloc_count() -> usize {
    DEALLOC_COUNT.load(Ordering::Relaxed)
}

/// Cumulative bytes ever allocated this process (monotonic).
pub fn bytes_allocated() -> usize {
    BYTES_ALLOCATED.load(Ordering::Relaxed)
}

/// Bytes currently live this process — allocated minus freed. The one
/// non-monotonic member of the family (it falls as blocks are released).
pub fn bytes_current() -> usize {
    BYTES_CURRENT.load(Ordering::Relaxed)
}

/// Check if a pointer is currently live (debug builds only).
#[cfg(debug_assertions)]
pub fn is_live(ptr: usize) -> bool {
    LIVE_ALLOCS
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .contains_key(&ptr)
}

/// Snapshot of the currently-live tracked allocations `(base, size, payload@16)`
/// (debug builds only). Consumed by the M3 alloc/free parity exit check to
/// report a non-empty live set (a leak face). The blocks are live, so reading
/// `payload@16` is sound.
#[cfg(debug_assertions)]
pub(crate) fn live_alloc_snapshot() -> Vec<(usize, usize, i64)> {
    let live = LIVE_ALLOCS.lock().unwrap_or_else(|e| e.into_inner());
    live.iter()
        .map(|(&addr, &size)| {
            // SAFETY: `addr` is a currently-live tracked allocation base of
            // `size` bytes; `payload@16` is within it when `size >= 24`.
            let payload = if size >= 24 {
                unsafe { *((addr as *const u8).add(16) as *const i64) }
            } else {
                0
            };
            (addr, size, payload)
        })
        .collect()
}

/// Debug + env-gated full-heap header scan (FIXME 0494 localization). When
/// `CRANELISP_HEAP_SCAN` is set, validates that EVERY currently-live tracked
/// allocation's header `alloc_size` still equals what was recorded at alloc. Fires
/// at the first corrupted chunk — catching an overrun into a live chunk's header at
/// the earliest subsequent alloc/free, together with the `site` label of where in
/// the lifecycle it was noticed. Layout-neutral (reads a side table + existing
/// headers; allocates nothing new in the heap). O(live) per call — acceptable for a
/// repro, off by default.
#[cfg(debug_assertions)]
fn scan_live_headers(site: &'static str) {
    use std::sync::atomic::AtomicBool;
    static ENABLED: LazyLock<bool> =
        LazyLock::new(|| std::env::var_os("CRANELISP_HEAP_SCAN").is_some());
    if !*ENABLED {
        return;
    }
    static TRIPPED: AtomicBool = AtomicBool::new(false);
    if TRIPPED.load(Ordering::Relaxed) {
        return;
    }
    let live = LIVE_ALLOCS.lock().unwrap_or_else(|e| e.into_inner());
    for (&addr, &recorded) in live.iter() {
        // SAFETY: `addr` is a currently-live tracked allocation base.
        let header = unsafe { *(addr as *const i64) } as usize;
        if header != recorded {
            TRIPPED.store(true, Ordering::Relaxed);
            panic!(
                "HEAP HEADER CORRUPTED (scan @ {site}) at {addr:#x}: header alloc_size \
                 reads {header} but chunk was allocated with {recorded}. An overrun \
                 clobbered a LIVE chunk's header. (FIXME 0494 bug #2.)"
            );
        }
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
    #[cfg(debug_assertions)]
    scan_live_headers("alloc-entry");
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

    // Update tracking counters. (The live-bytes high-water counter went with its
    // accessor in S118 ruling 7: with no consumer left it was a per-allocation
    // CAS loop no API could observe — cost, not evidence.)
    ALLOC_COUNT.fetch_add(1, Ordering::Relaxed);
    BYTES_ALLOCATED.fetch_add(total_size, Ordering::Relaxed);
    BYTES_CURRENT.fetch_add(total_size, Ordering::Relaxed);

    #[cfg(debug_assertions)]
    {
        LIVE_ALLOCS
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(base as usize, total_size);
        FREED_TRACKED
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .remove(&(base as usize));
    }

    // M3 (design §3): register the alloc/free parity atexit check the first time
    // a parity gate is observed on. Byte-identical-off — one cached bool load,
    // no registration when both gates are unset.
    crate::diagnostics::ensure_parity_registered();

    // §7.2 `PostAlloc` — the ONE alloc-side fault-plant event, after header init
    // + counters + tracking and before `rc_trace`/return. Unarmed ⇒ one cached
    // `Option` read and `NoAction`; the only armed action is `CapturePlant`,
    // which records `(base, total_size)` and touches no memory.
    let _ = crate::diagnostics::test_fault_event(crate::diagnostics::FaultEvent::PostAlloc {
        base: base as i64,
        total_size,
    });

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

    // SAFETY: caller guarantees base is valid and was returned by alloc_with_rc.
    let total_size = unsafe { *(base as *const i64) } as usize;

    #[cfg(debug_assertions)]
    scan_live_headers("dealloc-entry");

    // A4 release-gated PREcheck (design §7.5): hoisted ABOVE the debug tracking
    // block (whose always-on twins would otherwise pre-empt it in the debug
    // profile) and above `Layout` construction, so a malformed or poisoned
    // header produces a located seam message instead of a `Layout` panic or a
    // free with the wrong layout. Reads no side table, so it fires in the
    // release/`--link` lane too. The double-free + header-integrity halves stay
    // debug-only (they need `LIVE_ALLOCS`); M3's exit parity is their release
    // face (a double-free shows as DEALLOC_COUNT > ALLOC_COUNT).
    if crate::diagnostics::rc_check_release_enabled()
        && !crate::diagnostics::header_size_plausible(total_size as i64)
    {
        crate::diagnostics::seam_hard_fail(&format!(
            "dealloc: PRECHECK rejected base {:#x} BEFORE disposal — header alloc_size \
             {total_size} is not a plausible allocation size (below HeapHeader::SIZE, \
             or no valid Layout)",
            base as usize
        ));
    }

    // §7.2 `PreFree` — the ONE free-side pre-disposal fault-plant event, before
    // the debug tracking block. `SuppressFree` returns immediately: no
    // `LIVE_ALLOCS` removal, no scrub/quarantine, no `DEALLOC_COUNT` bump, so the
    // block is GENUINELY leaked and M3's ledger stays truthful (the count delta
    // AND the surviving live address are both real). Fires at most once.
    if crate::diagnostics::test_fault_event(crate::diagnostics::FaultEvent::PreFree {
        base: base as i64,
        total_size,
    }) == crate::diagnostics::FaultAction::SuppressFree
    {
        return;
    }

    #[cfg(debug_assertions)]
    {
        let addr = base as usize;
        let mut live = LIVE_ALLOCS.lock().unwrap_or_else(|e| e.into_inner());
        let recorded = live.remove(&addr);
        debug_assert!(
            recorded.is_some(),
            "double free or invalid free at {addr:#x}"
        );
        // Header-integrity check (FIXME 0494): the `total_size` we read from the
        // header MUST equal what we wrote at alloc. A mismatch means an adjacent
        // overrun clobbered this chunk's header — freeing with the wrong Layout is
        // exactly the `free(): chunks in smallbin corrupted` glibc reports. This
        // is layout-neutral (a side table), so it does not close the timing window
        // ASAN / MALLOC_CHECK_ close.
        if let Some(expected) = recorded {
            debug_assert!(
                expected == total_size,
                "HEAP HEADER CORRUPTED at {addr:#x}: header alloc_size reads \
                 {total_size} but this chunk was allocated with {expected} — an \
                 adjacent-chunk overrun clobbered the header. (FIXME 0494 bug #2.)"
            );
        }
    }

    debug_assert!(
        total_size >= HeapHeader::SIZE,
        "invalid alloc_size {total_size} at {:#x}",
        base as usize
    );

    let layout = Layout::from_size_align(total_size, 8)
        .unwrap_or_else(|_| unreachable!("invariant: valid layout for size {total_size}"));

    rc::rc_trace("free", base as i64, 0);

    // Fixed order (design §4): capture FREED_TRACKED identity → (M2) scrub →
    // (M1) quarantine-or-release → bump DEALLOC_COUNT.
    #[cfg(debug_assertions)]
    {
        // Capture size + payload word @+16 BEFORE scrubbing, for stale-dec reports.
        let payload_word = unsafe { *((base as *const u8).add(16) as *const i64) };
        FREED_TRACKED
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(base as usize, (total_size, payload_word));
    }

    // M2 scrub + M1 quarantine-or-release. When both modes are off this is one
    // cached bool load and `withheld == false` (byte-identical to the old
    // physical free below).
    // SAFETY: base is a live allocation of total_size == layout.size() bytes.
    let withheld = unsafe { crate::diagnostics::scrub_and_dispose(base, layout, total_size) };
    if !withheld {
        // SAFETY: base was allocated with this layout by alloc_with_rc and has
        // not been quarantined.
        unsafe { alloc::dealloc(base, layout) };
    }

    DEALLOC_COUNT.fetch_add(1, Ordering::Relaxed);
    BYTES_CURRENT.fetch_sub(total_size, Ordering::Relaxed);

    // §7.2 `PostFree` — the ONE post-discharge fault-plant event.
    // `ExtraDischarge` bumps the ledger once more WITHOUT touching memory: the
    // only UB-free route to the `deallocs > allocs` polarity. It proves the
    // report polarity + atexit wiring, not a real double-free (whose face stays
    // the debug `LIVE_ALLOCS.remove` assert above). The counter stays private to
    // this module — the hook never gets a setter.
    if crate::diagnostics::test_fault_event(crate::diagnostics::FaultEvent::PostFree {
        base: base as i64,
        total_size,
        withheld,
    }) == crate::diagnostics::FaultAction::ExtraDischarge
    {
        DEALLOC_COUNT.fetch_add(1, Ordering::Relaxed);
    }
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
/// (`cranelisp_intrinsics::heap_alloc`), not by linker name.
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
