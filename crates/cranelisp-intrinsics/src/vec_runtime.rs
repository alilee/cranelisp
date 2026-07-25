//! Vec runtime primitives for JIT-compiled Cranelisp code.
//!
//! A Vec value consists of two allocations:
//! - **Vec struct**: `[HeapHeader(16) | len(8) | cap(8) | data_ptr(8)]` = 40 bytes total
//!   Allocated via `alloc_with_rc` (has RC header).
//! - **Data buffer**: `cap * 8` bytes, plain allocation (no RC header).
//!
//! Layout offsets from base pointer:
//! - `+0`:  alloc_size (i64, from HeapHeader)
//! - `+8`:  rc (i64, from HeapHeader)
//! - `+16`: len (i64)
//! - `+24`: cap (i64)
//! - `+32`: data_ptr (i64, pointer to data buffer)
//!
//! All elements are i64 (uniform representation). Only indices `0..len` are live.
//!
//! ## Module name rationale
//!
//! Renamed from `vec` to `vec_runtime` in Sprint 67 Wave 3 (FIXME 0180 close).
//! The user-callable `vec-len` accessor physically lives in
//! `cranelisp-primitives::vec`; everything else here is backend-emitted-call
//! infrastructure (`runtime/vec_new`, `runtime/vec_drop`, the COW paths
//! `vec-set-copy` / `vec-push-copy` / `vec-push-grow`).

use std::alloc::{self, Layout};

use crate::alloc as heap_alloc_mod;

// ---------------------------------------------------------------------------
// Layout constants
// ---------------------------------------------------------------------------

/// Offset of `len` field from base pointer.
///
/// Blessed public-ABI contract (FIXME 0245): `cranelisp-primitives` reads this.
pub const LEN_OFFSET: usize = 16;
/// Offset of `cap` field from base pointer.
///
/// Blessed public-ABI contract (FIXME 0245): `cranelisp-primitives` reads this.
pub const CAP_OFFSET: usize = 24;
/// Offset of `data_ptr` field from base pointer.
///
/// Blessed public-ABI contract (FIXME 0245): `cranelisp-primitives` reads this.
pub const DATA_PTR_OFFSET: usize = 32;
/// Payload size after HeapHeader: len + cap + data_ptr = 24 bytes.
const VEC_PAYLOAD_SIZE: usize = 24;

// Single-source guard: lock the blessed layout-ABI offsets (FIXME 0245).
// Future drift in these values fails the build.
const _: () = assert!(LEN_OFFSET == 16);
const _: () = assert!(CAP_OFFSET == 24);
const _: () = assert!(DATA_PTR_OFFSET == 32);

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Read the `len` field from a Vec base pointer.
///
/// # Safety
/// `base` must point to a valid Vec struct.
#[inline]
unsafe fn read_len(base: *const u8) -> i64 {
    unsafe { *base.add(LEN_OFFSET).cast::<i64>() }
}

/// Read the `cap` field from a Vec base pointer.
///
/// # Safety
/// `base` must point to a valid Vec struct.
#[inline]
unsafe fn read_cap(base: *const u8) -> i64 {
    unsafe { *base.add(CAP_OFFSET).cast::<i64>() }
}

/// Read the `data_ptr` field from a Vec base pointer.
///
/// # Safety
/// `base` must point to a valid Vec struct.
#[inline]
unsafe fn read_data_ptr(base: *const u8) -> *mut i64 {
    unsafe { *base.add(DATA_PTR_OFFSET).cast::<i64>() as *mut i64 }
}

/// Write the `len` field.
#[inline]
unsafe fn write_len(base: *mut u8, len: i64) {
    unsafe {
        *base.add(LEN_OFFSET).cast::<i64>() = len;
    }
}

/// Write the `cap` field.
#[inline]
unsafe fn write_cap(base: *mut u8, cap: i64) {
    unsafe {
        *base.add(CAP_OFFSET).cast::<i64>() = cap;
    }
}

/// Write the `data_ptr` field.
#[inline]
unsafe fn write_data_ptr(base: *mut u8, data_ptr: *mut i64) {
    unsafe {
        *base.add(DATA_PTR_OFFSET).cast::<i64>() = data_ptr as i64;
    }
}

/// Allocate a data buffer of `cap` elements (each i64 = 8 bytes).
/// Returns null if cap == 0.
///
/// This is the **single** vec-data-buffer alloc path (Principle 7), paired with
/// [`free_data_buffer`]. `pub(crate)` so test fixtures that hand-build Vec structs
/// (e.g. `drop::tests::make_vec_struct`) allocate through it and register with the
/// debug data-buffer guard ([`databuf_guard::on_alloc`]) — a raw `alloc_zeroed`
/// bypass leaves the buffer untracked and trips the guard's "NOT live" tripwire
/// the moment the buffer crosses [`debug_assert_live_buffer`].
pub(crate) fn alloc_data_buffer(cap: i64) -> *mut i64 {
    if cap <= 0 {
        return std::ptr::null_mut();
    }
    let byte_size = cap as usize * 8;
    let layout = Layout::from_size_align(byte_size, 8)
        .unwrap_or_else(|_| unreachable!("invariant: valid layout for size {byte_size}"));
    // SAFETY: layout is non-zero (cap > 0).
    let ptr = unsafe { alloc::alloc_zeroed(layout) };
    if ptr.is_null() {
        alloc::handle_alloc_error(layout);
    }
    #[cfg(debug_assertions)]
    databuf_guard::on_alloc(ptr as usize, cap);
    ptr as *mut i64
}

/// Debug-only: validate that a vec's `data_ptr`/`cap` names a currently-live data
/// buffer (see [`databuf_guard::assert_live`]). No-op in release. Exposed so
/// `drop.rs`'s `consume_vec_with` can check a Vec before walking + freeing it.
#[inline]
pub(crate) fn debug_assert_live_buffer(data_ptr: *const i64, cap: i64, site: &'static str) {
    #[cfg(debug_assertions)]
    databuf_guard::assert_live(data_ptr as usize, cap, site);
    #[cfg(not(debug_assertions))]
    let _ = (data_ptr, cap, site);
}

/// Free a data buffer of `cap` elements.
///
/// `site` names the calling free path — used ONLY by the debug data-buffer guard
/// ([`databuf_guard`]) to report both sites on a double-free; it is a no-op string
/// in release (the guard is `#[cfg(debug_assertions)]`, so it does not affect the
/// release code path or heap layout — Principle 14 / `tests/CLAUDE.md`
/// §"Heap-header integrity…").
///
/// This is the **single** vec-data-buffer free path (Principle 7). `drop.rs`'s
/// `consume_vec_with` routes here rather than inlining its own `dealloc`, so every
/// untracked-buffer free crosses the guard.
///
/// # Safety
/// `data_ptr` must have been allocated by `alloc_data_buffer` with the given `cap`.
pub(crate) unsafe fn free_data_buffer(data_ptr: *mut i64, cap: i64, site: &'static str) {
    if data_ptr.is_null() || cap <= 0 {
        return;
    }
    #[cfg(debug_assertions)]
    databuf_guard::on_free(data_ptr as usize, cap, site);
    #[cfg(not(debug_assertions))]
    let _ = site;
    let byte_size = cap as usize * 8;
    let layout = Layout::from_size_align(byte_size, 8)
        .unwrap_or_else(|_| unreachable!("invariant: valid layout for size {byte_size}"));
    unsafe { alloc::dealloc(data_ptr as *mut u8, layout) };
}

// ---------------------------------------------------------------------------
// Debug-only untracked-buffer double-free guard (layout-NEUTRAL)
// ---------------------------------------------------------------------------
//
// Vec **data buffers** are plain `alloc`/`dealloc` allocations with NO RC header,
// so `crate::alloc`'s `LIVE_ALLOCS` double-free debug-assert (which keys on the
// `alloc_with_rc` base) never sees them. This side table extends the same
// double-free / free-of-non-live detection to the untracked data buffers, WITHOUT
// perturbing the allocation itself (no redzone, no padding, no size change) — the
// one class of instrumentation that does not close the layout/timing race window
// that hides bug #2 (FIXME 0494: ASAN + `MALLOC_CHECK_` both HID it by perturbing
// allocator layout). Debug-only; compiled out entirely in release.
#[cfg(debug_assertions)]
mod databuf_guard {
    use std::collections::HashMap;
    use std::sync::{LazyLock, Mutex};

    /// Live data-buffer pointers → their allocated `cap`.
    static LIVE: LazyLock<Mutex<HashMap<usize, i64>>> =
        LazyLock::new(|| Mutex::new(HashMap::new()));
    /// Recently-freed data-buffer pointers → the site that freed them. Cleared on
    /// re-alloc at the same address (so alloc→free→alloc→free reuse is NOT flagged;
    /// only a genuine second free of a still-freed pointer fires — this is why the
    /// side table is immune to the address-reuse false positives that confused the
    /// whole-trace analysis in FIXME 0494).
    static FREED: LazyLock<Mutex<HashMap<usize, &'static str>>> =
        LazyLock::new(|| Mutex::new(HashMap::new()));

    pub(super) fn on_alloc(ptr: usize, cap: i64) {
        LIVE.lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(ptr, cap);
        FREED.lock().unwrap_or_else(|e| e.into_inner()).remove(&ptr);
    }

    #[cfg(test)]
    pub(super) fn is_live(ptr: usize) -> bool {
        LIVE.lock()
            .unwrap_or_else(|e| e.into_inner())
            .contains_key(&ptr)
    }

    /// Validate that `ptr` (a vec's `data_ptr`) is a currently-live data buffer of
    /// the given `cap`. Fires if the buffer was already freed (a use-after-free of a
    /// stale vec whose buffer was reclaimed) or if the recorded cap disagrees (a
    /// corrupted `cap` field). `null`/`cap<=0` (the empty-vec sentinel) is skipped.
    pub(super) fn assert_live(ptr: usize, cap: i64, site: &'static str) {
        if ptr == 0 || cap <= 0 {
            return;
        }
        let live = LIVE.lock().unwrap_or_else(|e| e.into_inner());
        match live.get(&ptr) {
            Some(&live_cap) => {
                debug_assert!(
                    live_cap == cap,
                    "vec op {site} touched data buffer {ptr:#x} with cap {cap} but the \
                     live buffer there has cap {live_cap} — a corrupted cap field or a \
                     stale (reused-address) buffer. (FIXME 0494 bug #2.)"
                );
            }
            None => {
                let prev = FREED
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .get(&ptr)
                    .copied();
                panic!(
                    "USE-AFTER-FREE: vec op {site} touched data buffer {ptr:#x} (cap {cap}) \
                     that is NOT live — it was freed (previous free site = {prev:?}) and not \
                     re-allocated. A stale vec is being operated on after its buffer was \
                     reclaimed. (FIXME 0494 bug #2 — free-ownership defect on the \
                     launched-strand teardown.)"
                );
            }
        }
    }

    pub(super) fn on_free(ptr: usize, cap: i64, site: &'static str) {
        let removed = LIVE.lock().unwrap_or_else(|e| e.into_inner()).remove(&ptr);
        match removed {
            Some(live_cap) => {
                debug_assert!(
                    live_cap == cap,
                    "vec data buffer {ptr:#x} freed with cap {cap} but was allocated \
                     with cap {live_cap} (free site: {site})"
                );
                FREED
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .insert(ptr, site);
            }
            None => {
                let prev = FREED
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .get(&ptr)
                    .copied();
                panic!(
                    "DOUBLE/INVALID FREE of untracked vec data buffer at {ptr:#x}: \
                     this free site = {site}; previous free site = {prev:?}. \
                     (FIXME 0494 bug #2 — free-ownership defect on the launched-strand \
                     teardown.)"
                );
            }
        }
    }
}

/// Type alias for element inc/dec callback function pointer.
type ElemFn = extern "C" fn(i64) -> i64;

/// Call an element function if the pointer is non-null.
#[inline]
fn call_elem_fn(fn_ptr: i64, val: i64) {
    if fn_ptr != 0 {
        let f: ElemFn = unsafe { std::mem::transmute(fn_ptr) };
        f(val);
    }
}

/// Unpublished storage for [`vec_strings_from_owned`].
///
/// The Rust `Vec` retains the complete transferred-owner list until
/// publication. That makes cleanup independent of how many destination slots
/// have been initialized: an unwind releases every transferred HeapString
/// exactly once, then frees whichever Vec allocations exist.
struct UnpublishedVecStrings {
    elements: Vec<i64>,
    base: *mut u8,
    data: *mut i64,
    initialized: usize,
    armed: bool,
}

impl UnpublishedVecStrings {
    fn new(elements: Vec<i64>) -> Self {
        Self {
            elements,
            base: std::ptr::null_mut(),
            data: std::ptr::null_mut(),
            initialized: 0,
            armed: true,
        }
    }

    /// Allocate and initialize the unpublished Vec metadata with `len = 0`.
    ///
    /// # Safety
    ///
    /// Must be called at most once on this guard.
    unsafe fn allocate(&mut self) {
        assert!(self.base.is_null(), "unpublished Vec allocated twice");
        let cap = i64::try_from(self.elements.len())
            .expect("owned Vec String element count must fit in i64");

        self.base = heap_alloc_mod::alloc_with_rc(VEC_PAYLOAD_SIZE);
        // SAFETY: `base` is the fresh live allocation returned above with the
        // exact 24-byte Vec payload required by these three field writes.
        unsafe {
            write_len(self.base, 0);
            write_cap(self.base, cap);
            write_data_ptr(self.base, std::ptr::null_mut());
        }

        self.data = alloc_data_buffer(cap);
        // SAFETY: `base` remains live and owns its Vec metadata; `data` is
        // either null for cap zero or the fresh `cap`-slot allocation.
        unsafe {
            write_data_ptr(self.base, self.data);
        }
    }

    /// Copy the next slots into the unpublished data allocation.
    ///
    /// # Safety
    ///
    /// [`Self::allocate`] must have completed and `end` must not exceed the
    /// transferred element count.
    unsafe fn initialize_prefix(&mut self, end: usize) {
        assert!(end <= self.elements.len(), "initialized prefix exceeds cap");
        assert!(
            end >= self.initialized,
            "initialized prefix cannot move backwards"
        );
        for index in self.initialized..end {
            // SAFETY: `allocate` established `data` as `elements.len()` slots;
            // `index < end <= elements.len()` keeps this write in-bounds.
            unsafe {
                *self.data.add(index) = self.elements[index];
            }
        }
        self.initialized = end;
    }

    /// Publish `len` last and disarm cleanup.
    ///
    /// # Safety
    ///
    /// All element slots must have been initialized.
    unsafe fn publish(mut self) -> i64 {
        assert_eq!(
            self.initialized,
            self.elements.len(),
            "cannot publish a partially initialized Vec String"
        );
        let len = i64::try_from(self.initialized)
            .expect("owned Vec String element count must fit in i64");
        // SAFETY: the guard still owns the live Vec allocation and the
        // equality above proves all `0..len` slots are initialized.
        unsafe {
            write_len(self.base, len);
        }

        let published = self.base as i64;
        self.armed = false;
        published
    }
}

impl Drop for UnpublishedVecStrings {
    fn drop(&mut self) {
        if !self.armed {
            return;
        }

        for &element in &self.elements {
            crate::rc::consume_shallow(element);
        }

        if !self.base.is_null() {
            let cap = i64::try_from(self.elements.len())
                .expect("owned Vec String element count must fit in i64");
            // SAFETY: while armed, the guard uniquely owns `data` (null only
            // at cap zero) and `base`; neither allocation has been published
            // or freed, and both were allocated with these exact layouts.
            unsafe {
                free_data_buffer(self.data, cap, "vec_strings_from_owned(unpublished)");
                heap_alloc_mod::dealloc(self.base);
            }
        }
    }
}

/// Construct a runtime Vec that takes ownership of HeapString references.
///
/// This is a Rust-path helper only. It has no emitted-call symbol and is absent
/// from [`crate::intrinsics_table`].
///
/// # Safety
///
/// Every word in `elements` must be the base pointer of one live HeapString
/// allocation and carry one owned reference transferred to this function.
/// Duplicate words are valid only when the caller owns that many references.
/// From call entry the caller must not consume or separately release any
/// transferred reference, including if this function unwinds. On success the
/// returned live Vec owns exactly those references.
///
/// Before publication this function owns the input `Vec<i64>`, any allocated
/// Vec object and data buffer, and all transferred HeapString references. It
/// initializes every element slot before publishing `len` last. If it unwinds,
/// its guard shallow-consumes every transferred reference exactly once and
/// frees every unpublished allocation exactly once. Only `0..len` is live.
pub unsafe fn vec_strings_from_owned(elements: Vec<i64>) -> i64 {
    let mut unpublished = UnpublishedVecStrings::new(elements);
    // SAFETY: the caller contract transfers every live HeapString owner into
    // this armed guard; each method's precondition is established by the
    // preceding method, ending with every slot initialized before publish.
    unsafe {
        unpublished.allocate();
        unpublished.initialize_prefix(unpublished.elements.len());
        unpublished.publish()
    }
}

/// Borrow the live HeapString words in a runtime Vec for one callback.
///
/// This is a Rust-path helper only. It has no emitted-call symbol and is absent
/// from [`crate::intrinsics_table`].
///
/// # Safety
///
/// `base` must be a non-null, correctly aligned base pointer to a live Vec
/// whose live elements are HeapString base pointers. An owning Vec reference
/// must remain alive and the Vec must not be mutated for the complete callback.
/// The caller remains responsible for allocation provenance and liveness,
/// which runtime field checks cannot establish.
///
/// Before forming the slice this function checks `0 <= len <= cap`, checked
/// `cap * size_of::<i64>()` representability, and that `data_ptr` is non-null
/// and correctly aligned when `cap > 0`. The callback may copy a word only as a
/// non-owning observation; retaining or consuming an element requires an
/// explicit RC operation outside this helper's contract. Normal return and
/// unwind perform no increment, decrement, transfer, or consumption of the Vec
/// or its elements. Safe Rust cannot return the borrowed slice from `read`.
pub unsafe fn with_vec_strings<R>(base: i64, read: impl FnOnce(&[i64]) -> R) -> R {
    let base_addr = usize::try_from(base).expect("Vec String base pointer must be positive");
    assert_ne!(base_addr, 0, "Vec String base pointer must be non-null");
    assert_eq!(
        base_addr % std::mem::align_of::<i64>(),
        0,
        "Vec String base pointer must be aligned"
    );
    let base_ptr = base_addr as *const u8;

    // SAFETY: the caller contract guarantees `base_ptr` is the aligned base of
    // a live Vec allocation, so the fixed-offset len read is valid.
    let len = unsafe { read_len(base_ptr) };
    // SAFETY: the same live canonical Vec allocation contains the cap field at
    // its fixed offset.
    let cap = unsafe { read_cap(base_ptr) };
    assert!(
        0 <= len && len <= cap,
        "Vec String metadata requires 0 <= len <= cap (len={len}, cap={cap})"
    );

    let cap = usize::try_from(cap).expect("non-negative Vec String cap must fit usize");
    let byte_len = cap
        .checked_mul(std::mem::size_of::<i64>())
        .expect("Vec String capacity byte size overflow");
    assert!(
        byte_len <= isize::MAX as usize,
        "Vec String capacity exceeds slice representability"
    );

    // SAFETY: the caller contract guarantees the live Vec allocation contains
    // the data-pointer field at the canonical fixed offset.
    let data = unsafe { read_data_ptr(base_ptr) };
    if cap > 0 {
        assert!(!data.is_null(), "positive-capacity Vec String needs data");
        assert_eq!(
            data.align_offset(std::mem::align_of::<i64>()),
            0,
            "Vec String data pointer must be aligned"
        );
    }

    let len = usize::try_from(len).expect("non-negative Vec String len must fit usize");
    let data = if len == 0 {
        std::ptr::NonNull::<i64>::dangling().as_ptr()
    } else {
        data
    };
    // SAFETY: for zero length `data` is the aligned non-null dangling
    // sentinel. Otherwise the checked metadata gives `len <= cap`, and the
    // caller contract guarantees `data` points to that live initialized Vec
    // buffer for the complete callback.
    let elements = unsafe { std::slice::from_raw_parts(data, len) };
    read(elements)
}

// ---------------------------------------------------------------------------
// Extern C interface (called from JIT code)
// ---------------------------------------------------------------------------

/// Allocate a new Vec with the given initial capacity.
///
/// Allocates the Vec struct (40 bytes = 16 header + 24 payload) via `alloc_with_rc`.
/// Allocates a separate data buffer of `cap * 8` bytes.
/// Sets len=0, cap=cap, data_ptr to the data buffer.
/// Returns base pointer to the Vec struct (rc=1).
///
/// JIT name: "runtime/vec_new" — exported via export_name so link-mode resolves.
#[unsafe(export_name = "runtime/vec_new")]
pub extern "C" fn vec_new(cap: i64) -> i64 {
    let base = heap_alloc_mod::alloc_with_rc(VEC_PAYLOAD_SIZE);
    let data = alloc_data_buffer(cap);

    unsafe {
        write_len(base, 0);
        write_cap(base, cap);
        write_data_ptr(base, data);
    }

    base as i64
}

// `vec-len` (user-callable Vec length accessor) physically lives in
// `cranelisp-primitives::vec` post-FIXME-0180. It is referenced from this
// crate only via that path; no shim here.

/// Vec set — copy path.
///
/// Allocates a new Vec, copies all RETAINED elements from the source (calling
/// `elem_inc_fn` on each copied-over element for RC), and stores `val` at `idx`.
/// Does NOT dec the old element at `idx` — caller handles that.
/// Returns base pointer to the new Vec (rc=1).
///
/// **Does NOT inc the new `val`** (FIXME 0417): the new element's consuming inc
/// (heap-typed Var ⇒ inc; temporary ⇒ transfer) is emitted up-front in codegen
/// by `compile_vec_set`, exactly as `vec_push_copy` leaves the appended `val`
/// to the codegen-side inc. This is the single division of labour for the Vec
/// element-write convention: codegen owns the new-element consuming inc, the
/// runtime owns only the retained-element incs. (Prior to FIXME 0417 this helper
/// inc'd `val` unconditionally and codegen compensated a temporary's over-inc
/// with a dec — two opposite labour splits for one operation; PAIRED-OR-UAF if
/// only one side changes — see FIXME 0296.)
///
/// `elem_inc_fn`: function pointer `(i64) -> i64` for per-element RC inc.
///                Pass 0 (null) for NeverHeap element types.
///
/// JIT name: "vec-set-copy" — exported via export_name so link-mode resolves.
#[unsafe(export_name = "vec-set-copy")]
pub extern "C" fn vec_set_copy(vec: i64, idx: i64, val: i64, elem_inc_fn: i64) -> i64 {
    let src = vec as *const u8;
    unsafe {
        let len = read_len(src);
        let cap = read_cap(src);
        let src_data = read_data_ptr(src);
        #[cfg(debug_assertions)]
        databuf_guard::assert_live(src_data as usize, cap, "vec_set_copy(src)");

        // Allocate new Vec struct + data buffer.
        let new_base = heap_alloc_mod::alloc_with_rc(VEC_PAYLOAD_SIZE);
        let new_data = alloc_data_buffer(cap);

        // Copy all elements. Inc only the RETAINED copied-over elements; the new
        // `val` at `idx` is stored WITHOUT an inc here — its consuming inc is
        // emitted up-front in codegen (FIXME 0417, mirroring vec_push_copy).
        for i in 0..len as usize {
            let elem = *src_data.add(i);
            if i as i64 == idx {
                // Store the new value at the target index. No inc — codegen owns
                // the new-element consuming inc.
                *new_data.add(i) = val;
            } else {
                *new_data.add(i) = elem;
                call_elem_fn(elem_inc_fn, elem);
            }
        }

        write_len(new_base, len);
        write_cap(new_base, cap);
        write_data_ptr(new_base, new_data);

        new_base as i64
    }
}

/// Vec push — copy path.
///
/// Allocates a new Vec with `len + 1` capacity, copies all existing elements
/// (calling `elem_inc_fn` on each), and appends `val`.
/// Returns base pointer to the new Vec (rc=1).
///
/// JIT name: "vec-push-copy" — exported via export_name so link-mode resolves.
#[unsafe(export_name = "vec-push-copy")]
pub extern "C" fn vec_push_copy(vec: i64, val: i64, elem_inc_fn: i64) -> i64 {
    let src = vec as *const u8;
    unsafe {
        let len = read_len(src);
        // Only read in debug builds — the databuf liveness guard below is the
        // sole consumer (release builds compile it out).
        #[cfg(debug_assertions)]
        let cap = read_cap(src);
        let src_data = read_data_ptr(src);
        #[cfg(debug_assertions)]
        databuf_guard::assert_live(src_data as usize, cap, "vec_push_copy(src)");

        let new_cap = len + 1;

        // Allocate new Vec struct + data buffer.
        let new_base = heap_alloc_mod::alloc_with_rc(VEC_PAYLOAD_SIZE);
        let new_data = alloc_data_buffer(new_cap);

        // Copy existing elements, calling inc_fn on each.
        for i in 0..len as usize {
            let elem = *src_data.add(i);
            *new_data.add(i) = elem;
            call_elem_fn(elem_inc_fn, elem);
        }

        // Append the new value.
        *new_data.add(len as usize) = val;

        write_len(new_base, len + 1);
        write_cap(new_base, new_cap);
        write_data_ptr(new_base, new_data);

        new_base as i64
    }
}

/// Vec push — growth path.
///
/// Called when the Vec is the unique owner (rc==1) but the data buffer is full
/// (len >= cap). Reallocates the data buffer with doubled capacity (minimum 4),
/// stores val at `data[len]`, increments len. Returns the same Vec pointer.
///
/// JIT name: "vec-push-grow" — exported via export_name so link-mode resolves.
#[unsafe(export_name = "vec-push-grow")]
pub extern "C" fn vec_push_grow(vec: i64, val: i64) -> i64 {
    let base = vec as *mut u8;
    unsafe {
        let len = read_len(base);
        let old_cap = read_cap(base);
        let old_data = read_data_ptr(base);
        #[cfg(debug_assertions)]
        databuf_guard::assert_live(old_data as usize, old_cap, "vec_push_grow(in)");

        // Double capacity (minimum 4).
        let new_cap = if old_cap == 0 { 4 } else { old_cap * 2 };
        let new_data = alloc_data_buffer(new_cap);

        // Copy existing elements to new buffer.
        if len > 0 && !old_data.is_null() {
            std::ptr::copy_nonoverlapping(old_data, new_data, len as usize);
        }

        // Free old data buffer.
        free_data_buffer(old_data, old_cap, "vec_push_grow(old)");

        // Store new value at data[len].
        *new_data.add(len as usize) = val;

        // Update Vec struct fields.
        write_len(base, len + 1);
        write_cap(base, new_cap);
        write_data_ptr(base, new_data);

        vec
    }
}

/// Vec drop glue.
///
/// Loops through elements `0..len`, calling `elem_dec_fn` on each (if non-null).
/// Frees the data buffer, then frees the Vec struct.
///
/// `elem_dec_fn`: function pointer `(i64) -> i64` for per-element RC dec.
///                Pass 0 (null) for NeverHeap element types.
///
/// JIT name: "runtime/vec_drop" — exported via export_name so link-mode resolves.
#[unsafe(export_name = "runtime/vec_drop")]
pub extern "C" fn vec_drop(vec: i64, elem_dec_fn: i64) {
    let base = vec as *mut u8;
    unsafe {
        let len = read_len(base);
        let cap = read_cap(base);
        let data = read_data_ptr(base);
        #[cfg(debug_assertions)]
        databuf_guard::assert_live(data as usize, cap, "vec_drop(in)");

        // Dec each live element.
        if elem_dec_fn != 0 {
            for i in 0..len as usize {
                let elem = *data.add(i);
                call_elem_fn(elem_dec_fn, elem);
            }
        }

        // Free data buffer.
        free_data_buffer(data, cap, "vec_drop");

        // Free Vec struct.
        heap_alloc_mod::dealloc(base);
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
