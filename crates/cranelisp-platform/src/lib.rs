//! Shared interface crate for the cranelisp platform ABI.
//!
//! Both the cranelisp host binary and every platform DLL depend on this crate.
//! It defines the C-ABI contract types that cross the DLL boundary:
//! struct layouts, constants, wrapper types, and the `declare_platform!` macro.
//!
//! Platform authors work with safe wrapper types (`CLInt`, `CLString`, `CLBool`,
//! `CLFloat`) -- all `unsafe` is encapsulated here. The host uses
//! `manifest_to_descriptors()` to convert C-ABI manifests into safe Rust types.

use std::ops::Deref;
use std::sync::atomic::{AtomicPtr, Ordering};

/// ABI version -- bump on breaking changes to the platform contract.
/// The reimplementation starts fresh at version 1 (the sketch iterated to v3).
pub const ABI_VERSION: u32 = 1;

/// IO task tree tags -- shared between platform DLLs and the host trampoline.
pub const IO_TAG_PURE: i64 = 0;
pub const IO_TAG_EFFECT: i64 = 1;
pub const IO_TAG_BIND: i64 = 2;
/// Parallel IO dispatch: branches run concurrently with resource token serialization.
/// See spec §10.12 (Automatic IO Scheduling).
pub const IO_TAG_PAR: i64 = 3;

/// Byte offset of the resource token within an Effect node payload.
/// Effect layout: [tag i64][thunk_ptr i64][resource_token i64] -- 24 bytes.
pub const IO_EFFECT_RESOURCE_OFFSET: i64 = 16;

/// Scheduling class for a platform function, declared in the platform manifest.
///
/// Re-exported from `cranelisp-types` (Sprint 57 Wave 3 step A, Decision 26).
/// The canonical definition lives at the bottom of the dependency DAG
/// (`cranelisp_types::scheduling::SchedulingClass`) because it must appear
/// both on `PrimitiveKind::PlatformEffect` (a `cranelisp-types` variant
/// field) and in the C-ABI-adjacent surface here. A `cranelisp-types ->
/// cranelisp-platform` edge would invert the DAG and violate Principle 3.
///
/// External consumers (platform DLLs, `declare_platform!` macro users)
/// continue to import `cranelisp_platform::SchedulingClass` unchanged.
pub use cranelisp_types::SchedulingClass;

/// Per Decision 42 / FIXME 0104 — `cranelisp_types::PlatformError` is the
/// platform crate's boundary error type for `manifest_to_descriptors` and
/// any future platform-side helpers. Host re-exports for ergonomics; the
/// canonical definition lives in `cranelisp-types`.
pub use cranelisp_types::PlatformError;
use cranelisp_types::ErrorLocation;

/// Heap header size: `[i64 total_size][i64 rc]` = 16 bytes.
/// The host allocator returns payload pointer = base + HEAP_HEADER_SIZE.
/// The trampoline expects base pointers for IO nodes.
/// Derived from `cranelisp_types::HeapHeader::SIZE` to avoid duplication.
pub const HEAP_HEADER_SIZE: i64 = cranelisp_types::HeapHeader::SIZE as i64;

/// String layout: `[i64 len][u8 bytes...]` at payload pointer.
/// Payload pointer = alloc base + 16 (after size + rc headers).
pub const STRING_HEADER_BYTES: usize = 8;

// -- C-ABI contract types --

/// A single platform function descriptor in the C ABI.
///
/// All fields use raw pointers and lengths for C compatibility.
/// The host converts these into safe Rust types after loading.
#[repr(C)]
pub struct PlatformFn {
    /// Name as seen by cranelisp code (e.g. "print").
    pub name: *const u8,
    pub name_len: usize,
    /// JIT symbol name (e.g. "cranelisp_print").
    pub jit_name: *const u8,
    pub jit_name_len: usize,
    /// Function pointer (extern "C", all i64 params/returns).
    pub ptr: *const u8,
    /// Number of i64 parameters.
    pub param_count: u32,
    /// Type signature as S-expression string (e.g. "(Fn [String] (IO Int))").
    pub type_sig: *const u8,
    pub type_sig_len: usize,
    /// Docstring for the function.
    pub docstring: *const u8,
    pub docstring_len: usize,
    /// Array of parameter name pointers.
    pub param_names: *const *const u8,
    /// Array of parameter name lengths (parallel to param_names).
    pub param_name_lens: *const usize,
    /// Number of parameter names.
    pub param_name_count: usize,
    /// SchedulingClass discriminant: 0=Sequential, 1=Commutative, 2=ResourceSerial.
    pub scheduling_class: u32,
}

// Safety: PlatformFn is a C-ABI struct with raw pointers; it is only
// constructed and accessed within unsafe blocks during DLL loading.
// The pointers must remain valid for the lifetime of the manifest.
unsafe impl Send for PlatformFn {}
unsafe impl Sync for PlatformFn {}

/// Host callbacks provided to the platform at init time.
///
/// The platform stores these for later use (e.g. `read-line` needs
/// the host allocator to return heap-allocated strings).
#[repr(C)]
pub struct HostCallbacks {
    /// Allocate `size` bytes, returns payload pointer (base + 16).
    pub alloc: extern "C" fn(i64) -> i64,
}

/// Platform manifest returned by the DLL's entry point.
///
/// Contains the platform name, version, and array of function descriptors.
/// The host validates `abi_version` and extracts descriptors at load time.
#[repr(C)]
pub struct PlatformManifest {
    /// Must match `cranelisp_platform::ABI_VERSION`.
    pub abi_version: u32,
    /// Platform name (e.g. "stdio").
    pub name: *const u8,
    pub name_len: usize,
    /// Platform version string.
    pub version: *const u8,
    pub version_len: usize,
    /// Array of function descriptors.
    pub functions: *const PlatformFn,
    pub function_count: usize,
}

// -- Safe wrapper types --
//
// These `#[repr(transparent)]` wrappers over i64 provide type-safe
// conversions for platform authors. All `unsafe` is encapsulated here.

/// A cranelisp integer value (i64 passthrough).
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct CLInt(i64);

/// A cranelisp string value (pointer to `[i64 len][u8 bytes...]`).
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct CLString(i64);

/// A cranelisp boolean value (0 = false, 1 = true).
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct CLBool(i64);

/// A cranelisp float value (IEEE 754 f64 bitcast to i64).
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct CLFloat(i64);

// -- CLInt conversions --

impl From<i64> for CLInt {
    fn from(v: i64) -> Self {
        CLInt(v)
    }
}

impl From<CLInt> for i64 {
    fn from(v: CLInt) -> Self {
        v.0
    }
}

// -- CLBool conversions --

impl From<bool> for CLBool {
    fn from(v: bool) -> Self {
        CLBool(v as i64)
    }
}

impl From<CLBool> for bool {
    fn from(v: CLBool) -> Self {
        v.0 != 0
    }
}

// -- CLFloat conversions --

impl From<f64> for CLFloat {
    fn from(v: f64) -> Self {
        CLFloat(i64::from_ne_bytes(v.to_ne_bytes()))
    }
}

impl From<CLFloat> for f64 {
    fn from(v: CLFloat) -> Self {
        f64::from_ne_bytes(v.0.to_ne_bytes())
    }
}

// -- CLType trait --

/// Marker trait for cranelisp value types that can be IO-wrapped.
/// Only CL* types implement this -- prevents raw i64 from being lifted.
pub trait CLType: Copy {
    fn to_raw(self) -> i64;
}

impl CLType for CLInt {
    fn to_raw(self) -> i64 {
        self.0
    }
}
impl CLType for CLString {
    fn to_raw(self) -> i64 {
        self.0
    }
}
impl CLType for CLBool {
    fn to_raw(self) -> i64 {
        self.0
    }
}
impl CLType for CLFloat {
    fn to_raw(self) -> i64 {
        self.0
    }
}

// -- CLIO -- IO-wrapped return value --

/// IO-wrapped return value. Allocates IO nodes on the host heap.
/// Generic over CL type for type safety -- only CLType implementors accepted.
#[repr(transparent)]
#[derive(Debug)]
pub struct CLIO<CL: CLType>(i64, std::marker::PhantomData<CL>);

impl<CL: CLType> CLIO<CL> {
    /// Wrap a completed value in IO by allocating a Pure node on the heap.
    ///
    /// Returns a base pointer (not payload pointer) because the IO trampoline
    /// reads fields at base + HEAP_HEADER_SIZE offsets.
    pub fn pure(val: CL) -> Self {
        let alloc = get_global_alloc();
        let payload = alloc(16); // 2 x i64: tag + value
        // SAFETY: `payload` is a valid pointer returned by the host allocator for
        // at least 16 bytes. We write two i64 fields (tag at offset 0, value at
        // offset 8) within that allocation. The allocator guarantees 8-byte alignment.
        unsafe {
            *(payload as *mut i64) = IO_TAG_PURE;
            *((payload + 8) as *mut i64) = val.to_raw();
        }
        // Return base pointer (payload - header) for trampoline compatibility.
        CLIO(payload - HEAP_HEADER_SIZE, std::marker::PhantomData)
    }

    /// Wrap a Rust closure as a deferred IO Effect node with no resource token.
    ///
    /// The closure is double-boxed to produce a thin pointer (fits in one i64).
    /// The trampoline unboxes and calls it when forcing the IO tree.
    /// Resource token is set to 0 (unrestricted).
    pub fn effect(f: impl FnOnce() -> CL + 'static) -> Self {
        Self::effect_on_resource(0, f)
    }

    /// Wrap a Rust closure as a deferred IO Effect node with a resource token.
    ///
    /// The `token` identifies a shared resource. Two Effect nodes with the same
    /// non-zero token in a Par group will be serialized by the trampoline.
    pub fn effect_on_resource(token: i64, f: impl FnOnce() -> CL + 'static) -> Self {
        let thunk: Box<Box<dyn FnOnce() -> i64>> =
            Box::new(Box::new(move || f().to_raw()));
        let thunk_ptr = Box::into_raw(thunk) as i64;

        let alloc = get_global_alloc();
        let payload = alloc(24); // 3 x i64: tag + thunk_ptr + resource_token
        // SAFETY: `payload` is a valid pointer returned by the host allocator for
        // at least 24 bytes. We write three i64 fields (tag, thunk_ptr, token) at
        // offsets 0, 8, 16 within that allocation. `thunk_ptr` is a valid pointer
        // from `Box::into_raw` and will be consumed exactly once by `call_effect_thunk`.
        unsafe {
            *(payload as *mut i64) = IO_TAG_EFFECT;
            *((payload + 8) as *mut i64) = thunk_ptr;
            *((payload + 16) as *mut i64) = token;
        }
        // Return base pointer (payload - header) for trampoline compatibility.
        CLIO(payload - HEAP_HEADER_SIZE, std::marker::PhantomData)
    }
}

/// Call a double-boxed thunk pointer (created by `CLIO::effect()`).
///
/// This **consumes** the thunk -- it is valid to call exactly once.
/// The trampoline must not force the same Effect node twice.
///
/// # Safety
/// `thunk_ptr` must be a valid pointer from `Box::into_raw(Box<Box<dyn FnOnce() -> i64>>)`.
pub unsafe fn call_effect_thunk(thunk_ptr: i64) -> i64 {
    let thunk: Box<Box<dyn FnOnce() -> i64>> =
        unsafe { Box::from_raw(thunk_ptr as *mut Box<dyn FnOnce() -> i64>) };
    (*thunk)()
}

impl<CL: CLType> From<CLIO<CL>> for i64 {
    fn from(v: CLIO<CL>) -> Self {
        v.0
    }
}

// Explicit From impls for lifting natural types through CL* into CLIO:
impl From<i64> for CLIO<CLInt> {
    fn from(val: i64) -> Self {
        CLIO::pure(CLInt::from(val))
    }
}
impl From<String> for CLIO<CLString> {
    fn from(val: String) -> Self {
        CLIO::pure(CLString::from(val))
    }
}
impl From<bool> for CLIO<CLBool> {
    fn from(val: bool) -> Self {
        CLIO::pure(CLBool::from(val))
    }
}
impl From<f64> for CLIO<CLFloat> {
    fn from(val: f64) -> Self {
        CLIO::pure(CLFloat::from(val))
    }
}
// CL* -> CLIO directly:
impl From<CLInt> for CLIO<CLInt> {
    fn from(val: CLInt) -> Self {
        CLIO::pure(val)
    }
}
impl From<CLString> for CLIO<CLString> {
    fn from(val: CLString) -> Self {
        CLIO::pure(val)
    }
}
impl From<CLBool> for CLIO<CLBool> {
    fn from(val: CLBool) -> Self {
        CLIO::pure(val)
    }
}
impl From<CLFloat> for CLIO<CLFloat> {
    fn from(val: CLFloat) -> Self {
        CLIO::pure(val)
    }
}

// -- CLString conversions --

/// Global allocator function pointer, set by `HostContext::init()`.
/// Each DLL gets its own copy of this static (separate compilation unit).
static GLOBAL_ALLOC: AtomicPtr<()> = AtomicPtr::new(std::ptr::null_mut());

/// Get the global allocator function. Panics if not initialized.
fn get_global_alloc() -> extern "C" fn(i64) -> i64 {
    let ptr = GLOBAL_ALLOC.load(Ordering::SeqCst);
    assert!(
        !ptr.is_null(),
        "platform not initialized: HostContext::init() not called"
    );
    // SAFETY: The pointer was stored by `HostContext::init()` which cast a valid
    // `extern "C" fn(i64) -> i64` to `*mut ()`. We transmute it back to the
    // original function pointer type. The assert above ensures it is non-null.
    unsafe { std::mem::transmute(ptr) }
}

impl CLString {
    /// View the string contents as a `&str`.
    ///
    /// CLString stores a **base pointer** (matching the compiler's convention).
    /// The string payload starts at base + HEAP_HEADER_SIZE:
    /// `[alloc_size(8) | rc(8) | len(8) | bytes...]`
    pub fn as_str(&self) -> &str {
        // SAFETY: `self.0` is a base pointer to a heap allocation with layout
        // `[alloc_size: i64][rc: i64][len: i64][bytes: u8...]`. Adding
        // HEAP_HEADER_SIZE yields the payload pointer. The length field at the
        // payload start was written by `CLString::from(&str)` or the compiler,
        // and the subsequent `len` bytes are valid UTF-8 (guaranteed by
        // construction — only Rust `&str` data is ever stored).
        unsafe {
            let payload = self.0 + HEAP_HEADER_SIZE;
            let len = *(payload as *const i64) as usize;
            let bytes = std::slice::from_raw_parts(
                (payload + STRING_HEADER_BYTES as i64) as *const u8,
                len,
            );
            std::str::from_utf8_unchecked(bytes)
        }
    }
}

impl From<CLString> for String {
    fn from(v: CLString) -> Self {
        v.as_str().to_string()
    }
}

impl From<String> for CLString {
    fn from(s: String) -> Self {
        CLString::from(s.as_str())
    }
}

impl From<&str> for CLString {
    fn from(s: &str) -> Self {
        let bytes = s.as_bytes();
        let size = (STRING_HEADER_BYTES + bytes.len()) as i64;
        let alloc = get_global_alloc();
        let payload = alloc(size);
        // SAFETY: `payload` is a valid pointer returned by the host allocator for
        // `STRING_HEADER_BYTES + bytes.len()` bytes. We write the length as an i64
        // at offset 0, then copy the UTF-8 bytes at offset STRING_HEADER_BYTES.
        // `bytes` is a valid slice from a Rust `&str`, so the copy source is sound.
        unsafe {
            *(payload as *mut i64) = bytes.len() as i64;
            std::ptr::copy_nonoverlapping(
                bytes.as_ptr(),
                (payload + STRING_HEADER_BYTES as i64) as *mut u8,
                bytes.len(),
            );
        }
        // Store base pointer (payload - header) to match compiler convention.
        CLString(payload - HEAP_HEADER_SIZE)
    }
}

// -- CLOwned -- RAII RC wrapper for heap CL* types --

/// Trait for CL types that are heap-allocated with RC headers.
/// Layout: `[total_size: i64][rc: i64][payload...]`.
/// All CL* types store **base pointers** (matching the compiler's convention).
pub trait CLHeap: CLType + Copy {
    /// Get the raw base pointer.
    fn raw_ptr(&self) -> i64;

    /// Atomically increment the reference count.
    ///
    /// Uses `Ordering::SeqCst` to match the backend's Cranelift `atomic_rmw`
    /// semantics (arch decision 13). `Relaxed` is unsound because it allows
    /// reordering of the increment relative to field reads.
    fn inc_rc(&self) {
        let base = self.raw_ptr();
        let rc_addr = (base + 8) as *mut i64; // rc at base+8
        // SAFETY: `base` is a valid heap allocation base pointer with layout
        // `[alloc_size: i64][rc: i64][payload...]`. The RC field at base+8 is
        // an i64 with 8-byte alignment, valid for atomic access. The allocation
        // is live (RC >= 1) so the pointer is not dangling.
        unsafe {
            use std::sync::atomic::AtomicI64;
            let atomic = &*(rc_addr as *const AtomicI64);
            atomic.fetch_add(1, Ordering::SeqCst);
        }
    }

    /// Atomically decrement the reference count.
    /// If the old RC was 1 (now 0), frees the allocation.
    ///
    /// Uses `Ordering::SeqCst` -- `Relaxed` for dec is unsound because it
    /// allows the dec to be reordered before reads of object fields,
    /// potentially reading freed memory.
    fn dec_rc(&self) {
        let base = self.raw_ptr();
        let rc_addr = (base + 8) as *mut i64; // rc at base+8
        // SAFETY: Same invariants as `inc_rc` — `base` is a valid live heap
        // allocation, and RC at base+8 is an aligned i64 suitable for atomic ops.
        let old_rc = unsafe {
            use std::sync::atomic::AtomicI64;
            let atomic = &*(rc_addr as *const AtomicI64);
            atomic.fetch_sub(1, Ordering::SeqCst)
        };
        if old_rc == 1 {
            // RC reached 0 -- free the allocation
            // SAFETY: `base` points to the start of a global-allocator allocation.
            // `alloc_size` at base+0 records the total allocation size that was
            // used in the original `alloc` call. Alignment is 8 (matching the
            // host allocator). No other references exist (RC was 1, now 0).
            let total_size = unsafe { *(base as *const i64) } as usize;
            unsafe {
                let layout = std::alloc::Layout::from_size_align_unchecked(total_size, 8);
                std::alloc::dealloc(base as *mut u8, layout);
            }
        }
    }

    /// Create an owned handle that increments RC and decrements on drop.
    fn own(&self) -> CLOwned<Self> {
        CLOwned::new(*self)
    }

    /// Consuming-convention version of `own()` (Decision 24): take ownership
    /// of the caller's transferred reference and wrap it in a `CLOwned`
    /// without incrementing RC. The returned `CLOwned` will `dec_rc` on drop,
    /// releasing the caller's transferred reference. Net effect per call:
    /// caller +1 (transfer) → CLOwned drop -1 = balanced.
    ///
    /// Use this in platform externs that capture a heap-typed parameter into
    /// an Effect-thunk closure instead of `own()`. `own()` is still correct
    /// when the caller did NOT transfer ownership (e.g. when the extern
    /// takes a borrow / the ref is reused after the extern returns).
    ///
    /// See `design/backend/ring2-rc.md` §10.4 Form B for the rationale.
    fn into_owned_consuming(self) -> CLOwned<Self> {
        // No inc — the caller's transferred ref becomes the CLOwned's ref.
        // Construct the wrapper directly, bypassing `CLOwned::new`'s inc.
        CLOwned { inner: self }
    }
}

impl CLHeap for CLString {
    fn raw_ptr(&self) -> i64 {
        self.0 // base pointer
    }
}

/// RAII wrapper for heap-allocated CL* values.
/// Increments RC on creation, decrements on drop.
pub struct CLOwned<T: CLHeap> {
    inner: T,
}

impl<T: CLHeap> CLOwned<T> {
    /// Create a new owned handle, incrementing the reference count.
    pub fn new(val: T) -> Self {
        val.inc_rc();
        CLOwned { inner: val }
    }
}

impl<T: CLHeap> Drop for CLOwned<T> {
    fn drop(&mut self) {
        self.inner.dec_rc();
    }
}

impl<T: CLHeap> Deref for CLOwned<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.inner
    }
}

// -- HostContext --

/// Initialization handle for platform DLLs.
///
/// Exists solely to receive and store host callbacks at manifest time.
/// Platform authors declare a static instance; the `declare_platform!`
/// macro calls `init()` automatically.
pub struct HostContext {
    callbacks: AtomicPtr<HostCallbacks>,
}

impl Default for HostContext {
    fn default() -> Self {
        Self::new()
    }
}

impl HostContext {
    /// Create a new uninitialized context.
    pub const fn new() -> Self {
        HostContext {
            callbacks: AtomicPtr::new(std::ptr::null_mut()),
        }
    }

    /// Initialize from host callbacks.
    ///
    /// Stores a leaked copy of the callbacks and sets the crate-global
    /// allocator used by `From<String> for CLString`.
    ///
    /// # Safety
    /// `callbacks` must point to a valid `HostCallbacks` struct.
    pub unsafe fn init(&self, callbacks: *const HostCallbacks) {
        let cb_copy = unsafe { Box::new(std::ptr::read(callbacks)) };
        let raw = Box::into_raw(cb_copy);
        self.callbacks.store(raw, Ordering::SeqCst);

        // Set the global allocator for CLString conversions.
        let alloc_fn = unsafe { (*raw).alloc };
        GLOBAL_ALLOC.store(alloc_fn as *mut (), Ordering::SeqCst);
    }
}

// -- Owned descriptors (safe Rust types) --

/// Safe Rust descriptor for a platform function, converted from C-ABI.
///
/// Used by the host after loading a DLL manifest.
#[non_exhaustive]
pub struct OwnedPlatformFnDescriptor {
    pub name: String,
    pub jit_name: String,
    pub ptr: *const u8,
    pub param_count: usize,
    pub type_sig: String,
    pub docstring: String,
    pub param_names: Vec<String>,
    pub scheduling_class: SchedulingClass,
}

/// Convert a C-ABI manifest into safe Rust descriptors.
///
/// # Safety
/// All pointers in the manifest must be valid and point to UTF-8 data.
///
/// # Errors
/// UTF-8 validation failures construct `PlatformError::LoadFailed` with
/// `ErrorLocation::unknown()` (the caller — `int::load_platform_dll` —
/// rewrites `dll` and `location` at the call site). Per Decision 42 /
/// FIXME 0104.
pub unsafe fn manifest_to_descriptors(
    manifest: &PlatformManifest,
) -> Result<(String, String, Vec<OwnedPlatformFnDescriptor>), PlatformError> {
    let utf8_err = |what: &str, e: std::str::Utf8Error| PlatformError::LoadFailed {
        dll: std::path::PathBuf::new(),
        cause: format!("invalid UTF-8 in {what}: {e}"),
        location: ErrorLocation::unknown(),
    };

    let name = unsafe {
        let bytes = std::slice::from_raw_parts(manifest.name, manifest.name_len);
        std::str::from_utf8(bytes)
            .map_err(|e| utf8_err("platform name", e))?
            .to_string()
    };
    let version = unsafe {
        let bytes = std::slice::from_raw_parts(manifest.version, manifest.version_len);
        std::str::from_utf8(bytes)
            .map_err(|e| utf8_err("platform version", e))?
            .to_string()
    };

    let functions =
        unsafe { std::slice::from_raw_parts(manifest.functions, manifest.function_count) };

    let mut descriptors = Vec::with_capacity(manifest.function_count);
    for func in functions {
        let func_name = unsafe {
            let bytes = std::slice::from_raw_parts(func.name, func.name_len);
            std::str::from_utf8(bytes)
                .map_err(|e| utf8_err("function name", e))?
                .to_string()
        };
        let func_jit_name = unsafe {
            let bytes = std::slice::from_raw_parts(func.jit_name, func.jit_name_len);
            std::str::from_utf8(bytes)
                .map_err(|e| utf8_err("function jit_name", e))?
                .to_string()
        };
        let func_type_sig = unsafe {
            let bytes = std::slice::from_raw_parts(func.type_sig, func.type_sig_len);
            std::str::from_utf8(bytes)
                .map_err(|e| utf8_err("function type_sig", e))?
                .to_string()
        };
        let func_docstring = unsafe {
            let bytes = std::slice::from_raw_parts(func.docstring, func.docstring_len);
            std::str::from_utf8(bytes)
                .map_err(|e| utf8_err("function docstring", e))?
                .to_string()
        };

        let mut param_names = Vec::with_capacity(func.param_name_count);
        if func.param_name_count > 0 {
            let name_ptrs = unsafe {
                std::slice::from_raw_parts(func.param_names, func.param_name_count)
            };
            let name_lens = unsafe {
                std::slice::from_raw_parts(func.param_name_lens, func.param_name_count)
            };
            for i in 0..func.param_name_count {
                let pname = unsafe {
                    let bytes = std::slice::from_raw_parts(name_ptrs[i], name_lens[i]);
                    std::str::from_utf8(bytes)
                        .map_err(|e| utf8_err(&format!("param name {i}"), e))?
                        .to_string()
                };
                param_names.push(pname);
            }
        }

        descriptors.push(OwnedPlatformFnDescriptor {
            name: func_name,
            jit_name: func_jit_name,
            ptr: func.ptr,
            param_count: func.param_count as usize,
            type_sig: func_type_sig,
            docstring: func_docstring,
            param_names,
            scheduling_class: SchedulingClass::from_u32(func.scheduling_class),
        });
    }

    Ok((name, version, descriptors))
}

// -- declare_platform! macro --

/// Derive the JIT symbol name from a cranelisp function name.
///
/// Prepends `cranelisp_` and replaces `-` with `_`.
/// E.g. `"read-line"` -> `"cranelisp_read_line"`.
pub fn derive_jit_name(cl_name: &str) -> String {
    format!("cranelisp_{}", cl_name.replace('-', "_"))
}

/// Declare a platform DLL with metadata and function registrations.
///
/// Platform functions are normal `extern "C"` Rust functions using `CL*`
/// wrapper types -- they are defined outside the macro. The macro handles
/// only manifest generation and host callback initialization.
///
/// # Example
///
/// ```ignore
/// use cranelisp_platform::*;
///
/// static HOST: HostContext = HostContext::new();
///
/// pub extern "C" fn print_string(s: CLString) -> CLIO<CLInt> {
///     let owned = s.own();
///     CLIO::effect(move || { println!("{}", owned.as_str()); CLInt::from(0i64) })
/// }
///
/// declare_platform! {
///     name: "stdio",
///     version: "0.1.0",
///     host: HOST,
///     functions: [
///         print_string {
///             cl_name: "print",
///             sig: "(Fn [String] (IO Int))",
///             doc: "Print a string followed by a newline",
///             params: [s],
///             scheduling: SchedulingClass::Sequential,
///         },
///     ]
/// }
/// ```
#[macro_export]
macro_rules! declare_platform {
    (
        name: $platform_name:literal,
        version: $platform_version:literal,
        host: $host:ident,
        functions: [
            $(
                $fn_ident:ident {
                    cl_name: $cl_name:literal,
                    sig: $sig:literal,
                    doc: $doc:literal,
                    params: [$($param:ident),* $(,)?],
                    scheduling: $scheduling:expr,
                }
            ),* $(,)?
        ]
    ) => {
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn cranelisp_platform_manifest(
            callbacks: *const $crate::HostCallbacks,
        ) -> $crate::PlatformManifest {
            // Initialize the host context (stores callbacks, sets global alloc).
            unsafe { $host.init(callbacks); }

            // Build function descriptors.
            // Phase 1: Capture each function pointer, param info, and scheduling class
            // before shadowing the identifier.
            $(
                #[allow(unused)]
                let $fn_ident = {
                    let fn_ptr = $fn_ident as *const u8;
                    let param_names_vec: Vec<&'static [u8]> = vec![
                        $( stringify!($param).as_bytes(), )*
                    ];
                    let param_count = param_names_vec.len();
                    let (name_ptrs_ptr, name_lens_ptr) = if param_count > 0 {
                        let name_ptrs: Vec<*const u8> =
                            param_names_vec.iter().map(|b| b.as_ptr()).collect();
                        let name_lens: Vec<usize> =
                            param_names_vec.iter().map(|b| b.len()).collect();
                        let ptrs = Box::leak(name_ptrs.into_boxed_slice());
                        let lens = Box::leak(name_lens.into_boxed_slice());
                        (ptrs.as_ptr(), lens.as_ptr())
                    } else {
                        (std::ptr::null::<*const u8>(), std::ptr::null::<usize>())
                    };
                    let scheduling_class = ($scheduling) as u32;
                    (fn_ptr, name_ptrs_ptr, name_lens_ptr, param_count, scheduling_class)
                };
            )*

            // Phase 2: Derive jit_names at runtime and leak for 'static.
            $(
                let $fn_ident = {
                    let jit_name = $crate::derive_jit_name($cl_name);
                    let jit_bytes: &'static [u8] =
                        Box::leak(jit_name.into_bytes().into_boxed_slice());
                    ($fn_ident, jit_bytes)
                };
            )*

            // Phase 3: Build PlatformFn descriptors array.
            let functions: &'static [$crate::PlatformFn] = Box::leak(vec![
                $(
                    $crate::PlatformFn {
                        name: $cl_name.as_ptr(),
                        name_len: $cl_name.len(),
                        jit_name: $fn_ident.1.as_ptr(),
                        jit_name_len: $fn_ident.1.len(),
                        ptr: ($fn_ident.0).0,
                        param_count: ($fn_ident.0).3 as u32,
                        type_sig: $sig.as_ptr(),
                        type_sig_len: $sig.len(),
                        docstring: $doc.as_ptr(),
                        docstring_len: $doc.len(),
                        param_names: ($fn_ident.0).1,
                        param_name_lens: ($fn_ident.0).2,
                        param_name_count: ($fn_ident.0).3,
                        scheduling_class: ($fn_ident.0).4,
                    },
                )*
            ].into_boxed_slice());

            $crate::PlatformManifest {
                abi_version: $crate::ABI_VERSION,
                name: $platform_name.as_ptr(),
                name_len: $platform_name.len(),
                version: $platform_version.as_ptr(),
                version_len: $platform_version.len(),
                functions: functions.as_ptr(),
                function_count: functions.len(),
            }
        }
    };
}

// ---------------------------------------------------------------------
// Decision 24 — consuming capture-RC protocol (Sprint 59 Workstream C-i).
//
// These tests verify that `into_owned_consuming` preserves the caller's
// transferred-reference contract: one caller-transfer in, one CLOwned::drop
// dec out, net zero. `own()` vs `into_owned_consuming()` differ by whether
// they inc for the capture (former) or take the caller's transferred ref
// directly (latter). Regression guard for `design/backend/ring2-rc.md` §10.4.
// ---------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::Span;
    use std::sync::atomic::AtomicI64;

    // ---------------------------------------------------------------------
    // PlatformError adoption — Decision 42 / FIXME 0104.
    //
    // These tests pin the platform crate's public error surface to the
    // shape facades/platform.md §"Errors" specifies: each variant carries
    // an `ErrorLocation`; `manifest_to_descriptors` returns
    // `Result<…, PlatformError>` with `ErrorLocation::unknown()` at the
    // construction site (callers — `int::load_platform_dll` — rewrite the
    // location with the `(platform "name")` form's span before surfacing).
    // ---------------------------------------------------------------------

    // spec: design/arch/facades/platform.md §"Errors" — `LoadFailed`
    // carries `dll`, `cause`, and `location`. Re-exported `PlatformError`
    // must construct + display this variant.
    #[test]
    fn platform_error_load_failed_constructs_and_displays() {
        let err = PlatformError::LoadFailed {
            dll: std::path::PathBuf::from("nonexistent.dylib"),
            cause: "dlopen returned NULL".to_string(),
            location: ErrorLocation::from_span(Span::new(10, 35)),
        };
        let displayed = format!("{err}");
        assert!(
            displayed.contains("nonexistent.dylib"),
            "Display must surface the DLL path; got: {displayed}"
        );
        assert!(
            displayed.contains("dlopen returned NULL"),
            "Display must surface the underlying cause; got: {displayed}"
        );
        // Location accessor works.
        assert_eq!(err.location().span, Span::new(10, 35));
    }

    // spec: design/arch/facades/platform.md §"Errors" — `ManifestNotFound`
    // carries `dll` and `location`.
    #[test]
    fn platform_error_manifest_not_found_constructs_and_displays() {
        let err = PlatformError::ManifestNotFound {
            dll: std::path::PathBuf::from("stale.dylib"),
            location: ErrorLocation::from_span(Span::new(1, 9)),
        };
        let displayed = format!("{err}");
        assert!(
            displayed.contains("stale.dylib"),
            "Display must surface the DLL path; got: {displayed}"
        );
        assert!(
            displayed.contains("manifest"),
            "Display must mention manifest; got: {displayed}"
        );
        assert_eq!(err.location().span, Span::new(1, 9));
    }

    // spec: design/arch/facades/platform.md §"Errors" —
    // `AbiVersionMismatch` carries `dll`, `expected`, `found`, `location`.
    #[test]
    fn platform_error_abi_version_mismatch_constructs_and_displays() {
        let err = PlatformError::AbiVersionMismatch {
            dll: std::path::PathBuf::from("old.dylib"),
            expected: ABI_VERSION,
            found: 99,
            location: ErrorLocation::from_span(Span::new(20, 30)),
        };
        let displayed = format!("{err}");
        assert!(
            displayed.contains("old.dylib"),
            "Display must surface the DLL path; got: {displayed}"
        );
        // Both expected + found values must surface.
        assert!(
            displayed.contains(&ABI_VERSION.to_string()),
            "Display must surface the expected ABI; got: {displayed}"
        );
        assert!(
            displayed.contains("99"),
            "Display must surface the found ABI; got: {displayed}"
        );
        assert_eq!(err.location().span, Span::new(20, 30));
    }

    // spec: design/arch/facades/platform.md §"Errors" — `DispatchError`
    // carries `fn_name`, `cause`, `location`.
    #[test]
    fn platform_error_dispatch_error_carries_fn_name() {
        use cranelisp_types::Symbol;
        let err = PlatformError::DispatchError {
            fn_name: Symbol::from("read-line"),
            cause: "null fn pointer".to_string(),
            location: ErrorLocation::from_span(Span::new(100, 120)),
        };
        let displayed = format!("{err}");
        assert!(
            displayed.contains("read-line"),
            "Display must surface the fn name; got: {displayed}"
        );
        assert!(
            displayed.contains("null fn pointer"),
            "Display must surface the cause; got: {displayed}"
        );
        assert_eq!(err.location().span, Span::new(100, 120));
    }

    // spec: design/arch/facades/platform.md §"Errors" — DLL-author /
    // int code constructs `PlatformError` and wraps via `CranelispError`.
    // The `From<PlatformError> for CranelispError` blanket conversion
    // must succeed and preserve the location.
    #[test]
    fn platform_error_into_cranelisp_error_preserves_location() {
        use cranelisp_types::CranelispError;
        let err = PlatformError::LoadFailed {
            dll: std::path::PathBuf::from("missing.dylib"),
            cause: "no such file".to_string(),
            location: ErrorLocation::from_span(Span::new(7, 42)),
        };
        let wrapped: CranelispError = err.into();
        assert_eq!(wrapped.span(), Span::new(7, 42));
        // Through `CranelispError::Display`, the platform inner displays.
        let displayed = format!("{wrapped}");
        assert!(
            displayed.contains("missing.dylib"),
            "Display via CranelispError::Platform must surface inner; got: {displayed}"
        );
    }

    // spec: design/arch/facades/platform.md §"Errors" + FIXME 0104 Phase 2
    // — UTF-8 validation failures in `manifest_to_descriptors` construct
    // `PlatformError::LoadFailed` with `ErrorLocation::unknown()`; the
    // caller rewrites with the form's span before surfacing. This test
    // confirms the construction-side behaviour.
    #[test]
    fn manifest_to_descriptors_utf8_failure_returns_load_failed_with_unknown_location() {
        // Build a manifest whose name field is non-UTF-8 (a lone 0xFF byte).
        // Use a static lifetime backing store so the test exercise is sound:
        // the `&PlatformManifest` we pass borrows from `manifest_storage`
        // which lives the full test scope.
        let bad_name: &[u8] = &[0xFFu8];
        let version: &[u8] = b"0.1.0";
        let manifest = PlatformManifest {
            abi_version: ABI_VERSION,
            name: bad_name.as_ptr(),
            name_len: bad_name.len(),
            version: version.as_ptr(),
            version_len: version.len(),
            functions: std::ptr::null(),
            function_count: 0,
        };

        // SAFETY: pointers above point at the local slices that outlive the
        // call (`manifest_to_descriptors` is unsafe; we honour its contract
        // here by ensuring the pointers are valid and the lengths correct).
        let result = unsafe { manifest_to_descriptors(&manifest) };

        match result {
            Err(PlatformError::LoadFailed { cause, location, dll }) => {
                assert!(
                    cause.contains("UTF-8") || cause.contains("invalid"),
                    "cause must mention UTF-8 / invalid; got: {cause}"
                );
                // platform-side construction uses `ErrorLocation::unknown()`
                // → span is synthetic; int rewrites with the form's span.
                assert_eq!(
                    location.span,
                    Span::SYNTHETIC,
                    "platform crate constructs with unknown location; int rewrites at call site"
                );
                assert_eq!(
                    dll,
                    std::path::PathBuf::new(),
                    "platform crate has no DLL path on hand; int fills it in"
                );
            }
            Err(e) => panic!("expected LoadFailed, got different PlatformError: {e}"),
            Ok(_) => panic!("expected LoadFailed, got Ok"),
        }
    }


    // Allocate a mock heap-layout `[alloc_size(8) | rc(8) | payload(>=0)]` with
    // initial rc=1. Returns the base pointer. The payload is zero-filled;
    // the test doesn't care about contents — only the RC field.
    fn mock_heap_alloc(payload_size: usize) -> i64 {
        let total_size = HEAP_HEADER_SIZE as usize + payload_size;
        unsafe {
            let layout = std::alloc::Layout::from_size_align_unchecked(total_size, 8);
            let ptr = std::alloc::alloc_zeroed(layout);
            *(ptr as *mut i64) = total_size as i64;
            *((ptr as *mut i64).add(1)) = 1; // rc = 1
            ptr as i64
        }
    }

    // Read the current RC from a mock allocation.
    fn read_rc(base: i64) -> i64 {
        unsafe {
            let rc_addr = (base + 8) as *const AtomicI64;
            (*rc_addr).load(Ordering::SeqCst)
        }
    }

    // spec: design/backend/ring2-rc.md §10.4 — `into_owned_consuming` must NOT
    // inc RC on wrap (it takes the caller's transferred ref as-is) and MUST
    // dec on drop — so the net RC change is exactly -1 over the wrap+drop
    // pair, symmetric with the caller's +1 transfer.
    #[test]
    fn into_owned_consuming_does_not_inc_on_wrap() {
        let base = mock_heap_alloc(0);
        let s = CLString(base);
        assert_eq!(read_rc(base), 1, "starting rc = 1 (caller's transferred ref)");

        {
            let _owned = s.into_owned_consuming();
            assert_eq!(
                read_rc(base),
                1,
                "into_owned_consuming must NOT inc: still rc=1 after wrap"
            );
        }
        // After _owned drops, CLOwned::drop calls dec_rc. rc was 1, goes to 0,
        // so the allocation is freed. Cannot read_rc here (use-after-free).
    }

    // spec: design/backend/ring2-rc.md §10.4 — contrast with `own()`: `own()`
    // inc's on wrap, so one extra inc is needed by the caller when the
    // caller does NOT transfer ownership. This test locks in the behavioural
    // difference between the two wrappers so regressions are caught.
    #[test]
    fn own_vs_into_owned_consuming_rc_semantics_differ() {
        // own() path: wraps with inc, drops with dec — net zero, original ref survives.
        let base_a = mock_heap_alloc(0);
        let s_a = CLString(base_a);
        assert_eq!(read_rc(base_a), 1);

        {
            let _owned = s_a.own();
            assert_eq!(read_rc(base_a), 2, "own() inc's on wrap: rc=2");
        }
        assert_eq!(read_rc(base_a), 1, "own() dec's on drop: back to rc=1");
        // Manually free s_a (simulates caller's post-return dec of its own ref).
        unsafe {
            let total_size = *(base_a as *const i64) as usize;
            let layout = std::alloc::Layout::from_size_align_unchecked(total_size, 8);
            std::alloc::dealloc(base_a as *mut u8, layout);
        }

        // into_owned_consuming path: no inc on wrap, dec on drop — the original
        // ref itself is consumed and freed. Contrast verified above.
    }

    // spec: design/backend/ring2-rc.md §10.4 — the capture-Effect pattern used
    // by platform externs (print, capture_print): caller transfers one ref,
    // extern wraps via `into_owned_consuming`, closure holds `CLOwned`,
    // deferred thunk-drop dec's once. Net allocator operations: 1 alloc
    // (caller), 1 dealloc (CLOwned drop when closure drops).
    #[test]
    fn decision24_capture_effect_pattern_balanced() {
        // Simulate the caller's alloc + transfer. RC starts at 1 (caller's
        // single ref); caller immediately transfers ownership to the extern
        // (no further inc — the caller's ref becomes the extern's parameter).
        let base = mock_heap_alloc(0);
        let s = CLString(base);
        assert_eq!(read_rc(base), 1);

        // Simulate the extern: wrap via `into_owned_consuming`, capture into
        // a Rust closure (as `print_string` does via `CLIO::effect`).
        let owned = s.into_owned_consuming();
        assert_eq!(
            read_rc(base),
            1,
            "wrap must not inc — the captured ref IS the caller's transferred ref"
        );

        // The closure keeps the CLOwned alive. We inspect RC through the
        // closure's lifetime, then drop the closure to trigger CLOwned::drop.
        let boxed: Box<dyn FnOnce() -> i64> = Box::new(move || {
            // While the closure is live, RC stays at 1.
            read_rc(owned.raw_ptr())
        });

        let rc_during_call = boxed();
        assert_eq!(rc_during_call, 1, "RC stays at 1 through the capture");
        // After boxed() consumed itself, `owned` was dropped inside boxed's scope;
        // CLOwned::drop → dec_rc → rc 0 → std::alloc::dealloc.
        // Cannot read_rc(base) here — allocation is freed.
    }
}
