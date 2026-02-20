//! Shared interface crate for the cranelisp platform ABI.
//!
//! Both the cranelisp host binary and every platform DLL depend on this crate.
//! It defines the C-ABI contract types that cross the DLL boundary:
//! struct layouts, constants, wrapper types, and the `declare_platform!` macro.
//!
//! Platform authors work with safe wrapper types (`CLInt`, `CLString`, `CLBool`,
//! `CLFloat`) — all `unsafe` is encapsulated here. The host uses
//! `manifest_to_descriptors()` to convert C-ABI manifests into safe Rust types.

use std::sync::atomic::{AtomicPtr, Ordering};

/// ABI version — bump on breaking changes to the platform contract.
pub const ABI_VERSION: u32 = 1;

/// String layout: `[i64 len][u8 bytes...]` at payload pointer.
/// Payload pointer = alloc base + 16 (after size + rc headers).
pub const STRING_HEADER_BYTES: usize = 8;

// ── C-ABI contract types ──────────────────────────────────────────────────

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

// ── Safe wrapper types ────────────────────────────────────────────────────
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

// ── CLInt conversions ─────────────────────────────────────────────────────

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

// ── CLBool conversions ────────────────────────────────────────────────────

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

// ── CLFloat conversions ───────────────────────────────────────────────────

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

// ── CLType trait ──────────────────────────────────────────────────────────

/// Marker trait for cranelisp value types that can be IO-wrapped.
/// Only CL* types implement this — prevents raw i64 from being lifted.
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

// ── CLIO — IO-wrapped return value ────────────────────────────────────────

/// IO-wrapped return value. Allocates IOVal (tag=0, one field) on heap.
/// Generic over CL type for type safety — only CLType implementors accepted.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct CLIO<CL: CLType>(i64, std::marker::PhantomData<CL>);

impl<CL: CLType> CLIO<CL> {
    /// Wrap a value in IO by allocating IOVal on the heap.
    pub fn pure(val: CL) -> Self {
        let alloc = get_global_alloc();
        let ptr = alloc(16); // 2 * i64: tag + field
        unsafe {
            *(ptr as *mut i64) = 0; // IOVal tag = 0
            *((ptr + 8) as *mut i64) = val.to_raw(); // field value
        }
        CLIO(ptr, std::marker::PhantomData)
    }
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
// CL* → CLIO directly:
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

// ── CLString conversions ──────────────────────────────────────────────────

/// Global allocator function pointer, set by `HostContext::init()`.
/// Each DLL gets its own copy of this static (separate compilation unit).
static GLOBAL_ALLOC: AtomicPtr<()> = AtomicPtr::new(std::ptr::null_mut());

/// Get the global allocator function. Panics if not initialized.
fn get_global_alloc() -> extern "C" fn(i64) -> i64 {
    let ptr = GLOBAL_ALLOC.load(Ordering::Relaxed);
    assert!(!ptr.is_null(), "platform not initialized: HostContext::init() not called");
    unsafe { std::mem::transmute(ptr) }
}

impl CLString {
    /// View the string contents as a `&str`.
    ///
    /// # Safety invariant
    /// A `CLString` always holds a valid pointer to `[i64 len][u8 bytes...]`.
    pub fn as_str(&self) -> &str {
        unsafe {
            let ptr = self.0;
            let len = *(ptr as *const i64) as usize;
            let bytes =
                std::slice::from_raw_parts((ptr + STRING_HEADER_BYTES as i64) as *const u8, len);
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
        let ptr = alloc(size);
        unsafe {
            *(ptr as *mut i64) = bytes.len() as i64;
            std::ptr::copy_nonoverlapping(
                bytes.as_ptr(),
                (ptr + STRING_HEADER_BYTES as i64) as *mut u8,
                bytes.len(),
            );
        }
        CLString(ptr)
    }
}

// ── HostContext ────────────────────────────────────────────────────────────

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
        self.callbacks.store(raw, Ordering::Relaxed);

        // Set the global allocator for CLString conversions.
        let alloc_fn = unsafe { (*raw).alloc };
        GLOBAL_ALLOC.store(alloc_fn as *mut (), Ordering::Relaxed);
    }
}

// ── Owned descriptors (safe Rust types) ───────────────────────────────────

/// Safe Rust descriptor for a platform function, converted from C-ABI.
///
/// Used by the host after loading a DLL manifest.
pub struct OwnedPlatformFnDescriptor {
    pub name: String,
    pub jit_name: String,
    pub ptr: *const u8,
    pub param_count: usize,
    pub type_sig: String,
    pub docstring: String,
    pub param_names: Vec<String>,
}

/// Convert a C-ABI manifest into safe Rust descriptors.
///
/// # Safety
/// All pointers in the manifest must be valid and point to UTF-8 data.
pub unsafe fn manifest_to_descriptors(
    manifest: &PlatformManifest,
) -> Result<(String, String, Vec<OwnedPlatformFnDescriptor>), String> {
    let name = unsafe {
        let bytes = std::slice::from_raw_parts(manifest.name, manifest.name_len);
        std::str::from_utf8(bytes)
            .map_err(|e| format!("invalid UTF-8 in platform name: {}", e))?
            .to_string()
    };
    let version = unsafe {
        let bytes = std::slice::from_raw_parts(manifest.version, manifest.version_len);
        std::str::from_utf8(bytes)
            .map_err(|e| format!("invalid UTF-8 in platform version: {}", e))?
            .to_string()
    };

    let functions = unsafe {
        std::slice::from_raw_parts(manifest.functions, manifest.function_count)
    };

    let mut descriptors = Vec::with_capacity(manifest.function_count);
    for func in functions {
        let func_name = unsafe {
            let bytes = std::slice::from_raw_parts(func.name, func.name_len);
            std::str::from_utf8(bytes)
                .map_err(|e| format!("invalid UTF-8 in function name: {}", e))?
                .to_string()
        };
        let func_jit_name = unsafe {
            let bytes = std::slice::from_raw_parts(func.jit_name, func.jit_name_len);
            std::str::from_utf8(bytes)
                .map_err(|e| format!("invalid UTF-8 in function jit_name: {}", e))?
                .to_string()
        };
        let func_type_sig = unsafe {
            let bytes = std::slice::from_raw_parts(func.type_sig, func.type_sig_len);
            std::str::from_utf8(bytes)
                .map_err(|e| format!("invalid UTF-8 in function type_sig: {}", e))?
                .to_string()
        };
        let func_docstring = unsafe {
            let bytes = std::slice::from_raw_parts(func.docstring, func.docstring_len);
            std::str::from_utf8(bytes)
                .map_err(|e| format!("invalid UTF-8 in function docstring: {}", e))?
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
                        .map_err(|e| {
                            format!("invalid UTF-8 in param name {}: {}", i, e)
                        })?
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
        });
    }

    Ok((name, version, descriptors))
}

// ── declare_platform! macro ───────────────────────────────────────────────

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
/// wrapper types — they are defined outside the macro. The macro handles
/// only manifest generation and host callback initialization.
///
/// # Example
///
/// ```ignore
/// use cranelisp_platform::*;
///
/// static HOST: HostContext = HostContext::new();
///
/// pub extern "C" fn print_string(s: CLString) -> CLInt {
///     println!("{}", s.as_str());
///     0i64.into()
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
                }
            ),* $(,)?
        ]
    ) => {
        #[unsafe(no_mangle)]
        pub extern "C" fn cranelisp_platform_manifest(
            callbacks: *const $crate::HostCallbacks,
        ) -> $crate::PlatformManifest {
            // Initialize the host context (stores callbacks, sets global alloc).
            unsafe { $host.init(callbacks); }

            // Build function descriptors.
            // Phase 1: Capture each function pointer and param info before
            // shadowing the identifier.
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
                    (fn_ptr, name_ptrs_ptr, name_lens_ptr, param_count)
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
