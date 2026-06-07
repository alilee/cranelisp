//! Heap string layout and runtime helpers.
//!
//! `HeapString` layout is owned by this crate. The backend treats strings as
//! opaque heap pointers — all heap-layout knowledge lives here. This module
//! holds the **backend-emitted-call targets** for the runtime/string family:
//! `runtime/alloc_string`, `runtime/string_read`, and the `HeapString` layout
//! type. The user-callable string operations (`str-concat`, `str-len`,
//! `substring`, …) physically live in `cranelisp-primitives::string`
//! (FIXME 0180 close, Sprint 67 Wave 3).
//!
//! Layout: `[alloc_size(0) | rc(8) | len(16) | bytes(24)...]`
//! All offsets are from the base pointer (positive-only, base-pointer convention).
//!
//! ## Module name rationale
//!
//! The module is named `heap_string` (not `string`) so that
//! `cargo-public-api` baselines distinguish the backend-emitted-call domain
//! here from the user-callable surface in `cranelisp-primitives::string`.

use std::mem::{self, offset_of};

use cranelisp_types::HeapHeader;

use crate::alloc;

/// Heap string: `[header | len | bytes...]`.
/// Layout owned by this crate; opaque to the backend.
#[repr(C)]
pub struct HeapString {
    pub header: HeapHeader,
    /// Number of bytes (not characters) in the string.
    pub len: i64,
    // Bytes follow immediately at offset 24. Not a struct field because the
    // length is dynamic. Access via: base_ptr.byte_add(DATA_OFFSET)
}

impl HeapString {
    /// Offset of the `len` field from the base pointer (codegen-time constant).
    ///
    /// Blessed, stable public layout-ABI (FIXME 0245): `cranelisp-primitives`
    /// (`string.rs`) reads this directly for its user-callable string ops; it
    /// holds no duplicate copy of the offset (Principle 7). Evolution is an
    /// explicit version bump, not a source-level guard (Principle 14).
    pub const LEN_OFFSET: i32 = offset_of!(Self, len) as i32; // 16
    /// Offset of the byte payload from the base pointer (codegen-time constant).
    ///
    /// Blessed, stable public layout-ABI (FIXME 0245): the named Rust consumer
    /// is `cranelisp-primitives`; the FFI counterpart is `cranelisp-platform`'s
    /// `CLString::as_str`, which reaches the bytes via `read_string_as_str`.
    pub const DATA_OFFSET: usize = mem::size_of::<Self>(); // 24

    /// Total payload size after the header: len field + byte data.
    pub const fn payload_size(byte_len: usize) -> usize {
        mem::size_of::<i64>() + byte_len
    }
}

const _: () = assert!(HeapString::LEN_OFFSET == 16);
const _: () = assert!(HeapString::DATA_OFFSET == 24);

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Allocate a heap string from a byte slice. Returns the base pointer.
///
/// Layout: `[alloc_size | rc=1 | len | bytes...]`
pub fn alloc_string(bytes: &[u8]) -> *mut u8 {
    let payload_size = HeapString::payload_size(bytes.len());
    let base = alloc::alloc_with_rc(payload_size);

    // SAFETY: `base` is valid and has space for HeapHeader + payload_size bytes.
    unsafe {
        // len at offset 16
        *(base.add(HeapString::LEN_OFFSET as usize) as *mut i64) = bytes.len() as i64;
        // bytes at offset 24
        if !bytes.is_empty() {
            std::ptr::copy_nonoverlapping(bytes.as_ptr(), base.add(HeapString::DATA_OFFSET), bytes.len());
        }
    }

    base
}

/// Read string bytes from a base pointer. Returns (byte_ptr, byte_len).
///
/// # Safety
///
/// `base` must point to a valid HeapString allocation.
unsafe fn read_string_parts(base: *const u8) -> (&'static [u8], usize) {
    let len = unsafe { *(base.add(HeapString::LEN_OFFSET as usize) as *const i64) } as usize;
    let bytes = if len > 0 {
        unsafe { std::slice::from_raw_parts(base.add(HeapString::DATA_OFFSET), len) }
    } else {
        &[]
    };
    (bytes, len)
}

/// Read a string from a base pointer as a `&str`.
///
/// # Safety
///
/// `base` must point to a valid HeapString with valid UTF-8 content.
unsafe fn read_str(base: *const u8) -> &'static str {
    let (bytes, _) = unsafe { read_string_parts(base) };
    // SAFETY: all strings are created from valid UTF-8 sources.
    unsafe { std::str::from_utf8_unchecked(bytes) }
}

/// Read a heap String's content as an owned `String`, without consuming it.
///
/// Used by the fork-join error-slot ferry (`ivar.rs`, `io.rs`) to decode a
/// ferried panic message stashed in a heap String, so it can be re-raised into
/// the joining thread's slot via `panic::set_runtime_error`.
///
/// # Safety
///
/// `base` must point to a valid `HeapString` allocation with valid UTF-8.
pub(crate) unsafe fn read_str_for_ferry(base: i64) -> String {
    // SAFETY: caller guarantees `base` is a valid HeapString base pointer.
    unsafe { read_str(base as *const u8).to_string() }
}

// ---------------------------------------------------------------------------
// Extern C interface (called from JIT code)
// ---------------------------------------------------------------------------

/// Allocate a new string from raw bytes. Copies `byte_len` bytes from `bytes_ptr`.
/// Returns base pointer to a HeapString (rc=1).
#[unsafe(export_name = "runtime/alloc_string")]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn heap_alloc_string(bytes_ptr: *const u8, byte_len: i64) -> i64 {
    let len = byte_len as usize;
    let bytes = if bytes_ptr.is_null() || len == 0 {
        &[]
    } else {
        // SAFETY: caller guarantees bytes_ptr points to valid memory of byte_len bytes.
        unsafe { std::slice::from_raw_parts(bytes_ptr, len) }
    };
    alloc_string(bytes) as i64
}

/// Read a string's bytes for display/formatting. Writes pointer and length
/// to the provided out-parameters.
///
/// Used by the binary crate's ValueFormatter — NOT called from JIT code
/// directly (its JIT name `runtime/string_read` is reserved for future use).
#[unsafe(export_name = "runtime/string_read")]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn string_read(s: i64, out_ptr: *mut *const u8, out_len: *mut i64) {
    // SAFETY: `s` is a valid HeapString base pointer; out_ptr/out_len are valid.
    unsafe {
        let (bytes, len) = read_string_parts(s as *const u8);
        *out_ptr = if bytes.is_empty() {
            std::ptr::null()
        } else {
            bytes.as_ptr()
        };
        *out_len = len as i64;
    }
}

// ---------------------------------------------------------------------------
// Public Rust API
// ---------------------------------------------------------------------------

/// Read a string from a base pointer as a Rust `&str`. Public API for the
/// binary crate's `format_result_value`.
///
/// # Safety
///
/// `base_ptr` must be a valid HeapString base pointer (as i64).
pub unsafe fn read_string_as_str(base_ptr: i64) -> &'static str {
    unsafe { read_str(base_ptr as *const u8) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::alloc::{alloc_count, dealloc_count};

    // spec: 12-runtime §12.1.2 — empty string heap allocation
    #[test]
    fn test_alloc_string_empty() {
        let allocs_before = alloc_count();
        let deallocs_before = dealloc_count();
        let base = alloc_string(b"");
        unsafe {
            let len = *(base.add(HeapString::LEN_OFFSET as usize) as *const i64);
            assert_eq!(len, 0);
            alloc::dealloc(base);
        }
        assert!(alloc_count() - allocs_before >= 1);
        assert!(dealloc_count() - deallocs_before >= 1);
    }

    // spec: 12-runtime §12.1.2 — string heap layout [length | bytes]
    #[test]
    fn test_alloc_string_hello() {
        let allocs_before = alloc_count();
        let deallocs_before = dealloc_count();
        let base = alloc_string(b"hello");
        unsafe {
            let len = *(base.add(HeapString::LEN_OFFSET as usize) as *const i64);
            assert_eq!(len, 5);
            let s = read_str(base);
            assert_eq!(s, "hello");
            alloc::dealloc(base);
        }
        assert!(alloc_count() - allocs_before >= 1);
        assert!(dealloc_count() - deallocs_before >= 1);
    }

    // spec: 12-runtime §12.1.2 — extern string allocation from raw pointer
    #[test]
    fn test_alloc_string_extern() {
        let allocs_before = alloc_count();
        let deallocs_before = dealloc_count();
        let data = b"extern test";
        let s = heap_alloc_string(data.as_ptr(), data.len() as i64);
        assert_ne!(s, 0);
        unsafe {
            assert_eq!(read_str(s as *const u8), "extern test");
            alloc::dealloc(s as *mut u8);
        }
        assert!(alloc_count() - allocs_before >= 1);
        assert!(dealloc_count() - deallocs_before >= 1);
    }

    // spec: 12-runtime §12.1.2 — null pointer string allocation produces empty string
    #[test]
    fn test_alloc_string_null_ptr() {
        let s = heap_alloc_string(std::ptr::null(), 0);
        // spec §12.1.2: (null, 0) must produce a valid empty heap string, not crash.
        assert_ne!(s, 0);
        unsafe {
            // Read the i64 length field at LEN_OFFSET. The parenthesisation matters:
            // cast the (base + offset) address to `*const i64` THEN deref. Without the
            // inner parens the leading `*` would bind to `s as *const u8` (a one-byte
            // read) and the trailing `as *const i64` would reinterpret that byte as a
            // pointer — a null-deref. See sibling tests for the same idiom.
            let len = *(s as *const u8).add(HeapString::LEN_OFFSET as usize).cast::<i64>();
            assert_eq!(len, 0);
            alloc::dealloc(s as *mut u8);
        }
    }

    // spec: 12-runtime §12.1.2 — string stores UTF-8 bytes (multi-byte characters)
    #[test]
    fn test_unicode_string() {
        let s = alloc_string("héllo 世界".as_bytes()) as i64;
        unsafe {
            assert_eq!(read_str(s as *const u8), "héllo 世界");
            alloc::dealloc(s as *mut u8);
        }
    }

    // spec: 12-runtime §12.1.2 — string read returns pointer and byte length
    #[test]
    fn test_string_read() {
        let s = alloc_string(b"test read") as i64;
        let mut out_ptr: *const u8 = std::ptr::null();
        let mut out_len: i64 = 0;
        string_read(s, &mut out_ptr, &mut out_len);
        assert_eq!(out_len, 9);
        assert!(!out_ptr.is_null());
        let bytes = unsafe { std::slice::from_raw_parts(out_ptr, out_len as usize) };
        assert_eq!(std::str::from_utf8(bytes).unwrap(), "test read");
        unsafe { alloc::dealloc(s as *mut u8) };
    }
}
