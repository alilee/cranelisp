//! Heap string implementation.
//!
//! `HeapString` layout is owned by this crate. The backend treats strings as
//! opaque heap pointers — all string content access goes through the extern
//! functions defined here. This containment enables future representation
//! changes (e.g., ropes per NFR C.2.3) as runtime-only modifications.
//!
//! Layout: `[alloc_size(0) | rc(8) | len(16) | bytes(24)...]`
//! All offsets are from the base pointer (positive-only, base-pointer convention).

use std::mem::{self, offset_of};
use std::sync::atomic::{AtomicI64, Ordering};

use cranelisp_types::HeapHeader;

use crate::alloc;
use crate::rc;

/// Heap string: [header | len | bytes...]
/// Owned by cranelisp-runtime. Opaque to the backend.
#[repr(C)]
pub struct HeapString {
    pub header: HeapHeader,
    /// Number of bytes (not characters) in the string.
    pub len: i64,
    // Bytes follow immediately at offset 24. Not a struct field because the
    // length is dynamic. Access via: base_ptr.byte_add(DATA_OFFSET)
}

impl HeapString {
    pub const LEN_OFFSET: i32 = offset_of!(Self, len) as i32; // 16
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

    // SAFETY: base is valid and has space for HeapHeader + payload_size bytes.
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

/// Read a string from a base pointer as a &str.
///
/// # Safety
///
/// `base` must point to a valid HeapString with valid UTF-8 content.
unsafe fn read_str(base: *const u8) -> &'static str {
    let (bytes, _) = unsafe { read_string_parts(base) };
    // SAFETY: all strings are created from valid UTF-8 sources.
    unsafe { std::str::from_utf8_unchecked(bytes) }
}

// ---------------------------------------------------------------------------
// Extern C interface (called from JIT code)
// ---------------------------------------------------------------------------

/// Allocate a new string from raw bytes. Copies `byte_len` bytes from `bytes_ptr`.
/// Returns base pointer to a HeapString (rc=1).
#[unsafe(no_mangle)]
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

/// Concatenate two strings. Returns a new string (rc=1).
/// Both inputs are borrowed (caller manages their RC).
#[unsafe(no_mangle)]
pub extern "C" fn str_concat(a: i64, b: i64) -> i64 {
    // SAFETY: a and b are valid HeapString base pointers from JIT code.
    let a_str = unsafe { read_str(a as *const u8) };
    let b_str = unsafe { read_str(b as *const u8) };

    let combined = format!("{a_str}{b_str}");
    alloc_string(combined.as_bytes()) as i64
}

/// String equality (byte-wise). Returns 1 (true) or 0 (false).
#[unsafe(no_mangle)]
pub extern "C" fn str_eq(a: i64, b: i64) -> i64 {
    // SAFETY: a and b are valid HeapString base pointers from JIT code.
    let a_str = unsafe { read_str(a as *const u8) };
    let b_str = unsafe { read_str(b as *const u8) };
    if a_str == b_str { 1 } else { 0 }
}

/// String length in bytes.
#[unsafe(no_mangle)]
pub extern "C" fn str_len(s: i64) -> i64 {
    // SAFETY: s is a valid HeapString base pointer.
    unsafe { *(( s as *const u8).add(HeapString::LEN_OFFSET as usize) as *const i64) }
}

/// Identity function for strings — increments RC and returns the same pointer.
/// Used when a string value needs to be shared (creates a new reference).
#[unsafe(no_mangle)]
pub extern "C" fn string_identity(s: i64) -> i64 {
    // Atomically increment RC at base + HeapHeader::RC_OFFSET.
    // SAFETY: s is a valid HeapString base pointer; RC field is at offset 8.
    let rc_ptr = unsafe {
        &*((s as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const AtomicI64)
    };
    let new_rc = rc_ptr.fetch_add(1, Ordering::Release) + 1;
    rc::rc_trace("inc", s, new_rc);
    s
}

/// Read a string's bytes for display/formatting. Writes pointer and length
/// to the provided out-parameters.
///
/// Used by the binary crate's ValueFormatter — NOT called from JIT code.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn string_read(s: i64, out_ptr: *mut *const u8, out_len: *mut i64) {
    // SAFETY: s is a valid HeapString base pointer; out_ptr/out_len are valid.
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

/// Read a string from a base pointer as a Rust &str. Public API for the
/// binary crate's format_result_value.
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
    use crate::alloc::bytes_current;

    // spec: 12-runtime §12.1.2 — empty string heap allocation
    #[test]
    fn test_alloc_string_empty() {
        let bytes_before = bytes_current();
        let base = alloc_string(b"");
        unsafe {
            let len = *(base.add(HeapString::LEN_OFFSET as usize) as *const i64);
            assert_eq!(len, 0);
            alloc::dealloc(base);
        }
        assert_eq!(bytes_current(), bytes_before);
    }

    // spec: 12-runtime §12.1.2 — string heap layout [length | bytes]
    #[test]
    fn test_alloc_string_hello() {
        let bytes_before = bytes_current();
        let base = alloc_string(b"hello");
        unsafe {
            let len = *(base.add(HeapString::LEN_OFFSET as usize) as *const i64);
            assert_eq!(len, 5);
            let s = read_str(base);
            assert_eq!(s, "hello");
            alloc::dealloc(base);
        }
        assert_eq!(bytes_current(), bytes_before);
    }

    // spec: appendix-a-builtins §A.3 — str-concat concatenates two strings
    #[test]
    fn test_str_concat() {
        let bytes_before = bytes_current();
        let a = alloc_string(b"hello, ") as i64;
        let b = alloc_string(b"world!") as i64;
        let result = str_concat(a, b);

        unsafe {
            assert_eq!(read_str(result as *const u8), "hello, world!");
            alloc::dealloc(a as *mut u8);
            alloc::dealloc(b as *mut u8);
            alloc::dealloc(result as *mut u8);
        }
        assert_eq!(bytes_current(), bytes_before);
    }

    // spec: appendix-a-builtins §A.3 — str-eq returns true for equal strings
    #[test]
    fn test_str_eq_equal() {
        let a = alloc_string(b"same") as i64;
        let b = alloc_string(b"same") as i64;
        assert_eq!(str_eq(a, b), 1);
        unsafe {
            alloc::dealloc(a as *mut u8);
            alloc::dealloc(b as *mut u8);
        }
    }

    // spec: appendix-a-builtins §A.3 — str-eq returns false for different strings
    #[test]
    fn test_str_eq_not_equal() {
        let a = alloc_string(b"hello") as i64;
        let b = alloc_string(b"world") as i64;
        assert_eq!(str_eq(a, b), 0);
        unsafe {
            alloc::dealloc(a as *mut u8);
            alloc::dealloc(b as *mut u8);
        }
    }

    // spec: 12-runtime §12.1.2 — string length in bytes (not characters)
    #[test]
    fn test_str_len() {
        let s = alloc_string(b"hello") as i64;
        assert_eq!(str_len(s), 5);
        let empty = alloc_string(b"") as i64;
        assert_eq!(str_len(empty), 0);
        unsafe {
            alloc::dealloc(s as *mut u8);
            alloc::dealloc(empty as *mut u8);
        }
    }

    // spec: 12-runtime §12.3.2, appendix-a-builtins §A.3 — string-identity increments RC
    #[test]
    fn test_string_identity_increments_rc() {
        let bytes_before = bytes_current();
        let s = alloc_string(b"shared") as i64;

        // RC should be 1 after allocation.
        let rc_before = unsafe {
            *((s as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const i64)
        };
        assert_eq!(rc_before, 1);

        // string_identity should increment RC and return same pointer.
        let result = string_identity(s);
        assert_eq!(result, s);

        let rc_after = unsafe {
            *((s as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const i64)
        };
        assert_eq!(rc_after, 2);

        // Manually dec RC back for cleanup.
        unsafe {
            let rc_ptr = &*((s as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const AtomicI64);
            rc_ptr.fetch_sub(1, Ordering::Release);
            alloc::dealloc(s as *mut u8);
        }
        assert_eq!(bytes_current(), bytes_before);
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

    // spec: 12-runtime §12.1.2 — extern string allocation from raw pointer
    #[test]
    fn test_alloc_string_extern() {
        let bytes_before = bytes_current();
        let data = b"extern test";
        let s = heap_alloc_string(data.as_ptr(), data.len() as i64);
        assert_ne!(s, 0);
        unsafe {
            assert_eq!(read_str(s as *const u8), "extern test");
            alloc::dealloc(s as *mut u8);
        }
        assert_eq!(bytes_current(), bytes_before);
    }

    // spec: 12-runtime §12.1.2 — null pointer string allocation produces empty string
    #[test]
    fn test_alloc_string_null_ptr() {
        let s = heap_alloc_string(std::ptr::null(), 0);
        assert_ne!(s, 0);
        assert_eq!(str_len(s), 0);
        unsafe { alloc::dealloc(s as *mut u8) };
    }

    // spec: appendix-a-builtins §A.3 — str-concat with both empty strings
    #[test]
    fn test_str_concat_empty_strings() {
        let a = alloc_string(b"") as i64;
        let b = alloc_string(b"") as i64;
        let result = str_concat(a, b);
        assert_eq!(str_len(result), 0);
        unsafe {
            alloc::dealloc(a as *mut u8);
            alloc::dealloc(b as *mut u8);
            alloc::dealloc(result as *mut u8);
        }
    }

    // spec: appendix-a-builtins §A.3 — str-concat with one empty string
    #[test]
    fn test_str_concat_one_empty() {
        let a = alloc_string(b"hello") as i64;
        let b = alloc_string(b"") as i64;
        let result = str_concat(a, b);
        unsafe {
            assert_eq!(read_str(result as *const u8), "hello");
            alloc::dealloc(a as *mut u8);
            alloc::dealloc(b as *mut u8);
            alloc::dealloc(result as *mut u8);
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
}
