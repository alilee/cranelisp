//! Heap string implementation.
//!
//! `HeapString` layout is owned by this crate. The backend treats strings as
//! opaque heap pointers — all string content access goes through the extern
//! functions defined here. This containment enables future representation
//! changes (e.g., ropes per NFR C.2.3) as runtime-only modifications.
//!
//! Layout: `[alloc_size(0) | rc(8) | len(16) | bytes(24)...]`
//! All offsets are from the base pointer (positive-only, base-pointer convention).
//!
//! ## Wave 3b-2d.2 note (FIXME 0150)
//!
//! Per `design/arch/facades/primitives.md`, the user-callable string
//! operations (`str-concat`, `str-eq`, `substring`, `split`, …) are part of
//! the **primitives** surface — addressable in user code via the synthetic
//! `primitives` module. The actual extern fns continue to live here because
//! `cranelisp-runtime`'s pre-D43 shims (and the legacy
//! `cranelisp_intrinsics::string::*` paths backend's `IntrinsicSymbol`
//! table uses) still reach them at this location. `cranelisp-primitives`
//! re-exports the user-callable subset under `cranelisp_primitives::string`,
//! formalising the primitives-surface presentation without breaking the
//! transitional `runtime → intrinsics` shim chain.
//!
//! Moving these fns physically into `cranelisp-primitives` would require
//! either an `intrinsics → primitives` Cargo edge (which collides with the
//! existing `primitives → intrinsics` need for alloc helpers — Cargo cycle)
//! or editing `cranelisp-runtime` to point its shims at `cranelisp-primitives`
//! instead of `cranelisp-intrinsics`. Both routes are out of scope for this
//! wave (β-3 territory — see FIXME 0150). The Rust public-API surface of
//! `cranelisp-primitives` reflects the target shape via re-exports, which is
//! what `cargo-public-api` baselines see.

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

/// Concatenate two strings. Returns a new string (rc=1).
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — this extern dec's
/// both heap args before returning. Caller emits `compile_consuming_arg_list`
/// which incs heap-typed Var args so the caller's binding survives.
#[unsafe(export_name = "str-concat")]
pub extern "C" fn str_concat(a: i64, b: i64) -> i64 {
    // SAFETY: a and b are valid HeapString base pointers from JIT code.
    let a_str = unsafe { read_str(a as *const u8) };
    let b_str = unsafe { read_str(b as *const u8) };

    let combined = format!("{a_str}{b_str}");
    let result = alloc_string(combined.as_bytes()) as i64;
    // Decision 24: consume the heap arguments we did not return.
    rc::consume_shallow(a);
    rc::consume_shallow(b);
    result
}

/// String equality (byte-wise). Returns 1 (true) or 0 (false).
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — dec both heap args.
#[unsafe(export_name = "str-eq")]
pub extern "C" fn str_eq(a: i64, b: i64) -> i64 {
    // SAFETY: a and b are valid HeapString base pointers from JIT code.
    let a_str = unsafe { read_str(a as *const u8) };
    let b_str = unsafe { read_str(b as *const u8) };
    let result = if a_str == b_str { 1 } else { 0 };
    rc::consume_shallow(a);
    rc::consume_shallow(b);
    result
}

/// String length in bytes.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — dec the heap arg.
#[unsafe(export_name = "str-len")]
pub extern "C" fn str_len(s: i64) -> i64 {
    // SAFETY: s is a valid HeapString base pointer.
    let len = unsafe { *((s as *const u8).add(HeapString::LEN_OFFSET as usize) as *const i64) };
    rc::consume_shallow(s);
    len
}

/// Identity function for strings — increments RC and returns the same pointer.
/// Used when a string value needs to be shared (creates a new reference).
#[unsafe(export_name = "string-identity")]
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

/// Extract a substring from `start` (inclusive) to `end` (exclusive), clamping
/// out-of-bounds indices. Returns a new heap string (rc=1).
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — dec the heap arg.
#[unsafe(export_name = "substring")]
pub extern "C" fn str_substring(s: i64, start: i64, end: i64) -> i64 {
    let src = unsafe { read_str(s as *const u8) };
    let len = src.len() as i64;
    let start = start.clamp(0, len) as usize;
    let end = end.clamp(0, len) as usize;
    let end = end.max(start);
    let slice = &src[start..end];
    let result = alloc_string(slice.as_bytes()) as i64;
    rc::consume_shallow(s);
    result
}

/// Return the character at byte index `idx` as a single-character string.
/// Returns an empty string if `idx` is out of bounds.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — dec the heap arg.
#[unsafe(export_name = "char-at")]
pub extern "C" fn str_char_at(s: i64, idx: i64) -> i64 {
    let src = unsafe { read_str(s as *const u8) };
    let idx = idx as usize;
    let result = match src.get(idx..) {
        Some(rest) => match rest.chars().next() {
            Some(ch) => {
                let mut buf = [0u8; 4];
                let encoded = ch.encode_utf8(&mut buf);
                alloc_string(encoded.as_bytes()) as i64
            }
            None => alloc_string(b"") as i64,
        },
        None => alloc_string(b"") as i64,
    };
    rc::consume_shallow(s);
    result
}

/// Split a string by a separator. Returns a Vec of heap strings.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — dec both heap args.
#[unsafe(export_name = "split")]
pub extern "C" fn str_split(s: i64, sep: i64) -> i64 {
    let src = unsafe { read_str(s as *const u8) };
    let sep_str = unsafe { read_str(sep as *const u8) };

    let parts: Vec<&str> = src.split(sep_str).collect();
    let count = parts.len() as i64;

    // Allocate a Vec to hold the results.
    let vec_base = crate::vec::vec_new(count);

    unsafe {
        let data_ptr = *((vec_base as *const u8).add(crate::vec::DATA_PTR_OFFSET) as *const *mut i64);
        for (i, part) in parts.iter().enumerate() {
            let heap_str = alloc_string(part.as_bytes()) as i64;
            *data_ptr.add(i) = heap_str;
        }
        // Set len.
        *((vec_base as *mut u8).add(crate::vec::LEN_OFFSET) as *mut i64) = count;
    }

    rc::consume_shallow(s);
    rc::consume_shallow(sep);
    vec_base
}

/// Join a Vec of strings with a separator. Separator is the first argument.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — dec the separator
/// via `consume_shallow` and dec the Vec via `consume_vec_of_string` (which
/// walks the element Strings and frees the Vec struct + data buffer).
#[unsafe(export_name = "join")]
pub extern "C" fn str_join(sep: i64, vec: i64) -> i64 {
    let sep_str = unsafe { read_str(sep as *const u8) };

    let base = vec as *const u8;
    let len = unsafe { *(base.add(crate::vec::LEN_OFFSET) as *const i64) } as usize;
    let data_ptr = unsafe { *(base.add(crate::vec::DATA_PTR_OFFSET) as *const i64) as *const i64 };

    // Copy the joined bytes out before we release the input Vec.
    let mut parts: Vec<String> = Vec::with_capacity(len);
    for i in 0..len {
        let elem = unsafe { *data_ptr.add(i) };
        let s = unsafe { read_str(elem as *const u8) };
        parts.push(s.to_string());
    }

    let joined: String = parts.join(sep_str);
    let result = alloc_string(joined.as_bytes()) as i64;

    // Decision 24: consume both heap arguments.
    rc::consume_shallow(sep);
    crate::drop::consume_vec_of_string(vec);

    result
}

/// Replace all occurrences of `from` with `to` in `s`. Returns a new string.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — dec all three heap args.
#[unsafe(export_name = "replace")]
pub extern "C" fn str_replace(s: i64, from: i64, to: i64) -> i64 {
    let src = unsafe { read_str(s as *const u8) };
    let from_str = unsafe { read_str(from as *const u8) };
    let to_str = unsafe { read_str(to as *const u8) };
    let result = alloc_string(src.replace(from_str, to_str).as_bytes()) as i64;
    rc::consume_shallow(s);
    rc::consume_shallow(from);
    rc::consume_shallow(to);
    result
}

/// Trim leading and trailing whitespace. Returns a new string.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — dec the heap arg.
#[unsafe(export_name = "trim")]
pub extern "C" fn str_trim(s: i64) -> i64 {
    let src = unsafe { read_str(s as *const u8) };
    let result = alloc_string(src.trim().as_bytes()) as i64;
    rc::consume_shallow(s);
    result
}

/// Returns 1 if `s` starts with `prefix`, 0 otherwise.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — dec both heap args.
#[unsafe(export_name = "starts-with?")]
pub extern "C" fn str_starts_with(s: i64, prefix: i64) -> i64 {
    let src = unsafe { read_str(s as *const u8) };
    let prefix_str = unsafe { read_str(prefix as *const u8) };
    let result = if src.starts_with(prefix_str) { 1 } else { 0 };
    rc::consume_shallow(s);
    rc::consume_shallow(prefix);
    result
}

/// Returns 1 if `s` ends with `suffix`, 0 otherwise.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — dec both heap args.
#[unsafe(export_name = "ends-with?")]
pub extern "C" fn str_ends_with(s: i64, suffix: i64) -> i64 {
    let src = unsafe { read_str(s as *const u8) };
    let suffix_str = unsafe { read_str(suffix as *const u8) };
    let result = if src.ends_with(suffix_str) { 1 } else { 0 };
    rc::consume_shallow(s);
    rc::consume_shallow(suffix);
    result
}

/// Returns 1 if `s` contains `needle`, 0 otherwise.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — dec both heap args.
#[unsafe(export_name = "contains?")]
pub extern "C" fn str_contains(s: i64, needle: i64) -> i64 {
    let src = unsafe { read_str(s as *const u8) };
    let needle_str = unsafe { read_str(needle as *const u8) };
    let result = if src.contains(needle_str) { 1 } else { 0 };
    rc::consume_shallow(s);
    rc::consume_shallow(needle);
    result
}

/// Convert string to uppercase. Returns a new string.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — dec the heap arg.
#[unsafe(export_name = "to-upper")]
pub extern "C" fn str_to_upper(s: i64) -> i64 {
    let src = unsafe { read_str(s as *const u8) };
    let result = alloc_string(src.to_uppercase().as_bytes()) as i64;
    rc::consume_shallow(s);
    result
}

/// Convert string to lowercase. Returns a new string.
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — dec the heap arg.
#[unsafe(export_name = "to-lower")]
pub extern "C" fn str_to_lower(s: i64) -> i64 {
    let src = unsafe { read_str(s as *const u8) };
    let result = alloc_string(src.to_lowercase().as_bytes()) as i64;
    rc::consume_shallow(s);
    result
}

/// Read a string's bytes for display/formatting. Writes pointer and length
/// to the provided out-parameters.
///
/// Used by the binary crate's ValueFormatter — NOT called from JIT code.
#[unsafe(export_name = "runtime/string_read")]
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

    // spec: appendix-a-builtins §A.3 — str-concat concatenates two strings
    // Decision 24: str_concat consumes both heap args — test releases only the result.
    #[test]
    fn test_str_concat() {
        let allocs_before = alloc_count();
        let deallocs_before = dealloc_count();
        let a = alloc_string(b"hello, ") as i64;
        let b = alloc_string(b"world!") as i64;
        let result = str_concat(a, b);

        unsafe {
            assert_eq!(read_str(result as *const u8), "hello, world!");
            // Decision 24: extern consumed a and b — only dealloc the result.
            alloc::dealloc(result as *mut u8);
        }
        // Delta-based: at least 3 allocs (a + b + result), 3 deallocs (extern consumed a and b; test freed result).
        assert!(alloc_count() - allocs_before >= 3);
        assert!(dealloc_count() - deallocs_before >= 3);
    }

    // spec: appendix-a-builtins §A.3 — str-eq returns true for equal strings
    // Decision 24: str_eq consumes both heap args — nothing to dealloc.
    #[test]
    fn test_str_eq_equal() {
        let a = alloc_string(b"same") as i64;
        let b = alloc_string(b"same") as i64;
        assert_eq!(str_eq(a, b), 1);
        // Decision 24: extern consumed a and b.
    }

    // spec: appendix-a-builtins §A.3 — str-eq returns false for different strings
    // Decision 24: str_eq consumes both heap args — nothing to dealloc.
    #[test]
    fn test_str_eq_not_equal() {
        let a = alloc_string(b"hello") as i64;
        let b = alloc_string(b"world") as i64;
        assert_eq!(str_eq(a, b), 0);
        // Decision 24: extern consumed a and b.
    }

    // spec: 12-runtime §12.1.2 — string length in bytes (not characters)
    // Decision 24: str_len consumes its heap arg — nothing to dealloc.
    #[test]
    fn test_str_len() {
        let s = alloc_string(b"hello") as i64;
        assert_eq!(str_len(s), 5);
        let empty = alloc_string(b"") as i64;
        assert_eq!(str_len(empty), 0);
        // Decision 24: extern consumed s and empty.
    }

    // spec: 12-runtime §12.3.2, appendix-a-builtins §A.3 — string-identity increments RC
    #[test]
    fn test_string_identity_increments_rc() {
        let allocs_before = alloc_count();
        let deallocs_before = dealloc_count();
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
        // Delta-based: at least 1 alloc, 1 dealloc.
        assert!(alloc_count() - allocs_before >= 1);
        assert!(dealloc_count() - deallocs_before >= 1);
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
    // Decision 24: str_len consumes its heap arg.
    #[test]
    fn test_alloc_string_null_ptr() {
        let s = heap_alloc_string(std::ptr::null(), 0);
        assert_ne!(s, 0);
        assert_eq!(str_len(s), 0);
        // Decision 24: str_len consumed s.
    }

    // spec: appendix-a-builtins §A.3 — str-concat with both empty strings
    // Decision 24: str_concat + str_len both consume their heap args — only
    // the intermediate `result` needs an explicit dealloc, since str_len
    // consumes it at the end.
    #[test]
    fn test_str_concat_empty_strings() {
        let a = alloc_string(b"") as i64;
        let b = alloc_string(b"") as i64;
        let result = str_concat(a, b);
        assert_eq!(str_len(result), 0);
        // Decision 24: extern consumed a, b, and result (via str_len).
    }

    // spec: appendix-a-builtins §A.3 — str-concat with one empty string
    // Decision 24: str_concat consumes both heap args — test releases only the result.
    #[test]
    fn test_str_concat_one_empty() {
        let a = alloc_string(b"hello") as i64;
        let b = alloc_string(b"") as i64;
        let result = str_concat(a, b);
        unsafe {
            assert_eq!(read_str(result as *const u8), "hello");
            // Decision 24: extern consumed a and b — only dealloc the result.
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

    // ---------------------------------------------------------------------
    // Decision 24 extern-consumption tests (Sprint 56 Step 2c)
    //
    // Each test verifies RC balance for a string-family extern: the extern
    // must consume its heap arguments such that, after freeing the extern's
    // return value (if heap-typed), the net alloc/dealloc delta is zero.
    // A leak surfaces as an inequality; a double-free surfaces as a panic.
    // ---------------------------------------------------------------------

    // spec: design/arch/CLAUDE.md Decision 24 — consuming convention, extern str_concat
    #[test]
    fn decision24_str_concat_consumes_heap_args() {
        let allocs_before = alloc_count();
        let deallocs_before = dealloc_count();
        let a = alloc_string(b"foo") as i64; // rc=1
        let b = alloc_string(b"bar") as i64; // rc=1
        let result = str_concat(a, b);       // consumes a (−1, freed), consumes b (−1, freed)
        assert_eq!(unsafe { read_str(result as *const u8) }, "foobar");
        unsafe { alloc::dealloc(result as *mut u8) };
        // 3 allocs (a, b, result); 3 deallocs (extern freed a and b; test freed result).
        assert_eq!(alloc_count() - allocs_before, 3, "alloc count mismatch");
        assert_eq!(dealloc_count() - deallocs_before, 3, "dealloc count mismatch (leak or double-free)");
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consuming convention, extern str_eq
    #[test]
    fn decision24_str_eq_consumes_both_heap_args() {
        let allocs_before = alloc_count();
        let deallocs_before = dealloc_count();
        let a = alloc_string(b"xyz") as i64;
        let b = alloc_string(b"xyz") as i64;
        assert_eq!(str_eq(a, b), 1);
        // Extern consumed a and b — no further dealloc needed.
        assert_eq!(alloc_count() - allocs_before, 2);
        assert_eq!(dealloc_count() - deallocs_before, 2);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consuming convention, extern str_len
    #[test]
    fn decision24_str_len_consumes_heap_arg() {
        let allocs_before = alloc_count();
        let deallocs_before = dealloc_count();
        let s = alloc_string(b"abcde") as i64;
        assert_eq!(str_len(s), 5);
        assert_eq!(alloc_count() - allocs_before, 1);
        assert_eq!(dealloc_count() - deallocs_before, 1);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consuming convention, extern str_substring
    #[test]
    fn decision24_str_substring_consumes_heap_arg() {
        let allocs_before = alloc_count();
        let deallocs_before = dealloc_count();
        let s = alloc_string(b"hello world") as i64;
        let result = str_substring(s, 6, 11);
        assert_eq!(unsafe { read_str(result as *const u8) }, "world");
        unsafe { alloc::dealloc(result as *mut u8) };
        // 2 allocs (s, result); 2 deallocs (extern freed s, test freed result).
        assert_eq!(alloc_count() - allocs_before, 2);
        assert_eq!(dealloc_count() - deallocs_before, 2);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consuming convention, extern str_trim
    #[test]
    fn decision24_str_trim_consumes_heap_arg() {
        let allocs_before = alloc_count();
        let deallocs_before = dealloc_count();
        let s = alloc_string(b"  hi  ") as i64;
        let result = str_trim(s);
        assert_eq!(unsafe { read_str(result as *const u8) }, "hi");
        unsafe { alloc::dealloc(result as *mut u8) };
        assert_eq!(alloc_count() - allocs_before, 2);
        assert_eq!(dealloc_count() - deallocs_before, 2);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consuming convention, extern str_starts_with
    #[test]
    fn decision24_str_starts_with_consumes_both_heap_args() {
        let allocs_before = alloc_count();
        let deallocs_before = dealloc_count();
        let s = alloc_string(b"hello world") as i64;
        let prefix = alloc_string(b"hello") as i64;
        assert_eq!(str_starts_with(s, prefix), 1);
        assert_eq!(alloc_count() - allocs_before, 2);
        assert_eq!(dealloc_count() - deallocs_before, 2);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consuming convention, extern str_replace
    #[test]
    fn decision24_str_replace_consumes_three_heap_args() {
        let allocs_before = alloc_count();
        let deallocs_before = dealloc_count();
        let s = alloc_string(b"aaabbb") as i64;
        let from = alloc_string(b"a") as i64;
        let to = alloc_string(b"X") as i64;
        let result = str_replace(s, from, to);
        assert_eq!(unsafe { read_str(result as *const u8) }, "XXXbbb");
        unsafe { alloc::dealloc(result as *mut u8) };
        // 4 allocs, 4 deallocs (extern freed s/from/to; test freed result).
        assert_eq!(alloc_count() - allocs_before, 4);
        assert_eq!(dealloc_count() - deallocs_before, 4);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — consume_shallow handles rc>1 correctly
    // (scope semantic: the caller incs before the call, the extern dec's; net = 0.)
    #[test]
    fn decision24_consume_shallow_with_refcount_above_one() {
        use std::sync::atomic::{AtomicI64, Ordering};
        let allocs_before = alloc_count();
        let deallocs_before = dealloc_count();
        let s = alloc_string(b"shared") as i64;

        // Simulate caller-side inc (rc: 1 -> 2).
        unsafe {
            let rc_ptr = &*((s as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const AtomicI64);
            rc_ptr.fetch_add(1, Ordering::Release);
        }

        let len = str_len(s); // consume_shallow dec's (rc: 2 -> 1), no free.
        assert_eq!(len, 6);

        // String still alive with rc=1; clean up.
        unsafe { alloc::dealloc(s as *mut u8) };
        assert_eq!(alloc_count() - allocs_before, 1);
        assert_eq!(dealloc_count() - deallocs_before, 1);
    }
}
