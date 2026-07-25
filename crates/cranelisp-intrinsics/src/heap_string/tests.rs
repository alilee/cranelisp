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
        let len = *(s as *const u8)
            .add(HeapString::LEN_OFFSET as usize)
            .cast::<i64>();
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
