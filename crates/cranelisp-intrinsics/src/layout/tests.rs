use super::*;
use std::ffi::CString;

// spec: design/arch/platform-interface.md §5.5.4 — matching hashes return
// (the binary proceeds to main). `linked` is the ADDRESS of a `&str` (the
// platform rlib's exported symbol), so the test passes `&linked_str`.
#[test]
fn matching_hashes_return() {
    let linked_str: &'static str = "abc123";
    let expected = CString::new("abc123").unwrap();
    let name = CString::new("shapes").unwrap();
    // Returns without aborting — reaching the assertion is the test.
    cranelisp_check_layout_hash(
        (&raw const linked_str).cast::<u8>(),
        expected.as_ptr().cast::<u8>(),
        name.as_ptr().cast::<u8>(),
    );
}

// spec: design/arch/platform-interface.md §5.5.4 — D2 regression. The
// `--link` reader receives the ADDRESS of the platform rlib's exported
// `__cranelisp_layout_hash_<name>` symbol, which is a Rust `&str` fat
// reference (`(data_ptr, len)`), NOT a bare `char*`. The pre-fix intrinsic
// did `CStr::from_ptr(linked)`, reading the fat pointer's raw bytes instead
// of the hash → never matched. This test pins the corrected read: interpret
// `linked` as `*const &str` and use its (ptr, len) view — exactly like the
// `--run` host — so it reads precisely the hash even though the `&str` points
// into a larger rodata blob whose hash is followed by schema text.
#[test]
fn link_reader_dereferences_fat_pointer_to_get_hash() {
    // The platform rlib's hash `&str` points at the first 16 bytes of a
    // larger rodata blob; the bytes after the hash are NOT part of `len`.
    let blob: &'static str = "239228b4b2e2ecb1(schema (shapes/Rectangle))";
    let linked_str: &'static str = &blob[..16];
    let expected = CString::new("239228b4b2e2ecb1").unwrap();

    // The fat-pointer read sees exactly the 16-char hash (len-bounded), never
    // the trailing schema text — so the clean case matches.
    assert_eq!(linked_str.as_bytes(), expected.as_bytes());

    // Negative half: a drifted hash still differs (the fix makes the CLEAN
    // case match — it must NOT make every case match).
    let drift_blob: &'static str = "deadbeefdeadbeef(schema (shapes/Rectangle))";
    let drifted: &'static str = &drift_blob[..16];
    assert_ne!(
        drifted.as_bytes(),
        expected.as_bytes(),
        "a drifted hash still mismatches — the gate still refuses on drift"
    );

    // End-to-end through the intrinsic's read path: passing &linked_str
    // (address of the `&str`) returns without aborting on a match.
    let name = CString::new("shapes").unwrap();
    cranelisp_check_layout_hash(
        (&raw const linked_str).cast::<u8>(),
        expected.as_ptr().cast::<u8>(),
        name.as_ptr().cast::<u8>(),
    );
}
