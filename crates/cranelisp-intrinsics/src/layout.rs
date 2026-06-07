//! Platform layout-hash check for `--link` standalone binaries.
//!
//! The `--link` startup stub (`cranelisp-backend::exe::generate_startup_object_checked`)
//! bakes, per linked platform, the compiler-computed `expected_hash` and the
//! platform `name` as `.rodata`, declares the platform rlib's statically-linked
//! `__cranelisp_layout_hash_<name>` as imported data, and calls
//! [`cranelisp_check_layout_hash`] before running `main`
//! (`design/arch/platform-interface.md` §5.5.4 — the `--link` layout gate).
//!
//! This intrinsic is the compare-and-abort half of that gate. It strcmps the two
//! NUL-terminated hash strings and, on mismatch, prints rebuild guidance and
//! `abort()`s — so a binary linked against a platform whose ADT layout has drifted
//! from what the compiler recorded fails loudly at startup rather than reading
//! fields at stale offsets.
//!
//! It is force-linked into the produced binary via `cranelisp-exe-bundle`'s
//! `pub use cranelisp_intrinsics::layout` re-export (the same discipline as every
//! other startup intrinsic), since backend declares it `Linkage::Import` and never
//! references the Rust symbol directly.
//!
//! NOTE: it is NOT in `intrinsics_table()` — that catalog publishes
//! backend-emitted-call targets resolved via the JIT/cache/`--link` symbol paths
//! for *user-code* dispatch. `cranelisp_check_layout_hash` is emitted only into the
//! startup object and resolved by the system linker against the force-linked
//! archive, exactly like `cranelisp_init_primitives` / `exit` / `cranelisp_run_io`
//! in the startup stub (none of which are catalog entries either).

use std::ffi::CStr;

/// Compare the linked and expected platform layout hashes; abort on mismatch.
///
/// Parameters (all NUL-terminated C strings, from `.rodata` / imported data):
/// - `linked`:   the platform rlib's `__cranelisp_layout_hash_<name>` hash.
/// - `expected`: the compiler-computed hash baked into the startup stub.
/// - `name`:     the platform name (for the diagnostic).
///
/// On a match this returns and `main` proceeds. On a mismatch it prints
/// `"platform '<name>' layout hash mismatch — run /platform-schema <name> and
/// rebuild"` to stderr and calls `std::process::abort()`.
///
/// # Safety
///
/// All three pointers must be non-null and point to valid NUL-terminated byte
/// sequences (the startup stub guarantees this — they are baked `.rodata` /
/// linked data symbols).
#[unsafe(export_name = "cranelisp_check_layout_hash")]
#[allow(clippy::not_unsafe_ptr_arg_deref)] // Called from the startup stub; cannot be marked unsafe.
pub extern "C" fn cranelisp_check_layout_hash(
    linked: *const u8,
    expected: *const u8,
    name: *const u8,
) {
    // SAFETY: caller (the backend startup stub) guarantees non-null,
    // NUL-terminated C strings.
    let linked_hash = unsafe { CStr::from_ptr(linked as *const std::os::raw::c_char) };
    let expected_hash = unsafe { CStr::from_ptr(expected as *const std::os::raw::c_char) };

    if linked_hash.to_bytes() == expected_hash.to_bytes() {
        return;
    }

    // SAFETY: same guarantee for the name string.
    let platform_name = unsafe { CStr::from_ptr(name as *const std::os::raw::c_char) }
        .to_string_lossy()
        .into_owned();

    eprintln!(
        "platform '{platform_name}' layout hash mismatch — run /platform-schema {platform_name} and rebuild"
    );
    std::process::abort();
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CString;

    // spec: design/arch/platform-interface.md §5.5.4 — matching hashes return
    // (the binary proceeds to main).
    #[test]
    fn matching_hashes_return() {
        let linked = CString::new("abc123").unwrap();
        let expected = CString::new("abc123").unwrap();
        let name = CString::new("shapes").unwrap();
        // Returns without aborting — reaching the assertion is the test.
        cranelisp_check_layout_hash(
            linked.as_ptr() as *const u8,
            expected.as_ptr() as *const u8,
            name.as_ptr() as *const u8,
        );
    }

    // The mismatch path aborts the process, which cannot be exercised in-process
    // without crashing the test runner. The compare logic is a byte-equality
    // check; this test pins that equal byte sequences compare equal and differing
    // ones differ (the predicate the abort branch hinges on), without invoking
    // the abort.
    #[test]
    fn hash_byte_comparison_is_exact() {
        let a = CString::new("hash-A").unwrap();
        let b = CString::new("hash-A").unwrap();
        let c = CString::new("hash-B").unwrap();
        assert_eq!(a.as_bytes(), b.as_bytes(), "equal hashes compare equal");
        assert_ne!(a.as_bytes(), c.as_bytes(), "differing hashes compare unequal");
    }
}
