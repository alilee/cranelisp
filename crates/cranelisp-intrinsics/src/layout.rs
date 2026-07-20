//! Platform layout-hash check for `--link` standalone binaries.
//!
//! The `--link` startup stub (int's `src/exe.rs::generate_startup_object`)
//! bakes, per linked platform, the compiler-computed `expected_hash` and the
//! platform `name` as `.rodata`, declares the platform rlib's statically-linked
//! `__cranelisp_layout_hash_<name>` as imported data, and calls
//! [`cranelisp_check_layout_hash`] before running `main`
//! (`design/arch/platform-interface.md` §5.5.4 — the `--link` layout gate).
//!
//! This intrinsic is the compare-and-abort half of that gate. It compares the
//! linked hash against the baked `expected` hash and, on mismatch, prints rebuild
//! guidance and `abort()`s — so a binary linked against a platform whose ADT
//! layout has drifted from what the compiler recorded fails loudly at startup
//! rather than reading fields at stale offsets.
//!
//! The linked hash is read AS a Rust `&str` fat reference (`*const &str`), the
//! same `(ptr, len)` view the `--run` host uses (`src/platform.rs`) — NOT via
//! `CStr::from_ptr` on the symbol address (the D2 defect: `__cranelisp_layout_hash_<name>`
//! is a `&str` symbol, not a `char*`, so a `CStr` read strcmp'd the fat pointer's
//! raw bytes instead of the hash, and the clean case never matched). See
//! [`cranelisp_check_layout_hash`]'s doc for the per-parameter representation.
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
/// Parameters (addresses baked / linked into the startup stub):
///
/// - `linked` — the ADDRESS of the platform rlib's exported
///   `__cranelisp_layout_hash_<name>` symbol. That symbol is a Rust
///   `&'static str` — a `(data_ptr, len)` fat reference into the platform's
///   `.rodata`, NOT a bare `char*` (D2). This intrinsic reads it AS a fat
///   reference (`*const &str`), exactly mirroring the `--run` host reader
///   (`src/platform.rs`), so the two run modes read the identical symbol
///   identically.
/// - `expected` — a NUL-terminated C string: the compiler-computed hash baked
///   into the startup stub by int's `src/exe.rs` (`define_cstr_data`).
/// - `name` — a NUL-terminated C string: the platform name (for the diagnostic).
///
/// On a match this returns and `main` proceeds. On a mismatch it prints
/// `"platform '<name>' layout hash mismatch — run /platform-schema <name> and
/// rebuild"` to stderr and calls `std::process::abort()`.
///
/// # Safety
///
/// - `linked` must point to a valid, initialised Rust `&'static str` (the
///   platform rlib's exported layout-hash symbol — the startup stub links it).
/// - `expected` and `name` must be non-null, NUL-terminated byte sequences (the
///   stub bakes them as `.rodata`).
#[unsafe(export_name = "cranelisp_check_layout_hash")]
#[allow(clippy::not_unsafe_ptr_arg_deref)] // Called from the startup stub; cannot be marked unsafe.
pub extern "C" fn cranelisp_check_layout_hash(
    linked: *const u8,
    expected: *const u8,
    name: *const u8,
) {
    // SAFETY: `linked` is the address of the platform rlib's exported
    // `__cranelisp_layout_hash_<name>` symbol, which is a Rust `&'static str`
    // (the producer — `declare_platform!` in `cranelisp-platform` — exports it
    // as `pub static … : &str`). Read it AS a `&str` fat reference, the same way
    // the `--run` host does (`library.get::<*const &str>` → `**sym`), so the
    // (ptr, len) view is identical across run modes. `'static` because the symbol
    // lives for the process lifetime.
    let linked_hash: &'static str = unsafe { *(linked as *const &'static str) };

    // SAFETY: caller bakes `expected` as a NUL-terminated `.rodata` C string.
    let expected_hash = unsafe { CStr::from_ptr(expected as *const std::os::raw::c_char) };

    if linked_hash.as_bytes() == expected_hash.to_bytes() {
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
mod tests;
