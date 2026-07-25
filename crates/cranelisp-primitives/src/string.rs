//! User-callable string primitives — primitives-surface presentation.
//!
//! The kebab-case string operations callable from user code (`str-concat`,
//! `str-eq`, `substring`, `split`, `to-upper`, …) belong to the **primitives**
//! bounded context — they are addressable via the synthetic `primitives`
//! module's symbol table with kebab-case JIT names.
//!
//! ## Heap representation boundaries
//!
//! These bodies physically live here. They read heap-layout offsets from
//! `cranelisp-intrinsics`' blessed public layout ABI — never local copies
//! (single source of truth, Principle 7): string offsets from
//! [`cranelisp_intrinsics::heap_string::HeapString::LEN_OFFSET`] and
//! [`HeapString::DATA_OFFSET`] (whose const rustdoc is the canonical
//! statement). `split`/`join` do not know the Vec representation: they cross
//! through the purpose-specific owned-construction and scoped-read operations
//! in [`cranelisp_intrinsics::vec_runtime`]. The alloc/rc/drop helpers in
//! `cranelisp-intrinsics::{alloc, rc, drop}` carry the consuming-convention
//! plumbing (Decision 24).
//!
//! ## Consuming convention (Decision 24)
//!
//! Every extern fn here MUST consume its heap-typed arguments (dec any heap
//! arg it does not return). Internal Rust callers may handle ownership
//! differently; the extern boundary is fixed for codegen uniformity.

use cranelisp_intrinsics::heap_string::{HeapString, alloc_string};
use cranelisp_intrinsics::vec_runtime::{vec_strings_from_owned, with_vec_strings};
use cranelisp_intrinsics::{alloc, drop as drop_glue, rc};

// ---------------------------------------------------------------------------
// Internal helpers — duplicate of intrinsics::heap_string's private helpers,
// scoped to this module so the user-callable fns are self-contained.
// ---------------------------------------------------------------------------

/// Read string bytes from a base pointer. Returns (byte_ptr, byte_len).
///
/// # Safety
///
/// `base` must point to a valid `HeapString` allocation.
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
/// `base` must point to a valid `HeapString` with valid UTF-8 content.
unsafe fn read_str(base: *const u8) -> &'static str {
    let (bytes, _) = unsafe { read_string_parts(base) };
    // SAFETY: all strings are created from valid UTF-8 sources.
    unsafe { std::str::from_utf8_unchecked(bytes) }
}

// ---------------------------------------------------------------------------
// Extern C interface — user-callable string primitives.
// ---------------------------------------------------------------------------

/// Concatenate two strings. Returns a new string (rc=1).
///
/// Decision 24: consuming convention — dec both heap args.
pub(crate) fn str_concat(a: i64, b: i64) -> i64 {
    // SAFETY: a and b are valid HeapString base pointers from JIT code.
    let a_str = unsafe { read_str(a as *const u8) };
    let b_str = unsafe { read_str(b as *const u8) };

    let combined = format!("{a_str}{b_str}");
    let result = alloc_string(combined.as_bytes()) as i64;
    rc::consume_shallow(a);
    rc::consume_shallow(b);
    result
}

/// String equality (byte-wise). Returns 1 (true) or 0 (false).
///
/// Decision 24: consuming convention — dec both heap args.
pub(crate) fn str_eq(a: i64, b: i64) -> i64 {
    let a_str = unsafe { read_str(a as *const u8) };
    let b_str = unsafe { read_str(b as *const u8) };
    let result = if a_str == b_str { 1 } else { 0 };
    rc::consume_shallow(a);
    rc::consume_shallow(b);
    result
}

/// String inequality (byte-wise) — logical negation of `str-eq`.
/// Returns 1 (true) when the strings differ, 0 (false) when equal.
/// This is the `Eq.!=` String dispatch target (`spec/07-traits.md §7.7.2`),
/// the not-equal counterpart of `str-eq` exactly as `neq-i64` is to `eq-i64`.
///
/// Decision 24: consuming convention — dec both heap args.
pub(crate) fn neq_string(a: i64, b: i64) -> i64 {
    let a_str = unsafe { read_str(a as *const u8) };
    let b_str = unsafe { read_str(b as *const u8) };
    let result = if a_str != b_str { 1 } else { 0 };
    rc::consume_shallow(a);
    rc::consume_shallow(b);
    result
}

/// String length in bytes.
///
/// Decision 24: consuming convention — dec the heap arg.
pub(crate) fn str_len(s: i64) -> i64 {
    // SAFETY: `s` is a valid HeapString base pointer.
    let len = unsafe { *((s as *const u8).add(HeapString::LEN_OFFSET as usize) as *const i64) };
    rc::consume_shallow(s);
    len
}

/// Identity function for strings — increments RC and returns the same pointer.
/// Used when a string value needs to be shared (creates a new reference).
pub(crate) fn string_identity(s: i64) -> i64 {
    // Atomically increment RC via the blessed `rc::rc_inc` entry point (the
    // single owner of the shallow-inc discipline, Principle 7). Behaviour is
    // identical to the former inline `fetch_add(Release)` + `rc_trace("inc")`:
    // a HeapString is always a heap pointer, so `rc_inc`'s nullary-tag branch
    // is never taken.
    rc::rc_inc(s);
    s
}

/// Extract a substring from `start` (inclusive) to `end` (exclusive), clamping
/// out-of-bounds indices. Returns a new heap string (rc=1).
///
/// Decision 24: consuming convention — dec the heap arg.
pub(crate) fn str_substring(s: i64, start: i64, end: i64) -> i64 {
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
/// Decision 24: consuming convention — dec the heap arg.
pub(crate) fn str_char_at(s: i64, idx: i64) -> i64 {
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
/// Decision 24: consuming convention — dec both heap args.
pub(crate) fn str_split(s: i64, sep: i64) -> i64 {
    let src = unsafe { read_str(s as *const u8) };
    let sep_str = unsafe { read_str(sep as *const u8) };

    let elements = src
        .split(sep_str)
        .map(|part| alloc_string(part.as_bytes()) as i64)
        .collect();

    // SAFETY: every element is a fresh HeapString owned reference. Ownership
    // of each reference transfers exactly once into the returned Vec.
    let vec_base = unsafe { vec_strings_from_owned(elements) };

    rc::consume_shallow(s);
    rc::consume_shallow(sep);
    vec_base
}

/// Join a Vec of strings with a separator. Separator is the first argument.
///
/// Decision 24: consuming convention — dec separator via `consume_shallow`
/// and the Vec via `consume_vec_of_string` (walks element Strings + frees
/// the Vec struct + data buffer).
pub(crate) fn str_join(sep: i64, vec: i64) -> i64 {
    let sep_str = unsafe { read_str(sep as *const u8) };

    // SAFETY: `vec` is a live, immutable Vec-of-String for the duration of
    // the callback. The callback borrows element bases only; it performs no
    // retain, release, or ownership transfer for individual elements.
    let joined = unsafe {
        with_vec_strings(vec, |elements| {
            let parts = elements
                .iter()
                .map(|element| read_str(*element as *const u8))
                .collect::<Vec<_>>();
            parts.join(sep_str)
        })
    };
    // The callback has returned, so the unsafe Vec-element slice borrow has
    // ended before this unrelated runtime allocation begins.
    let result = alloc_string(joined.as_bytes()) as i64;

    rc::consume_shallow(sep);
    drop_glue::consume_vec_of_string(vec);

    result
}

/// Replace all occurrences of `from` with `to` in `s`. Returns a new string.
///
/// Decision 24: consuming convention — dec all three heap args.
pub(crate) fn str_replace(s: i64, from: i64, to: i64) -> i64 {
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
/// Decision 24: consuming convention — dec the heap arg.
pub(crate) fn str_trim(s: i64) -> i64 {
    let src = unsafe { read_str(s as *const u8) };
    let result = alloc_string(src.trim().as_bytes()) as i64;
    rc::consume_shallow(s);
    result
}

/// Returns 1 if `s` starts with `prefix`, 0 otherwise.
///
/// Decision 24: consuming convention — dec both heap args.
pub(crate) fn str_starts_with(s: i64, prefix: i64) -> i64 {
    let src = unsafe { read_str(s as *const u8) };
    let prefix_str = unsafe { read_str(prefix as *const u8) };
    let result = if src.starts_with(prefix_str) { 1 } else { 0 };
    rc::consume_shallow(s);
    rc::consume_shallow(prefix);
    result
}

/// Returns 1 if `s` ends with `suffix`, 0 otherwise.
///
/// Decision 24: consuming convention — dec both heap args.
pub(crate) fn str_ends_with(s: i64, suffix: i64) -> i64 {
    let src = unsafe { read_str(s as *const u8) };
    let suffix_str = unsafe { read_str(suffix as *const u8) };
    let result = if src.ends_with(suffix_str) { 1 } else { 0 };
    rc::consume_shallow(s);
    rc::consume_shallow(suffix);
    result
}

/// Returns 1 if `s` contains `needle`, 0 otherwise.
///
/// Decision 24: consuming convention — dec both heap args.
pub(crate) fn str_contains(s: i64, needle: i64) -> i64 {
    let src = unsafe { read_str(s as *const u8) };
    let needle_str = unsafe { read_str(needle as *const u8) };
    let result = if src.contains(needle_str) { 1 } else { 0 };
    rc::consume_shallow(s);
    rc::consume_shallow(needle);
    result
}

/// Convert string to uppercase. Returns a new string.
///
/// Decision 24: consuming convention — dec the heap arg.
pub(crate) fn str_to_upper(s: i64) -> i64 {
    let src = unsafe { read_str(s as *const u8) };
    let result = alloc_string(src.to_uppercase().as_bytes()) as i64;
    rc::consume_shallow(s);
    result
}

/// Convert string to lowercase. Returns a new string.
///
/// Decision 24: consuming convention — dec the heap arg.
pub(crate) fn str_to_lower(s: i64) -> i64 {
    let src = unsafe { read_str(s as *const u8) };
    let result = alloc_string(src.to_lowercase().as_bytes()) as i64;
    rc::consume_shallow(s);
    result
}

// Suppress unused-import warning when `alloc` is only referenced via test
// modules below.
#[allow(dead_code)]
fn _force_alloc_dep() {
    let _ = alloc::alloc_count;
}

#[cfg(test)]
mod tests;
