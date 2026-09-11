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

use cranelisp_intrinsics::handle::{Borrowed, Owned};
use cranelisp_intrinsics::heap_string::{HeapString, alloc_string};
use cranelisp_intrinsics::vec_runtime::{vec_strings_from_owned, with_vec_strings};
use cranelisp_intrinsics::{alloc, drop as drop_glue, rc};

use crate::abi_facts::adopt_produced_value;

// ---------------------------------------------------------------------------
// Internal helpers — duplicate of intrinsics::heap_string's private helpers,
// scoped to this module so the user-callable fns are self-contained.
// ---------------------------------------------------------------------------

/// Read string bytes from a base pointer. Returns (byte_ptr, byte_len).
///
/// # Safety
///
/// `base` must point to a valid `HeapString` allocation.
unsafe fn read_string_parts<'a>(string: Borrowed<'a>) -> (&'a [u8], usize) {
    let base = string.raw_for_read() as *const u8;
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
unsafe fn read_str<'a>(string: Borrowed<'a>) -> &'a str {
    let (bytes, _) = unsafe { read_string_parts(string) };
    // SAFETY: all strings are created from valid UTF-8 sources.
    unsafe { std::str::from_utf8_unchecked(bytes) }
}

/// Read one element whose lifetime is scoped by `with_vec_strings`' callback.
unsafe fn read_scoped_vec_string<'a>(raw: i64) -> &'a str {
    let base = raw as *const u8;
    let len = unsafe { *(base.add(HeapString::LEN_OFFSET as usize) as *const i64) } as usize;
    let bytes = if len == 0 {
        &[]
    } else {
        unsafe { std::slice::from_raw_parts(base.add(HeapString::DATA_OFFSET), len) }
    };
    // SAFETY: runtime Strings contain valid UTF-8 and the callback keeps this
    // element live for the returned borrow's complete use.
    unsafe { std::str::from_utf8_unchecked(bytes) }
}

// ---------------------------------------------------------------------------
// Extern C interface — user-callable string primitives.
// ---------------------------------------------------------------------------

/// Concatenate two strings. Returns a new string (rc=1).
///
/// Decision 24: consuming convention — dec both heap args.
pub(crate) fn str_concat(a: Owned, b: Owned) -> Owned {
    // SAFETY: a and b are valid HeapString base pointers from JIT code.
    let a_str = unsafe { read_str(a.as_borrowed()) };
    let b_str = unsafe { read_str(b.as_borrowed()) };

    let combined = format!("{a_str}{b_str}");
    // SAFETY: `alloc_string` returned a fully initialized fresh RC=1 String.
    let result = unsafe { adopt_produced_value(alloc_string(combined.as_bytes()) as i64) };
    rc::consume_shallow(a);
    rc::consume_shallow(b);
    result
}

/// String equality (byte-wise). Returns 1 (true) or 0 (false).
///
/// Decision 24: consuming convention — dec both heap args.
pub(crate) fn str_eq(a: Owned, b: Owned) -> i64 {
    let a_str = unsafe { read_str(a.as_borrowed()) };
    let b_str = unsafe { read_str(b.as_borrowed()) };
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
pub(crate) fn neq_string(a: Owned, b: Owned) -> i64 {
    let a_str = unsafe { read_str(a.as_borrowed()) };
    let b_str = unsafe { read_str(b.as_borrowed()) };
    let result = if a_str != b_str { 1 } else { 0 };
    rc::consume_shallow(a);
    rc::consume_shallow(b);
    result
}

/// String length in bytes.
///
/// Decision 24: consuming convention — dec the heap arg.
pub(crate) fn str_len(s: Owned) -> i64 {
    // SAFETY: `s` is a valid HeapString base pointer.
    let len = unsafe {
        *((s.raw_for_read() as *const u8).add(HeapString::LEN_OFFSET as usize) as *const i64)
    };
    rc::consume_shallow(s);
    len
}

/// Identity function for strings — increments RC and returns the same pointer.
/// Used when a string value needs to be shared (creates a new reference).
pub(crate) fn string_identity(s: Borrowed<'_>) -> Owned {
    s.to_owned()
}

/// Extract a substring from `start` (inclusive) to `end` (exclusive), clamping
/// out-of-bounds indices. Returns a new heap string (rc=1).
///
/// Decision 24: consuming convention — dec the heap arg.
pub(crate) fn str_substring(s: Owned, start: i64, end: i64) -> Owned {
    let src = unsafe { read_str(s.as_borrowed()) };
    let len = src.len() as i64;
    let start = start.clamp(0, len) as usize;
    let end = end.clamp(0, len) as usize;
    let end = end.max(start);
    let slice = &src[start..end];
    // SAFETY: `alloc_string` returned a fully initialized fresh RC=1 String.
    let result = unsafe { adopt_produced_value(alloc_string(slice.as_bytes()) as i64) };
    rc::consume_shallow(s);
    result
}

/// Return the character at byte index `idx` as a single-character string.
/// Returns an empty string if `idx` is out of bounds.
///
/// Decision 24: consuming convention — dec the heap arg.
pub(crate) fn str_char_at(s: Owned, idx: i64) -> Owned {
    let src = unsafe { read_str(s.as_borrowed()) };
    let idx = idx as usize;
    let raw = match src.get(idx..) {
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
    // SAFETY: every match arm returned one fully initialized fresh RC=1 String.
    let result = unsafe { adopt_produced_value(raw) };
    rc::consume_shallow(s);
    result
}

/// Split a string by a separator. Returns a Vec of heap strings.
///
/// Decision 24: consuming convention — dec both heap args.
pub(crate) fn str_split(s: Owned, sep: Owned) -> Owned {
    let src = unsafe { read_str(s.as_borrowed()) };
    let sep_str = unsafe { read_str(sep.as_borrowed()) };

    let elements = src
        .split(sep_str)
        .map(|part| {
            // SAFETY: `alloc_string` returned a fully initialized fresh RC=1 String.
            unsafe { adopt_produced_value(alloc_string(part.as_bytes()) as i64) }
        })
        .collect::<Vec<_>>();

    // SAFETY: every element is a fresh HeapString owned reference. Ownership
    // of each reference transfers exactly once into the returned Vec.
    let vec_base = vec_strings_from_owned_handles(elements);

    rc::consume_shallow(s);
    rc::consume_shallow(sep);
    vec_base
}

/// Join a Vec of strings with a separator. Separator is the first argument.
///
/// Decision 24: consuming convention — dec separator via `consume_shallow`
/// and the Vec via `consume_vec_of_string` (walks element Strings + frees
/// the Vec struct + data buffer).
pub(crate) fn str_join(sep: Owned, vec: Owned) -> Owned {
    let sep_str = unsafe { read_str(sep.as_borrowed()) };

    // SAFETY: `vec` is a live, immutable Vec-of-String for the duration of
    // the callback. The callback borrows element bases only; it performs no
    // retain, release, or ownership transfer for individual elements.
    let joined = unsafe {
        with_vec_strings(vec.raw_for_read(), |elements| {
            let parts = elements
                .iter()
                .map(|element| {
                    // SAFETY: `with_vec_strings` keeps each element live for this callback.
                    read_scoped_vec_string(*element)
                })
                .collect::<Vec<_>>();
            parts.join(sep_str)
        })
    };
    // The callback has returned, so the unsafe Vec-element slice borrow has
    // ended before this unrelated runtime allocation begins.
    // SAFETY: `alloc_string` returned a fully initialized fresh RC=1 String.
    let result = unsafe { adopt_produced_value(alloc_string(joined.as_bytes()) as i64) };

    rc::consume_shallow(sep);
    drop_glue::consume_vec_of_string(vec);

    result
}

/// Replace all occurrences of `from` with `to` in `s`. Returns a new string.
///
/// Decision 24: consuming convention — dec all three heap args.
pub(crate) fn str_replace(s: Owned, from: Owned, to: Owned) -> Owned {
    let src = unsafe { read_str(s.as_borrowed()) };
    let from_str = unsafe { read_str(from.as_borrowed()) };
    let to_str = unsafe { read_str(to.as_borrowed()) };
    let raw = alloc_string(src.replace(from_str, to_str).as_bytes()) as i64;
    // SAFETY: `alloc_string` returned a fully initialized fresh RC=1 String.
    let result = unsafe { adopt_produced_value(raw) };
    rc::consume_shallow(s);
    rc::consume_shallow(from);
    rc::consume_shallow(to);
    result
}

/// Trim leading and trailing whitespace. Returns a new string.
///
/// Decision 24: consuming convention — dec the heap arg.
pub(crate) fn str_trim(s: Owned) -> Owned {
    let src = unsafe { read_str(s.as_borrowed()) };
    // SAFETY: `alloc_string` returned a fully initialized fresh RC=1 String.
    let result = unsafe { adopt_produced_value(alloc_string(src.trim().as_bytes()) as i64) };
    rc::consume_shallow(s);
    result
}

/// Returns 1 if `s` starts with `prefix`, 0 otherwise.
///
/// Decision 24: consuming convention — dec both heap args.
pub(crate) fn str_starts_with(s: Owned, prefix: Owned) -> i64 {
    let src = unsafe { read_str(s.as_borrowed()) };
    let prefix_str = unsafe { read_str(prefix.as_borrowed()) };
    let result = if src.starts_with(prefix_str) { 1 } else { 0 };
    rc::consume_shallow(s);
    rc::consume_shallow(prefix);
    result
}

/// Returns 1 if `s` ends with `suffix`, 0 otherwise.
///
/// Decision 24: consuming convention — dec both heap args.
pub(crate) fn str_ends_with(s: Owned, suffix: Owned) -> i64 {
    let src = unsafe { read_str(s.as_borrowed()) };
    let suffix_str = unsafe { read_str(suffix.as_borrowed()) };
    let result = if src.ends_with(suffix_str) { 1 } else { 0 };
    rc::consume_shallow(s);
    rc::consume_shallow(suffix);
    result
}

/// Returns 1 if `s` contains `needle`, 0 otherwise.
///
/// Decision 24: consuming convention — dec both heap args.
pub(crate) fn str_contains(s: Owned, needle: Owned) -> i64 {
    let src = unsafe { read_str(s.as_borrowed()) };
    let needle_str = unsafe { read_str(needle.as_borrowed()) };
    let result = if src.contains(needle_str) { 1 } else { 0 };
    rc::consume_shallow(s);
    rc::consume_shallow(needle);
    result
}

/// Convert string to uppercase. Returns a new string.
///
/// Decision 24: consuming convention — dec the heap arg.
pub(crate) fn str_to_upper(s: Owned) -> Owned {
    let src = unsafe { read_str(s.as_borrowed()) };
    // SAFETY: `alloc_string` returned a fully initialized fresh RC=1 String.
    let result =
        unsafe { adopt_produced_value(alloc_string(src.to_uppercase().as_bytes()) as i64) };
    rc::consume_shallow(s);
    result
}

/// Convert string to lowercase. Returns a new string.
///
/// Decision 24: consuming convention — dec the heap arg.
pub(crate) fn str_to_lower(s: Owned) -> Owned {
    let src = unsafe { read_str(s.as_borrowed()) };
    // SAFETY: `alloc_string` returned a fully initialized fresh RC=1 String.
    let result =
        unsafe { adopt_produced_value(alloc_string(src.to_lowercase().as_bytes()) as i64) };
    rc::consume_shallow(s);
    result
}

/// Transfer fresh String children into the existing guarded raw Vec receiver.
fn vec_strings_from_owned_handles(elements: Vec<Owned>) -> Owned {
    let mut raw_elements = Vec::with_capacity(elements.len());
    for element in elements {
        raw_elements.push(element.into_raw());
    }
    // SAFETY: capacity was prepared before any child transfer. From function
    // entry the receiver guards every raw child through Vec construction.
    let raw_vec = unsafe { vec_strings_from_owned(raw_elements) };
    // SAFETY: the receiver returned one completed fresh RC=1 Vec.
    unsafe { adopt_produced_value(raw_vec) }
}

// Suppress unused-import warning when `alloc` is only referenced via test
// modules below.
#[allow(dead_code)]
fn _force_alloc_dep() {
    let _ = alloc::alloc_count;
}

#[cfg(test)]
mod tests;
