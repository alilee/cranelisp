//! Single-source heap-cell read/write primitives (MED-1, FIXME 0370).
//!
//! The bare "read/write an `i64` at a byte offset from a base pointer" operation
//! was open-coded across `trace.rs`, `io.rs`, `ivar.rs`, `panic.rs`, and
//! `alloc.rs` — each site re-deriving `*((base + off) as *const/*mut i64)`. This
//! module is the **single owner** of that mechanically-identical primitive
//! (Principle 7), keeping the `unsafe` raw-pointer arithmetic in one place
//! (improving the "find all unsafe in one location" property the unsafe-audit
//! rules want).
//!
//! Offsets are `isize` so both the signed indexing the IO trampoline uses
//! (`base + FIELD_1_OFFSET + i*8`) and the `usize` field offsets the trace
//! drop-glue uses (`off as isize`) route through the same helpers. The base is
//! `i64` because every heap value in this crate is carried as an `i64`
//! alloc-base pointer (the base-pointer convention, Decision 10/11).
//!
//! These helpers do NOT own the heap *header* layout — that single source is
//! [`cranelisp_types::HeapHeader`] (`SIZE` / `RC_OFFSET`), referenced by the
//! per-module layout constants. This module owns only the *accessor* over those
//! constants, which `bounded-contexts.md` §4b invariant 2 left without a single
//! owner (it names three layout-*constant* owners but no read/write accessor
//! owner). The *consuming* RC dec sequences (Release store + Acquire fence on
//! free) deliberately stay per-module — each owns distinct ownership semantics
//! (MED-1 recommendation 2) — and do NOT route through here.

/// Read an `i64` at a byte `offset` from base pointer `base`.
///
/// # Safety
/// `base` must be a valid pointer with at least `offset + 8` bytes readable.
#[inline]
pub(crate) unsafe fn read_i64(base: i64, offset: isize) -> i64 {
    unsafe { *((base as isize + offset) as *const i64) }
}

/// Write `value` as an `i64` at a byte `offset` from base pointer `base`.
///
/// # Safety
/// `base` must be a valid pointer with at least `offset + 8` bytes writable.
#[inline]
pub(crate) unsafe fn write_i64(base: i64, offset: isize, value: i64) {
    unsafe { *((base as isize + offset) as *mut i64) = value }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A round-trip through the shared accessor matches a hand-rolled raw read
    /// at the same offset — confirming the extracted primitive is the same
    /// mechanical operation the open-coded sites performed.
    #[test]
    fn write_then_read_round_trips_at_offset() {
        // A small i64-aligned buffer; treat its address as a heap base.
        let mut cells = [0i64; 4];
        let base = cells.as_mut_ptr() as i64;

        // Write distinct sentinels at offsets 8, 16, 24 (slots 1, 2, 3).
        unsafe {
            write_i64(base, 8, 0x1111);
            write_i64(base, 16, 0x2222);
            write_i64(base, 24, 0x3333);
        }

        // The shared reader returns what was written.
        assert_eq!(unsafe { read_i64(base, 8) }, 0x1111);
        assert_eq!(unsafe { read_i64(base, 16) }, 0x2222);
        assert_eq!(unsafe { read_i64(base, 24) }, 0x3333);

        // And agrees with a hand-rolled raw read (the open-coded form).
        let raw = unsafe { *((base as isize + 16) as *const i64) };
        assert_eq!(raw, 0x2222);

        // Slot 0 (offset 0) was never written.
        assert_eq!(unsafe { read_i64(base, 0) }, 0);
    }
}
