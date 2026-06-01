//! User-callable Vec primitives — primitives-surface presentation.
//!
//! Per Decision 43 + `design/arch/facades/primitives.md`: `vec-len` is the
//! kebab-case, user-addressable Vec read accessor. The Vec runtime helpers
//! (`vec_new`, `vec_drop`, `vec_set_copy`, `vec_push_copy`, `vec_push_grow`)
//! live in `cranelisp-intrinsics::vec_runtime` — they are backend-emitted-call
//! targets, not user-callable from source.
//!
//! ## FIXME 0180 / 0245 close (S67 Wave 3 relocation; S73 layout dedup)
//!
//! `vec_len` physically lives here; no re-export from intrinsics. The Vec
//! heap-layout offset is sourced exclusively from `cranelisp-intrinsics`'
//! blessed public layout ABI (`vec_runtime::LEN_OFFSET`, FIXME 0245) — no
//! local copy. Single source of truth (Principle 7).

use cranelisp_intrinsics::vec_runtime::LEN_OFFSET;

/// Read the length of a Vec.
///
/// JIT name: `vec-len` (exported via `export_name`).
#[unsafe(export_name = "vec-len")]
pub(crate) extern "C" fn vec_len(vec: i64) -> i64 {
    // SAFETY: `vec` is a valid Vec base pointer from JIT code; len field is at +16.
    unsafe { *((vec as *const u8).add(LEN_OFFSET) as *const i64) }
}

#[cfg(test)]
mod tests {
    use super::*;

    // spec: 12-runtime §12.1.5 — vec-len reads len at offset 16 from base
    #[test]
    fn vec_len_reads_field_at_offset_16() {
        // Simulate a Vec struct in memory: [size, rc, len, cap, data_ptr].
        let buf = [0i64, 0, 42, 0, 0];
        let base = buf.as_ptr() as i64;
        assert_eq!(vec_len(base), 42);
    }

    #[test]
    fn vec_len_zero_for_empty_vec() {
        let buf = [0i64, 0, 0, 0, 0];
        let base = buf.as_ptr() as i64;
        assert_eq!(vec_len(base), 0);
    }
}
