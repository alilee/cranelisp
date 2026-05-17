//! User-callable Vec primitives — primitives-surface presentation.
//!
//! Per Decision 43 + `design/arch/facades/primitives.md`: `vec-len` is the
//! kebab-case, user-addressable Vec read accessor. The Vec runtime helpers
//! (`vec_new`, `vec_drop`, `vec_set_copy`, `vec_push_copy`, `vec_push_grow`)
//! live in `cranelisp-intrinsics::vec_runtime` — they are backend-emitted-call
//! targets, not user-callable from source.
//!
//! ## FIXME 0180 close (Sprint 67 Wave 3 — physical relocation)
//!
//! `vec_len` physically lives here; no re-export from intrinsics. The Vec
//! layout offsets (`LEN_OFFSET` = 16) are duplicated here to avoid a
//! load-bearing import of intrinsics' layout constants. The duplication is
//! safe because the layout is fixed by Decision 11 (base-pointer ABI) and
//! the `HeapHeader` (`size: i64 @ +0`, `rc: i64 @ +8`) — `len` always lives
//! at `+16` from the base. A debug_assert at module load could verify this
//! against `cranelisp_intrinsics::vec_runtime`'s offsets, but a static const
//! assert is structurally simpler.

/// Offset of the `len` field from a Vec's base pointer.
///
/// Layout from base: `[size(i64) @ +0 | rc(i64) @ +8 | len(i64) @ +16 | cap(i64) @ +24 | data_ptr(i64) @ +32]`.
const LEN_OFFSET: usize = 16;

/// Read the length of a Vec.
///
/// JIT name: `vec-len` (exported via `export_name`).
#[unsafe(export_name = "vec-len")]
pub extern "C" fn vec_len(vec: i64) -> i64 {
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
