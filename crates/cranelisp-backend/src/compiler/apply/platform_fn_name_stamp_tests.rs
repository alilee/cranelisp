use super::{platform_fn_name_bytes, EFFECT_FN_NAME_ABS_OFFSET};
use cranelisp_types::HeapHeader;

// spec: design/arch/bounded-contexts.md §5 invariant 9 (S81 / FIXME 0327,
//       the fault-guarded dispatch funnel step 2/4) — the absolute byte
//       offset of the Effect node's fn-name field (field-3) MUST be composed
//       from the named ABI constants (HeapHeader::SIZE + the platform
//       payload offset), NEVER hard-coded. The Effect node base layout is
//       [HeapHeader(16) | tag | thunk_ptr | resource_token | fn_name_handle],
//       so field-3 sits at base+40. This pins the composition: if the header
//       size or the platform payload offset changes, this assertion catches
//       a stale hard-coded value.
#[test]
fn effect_fn_name_offset_is_composed_from_named_constants() {
    // Composed value equals header + payload offset.
    assert_eq!(
        EFFECT_FN_NAME_ABS_OFFSET,
        HeapHeader::SIZE as i64 + cranelisp_platform::IO_EFFECT_FN_NAME_OFFSET,
    );
    // And it lands one i64 past the resource token (base+40 today).
    assert_eq!(
        EFFECT_FN_NAME_ABS_OFFSET,
        HeapHeader::SIZE as i64 + cranelisp_platform::IO_EFFECT_RESOURCE_OFFSET + 8,
    );
}

// spec: design/arch/bounded-contexts.md §5 invariant 9 — the baked fn-name
//       handle is a NUL-terminated UTF-8 byte sequence (the C-string the
//       trampoline fault guard reads in step 3, degrading a null handle to
//       "<unknown>"). This is the same self-describing convention the
//       layout-hash gate bakes (exe.rs::define_cstr_data).
#[test]
fn baked_fn_name_is_nul_terminated_utf8() {
    let bytes = platform_fn_name_bytes("platform.shapes/rectangle-area");
    assert_eq!(*bytes.last().unwrap(), 0u8, "must be NUL-terminated");
    assert_eq!(
        &bytes[..bytes.len() - 1],
        b"platform.shapes/rectangle-area",
        "the name bytes precede the NUL terminator verbatim",
    );
    // An empty name still produces a valid (just-NUL) C string.
    assert_eq!(platform_fn_name_bytes(""), vec![0u8]);
}
