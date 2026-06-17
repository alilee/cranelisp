//! The pure, codegen-baked **value formatter** for `(trace ...)` (the
//! `DisplayDescriptor` ABI + [`cranelisp_trace_format`]).
//!
//! Split out of `trace.rs` (HIGH-3, FIXME 0370): this is the one self-contained,
//! *pure* protocol in the trace machinery. It shares ZERO state with the GOT-swap
//! / trace-stack / drop-glue code that remains in `trace.rs` — it is a pure walk
//! of a backend-baked descriptor blob against a runtime heap value, with no
//! symbol-table access and no thread-local state (BC §4b invariant 12).
//!
//! # DisplayDescriptor — the codegen-baked, self-contained value-render contract
//!
//! This is the cross-crate ABI between backend (the emitter — FIXME 0255) and
//! intrinsics (the reader — [`cranelisp_trace_format`], below). Backend bakes one
//! descriptor tree per traced param/result; `cranelisp_trace_format` walks it
//! against the runtime heap value with ZERO symbol-table access and NO
//! thread-local state. The full layout contract is documented on the types
//! below — read it before touching either side.

use std::ptr;

use crate::heap_string::alloc_string;

/// Heap-layout offset of an ADT's tag from its base pointer (base-pointer
/// convention, Decision 10): `[alloc_size(+0) | rc(+8) | tag(+16) | f0(+24) …]`.
const PAYLOAD_OFFSET: usize = 16;
/// Heap-layout offset of an ADT's first field from its base pointer.
const FIELD0_OFFSET: usize = 24;

/// Kind tag for a [`DisplayDescriptor`] (the `kind` field, an `i32`).
///
/// One discriminant per renderable value shape, mirroring `int`'s
/// `format_field_value` match. The numeric values are part of the cross-crate
/// ABI — backend bakes these integers; do not renumber without a coordinated
/// backend change (FIXME 0255).
///
/// # ABI: stable discriminants
/// `#[repr(i32)]` so the discriminant is a fixed-width field backend can emit
/// as a plain `iconst`.
#[repr(i32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DescriptorKind {
    /// Decimal integer. No children, no payload.
    Int = 0,
    /// `true` / `false`. No children, no payload.
    Bool = 1,
    /// `d.d` float (mandatory `.0`). No children, no payload.
    Float = 2,
    /// Quoted string (`"…"`). Value is a `HeapString` pointer. No children.
    String = 3,
    /// `<closure>`. No children, no payload.
    Fn = 4,
    /// `[e1 e2 …]`. Exactly ONE child descriptor (the element renderer);
    /// `child0` is its self-relative offset. Value is a `HeapVec` pointer.
    Vec = 5,
    /// `Type.Ctor` (nullary) / `(Type.Ctor f1 f2 …)` (data) per spec §1.5.
    /// Carries the type-name string + a per-constructor table baked into the
    /// blob; see [`DisplayDescriptor`] for the Adt encoding.
    Adt = 6,
    /// Residual type variable — bare `value` fallback. A monomorphic trace
    /// should not hit this (backend bakes the substituted concrete descriptor);
    /// it exists as a defensive default. No children.
    TypeVar = 7,
}

/// One node in a baked display descriptor (the `#[repr(C)]` cross-crate ABI).
///
/// # Encoding overview — ONE encoding for BOTH modes
///
/// A descriptor TREE is laid out as a flat, **position-independent arena blob**:
/// a contiguous byte buffer holding descriptor records and the variable-length
/// data they reference (string bytes, constructor tables). Every cross-reference
/// inside the blob is a **self-relative byte offset** — an `i32` measured from
/// the address of the offset field itself — NOT an absolute pointer. The blob
/// therefore contains no absolute addresses and needs **no intra-blob
/// relocations**; it is identical in JIT mode (leaked `Box<[u8]>`, address
/// embedded as an `iconst`) and object mode (a `.rodata` data symbol, one
/// relocation for the wrapper's reference to the blob root). This is the single
/// encoding `/arch` blessed (`tracing.md` §3.4 "arena blob with offset-relative
/// child links"). `cranelisp_trace_format` receives a pointer to ONE
/// `DisplayDescriptor` record (the blob root for that value) and follows the
/// self-relative offsets to reach children/strings/ctor-tables.
///
/// **Self-relative offset convention (the single rule).** A field of type
/// "self-relative offset" holds an `i32`. The referent address is
/// `(&field as *const i32 as isize + offset as isize) as *const T`. A `0`
/// offset means "absent" (no child / no string / empty table). Because the
/// offset is measured from the field's own address, the same encoded blob
/// works no matter where the blob is loaded — JIT heap or `.rodata`.
///
/// # Record layout (`#[repr(C)]`, all fields naturally aligned)
///
/// | Offset | Field        | Type  | Meaning |
/// |-------:|--------------|-------|---------|
/// | 0      | `kind`       | `i32` | [`DescriptorKind`] discriminant. |
/// | 4      | `_pad`       | `i32` | Reserved (zero); keeps `name_off` 8-aligned-friendly and the record a round 24 bytes. |
/// | 8      | `name_off`   | `i32` | Self-relative offset to a `BlobStr` (the type name, Adt only; `0` otherwise). |
/// | 12     | `child0_off` | `i32` | Self-relative offset to the first/only child descriptor (`Vec` element; `0` otherwise). |
/// | 16     | `ctors_off`  | `i32` | Self-relative offset to a `CtorTable` (Adt only; `0` otherwise). |
/// | 20     | `_pad2`      | `i32` | Reserved (zero). |
///
/// `size_of::<DisplayDescriptor>() == 24`, `align_of == 4`. Backend MUST emit
/// records at 4-byte-aligned blob offsets.
///
/// # `BlobStr` — a length-prefixed byte string inside the blob
///
/// A `BlobStr` is `[ len: i32 | bytes: [u8; len] ]` (NOT NUL-terminated —
/// length-prefixed, so embedded NULs and exact byte counts are safe). It is
/// referenced by a self-relative offset (to the `len` field). The bytes are
/// raw UTF-8.
///
/// # `CtorTable` — the Adt per-constructor table inside the blob
///
/// Referenced from `ctors_off`. Layout:
/// `[ n_ctors: i32 | single_match: i32 | CtorEntry[n_ctors] ]` where
/// `single_match` is `1` iff the type has exactly one constructor whose name
/// equals the type name (the `Type.` prefix is suppressed per spec §1.5), else
/// `0`. Each `CtorEntry` is:
/// `[ tag: i32 | n_fields: i32 | name_off: i32 | fields_off: i32 ]`
/// — `tag` is the runtime constructor tag, `name_off` is a self-relative offset
/// (from the `CtorEntry`'s `name_off` field) to a `BlobStr` (ctor name), and
/// `fields_off` is a self-relative offset (from the `CtorEntry`'s `fields_off`
/// field) to an array of `n_fields` self-relative `i32` offsets, each pointing
/// to that field's child [`DisplayDescriptor`]. (The two-level indirection
/// keeps every cross-link a self-relative `i32`.)
///
/// # Lifetime
///
/// Descriptors are program-lifetime (JIT: leaked; object: static `.rodata`),
/// never freed. `cranelisp_trace_format` only reads them.
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct DisplayDescriptor {
    /// [`DescriptorKind`] discriminant.
    pub kind: i32,
    /// Reserved (zero).
    pub _pad: i32,
    /// Self-relative offset to the type-name `BlobStr` (Adt only; else 0).
    pub name_off: i32,
    /// Self-relative offset to the first/only child descriptor (Vec element;
    /// else 0).
    pub child0_off: i32,
    /// Self-relative offset to the `CtorTable` (Adt only; else 0).
    pub ctors_off: i32,
    /// Reserved (zero).
    pub _pad2: i32,
}

const _: () = assert!(std::mem::size_of::<DisplayDescriptor>() == 24);
const _: () = assert!(std::mem::align_of::<DisplayDescriptor>() == 4);

// ── Self-relative-offset readers (the blob-walk primitives) ────────────────────

/// Resolve a self-relative offset stored at `field_ptr` to a typed pointer.
/// Returns `None` when the offset is 0 ("absent").
///
/// # Safety
/// `field_ptr` must point to a valid `i32` inside a descriptor blob, and the
/// referent (if the offset is non-zero) must be a valid `T` inside the same
/// blob.
unsafe fn follow_self_rel<T>(field_ptr: *const i32) -> Option<*const T> {
    let off = unsafe { *field_ptr };
    if off == 0 {
        return None;
    }
    let base = field_ptr as isize;
    Some((base + off as isize) as *const T)
}

/// Read a `BlobStr` (`[len:i32 | bytes]`) at `ptr` as a `&str`.
///
/// # Safety
/// `ptr` must point to a valid `BlobStr` inside a descriptor blob.
unsafe fn read_blob_str<'a>(ptr: *const i32) -> &'a str {
    let len = unsafe { *ptr } as usize;
    let bytes = unsafe { std::slice::from_raw_parts(ptr.add(1) as *const u8, len) };
    // Backend bakes valid UTF-8 (type/constructor names are Rust strings).
    std::str::from_utf8(bytes).unwrap_or("<bad-utf8>")
}

// ── The pure descriptor-driven formatter ───────────────────────────────────────

/// Format a runtime value as a cranelisp heap String, driven entirely by a
/// backend-baked [`DisplayDescriptor`].
///
/// `value` is the runtime value (an `i64` scalar or a heap pointer);
/// `descriptor_ptr` is a `*const DisplayDescriptor` (the blob root for this
/// value's static type). Returns a heap `String` (alloc-base pointer, RC=1) —
/// the same shape `alloc_string` produces.
///
/// **Purity (BC §4b invariant 12).** This intrinsic performs ZERO symbol-table
/// access and holds NO thread-local state. Everything `format_value` used to
/// resolve from the live `symbol_tables` (ADT constructor names, field layouts,
/// single-ctor suppression) is baked into the descriptor at codegen. It reuses
/// only the heap-layout reads intrinsics already owns (`HeapString` len/bytes,
/// `HeapVec` len/data, the base-pointer ADT tag/field offsets).
///
/// Arity is `(2, true)` — backend's `declare_trace_extern("cranelisp_trace_format",
/// 2, true)` is unchanged.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_trace_format(value: i64, descriptor_ptr: i64) -> i64 {
    let s = if descriptor_ptr == 0 {
        // Defensive: no descriptor -> bare value.
        format!("{value}")
    } else {
        // SAFETY: backend guarantees descriptor_ptr is a valid blob-root
        // DisplayDescriptor for the static type of `value`.
        unsafe { render_value(value, descriptor_ptr as *const DisplayDescriptor) }
    };
    alloc_string(s.as_bytes()) as i64
}

/// Render `value` per `desc` to a Rust `String` (no `:Type` prefix).
///
/// # Safety
/// `desc` must point to a valid [`DisplayDescriptor`] blob root, and `value`
/// must be consistent with that descriptor's kind (scalar or the right heap
/// shape).
unsafe fn render_value(value: i64, desc: *const DisplayDescriptor) -> String {
    let kind = unsafe { (*desc).kind };
    match kind {
        k if k == DescriptorKind::Int as i32 => format!("{value}"),
        k if k == DescriptorKind::Bool as i32 => {
            if value != 0 { "true".to_string() } else { "false".to_string() }
        }
        k if k == DescriptorKind::Float as i32 => {
            let f = f64::from_bits(value as u64);
            let s = format!("{f}");
            if s.contains('.') { s } else { format!("{s}.0") }
        }
        k if k == DescriptorKind::String as i32 => {
            if value == 0 || (value as usize) < cranelisp_types::NULLARY_TAG_THRESHOLD {
                format!("<invalid-string:{value}>")
            } else {
                // SAFETY: value is a heap HeapString pointer (guarded above).
                let s = unsafe { crate::heap_string::read_string_as_str(value) };
                format!("\"{s}\"")
            }
        }
        k if k == DescriptorKind::Fn as i32 => "<closure>".to_string(),
        k if k == DescriptorKind::Vec as i32 => unsafe { render_vec(value, desc) },
        k if k == DescriptorKind::Adt as i32 => unsafe { render_adt(value, desc) },
        // TypeVar (residual) and any unknown kind: bare value fallback.
        _ => format!("{value}"),
    }
}

/// Render a `HeapVec` value as `[e1 e2 …]` using the single child descriptor.
///
/// # Safety
/// `desc.kind == Vec`; `value` is a `HeapVec` pointer or nullary.
unsafe fn render_vec(value: i64, desc: *const DisplayDescriptor) -> String {
    if value == 0 || (value as usize) < cranelisp_types::NULLARY_TAG_THRESHOLD {
        return "[]".to_string();
    }
    let base = value as *const u8;
    // SAFETY: value is a heap HeapVec pointer (guarded above).
    let len = unsafe {
        *(base.add(crate::vec_runtime::LEN_OFFSET) as *const i64)
    } as usize;
    if len == 0 {
        return "[]".to_string();
    }
    let data_ptr = unsafe {
        *(base.add(crate::vec_runtime::DATA_PTR_OFFSET) as *const *const i64)
    };
    if data_ptr.is_null() {
        return "[]".to_string();
    }
    // Resolve the element child descriptor (self-relative from child0_off).
    let child0_field = unsafe { ptr::addr_of!((*desc).child0_off) };
    let elem_desc: Option<*const DisplayDescriptor> =
        unsafe { follow_self_rel(child0_field) };
    let mut elems = Vec::with_capacity(len);
    for i in 0..len {
        let elem_val = unsafe { *data_ptr.add(i) };
        let formatted = match elem_desc {
            Some(ed) => unsafe { render_value(elem_val, ed) },
            None => format!("{elem_val}"),
        };
        elems.push(formatted);
    }
    format!("[{}]", elems.join(" "))
}

/// Render an Adt value per spec §1.5 using the baked constructor table.
///
/// Nullary: `Type.Ctor` (or bare `Ctor` if single-match). Data:
/// `(Type.Ctor f1 f2 …)` (or `(Ctor …)` if single-match).
///
/// # Safety
/// `desc.kind == Adt`; `value` is a nullary tag or a `HeapAdt` pointer.
unsafe fn render_adt(value: i64, desc: *const DisplayDescriptor) -> String {
    // Type name (for the Type.Ctor prefix). May be absent defensively.
    let name_field = unsafe { ptr::addr_of!((*desc).name_off) };
    let type_name: &str = match unsafe { follow_self_rel::<i32>(name_field) } {
        Some(p) => unsafe { read_blob_str(p) },
        None => "",
    };

    // Constructor table.
    let ctors_field = unsafe { ptr::addr_of!((*desc).ctors_off) };
    let Some(ctab) = (unsafe { follow_self_rel::<i32>(ctors_field) }) else {
        // No ctor table -> bare value fallback.
        return format!("{value}");
    };
    // CtorTable: [ n_ctors:i32 | single_match:i32 | CtorEntry[n] ]
    let n_ctors = unsafe { *ctab } as usize;
    let single_match = unsafe { *ctab.add(1) } != 0;
    // CtorEntry stride = 4 i32s (tag, n_fields, name_off, fields_off).
    let entries_base = unsafe { ctab.add(2) };

    let is_nullary = (value as usize) < cranelisp_types::NULLARY_TAG_THRESHOLD;
    let runtime_tag: i64 = if is_nullary {
        value
    } else {
        // Heap ADT: tag at PAYLOAD_OFFSET (16).
        unsafe { *((value as *const u8).add(PAYLOAD_OFFSET) as *const i64) }
    };

    // Find the CtorEntry whose tag matches.
    let mut found: Option<*const i32> = None;
    for i in 0..n_ctors {
        let entry = unsafe { entries_base.add(i * 4) };
        let tag = unsafe { *entry } as i64;
        if tag == runtime_tag {
            found = Some(entry);
            break;
        }
    }
    let Some(entry) = found else {
        return format!("<unknown-tag:{runtime_tag}>");
    };
    let n_fields = unsafe { *entry.add(1) } as usize;
    let ctor_name_field = unsafe { entry.add(2) };
    let ctor_name: &str = match unsafe { follow_self_rel::<i32>(ctor_name_field) } {
        Some(p) => unsafe { read_blob_str(p) },
        None => "<ctor>",
    };

    let ctor_display = if single_match {
        ctor_name.to_string()
    } else {
        format!("{type_name}.{ctor_name}")
    };

    if n_fields == 0 || is_nullary {
        // Nullary constructor: just the constructor display.
        return ctor_display;
    }

    // Data constructor: read each field + its child descriptor.
    let fields_off_field = unsafe { entry.add(3) };
    let Some(field_offs) = (unsafe { follow_self_rel::<i32>(fields_off_field) }) else {
        return ctor_display;
    };
    let mut field_strs = Vec::with_capacity(n_fields);
    for i in 0..n_fields {
        // field_offs[i] is a self-relative offset (from its own address) to the
        // field's child DisplayDescriptor.
        let off_field = unsafe { field_offs.add(i) };
        let field_desc: Option<*const DisplayDescriptor> =
            unsafe { follow_self_rel(off_field) };
        // Field value at FIELD0_OFFSET + i*8 of the heap ADT.
        let field_val = unsafe {
            *((value as *const u8).add(FIELD0_OFFSET + i * 8) as *const i64)
        };
        let s = match field_desc {
            Some(fd) => unsafe { render_value(field_val, fd) },
            None => format!("{field_val}"),
        };
        field_strs.push(s);
    }
    format!("({ctor_display} {})", field_strs.join(" "))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::alloc::alloc_with_rc;

    /// Allocate a base-pointer ADT cell `[alloc_size | rc=1 | tag | f0 | f1 …]`
    /// for the formatter tests (a local minimal copy of trace.rs's `alloc_adt`,
    /// kept here so the formatter's tests are self-contained).
    fn alloc_adt(tag: i64, fields: &[i64]) -> i64 {
        let payload_size = (1 + fields.len()) * 8;
        let base = alloc_with_rc(payload_size) as i64;
        unsafe {
            *((base as *mut u8).add(PAYLOAD_OFFSET) as *mut i64) = tag;
            for (i, &field) in fields.iter().enumerate() {
                *((base as *mut u8).add(FIELD0_OFFSET + i * 8) as *mut i64) = field;
            }
        }
        base
    }

    // ── DisplayDescriptor — blob-building helpers for tests ───────────────────
    //
    // These build descriptor blobs *by hand* into a Vec<u8>, exactly as backend
    // (FIXME 0255) will, then exercise `cranelisp_trace_format` against them.
    // The builder mirrors the documented arena-blob encoding: records and data
    // packed contiguously, cross-links as self-relative i32 offsets.

    /// A tiny arena-blob builder. All cross-links use self-relative i32 offsets.
    struct BlobBuilder {
        buf: Vec<u8>,
    }

    impl BlobBuilder {
        fn new() -> Self {
            BlobBuilder { buf: Vec::new() }
        }

        fn align4(&mut self) {
            while !self.buf.len().is_multiple_of(4) {
                self.buf.push(0);
            }
        }

        fn pos(&self) -> usize {
            self.buf.len()
        }

        /// Reserve a 24-byte descriptor record, return its offset.
        fn reserve_desc(&mut self) -> usize {
            self.align4();
            let at = self.buf.len();
            self.buf.extend_from_slice(&[0u8; 24]);
            at
        }

        fn write_i32(&mut self, at: usize, v: i32) {
            self.buf[at..at + 4].copy_from_slice(&v.to_le_bytes());
        }

        /// Set a descriptor field to a self-relative offset pointing at `target`.
        /// `field_index` is 0=kind,1=_pad,2=name_off,3=child0_off,4=ctors_off,5=_pad2.
        fn set_desc_kind(&mut self, desc_at: usize, kind: DescriptorKind) {
            self.write_i32(desc_at, kind as i32);
        }

        fn set_self_rel(&mut self, field_at: usize, target_at: usize) {
            let rel = target_at as isize - field_at as isize;
            self.write_i32(field_at, rel as i32);
        }

        /// Append a BlobStr ([len:i32 | bytes]); return its offset.
        fn append_str(&mut self, s: &str) -> usize {
            self.align4();
            let at = self.buf.len();
            self.buf.extend_from_slice(&(s.len() as i32).to_le_bytes());
            self.buf.extend_from_slice(s.as_bytes());
            at
        }

        /// Pointer to the blob root (after building). The Vec must outlive use.
        fn root_ptr(&self) -> *const DisplayDescriptor {
            self.buf.as_ptr() as *const DisplayDescriptor
        }

        fn ptr_at(&self, at: usize) -> *const DisplayDescriptor {
            unsafe { self.buf.as_ptr().add(at) as *const DisplayDescriptor }
        }
    }

    /// Read back the heap String produced by `cranelisp_trace_format`.
    fn read_format_result(value: i64, desc_ptr: i64) -> String {
        let s_heap = cranelisp_trace_format(value, desc_ptr);
        let s = unsafe { crate::heap_string::read_string_as_str(s_heap) }.to_string();
        unsafe { crate::alloc::dealloc(s_heap as *mut u8) };
        s
    }

    // spec: spec/04-expressions.md §4.12.2 / §12.9 — scalar trace formatting
    #[test]
    fn descriptor_int() {
        let mut b = BlobBuilder::new();
        let d = b.reserve_desc();
        b.set_desc_kind(d, DescriptorKind::Int);
        assert_eq!(read_format_result(42, b.root_ptr() as i64), "42");
        assert_eq!(read_format_result(-7, b.root_ptr() as i64), "-7");
    }

    #[test]
    fn descriptor_bool() {
        let mut b = BlobBuilder::new();
        let d = b.reserve_desc();
        b.set_desc_kind(d, DescriptorKind::Bool);
        assert_eq!(read_format_result(1, b.root_ptr() as i64), "true");
        assert_eq!(read_format_result(0, b.root_ptr() as i64), "false");
    }

    #[test]
    fn descriptor_float() {
        let mut b = BlobBuilder::new();
        let d = b.reserve_desc();
        b.set_desc_kind(d, DescriptorKind::Float);
        let bits = 1.0_f64.to_bits() as i64;
        assert_eq!(read_format_result(bits, b.root_ptr() as i64), "1.0");
        let bits2 = 3.5_f64.to_bits() as i64;
        assert_eq!(read_format_result(bits2, b.root_ptr() as i64), "3.5");
    }

    #[test]
    fn descriptor_string() {
        let mut b = BlobBuilder::new();
        let d = b.reserve_desc();
        b.set_desc_kind(d, DescriptorKind::String);
        let heap_s = alloc_string(b"hello") as i64;
        assert_eq!(read_format_result(heap_s, b.root_ptr() as i64), "\"hello\"");
        unsafe { crate::alloc::dealloc(heap_s as *mut u8) };
    }

    #[test]
    fn descriptor_fn() {
        let mut b = BlobBuilder::new();
        let d = b.reserve_desc();
        b.set_desc_kind(d, DescriptorKind::Fn);
        assert_eq!(read_format_result(0, b.root_ptr() as i64), "<closure>");
    }

    #[test]
    fn descriptor_typevar_fallback() {
        let mut b = BlobBuilder::new();
        let d = b.reserve_desc();
        b.set_desc_kind(d, DescriptorKind::TypeVar);
        assert_eq!(read_format_result(99, b.root_ptr() as i64), "99");
    }

    // spec: spec/04-expressions.md §12.9 — Vec element formatting
    #[test]
    fn descriptor_vec_of_int() {
        // Build blob: [ root(Vec) | child(Int) ].
        let mut b = BlobBuilder::new();
        let root = b.reserve_desc();
        let child = b.reserve_desc();
        b.set_desc_kind(root, DescriptorKind::Vec);
        b.set_desc_kind(child, DescriptorKind::Int);
        // child0_off is field index 3 -> byte offset root + 12.
        b.set_self_rel(root + 12, child);

        // Build a HeapVec of [1, 2, 3].
        let vec_ptr = crate::vec_runtime::vec_new(3);
        let v = crate::vec_runtime::vec_push_grow(vec_ptr, 1);
        let v = crate::vec_runtime::vec_push_grow(v, 2);
        let v = crate::vec_runtime::vec_push_grow(v, 3);

        let out = read_format_result(v, b.ptr_at(root) as i64);
        assert_eq!(out, "[1 2 3]");
        crate::vec_runtime::vec_drop(v, 0);
    }

    #[test]
    fn descriptor_vec_empty() {
        let mut b = BlobBuilder::new();
        let root = b.reserve_desc();
        let child = b.reserve_desc();
        b.set_desc_kind(root, DescriptorKind::Vec);
        b.set_desc_kind(child, DescriptorKind::Int);
        b.set_self_rel(root + 12, child);
        let vec_ptr = crate::vec_runtime::vec_new(0);
        assert_eq!(read_format_result(vec_ptr, b.ptr_at(root) as i64), "[]");
        crate::vec_runtime::vec_drop(vec_ptr, 0);
    }

    // spec: spec/04-expressions.md §1.5 — ADT constructor dot notation
    //
    // Builds a `(deftype Color Red Green Blue)`-style nullary enum descriptor
    // plus a `(deftype (Option a) None (Some [:a val]))`-style nested data ADT
    // to exercise both the nullary and data paths + nesting.
    #[test]
    fn descriptor_adt_nullary_enum() {
        // type Color { Red=0, Green=1, Blue=2 } — multi-ctor, no single-match.
        let mut b = BlobBuilder::new();
        let root = b.reserve_desc();
        b.set_desc_kind(root, DescriptorKind::Adt);
        let type_name = b.append_str("Color");
        // CtorTable: [n_ctors=3 | single_match=0 | 3 x CtorEntry(4 i32)].
        b.align4();
        let ctab = b.pos();
        b.buf.extend_from_slice(&3i32.to_le_bytes()); // n_ctors
        b.buf.extend_from_slice(&0i32.to_le_bytes()); // single_match
        // Reserve 3 entries (4 i32 each).
        let entries_at = b.pos();
        b.buf.extend_from_slice(&[0u8; 3 * 16]);
        // Names.
        let red = b.append_str("Red");
        let green = b.append_str("Green");
        let blue = b.append_str("Blue");
        // Fill entries: tag, n_fields=0, name_off (self-rel), fields_off=0.
        for (i, (tag, name_at)) in [(0, red), (1, green), (2, blue)].iter().enumerate() {
            let e = entries_at + i * 16;
            b.write_i32(e, *tag); // tag
            b.write_i32(e + 4, 0); // n_fields
            b.set_self_rel(e + 8, *name_at); // name_off
            b.write_i32(e + 12, 0); // fields_off
        }
        // Link root.name_off (offset root+8) and root.ctors_off (offset root+16).
        b.set_self_rel(root + 8, type_name);
        b.set_self_rel(root + 16, ctab);

        assert_eq!(read_format_result(0, b.ptr_at(root) as i64), "Color.Red");
        assert_eq!(read_format_result(1, b.ptr_at(root) as i64), "Color.Green");
        assert_eq!(read_format_result(2, b.ptr_at(root) as i64), "Color.Blue");
    }

    #[test]
    fn descriptor_adt_nested_data() {
        // type Option a { None=0, Some(a)=1 }, instantiated at Int.
        // We render `(Some 42)`.
        let mut b = BlobBuilder::new();
        let root = b.reserve_desc();
        let int_field = b.reserve_desc(); // descriptor for the Some field (Int)
        b.set_desc_kind(root, DescriptorKind::Adt);
        b.set_desc_kind(int_field, DescriptorKind::Int);
        let type_name = b.append_str("Option");
        // CtorTable: [n=2 | single_match=0 | 2 entries].
        b.align4();
        let ctab = b.pos();
        b.buf.extend_from_slice(&2i32.to_le_bytes());
        b.buf.extend_from_slice(&0i32.to_le_bytes());
        let entries_at = b.pos();
        b.buf.extend_from_slice(&[0u8; 2 * 16]);
        let none_name = b.append_str("None");
        let some_name = b.append_str("Some");
        // Some has 1 field -> a fields_off array of 1 self-rel i32.
        b.align4();
        let some_fields = b.pos();
        b.buf.extend_from_slice(&0i32.to_le_bytes()); // placeholder for field0 off
        // field0 self-rel -> int_field descriptor.
        b.set_self_rel(some_fields, int_field);

        // Entry 0: None tag=0 n_fields=0.
        let e0 = entries_at;
        b.write_i32(e0, 0);
        b.write_i32(e0 + 4, 0);
        b.set_self_rel(e0 + 8, none_name);
        b.write_i32(e0 + 12, 0);
        // Entry 1: Some tag=1 n_fields=1.
        let e1 = entries_at + 16;
        b.write_i32(e1, 1);
        b.write_i32(e1 + 4, 1);
        b.set_self_rel(e1 + 8, some_name);
        b.set_self_rel(e1 + 12, some_fields);

        b.set_self_rel(root + 8, type_name);
        b.set_self_rel(root + 16, ctab);

        // None is nullary tag 0.
        assert_eq!(read_format_result(0, b.ptr_at(root) as i64), "Option.None");

        // Build a heap (Some 42): [hdr | tag=1 | field0=42].
        let some_val = alloc_adt(1, &[42]);
        assert_eq!(
            read_format_result(some_val, b.ptr_at(root) as i64),
            "(Option.Some 42)"
        );
        // The Some cell holds an Int field (not heap), free the cell directly.
        unsafe { crate::alloc::dealloc(some_val as *mut u8) };
    }

    #[test]
    fn descriptor_adt_single_match_product() {
        // type Point { Point(Int, Int) } — single ctor whose name == type name.
        // single_match=1 suppresses the `Point.` prefix -> `(Point 3 4)`.
        let mut b = BlobBuilder::new();
        let root = b.reserve_desc();
        let f0 = b.reserve_desc();
        let f1 = b.reserve_desc();
        b.set_desc_kind(root, DescriptorKind::Adt);
        b.set_desc_kind(f0, DescriptorKind::Int);
        b.set_desc_kind(f1, DescriptorKind::Int);
        let type_name = b.append_str("Point");
        b.align4();
        let ctab = b.pos();
        b.buf.extend_from_slice(&1i32.to_le_bytes()); // n_ctors
        b.buf.extend_from_slice(&1i32.to_le_bytes()); // single_match = 1
        let entries_at = b.pos();
        b.buf.extend_from_slice(&[0u8; 16]);
        let point_name = b.append_str("Point");
        b.align4();
        let fields = b.pos();
        b.buf.extend_from_slice(&[0u8; 8]); // 2 field offsets
        b.set_self_rel(fields, f0);
        b.set_self_rel(fields + 4, f1);
        // Entry 0: Point tag=0 n_fields=2.
        b.write_i32(entries_at, 0);
        b.write_i32(entries_at + 4, 2);
        b.set_self_rel(entries_at + 8, point_name);
        b.set_self_rel(entries_at + 12, fields);
        b.set_self_rel(root + 8, type_name);
        b.set_self_rel(root + 16, ctab);

        let pt = alloc_adt(0, &[3, 4]);
        assert_eq!(read_format_result(pt, b.ptr_at(root) as i64), "(Point 3 4)");
        unsafe { crate::alloc::dealloc(pt as *mut u8) };
    }

    // ── Self-relative offset round-trip ───────────────────────────────────────

    #[test]
    fn self_rel_offset_round_trip() {
        // Two descriptors; parent's child0_off self-rel-points to child.
        let mut b = BlobBuilder::new();
        let parent = b.reserve_desc();
        let child = b.reserve_desc();
        b.set_desc_kind(parent, DescriptorKind::Vec);
        b.set_desc_kind(child, DescriptorKind::Int);
        b.set_self_rel(parent + 12, child); // child0_off

        let parent_ptr = b.ptr_at(parent);
        let child0_field = unsafe { ptr::addr_of!((*parent_ptr).child0_off) };
        let resolved: Option<*const DisplayDescriptor> =
            unsafe { follow_self_rel(child0_field) };
        let resolved = resolved.expect("child0 offset must resolve");
        // Resolved pointer must equal the child descriptor's address, and have
        // kind Int.
        assert_eq!(resolved as usize, b.ptr_at(child) as usize);
        assert_eq!(unsafe { (*resolved).kind }, DescriptorKind::Int as i32);
    }

    #[test]
    fn self_rel_zero_is_absent() {
        let mut b = BlobBuilder::new();
        let d = b.reserve_desc();
        b.set_desc_kind(d, DescriptorKind::Vec);
        // child0_off left 0.
        let dptr = b.ptr_at(d);
        let field = unsafe { ptr::addr_of!((*dptr).child0_off) };
        let resolved: Option<*const DisplayDescriptor> =
            unsafe { follow_self_rel(field) };
        assert!(resolved.is_none(), "zero offset means absent");
    }

    #[test]
    fn descriptor_repr_is_24_bytes() {
        // Pins the cross-crate ABI record size + alignment (backend reads it).
        assert_eq!(std::mem::size_of::<DisplayDescriptor>(), 24);
        assert_eq!(std::mem::align_of::<DisplayDescriptor>(), 4);
    }
}
