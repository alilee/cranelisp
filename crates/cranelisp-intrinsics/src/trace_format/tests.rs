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
