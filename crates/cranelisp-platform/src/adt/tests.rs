use super::*;
use crate::CLInt;

// Install a schema for the test process. OnceLock means the first install
// in this test binary wins; all fixtures share one combined schema.
fn ensure_test_schema() {
    let artifact = "\
;; layout-hash: test
(schema
  (shapes/Rectangle
    (Rectangle 0 ((w primitives/Int) (h primitives/Int))))
  (shapes/OptionInt
    (None 0 ())
    (Some 1 ((val primitives/Int)))))";
    let schema = Schema::parse(artifact).expect("test schema parses");
    set_global_schema(schema);
}

/// Allocate a synthetic full heap-ADT:
///   `[alloc_size: i64][rc: i64][tag: u32][pad: u32][field0: i64]…`
/// at the returned alloc base. Free via `free_cladt_payload`.
fn alloc_cladt_payload(tag: u32, fields: &[i64]) -> i64 {
    let payload_size = 8 + fields.len() * 8;
    let total_size = 16 + payload_size;
    // SAFETY: standard allocator path; layout aligned to 8.
    unsafe {
        let layout = std::alloc::Layout::from_size_align_unchecked(total_size, 8);
        let base = std::alloc::alloc_zeroed(layout);
        *(base as *mut i64) = total_size as i64;
        *((base as *mut i64).add(1)) = 1;
        let payload = base.add(16);
        *(payload as *mut u32) = tag;
        *(payload.add(4) as *mut u32) = 0;
        for (i, val) in fields.iter().enumerate() {
            *((payload.add(8 + i * 8)) as *mut i64) = *val;
        }
        base as i64
    }
}

fn free_cladt_payload(base: i64, field_count: usize) {
    let payload_size = 8 + field_count * 8;
    let total_size = 16 + payload_size;
    unsafe {
        let layout = std::alloc::Layout::from_size_align_unchecked(total_size, 8);
        std::alloc::dealloc(base as *mut u8, layout);
    }
}

struct Rectangle;
impl CLAdtType for Rectangle {
    const TYPE_NAME: &'static str = "shapes/Rectangle";
}

struct OptionInt;
impl CLAdtType for OptionInt {
    const TYPE_NAME: &'static str = "shapes/OptionInt";
}

// spec: design/arch/platform-interface.md §5.5 — read_tag is a fixed
// offset-0 read, no schema lookup, no callback.
#[test]
fn read_tag_fixed_offset_no_callback() {
    let payload = alloc_cladt_payload(42, &[]);
    let r: CLAdt<Rectangle> = CLAdt::from_raw(payload);
    assert_eq!(r.read_tag(), 42);
    free_cladt_payload(payload, 0);
}

// spec: design/arch/platform-interface.md §5.5 — read_field on a product
// resolves byte offsets BY NAME from the embedded schema.
#[test]
fn read_field_product_by_name() {
    ensure_test_schema();
    let payload = alloc_cladt_payload(0, &[3, 4]);
    let r: CLAdt<Rectangle> = CLAdt::from_raw(payload);
    assert_eq!(i64::from(r.read_field::<CLInt>("w")), 3);
    assert_eq!(i64::from(r.read_field::<CLInt>("h")), 4);
    // Self-qualified product field works too.
    assert_eq!(i64::from(r.read_field::<CLInt>("Rectangle.w")), 3);
    free_cladt_payload(payload, 2);
}

// spec: design/arch/platform-interface.md §5.5 — sum-type field access is
// dot-qualified by constructor name.
#[test]
fn read_field_sum_dot_qualified() {
    ensure_test_schema();
    let payload = alloc_cladt_payload(1, &[7]);
    let opt: CLAdt<OptionInt> = CLAdt::from_raw(payload);
    assert_eq!(opt.read_tag(), 1);
    assert_eq!(i64::from(opt.read_field::<CLInt>("Some.val")), 7);
    free_cladt_payload(payload, 1);
}

// spec: design/arch/platform-interface.md §5.5 — a witness mismatch panics.
#[test]
#[should_panic(expected = "witness mismatch")]
fn field_type_witness_mismatch_panics() {
    ensure_test_schema();
    let payload = alloc_cladt_payload(0, &[3, 4]);
    let r: CLAdt<Rectangle> = CLAdt::from_raw(payload);
    let _ = r.read_field::<crate::CLBool>("w");
}

// spec: design/arch/platform-interface.md §5.5 — an unqualified field on a
// sum is rejected (ambiguous).
#[test]
#[should_panic(expected = "schema lookup miss")]
fn sum_unqualified_field_rejected() {
    ensure_test_schema();
    let payload = alloc_cladt_payload(1, &[7]);
    let opt: CLAdt<OptionInt> = CLAdt::from_raw(payload);
    let _ = opt.read_field::<CLInt>("val");
}

// CLAdt is #[repr(transparent)] — round-trips through i64.
#[test]
fn cladt_repr_transparent_roundtrips() {
    let raw: i64 = 0xDEAD_BEEF_CAFE_BABEu64 as i64;
    let r: CLAdt<Rectangle> = CLAdt::from_raw(raw);
    assert_eq!(r.to_raw(), raw);
    assert_eq!(r.raw_ptr(), raw);
    assert_eq!(
        std::mem::size_of::<CLAdt<Rectangle>>(),
        std::mem::size_of::<i64>()
    );
}
