//! Crate-integration tests for `CLAdt` product types — rows T10, T11
//! of `tests/plan/sprint71-platform.md`.
//!
//! These exercise `read_field` / `own_field` against synthetic heap
//! fixtures that mimic the `[heap_header(16) | tag(4) | pad(4) | field0(8) | ...]`
//! layout the host writes via `alloc_with_tag` (when wired).
//!
//! No DLL loading; all schemas / marker types are constructed inline as
//! test fixtures. This matches the design §10 brief "synthetic in-test
//! platforms via declare_platform! against real DLLs is deferred to /qa
//! round-trip tests (FIXME 0235)".

use cranelisp_platform::{
    AnyAdt, CLAdt, CLAdtType, CLInt, CLOwned, GetSchema, Schema,
};
use std::sync::OnceLock;

// -----------------------------------------------------------------
// Marker types — emitted manually here, mirroring what
// `declare_platform!` would emit from a `schema:` arm.
// -----------------------------------------------------------------

pub struct Point;
impl CLAdtType for Point {
    const TYPE_NAME: &'static str = "Point";
}
impl GetSchema for Point {
    fn schema() -> &'static Schema { points_schema() }
}

pub struct Bounds;
impl CLAdtType for Bounds {
    const TYPE_NAME: &'static str = "Bounds";
}
impl GetSchema for Bounds {
    fn schema() -> &'static Schema { points_schema() }
}

fn points_schema() -> &'static Schema {
    static S: OnceLock<Schema> = OnceLock::new();
    S.get_or_init(|| Schema::parse(
        "((Point ((CLInt x) (CLInt y))) \
          (Bounds ((Point tl) (Point br))))"
    ).unwrap())
}

// -----------------------------------------------------------------
// Heap fixture helpers — mimic the host's `alloc_with_tag` shape.
// -----------------------------------------------------------------

/// Allocate a full heap-ADT block:
///   `[alloc_size: i64][rc: i64][tag: u32][pad: u32][field0: i64]...`
/// Returns the **alloc base** pointer (matching CLString's convention,
/// which `CLAdt::from_raw` expects).
fn alloc_full_heap_adt(tag: u32, fields: &[i64]) -> i64 {
    let payload_size = 8 + fields.len() * 8;
    let total_size = 16 + payload_size; // header + payload
    unsafe {
        let layout = std::alloc::Layout::from_size_align_unchecked(total_size, 8);
        let alloc_base = std::alloc::alloc_zeroed(layout);
        *(alloc_base as *mut i64) = total_size as i64; // alloc_size
        *((alloc_base as *mut i64).add(1)) = 1;        // rc = 1
        let payload = alloc_base.add(16);
        *(payload as *mut u32) = tag;
        *(payload.add(4) as *mut u32) = 0;
        for (i, val) in fields.iter().enumerate() {
            *(payload.add(8 + i * 8) as *mut i64) = *val;
        }
        alloc_base as i64
    }
}

fn read_rc(base: i64) -> i64 {
    unsafe { *((base + 8) as *const i64) }
}

// -----------------------------------------------------------------
// T11 — CLAdt<Bounds> nested read via own_field
// spec: design/platform/sprint71-redesign.md §4.4 + tests/plan/sprint71-platform.md row T11
// -----------------------------------------------------------------

#[test]
fn t11_bounds_nested_read_via_own_field() {
    // Build Point{x=10, y=20} as a heap-ADT.
    let point_payload = alloc_full_heap_adt(0, &[10, 20]);
    // Bounds{tl=point_payload, br=point_payload} — share the pointer to
    // exercise inc-on-read; we observe RC change.
    let bounds_payload = alloc_full_heap_adt(0, &[point_payload, point_payload]);

    let bounds: CLAdt<Bounds> = CLAdt::from_raw(bounds_payload);

    // RC of point starts at 1.
    assert_eq!(read_rc(point_payload), 1);

    {
        // own_field inc-on-read → RC becomes 2.
        let tl: CLOwned<CLAdt<Point>> = bounds.own_field::<CLAdt<Point>>("tl");
        assert_eq!(read_rc(point_payload), 2);

        let x: CLInt = tl.read_field::<CLInt>("x");
        let y: CLInt = tl.read_field::<CLInt>("y");
        assert_eq!(i64::from(x), 10);
        assert_eq!(i64::from(y), 20);
    } // tl drops here, dec_rc → 1

    assert_eq!(read_rc(point_payload), 1);

    // Cleanup: drop the point + bounds allocations.
    unsafe {
        // bounds first (no inc on payload elements is held)
        let bounds_layout = std::alloc::Layout::from_size_align_unchecked(16 + 8 + 16, 8);
        std::alloc::dealloc(bounds_payload as *mut u8, bounds_layout);
        // point — RC=1 by now (one transferred ref from the test setup)
        let point_layout = std::alloc::Layout::from_size_align_unchecked(16 + 8 + 16, 8);
        std::alloc::dealloc(point_payload as *mut u8, point_layout);
    }
}

// -----------------------------------------------------------------
// T15 — CLAdt::own_field inc-on-read RC discipline (integration variant)
// spec: design/platform/sprint71-redesign.md §4.1 + tests/plan/sprint71-platform.md row T15
// -----------------------------------------------------------------

#[test]
fn t15_own_field_inc_on_read_rc_discipline() {
    let point_payload = alloc_full_heap_adt(0, &[1, 2]);
    let outer = alloc_full_heap_adt(0, &[point_payload, point_payload]);

    let bounds: CLAdt<Bounds> = CLAdt::from_raw(outer);

    let start_rc = read_rc(point_payload);
    {
        let _owned_tl: CLOwned<CLAdt<Point>> = bounds.own_field::<CLAdt<Point>>("tl");
        assert_eq!(read_rc(point_payload), start_rc + 1, "own_field inc'd");
    }
    assert_eq!(read_rc(point_payload), start_rc, "CLOwned drop dec'd");

    // Cleanup
    unsafe {
        let bounds_layout = std::alloc::Layout::from_size_align_unchecked(16 + 8 + 16, 8);
        std::alloc::dealloc(outer as *mut u8, bounds_layout);
        let point_layout = std::alloc::Layout::from_size_align_unchecked(16 + 8 + 16, 8);
        std::alloc::dealloc(point_payload as *mut u8, point_layout);
    }
}

// -----------------------------------------------------------------
// AnyAdt round-trip — coerce typed → AnyAdt via raw, then back
// -----------------------------------------------------------------

#[test]
fn anyadt_to_typed_round_trip() {
    let payload = alloc_full_heap_adt(7, &[42, 99]);
    let any: CLAdt<AnyAdt> = CLAdt::from_raw(payload);
    assert_eq!(any.read_tag_any(), 7);
    let p: CLAdt<Point> = any.into_typed::<Point>();
    let x: CLInt = p.read_field::<CLInt>("x");
    assert_eq!(i64::from(x), 42);

    unsafe {
        let layout = std::alloc::Layout::from_size_align_unchecked(16 + 8 + 16, 8);
        std::alloc::dealloc(payload as *mut u8, layout);
    }
}
