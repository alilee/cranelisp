//! Crate-integration tests for `CLAdt` product types under the embedded
//! generated-schema model (FIXME 0286 / platform-interface.md §5.5).
//!
//! These exercise name-based `read_field` / `own_field` against synthetic heap
//! fixtures that mimic the `[heap_header(16) | tag(4) | pad(4) | field0(8) | …]`
//! layout the host writes via `alloc_with_tag`. The schema is the
//! generated-artifact grammar, installed once via `set_global_schema` (mirroring
//! the macro's `schema:` embed arm); marker types are author-defined and keyed
//! by FQ name. No DLL loading.

use cranelisp_platform::{CLAdt, CLAdtType, CLInt, CLOwned, Schema, set_global_schema};
use std::sync::Once;

mod common;
use common::{alloc_full_heap_adt, dealloc_heap_adt, read_rc};

// -----------------------------------------------------------------
// Author-defined marker types, keyed by FQ name.
// -----------------------------------------------------------------

struct Point;
impl CLAdtType for Point {
    const TYPE_NAME: &'static str = "geometry/Point";
}

struct Bounds;
impl CLAdtType for Bounds {
    const TYPE_NAME: &'static str = "geometry/Bounds";
}

static INSTALL: Once = Once::new();

/// Install the test's generated-artifact schema once (OnceLock under the hood).
fn install_schema() {
    INSTALL.call_once(|| {
        let artifact = "\
;; layout-hash: products
(schema
  (geometry/Point
    (Point 0 ((x primitives/Int) (y primitives/Int))))
  (geometry/Bounds
    (Bounds 0 ((tl geometry/Point) (br geometry/Point)))))";
        set_global_schema(Schema::parse(artifact).expect("artifact parses"));
    });
}

// spec: design/arch/platform-interface.md §5.5 — product field read by name.
#[test]
fn product_read_field_by_name() {
    install_schema();
    let p = alloc_full_heap_adt(0, &[10, 20]);
    let point: CLAdt<Point> = CLAdt::from_raw(p);
    assert_eq!(i64::from(point.read_field::<CLInt>("x")), 10);
    assert_eq!(i64::from(point.read_field::<CLInt>("y")), 20);
    dealloc_heap_adt(p);
}

// spec: design/arch/platform-interface.md §5.5.2 — typed fields drive
// nested-ADT navigation: own_field on a field typed `geometry/Point` returns a
// CLAdt<Point> with inc-on-read RC discipline.
#[test]
fn bounds_nested_read_via_own_field() {
    install_schema();
    let point_payload = alloc_full_heap_adt(0, &[10, 20]);
    let bounds_payload = alloc_full_heap_adt(0, &[point_payload, point_payload]);
    let bounds: CLAdt<Bounds> = CLAdt::from_raw(bounds_payload);

    assert_eq!(read_rc(point_payload), 1);
    {
        let tl: CLOwned<CLAdt<Point>> = bounds.own_field::<CLAdt<Point>>("tl");
        assert_eq!(read_rc(point_payload), 2, "own_field inc'd");
        assert_eq!(i64::from(tl.read_field::<CLInt>("x")), 10);
        assert_eq!(i64::from(tl.read_field::<CLInt>("y")), 20);
    } // tl drops → dec
    assert_eq!(read_rc(point_payload), 1);

    dealloc_heap_adt(bounds_payload);
    dealloc_heap_adt(point_payload);
}
