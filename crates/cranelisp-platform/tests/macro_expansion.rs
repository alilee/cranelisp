//! Crate-integration tests for the `declare_platform!` macro's `schema:`
//! arm — rows T17, T18 of `tests/plan/sprint71-platform.md`.

use cranelisp_platform::{CLAdt, CLAdtType, GetSchema, HostContext, SchedulingClass};

// Static HOST required by declare_platform!.
static HOST: HostContext = HostContext::new();

// A trivial extern fn the macro can reference. We do not call it from the
// test — we just need it to satisfy `functions: [...]`.
#[allow(unsafe_op_in_unsafe_fn)]
pub extern "C" fn noop_fn() -> cranelisp_platform::CLIO<cranelisp_platform::CLInt> {
    cranelisp_platform::CLIO::pure(cranelisp_platform::CLInt::from(0i64))
}

// -----------------------------------------------------------------
// T17 — declare_platform! `schema:` arm emits marker types
// spec: tests/plan/sprint71-platform.md row T17
// -----------------------------------------------------------------

cranelisp_platform::declare_platform! {
    name: "macro-test",
    version: "0.1.0",
    host: HOST,
    schema: "((Rectangle ((CLInt w) (CLInt h))) (OptionInt None (Some ((CLInt val)))))",
    schema_types: [Rectangle, OptionInt],
    functions: [
        noop_fn {
            cl_name: "noop",
            sig: "(Fn [] (IO Int))",
            doc: "noop",
            params: [],
            scheduling: SchedulingClass::Commutative,
        },
    ]
}

#[test]
fn t17_marker_types_emitted_with_correct_type_names() {
    // Marker types Rectangle + OptionInt exist as named structs;
    // their CLAdtType impl returns the matching string.
    assert_eq!(<Rectangle as CLAdtType>::TYPE_NAME, "Rectangle");
    assert_eq!(<OptionInt as CLAdtType>::TYPE_NAME, "OptionInt");

    // The marker types are usable as CLAdt<T> type parameters — exercising
    // this with a from_raw at a synthetic non-dereffed value confirms the
    // type is well-formed at the type system level.
    let _r: CLAdt<Rectangle> = CLAdt::from_raw(0);
    let _o: CLAdt<OptionInt> = CLAdt::from_raw(0);
}

// -----------------------------------------------------------------
// T18 — `LazyLock<Schema>` per-DLL static is reachable + force-inits
// spec: tests/plan/sprint71-platform.md row T18
// -----------------------------------------------------------------

#[test]
fn t18_dll_schema_lazy_static_is_reachable() {
    // The schema is reachable via the GetSchema trait emitted by the macro.
    let schema = <Rectangle as GetSchema>::schema();
    assert!(!schema.is_empty(), "DLL_SCHEMA should be populated");

    // The parsed schema contains both declared types.
    assert!(schema.lookup_type("Rectangle").is_some());
    assert!(schema.lookup_type("OptionInt").is_some());

    // Both marker types route through the SAME per-DLL schema static.
    let schema_via_option = <OptionInt as GetSchema>::schema();
    // Pointer equality — they reference the same static.
    assert!(std::ptr::eq(schema, schema_via_option));
}
