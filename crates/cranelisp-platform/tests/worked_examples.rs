//! Crate-integration tests — the worked synthetic platform from the
//! platform-author experience (platform-interface.md §4), reworked for the
//! three-exports / embedded-generated-schema model (FIXME 0286).
//!
//! These exercise end-to-end name-based field lookup against synthetic heap
//! fixtures: the schema is the generated-artifact grammar embedded via the
//! macro's `schema:` arm; field access resolves by name from the installed
//! global schema; marker types are author-defined and FQ-keyed; sigs are fully
//! qualified. The extern functions are exactly what a real DLL author writes
//! (the §4 `rectangle_area` example).

use cranelisp_platform::{
    CLAdt, CLAdtType, CLInt, CLOwned, HostCallbacks, HostContext, SchedulingClass,
};
use std::sync::Once;

static HOST: HostContext = HostContext::new();

// Author-defined marker types, FQ-keyed (the macro no longer auto-emits these).
pub struct Rectangle;
impl CLAdtType for Rectangle {
    const TYPE_NAME: &'static str = "shapes/Rectangle";
}
pub struct OptionInt;
impl CLAdtType for OptionInt {
    const TYPE_NAME: &'static str = "shapes/OptionInt";
}
pub struct ListInt;
impl CLAdtType for ListInt {
    const TYPE_NAME: &'static str = "shapes/ListInt";
}

fn alloc_full_heap_adt(tag: u32, fields: &[i64]) -> i64 {
    let payload_size = 8 + fields.len() * 8;
    let total_size = 16 + payload_size;
    unsafe {
        let layout = std::alloc::Layout::from_size_align_unchecked(total_size, 8);
        let alloc_base = std::alloc::alloc_zeroed(layout);
        *(alloc_base as *mut i64) = total_size as i64;
        *((alloc_base as *mut i64).add(1)) = 1;
        let payload = alloc_base.add(16);
        *(payload as *mut u32) = tag;
        *(payload.add(4) as *mut u32) = 0;
        for (i, val) in fields.iter().enumerate() {
            *(payload.add(8 + i * 8) as *mut i64) = *val;
        }
        alloc_base as i64
    }
}

fn dealloc_heap_adt(base: i64) {
    unsafe {
        let total_size = *(base as *const i64) as usize;
        let layout = std::alloc::Layout::from_size_align_unchecked(total_size, 8);
        std::alloc::dealloc(base as *mut u8, layout);
    }
}

// -----------------------------------------------------------------
// Worked extern functions — what a real DLL author would write
// (platform-interface.md §4, "rectangle_area").
// -----------------------------------------------------------------

#[allow(unused)]
pub extern "C" fn rectangle_area(r: CLAdt<Rectangle>) -> CLInt {
    let w = r.read_field::<CLInt>("w"); // by NAME — against the embedded schema
    let h = r.read_field::<CLInt>("h");
    CLInt::from(i64::from(w) * i64::from(h))
}

#[allow(unused)]
pub extern "C" fn option_or_default(opt: CLAdt<OptionInt>, default: CLInt) -> CLInt {
    match opt.read_tag() {
        0 => default,
        1 => opt.read_field::<CLInt>("Some.val"),
        _ => unreachable!(),
    }
}

#[allow(unused)]
pub extern "C" fn list_sum(list: CLAdt<ListInt>) -> CLInt {
    let mut node = list;
    let mut sum: i64 = 0;
    let mut owned: Vec<CLOwned<CLAdt<ListInt>>> = Vec::new();
    loop {
        match node.read_tag() {
            0 => break,
            1 => {
                sum += i64::from(node.read_field::<CLInt>("Cons.head"));
                let tail = node.own_field::<CLAdt<ListInt>>("Cons.tail");
                use cranelisp_platform::CLHeap;
                node = CLAdt::from_raw((*tail).raw_ptr());
                owned.push(tail);
            }
            _ => unreachable!(),
        }
    }
    drop(owned);
    CLInt::from(sum)
}

// -----------------------------------------------------------------
// declare_platform! invocation — the `schema:` EMBED arm with the
// generated-artifact grammar; FQ sigs; no schema_types.
// -----------------------------------------------------------------

cranelisp_platform::declare_platform! {
    name: "worked-examples",
    version: "0.1.0",
    host: HOST,
    schema: "\
;; layout-hash: workedexamples
(schema
  (shapes/Rectangle
    (Rectangle 0 ((w primitives/Int) (h primitives/Int))))
  (shapes/OptionInt
    (None 0 ())
    (Some 1 ((val primitives/Int))))
  (shapes/ListInt
    (Nil 0 ())
    (Cons 1 ((head primitives/Int) (tail shapes/ListInt)))))",
    functions: [
        rectangle_area {
            cl_name: "rectangle-area",
            sig: "(Fn [shapes/Rectangle] primitives/Int)",
            doc: "Compute the area of a rectangle",
            params: [r],
            scheduling: SchedulingClass::Commutative,
        },
        option_or_default {
            cl_name: "option-or-default",
            sig: "(Fn [shapes/OptionInt primitives/Int] primitives/Int)",
            doc: "Unwrap Option or use default",
            params: [opt, default],
            scheduling: SchedulingClass::Commutative,
        },
        list_sum {
            cl_name: "list-sum",
            sig: "(Fn [shapes/ListInt] primitives/Int)",
            doc: "Sum the elements of a ListInt",
            params: [list],
            scheduling: SchedulingClass::Commutative,
        },
    ]
}

// `cranelisp_platform_manifest` is emitted by the macro at this module's root —
// callable directly in-crate.

extern "C" fn test_alloc(_size: i64) -> i64 {
    0
}

static INSTALL: Once = Once::new();

/// Invoke the macro-emitted manifest entry once, as the host would — this
/// installs the embedded schema for name-based field access.
fn install() {
    INSTALL.call_once(|| {
        let cb = HostCallbacks {
            alloc: test_alloc,
            alloc_with_tag: cranelisp_platform::null_alloc_with_tag,
            validate_schema: cranelisp_platform::null_validate_schema,
        };
        let _ = unsafe { cranelisp_platform_manifest(&cb) };
    });
}

// spec: design/arch/platform-interface.md §4 — rectangle_area reads fields by
// name against the embedded generated schema.
#[test]
fn rectangle_area_end_to_end() {
    install();
    let payload = alloc_full_heap_adt(0, &[3, 4]);
    let r: CLAdt<Rectangle> = CLAdt::from_raw(payload);
    assert_eq!(i64::from(rectangle_area(r)), 12);
    dealloc_heap_adt(payload);
}

// spec: design/arch/platform-interface.md §5.5 — sum-type dispatch + field.
#[test]
fn option_or_default_none_returns_default() {
    install();
    let payload = alloc_full_heap_adt(0, &[]);
    let opt: CLAdt<OptionInt> = CLAdt::from_raw(payload);
    assert_eq!(i64::from(option_or_default(opt, CLInt::from(42i64))), 42);
    dealloc_heap_adt(payload);
}

#[test]
fn option_or_default_some_returns_inner() {
    install();
    let payload = alloc_full_heap_adt(1, &[7]);
    let opt: CLAdt<OptionInt> = CLAdt::from_raw(payload);
    assert_eq!(i64::from(option_or_default(opt, CLInt::from(42i64))), 7);
    dealloc_heap_adt(payload);
}

// spec: design/arch/platform-interface.md §5.5.2 — recursive ListInt walk.
#[test]
fn list_sum_recursive_walk() {
    install();
    let nil = alloc_full_heap_adt(0, &[]);
    let cons3 = alloc_full_heap_adt(1, &[3, nil]);
    let cons2 = alloc_full_heap_adt(1, &[2, cons3]);
    let cons1 = alloc_full_heap_adt(1, &[1, cons2]);

    let list: CLAdt<ListInt> = CLAdt::from_raw(cons1);
    assert_eq!(i64::from(list_sum(list)), 6);

    dealloc_heap_adt(cons1);
    dealloc_heap_adt(cons2);
    dealloc_heap_adt(cons3);
    dealloc_heap_adt(nil);
}
