//! Crate-integration tests — worked synthetic platforms per rows T19,
//! T20, T21 of `tests/plan/sprint71-platform.md`.
//!
//! These exercise end-to-end marker-type + schema-driven field lookup
//! against synthetic heap fixtures. No DLL load; we call the extern
//! functions directly with hand-constructed `CLAdt<T>` values.

use cranelisp_platform::{
    CLAdt, CLInt, CLOwned, GetSchema, HostContext, SchedulingClass, Schema,
};

static HOST: HostContext = HostContext::new();

// Heap fixture helper.
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
// Worked extern functions — what a real DLL author would write.
// -----------------------------------------------------------------

#[allow(unused)]
pub extern "C" fn rectangle_area(r: CLAdt<Rectangle>) -> CLInt {
    let w = r.read_field::<CLInt>("w");
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
                let head = node.read_field::<CLInt>("Cons.head");
                sum += i64::from(head);
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
// declare_platform! invocation with full schema_types list.
// -----------------------------------------------------------------

cranelisp_platform::declare_platform! {
    name: "worked-examples",
    version: "0.1.0",
    host: HOST,
    schema: "((Rectangle ((CLInt w) (CLInt h))) \
             (OptionInt None (Some ((CLInt val)))) \
             (ListInt Nil (Cons ((CLInt head) (ListInt tail)))))",
    schema_types: [Rectangle, OptionInt, ListInt],
    functions: [
        rectangle_area {
            cl_name: "rectangle-area",
            sig: "(Fn [Rectangle] Int)",
            doc: "Compute the area of a rectangle",
            params: [r],
            scheduling: SchedulingClass::Commutative,
        },
        option_or_default {
            cl_name: "option-or-default",
            sig: "(Fn [OptionInt Int] Int)",
            doc: "Unwrap Option or use default",
            params: [opt, default],
            scheduling: SchedulingClass::Commutative,
        },
        list_sum {
            cl_name: "list-sum",
            sig: "(Fn [ListInt] Int)",
            doc: "Sum the elements of a ListInt",
            params: [list],
            scheduling: SchedulingClass::Commutative,
        },
    ]
}

// Confirm the schema parsed cleanly + carries all three types.
#[test]
fn worked_examples_schema_well_formed() {
    let s: &Schema = <Rectangle as GetSchema>::schema();
    assert!(s.lookup_type("Rectangle").is_some());
    assert!(s.lookup_type("OptionInt").is_some());
    assert!(s.lookup_type("ListInt").is_some());
}

// T19 — rectangle_area
// spec: tests/plan/sprint71-platform.md row T19
#[test]
fn t19_rectangle_area_end_to_end() {
    let payload = alloc_full_heap_adt(0, &[3, 4]);
    let r: CLAdt<Rectangle> = CLAdt::from_raw(payload);
    let area = rectangle_area(r);
    assert_eq!(i64::from(area), 12);
    dealloc_heap_adt(payload);
}

// T20 — option_or_default
// spec: tests/plan/sprint71-platform.md row T20
#[test]
fn t20_option_or_default_none_returns_default() {
    let payload = alloc_full_heap_adt(0, &[]); // None
    let opt: CLAdt<OptionInt> = CLAdt::from_raw(payload);
    let result = option_or_default(opt, CLInt::from(42i64));
    assert_eq!(i64::from(result), 42);
    dealloc_heap_adt(payload);
}

#[test]
fn t20_option_or_default_some_returns_inner() {
    let payload = alloc_full_heap_adt(1, &[7]); // Some(7)
    let opt: CLAdt<OptionInt> = CLAdt::from_raw(payload);
    let result = option_or_default(opt, CLInt::from(42i64));
    assert_eq!(i64::from(result), 7);
    dealloc_heap_adt(payload);
}

// T21 — list_sum
// spec: tests/plan/sprint71-platform.md row T21
#[test]
fn t21_list_sum_recursive_walk() {
    let nil = alloc_full_heap_adt(0, &[]);
    let cons3 = alloc_full_heap_adt(1, &[3, nil]);
    let cons2 = alloc_full_heap_adt(1, &[2, cons3]);
    let cons1 = alloc_full_heap_adt(1, &[1, cons2]);

    let list: CLAdt<ListInt> = CLAdt::from_raw(cons1);
    let result = list_sum(list);
    assert_eq!(i64::from(result), 6);

    dealloc_heap_adt(cons1);
    dealloc_heap_adt(cons2);
    dealloc_heap_adt(cons3);
    dealloc_heap_adt(nil);
}
