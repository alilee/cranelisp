//! Crate-integration tests for `CLAdt` sum types — rows T12, T13, T14
//! of `tests/plan/sprint71-platform.md`.

use cranelisp_platform::{CLAdt, CLAdtType, CLInt, CLOwned, GetSchema, Schema};
use std::sync::OnceLock;

// -----------------------------------------------------------------
// Marker types
// -----------------------------------------------------------------

pub struct OptionInt;
impl CLAdtType for OptionInt { const TYPE_NAME: &'static str = "OptionInt"; }
impl GetSchema for OptionInt {
    fn schema() -> &'static Schema {
        static S: OnceLock<Schema> = OnceLock::new();
        S.get_or_init(|| Schema::parse(
            "((OptionInt None (Some ((CLInt val)))))"
        ).unwrap())
    }
}

pub struct ListInt;
impl CLAdtType for ListInt { const TYPE_NAME: &'static str = "ListInt"; }
impl GetSchema for ListInt {
    fn schema() -> &'static Schema {
        static S: OnceLock<Schema> = OnceLock::new();
        S.get_or_init(|| Schema::parse(
            "((ListInt Nil (Cons ((CLInt head) (ListInt tail)))))"
        ).unwrap())
    }
}

// -----------------------------------------------------------------
// Heap fixture helpers
// -----------------------------------------------------------------

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
// T12 — CLAdt<OptionInt> — None variant
// spec: tests/plan/sprint71-platform.md row T12
// -----------------------------------------------------------------

#[test]
fn t12_option_none() {
    let payload = alloc_full_heap_adt(0, &[]);
    let opt: CLAdt<OptionInt> = CLAdt::from_raw(payload);
    assert_eq!(opt.read_tag(), 0);
    // No read_field for None (nullary variant).
    dealloc_heap_adt(payload);
}

// -----------------------------------------------------------------
// T13 — CLAdt<OptionInt> — Some + sum-type dot-qualified lookup
// spec: tests/plan/sprint71-platform.md row T13
// -----------------------------------------------------------------

#[test]
fn t13_option_some_dot_qualified() {
    let payload = alloc_full_heap_adt(1, &[7]);
    let opt: CLAdt<OptionInt> = CLAdt::from_raw(payload);
    assert_eq!(opt.read_tag(), 1);
    let val: CLInt = opt.read_field::<CLInt>("Some.val");
    assert_eq!(i64::from(val), 7);
    dealloc_heap_adt(payload);
}

// -----------------------------------------------------------------
// T14 — CLAdt<ListInt> — recursive walk Nil + Cons
// spec: tests/plan/sprint71-platform.md row T14
// -----------------------------------------------------------------

#[test]
fn t14_list_recursive_walk() {
    // Build Cons(1, Cons(2, Cons(3, Nil)))
    let nil = alloc_full_heap_adt(0, &[]);
    let cons3 = alloc_full_heap_adt(1, &[3, nil]);
    let cons2 = alloc_full_heap_adt(1, &[2, cons3]);
    let cons1 = alloc_full_heap_adt(1, &[1, cons2]);

    // Iterative walk via repeated own_field. We hold each tail's CLOwned
    // until consumed.
    let mut node: CLAdt<ListInt> = CLAdt::from_raw(cons1);
    let mut sum: i64 = 0;

    // We collect the owned wrappers so they drop after the loop body — to
    // avoid use-after-free of the parent's borrowed reference.
    let mut owned_tails: Vec<CLOwned<CLAdt<ListInt>>> = Vec::new();

    loop {
        match node.read_tag() {
            0 => break, // Nil
            1 => {
                let head: CLInt = node.read_field::<CLInt>("Cons.head");
                sum += i64::from(head);
                let tail: CLOwned<CLAdt<ListInt>> = node.own_field::<CLAdt<ListInt>>("Cons.tail");
                node = CLAdt::from_raw(tail.raw_ptr_via_clheap());
                owned_tails.push(tail);
            }
            _ => unreachable!(),
        }
    }

    assert_eq!(sum, 6);

    // Drop the owned tails — they decrement RCs back to original.
    drop(owned_tails);

    // Cleanup
    dealloc_heap_adt(cons1);
    dealloc_heap_adt(cons2);
    dealloc_heap_adt(cons3);
    dealloc_heap_adt(nil);
}

// Helper trait to access raw_ptr through CLOwned via Deref.
trait RawPtrViaClheap {
    fn raw_ptr_via_clheap(&self) -> i64;
}
impl RawPtrViaClheap for CLOwned<CLAdt<ListInt>> {
    fn raw_ptr_via_clheap(&self) -> i64 {
        use cranelisp_platform::CLHeap;
        // Deref to inner CLAdt<ListInt>, then take raw_ptr.
        (**self).raw_ptr()
    }
}
