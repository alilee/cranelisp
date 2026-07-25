//! Crate-integration tests for `CLAdt` sum types under the embedded
//! generated-schema model (FIXME 0286 / platform-interface.md §5.5).
//!
//! Name-based field access against synthetic heap fixtures; the schema is the
//! generated-artifact grammar installed once via `set_global_schema`; marker
//! types are author-defined and FQ-keyed. Sum-type fields are dot-qualified by
//! constructor name (`"Some.val"`, `"Cons.head"`).

use cranelisp_platform::{CLAdt, CLAdtType, CLInt, CLOwned, Schema, set_global_schema};
use std::sync::Once;

struct OptionInt;
impl CLAdtType for OptionInt {
    const TYPE_NAME: &'static str = "data/OptionInt";
}

struct ListInt;
impl CLAdtType for ListInt {
    const TYPE_NAME: &'static str = "data/ListInt";
}

static INSTALL: Once = Once::new();

fn install_schema() {
    INSTALL.call_once(|| {
        let artifact = "\
;; layout-hash: sums
(schema
  (data/OptionInt
    (None 0 ())
    (Some 1 ((val primitives/Int))))
  (data/ListInt
    (Nil 0 ())
    (Cons 1 ((head primitives/Int) (tail data/ListInt)))))";
        set_global_schema(Schema::parse(artifact).expect("artifact parses"));
    });
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

// spec: design/arch/platform-interface.md §5.5 — None (nullary) variant tag.
#[test]
fn option_none() {
    install_schema();
    let payload = alloc_full_heap_adt(0, &[]);
    let opt: CLAdt<OptionInt> = CLAdt::from_raw(payload);
    assert_eq!(opt.read_tag(), 0);
    dealloc_heap_adt(payload);
}

// spec: design/arch/platform-interface.md §5.5 — Some with dot-qualified field.
#[test]
fn option_some_dot_qualified() {
    install_schema();
    let payload = alloc_full_heap_adt(1, &[7]);
    let opt: CLAdt<OptionInt> = CLAdt::from_raw(payload);
    assert_eq!(opt.read_tag(), 1);
    assert_eq!(i64::from(opt.read_field::<CLInt>("Some.val")), 7);
    dealloc_heap_adt(payload);
}

// spec: design/arch/platform-interface.md §5.5.2 — recursive walk over a
// self-referential ADT: the `tail` field is typed `data/ListInt`, looked up in
// the same schema map.
#[test]
fn list_recursive_walk() {
    install_schema();
    let nil = alloc_full_heap_adt(0, &[]);
    let cons3 = alloc_full_heap_adt(1, &[3, nil]);
    let cons2 = alloc_full_heap_adt(1, &[2, cons3]);
    let cons1 = alloc_full_heap_adt(1, &[1, cons2]);

    let mut node: CLAdt<ListInt> = CLAdt::from_raw(cons1);
    let mut sum: i64 = 0;
    let mut owned_tails: Vec<CLOwned<CLAdt<ListInt>>> = Vec::new();

    loop {
        match node.read_tag() {
            0 => break,
            1 => {
                sum += i64::from(node.read_field::<CLInt>("Cons.head"));
                let tail: CLOwned<CLAdt<ListInt>> = node.own_field::<CLAdt<ListInt>>("Cons.tail");
                node = CLAdt::from_raw(raw_ptr(&tail));
                owned_tails.push(tail);
            }
            _ => unreachable!(),
        }
    }

    assert_eq!(sum, 6);
    drop(owned_tails);

    dealloc_heap_adt(cons1);
    dealloc_heap_adt(cons2);
    dealloc_heap_adt(cons3);
    dealloc_heap_adt(nil);
}

fn raw_ptr(owned: &CLOwned<CLAdt<ListInt>>) -> i64 {
    use cranelisp_platform::CLHeap;
    (**owned).raw_ptr()
}
