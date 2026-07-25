use super::*;
use std::sync::Arc;

// spec: 12-runtime §12.2 — GOT slot store and load
#[test]
fn test_store_and_load_slot() {
    let got = GotTable::new();
    let fake_ptr = 0x1234usize as *const u8;
    got.store_slot(0, fake_ptr);
    assert_eq!(got.load_slot(0), fake_ptr);
}

// spec: 12-runtime §12.2 — GOT base pointer is valid (non-null)
#[test]
fn test_got_base_ptr_non_null() {
    let got = GotTable::new();
    assert!(!got.base_ptr().is_null());
}

// spec: 12-runtime §12.2 — GOT slots initialize to null
#[test]
fn test_got_slots_initialize_null() {
    let got = GotTable::new();
    assert!(got.load_slot(0).is_null());
    assert!(got.load_slot(1).is_null());
}

// spec: 12-runtime §12.2 — GOT static-backing construction (FIXME 0280)
#[test]
fn test_with_static_backing_store_and_load() {
    // A process-lifetime writable static slab — the shape
    // `cranelisp-primitives` exports as `__cranelisp_got_primitives`.
    // `std::array::from_fn` cannot build a const initializer, so use a
    // leaked Box to obtain a genuine `&'static` for the test (the slab is
    // never freed, satisfying the `'static` + single-backing contract).
    let slab: &'static [AtomicPtr<u8>; GOT_TABLE_SIZE] =
        Box::leak(Box::new(std::array::from_fn(|_| {
            AtomicPtr::new(std::ptr::null_mut())
        })));
    let slab_addr = slab.as_ptr() as *const u8;

    let got = GotTable::with_static_backing(slab);

    // base_ptr() must point AT the static slab, not a fresh heap allocation.
    assert_eq!(
        got.base_ptr(),
        slab_addr,
        "static-backed GotTable must expose the slab address as base_ptr"
    );

    // Slots start null, and writes land in the static (observable through
    // both the table API and the raw slab reference — same memory).
    assert!(got.load_slot(3).is_null());
    let fake = 0xBEEFusize as *const u8;
    got.store_slot(3, fake);
    assert_eq!(got.load_slot(3), fake);
    assert_eq!(
        slab[3].load(Ordering::Acquire) as *const u8,
        fake,
        "write through the table must be visible on the backing static"
    );
}

// spec: 12-runtime §12.2 — atomic GOT: concurrent writes to disjoint slots
#[test]
fn test_atomic_got_concurrent_writes() {
    let got = Arc::new(GotTable::new());
    let got2 = Arc::clone(&got);

    let t1 = std::thread::spawn(move || {
        let ptr = 0x1111usize as *const u8;
        got2.store_slot(0, ptr);
    });
    let ptr2 = 0x2222usize as *const u8;
    got.store_slot(1, ptr2);
    t1.join().unwrap();

    assert_eq!(got.load_slot(0), 0x1111usize as *const u8);
    assert_eq!(got.load_slot(1), 0x2222usize as *const u8);
}
