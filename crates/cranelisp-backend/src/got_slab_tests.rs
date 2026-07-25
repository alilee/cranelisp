//! GOT slab-stability invariant tests (S101 item d; rehomed from the deleted
//! `got.rs` re-export shim at S111 R4 §1.2). Backend-side because the invariant
//! is one BACKEND codegen depends on: finalized machine code bakes the slab
//! `base_ptr()` (via `__cranelisp_got_{M}` resolution), so the slab must not
//! move for the session's lifetime while `next_got_slot` grows
//! (`design/backend/ownership-codegen.md` §8.2). The subject types (`GotTable`,
//! `SymbolTable`, `GOT_TABLE_SIZE`) live in `cranelisp-types`; these assertions
//! pin the property the backend relies on.
//!
//! VERIFIED FINDING: the slab does not GROW at all — `GotTable` is a FIXED
//! `GOT_TABLE_SIZE`(=1024)-slot array allocated once and never reallocated;
//! "growth" is only the monotone `SymbolTable::next_got_slot` index into it.
//! `base_ptr()` is therefore structurally stable under any number of
//! `allocate_got_slot` / `store_slot` events.

use cranelisp_types::{GOT_TABLE_SIZE, ModuleFullPath, SymbolTable};

// spec: design/backend/ownership-codegen.md §8.2 — the slab base address
// is stable while `next_got_slot` grows through the ENTIRE slot range:
// machine code that baked `base_ptr()` (via `__cranelisp_got_{M}`
// resolution) stays valid across every later allocation + store. This is
// the invariant Wave 4's fresh-slot allocation depends on.
#[test]
fn slab_base_is_stable_across_full_allocation_and_store_churn() {
    let mut st: SymbolTable = SymbolTable::new(ModuleFullPath::from("user"));
    let base_before = st.got.base_ptr();

    // Simulate a session's worth of slot churn: allocate EVERY slot the
    // slab has and store a distinct pointer into each.
    let mut slots = Vec::with_capacity(GOT_TABLE_SIZE);
    for i in 0..GOT_TABLE_SIZE {
        let slot = st.allocate_got_slot().expect("fresh table has free slots");
        assert_eq!(slot, i, "allocate_got_slot must be monotone from 0");
        st.got.store_slot(slot, (0x1000 + i * 8) as *const u8);
        slots.push(slot);

        // The base must not move at ANY point during growth (a baked
        // GOT reference in finalized code reads through this address).
        assert_eq!(
            st.got.base_ptr(),
            base_before,
            "slab base moved at allocation {i} — baked machine code \
             would read a dangling GOT"
        );
    }

    // Slot CONTENTS are addressable and intact after full churn: the
    // stored pointer round-trips for every slot (slot address = base +
    // slot*8 semantics — earlier stores were not disturbed by later
    // allocations).
    for (i, slot) in slots.iter().enumerate() {
        assert_eq!(
            st.got.load_slot(*slot),
            (0x1000 + i * 8) as *const u8,
            "slot {i} content disturbed by later growth"
        );
    }
    assert_eq!(st.next_got_slot, GOT_TABLE_SIZE, "high-water = slot count");
}

// spec: design/backend/ownership-codegen.md §8.2 — re-storing an existing
// slot (the ABI-preserving in-place patch path, and the trap-stub patch
// on a BROKEN symbol's slot) neither moves the slab nor disturbs
// neighbouring slots.
#[test]
fn in_place_slot_patch_is_isolated_and_base_stable() {
    let mut st: SymbolTable = SymbolTable::new(ModuleFullPath::from("user"));
    let base = st.got.base_ptr();
    let a = st.allocate_got_slot().expect("fresh table has free slots");
    let b = st.allocate_got_slot().expect("fresh table has free slots");
    st.got.store_slot(a, 0xAAAA as *const u8);
    st.got.store_slot(b, 0xBBBB as *const u8);

    // Patch `a` in place (the store_slot path the trap stub rides).
    st.got.store_slot(a, 0xCCCC as *const u8);

    assert_eq!(st.got.base_ptr(), base, "patch must not move the slab");
    assert_eq!(st.got.load_slot(a), 0xCCCC as *const u8, "patched slot");
    assert_eq!(st.got.load_slot(b), 0xBBBB as *const u8, "neighbour intact");
}
