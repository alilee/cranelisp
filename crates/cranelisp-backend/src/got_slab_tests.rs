//! GOT slab-stability invariant tests (S101 item d; rehomed from the deleted
//! `got.rs` re-export shim at S111 R4 §1.2). Backend-side because the invariant
//! is one BACKEND codegen depends on: finalized machine code bakes the slab
//! `base_ptr()` (via `__cranelisp_got_{M}` resolution), so the slab must not
//! move for the session's lifetime while lifecycle settlement mints slots
//! (`design/backend/ownership-codegen.md` §8.2). The subject types (`GotTable`,
//! `SymbolTable`, `GOT_TABLE_SIZE`) live in `cranelisp-types`; these assertions
//! pin the property the backend relies on.
//!
//! VERIFIED FINDING: the slab does not GROW at all — `GotTable` is a FIXED
//! `GOT_TABLE_SIZE`(=1024)-slot array allocated once and never reallocated;
//! lifecycle settlement claims the first free slot monotonically through the
//! fixed range. `base_ptr()` is therefore structurally stable under every
//! checked mint and `store_slot` event.

use cranelisp_types::{
    GOT_TABLE_SIZE, LifecycleError, ModuleFullPath, Scheme, SlotMintError, Symbol, SymbolTable,
    Type, Visibility,
};

fn mint_slot(st: &mut SymbolTable, index: usize) -> usize {
    st.install_extern(
        Symbol::from(format!("slot-{index}")),
        Scheme {
            type_vars: vec![],
            constraints: Default::default(),
            ty: Type::Fn(vec![], Box::new(Type::Int)),
        },
        vec![],
        None,
        index as u64,
        None,
        None,
        Visibility::Private,
    )
    .expect("fresh table has free slots")
    .index()
}

// spec: design/backend/ownership-codegen.md §8.2 — the slab base address
// is stable while lifecycle settlement fills the ENTIRE slot range:
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
        let slot = mint_slot(&mut st, i);
        assert_eq!(slot, i, "lifecycle slot mint must be monotone from 0");
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

    // The first mint beyond the fixed slab must diagnose exhaustion. It must
    // neither reuse an existing capability nor partially publish the failed
    // binding or disturb the slab state accumulated above.
    let count_before_exhaustion = st.all_symbols().count();
    let overflow_name = Symbol::from("slot-overflow");
    let overflow = st.install_extern(
        overflow_name.clone(),
        Scheme {
            type_vars: vec![],
            constraints: Default::default(),
            ty: Type::Fn(vec![], Box::new(Type::Int)),
        },
        vec![],
        None,
        GOT_TABLE_SIZE as u64,
        None,
        None,
        Visibility::Private,
    );
    match overflow {
        Err(LifecycleError::SlotMint(SlotMintError::Exhausted(error))) => {
            assert_eq!(error.module, ModuleFullPath::from("user"));
        }
        other => panic!("the first post-capacity lifecycle mint must exhaust, got {other:?}"),
    }
    assert!(
        st.get(overflow_name.as_ref()).is_none(),
        "an exhausted mint must not publish a binding"
    );
    assert_eq!(
        st.all_symbols().count(),
        count_before_exhaustion,
        "an exhausted mint must not reuse a slot or change table population"
    );
    assert_eq!(
        st.got.base_ptr(),
        base_before,
        "an exhausted mint must not disturb the slab"
    );

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
    assert_eq!(
        slots.len(),
        GOT_TABLE_SIZE,
        "all slots were minted exactly once"
    );
}

// spec: design/backend/ownership-codegen.md §8.2 — re-storing an existing
// slot (the ABI-preserving in-place patch path, and the trap-stub patch
// on a BROKEN symbol's slot) neither moves the slab nor disturbs
// neighbouring slots.
#[test]
fn in_place_slot_patch_is_isolated_and_base_stable() {
    let mut st: SymbolTable = SymbolTable::new(ModuleFullPath::from("user"));
    let base = st.got.base_ptr();
    let a = mint_slot(&mut st, 0);
    let b = mint_slot(&mut st, 1);
    st.got.store_slot(a, 0xAAAA as *const u8);
    st.got.store_slot(b, 0xBBBB as *const u8);

    // Patch `a` in place (the store_slot path the trap stub rides).
    st.got.store_slot(a, 0xCCCC as *const u8);

    assert_eq!(st.got.base_ptr(), base, "patch must not move the slab");
    assert_eq!(st.got.load_slot(a), 0xCCCC as *const u8, "patched slot");
    assert_eq!(st.got.load_slot(b), 0xBBBB as *const u8, "neighbour intact");
}
