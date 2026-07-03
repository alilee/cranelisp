//! Global Offset Table (GOT) — re-exports from `cranelisp-types`.
//!
//! The `GotTable` type was moved into `cranelisp-types` in Sprint 56 Wave 0
//! (§9.8 G7 pull-forward) so `SymbolTable` can own the GOT directly. This
//! module preserves the public path `cranelisp_backend::got::GotTable` for
//! backward compatibility during the migration. Later sprints remove the
//! re-export.

pub use cranelisp_types::GotTable;

// =========================================================================
// S101 item (d) — §8.2 slab-growth invariant verification
// (`design/backend/ownership-codegen.md` §8.2: "the per-module GOT slab's
// base address is baked into finalized machine code, so the slab must not
// move for the session's lifetime while `next_got_slot` grows").
//
// VERIFIED FINDING (pinned by the tests below): the slab does not GROW at
// all — `GotTable` is a FIXED `GOT_TABLE_SIZE`(=1024)-slot array allocated
// once (`Box<[AtomicPtr<u8>; GOT_TABLE_SIZE]>`, or the caller-supplied
// `'static` slab for `primitives`) and never reallocated; "growth" is only
// the monotone `SymbolTable::next_got_slot` index into it. `base_ptr()` is
// therefore structurally stable under any number of `allocate_got_slot` /
// `store_slot` events — fresh-slot churn (Wave 4's ABI-epoch versioning)
// adds growth EVENTS, not a growth KIND, and cannot move the slab.
//
// RESIDUAL RISK for Wave 4 (reported, not cured here): the hard bound is
// EXHAUSTION, not movement. `SymbolTable::allocate_got_slot` is UNCHECKED
// (monotone `+= 1`, no bound test); `store_slot`/`load_slot` only
// `debug_assert!(slot < GOT_TABLE_SIZE)` — in release, slot 1024 would index
// out of bounds (UB). Today every allocation is one-per-definition;
// fresh-slot churn makes long dev sessions with many ABI-changing
// redefinitions approach the bound faster. The session (Wave 4) should treat
// slot exhaustion as a surfaced error or rely on the persisted
// `next_got_slot` high-water staying far below 1024.
// =========================================================================

#[cfg(test)]
mod slab_growth_tests {
    use cranelisp_types::{ModuleFullPath, SymbolTable, GOT_TABLE_SIZE};

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
            let slot = st.allocate_got_slot();
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
        let a = st.allocate_got_slot();
        let b = st.allocate_got_slot();
        st.got.store_slot(a, 0xAAAA as *const u8);
        st.got.store_slot(b, 0xBBBB as *const u8);

        // Patch `a` in place (the store_slot path the trap stub rides).
        st.got.store_slot(a, 0xCCCC as *const u8);

        assert_eq!(st.got.base_ptr(), base, "patch must not move the slab");
        assert_eq!(st.got.load_slot(a), 0xCCCC as *const u8, "patched slot");
        assert_eq!(st.got.load_slot(b), 0xBBBB as *const u8, "neighbour intact");
    }
}
