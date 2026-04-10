// Global Offset Table (GOT) for interactive (REPL) mode.
//
// In Interactive mode, function calls go through a GOT slot so that
// redefining a function updates all call sites. In Batch mode, calls
// are direct and the GOT is not used.
//
// The GOT uses AtomicPtr<u8> slots so that concurrent codegen workers
// can write code pointers to disjoint slots without data races.
// JIT-generated code reads slots via raw pointer loads (got_base + slot * 8)
// which is safe because AtomicPtr has the same layout as *const u8.

use std::sync::atomic::{AtomicPtr, Ordering};

use crate::codegen_types::GOT_TABLE_SIZE;

/// Shared GOT table: array of atomic function pointers.
///
/// Shared between the main thread and codegen worker threads via `Arc`.
/// Workers write to pre-assigned disjoint slots using `store(Release)`.
/// The main thread reads after `hot_flush` barrier ensures happens-before.
/// JIT code reads via raw pointer loads at `got_base + slot * 8`.
pub struct GotTable {
    slots: Box<[AtomicPtr<u8>; GOT_TABLE_SIZE]>,
}

// SAFETY: GotTable contains AtomicPtr which is inherently Send+Sync.
// The raw pointer values stored point to JIT code pages that remain
// valid for the process lifetime (Cranelift leaks code memory on drop).
unsafe impl Send for GotTable {}
unsafe impl Sync for GotTable {}

impl GotTable {
    /// Create a new GOT table with all slots initialized to null.
    pub fn new() -> Self {
        // Initialize all slots to null. AtomicPtr::new is const, but
        // we need a boxed array, so use a Vec and convert.
        let mut slots = Vec::with_capacity(GOT_TABLE_SIZE);
        for _ in 0..GOT_TABLE_SIZE {
            slots.push(AtomicPtr::new(std::ptr::null_mut()));
        }
        let boxed: Box<[AtomicPtr<u8>; GOT_TABLE_SIZE]> = slots
            .into_boxed_slice()
            .try_into()
            .unwrap_or_else(|_| unreachable!("invariant: vec has GOT_TABLE_SIZE elements"));
        GotTable { slots: boxed }
    }

    /// Get the base address of the GOT table.
    ///
    /// Returns a raw pointer suitable for use as the `got_base_ptr` constant
    /// in JIT-generated code. The pointer is stable for the lifetime of the
    /// `Arc<GotTable>`.
    pub fn base_ptr(&self) -> *const u8 {
        self.slots.as_ptr() as *const u8
    }

    /// Atomically write a code pointer to a GOT slot.
    ///
    /// Uses `Release` ordering so that after a flush barrier (thread join
    /// or channel recv), the main thread sees all writes.
    pub fn store_slot(&self, slot: usize, ptr: *const u8) {
        debug_assert!(
            slot < GOT_TABLE_SIZE,
            "invariant: GOT slot {slot} out of range"
        );
        self.slots[slot].store(ptr as *mut u8, Ordering::Release);
    }

    /// Read a code pointer from a GOT slot.
    ///
    /// Uses `Acquire` ordering to pair with worker `Release` stores.
    pub fn load_slot(&self, slot: usize) -> *const u8 {
        debug_assert!(
            slot < GOT_TABLE_SIZE,
            "invariant: GOT slot {slot} out of range"
        );
        self.slots[slot].load(Ordering::Acquire) as *const u8
    }
}

impl Default for GotTable {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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

    // spec: 12-runtime §12.2 — atomic GOT: concurrent writes to disjoint slots
    #[test]
    fn test_atomic_got_concurrent_writes() {
        let got = Arc::new(GotTable::new());
        let got2 = Arc::clone(&got);

        // Simulate two workers writing to disjoint slots.
        let t1 = std::thread::spawn(move || {
            let ptr = 0x1111usize as *const u8;
            got2.store_slot(0, ptr);
        });
        let ptr2 = 0x2222usize as *const u8;
        got.store_slot(1, ptr2);
        t1.join().unwrap();

        // After join (happens-before), both writes are visible.
        assert_eq!(got.load_slot(0), 0x1111usize as *const u8);
        assert_eq!(got.load_slot(1), 0x2222usize as *const u8);
    }
}
