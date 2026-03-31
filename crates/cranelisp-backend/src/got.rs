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

use std::collections::HashMap;
use std::sync::atomic::{AtomicPtr, Ordering};
use std::sync::Arc;

use cranelisp_types::{CranelispError, Span, Symbol};

use crate::codegen_types::{DefCodegen, GOT_TABLE_SIZE};

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

/// Per-module codegen state. Owns the GOT and per-definition artifacts.
pub struct ModuleCodegenState {
    /// Shared GOT table: array of atomic function pointers.
    /// Lazily allocated on first use. Shared with codegen workers via Arc.
    got_table: Option<Arc<GotTable>>,
    /// Next available GOT slot index.
    next_got_slot: usize,
    /// Per-definition codegen artifacts.
    pub def_codegen: HashMap<Symbol, DefCodegen>,
}

// SAFETY: ModuleCodegenState contains an Arc<GotTable> (Send+Sync) and
// a HashMap of DefCodegen (Send+Sync). Raw pointers in DefCodegen point
// to JIT code pages that are valid for the process lifetime.
unsafe impl Send for ModuleCodegenState {}
unsafe impl Sync for ModuleCodegenState {}

impl ModuleCodegenState {
    /// Create a new module codegen state with no GOT allocated.
    pub fn new() -> Self {
        ModuleCodegenState {
            got_table: None,
            next_got_slot: 0,
            def_codegen: HashMap::new(),
        }
    }

    /// Ensure the GOT table is allocated, returning a reference to the Arc.
    fn ensure_got(&mut self) -> &Arc<GotTable> {
        if self.got_table.is_none() {
            self.got_table = Some(Arc::new(GotTable::new()));
        }
        self.got_table
            .as_ref()
            .unwrap_or_else(|| unreachable!("invariant: GOT just allocated"))
    }

    /// Set the GOT table to a pre-existing shared table.
    ///
    /// Used by N-core codegen workers that share a GOT table with the main
    /// thread. The worker writes code pointers atomically to pre-assigned slots.
    pub fn set_shared_got(&mut self, got: Arc<GotTable>) {
        self.got_table = Some(got);
    }

    /// Get the base address of the GOT table, allocating if needed.
    pub fn got_base_ptr(&mut self) -> *const u8 {
        self.ensure_got().base_ptr()
    }

    /// Get a shared reference to the GOT table for concurrent access.
    ///
    /// Allocates the GOT table if not already allocated. Returns an
    /// `Arc<GotTable>` that can be cloned for codegen worker threads.
    pub fn shared_got(&mut self) -> Arc<GotTable> {
        self.ensure_got();
        Arc::clone(
            self.got_table
                .as_ref()
                .unwrap_or_else(|| unreachable!("invariant: GOT just allocated")),
        )
    }

    /// Get the current next_got_slot counter value.
    ///
    /// Used by `SharedCodegenState::extract_from` to capture the slot
    /// counter when bridging between InMemWorkerState and the new types.
    pub fn next_got_slot(&self) -> usize {
        self.next_got_slot
    }

    /// Set the next_got_slot counter.
    ///
    /// Used by `SharedCodegenState::sync_back_to` to restore the slot
    /// counter after the worker loop completes.
    pub fn set_next_got_slot(&mut self, slot: usize) {
        self.next_got_slot = slot;
    }

    /// Allocate a new GOT slot for a function, returning the slot index.
    ///
    /// Returns a `CranelispError::CodegenError` if the GOT is full.
    pub fn allocate_slot(&mut self) -> Result<usize, CranelispError> {
        if self.next_got_slot >= GOT_TABLE_SIZE {
            return Err(CranelispError::CodegenError {
                message: format!(
                    "GOT table full: cannot allocate slot (max {GOT_TABLE_SIZE})"
                ),
                span: Span::SYNTHETIC,
            });
        }
        let slot = self.next_got_slot;
        self.next_got_slot += 1;
        Ok(slot)
    }

    /// Update the function pointer at a GOT slot.
    pub fn update_slot(&mut self, slot: usize, ptr: *const u8) {
        let got = self.ensure_got();
        got.store_slot(slot, ptr);
    }

    /// Get the function pointer at a GOT slot.
    pub fn get_slot(&self, slot: usize) -> Option<*const u8> {
        self.got_table
            .as_ref()
            .map(|got| got.load_slot(slot))
    }

    /// Allocate a GOT slot for a definition and record it in def_codegen.
    /// If the definition already has a slot, reuses it.
    pub fn ensure_slot_for(&mut self, name: &Symbol) -> Result<usize, CranelispError> {
        // Check if we already have a slot.
        if let Some(dc) = self.def_codegen.get(name)
            && let Some(slot) = dc.got_slot
        {
            return Ok(slot);
        }

        let slot = self.allocate_slot()?;
        let dc = self.def_codegen.entry(name.clone()).or_default();
        dc.got_slot = Some(slot);
        Ok(slot)
    }

    /// Update the GOT slot and code_ptr for a definition.
    pub fn update_def(&mut self, name: &Symbol, code_ptr: *const u8) {
        // Read the slot first to avoid overlapping borrows.
        let slot = self
            .def_codegen
            .get(name)
            .and_then(|dc| dc.got_slot);

        if let Some(slot) = slot {
            self.update_slot(slot, code_ptr);
        }

        let dc = self.def_codegen.entry(name.clone()).or_default();
        dc.code_ptr = Some(code_ptr);
    }
}

impl Default for ModuleCodegenState {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // spec: 12-runtime §12.2 — GOT slot allocation for per-module function table
    #[test]
    fn test_allocate_slot() {
        let mut state = ModuleCodegenState::new();
        let slot = state.allocate_slot().unwrap();
        assert_eq!(slot, 0);
        let slot2 = state.allocate_slot().unwrap();
        assert_eq!(slot2, 1);
    }

    // spec: 12-runtime §12.2 — GOT slot update and retrieval
    #[test]
    fn test_update_and_get_slot() {
        let mut state = ModuleCodegenState::new();
        let slot = state.allocate_slot().unwrap();
        let fake_ptr = 0x1234usize as *const u8;
        state.update_slot(slot, fake_ptr);
        assert_eq!(state.get_slot(slot), Some(fake_ptr));
    }

    // spec: 12-runtime §12.2 — GOT slot reuse for same symbol name
    #[test]
    fn test_ensure_slot_for_reuses() {
        let mut state = ModuleCodegenState::new();
        let name = Symbol::from("foo");
        let slot1 = state.ensure_slot_for(&name).unwrap();
        let slot2 = state.ensure_slot_for(&name).unwrap();
        assert_eq!(slot1, slot2, "should reuse the same slot");
    }

    // spec: 12-runtime §12.2 — GOT base pointer is valid (non-null)
    #[test]
    fn test_got_base_ptr_non_null() {
        let mut state = ModuleCodegenState::new();
        let ptr = state.got_base_ptr();
        assert!(!ptr.is_null());
    }

    // spec: 12-runtime §12.2 — GOT def update stores code pointer and metadata
    #[test]
    fn test_update_def() {
        let mut state = ModuleCodegenState::new();
        let name = Symbol::from("bar");
        let slot = state.ensure_slot_for(&name).unwrap();
        let fake_ptr = 0xABCDusize as *const u8;
        state.update_def(&name, fake_ptr);

        assert_eq!(state.get_slot(slot), Some(fake_ptr));
        assert_eq!(state.def_codegen.get(&name).unwrap().code_ptr, Some(fake_ptr));
    }

    // spec: 12-runtime §12.2 — cross-eval GOT: mono defn slot visible to subsequent defns
    //
    // Simulates the REPL scenario: a constrained-poly function (`countdown`)
    // is defined in eval 1, then called in eval 2 (`main`). The monomorphised
    // specialization (`countdown$Int`) must get a GOT slot that is visible
    // when compiling the calling defn.
    #[test]
    fn test_mono_defn_got_slot_visible_across_evals() {
        let mut state = ModuleCodegenState::new();

        // Eval 1: register the base constrained fn (no codegen, just template).
        let countdown = Symbol::from("countdown");
        let _base_slot = state.ensure_slot_for(&countdown).unwrap();

        // Eval 2: monomorphisation produces `countdown$Int`.
        // The backend compiles it and registers a GOT slot.
        let mono_name = Symbol::from("countdown$Int");
        let mono_slot = state.ensure_slot_for(&mono_name).unwrap();
        let fake_ptr = 0x4242usize as *const u8;
        state.update_def(&mono_name, fake_ptr);

        // Now compile `main` which calls `countdown$Int`.
        // Build got_slots from def_codegen (as compile_and_register_defn does).
        let mut got_slots: std::collections::HashMap<Symbol, usize> = std::collections::HashMap::new();
        for (name, dc) in &state.def_codegen {
            if let Some(s) = dc.got_slot {
                got_slots.insert(name.clone(), s);
            }
        }

        // The mono defn's GOT slot must be visible.
        assert!(
            got_slots.contains_key(&mono_name),
            "countdown$Int must be in got_slots for main's compilation"
        );
        assert_eq!(got_slots[&mono_name], mono_slot);
        assert_eq!(state.get_slot(mono_slot), Some(fake_ptr));
    }

    // spec: 12-runtime §12.2 — multiple mono specializations get distinct GOT slots
    #[test]
    fn test_multiple_mono_specializations_distinct_slots() {
        let mut state = ModuleCodegenState::new();

        let add_int = Symbol::from("add$Int+Int");
        let add_float = Symbol::from("add$Float+Float");

        let slot_int = state.ensure_slot_for(&add_int).unwrap();
        let slot_float = state.ensure_slot_for(&add_float).unwrap();

        assert_ne!(slot_int, slot_float, "distinct specializations need distinct slots");

        // Verify both are retrievable from def_codegen.
        assert_eq!(state.def_codegen.get(&add_int).unwrap().got_slot, Some(slot_int));
        assert_eq!(state.def_codegen.get(&add_float).unwrap().got_slot, Some(slot_float));
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

    // spec: 12-runtime §12.2 — shared_got returns Arc sharing same memory
    #[test]
    fn test_shared_got_same_base() {
        let mut state = ModuleCodegenState::new();
        let base1 = state.got_base_ptr();
        let shared = state.shared_got();
        assert_eq!(base1, shared.base_ptr(), "shared GOT must have same base address");
    }
}
