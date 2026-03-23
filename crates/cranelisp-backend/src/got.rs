// Global Offset Table (GOT) for interactive (REPL) mode.
//
// In Interactive mode, function calls go through a GOT slot so that
// redefining a function updates all call sites. In Batch mode, calls
// are direct and the GOT is not used.

use std::collections::HashMap;

use cranelisp_types::{CranelispError, Span, Symbol};

use crate::codegen_types::{DefCodegen, GOT_TABLE_SIZE};

/// Per-module codegen state. Owns the GOT and per-definition artifacts.
pub struct ModuleCodegenState {
    /// Global offset table: array of function pointers for indirect calls.
    /// Lazily allocated on first use.
    got_table: Option<Box<[*const u8; GOT_TABLE_SIZE]>>,
    /// Next available GOT slot index.
    next_got_slot: usize,
    /// Per-definition codegen artifacts.
    pub def_codegen: HashMap<Symbol, DefCodegen>,
}

// SAFETY: GOT contains raw pointers that are only dereferenced from the JIT
// execution thread. The ModuleCodegenState is not shared across threads.
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

    /// Ensure the GOT table is allocated, returning a mutable reference.
    fn ensure_got(&mut self) -> &mut [*const u8; GOT_TABLE_SIZE] {
        if self.got_table.is_none() {
            self.got_table = Some(Box::new([std::ptr::null(); GOT_TABLE_SIZE]));
        }
        self.got_table
            .as_mut()
            .unwrap_or_else(|| unreachable!("invariant: GOT just allocated"))
    }

    /// Get the base address of the GOT table, allocating if needed.
    pub fn got_base_ptr(&mut self) -> *const u8 {
        let got = self.ensure_got();
        got.as_ptr() as *const u8
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
        debug_assert!(
            slot < GOT_TABLE_SIZE,
            "invariant: GOT slot {slot} out of range"
        );
        got[slot] = ptr;
    }

    /// Get the function pointer at a GOT slot.
    pub fn get_slot(&self, slot: usize) -> Option<*const u8> {
        self.got_table
            .as_ref()
            .map(|got| got[slot])
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
}
