# Per-Module GOT Design

**Author:** `/arch`
**Date:** 2026-03-28 (updated 2026-04-10)
**Status:** Implemented
**Audience:** `/backend`, `/int`

## 1. Problem Statement

The reimplementation has two codegen paths:

- **Object path** (`compile_module_to_object` in `cache/object.rs`): already uses per-module GOTs. Each module's `.o` file declares its own `__cranelisp_got_<module>` data symbol, and cross-module calls reference the target module's GOT via imported data symbols. The linker resolves these at load time.

- **JIT path** (`codegen_and_execute` in `pipeline.rs`): uses a single flat `ModuleCodegenState` on `InMemWorkerState.got_state`. All functions from all modules share one `GotTable`, one `got_base_ptr`, one slot index namespace. The `got_slots: HashMap<Symbol, usize>` passed to `CompileContext` is a flat map of every known function to a slot in the single GOT.

This flat model has three problems:

1. **Parallel codegen contention.** With a single `ModuleCodegenState`, codegen workers compiling different modules must all synchronize on slot allocation and def_codegen writes. The Sprint 40a design puts `inmem_worker` behind a `Mutex`, but workers would need to lock it for every slot lookup.

2. **GOT capacity.** `GOT_TABLE_SIZE` is 1024 slots shared across all modules. A program with 10 modules averaging 50 exported functions fills half the GOT. With stdlib, prelude, and user code, this is tight.

3. **Incoherence with the object path.** The object path's per-module GOT data symbols (`__cranelisp_got_<module>`) have no JIT-path counterpart. Cache-hit loading must bridge between the two models — the linker resolves per-module data symbols to addresses inside a single flat GOT. This works but is fragile and limits future evolution (e.g., per-module GOT resizing, module unloading).

### Sketch Comparison

The sketch uses per-module GOTs in the object path (same `__cranelisp_got_<module>` convention). Its JIT path also uses a flat GOT — the same problem exists there. The reimplementation should fix this rather than carry the debt forward.

## 2. Target State

Each module gets its own `GotTable` and its own `ModuleCodegenState`. Functions compiled in module A use module A's GOT base pointer. Cross-module calls look up the target function's owning module, then use that module's GOT base + the function's slot index within that module's GOT.

This matches the object path's model exactly: each module owns a GOT, cross-module references are by `(module, slot)` pairs.

## 3. Data Structures

### 3.1 `ModuleGotRegistry` (new, on `InMemWorkerState`)

Replaces the current `got_state: ModuleCodegenState` field.

```rust
/// Registry of per-module GOT tables for the JIT path.
///
/// Each module gets its own `ModuleCodegenState` with its own `GotTable`.
/// Slot indices are local to each module (slot 0 in module A is independent
/// of slot 0 in module B).
pub struct ModuleGotRegistry {
    /// Per-module codegen state. Each module has its own GOT table
    /// and its own slot namespace.
    module_gots: HashMap<ModuleFullPath, ModuleCodegenState>,
}

impl ModuleGotRegistry {
    pub fn new() -> Self {
        ModuleGotRegistry {
            module_gots: HashMap::new(),
        }
    }

    /// Get or create the ModuleCodegenState for a module.
    pub fn ensure_module(&mut self, module: &ModuleFullPath) -> &mut ModuleCodegenState {
        self.module_gots.entry(module.clone()).or_default()
    }

    /// Get the ModuleCodegenState for a module (read-only).
    pub fn get_module(&self, module: &ModuleFullPath) -> Option<&ModuleCodegenState> {
        self.module_gots.get(module)
    }

    /// Get the ModuleCodegenState for a module (mutable).
    pub fn get_module_mut(&mut self, module: &ModuleFullPath) -> Option<&mut ModuleCodegenState> {
        self.module_gots.get_mut(module)
    }

    /// Build a FnSlotMap for compilation of a given module.
    ///
    /// Returns the local GOT slots (for the module's own functions)
    /// and a CrossModuleGot map for imported functions.
    pub fn build_compilation_maps(
        &self,
        module: &ModuleFullPath,
        imports: &HashMap<Symbol, ModuleFullPath>,  // fn_name -> owning module
    ) -> (HashMap<Symbol, usize>, i64, CrossModuleGot) {
        let local_state = self.module_gots.get(module);

        // Local slots: functions defined in this module.
        let mut local_slots: HashMap<Symbol, usize> = HashMap::new();
        let mut got_base: i64 = 0;
        if let Some(state) = local_state {
            got_base = state.got_base_ptr_readonly()
                .map(|p| p as i64)
                .unwrap_or(0);
            for (name, dc) in &state.def_codegen {
                if let Some(slot) = dc.got_slot {
                    local_slots.insert(name.clone(), slot);
                }
            }
        }

        // Cross-module slots: functions imported from other modules.
        let mut cross_module: CrossModuleGot = HashMap::new();
        for (fn_name, owning_module) in imports {
            if let Some(owner_state) = self.module_gots.get(owning_module) {
                if let Some(dc) = owner_state.def_codegen.get(fn_name) {
                    if let Some(slot) = dc.got_slot {
                        let owner_base = owner_state.got_base_ptr_readonly()
                            .map(|p| p as i64)
                            .unwrap_or(0);
                        cross_module.insert(
                            (owning_module.clone(), fn_name.clone()),
                            (owner_base, slot),
                        );
                    }
                }
            }
        }

        (local_slots, got_base, cross_module)
    }
}
```

### 3.2 `InMemWorkerState` Changes

```rust
pub struct InMemWorkerState {
    /// Per-module GOT registry (replaces flat got_state).
    pub got_registry: ModuleGotRegistry,
    /// JIT instances that must stay alive.
    pub jit_modules: Vec<Jit>,
    // ... traced_fns, trace_extra_symbols, cache_linkers unchanged ...
}
```

### 3.3 `ModuleCodegenState` Addition

Add a read-only base pointer accessor that does not force allocation:

```rust
impl ModuleCodegenState {
    /// Get the GOT base pointer without allocating.
    /// Returns None if the GOT has not been allocated yet.
    pub fn got_base_ptr_readonly(&self) -> Option<*const u8> {
        self.got_table.as_ref().map(|got| got.base_ptr())
    }
}
```

### 3.4 `FnSlotEntry` (new boundary type in `cranelisp-types`)

```rust
/// Identifies a function's GOT location: which module's GOT and which slot.
///
/// Used in CodegenItem and cache metadata to communicate GOT assignments
/// from the integration layer to codegen workers.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FnSlotEntry {
    /// The module that owns the GOT containing this function's slot.
    pub module: ModuleFullPath,
    /// Slot index within that module's GOT.
    pub slot_index: usize,
}
```

### 3.5 `CodegenItem` Changes

The `CodegenPacket.got_slot_map` currently maps `Symbol -> usize` (flat slot index). This changes to carry per-module information:

```rust
pub struct CodegenPacket {
    // ... existing fields ...

    /// GOT slot map for this module's own functions.
    /// Maps function name -> slot index within this module's GOT.
    pub local_got_slots: HashMap<Symbol, usize>,

    /// GOT base pointer for this module's own GOT table.
    pub local_got_base: i64,

    /// Cross-module GOT for imported functions.
    /// Maps (owning_module, fn_name) -> (got_base_ptr, slot_index).
    pub cross_module_got: CrossModuleGot,

    /// Shared GOT table for THIS MODULE's atomic code pointer writes.
    pub shared_got: Option<Arc<GotTable>>,

    // REMOVED: got_slot_map: HashMap<Symbol, usize>  (was flat)
    // REMOVED: shared_got that pointed to the global flat table
    // ... shared_isa unchanged ...
}
```

## 4. How Compilation Works

### 4.1 Slot Allocation (in `compile_unit`, stages 1-5)

Before codegen, `compile_unit` (or `codegen_and_execute`) allocates GOT slots for the module being compiled. This happens on the main thread, under the `inmem_worker` mutex:

```rust
// Inside codegen_and_execute, before enqueuing:
let inmem = session.inmem_worker.lock().unwrap();
let module_state = inmem.got_registry.ensure_module(&ctx.module);

// Pre-allocate slots for all functions in this module.
for defn in &program {
    if let TopLevel::Defn(d) = defn {
        module_state.ensure_slot_for(&d.name)?;
    }
}
// Also for mono defns, default method defns, etc.

// Build the compilation maps.
let (local_slots, local_base, cross_module) =
    inmem.got_registry.build_compilation_maps(&ctx.module, &fn_to_module);
```

The `fn_to_module` map (`HashMap<Symbol, ModuleFullPath>`) is derived from the module's import declarations and the symbol tables. It maps each imported function name to its defining module. This is the same information the object path uses (`ObjectCompileInput.fn_to_module`).

### 4.2 JIT Compilation

The backend's `CompileContext` already has the right shape:

```rust
pub struct CompileContext<'a> {
    // ...
    pub got_slots: Option<&'a HashMap<Symbol, usize>>,        // local module slots
    pub got_base_ptr: Option<i64>,                              // local module GOT base
    pub cross_module_got: Option<&'a CrossModuleGot>,          // imported fn GOT refs
    // ...
}
```

Currently `got_slots` is flat (all modules) and `cross_module_got` is always `None`. After this change:

- `got_slots` contains only this module's functions' slot indices.
- `got_base_ptr` is this module's GOT base address.
- `cross_module_got` contains entries for every imported function.

The `resolve_got_entry` method in `apply.rs` already handles both paths correctly — it checks local GOT first, then cross-module GOT. No changes needed in the backend compiler logic.

### 4.3 After Compilation

After JIT compilation, the worker writes code pointers to the module's `GotTable` via atomic stores (same as today). The `Jit` instance is pushed to `jit_modules` (or `jit_collector` in async mode).

## 5. How Parallel Codegen Works

Each worker receives a `CodegenPacket` (or equivalent) containing:

- `local_got_slots` + `local_got_base` for the module's own GOT.
- `cross_module_got` for imported functions.
- `shared_got: Arc<GotTable>` for this module's GOT table (cloned from the module's `ModuleCodegenState`).

Workers compile independently:

1. Worker A compiles module `core.option` into `core.option`'s GOT.
2. Worker B compiles module `user` into `user`'s GOT.
3. No contention: each writes to a different `GotTable`.

Cross-module references work because `cross_module_got` entries carry the *owning module's* GOT base pointer. Worker B compiling `user` has an entry like `(core.option, "Some") -> (0x7f00..., 3)` meaning "function `Some` is at slot 3 of the GOT table at address `0x7f00...`". This address is stable because `GotTable` is heap-allocated (boxed array) and never moves.

### 5.1 Ordering Constraint

Cross-module GOT base pointers must be known before a dependent module can compile. This means the dependency module's `GotTable` must be allocated before the dependent module's `CodegenPacket` is built.

Since `compile_unit` runs dependencies before dependents (topological order on the main thread), this is naturally satisfied: by the time the main thread builds `user`'s `CodegenPacket`, `core.option`'s `ModuleCodegenState` already exists with an allocated `GotTable`.

Slot *contents* (code pointers) do not need to be filled before a dependent compiles — the compiled code reads slots via GOT-indirect loads at runtime, not at compile time. The slot just needs to be populated before execution (`hot_flush` barrier ensures this).

## 6. Cache-Hit Loading

### 6.1 `.meta.json` Slot Map

The cached `.meta.json` already stores `got_slots: HashMap<Symbol, usize>` — these are slot indices relative to the module's own GOT. This is already per-module (matching the object path).

### 6.2 JIT Cache-Hit Load

When loading a cached `.o` via `Linker`:

1. Create or look up the target module's `ModuleCodegenState` in `got_registry`.
2. For each slot in the cached `got_slots`, ensure the slot exists (using `ensure_slot_for` or by bumping `next_got_slot` to at least `max_slot + 1`).
3. The `Linker` resolves the `__cranelisp_got_<module>` data symbol to the module's `GotTable` base address. The linker also resolves imported modules' GOT symbols to their respective base addresses.
4. After linking, function code pointers are written into the correct module's GOT slots.

This is cleaner than today's approach where the linker must map per-module data symbols to offsets within a single flat GOT.

## 7. `fn_to_module` Map Construction

The integration layer must build a `HashMap<Symbol, ModuleFullPath>` mapping each function name visible to the module being compiled to its defining module. Sources:

1. **Imports**: The module's `ModuleStructure.imports` declares which modules are imported. For each imported symbol, look up the defining module in the symbol table.
2. **Prelude**: Prelude-injected symbols come from the `prelude` module (and transitively from `core.*` modules).
3. **Local definitions**: Functions defined in this module map to `ctx.module`.

This map is analogous to `ObjectCompileInput.fn_to_module` in the object path. The integration layer already has access to the symbol tables needed to build it.

## 8. Migration Path

### Phase 1: Internal restructuring (no behavior change)

1. Add `ModuleGotRegistry` to `got.rs`.
2. Add `got_base_ptr_readonly()` to `ModuleCodegenState`.
3. Replace `InMemWorkerState.got_state: ModuleCodegenState` with `got_registry: ModuleGotRegistry`.
4. In `codegen_and_execute`, route all GOT operations through `got_registry.ensure_module(&ctx.module)` instead of `got_state` directly.
5. **Key invariant for this phase**: all modules still route through a single entry in the registry (e.g., everything under `ModuleFullPath::from("user")`). This means behavior is identical — one module, one GOT. Tests pass without change.

### Phase 2: Populate `cross_module_got`

6. Build `fn_to_module` map in `codegen_and_execute` from symbol table imports.
7. Call `got_registry.build_compilation_maps()` to produce `local_slots`, `local_base`, and `cross_module_got`.
8. Pass `cross_module_got` through to `CompileContext` (currently always `None`).
9. `resolve_got_entry` in `apply.rs` now uses cross-module lookups for imported functions.

**Test**: Multi-module programs work correctly — imported functions are called via the owning module's GOT.

### Phase 3: Per-module slot namespaces

10. Each module gets its own slot counter (slot 0 per module). Currently all modules share a global counter.
11. Each module gets its own `GotTable` allocation.
12. Cache-hit loading creates per-module `GotTable` instances.

**Test**: GOT capacity is no longer shared. A 10-module program uses 10 independent GOT tables.

### Phase 4: Wire into parallel codegen

13. `CodegenPacket` carries per-module GOT info (§3.5).
14. Workers use module-local `Arc<GotTable>` for atomic writes.
15. No `inmem_worker` mutex needed during compilation — only during slot allocation on the main thread.

## 9. GOT Base Literal Pool (Unified Codegen)

### 9.1 Problem: ADRP Range

On aarch64, `global_value(DataId)` in PIC mode lowers to ADRP+LDR with ±4GB range. GOT tables are heap-allocated (`Box<[AtomicPtr; N]>` inside `Arc<GotTable>`) and may be >4GB from loaded object code. ADRP cannot reach them directly.

### 9.2 Solution: Literal Pool Entries

Each `__cranelisp_got_{module}` data symbol is an 8-byte literal pool entry containing the GOT table's heap address. The entry is co-located with the code:

- **JIT mode**: defined as data in the JIT module (`Jit::define_got_data`), content is the `GotTable::base_ptr()` value. `global_value` materializes the entry address via `movz+movk`.
- **Object mode**: defined as Export data in the .o's data section (8 bytes, zeroed). The linker patches it with the actual `GotTable` address at load time. ADRP+LDR reaches the entry because it's in the same .o / mmap region.

### 9.3 Call Sequence

```
  entry_addr = global_value(__cranelisp_got_{module})  // address of literal pool entry
  got_base   = load(entry_addr)                         // GOT table base address
  fn_ptr     = load(got_base + slot * 8)                // function pointer from GOT
  call_indirect(fn_ptr)
```

On aarch64 this is ADRP+LDR (literal pool) + ADD+LDR (GOT slot) + BLR. Two loads: one to get the GOT base from the literal pool, one to get the function pointer from the GOT. The first load is from co-located data (always reachable); the second is the actual dispatch.

### 9.4 Immutability Constraints

- **GOT tables are immovable.** Once allocated, a GOT's base address never changes. Any number of literal pool entries across any number of loaded .o files may hold this address — they cannot all be found and updated.
- **GOT entries are mutable.** Function pointers in GOT slots are `AtomicPtr` — updated when functions are redefined at the REPL via `store(Release)`.
- **Literal pool entries are fixed at load time.** Written once when the .o is loaded (linker fixup) or when the JIT module is created (`define_got_data`). Not updated thereafter.

### 9.5 Unified Codegen

The same Cranelift IR (`global_value` + `load` + `iadd_imm` + `load`) is used for both JIT and object paths. No mode-specific codegen. This means:
- Object-loaded functions can be redefined at the REPL (the GOT entry is updated, all callers see the new pointer).
- `--release` AOT compilation can optimize the literal pool load away (inline the GOT base as a link-time constant).

## 10. Risks

**Low**: Backend compiler changes are minimal. `resolve_got_entry` already handles cross-module GOT lookups. The `CompileContext` already has the right fields. The change is primarily in the integration layer (`pipeline.rs`, `session.rs`).

**Medium**: `fn_to_module` map construction. Building the correct mapping requires traversing import chains in symbol tables. Errors here would cause "no GOT slot" failures at runtime. Mitigated by the fact that the object path already does this correctly — the logic can be shared or adapted.

**Low**: Migration phases are independently testable. Each phase preserves all existing tests. Regressions are caught immediately.
