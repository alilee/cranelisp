# Per-Module GOT Design

**Author:** `/arch`
**Date:** 2026-03-28 (updated 2026-04-19, Sprint 58 Wave 2 close: §9.2/§9.3/§9.4/§9.5 unified one-load shape)
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

### 9.2 Solution: Unified one-load GOT shape (Sprint 58 Wave 2)

**Updated Sprint 58 Wave 2** per Decision 23 (UPDATED with two-GOT framing) and Decision 36 (function bare names + `Linkage::Local`). Sprint 58 Wave 2 close unified the GOT-load shape across JIT and Object modes per `/sprint`'s direction "the same call will be used to load the got base from the literal pool in both jit and object." The previous two-load shape — where `__cranelisp_got_{module}` was a pointer cell containing the GOT table's heap address, requiring an extra load to dereference the pointer — is replaced by a one-load shape in which `__cranelisp_got_{module}` IS the GOT slab base directly.

In both modes, the symbol address `__cranelisp_got_{module}` IS the slab base. CLIF emits one less load; the same load mechanism resolves in JIT and Object modes:

- **JIT mode**: `__cranelisp_got_{module}` is registered with the JIT builder as `JITBuilder::symbol(name, GotTable.base_ptr())` — the symbol address resolves directly to the slab base. There is no pointer-cell indirection. The previous `Jit::define_got_data` helper (which defined a pointer-cell data symbol holding the slab address) is **deleted**; the symbol registration is folded into `extra_symbols` at the three call sites (priority worker, REPL eval, trace-extra-symbols path).
- **Object mode**: `__cranelisp_got_{module}` is defined inside the per-module `.o` via `CodeFinalizer::define_module_got_data(name, slot_count, slot_funcs)` (the trait method added in Sprint 58 Wave 2 per Decision 23 — see `compile-to-module.md` §5.3/§5.4). The implementation declares the symbol as `Linkage::Export` data of `slot_count * 8` bytes (regular `__DATA` section, NOT `__bss`) with function-address relocation initializers at byte offset `slot * 8` for each defined function. The system linker (`--link` mode) materialises the relocations into actual function addresses at load time. The symbol address IS the slab.

**`__bss` section discipline.** The Object-mode definition uses regular `__DATA` (with explicit zero-init bytes) rather than `__DATA,__bss` (`S_ZEROFILL`). macOS `ld` segfaults on `.o` files containing relocations in a `S_ZEROFILL` section because BSS has no file content for the linker to patch — the data must land in `__DATA,__data` for `ld` to apply the function-address relocations. Cranelift's `desc.define(vec![0u8; slot_count * 8].into_boxed_slice())` produces the correct section affinity; `desc.define_zeroinit(slot_count * 8)` does not.

### 9.3 Call Sequence (unified one-load shape)

```
  slab_base = global_value(__cranelisp_got_{module})   // GOT slab base address
  slot_addr = slab_base + slot * 8                      // address of slot
  fn_ptr    = load(slot_addr)                           // function pointer from GOT
  call_indirect(fn_ptr)
```

On aarch64 this is ADRP+LDR (system GOT pages, fetching the slab base address) + LDR (GOT slot) + BLR. **One load** from the slab itself (the actual dispatch); the address materialisation goes through the system's GOT-load relocation mechanism, not through a co-located literal pool entry holding a pointer cell.

How the symbol is registered/defined in each mode (the resolver behind the shared `__cranelisp_got_{module}` reference):

- **JIT mode**: `JITBuilder::symbol(name, GotTable.base_ptr())` — symbol address resolves to slab base directly. No pointer-cell indirection. Cranelift's data-symbol resolution returns `GotTable.base_ptr()` when the JIT finalizer encounters the `Linkage::Import` data reference emitted by `compile_to_module`.
- **Object mode**: `CodeFinalizer::define_module_got_data(name, slot_count, slot_funcs)` defines `__cranelisp_got_{M}` as `Linkage::Export` data of size `slot_count * 8` bytes (regular `__DATA`, NOT `__bss`) with function-address relocation initializers. Symbol address IS the slab. The system linker patches the slot bytes with the actual function addresses at load time.

This is the canonical illustration of Decision 23's two-GOT model: byte-identical CLIF in both modes, two resolvers behind the same data symbol. The CLIF emitted by `compile_to_module` is mode-agnostic — the FnCompiler does not know which `Module` impl resolves `__cranelisp_got_{M}` at finalize time. JIT mode resolves it to the live `Arc<GotTable>` slab base on `SymbolTable.got` (the SymbolTable GOT — read by `--run`/REPL); Object mode resolves it to the `.o` data section GOT slab the linker materialises (the `.o` data section GOT — read by `--link` mode's system linker, dormant in `--run`/REPL after cache-hit). Cross-references: Decision 23 (byte-identical CLIF — preserved by the unified shape); Decision 36 (function bare names + `Linkage::Local` — relocation initializers in Object mode point at intra-`.o` Local function symbols, which is correct because `.o`-local function symbols cannot collide across `.o`s); `design/arch/interfaces.md` §"Two-GOT model" subsection (the visual reference).

**Sprint 58 Wave 2 history note.** The shape described in §9.2/§9.3 above was OLD (two-load: ADRP+LDR (literal pool) + ADD+LDR (GOT slot) + BLR — first load fetching a pointer cell holding the slab base, second load fetching the function pointer). Sprint 58 Wave 2 close unified this to the one-load shape per `/sprint`'s direction "the same call will be used to load the got base from the literal pool in both jit and object." JIT mode's `Jit::define_got_data` helper was deleted as part of this unification; Object mode gained `CodeFinalizer::define_module_got_data` to publish the slab as a `Linkage::Export` data symbol with function-address relocation initializers.

### 9.4 Immutability Constraints

- **GOT tables are immovable.** Once allocated, a SymbolTable GOT slab's base address never changes. Loaded `.o` files' GOT data symbols hold their slab addresses through the system loader's relocation machinery — JIT-mode resolution writes the slab base into the JIT builder's `extra_symbols` once at module-build time, and Object-mode resolution materialises the `Linkage::Export` data symbol once at link/load time.
- **GOT entries are mutable.** Function pointers in GOT slots are `AtomicPtr` — updated when functions are redefined at the REPL via `store(Release)` per Decision 31's atomic-swap discipline.
- **GOT slab base address is fixed at module-build / load time.** In JIT mode, the slab base is registered with the JIT builder via `JITBuilder::symbol(name, GotTable.base_ptr())` once when the module is built. In Object mode, the slab base is the `__cranelisp_got_{M}` `Linkage::Export` data symbol's address inside the `.o`'s `__DATA` section, fixed when the system linker (or our cache `Linker`) loads the `.o`. Not updated thereafter; only slot CONTENTS mutate.

### 9.5 Unified Codegen

The same Cranelift IR (`global_value` + `iadd_imm` + `load`) is used for both JIT and object paths — one load to fetch the function pointer from the slot, no mode-specific codegen. This means:
- Object-loaded functions can be redefined at the REPL (the GOT entry is updated, all callers see the new pointer through the atomic-swap discipline of Decision 31).
- `--release` AOT compilation can optimize the GOT-base materialisation away when the slab base is a link-time constant (the slot load becomes a single absolute-address load).
- The CLIF is byte-identical between JIT and Object modes per Decision 23 — the only difference is which `Module` impl resolves `__cranelisp_got_{M}` at finalize time.

## 10. Risks

**Low**: Backend compiler changes are minimal. `resolve_got_entry` already handles cross-module GOT lookups. The `CompileContext` already has the right fields. The change is primarily in the integration layer (`pipeline.rs`, `session.rs`).

**Medium**: `fn_to_module` map construction. Building the correct mapping requires traversing import chains in symbol tables. Errors here would cause "no GOT slot" failures at runtime. Mitigated by the fact that the object path already does this correctly — the logic can be shared or adapted.

**Low**: Migration phases are independently testable. Each phase preserves all existing tests. Regressions are caught immediately.
