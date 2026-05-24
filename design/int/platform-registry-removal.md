# Platform Registry Removal — G8 Design

**Sprint**: 57 (Phase 4 Step 4a of `design/arch/pipeline-v4-roadmap.md`); refreshed Sprint 68 per FIXME 0162 to reflect the S66 fn_ptr unification (commit `b09ec76`) and its same-day rollback (`1dc57ae`).
**Owner**: `/int` + `/platform` (co-design).
**Status**: Implemented + refreshed-for-coherence post-S66 rollback. The substance — delete `PlatformRegistry`; cross-module platform-fn resolution follows Import chains to the defining `ModuleEntry::Def` — landed in Sprint 57 Wave 3 and remains correct. **Only the storage location of the runtime call pointer has moved**: it is no longer a `platform_fn_ptr: Option<*const u8>` field on `ModuleEntry::Def` (that field briefly existed via the S66 unification and was rolled back the same day). Per Decision 35's post-rollback canonical statement, the **GOT is the single source of truth for callable addresses**. The platform-fn pointer for a `PrimitiveKind::PlatformEffect` entry lives in the per-module `GotTable`, indexed by `ModuleEntry::Def.got_slot`. Read via `entry_owning_module.got().load_slot(entry.got_slot.unwrap())`; written via `symbol_table.got().store_slot(slot, desc.ptr)`.

This document covers the original G8 migration plus the post-S66 rollback storage location. The PlatformRegistry-deletion substance is unchanged; the §"platform_fn_ptr field" language across this doc is updated below to read against the per-module GOT.

`/arch` Decision 26 establishes the shape. This doc fixes the `scheduling_class` placement (§3 below), the registration path (§4), the IO trampoline migration (§5), and error handling (§5.3). For the post-rollback canonical statement see `design/arch/decisions/0035-code-enum-integration-layer.md` §"Amendment (Sprint 66 — rollback, 2026-05-09)" and `design/arch/decisions/0041-compile-to-module-per-symbol-jit-direct-writes.md` §"S66 amendment + rollback".

## 1. References

- `design/arch/decisions/0035-code-enum-integration-layer.md` §"Amendment (Sprint 66 — rollback, 2026-05-09)" — **the post-rollback canonical statement: GOT is the single source of truth for callable addresses; no per-entry pointer field.**
- `design/arch/decisions/0041-compile-to-module-per-symbol-jit-direct-writes.md` §"S66 amendment + rollback" — same post-rollback canon for primitive/JIT cardinality interactions.
- `design/arch/legacy/decisions/0026-platform-fn-pointers-on-moduleentry-def.md` §"Postscript (Sprint 66 — fn_ptr unification + rollback)" — superseded; the original `platform_fn_ptr` field location.
- `crates/cranelisp-types/src/module.rs` `ModuleEntry::Def.got_slot` rustdoc + `design/arch/bounded-contexts.md` §7.
- `crates/cranelisp-types/src/module.rs` `ModuleEntry::Def` (no `fn_ptr` field, no `platform_fn_ptr` field — just `got_slot: Option<usize>`).
- `crates/cranelisp-types/src/got.rs` (`GotTable` API — `load_slot`, `store_slot`, `base_ptr`).
- `src/worker.rs` `handle_platform` and `collect_jit_setup` — the GOT-slot read/write patterns landed per the rollback commit.
- `design/arch/pipeline-v4.md` §3.4 (platform loading), §9.1 (SymbolTable single store), §9.6 (introspection separate).
- `design/arch/pipeline-v4-roadmap.md` Phase 4 Step 4a (G8).
- `sprints/SPRINT.md` §Architecture Review condition 3 (scheduling_class placement decided in Wave 1).
- `design/int/bind-chain-analysis.md` — downstream consumer of `scheduling_class`.
- `design/int/io-integration.md` — platform DLL loading and registration handshake.
- `crates/cranelisp-platform/src/lib.rs` — `SchedulingClass` enum, `PlatformFn` C-ABI, `call_effect_thunk`.

## 2. Current state

### 2.1 PlatformRegistry shape

`src/platform_registry.rs` defines:

```rust
pub struct PlatformFunction {
    pub jit_name: JitSymbol,      // "cranelisp_print"
    pub fn_ptr: *const u8,         // into the loaded DLL
    pub scheduling_class: SchedulingClass,
}

#[derive(Default)]
pub struct PlatformRegistry {
    entries: HashMap<FQSymbol, PlatformFunction>,
}
```

Session-level field: `CompilerSession.platform_registry: PlatformRegistry` (swapped in/out of a `Mutex<PlatformRegistry>` during worker execution — `src/session_v4.rs:993–1026` and `:1088–1128`). Populated during platform DLL loading; read at codegen time and at bind-chain-analysis time; held for process lifetime because the pointers remain valid only while the DLL is loaded (handled separately by `loaded_platforms`).

### 2.2 Writers

One writer. `handle_platform` in `src/worker.rs:1454–1493`:

```rust
for desc in &platform.descriptors {
    let fq = FQSymbol {
        module: ModuleFullPath::from(format!("platform.{}", platform.name)),
        symbol: Symbol::from(desc.name.as_str()),
    };
    ctx.platform_registry.register(fq, PlatformFunction {
        jit_name: JitSymbol::from(desc.jit_name.clone()),
        fn_ptr: desc.ptr,
        scheduling_class: desc.scheduling_class,
    });
}
```

Called by the worker when a `(platform "name")` form is encountered during form processing. The platform DLL is loaded via `crate::platform::load_and_register_platform` before this loop runs; that same call has already populated the `SymbolTable` with `ModuleEntry::Def` entries carrying `DefKind::Primitive { primitive_kind: PrimitiveKind::PlatformEffect, jit_name: Some(desc.jit_name) }` for each function (see `src/platform.rs` — the type signatures go on the symbol table; the code pointers go on the registry). The registry and the symbol table are therefore populated in the same loop but written to separate stores.

### 2.3 Readers

Three distinct readers:

- **`collect_jit_setup`** (`src/worker.rs:2113–2157`) — iterates the module's symbol table looking for `PlatformEffect` primitives and Import entries that resolve to them, then calls `platform_registry.fn_ptr_by_jit_name(jit_name)` for each. Produces `jit_symbols: Vec<(String, *const u8)>` registered on the `JITBuilder` before `compile_to_module`. This is the "link-time" platform-fn read.
- **`bind_chain_analysis.rs` `classify_expr`** (`src/bind_chain_analysis.rs:137–155, 397–410`) — consults `registry.scheduling_class(name)` during the auto-scheduling pass over `bind!` chains. Reads only `scheduling_class`, not `fn_ptr` or `jit_name`. This is the typecheck/scheduling-time platform-metadata read.
- **IO trampoline — indirect** (`crates/cranelisp-runtime/src/io.rs:63` `run_io_trampoline`) — does NOT read the registry directly. Instead it dereferences an `Effect` node's `thunk_ptr` (a heap-boxed closure prepared at codegen time with the DLL fn pointer baked in) via `cranelisp_platform::call_effect_thunk`. The "IO trampoline resolves platform functions by symbol-table lookup" language in the sprint text is slightly loose — the trampoline itself does not see the registry, but the codegen that *builds* effect thunks does. In the Phase 4 G8 target, the codegen builder is what consults the symbol table instead of `PlatformRegistry`.

A fourth reader exists in tests (`PlatformRegistry::with_test_entries`) and is a test harness, not a production consumer.

### 2.4 PlatformRegistry public API

| Method | Used by | Disposition under G8 |
|--------|---------|-----------------------|
| `register` | `handle_platform` (worker.rs:1481) | DELETED — worker writes to the symbol-table entry directly. |
| `scheduling_class(&Symbol)` | `bind_chain_analysis.rs` | DELETED — `bind_chain_analysis` reads from symbol table (see §3 for exact shape). |
| `jit_symbols()` / `jit_symbols_owned()` | Only `collect_jit_setup` reads these via `fn_ptr_by_jit_name` lookups; pure `jit_symbols()` / `_owned()` are now only referenced by dead "legacy" code per the doc-comments on lines 69 and 81. | DELETED. |
| `fn_ptr_by_jit_name(&JitSymbol)` | `collect_jit_setup` (worker.rs:2129, 2142) | DELETED — `collect_jit_setup` reads the entry's `got_slot`, then `entry_owning_module.got().load_slot(slot)` for the runtime address. (Post-S66 rollback: there is no `platform_fn_ptr` field on `ModuleEntry::Def`; the GOT slot is the single source of truth per Decision 35.) |
| `is_empty()` | Test helpers only | DELETED with the struct. |
| `with_test_entries` (cfg(test)) | Tests | DELETED; test rewiring covered in §7. |

After G8, no surviving Rust type named `PlatformRegistry` exists. The `PlatformFunction` DTO is also deleted — its fields split: `jit_name` is on `DefKind::Primitive.jit_name`; `fn_ptr` is written to the per-module `GotTable` slot indexed by `ModuleEntry::Def.got_slot` (no `platform_fn_ptr` entry-field — see post-S66 rollback note in §1); `scheduling_class` moves per §3.

## 3. `scheduling_class` placement — Option A vs Option B

`/arch` Decision 26 flags this as an open Wave 1 call. Two options:

- **Option A**: separate sibling field on `ModuleEntry::Def`:
  ```rust
  ModuleEntry::Def {
      // …
      scheduling_class: Option<SchedulingClass>,
      // (no `platform_fn_ptr` sibling — post-S66 rollback, the runtime fn ptr
      // lives in the per-module GotTable slot indexed by got_slot. The S66
      // unification briefly introduced a sibling `fn_ptr` field; it was
      // rolled back the same day per `1dc57ae` because the GOT is the single
      // source of truth — Decision 35 post-rollback canon.)
      got_slot: Option<usize>,
      // …
  }
  ```
  Always present; `Some` only when `kind == Primitive { primitive_kind: PlatformEffect, .. }`.

- **Option B**: variant field inside `PrimitiveKind::PlatformEffect`:
  ```rust
  enum PrimitiveKind {
      // …
      PlatformEffect { scheduling_class: SchedulingClass },
      // …
  }
  ```
  Exists only for the category that carries it. Readers destructure `kind` to access it.

### 3.1 Recommended choice: **Option B**

Rationale:

1. **Principle 6 (complexity budget)**: Option A allocates one `Option<SchedulingClass>` on every `ModuleEntry::Def`. Most entries are user functions, type defs, constructors, macros — none of which carry a scheduling class. Option B restricts the field to the kind that actually has meaning. For a typical program this is ~15 entries vs ~thousands.
2. **Principle 7 (single source of truth)**: Option A admits ill-formed states — a `Def` with `kind: UserFn { .. }` but `scheduling_class: Some(..)` — that the type system cannot reject. Option B makes the invariant structural: if you can read the scheduling class, you already know the entry is a platform effect. No runtime assertion or "must be Some if kind is X" comment.
3. **Existing precedent**: `PrimitiveKind` already carries kind-specific data (`jit_name: Some(_)` is the extern name for a `Primitive`). Extending the PlatformEffect variant follows the same pattern.
4. **Reader ergonomics**: `bind_chain_analysis.rs:classify_expr` already walks a `ModuleEntry::Def` looking for platform-effect-ness. The walk becomes:
   ```rust
   if let ModuleEntry::Def { kind: DefKind::Primitive { primitive_kind: PrimitiveKind::PlatformEffect { scheduling_class }, .. }, .. } = entry {
       return *scheduling_class;
   }
   ```
   One destructure, both the kind-check and the class-read fused. Option A requires two reads and an `Option::expect` / `unwrap_or_default`.

### 3.2 Cost of Option B

1. Every constructor of `PrimitiveKind::PlatformEffect` must now pass a `scheduling_class`. Audit: currently only one constructor — the `register_platform_primitives` path in `src/platform.rs` (and sketch lineage). The `SchedulingClass` is already in scope there from the manifest; no new plumbing needed.
2. Pattern matches that destructure `PrimitiveKind::PlatformEffect` (today there are two in `bind_chain_analysis.rs` and one in `collect_jit_setup`) must bind `scheduling_class` explicitly (or `..`). Trivial diff.
3. Serialization: `SchedulingClass` derives `Serialize + Deserialize` (it is `#[repr(u32)]` on a small enum in `cranelisp-platform`). The variant field will serialise naturally — no `#[serde(skip)]` because `scheduling_class` is static manifest data, not runtime state. This is different from the runtime fn pointer, which is **not persisted at all** post-S66 rollback — `GotTable` slots hold `AtomicPtr<u8>` runtime addresses in non-serialised memory, re-populated on every session start (cold start: by `handle_platform`; cache-hit load: by the platform-reload pass that walks the persisted `PlatformDecl` list).

### 3.3 `/arch` Decision 26 alignment

Decision 26's preference is Option B (tighter scope), with the call deferred to `/int`. This design records **Option B** as the `/int` position, with the rationale above. Decision 26 text should be updated to reflect the final call after Wave 1 review. `/platform` concurrence is expected via the FIXME(/platform) stub below; if `/platform` disagrees, the shape moves to Option A (the invariants still hold, the accommodation is one extra `Option` field).

<!-- FIXME(/platform): confirm Option B (scheduling_class inside PrimitiveKind::PlatformEffect variant) aligns with the DLL manifest flow and bind-chain analysis. /platform owns crates/cranelisp-platform/ and may have visibility into a scheduling_class evolution (ResourceSerial token shape, future variants) that affects the choice between A and B. If Option A is preferred, edit this section in place or respond with rationale. -->

## 4. Registration path — where the pointer is written

### 4.1 Sequence under G8

1. Form processing encounters `(platform "name")` in the entry module.
2. `crate::platform::load_and_register_platform` runs (unchanged from today):
   - Resolves the DLL path, `dlopen`s, reads the C-ABI manifest.
   - For each `PlatformFn` descriptor in the manifest, registers a `ModuleEntry::Def` on `symbol_tables["platform.{name}"]` with:
     - `scheme`: the function type (from the type string in the manifest).
     - `kind: Box::new(DefKind::Primitive { primitive_kind: PrimitiveKind::PlatformEffect { scheduling_class: desc.scheduling_class }, jit_name: Some(JitSymbol::from(desc.jit_name.clone())) })`. **This is where Option B's `scheduling_class` flows in.**
     - `ast: None` (platform primitives have no Cranelisp body).
     - `got_slot: Some(slot)` — GOT slot allocated via `SymbolTable::allocate_got_slot()` for cross-module calls; the slot itself starts holding a null `AtomicPtr<u8>`, populated in step 3.
     - `code: None` — no compiled Cranelisp code (the DLL owns the native code).
   - Stores the DLL handle in `loaded_platforms` (keeps the DLL alive).
3. After `load_and_register_platform` returns, the worker iterates `platform.descriptors` a second time (or folds this into the loop in `load_and_register_platform`; see §4.2) and for each descriptor reads the entry's `got_slot` and writes the runtime fn ptr to the per-module `GotTable`:
   ```rust
   let module_path = ModuleFullPath::from(format!("platform.{}", platform.name));
   let table = symbol_tables.get(&module_path)
       .ok_or_else(|| /* internal error: platform module missing */)?;
   if let Some(ModuleEntry::Def { got_slot: Some(slot), .. }) = table.get(desc.name.as_ref()) {
       table.got().store_slot(*slot, desc.ptr);
   }
   ```
   (Post-S66 rollback: there is no `platform_fn_ptr` field on `ModuleEntry::Def`. The GOT-store is via the per-module `Arc<GotTable>` reached through `SymbolTable.got()`, which is the canonical `AtomicPtr<u8>` write per Decision 35.)
4. No registry write. `ctx.platform_registry` field vanishes.

### 4.2 `/platform` surface — where the write lands

The write belongs in `crate::platform::load_and_register_platform` (owned by `/platform` / integration co-ownership). Reasons:
1. That function already has `SchedulingClass`, `fn_ptr`, the descriptor, and a mutable `symbol_tables` handle in scope.
2. Splitting the write across two loops (one in `load_and_register_platform` for type info, another in `handle_platform` for the pointer) re-creates the dual-store pattern G8 is deleting.
3. `handle_platform` in `worker.rs` reduces to: call `load_and_register_platform`, done. No post-loop bookkeeping.

The signature of `load_and_register_platform` likely gains a `&DashMap<ModuleFullPath, SymbolTable>` parameter or evolves to return the `Vec<PlatformFn>` descriptors for the caller to loop. `/platform` makes the call in its Wave 1 design.

(Historical: the inline `FIXME(/platform)` that lived here is resolved — write lands inside `load_and_register_platform` per the rollback commit's worker.rs changes; the inline FIXME protocol is retired per Sprint 63 M7 anyway.)

### 4.3 Invariant

**Typecheck-time invariant**: every `ModuleEntry::Def { kind: Primitive { primitive_kind: PlatformEffect { .. }, .. }, .. }` has `got_slot: Some(slot)`, and `entry_owning_module.got().load_slot(slot)` returns a non-null ptr post-`handle_platform`. Violation = internal error. The transient between slot allocation (§4.1 step 2) and pointer write (§4.1 step 3) is guarded by the same lock that gates the platform-form processing; once `handle_platform` returns successfully, the slot's `AtomicPtr<u8>` is populated.

This means **runtime** readers (bind-chain analysis, codegen's effect-thunk builder, IO trampoline codegen) can read `entry_owning_module.got().load_slot(entry.got_slot.unwrap())` and trust it is non-null. The only check is the kind discriminant. A null slot for a `PlatformEffect` is an internal bug, not a user-facing error.

## 5. IO trampoline migration

### 5.1 Clarification — what "IO trampoline resolves platform fns by symbol-table lookup" means

The runtime `run_io_trampoline` in `crates/cranelisp-runtime/src/io.rs:63` does not read `PlatformRegistry` and will not read `symbol_tables` after G8 either. The trampoline consumes already-built `Effect` heap nodes whose `thunk_ptr` field points at a boxed closure that captures the DLL function pointer at *construction* time. The migration affects the **constructor** of those `Effect` nodes (the codegen path + any Rust-side effect builders in the runtime), not the trampoline's inner loop.

The constructors are of two kinds:
1. **Cranelisp-emitted effect calls**: when codegen encounters a call to a `PlatformEffect` primitive, it emits code that builds an `Effect` node with a thunk that invokes the DLL fn. Today this flows through `collect_jit_setup` + JIT symbol registration (`Linkage::Import` resolved to the pointer discovered via `fn_ptr_by_jit_name`). After G8, the pointer is read off the symbol-table entry in the same place — see §5.2.
2. **Runtime-emitted effect calls** (if any — e.g. IO platform thunks constructed by `cranelisp_platform::CLIO::effect()` inside a DLL): these are inside the loaded DLL and do not go through any registry; the DLL captures its own function pointers at load time. Unaffected by G8.

Only (1) changes. (2) continues to work because the DLL's view of itself is stable.

### 5.2 The actual read-site change

`collect_jit_setup` (worker.rs:2113) and `collect_jit_setup_public` (worker.rs:2166) are the migration targets. Today:

```rust
if let DefKind::Primitive {
    primitive_kind: PrimitiveKind::PlatformEffect,
    jit_name: Some(jit_name),
} = kind.as_ref()
    && let Some(ptr) = platform_registry.fn_ptr_by_jit_name(jit_name)
{
    jit_symbols.push((jit_name.0.clone(), ptr));
}
```

After G8 (post-S66 rollback shape):

```rust
if let ModuleEntry::Def {
    kind,
    got_slot: Some(slot),
    ..
} = entry
    && let DefKind::Primitive {
        primitive_kind: PrimitiveKind::PlatformEffect { .. },  // Option B — no need to bind scheduling_class here
        jit_name: Some(jit_name),
    } = kind.as_ref()
{
    let ptr = entry_owning_module.got().load_slot(*slot);
    if !ptr.is_null() {
        jit_symbols.push((jit_name.0.clone(), ptr));
    }
}
```

The `platform_registry` parameter disappears from both functions' signatures (and from every caller — `inline_jit_codegen_for_names`, `inline_jit_codegen_for_module`, `collect_jit_setup_public`, `ModuleCompiler`, etc.). The runtime fn ptr is read from the per-module `GotTable` slot indexed by `got_slot` — no `platform_fn_ptr` field is read from the entry (it doesn't exist; see §1 post-S66-rollback note).

### 5.3 Error handling — null GOT slot vs graceful fall-through

Per §4.3 invariant, the slot indexed by `entry.got_slot.unwrap()` is non-null on every `PlatformEffect` entry post-`handle_platform`. The read path checks the kind discriminant first, then the slot's load; a null slot silently skips the entry (no registration). This preserves the pre-G8 behaviour (`fn_ptr_by_jit_name` returning `None` skipped too) and does not panic.

The more visible error site is in the **typecheck** path: if the user writes `(import [platform.stdio [print]])` but `print` does not exist in the `platform.stdio` symbol table, resolution fails at typecheck time with the existing "symbol not found" error. This is unchanged by G8.

The *only* failure mode unique to G8 would be an internal consistency bug: a `PlatformEffect` entry exists with `got().load_slot(slot)` returning null. Per §4.3 this cannot happen transiently — step 2 of §4.1 creates the entry with a null slot and step 3 stores the pointer before the scheduler progresses past the platform form. If a future refactor separates the two steps, add a `debug_assert!` inside `load_and_register_platform`'s caller verifying `!got.load_slot(slot).is_null()` before marking platform loading complete.

## 6. Sketch comparison

The sketch has `sketch/src/platform.rs` (DLL loading + path resolution) and stores platform function pointers via `sketch/src/typechecker/primitives.rs:960–980`:

```rust
cm.insert_def(Symbol::from(desc.name.as_str()), scheme, Visibility::Public, Some(meta));
cm.set_jit_name(&desc.name, JitSymbol::from(desc.jit_name.as_str()));
self.platform_scheduling.insert(desc.name.clone(), desc.scheduling_class);
```

And retrieves scheduling class via (`sketch/src/typechecker/primitives.rs:987`):

```rust
pub fn scheduling_of(&self, name: &str) -> SchedulingClass {
    self.platform_scheduling.get(name).copied().unwrap_or_default()
}
```

The sketch's shape: the type info lives on `CompiledModule` (via `cm.insert_def`); the scheduling class lives on a separate `HashMap<Symbol, SchedulingClass>` on the TypeChecker; the function pointer lives in a third place (the JIT symbol registration via `JITBuilder::symbol`). **Three parallel stores** for the three facets of one platform function. The sketch did not consolidate.

The sketch does *not* have a `PlatformRegistry` equivalent — the `fn_ptr` is registered directly on the JITBuilder at load time and never stored anywhere else. The prototype's v4-era rewrite introduced `PlatformRegistry` as a *step toward* consolidation (one store keyed by `FQSymbol` carrying all three facets). G8 completes the consolidation by moving into the symbol table: now all three facets (type info, scheduling class, fn ptr) live on one `ModuleEntry::Def`.

**Decision to follow or diverge**: *partial divergence with informed motivation*. The sketch's three-store shape is the problem G8 solves; the sketch's *solution* (register into JIT directly, never store) is the shape we reject because cross-module GOT-indirect resolution requires the fn pointer to be discoverable by module path + symbol at JIT-finalize time. `PlatformRegistry` was a useful intermediate shape that proved the consolidation worked with a lightweight DashMap keyed by FQSymbol; G8 adopts the FQSymbol → platform-fn mapping but collapses the DashMap into the already-existing `symbol_tables` (Principle 11 — single store). The sketch's `scheduling_of` fallback to `SchedulingClass::default()` on lookup miss is retained as the safe default: `bind_chain_analysis` never crashes on a non-platform symbol, it just classifies it as `Sequential`.

## 7. Coordination with `/platform` skill

`/platform` owns `crates/cranelisp-platform/` (shared ABI crate, compiler-side — **not** a DashMap). The C-ABI contracts (`PlatformFn`, `SchedulingClass`, `call_effect_thunk`, `declare_platform!` macro) stay. `/platform`'s crate is a library of types + utilities, not a registry.

What survives in the integration layer under `/platform` ownership:
- DLL loading (`dlopen`, manifest parsing): unchanged; `crate::platform::load_and_register_platform` keeps doing it.
- DLL lifetime management: `loaded_platforms: Mutex<Vec<LoadedPlatform>>` on `CompilerSession` is unchanged.
- Path resolution (`resolve_platform_path`): unchanged.
- The `PlatformFn` C-ABI descriptor: unchanged.

What goes away:
- `src/platform_registry.rs` — the entire file.
- `CompilerSession.platform_registry` field and all its references.
- `PriorityWorkerRefs.platform_registry` field.
- The `Mutex<PlatformRegistry>` swap-in/swap-out dance in `register_module_with_source` (`src/session_v4.rs:993–1026`) and `reload_module` (`src/session_v4.rs:1088–1128`).

What `/platform` must confirm:
- The DLL-load loop inside `load_and_register_platform` can take a `&DashMap<ModuleFullPath, SymbolTable>` (or equivalent) and write both the symbol-table entry AND the per-module GOT slot (via `symbol_table.got().store_slot(slot, desc.ptr)`) in one pass. No reason this is blocked — the function already writes to the symbol table today; the only new behaviour is also storing one pointer in the entry's GOT slot before the next iteration.
- No DLL currently pre-registers a `PlatformRegistry` object via the `declare_platform!` macro. (Spot-check: `crates/cranelisp-platform/src/lib.rs` shows the macro produces `PlatformFn` descriptors, not registry entries. No coupling.)

(Historical: the inline `FIXME(/platform)` that confirmed these bullets is resolved — both bullets confirmed in Sprint 57 Wave 1 review; the inline FIXME protocol is retired per Sprint 63 M7.)

## 8. Cache interaction — null GOT slot on cache-hit load

`GotTable` slots are not serialised — they hold `AtomicPtr<u8>` runtime addresses in non-serialised memory, allocated fresh on every session start. On cache-hit load (`try_cache_hit_load`), every restored `PlatformEffect` entry deserialises with its `got_slot: Some(slot)` preserved (the slot index is stable), and `kind: PrimitiveKind::PlatformEffect { scheduling_class }` preserved, but the underlying `GotTable`'s slot starts null. For the pointer to become callable, the platform DLL must be reloaded and the slot re-populated.

**Mechanism**: the `SymbolTable.platforms: Vec<PlatformDecl>` field (per `pipeline-v4.md` §9.1 — a serialised record of `(platform "name")` forms) stores the DLL name. On cache-hit load, the scheduler or session iterates each restored module's `platforms` list, reloads the DLL, and walks its manifest to rewrite each `PlatformEffect` entry's GOT slot via `symbol_table.got().store_slot(slot, desc.ptr)`. This is the same loop as cold-start but triggered by cache restore rather than form processing.

Today the `SymbolTable.platforms` field may not yet be persisted — it lands properly in Phase 5 (Step 5a: structural declarations on `SymbolTable`). Until Phase 5, cache restore of platform-using modules is incomplete: the restore succeeds but the GOT slot stays null, which breaks the next `collect_jit_setup` iteration. Phase 4 G8 therefore either:
- **(a)** Gates full platform-cache support behind Phase 5 (accept that cache-hit platform modules require a full re-platform-load from the `PlatformDecl` stored on disk). This matches today's behaviour — the sketch also did not cache platform state because DLL load is `O(1)` anyway; and
- **(b)** Temporarily retains the `(platform "name")` form re-execution path inside the cache-hit codepath for the module (worker sees cache hit → still runs `handle_platform` for each `PlatformDecl` in the manifest → writes the GOT slot).

**/int position**: option (a) — Phase 5 is the right time to close this gap. Phase 4 G8 scope is the `PlatformRegistry` deletion; ambitious cache-restore behaviours expand the wave surface unnecessarily. If the 5 v4_platform failures in the 14-failure baseline are cache-dependent (triage TBD; see §9), option (b) may be required this sprint as a minimal glue.

(Historical: the inline `FIXME(/platform)` here triaged the 5 v4_platform failures; resolved in Sprint 57 Wave 3.)

## 9. Test strategy

Per `src/CLAUDE.md` and the sprint's testing ownership clause, `/int` writes unit tests inside the binary crate during Wave 3 implementation. `/qa` writes integration tests in `tests/`.

### 9.1 Unit tests (owned by `/int`, written in Wave 3)

- `src/worker.rs::tests` — `collect_jit_setup_finds_platform_fn_via_entry`:
  1. Build a synthetic `SymbolTable` with one `PlatformEffect` entry carrying `got_slot: Some(slot)`; pre-populate the table's `GotTable` via `table.got().store_slot(slot, 0x1000 as *const u8)` and set `kind.jit_name: Some("cranelisp_print")`.
  2. Call `collect_jit_setup` (no `platform_registry` parameter in the G8 signature).
  3. Assert `jit_symbols` contains `("cranelisp_print", 0x1000 as *const u8)`.

- `src/worker.rs::tests` — `collect_jit_setup_follows_imports`:
  1. Two modules: `platform.stdio` with the entry, `user` with a `ModuleEntry::Import { source: FQSymbol { "platform.stdio", "print" } }`.
  2. Call `collect_jit_setup` against `user`.
  3. Assert resolution works through the Import chain.

- `src/bind_chain_analysis.rs::tests` — `classify_expr_reads_scheduling_class_from_symbol_table`:
  1. Symbol-table setup with `PlatformEffect { scheduling_class: Commutative }`.
  2. Expression referencing the platform fn.
  3. Assert classification returns `Commutative`.

### 9.2 Integration tests (owned by `/qa`, written in Wave 3 or Wave 5)

- `tests/v4_platform/platform_fn_on_entry.rs` — register a platform module, assert the symbol-table entry carries `got_slot: Some(slot)` AND `symbol_table.got().load_slot(slot)` returns a non-null ptr after form processing.
- `tests/v4_platform/cross_module_platform_resolution.rs` — user module imports a platform fn, call it, assert behaviour matches direct call.
- The 5 v4_platform failure triage: classify each failure against §8 (cache-dependent vs pure-G8). Expected to clear under G8 (perhaps with §8's option (b) glue for cache-interacting cases).

### 9.3 Regression

- 14-failure baseline preserved or improved.
- IO + platform demo (`repl/demos/ring4a.demo` or equivalent) plays cleanly.

## 10. Deletion list — Sprint 57 Wave 3

| # | Item | File:line (approx) |
|---|------|--------------------|
| 1 | `pub struct PlatformRegistry` + impl block | `src/platform_registry.rs` (entire file) |
| 2 | `pub struct PlatformFunction` | `src/platform_registry.rs` (entire file) |
| 3 | `mod platform_registry;` + `pub use` | `src/lib.rs` (find + remove) |
| 4 | `CompilerSession.platform_registry: PlatformRegistry` | `src/session_v4.rs` (field + constructor) |
| 5 | `PriorityWorkerRefs.platform_registry: &'a Mutex<PlatformRegistry>` | `src/worker.rs:2853` |
| 6 | `ModuleCompiler.platform_registry: &'a mut PlatformRegistry` | `src/worker.rs:47, :116` |
| 7 | `platform_registry` parameter on `collect_jit_setup`, `collect_jit_setup_public`, `inline_jit_codegen_for_module`, `inline_jit_codegen_for_names`, `handle_platform`, `codegen_and_execute` caller chain | `src/worker.rs` (6 call sites) + `src/session_v4.rs` (3 call sites) |
| 8 | `platform_registry.register(...)` in `handle_platform` | `src/worker.rs:1481` |
| 9 | `Mutex<PlatformRegistry>` swap-in/out in `register_module_with_source` and `reload_module` | `src/session_v4.rs:993–1026, 1088–1128` |
| 10 | Test helpers `PlatformRegistry::with_test_entries`, `PlatformRegistry::new()` in tests | `src/bind_chain_analysis.rs` tests; replace with synthetic `SymbolTable` construction helper |

Cross-check: `grep -n PlatformRegistry src/` returns zero matches after Wave 3.

## 11. Acceptance (Wave 3 gate criteria, additions to SPRINT.md Wave 3)

1. `PlatformRegistry` struct, field, constructor, all call sites deleted — confirmed by grep.
2. Every platform-fn lookup goes through `symbol_tables[module].got().load_slot(entry.got_slot.unwrap())` for the runtime ptr (post-S66 rollback canonical path; no `platform_fn_ptr` field exists), or `scheduling_class` on the `PrimitiveKind::PlatformEffect` variant per Option B for the metadata.
3. 5 v4_platform failures pass (or triaged per §8 into Phase 5 scope with rationale).
4. IO regression suite passes: `examples/*.cl` using `print`, `read-line`, `time`, etc. unchanged.
5. `bind-chain` auto-scheduling still classifies Commutative and ResourceSerial calls correctly — existing Ring 4 integration tests pass.
6. RC balance in IO trampoline — `/qa`'s integration test from `/arch` condition 6 exercises the trampoline path with a platform effect; `LIVE_ALLOCS` sanity check post-execution.
7. `cargo clippy -p cranelisp --all-targets` clean.
8. No new warnings introduced in `cranelisp-platform` or `cranelisp-runtime`.

## 12. Next skills

After this design doc is approved and `/platform` responds on the FIXMEs in §3, §4.2, §7, §8:

- `/int` — execute Wave 3 per §10 deletion list + §11 acceptance criteria.
- `/platform` — own the `load_and_register_platform` signature change (§4.2) and the potential cache-hit glue (§8 option b).
- `/backend` — confirm `compile_to_module` correctly resolves platform fns through the symbol-table Import chain in its GOT-reference emission (§9.3 of `pipeline-v4.md`).
- `/qa` — write the integration tests in §9.2; verify the 5 v4_platform failures clear.
- `/review` — enforce the `grep -n PlatformRegistry src/` → zero-matches invariant during Wave 3 review.
