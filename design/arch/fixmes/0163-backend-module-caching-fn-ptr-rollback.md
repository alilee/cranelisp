---
number: 0163
target: /design (backend)
filed_by: /arch
filed_at: 2026-05-09
sprint_filed: 66
refers_to: design/backend/module-caching.md §14.1, §14.3, §"Persisted shape" table row, §1080 (`platform_fn_ptr` re-derive note), §1184 (cache-hit reload write site), §1247 (`#[serde(skip)]` summary), §1310 (Runtime fields summary)
status: open
---

# Update `module-caching.md` for the S66 fn_ptr unification rollback

## Issue

`design/backend/module-caching.md` describes the cache shape on the assumption that `ModuleEntry::Def` carries (a) a `code: Option<C>` lifecycle owner, both `#[serde(skip)]`, and (b) a `platform_fn_ptr: Option<*const u8>` `#[serde(skip)]` sibling. Through Sprint 66 the source went through two evolutions: commit `b09ec76` collapsed `platform_fn_ptr` into a unified `fn_ptr: Option<*const u8>` covering all four ptr origins; the same-day rollback commit `1dc57ae` removed the unified `fn_ptr` field after identifying it as redundant with the per-module `GotTable` already maintained by `SymbolTable.got` (a serde-skip Arc<GotTable>).

## Proposed resolution

Update the doc to reflect the post-rollback canonical statement: **GOT is the single source of truth for callable addresses.** The runtime call pointer for a `ModuleEntry::Def` lives in the per-module `GotTable`, indexed by `got_slot`. The `GotTable` itself is `#[serde(skip)]` (it carries `AtomicPtr<u8>` slots; not serialisable; re-populated on cache-hit load by codegen / linker / platform reload).

Specific call-out edits:

1. **§"Persisted shape" table row** (around line 78). Replace "`code` (per-function) and `platform_fn_ptr` are `#[serde(skip)]` and re-derived on cache-hit load" with: "`code` (per-function) is `#[serde(skip)]`; the per-module `got` field (`Arc<GotTable>`) is `#[serde(skip)]`; both are re-populated on cache-hit load. There is no longer a per-entry pointer field — the GOT slot index (`got_slot: Option<usize>`) IS the entry's address handle, persisted with the entry, and the GOT itself is recreated and re-populated on load."

2. **§"`code` / `platform_fn_ptr` placement" row** (around line 80). Rename the row "`code` / GOT placement" or similar. Replace the body: drop "`platform_fn_ptr: Option<*const u8>` (per-platform-effect) live directly on `ModuleEntry::Def`, both `#[serde(skip)]`"; replace with: "`code: Option<C>` (per-function) lives directly on `ModuleEntry::Def` and is `#[serde(skip)]`. The runtime call pointer for any callable entry lives in the per-module `GotTable` (`SymbolTable.got: Arc<GotTable>`, `#[serde(skip)]`), indexed by `ModuleEntry::Def.got_slot: Option<usize>` (which IS persisted). Cache-hit re-derive: deserialise the symbol table; the priority worker re-runs codegen against the deserialised `ast` bodies (writing `code` and the GOT slot for user fns); the platform-reload pass re-opens each persisted `PlatformDecl`'s DLL and writes each platform-fn pointer to its entry's GOT slot." Cite Decisions 25/26/31/35 (S66-amended) + the post-rollback statement in Decisions 35 and 41.

3. **§14.1 step description** (around line ~1184) — "cl_name → fn_ptr, and write into `entry.platform_fn_ptr`. If the DLL …" → update to "cl_name → fn_ptr, and write to `symbol_table.got().store_slot(entry.got_slot.unwrap(), fn_ptr)`. The `got_slot` was allocated when the entry was first created (or restored by the typecheck table-load pass); on cache-hit reload the GOT itself is freshly allocated, so all slots start null and the platform-reload pass re-populates each platform-fn slot."

4. **`#[serde(skip)]` summary** (around line 1247) — "`platform_fn_ptr` / `got` / `linker` field" — drop the `platform_fn_ptr` reference (no such field exists post-rollback). Keep `code`, `got`, `linker`. Add a note that `got` re-population on cache-hit load is the responsibility of (a) the priority worker for user-fn entries via codegen, (b) the platform-reload pass for `PrimitiveKind::PlatformEffect` entries via `handle_platform` re-execution, (c) `cranelisp-primitives::PRIMITIVES_TABLE` static-init for primitive entries (which is process-static, not session-cached, so cache restore doesn't touch primitive slots).

5. **Runtime fields summary** (around line 1310) — "Runtime fields (`code`, `platform_fn_ptr`, `got`, `linker`) all `#[serde(skip)]`" — drop `platform_fn_ptr`. Restate: "Runtime fields (`code`, `got`, `linker`) all `#[serde(skip)]` — cache-restore re-derives `code` by loading the cached `.o` via `Linker::load_object`, looking up function symbols by their bare names per Decision 36, and constructing `Code::Linker(Arc<Linker>)`; for each defined symbol the linker's resolved address is written to the entry's GOT slot via `symbol_table.got().store_slot(slot, ptr)`. `got` is recreated fresh on `SymbolTable::default()`-style construction at deserialise time (or via a custom Deserialize impl that calls `GotTable::new()` for the field's `#[serde(skip)]` default). The `Arc<Jit>` lives directly on `code` for fresh-build entries per Decision 31 Scenario 2; cache-hit entries hold `Arc<Linker>` instead. Both variants share the same GOT-slot read pattern via `symbol_table.got().load_slot(entry.got_slot.unwrap())`."

## Operational implication / Context

`SymbolTable.got` is a `#[serde(skip)]` field. The GOT itself (the array of `AtomicPtr<u8>`) is NOT in the cache `.meta.json`. The `got_slot: Option<usize>` per-entry index IS in the manifest (it's a plain `usize`, no skip).

On cache-hit load:
1. Deserialise `.meta.json` → `SymbolTable<(), ()>` with empty/default `got` (per `default_got_arc` or equivalent).
2. The session's restore loop walks the table; for each entry whose kind requires a runtime ptr, repopulates the slot.
3. User-fn entries: the linker (from `load_object`) provides the resolved address; written to `entry.got_slot`'s GOT slot.
4. Primitive entries: handled by the synthetic `primitives` module's static `PRIMITIVES_TABLE`, which is process-static — its GOT is populated once at static-init.
5. Platform-effect entries: the persisted `PlatformDecl` for the owning module records which DLL to reload. The platform-reload pass walks each restored module's `platforms`, re-opens each DLL, walks its manifest, and writes each platform-fn descriptor's pointer to its corresponding entry's GOT slot.

Source-of-truth check before editing:
- `crates/cranelisp-types/src/module.rs:430–460` (`got_slot` doc-comment, no fn_ptr/platform_fn_ptr fields)
- `crates/cranelisp-types/src/got.rs` (`GotTable` API, including the implicit Acquire/Release ordering on slot reads/writes)
- `src/worker.rs` `handle_platform` and `collect_jit_setup` (post-`1dc57ae` GOT-slot patterns)
- `crates/cranelisp-backend/src/cache/serialize.rs` (the `fn_ptr` substring assertion is now structural — no `fn_ptr` substring should appear in the serialised JSON)

This doc-update is purely descriptive — no source change implied. The cache shape itself has already migrated via the two S66 commits. /design (backend) owns this doc; /arch's canonical post-rollback statement lives in the Decisions register and in `design/arch/facades/types.md` §"Symbol table — the single store" `got_slot` doc.
