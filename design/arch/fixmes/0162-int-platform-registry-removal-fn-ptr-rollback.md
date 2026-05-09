---
number: 0162
target: /design (int)
filed_by: /arch
filed_at: 2026-05-09
sprint_filed: 66
refers_to: design/int/platform-registry-removal.md (multiple sites — §2 OwnedPlatformFnDescriptor, §3 the field-access patterns, §4.1–4.3 the load/write protocol, §5 the read sites, §8 cache interaction, §9 test fixtures)
status: open
---

# Update `platform-registry-removal.md` for the S66 fn_ptr unification rollback

## Issue

`design/int/platform-registry-removal.md` describes G8's migration of platform fn pointers from a `PlatformRegistry` DashMap into a `#[serde(skip)] platform_fn_ptr: Option<*const u8>` field on `ModuleEntry::Def`. The doc references that field at multiple sites (~25 mentions) — it pre-dates the S66 fn_ptr unification (commit `b09ec76`, which removed `platform_fn_ptr` and added a unified `fn_ptr` field) and the same-day rollback (commit `1dc57ae`, which removed the unified `fn_ptr` field after identifying it as redundant with the per-module `GotTable`).

The doc's substance — **delete `PlatformRegistry`; platform-fn lookup follows Import chains to the defining `PlatformEffect` entry in the symbol table** — remains correct and load-bearing. Only the storage location of the runtime call pointer has moved through the two-step S66 evolution.

## Proposed resolution

Update the doc to reflect the post-rollback canonical statement: **GOT is the single source of truth for callable addresses.** The platform-fn pointer for a `PrimitiveKind::PlatformEffect` entry lives in the per-module `GotTable`, indexed by `ModuleEntry::Def.got_slot`. Read via `entry_owning_module.got().load_slot(entry.got_slot.unwrap())`; written via `symbol_table.got().store_slot(slot, desc.ptr)`.

Specific call-out edits:

1. **§2 `OwnedPlatformFnDescriptor`** (line ~31, the example shape). The descriptor's `fn_ptr: *const u8` field is unchanged — that's the descriptor's own field, internal to the platform crate. No edit there.

2. **§3 field-access pattern table** (line ~80, `fn_ptr_by_jit_name(&JitSymbol)` row). Update from "DELETED — `collect_jit_setup` reads `platform_fn_ptr` directly off the entry it already visits" to: "DELETED — `collect_jit_setup` reads the entry's `got_slot`, then `entry_owning_module.got().load_slot(slot)` for the runtime address."

3. **§4 protocol description** (lines ~95, ~130, ~151, ~158–159, ~167, ~173, ~177, ~179) — the `platform_fn_ptr` field/write/read pattern. Replace each occurrence:
   - "`platform_fn_ptr: None`" at entry construction → "`got_slot: Some(slot)` allocated via `SymbolTable::allocate_got_slot()`"
   - "`*platform_fn_ptr = Some(desc.ptr)`" / "writes `platform_fn_ptr`" → "`symbol_table.got().store_slot(slot, desc.ptr)`"
   - "reads `platform_fn_ptr.unwrap()`" → "reads `entry_owning_module.got().load_slot(entry.got_slot.unwrap())`; null-check the result before dispatch"

4. **§4.3 invariant** ("every `ModuleEntry::Def { kind: Primitive { primitive_kind: PlatformEffect { .. }, .. }, .. }` has `platform_fn_ptr: Some(_)`") — restate as: "every such entry has `got_slot: Some(slot)`, and `entry_owning_module.got().load_slot(slot)` returns a non-null ptr post-`handle_platform`. The transient between slot allocation (§4.1 step 2) and pointer write (§4.1 step 3) is guarded by the same lock that gates the platform-form processing."

5. **§5 read sites** — `collect_jit_setup` migration: "reads `platform_fn_ptr` directly off the entry" → "reads `got_slot` off the entry, then `symbol_table.got().load_slot(slot)`". Update §5.3 error-handling discussion the same way.

6. **§8 cache interaction** — "`platform_fn_ptr = None` on cache-hit load" → "GOT slot is null on cache-hit load (re-allocated and re-populated by the platform-reload pass; the persisted `PlatformDecl` records which DLL to reload)".

7. **§9 test fixtures** — assertion text "carries `platform_fn_ptr: Some(_)`" → "carries `got_slot: Some(slot)` AND `symbol_table.got().load_slot(slot)` returns a non-null ptr".

8. **Inline `<!-- FIXME(/platform): … platform_fn_ptr -->` comments** — these were old-style inline FIXMEs; the doc edit can drop them once the migration is documented (or leave them as resolved-by-S66-rollback historical notes, citing the `1dc57ae` commit).

## Operational implication / Context

This is a doc-coherence sweep — the source has already migrated through both S66 phases (commits `b09ec76` and `1dc57ae`); this doc is the only remaining design artefact still describing the pre-S66 / pre-rollback shape. /arch's canonical post-rollback statement is in:

- `design/arch/decisions/0035-code-enum-integration-layer.md` §"Amendment (Sprint 66 — rollback, 2026-05-09)"
- `design/arch/decisions/0041-compile-to-module-per-symbol-jit-direct-writes.md` §"S66 amendment + rollback"
- `design/arch/legacy/decisions/0026-platform-fn-pointers-on-moduleentry-def.md` §"Postscript (Sprint 66 — fn_ptr unification + rollback)"
- `design/arch/facades/types.md` §"Symbol table — the single store" (`got_slot` doc on `ModuleEntry::Def`)
- `crates/cranelisp-types/src/module.rs:430–460` (`got_slot` doc-comment)
- `crates/cranelisp-types/src/got.rs` (`GotTable` API)

Source-of-truth check before editing: `crates/cranelisp-types/src/module.rs` `ModuleEntry::Def` (no `fn_ptr` field, no `platform_fn_ptr` field — just `got_slot: Option<usize>`); `src/worker.rs` `handle_platform` and `collect_jit_setup` (the GOT-slot read/write patterns are already in source per the rollback commit's worker.rs changes).
