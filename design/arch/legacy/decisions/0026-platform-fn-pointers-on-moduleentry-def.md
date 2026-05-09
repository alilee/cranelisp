---
number: 0026
title: Platform function pointers live on `ModuleEntry::Def.platform_fn_ptr` as a `#[serde(skip)]` field; `scheduling_class` is a variant field on `PrimitiveKind::PlatformEffect`
status: operative
---

# 0026 — Platform function pointers live on `ModuleEntry::Def.platform_fn_ptr` as a `#[serde(skip)]` field; `scheduling_class` is a variant field on `PrimitiveKind::PlatformEffect`

Platform DLL function pointers live on the `PrimitiveKind::PlatformEffect` `ModuleEntry::Def` entry directly, via the `#[serde(skip)] platform_fn_ptr: Option<*const u8>` sibling field. The scheduling class lives inside the enum variant: `PrimitiveKind::PlatformEffect { scheduling_class: SchedulingClass }`. `PlatformRegistry` is deleted. JIT-symbol collection, the IO trampoline, and bind-chain scheduling all look up platform fns by following Import chains to the defining `PlatformEffect` entry in the symbol table, reading `scheduling_class` off the destructured variant and `platform_fn_ptr` off the sibling field. The two fields have different serialisation discipline because they have different regeneration stories: `scheduling_class` is static manifest metadata that serialises with the entry; `platform_fn_ptr` is a runtime DLL pointer that is re-resolved on cache-hit load by re-opening the DLL and reading its manifest (the `PlatformDecl` entry stored persistently records which DLL to reload). The asymmetry (one in variant, one sibling) is load-bearing: putting `scheduling_class` in the variant makes ill-formed states unrepresentable (one cannot attach a class to a non-`PlatformEffect` entry), while keeping `platform_fn_ptr` as a serde-skip sibling avoids per-variant serde gymnastics for a field that always deserialises to `None`. This placement was independently selected by `/arch`, `/platform`, and `/int` in Sprint 57 Phase 3a review (three-way convergence recorded in `sprints/SPRINT.md` §Architecture Review Phase 3a step 9). Rejected alternatives: (a) keep `PlatformRegistry` as a "lookup optimisation" (same DashMap-vs-entry divergence Decision 25 rejects); (b) store platform ptrs on a session-level side map indexed by FQSymbol (still a parallel store); (c) place `scheduling_class` as a sibling `Option<SchedulingClass>` on `ModuleEntry::Def` (permits miswrites, and carries dead state on every non-platform entry). Canonical location: `crates/cranelisp-types/src/module.rs` `ModuleEntry::Def` + `DefKind::Primitive.primitive_kind` (after G8 lands); owned by `/int` + `/platform` co-design. Rationale: Principle 11 (single store) + Principle 7 (one platform-fn-ptr location per symbol) + Principle 6 (complexity budget — variant-internal scheduling_class carries the field only where it applies) + Principle 1 (decoupling — the IO trampoline reads from `symbol_tables`, not from a side registry, same as every other cross-module symbol lookup).

## Postscript (Sprint 66 — fn_ptr unification + rollback, 2026-05-09)

The `platform_fn_ptr` sibling field has been **removed** from `ModuleEntry::Def`. The substance of this decision (delete `PlatformRegistry`; platform-fn lookup follows Import chains to the defining `PlatformEffect` entry in the symbol table; `scheduling_class` lives inside the `PrimitiveKind::PlatformEffect` variant) is **unchanged** — only the storage location of the runtime call pointer moved.

Two-step history:

1. **`b09ec76` (S66 Wave 0):** `platform_fn_ptr` removed; replaced by a unified `fn_ptr: Option<*const u8>` covering all four ptr origins (JIT, linker-loaded, primitive, platform DLL).
2. **`1dc57ae` (same day, rollback):** the unified `fn_ptr` also removed once /arch identified it as redundant with the per-module `GotTable` (which JIT-emitted code already reads via `got_base + slot * 8`). Post-rollback the GOT is the single source of truth for callable addresses.

**Post-rollback platform-fn registration.** `handle_platform` allocates a GOT slot (via `SymbolTable::allocate_got_slot`) for each platform-fn entry if one is not yet present, writes the slot id back onto the entry as `got_slot: Some(slot)`, and stores the descriptor's pointer via `symbol_table.got().store_slot(slot, desc.ptr)`. Cross-module lookup is unchanged — follow Import chains to the defining `PlatformEffect` entry, then read the runtime address via `entry_owning_module.got().load_slot(entry.got_slot.unwrap())`.

**Cache-restore.** Unchanged in substance — the persisted `PlatformDecl` records which DLL to reload; on cache-hit load the platform-reload path re-opens the DLL, walks its manifest, and writes each platform-fn descriptor's pointer to the GOT slot of the corresponding `PrimitiveKind::PlatformEffect` entry. The `scheduling_class` deserialises with the entry as before.

**`scheduling_class` placement unchanged.** Still inside the `PrimitiveKind::PlatformEffect` variant. The asymmetry argument (variant-internal makes ill-formed states unrepresentable) holds — `scheduling_class` has no equivalent in the GOT.

See Decision 41's "S66 amendment + rollback" for the canonical post-rollback statement and `crates/cranelisp-types/src/module.rs:430–460` for the `got_slot` doc-comment.
