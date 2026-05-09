---
number: 0162
target: /arch
filed_by: /arch
filed_at: 2026-05-09
sprint_filed: 66
refers_to: design/arch/interfaces.md §"ModuleEntry::Def" (around lines 990–1043, 1666)
status: open
---

# interfaces.md narrative needs fn_ptr unification follow-up

## Issue

The S66 fn_ptr unification (2026-05-09) revised the `ModuleEntry::Def` shape: the per-entry call-address ptr migrated to a unified `fn_ptr: Option<*const u8>` field, and `Code` variants slimmed to lifecycle owner only (`Code::Jit(Arc<Jit>)` / `Code::Linker(Arc<Linker>)`). The four facades (`types.md`, `backend.md`, `primitives.md`, `platform.md`), the Wave 0 authoring plan, and Decisions 31 + 41 were updated in the same commit.

`interfaces.md` was NOT updated in that commit because the dispatching brief explicitly bounded the edit set to facades + plan + decisions. The narrative companion to `cranelisp-types` therefore now carries language that contradicts the facade target shape:

1. **Lines ~990–1025** — the `code: Option<C>` doc-comment still says "this carries the raw code pointer stored into the GOT slot plus an `Arc<Jit>` shared across every sibling entry produced by the same `compile_to_module` batch". Post-S66 the `Code` variants no longer embed a ptr; the ptr lives on the sibling `fn_ptr` field. The "raw code pointer" claim is wrong; the "shared across every sibling entry produced by the same batch" claim is also obsolete (Decision 41 — per-symbol JIT cardinality means one `Arc<Jit>` per defn in JIT mode).
2. **Lines ~1026–1043** — the `platform_fn_ptr: Option<*const u8>` field is shown verbatim. Post-S66 the field is renamed to `fn_ptr` and unified across all four ptr origins (JIT user fn, linker user fn, primitive, platform DLL).
3. **Line ~1666** — the prose note "the full set of typecheck- and codegen-populated fields on `ModuleEntry::Def` (`ast`, `code`, `platform_fn_ptr`, `got_slot`, `callees`, `trait_origin`)" lists the obsolete field name and would need to mention the new `fn_ptr` plus drop `platform_fn_ptr`.

## Proposed resolution

`/arch` updates `interfaces.md`:

1. Replace the `platform_fn_ptr` field block (~lines 1026–1043) with a unified `fn_ptr` field block. Doc-comment should explain the four origins encoded by `kind: DefKind` (Function/UserFn → JIT/linker; Primitive { Builtin/Inline } → primitive; Primitive { PlatformEffect } → platform DLL). Cross-reference `facades/types.md` §"Symbol table — the single store" + the S66 fn_ptr unification commit.
2. Revise the `code: Option<C>` doc-comment (~lines 990–1025) to say "lifecycle owner only" — `Arc<Jit>` for JIT-built user fns, `Arc<Linker>` for cache-hit user fns, `None` for primitives + platform DLL fns. Drop the "raw code pointer" claim. Drop the "shared across every sibling entry produced by the same batch" claim (Decision 41 — per-symbol JIT cardinality means one Jit per JIT-built defn).
3. Update the prose note at line ~1666 to drop `platform_fn_ptr` and mention `fn_ptr`.

This is a documentation-only sweep; no source change. Estimated effort: ~30 minutes.

## Operational implication / Context

The four facades are the canonical as-designed surface. `interfaces.md` is the narrative companion — its purpose is to make the canonical types crate's *why* legible. The narrative is now drifting; the audit checklist principle (every edit obligates consistency across the canonical set) was honoured for the facades + decisions in the originating commit, but the dispatching brief's bounded edit list left this one canonical document for a follow-up.

The drift is small — the narrative still correctly names `ModuleEntry::Def`, the `code` field is still `Option<C>`, the `Arc<Jit>` lifecycle is still the reclaim primitive. Only the per-entry ptr's location (variant-internal vs sibling field) and the field's rename (`platform_fn_ptr` → `fn_ptr` with broader coverage) differ. Until this FIXME closes, readers who land on `interfaces.md` first see a stale picture; the facades are the durable target.

`/arch` resolves on next invocation that touches `design/arch/`.
