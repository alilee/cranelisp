---
number: 0252
target: /design
filed_by: /dev (backend)
note: Renumbered 0246→0252 by /sprint (S76) — 0246 was used in-session by /design (typecheck)'s check_type_expr surface FIXME, resolved+deleted by /arch's seam-settle. Max active was 0251.
filed_at: 2026-06-03
sprint_filed: 76
refers_to: design/backend/jit-setup-boundary.md §1.2, §1.3 (derivation 3), §1.3 footnote
status: open
---

# `jit-setup-boundary.md` platform-effect derivation describes a retired `DefKind` shape

## Issue

§1.2 and §1.3 (derivation 3) describe the platform-effect jit-name walk in
terms of a `DefKind` shape that no longer exists in `cranelisp-types`:

> §1.2: "it walks every module's `SymbolTable` for `PlatformEffect` jit-names"
> §1.3 derivation 3: "for each `DefKind::Primitive { primitive_kind:
> PlatformEffect, jit_name: Some(n) }` with a populated GOT slot, register
> `(n, got.load_slot(slot))`"

The current `cranelisp-types` shape (`crates/cranelisp-types/src/module.rs`)
is:

- `DefKind::PlatformEffect { scheduling_class }` — a **top-level** `DefKind`
  variant, NOT nested under `DefKind::Primitive { primitive_kind: .. }`.
- There is **no** `jit_name` field. It was retired (S69 Submission 36 — the
  `PrimitiveKind` enum and the `jit_name` sibling field both removed). The
  rustdoc on `DefKind::Primitive` states: "The symbol-table key IS the JIT
  linker name uniformly per `src/CLAUDE.md` §JIT Symbol Names; no separate
  `jit_name` field."

The design doc's derivation-3 text matches the OLD shape that int's
`src/worker.rs::collect_jit_setup` (lines ~2964-2996) still compiles against —
which is consistent with int being intentionally red this wave, but means the
design doc cannot be implemented verbatim.

## Proposed resolution

Update §1.2 / §1.3 derivation 3 (and the §1.3 footnote that says "resolved by
walking each module's defs + import chains") to describe the current shape:

- Match `DefKind::PlatformEffect { .. }` (top-level variant) with
  `got_slot: Some(slot)`.
- The JIT linker name is the **symbol-table key** (the `Symbol`), not a
  retired `jit_name` payload.
- For the `ModuleEntry::Import` edge case, the canonical jit-name is the
  **defining module's** symbol key (`source.symbol`), not the importing
  module's local alias.

The implementation already follows the corrected shape (see
`crates/cranelisp-backend/src/jit.rs::register_platform_effect_symbols`); this
FIXME aligns the design doc to the implemented (and type-correct) derivation.

## Operational implication / Context

The implemented `Jit::new(symbol_tables)` is type-correct and unit-tested
(`jit_new_registers_platform_effect_and_got_symbols`,
`jit_new_follows_import_edge_for_platform_effect`). No code change is owed from
this FIXME — it is a doc-accuracy correction so the next reader of
`jit-setup-boundary.md` is not misled into re-introducing the retired shape.
Independently, int's W-Collapse (S76 W2) must migrate `collect_jit_setup` off
the same retired shape when it switches to calling `Jit::new(symbol_tables)`.
