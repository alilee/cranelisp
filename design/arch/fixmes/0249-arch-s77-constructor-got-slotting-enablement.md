---
number: 0249
target: /arch
filed_by: /arch
filed_at: 2026-06-02
sprint_filed: 75
refers_to: design/backend/compile-to-module.md §2.6, §2.6.5; design/arch/bounded-contexts.md §3 (backend — "Minimal JIT-setup boundary" / invariant 3); crates/cranelisp-backend/src/{lib,code,compiler/apply}.rs rustdoc (post-W5b canonical surface); crates/cranelisp-typecheck/src/checker.rs (register_constructors); src/ (derive_codegen_batch); design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md (the primitives precedent this mirrors)
status: open
---

# S77 enablement — got-slot constructor `Def`s so backend's constructor-as-value (Path 2) is callable

## Issue

Backend's retired-into-rustdoc design (S75 W5b — `facades/backend.md` → BC §3 + `crates/cranelisp-backend/src/{lib,code,compiler/apply}.rs` source rustdoc) now **assumes constructor `Def`s are got-slotted callable**, exactly as it assumes primitives' GOT entries exist (Decision 0048). Two backend commitments depend on this assumption:

1. **Constructor-as-value (Path 2).** `(map Some list)` passes the constructor `Def`'s `got_slot` address through the same fn-as-value / GOT-resolving path that operator/primitive-as-value already uses (`compile_fn_as_value` over the got-slotted ctor `Def`). The bespoke as-value closure (`compile_data_constructor_as_value` + `compile_ctor_wrapper_body`) was **DELETED** in S75 W4 on the strength of this assumption (per `design/backend/compile-to-module.md` §2.6 W4 correction — backend designs for the final state, mirroring primitives; int not-yet-producing the GOT entries is int's red state, not a backend concern).

2. **The S77 `Jit::new(symbol_tables)` target** (BC §3 "Minimal JIT-setup boundary") + the `INTRINSICS_TABLE` read derive the entire JIT symbol set from `symbol_tables`. For the GOT data symbols to address every callable — including constructors reached first-class — the constructor `Def` entries must carry a `got_slot` like any other callable, so that `symbol_tables[M].got()` mounts them.

Today, constructor `Def` synthesis (typecheck's `register_constructors`) assigns **no `got_slot`**, and int's compile-batch derivation does not enumerate the `TypeDef`-synthesised ctor `Def`s into the compile batch. So Path 2 is structurally un-callable: backend emits a GOT-indirect reference to a slot that was never assigned or populated.

## Proposed resolution (S77 — mirrors Decision 0048)

Two co-ordinated changes, the constructor analogue of the primitives got-slotting that Decision 0048 already landed:

(a) **typecheck got-slots `DefKind::Constructor` entries.** `register_constructors` (the synthesiser that turns each `TypeDef` constructor into a `ModuleEntry::Def { kind: DefKind::Constructor { .. } }`) assigns a `got_slot: Some(N)` from the module's GOT layout, identically to a user `Def` — so the constructor is addressable as a value. (Currently `register_constructors` produces ctor `Def`s with no `got_slot`.)

(b) **int `derive_codegen_batch` enumerates the synthesised ctor `Def`s into the compile batch.** The `TypeDef`-synthesised constructor `Def`s must appear in the set of names handed to `compile_to_module` (or the per-symbol JIT workers) so their bodies (`Expr::ConstrADT`) are lowered via `compile_constr_adt` and their GOT slots are populated with the resulting fn pointer — same as any user-defined function.

Both changes are the **constructor mirror of the primitives Decision 0048 got-slotting** — primitives proved the pattern (a synthetic module's entries carrying GOT slots + a populated `GotTable`, dispatched GOT-indirect like any module). Constructors are ordinary `ModuleEntry::Def` entries in their defining user module; got-slotting them makes them first-class callable through the uniform path with no new mechanism.

## Operational implication / Context

- **This is the S77 dependency that backend's retired-into-rustdoc design now assumes.** It is named here (rather than left implicit in source rustdoc) so the S77 typecheck + int waves have an explicit, tracked enablement item, and so a future reader of BC §3's "backend assumes ctor GOT entries exist" finds the where-it-lands.
- **Cross-skill cascade:** (a) is `/dev (typecheck)`; (b) is `/dev (int)`. `/arch` resolves this FIXME by confirming the enablement is sequenced (or by amending BC §3 / the per-crate design seams if the resolution shape changes), then files the per-crate work or hands to `/sprint` for S77 wave placement.
- **Until S77 lands this**, constructor-as-value (`(map Some list)`) is non-functional at runtime — the same red-state carry as int's parallel-pipeline collapse. Direct construction (`(Some 42)` via the Apply path → `compile_constr_adt`) and pattern matching (`Pattern::Constructor` reading `DefKind::Constructor.tag`) are unaffected; only the first-class-value path depends on this FIXME.
- **Grounding:** `design/backend/compile-to-module.md` §2.6.5 is the backend-owned home for the int/typecheck enablement seam (the "GOT-entry producer = typecheck (got-slot) + int (batch) — backend ASSUMES it" row in the §2.6 primitives/constructor symmetry table).
