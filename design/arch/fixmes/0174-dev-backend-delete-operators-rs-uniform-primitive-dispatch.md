---
number: 0174
target: /dev (backend)
filed_by: /arch
filed_at: 2026-05-13
sprint_filed: 66
refers_to: design/arch/facades/backend.md §"Non-goals / forbidden patterns" (new section); design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md; design/arch/principles/17-module-locality-in-typecheck.md; design/typecheck/wave-3a-check-form.md §8 (the 4 `stdlib_trait_impls` failures rooted in the absent primitives entries); FIXME 0150 (runtime split); crates/cranelisp-backend/src/operators.rs (531 lines — the entire body of the forbidden pattern); facades/primitives.md (the destination for primitive registration)
status: open
---

# Delete `crates/cranelisp-backend/src/operators.rs` — uniform primitive dispatch via `ModuleEntry::Def` lookup

## Issue

`crates/cranelisp-backend/src/operators.rs::emit_builtin_op` is a 531-line `match name { "add-i64" => …, "not" => …, … }` dispatch over the 19 Ring 0 primitives. It is the forbidden operator-special-casing pattern documented in `facades/backend.md` §"Non-goals / forbidden patterns" (per user-arbitrated 2026-05-13 in the `/arch` Wave 3a round). The file embodies the pre-Decision-43 shape: backend has trait/operator knowledge, dispatching by hard-coded name; primitives have no `ModuleEntry::Def` in the `primitives` synthetic module; the mappable-path (`(let [f =] (f 1 2))`) and bare-primitive-as-value paths fail because there is no GOT slot to capture.

Per Decision 43 + Principle 17 + the user-arbitrated facade direction:

- Every primitive — `not`, `+`, `=`, the 18 arithmetic and comparison operators in `ring0_primitives()`, any future primitive — MUST be a `ModuleEntry::Def { kind: DefKind::Primitive { primitive_kind: Builtin }, got_slot: Some(_), code: None, … }` in the synthetic `primitives` module.
- Backend dispatch for a primitive call is **byte-identical** to dispatch for a user function: look up the resolved FQ in the symbol table, read the GOT slot, emit a GOT-indirect call. The standard codegen path.
- Inline substitution (the legitimate optimisation) is keyed on `Symbol` only, applied to the same call shape, never a parallel dispatch path. Per `facades/backend.md` §"Consumed surface" — `cranelisp-primitives` provides the substitution table; backend matches by name in `primitives_inline.rs` (D43 rename of operators.rs's substitution role) and emits inline Cranelift IR for matched names, falling through to the GOT-indirect call for the rest.

The current `operators.rs` does both jobs (dispatch + substitution) in a way that is incompatible with the post-D43 split. The deletion follows once D43's `cranelisp-primitives` crate exists and seeds `primitives/` with `ModuleEntry::Def` entries for every primitive.

## Proposed resolution

Wave 4 / D43 close-out work:

1. **Land `cranelisp-primitives` per Decision 43 + FIXME 0150.** Seed the synthetic `primitives` `SymbolTable` with `ModuleEntry::Def` entries for every Ring 0 primitive (`not`, `add-i64`, `sub-i64`, …, `eq-f64`). Each entry has `got_slot: Some(_)` (allocated at static init or session init), `code: None` (the fn ptr is published into the GOT by static init, indexed by `got_slot`).
2. **Create `crates/cranelisp-backend/src/primitives_inline.rs`** (per Decision 43 + facade §"Consumed surface"). It carries ONLY the name-keyed inline-substitution table — `match name { "add-i64" => Some(inline emit fn), … }`. No dispatch role; no fallback path; if a name is not in the table, the substitution is a no-op and backend's standard GOT-indirect emission applies.
3. **Refactor backend codegen call sites** that currently invoke `emit_builtin_op` to use the standard codegen path: resolve callee FQ → look up `ModuleEntry::Def` → check `primitives_inline.rs` for inline substitution → if no substitution, emit GOT-indirect call.
4. **Delete `crates/cranelisp-backend/src/operators.rs`** and remove the `mod operators;` line from `lib.rs`.
5. **Run `cargo nextest run -p cranelisp-backend`** + the full workspace gate.
6. **Verify the 4 `stdlib_trait_impls` failures (per `design/typecheck/wave-3a-check-form.md` §8) resolve** — specifically `stdlib_not_*` (the bare `(let [f not] (f true))` mappable path that fails today because `not` has no symbol-table entry).

## Operational implication / Context

This FIXME is the explicit tracking item for the user-arbitrated direction that `operators.rs` is forbidden and to be deleted. It is bound to Wave 4 / D43 close-out because the prerequisite (`cranelisp-primitives` crate exists and seeds the primitive entries) is itself a Wave 4 deliverable per Decision 43.

The facade text alone (added in this `/arch` cycle) is the Wave 3a deliverable; the source-level deletion + refactor is Wave 4. The two-step sequencing keeps the Wave 3a-β cluster-atomic work focused on typecheck cluster-atomic shape, with the backend operator cleanup as a separate, downstream concern.

`/sprint` may co-schedule this FIXME with FIXME 0150 if both can be delivered together; they share the `cranelisp-primitives` substrate.

If `/dev (backend)` discovers during the refactor that some Ring 0 primitive cannot be expressed as a GOT-callable (e.g., a polymorphic intrinsic whose Cranelift emission depends on caller-site operand types in a way that the GOT-call shape doesn't carry), file a counter-FIXME `target: /arch` — the facade position is uniform GOT dispatch; an exception requires arbitration.
