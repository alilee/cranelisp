---
number: 0161
target: /arch
filed_by: /arch
filed_at: 2026-05-09
sprint_filed: 66
refers_to: design/arch/facades/primitives.md §"Public surface" (PRIMITIVES_TABLE static), design/arch/facades/backend.md §"GOT-population observation", design/arch/decisions/0031-one-jitmodule-per-compile-batch.md, design/arch/fixmes/0159-primitives-seed-time-fn-ptr-resolution.md (resolved S66 Wave B)
status: open
---

# Post-S66 — evaluate static GOT for primitives

## Issue

FIXME 0159 (resolved S66 Wave B) makes the symbol-table side of primitives a static (`pub static PRIMITIVES_TABLE: LazyLock<SymbolTable>` in `cranelisp-primitives`). Both `int`'s session init and backend's `register_intrinsics` read from the same static — single source of truth at the SymbolTable layer.

The **GOT slot** for each primitive, however, stays at backend's existing per-batch `register_intrinsics` cardinality per Decision 31 (one `JITModule` per compile batch). The fn ptrs are re-registered for every batch's `JITModule`. This is correct for fresh-build code where `Arc<Jit>` lifecycle drives reclaim; for primitives — whose pointers are address-stable for the process lifetime, identical across all batches, defined in static memory — it is potentially redundant work.

## Proposed resolution

After S66 lands, evaluate whether the GOT slot for primitives should also become a static rather than per-batch JITModule registration. Two layers to consider:

1. **The fn ptr value.** Already address-stable in `PRIMITIVES_TABLE` per FIXME 0159 — no work here.
2. **The GOT slot's storage.** Currently allocated via `SymbolTable.next_got_slot.fetch_add(…)` like any other entry, written by `register_intrinsics` per batch. Could become a process-lifetime static slot allocated at `LazyLock` init time and shared across all sessions.

Trade-offs:
- **Pro**: eliminates per-batch redundant write; smaller `register_intrinsics` body; aligns the GOT side with the SymbolTable side (static-everywhere for primitives).
- **Con**: introduces a category of "static GOT slot" that sits outside the per-module GOT table convention (`__cranelisp_got_{module}`); may complicate the two-GOT model in Decision 23 if primitives' slot resolution diverges from other modules'; may interact with REPL redefinition discipline (primitives can't be redefined — that's correct; static is fine — but the codepath in backend's symbol_lookup_fn would gain a primitives special-case).

## Operational implication / Context

Filed during /arch Wave B (Sprint 66 Phase 3 FIXME resolutions, 2026-05-09) per the FIXME 0159 resolution note: "**GOT side**: stays at backend's existing `register_intrinsics` for S66; follow-up FIXME (filed during /arch Wave B) for post-S66 evaluation of static-GOT refinement."

Not blocking S66; not load-bearing for any S66 acceptance criterion. Open question for S67+ when the `PRIMITIVES_TABLE` static has settled in source and the primitives slice has executed Phase α/β/γ. The right time to evaluate is after observing one or more sprints' worth of `register_intrinsics` invocations against the static — does the per-batch registration cost matter at the observed cadence? Does the two-GOT model complicate enough that the saving isn't worth the special-case?

If evaluation determines static-GOT is the right move, /arch authors a follow-up Decision (numbered, in `design/arch/decisions/`) reframing Decision 23's two-GOT model to admit a third "process-lifetime static GOT" category for primitives. That Decision would then drive a follow-up implementation slice for the relevant crates (backend, primitives, int).

If evaluation determines the per-batch registration is fine as-is, this FIXME closes with a one-line note in the closing commit message.
