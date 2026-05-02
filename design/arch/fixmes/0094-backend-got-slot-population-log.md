---
number: 0094
target: /arch
filed_by: /design
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/arch/facades/backend.md §"Public surface", design/backend/backend.md §4.3
status: open
---

# Observability gap — backend has no first-class log of GOT-slot population

## Issue

The integration layer populates GOT slots after each batch's `compile_to_module` returns. There is no first-class log entry per slot population — `Introspection.code_size` records per-defn size but does not record GOT slot index, address, or `Arc<Jit>` identity.

Future incident response on a GOT-slot bug (a Decision 31 reclaim regression, a cross-module call hitting a stale slot, a pre-S58-style silent-NULL category that returns) would benefit from a structured log:

```
module M slot N := ptr P (jit=Arc<Jit>@addr Q)
```

Today the only signal that a slot was populated is `code_size > 0` plus the absence of a runtime crash. The pre-Sprint-58 `worker.rs:2810-2823` pattern — silently treating `None` as "skip this slot" — is the historical category Decision 37 closes. The defensive error fires at the call site, but there is no positive log of successful population to compare against when a downstream call fails.

## Proposed resolution

`/arch` decides whether this becomes:

- An `Introspection` extension — a new optional `got_population: Vec<GotEvent>` field per module (where `GotEvent { slot: usize, ptr: *const u8, jit_addr: usize }`), populated when introspection is enabled, OR
- A separate trace flag — `CRANELISP_GOT_TRACE=1` writing to a side log (stderr like `CRANELISP_CODEGEN_DUMP`, or a structured event stream).

If `/arch` greenlights the `Introspection` extension, `cranelisp-types` gains a small DTO; backend's `compile_to_module` populates it (the data is already in hand at the per-symbol write_code site); `int`'s GOT-population loop adds the events.

If `/arch` greenlights the separate trace flag, backend has no new surface — the writer is `int`'s, fed by data backend already returns via `LinkerArtefact.ptrs` and per-symbol `Code::Jit { jit, ptr }`.

Either way, `design/backend/backend.md` §4.3 gains an elaboration once the choice is made.

## Operational implication / Context

This is a pure observability addition; no runtime behaviour changes. The cost of the `Introspection`-extension shape is one extra Vec push per defined symbol when introspection is enabled (zero cost when disabled, per Decision 38's `Option`-discriminated mode). The cost of the trace-flag shape is similarly zero when the env var is unset.

The audit `audits/backend-20260423.md` does not specifically flag this gap — it is surfaced by this design refresh as a maintainability-of-future-incidents question. No defect today; future-incident-response insurance.
