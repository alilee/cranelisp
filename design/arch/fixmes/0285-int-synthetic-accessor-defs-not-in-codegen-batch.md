---
number: 0285
target: /int
filed_by: /qa
filed_at: 2026-06-07
sprint_filed: 76
refers_to: tests/trace.rs::{trace_nanos_accessor_resolves_in_repl,trace_linked_accessor_consumption_parks_defect} (FAILING), src/bootstrap.rs (Trace accessor Defs with ast: Some), src/worker.rs (derive_codegen_batch), design/arch/fixmes/0276-qa-link-mode-synthetic-accessor-unresolved-and-park.md (/qa resolution status)
status: open
---

# Bootstrap-synthesised accessor Defs never compiled — broken in REPL/JIT too, not just --link

## Issue

0276's triage found the defect is NOT link-specific: the bootstrap-synthesised
Trace accessor Defs (`nanos`, `name`, …, seeded with `ast: Some` by the S76
mount) are absent from the JIT codegen batch as well — `(nanos (trace …))`
panics "can't resolve symbol nanos" in the REPL and PARKS the session in
--link (the park is the 0276 defect-2 robustness item). Match-based TraceCall
extraction works; only the accessor FUNCTIONS are missing. The S76 W2 0249-b
fix covered synthesised CONSTRUCTORS; the accessor Defs are the uncovered
sibling.

Failing tests: tests/trace.rs::trace_nanos_accessor_resolves_in_repl,
trace_linked_accessor_consumption_parks_defect.

## Proposed resolution

1. Extend the codegen-batch derivation to include bootstrap-synthesised
   non-constructor Defs with `ast: Some` (the accessor family) — both JIT and
   link batches; unit test alongside the 0249-b constructor test.
2. The worker-panic→park robustness item (defect 2) stays named in the ledger
   (every unresolved-symbol panic currently converts to a hang) — fix here if
   cheap, else carry explicitly.

## Operational implication / Context

Blocks accessor-based trace consumption in ALL modes. S76 W4 or S77. The
failing tests are the durable record; 0276 carries the triage history.
