---
number: 0353
target: /platform
filed_by: /dev
filed_at: 2026-06-14
sprint_filed: 82
refers_to: spec/10-io.md §10.12.4, crates/cranelisp-backend/src/compiler/control_flow.rs (par_codegen_tests), crates/cranelisp-platform/src/lib.rs (resource_serial_token_lands_on_effect_node), design/backend/io-scheduling.md §5.2
status: open
---

# ResourceSerial token-serialization runtime behaviour is un-witnessed (no test-capture fixture)

## Issue

The S82 close of FIXME 0135 (`tests/legacy/lenient.rs`) harvested every
`test_io_schedule_*` GAP that has a portable seam:

- Par-node CLIF emission (commutative pair) → `control_flow.rs`
  `par_codegen_tests::par_bind_emits_par_node_with_branch_count` +
  `par_bind_branch_count_tracks_bindings`.
- Sequential `let` emits NO Par node (negative) → `control_flow.rs`
  `par_codegen_tests::sequential_let_emits_no_par_node` (S82, this change-set).
- Data-dependency analysis (dependent binding not sparkable) →
  `control_flow.rs` `sparkability_tests::dependent_binding_is_not_sparkable`
  + `mixed_independent_and_dependent_returns_only_independent`.
- Scheduling-class C-ABI manifest round-trip (Sequential / Commutative /
  ResourceSerial / unknown→Sequential) → `cranelisp-platform/src/lib.rs`
  `manifest_lifts_*_scheduling_class`.
- ResourceSerial token PLACEMENT on the Effect node →
  `cranelisp-platform/src/lib.rs` `resource_serial_token_lands_on_effect_node`.

**Two of the legacy GAPs remain un-witnessed** — the legacy tests were
themselves TODO stubs with no assertion
(`test_io_schedule_resource_serial_same_token_sequential`,
`test_io_schedule_resource_serial_diff_token_parallel`). Both assert the
trampoline's *runtime serialization decision* per spec §10.12.4:

1. Two `ResourceSerial` calls with the **same** non-zero token are
   serialized even when data-independent (observed via timing: two 50ms
   calls take ~100ms).
2. Two `ResourceSerial` calls with **different** tokens run concurrently
   (~50ms, not ~100ms).

This behaviour lives in the intrinsics IO trampoline
(`dispatch_par_branches`, design/backend/io-scheduling.md §5.2, Decision
0043). It is NOT unit-testable (it is a runtime dispatch decision over a
live thread pool) and it is NOT e2e-witnessable today: the `cranelisp-test-capture`
platform DLL has no `ResourceSerial` functions with controllable timing +
tokens. The legacy stubs acknowledged exactly this ("ResourceSerial test
functions not yet available in test-capture platform").

## Proposed resolution

1. **`/platform`** — add ResourceSerial functions to `cranelisp-test-capture`
   (e.g. `test-resource-sleep-ms` taking a token + duration), declared with
   `SchedulingClass::ResourceSerial` and a caller-supplied resource token.
2. **`/qa`** — once the fixture exists, author a timing e2e (in `tests/spec_10_io.rs`
   or a platform-scheduling e2e file) asserting same-token≈2× and
   diff-token≈1× wall-clock, `// spec: spec/10-io.md §10.12.4`. This is the
   end-to-end witness the two legacy stubs always owed.

A failing-not-ignored red guard was deliberately NOT committed at S82 close:
without the ResourceSerial fixture the test can only skip (matching the legacy
stub behaviour), and a skip is not a defect guard. The durable record is this
FIXME + the `tests/plan/ledger.md` S82 entry. When the fixture lands, the e2e
flips from "cannot be written" to green.

## Operational implication / Context

This is the runtime-dispatch remainder of 0135 — closed at S82 because the
portable kernel was fully harvested and `tests/legacy/lenient.rs` was deleted.
No source defect is implied: the trampoline serialization is implemented
(io-scheduling.md §5.2); what is missing is the *test fixture* to witness it
end-to-end. Until the fixture exists the only evidence the behaviour is correct
is the design doc + the token-placement unit (`resource_serial_token_lands_on_effect_node`).
