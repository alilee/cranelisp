---
number: 0907
target: /qa
filed_by: /qa
filed_at: 2026-07-26
sprint_filed: 118
refers_to: design/backend/non-concrete-release-contract.md §4, §5;
  crates/cranelisp-backend/src/drop_glue.rs;
  tests/spec_10_io.rs;
  tests/ctor_as_value.rs;
  tests/examples.rs;
  tests/stdlib_conformance.rs;
  tests/plan/s122-evidence-delta.md
status: open
ruled_at: design/backend/non-concrete-release-contract.md §4 face 4, §5
---

# IO release after the runtime-directed teardown — evidence and rider reconciliation

## Current state (verified 2026-09-24)

- The concrete `IO T` release refusal (`constructor 'Bind' disagrees on
  declared parameter identity`) is ruled and its mechanism delivered:
  `drop_glue.rs` classifies `primitives/IO` as runtime-owned before shape
  derivation and releases through `runtime/free_io_node`; `Pure` carries a
  stamped payload-glue word
  ([contract](../../backend/non-concrete-release-contract.md) §5). An
  admission exclusion for IO stays rejected (contract §4.5).
- The S122 nested-action `sequence-io` abort was attributed separately and its
  reduced public batch passes; it is not this filing's evidence.
- The seven S118 cells — `spec_10_io` (three), `ctor_as_value` (two),
  `every_example_runs_with_documented_exit` (examples 21 and 23) and
  `stdlib_all_public_modules_compile_and_run` (`core.io`, `core`) — are not
  among the six non-environmental REDs of the S122 opening stocktake
  (run `b5d19d16-6bf5-4265-bc02-18fb1f773fde`,
  [candidate inventory](../../../sprints/s122-candidate-inventory.md)). Not
  rerun here.
- Several consumers still describe the pre-delivery refusal as current.

## Remaining obligation

1. **Evidence (`qa`).** Accept the seven cells' passing state as closure
   evidence for the refusal, or rerun them. Add a
   balance cell for a trait instance over IO, such as
   `(impl (Functor IO) (defn fmap [g io] (bind io (fn [x] (Pure (g x))))))`:
   in S118 it compiled, returned correctly and retained about 68 bytes per
   call. The unrun-`Bind` payload residual is FIXME 0934's.
2. **Stale refusal text (route to owners).** Once the cells pass:
   - `test` updates the `// defect:` notation on those cells;
   - `training` removes the known-red headers and part markers in examples 21
     and 23;
   - `test` flips the retained red segment in `repl/demos/archive/ring4s.demo`;
   - `dev` (stdlib) authors the six `core.io` self-tests listed in
     `stdlib/plan-stdlib.md` §6.2;
   - `docs` removes the limitation notes in `user/getting-started.md` and
     `user/guide/concurrency.md`.
3. **Introspection (`spec`/`design` int).** `Bind` and `IO` are named by
   diagnostics yet `/info Bind` and `/info IO` report unknown symbols while
   `Pure` introspects. Decide whether the manually seeded `Bind` must be
   introspectable.

## Closure

The seven cells and the trait-instance balance cell pass, and the listed
owners have removed their refusal-era text or recorded why it stays.
