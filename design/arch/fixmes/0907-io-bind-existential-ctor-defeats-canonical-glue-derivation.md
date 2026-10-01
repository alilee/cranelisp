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

## S122 disposition (user-approved 2026-09-30)

Under the [approved S122 disposition](../../../tests/plan/s122-evidence-delta.md#final-disposition-proposal-2026-09-30):

- **S122 work (K2), evidence only.** `test` measures one marginal pair for the balance cell (`Functor IO` instance). A balanced pair retires the balance obligation. A confirmed ordinary leak becomes a committed RED carried to S123 under K7. A double discharge, use-after-free or corruption returns to the user with its attribution for a fix decision.
- **Balance obligation retired (qa, 2026-09-30).**
  `spec_10_io::functor_io_instance_calls_balance_against_inline_bind` passes.
  - Three `fmap` calls through the `Functor IO` instance are measured against
    three inline `bind`s.
  - Control 10/10, subject 13/13: a marginal of +3/+3 and a residual of 0.
  - Both exits are 42. `CRANELISP_RC_DEC_CHECK` is armed, and the harness
    capability fence passed 3/3.
  - Source `f0d1006f…`; log `.local/s122-final-test/k2-pairs.log`.
  - The S118 retention of about 68 bytes per call no longer reproduces.
- **The refusal face is closed.** The seven S118 cells pass in the last full run; QA accepts that as closure evidence for the refusal.
- **Later phases.** The refusal-era text (obligation 2) routes in Phase 6a/6b; obligation 3, whether `/info Bind` must introspect, goes to `spec` on `repl/` in Phase 6a.
- **Obligation 2, docs leg: satisfied (qa, 2026-09-30).**
  - `user/getting-started.md` and `user/guide/concurrency.md` carry no IO
    release or `Bind` refusal or limitation text at `dc78ddbe`, at
    `88bbbd12`, or in the working tree.
  - The concurrency guide's "Honest scope" limitations cover launch
    cancellation and disconnect or shutdown effects, which are unrelated.
  - `docs` owes no edit here.
- **Obligation 2, training leg: satisfied (qa, 2026-09-30).**
  - `training` reported the refusal-era text removed from examples 21 and 23.
  - QA checked the working tree. Neither file, nor `examples/CLAUDE.md` or
    `examples/plan-examples.md`, still carries the known-red header, the
    `disagrees on declared parameter identity` refusal, a 0907 reference or a
    dark-part marker. The remaining `=== Part N ===` headings are ordinary
    lesson sections.
  - The removal is uncommitted, so this holds only in the change-set that
    commits it.
  - The `test` and stdlib legs remain.

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

1. **Evidence (`qa`).** Discharged: the refusal closed on the seven cells, and
   the balance obligation on the K2 cell above.
2. **Stale refusal text (route to owners).** Once the cells pass:
   - `test` updates the `// defect:` notation on those cells;
   - `training`'s leg for examples 21 and 23 is satisfied; the S122
     disposition records the check;
   - `test` flips the retained red segment in `repl/demos/archive/ring4s.demo`;
   - `dev` (stdlib) authors the six `core.io` self-tests listed in
     `stdlib/plan-stdlib.md` §6.2.
   - The `docs` leg is satisfied; the S122 disposition records the check.
3. **Introspection (`spec`/`design` int).** `Bind` and `IO` are named by
   diagnostics yet `/info Bind` and `/info IO` report unknown symbols while
   `Pure` introspects. Decide whether the manually seeded `Bind` must be
   introspectable.

## Closure

The listed owners have removed their refusal-era text or recorded why it
stays, and obligation 3 is decided. The evidence obligation is already met.
