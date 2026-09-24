---
number: 0863
target: /dev
filed_by: /dev
filed_at: 2026-07-24
sprint_filed: 117
refers_to: design/arch/macro-availability-model.md;
  design/int/int.md;
  design/int/s117-conformance-recovery.md;
  tests/spec_11_stdlib.rs::def_definition_echo_lists_every_emitted_definition_in_order;
  tests/spec_11_stdlib.rs::def_info_and_sig_describe_macro_while_bare_use_expands_value
status: open
---

# Macro checkpoints and ordered definition results — coverage and interior reconciliation

## Current state (verified 2026-09-24)

- The user replaced the Sprint 117 cluster-wide prepared transaction with
  durable source-order macro checkpoints on 2026-09-03. The architecture is
  [macro availability](../macro-availability-model.md); the Binary/int
  mechanism is `design/int/int.md` (the REPL-eval refinement and macro
  checkpoint paragraphs).
- `PreparedMacroTurn`, `TurnCheckWorld`, `EnteredMacroProvenance` and
  `PreparedPresentation` are absent from source. `TurnDefinitions` carries
  every emitted definition in order, so a `def` echo lists both the backing
  function and its zero-argument macro.
- Existing evidence includes the two named `spec_11_stdlib` cases,
  `spec_09_macros` checkpoint cases and
  `s76_macro_availability::generated_macro_checkpoint_is_not_replayed_after_later_dependency_gap_neg`.

## Remaining obligation

1. **Focused coverage (`qa` allocates, `test`/`dev` author).** Confirm or add
   evidence for each checkpoint property not yet witnessed:
   - a failure at each checkpoint preparation and backend boundary leaves no
     partial parent, clause, owner or GOT update;
   - a successful checkpoint survives a later failed form while the non-macro
     cluster publishes nothing;
   - a failed macro redefinition keeps the earlier committed macro;
   - a shrinking redefinition retires exactly the surplus clause rows;
   - dependency-module publication, and retry without duplication or
     reordering;
   - private emitted definitions; zero, one and several emitted definitions
     in source order; direct `defmacro` controls.
2. **Interior reconciliation (`design` int).**
   `design/int/s117-conformance-recovery.md` still describes the superseded
   global transaction in its retained sections. Reduce it to current
   mechanism or retire it.

The stdlib face-3 API question stays with FIXME 0800.

## Closure

Each listed property has an executing witness or an explicit `qa`
disposition, and no current int design describes the superseded transaction
as authority.
