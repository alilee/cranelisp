---
number: 0889
target: /dev
filed_by: /sprint
filed_at: 2026-07-26
sprint_filed: 118
refers_to: design/int/macro-turn-ownership.md;
  src/expander.rs::invoke_clause;
  tests/macro_turn_marshal_leak_0889.rs;
  tests/plan/s122-evidence-delta.md (Q5 matched measurement)
status: open
---

# Macro-turn marshal leak: the unclassified 46-allocation residue

## Open record

A full stdlib-prelude session still ends with **46 allocations that are not
freed**. The Q5 measurement is alloc 1,198 against dealloc 1,152. It was taken
on the same input and configuration as S118's 1,143 residual; see the
[evidence delta](../../../tests/plan/s122-evidence-delta.md).

- The 46 are **unclassified**. The RC summary cannot tell whether they are
  remaining macro-turn allocations, retained session or runtime owners, or
  another allocation class.
- The 46 are not a threshold, a gate or a zero-leak claim. Do not call them
  harmless overhead, and do not call them a proven leak, without liveness or
  provenance evidence.
- **Closure.** Attribute the 46 by provenance. Then either fix a macro-turn
  share, or re-home a share that belongs elsewhere to its owner, and retire
  this record.
- **Trigger.** Any claim of zero session residue must first resolve this
  provenance or narrow the claim. No experiment is scheduled merely because
  the number is nonzero.
- **Out of scope.** Residue after a macro *runtime error* is
  [ACT-0976](../../../sprints/actions/ACT-0976-macro-runtime-error-residue-intake.md).
  The macro-turn contract's Rule 3 permits forfeiting the argument tree on
  that path.

## Resolved in S122

These claims of the original filing no longer hold, verified against source
on 2026-09-30:

- **The marshaller produces single-owner trees and transfers them.**
  `src/marshal.rs` returns `Owned` roots whose parents own their children.
  `protect_marshalled_cell` and the marshal-side `rc_inc` no longer exist.
- **A successful expansion discharges its result exactly once.**
  `expander.rs::invoke_clause` reads the result through `runtime_to_sexp`,
  then calls `consume_sexp`.
- **Evidence.** Both balance cells in `tests/macro_turn_marshal_leak_0889.rs`
  pass: `macro_turn_marshal_one_argument_expansion_is_balanced` and
  `macro_turn_marshal_nullary_expansion_is_balanced`.
- **Contract.** [`design/int/macro-turn-ownership.md`](../../int/macro-turn-ownership.md)
  is the current protocol.
