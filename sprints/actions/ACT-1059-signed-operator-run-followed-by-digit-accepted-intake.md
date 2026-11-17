---
id: ACT-1059
title: An operator run that starts with `+` or `-` and is followed by a digit is read as two tokens
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-16
refers_to:
  - spec/01-lexical.md
  - crates/cranelisp-frontend/src/reader.rs
  - audits/cranelisp-frontend-s123.md
  - tests/plan/s124-evidence-delta.md
---

## Observation

Frontend audit R3, accepted by the user at S124 Phase 1 and executed by `qa`
on `target/debug/cranelisp` at `4b58ab93`, 2026-11-16, with no prelude. The
fixtures are REPRO-R3 of the
[S124 evidence delta](../../tests/plan/s124-evidence-delta.md#35-frontend-audit-r1-r2-r3).

- **Requirement.** [§1.4.2](../../spec/01-lexical.md#142-operator-symbols):
  `operator_symbol = operator_char+ !digit`. An operator run MUST NOT be
  immediately followed by a digit.
- **Accepted.** `(let [+* 5] (primitives/add-i64 +*1))` as the value of
  `main` runs and exits 6: `+*1` is read as the symbol `+*` and the integer
  `1`. `-*1` and `->1` behave the same way.
- **Control.** `**1` in the same position is rejected:
  `parse error at 63..65: operator symbol must not be immediately followed by
  a digit`. `+1` and `-1` read as signed integers, and `+* 1` with a space is
  two tokens, as required.
- **Class:** `silent-accept`.

## Attribution

- **Mechanism: confirmed at source.** In `crates/cranelisp-frontend/src/reader.rs`,
  `read_plus_or_operator` and `read_minus_or_number` return the symbol after
  `consume_operator_chars` without the digit guard that `read_operator`
  applies. The `**1` control takes `read_operator` and differs only in its
  first character. *Refuted if* a signed branch that applies the guard still
  accepts `+*1`.
- **Entry point:** frontend implementation. No public type changes.
- **Coverage.** The §1.4.2 band cites three reader unit tests, none with a
  digit after a `+`- or `-`-led run.

## Next

1. `test` commits REPRO-R3 as a failing-not-ignored RED with its control.
2. Frontend `design` then `dev` apply the guard in both signed branches, with
   reader unit rows for `+*1`, `-*1`, `->1` and the preserved `+1`, `-1`, `+`.
3. `qa` restores the §1.4.2 band as `[Tested+Neg …]` when the cell passes.

## Completion evidence

REPRO-R3 fails for the acceptance, then passes with the reader error, with the
signed-integer and spaced controls unchanged.
