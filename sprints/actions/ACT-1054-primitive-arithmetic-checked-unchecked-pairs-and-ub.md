---
id: ACT-1054
title: Pair checked and unchecked arithmetic primitives and define undefined behaviour
status: deferred
priority: advisory
from: sprint
to: spec
sprint: 123
filed_at: 2026-11-16
refers_to:
  - spec/12-runtime.md
  - spec/appendix-a-builtins.md
  - spec/07-traits.md
---

## Request

The user's direction (S123 Phase 5 → 6a checkpoint, 2026-11-16), deferred
because it is primitive behaviour, not language behaviour. The user's words:
"add-i64 should have a pair unchecked-add-i64 and it should wrap (and
unchecked-div-i64 should be allowed to trap on /0). trap and wrap being
manifestations of undefined behaviour. add-i64 should return a Result and
error on wrap. … we should tighten our definition of UB. functions that can
panic should declare when their behaviour is undefined."

Frame for the user, when scheduled:

- Checked integer primitives (`add-i64` and its siblings, `div-i64`) report
  failure as a value: a `Result` that errors on overflow or a zero divisor.
- Each has an `unchecked-` twin whose failure case is undefined behaviour;
  wrapping and a CPU trap are both admissible manifestations.
- A definition of undefined behaviour for the language, and a rule that a
  function that can panic or has undefined behaviour declares the conditions.

## Current state

`spec/12-runtime.md` §12.7.3: `add-i64`, `sub-i64` and `mul-i64` wrap;
`div-i64` panics on a zero divisor and wraps `Int.MIN / -1`;
`primitives/checked-quot` returns `Option`. A stdlib's `Num Int` chooses its
own panic-aversion (§7.7, user ruling 2026-11-16). On x86 a CPU divide trap is
`SIGFPE`, which ends the process by signal rather than through the §12.7
panic path, so a trapping primitive also needs its exit behaviour stated.

## Disposition

Deferred by the user. Not scheduled; carry to the roadmap.
