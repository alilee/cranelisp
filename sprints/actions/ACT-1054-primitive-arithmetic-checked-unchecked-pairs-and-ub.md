---
id: ACT-1054
title: Robust primitives; panics removed; unchecked primitives and their warning a future requirement
status: open
priority: advisory
from: sprint
to: spec
sprint: 126
filed_at: 2026-11-16
refers_to:
  - spec/12-runtime.md
  - spec/appendix-a-builtins.md
  - spec/07-traits.md
  - spec/appendix-d-open-questions.md
  - tests/spec_12_runtime.rs
---

## Request

Implement the user's ruling of 2026-11-28, recorded by `spec` as S125-Q12 in
[appendix D](../../spec/appendix-d-open-questions.md). It supersedes the
2026-11-16 direction quoted below wherever the two differ.

- **Every primitive the language offers is robust.** It reports failure
  through its type and does not crash.
- **Unchecked primitives are a future requirement, not built now.** These are
  `unchecked-` primitives whose failure is undefined behaviour ("the
  programmer brought it upon themselves"). With them comes a compiler warning
  on any function that can reach one through its calls.
- **Runtime panics are removed as a category.** This replaces the 2026-11-15
  ruling in §12.7.2. The current panic sources, `div-i64` with a zero divisor
  and `vec-get`/`vec-set` out of bounds, become robust forms.
- **Stack exhaustion and allocation failure** SHOULD produce a one-line
  diagnostic naming the cause, at no cost to execution that does not fail,
  where the platform permits. An operating-system out-of-memory kill is a
  named limit.
- **Graceful failure is the platform designer's responsibility.** "The pure
  language should assume it, not guard against it."

Route:
1. `spec` rewrites the sections listed in the S125-Q12 inventory. Its 30
   pointers mark them.
2. `arch` and `design` work on the primitives and the runtime diagnostic.
3. `qa` re-allocates evidence. The T-STACK cells
   (the `s125_stack_exhaustion` cells in `tests/spec_12_runtime.rs`) are retargeted to the
   diagnostic, and the panic-source cells are retired or rewritten.
4. `dev`, then the stdlib, examples and exemplar migration.

The §9.9.4 and §4.12.5 "runtime error" wording reconciliation is part of
step 1.

## Earlier direction (2026-11-16)

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

Scheduled by the user's 2026-11-28 ruling. Candidate scope for S126.
