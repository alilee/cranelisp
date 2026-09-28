---
id: ACT-1005
title: Establish macro-order and begin round-trip edge cases
status: deferred
priority: required
from: sprint
to: qa
sprint: 122
filed_at: 2026-09-28
refers_to:
  - spec/09-macros.md
  - repl/spec/15-session-persistence.md
  - design/arch/macro-availability-model.md
  - src/save.rs
  - tests/s76_macro_availability.rs
---

## Disposition

User-deferred from S122 for one or two sprints: revisit in S123 or S124.
The user directed recording this action and focusing on the four reproduced
persistence failures. This is the first explicit deferral of this edge-case
investigation. It neither changes macro semantics nor approves a dependency
sort or another persistence representation. QA records it as this single
item's user deferral; it is not a carry for any other open item.

## Question and evidence

Determine whether regenerating accepted REPL definitions can put a macro use
before its definition and break a cold reload, including after redefinition.
Separate execution of a macro's implementation from re-expansion of the syntax
it returns. Do not infer compiled macro-call dependencies from emitted syntax.

Source/spec inspection on `0272a5d9` plus the S122 working tree establishes:

- Macro §9.3.4 permits earlier same-module macros but prohibits same-module
  non-macro expansion-time helpers; §9.12.1 requires completed macro compilation
  checkpoints. Existing composition tests return syntax for re-expansion;
  they do not establish arbitrary calls between compiled macro implementations.
- REPL §15.4 requires authorship order and redefinition in place. The current
  regenerator groups definitions by kind. That known mismatch remains separate
  from the unproven macro-order round-trip failure; no ruling is reversed here.
- Macro-generated definitions retain their original macro invocation for
  persistence. `src/save.rs` also retains a literal REPL `begin` whole, while
  macro §9.6 forbids a literal top-level `begin` in batch source. Establish the
  actual REPL-startup/batch consequences before proposing a correction.

No failing round-trip reproduction has been established for the proposed
macro-dependency ordering edge case. Earlier suggestions of general macro
sorting or admissible dependency cycles were hypotheses, not findings.

## Completion

QA allocates a bounded reproduction covering accepted redefinition followed
by save and cold reload, with ordinary macro composition as a control. Include
original macro calls that produce multiple definitions and literal REPL
clusters where relevant. Classify current behavior against the existing
requirements; retain confirmed defects as unignored spec-traced regressions.
Route a real semantic conflict to `spec` and the user, and a realization issue
to its design owner. Retire this action if the edge-case claim is falsified.

The separate reproduced type-reload, rejected-redefinition persistence and
cached-dependency save failures remain S122 work.
