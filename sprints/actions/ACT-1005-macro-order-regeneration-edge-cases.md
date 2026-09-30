---
id: ACT-1005
title: Correct regeneration ordering together with macro-order and begin edge cases
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
sort or another persistence representation.

On 2026-09-30 the user also approved carrying P7's authored-order and
structural-section-order correction to S123/S124 with this action, so the
ordering requirements and macro-before-use constraint receive one coherent
solution. This is P7's first explicit deferral. REPL §15.4 rules 2 and 4
remain requirements; the current grouping/sorting is an accepted interim
nonconformance, not a reversal of those rules.

Also on 2026-09-30, the user approved the
[S122 disposition](../../tests/plan/s122-evidence-delta.md#final-disposition-proposal-2026-09-30),
whose K8 folds P6 into this action's literal-cluster cases: redefining one
member of a shared `begin` may keep the old sibling in the record. P6 is an
unobserved lead (first deferral); its falsifier is to redefine one member and
regenerate.

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
  regenerator groups definitions by kind. This established mismatch is distinct
  from the macro-order edge case, but their corrections are now scheduled
  together; no ruling is reversed here.
- Macro-generated definitions retain their original macro invocation for
  persistence. `src/save.rs` also retains a literal REPL `begin` whole, while
  macro §9.6 forbids a literal top-level `begin` in batch source. Establish the
  actual REPL-startup/batch consequences before proposing a correction.

No failing round-trip reproduction has been established for the proposed
macro-dependency ordering edge case. Earlier suggestions of general macro
sorting or admissible dependency cycles were hypotheses, not findings.

## Completion

Conform regeneration to REPL §15.4 rules 2 and 4, including after cache
restore (rule 6), together with the disposition of the macro-order cases
below. Verify appended definitions, in-place redefinitions, interleaved
definition kinds and structural-section ordering. The 2026-09-30 carry was
checked against `src/save.rs::generate_module_source` and §15.4: the current
kind grouping and structural sequence differ from the required authored order.

QA allocates a bounded reproduction covering accepted redefinition followed
by save and cold reload, with ordinary macro composition as a control. Include
original macro calls that produce multiple definitions and literal REPL
clusters where relevant. Classify current behavior against the existing
requirements; retain confirmed defects as unignored spec-traced regressions.
Route a real semantic conflict to `spec` and the user, and a realization issue
to its design owner. Retire this action if the edge-case claim is falsified.

The separate reproduced type-reload, rejected-redefinition persistence and
cached-dependency save failures remain S122 work.
