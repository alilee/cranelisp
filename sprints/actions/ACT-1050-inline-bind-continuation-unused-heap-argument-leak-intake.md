---
id: ACT-1050
title: An inline bind continuation that ignores a heap argument leaks it
status: deferred
priority: required
from: qa
to: qa
sprint: 123
filed_at: 2026-11-16
refers_to:
  - tests/bind_unused_heap_argument.rs
  - crates/cranelisp-backend/src/compiler/control_flow/lambda.rs::compile_lambda
  - crates/cranelisp-backend/src/compiler/fn_compiler.rs::emit_release
  - tests/plan/s123-evidence-delta.md
---

## Observation

`(bind (Pure [49]) (fn [v] (Pure 49)))` leaves the bound `Vec` unreleased.
Each evaluation leaks one block, so a loop leaks without bound. The armed
release check stays silent, so this is a leak, not a memory-safety fault.

- **Repro:** `tests/bind_unused_heap_argument.rs`, 12 RED subjects, one for
  each of `--run`, `--link` and the REPL, moves on and moves off, flat
  `[49]` and nested `[[49]]` payloads. Each fails at `assert_balanced` with
  marginal residual 1 (flat) or 2 (nested), after both halves exit with the
  right value.
- **Controls,** passing in every leg: the same continuation let-bound and
  then passed (the pair's control half); a named `defn` passed to `bind`;
  a continuation that uses `v`.
- **Not caused by S123:** the pre-U′ control compiler gives the same counts
  in both polarities
  ([QA intake](../../tests/plan/s123-evidence-delta.md#310-u-cost-and-residue-readings-and-the-w2-suite)).
- **Carried to S124** under the correction-loop stop rule
  ([METHOD §2.5](../METHOD.md#25-mid-sprint-adjustment)): it was found
  after W2's first review round, and it neither loses data nor crashes. The user may pull it back into S123.

## Attribution

Provisional. The mechanism was not observed at its seam:
`CRANELISP_CODEGEN_DUMP` does not print lambda bodies.

- **Hypothesis:** the inline continuation reaches `compile_lambda` without
  a heap type for its parameter. The planned drop at introduction then
  emits nothing, because `FnCompiler::emit_release` returns early for an
  absent or non-heap type (source read 2026-11-16).
- **Supporting control:** the let-bound twin differs only in where the
  lambda is written, and it balances. A source annotation `(Vec Int)` on
  the parameter does not cure the subject.
- **Candidate producers:** typecheck's recorded type for a lambda in a
  builtin's argument, or the backend's reading of it.
- **Refuted if** the subject lambda's CLIF releases its parameter.

## Request

1. `dev`(backend) observes the parameter type that reaches `compile_lambda`
   for the subject and for the let-bound control before choosing a fix, and
   reports the producer. If the producer is typecheck, the coordinator
   routes it there.
2. The correction must not:
   - release in the `bind` node or its disposer, which double-releases
     the used-argument control;
   - cover only `Vec` payloads (the nested cells guard this);
   - cover only `bind` when the type is lost for every inline lambda
     argument to a builtin.
3. `dev` adds a module row at the seam that owns the fix.
4. `qa` then decides whether other builtins that take an inline lambda need
   independent evidence.

## Completion evidence

- All 18 tests in `tests/bind_unused_heap_argument.rs` pass, with no change
  to their assertions.
- The module row fails without the fix and passes with it.
- `test` adds `fixed=` to the cells' `// defect:` lines.
