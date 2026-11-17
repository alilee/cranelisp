---
id: ACT-1050
title: An inline bind continuation that ignores a heap argument leaks it
status: open
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
  - src/bind_chain_analysis.rs::make_bind
  - tests/plan/s124-evidence-delta.md
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

**Observed 2026-11-16 at `4b58ab93`; the producer is the binary's bind-chain
rewrite.** Evidence and controls:
[S124 evidence delta §8.1](../../tests/plan/s124-evidence-delta.md#81-act-1050--the-producer-is-the-binarys-bind-chain-rewrite).

- `src/bind_chain_analysis.rs::make_bind` rebuilds every inline
  `(bind io (fn [x] …))` and gives the callee, the `Lambda` and the `Apply`
  the application's span. Typecheck records expression types by span
  (`CheckState::expr_types`), so the `Lambda` does not keep a function type
  and its parameter is introduced untyped.
- **Seam:** the subject's lambda is emitted under the `bind` form's span and
  never reads its parameter. The control's lambda carries the `fn`'s span and
  calls the `(Vec Int)` drop glue.
- **Controls:** an inline continuation the rewrite does not match (wrapped
  in `if` or `let`) balances. A parameter used twice under the rewrite
  balances under the armed check, which refutes a wrong scalar type.
- **Not observed:** the type value that reaches `compile_lambda`. The
  span-keyed table is a source reading.
- **Refuted if** the category census records no absent-arm entry for the
  subject's frame, or a rebuilt `Lambda` that keeps the written span still
  leaks.

## Request

1. `design`(int), with `design`(typecheck) for the span-keyed table, places
   the correction. It precedes close step 2, which would refuse the subject.
2. The correction must not:
   - release in the `bind` node or its disposer, which double-releases
     the used-argument control;
   - cover only `Vec` payloads (the nested cells guard this);
   - cover only the first step of a rebuilt chain (cell T-1050-a);
   - type the parameter in the backend, which would fabricate a category.
3. `dev` adds a module row at the seam that owns the fix.

## Completion evidence

- All 18 tests in `tests/bind_unused_heap_argument.rs` and T-1050-a pass,
  with no change to the committed assertions.
- The module row fails without the fix and passes with it.
- `test` sets the cells' `locus=` to `src/bind_chain_analysis.rs::make_bind`,
  their class to `node-span-collision`, and adds `fixed=`.
