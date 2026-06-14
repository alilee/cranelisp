---
number: 0350
target: /design
filed_by: /dev
filed_at: 2026-06-14
sprint_filed: 82
refers_to: crates/cranelisp-backend/src/compiler/control_flow.rs (span-derived closure drop-glue name `runtime/closure_drop_glue_<start>_<end>`), design/backend/ (monomorphisation of lambda-bodied polymorphic fns), design/arch/fixmes/0347-backend-monomorphise-polymorphic-fn-with-lambda-and-fold.md, crates/cranelisp-typecheck/src/program.rs (`expr_contains_lambda` gate — the band-aid that CANNOT yet be removed)
status: open
---

# Backend closure DROP-GLUE codegen name is span-derived, not monomorphisation-aware — blocks removal of the typecheck `expr_contains_lambda` band-aid (the remaining half of 0347 defect 1)

## Issue (S82 /dev typecheck finding, FIXME 0349 follow-on)

0347 defect 1 reported that a lambda-bodied polymorphic fn, when monomorphised
at >1 instantiation, emits the same span-derived **lambda function** name
(`__lambda_<start>_<end>__`) twice → linker `Duplicate definition of
identifier`. The lambda-function half was subsequently addressed in
`cranelisp-backend`. **But the closure DROP-GLUE name is still span-derived and
NOT uniquified per mono instantiation.**

The S82 task brief asked /dev (typecheck) to remove the `expr_contains_lambda`
gate in `crates/cranelisp-typecheck/src/program.rs` (the band-aid that keeps
lambda-bodied pure-parametric polymorphic fns monomorphised-in-place rather than
generalized-early), on the premise that backend defect 1 was fully fixed.
Removing the gate re-reds **exactly the same 4 examples** 0347 named, with a
DIFFERENT symbol:

```
13-higher-order.cl:  Duplicate definition of identifier: runtime/closure_drop_glue_2004_2022
21-hello-io.cl:      Duplicate definition of identifier: runtime/closure_drop_glue_4279_4289
23-io-sequence.cl:   Duplicate definition of identifier: runtime/closure_drop_glue_2752_2773
27-lazy-seq.cl:      Duplicate definition of identifier: runtime/closure_drop_glue_2290_2313
```

So the lambda-function name was uniquified, but its closure's drop-glue function
(`runtime/closure_drop_glue_<span.start>_<span.end>`) was not. When a
lambda-bodied polymorphic fn is monomorphised at N concrete instantiations, the
backend emits N copies of that same source lambda → N drop-glue defs with the
identical span-derived name → linker rejects copies 2..N.

## Proposed resolution

Owning surface: **backend** (`/design` for backend, then `/dev`).

Uniquify the closure drop-glue codegen name per monomorphic instantiation —
append the mono key (the concrete type-substitution suffix) to
`runtime/closure_drop_glue_<start>_<end>`, the SAME way the enclosing mono fn
and the lambda function are already suffixed. The two span-derived closure
symbols (lambda body + drop glue) must share the same uniquification scheme so N
mono copies of one source lambda get N distinct symbol pairs.

Once the drop-glue name is mono-aware, the typecheck-side `expr_contains_lambda`
gate (`crates/cranelisp-typecheck/src/program.rs`, two sites — the single-defn
and multi-sig writebacks, plus the helper fn) can be deleted, re-enabling the
0344/0349 generalize-before-cross-defn-use writeback for higher-order
(lambda-bodied) polymorphic fns. /dev (typecheck) will remove the gate in the
sprint the backend fix lands and verify the 4 examples stay green.

## Operational implication / Context

- **0349 (mono-variant creation under forward-reference ordering) is FIXED and
  is INDEPENDENT of this gate** — the 0344 e2e
  (`tests/spec_04_expressions.rs::polymorphic_accumulator_fold_does_not_over_unify`)
  now passes (the fold helpers contain no lambdas, so the gate never applied to
  them). This FIXME is ONLY about the lambda-bodied case the gate still
  suppresses.
- The `expr_contains_lambda` gate REMAINS in place this sprint (S82) — removing
  it without this backend fix re-reds the 4 examples. The gate's rustdoc in
  `program.rs` is updated to cite this FIXME and the drop-glue (not just
  lambda-name) root cause.
- 0347 should be re-pointed/closed against this re-attribution: its defect-1
  lambda-name half is done; its remaining half is this drop-glue collision;
  its defect-2 (monomorphised recursive-fold wrong value) is the 0344/0349
  cause and is now fixed.
