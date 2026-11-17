---
id: ACT-1062
title: A match on a type whose fields mention its parameters out of declaration order binds each field with another parameter's type
status: open
priority: blocking
from: qa
to: qa
sprint: 124
filed_at: 2026-11-16
refers_to:
  - spec/06-pattern-matching.md
  - spec/12-runtime.md
  - crates/cranelisp-backend/src/compiler/context.rs::ctor_field_types
  - design/backend/non-concrete-release-contract.md
  - tests/plan/s124-evidence-delta.md
---

## Observation

Read from source by `design`(backend) in S124 Phase 3 and executed by `qa` on
`target/debug/cranelisp` at `4b58ab93`, 2026-11-16, with no prelude. Fixtures,
controls and the full table are §8.2 of the
[S124 evidence delta](../../tests/plan/s124-evidence-delta.md#82-act-1062--a-match-binds-another-parameters-type-memory-unsafe).

```clojure
(deftype (P a b) (MkP [:b y :a x]))
(defn f [p] (match p [(MkP y x) (add-i64 x (str-len y))]))
(defn main [] (Pure (f (MkP "abc" 2000))))
```

- **Required:** 2003 (exit 211).
- **Observed:** SIGSEGV under `--run`, `--link` and the REPL, with and
  without `CRANELISP_RC_DEC_CHECK`.
- **Control:** the same program with the fields declared `[:a x :b y]` exits
  211 with 3 allocations and 3 frees.
- **Other faces:** a parameter no field mentions (`(deftype (R a b) (MkR [:b y]))`
  at `(R Int String)`) aborts in the release path; the synthetic accessors of
  an out-of-order product (`Duo.x`, `Duo.y`) fault the same way. Each has a
  passing in-order control.
- **Class:** mechanism `projection-mirror`; faces `scalar-as-pointer` and
  `uaf`. This is a memory-safety defect in a legal program.

## Attribution

- **Mechanism: observed at the emission seam.** In the subject's CLIF for
  `f` the retain is applied to the word loaded from the `Int` field, and the
  `String` field reaches a consuming call with no retain. The control puts
  the same retain on the `String` field. The pair differs only in field
  order.
- **Locus: a source reading consistent with every leg.**
  `CompileContext::ctor_field_types` pairs the scrutinee's type arguments
  with type variables in order of first appearance across the constructors'
  fields. Drop glue and `cranelisp_types::ctor_field_types_at` pair them with
  the declared parameters.
- **Owner: backend.** The REPL echoes the correct type for `f`.
- **Refuted if** `ctor_field_types_at` returns the same pairing for the
  subject.
- **Why coverage missed it:** no corpus type mentions its parameters out of
  declaration order.

## Request

1. `test` commits REPRO-1062-a to REPRO-1062-d of the
   [evidence delta](../../tests/plan/s124-evidence-delta.md#91-type-concreteness-item-1)
   in `tests/spec_06_pattern_matching.rs`, failing and not ignored, with
   `// defect: class=projection-mirror locus=crates/cranelisp-backend/src/compiler/context.rs::ctor_field_types found=S124 owner=/dev`.
2. `dev`(backend) lands the M-1062 module row RED, then close step 1 (packet
   row D1), which deletes the walk
   ([release contract §7.4](../../design/backend/non-concrete-release-contract.md#74-the-r-1-structural-close-open)).
3. The correction must cover sums whose constructors disagree on first
   appearance, and the accessor frame, not only a product match.

## Completion evidence

- Each REPRO-1062 subject fails by signal before step 1 and passes after it;
  every control passes throughout.
- The accessor leg passes after step 1 and after the accessor producer
  correction.
- `qa` adds the parameter-order axis to the definition-variants audit in
  `tests/plan/PLAN.md` and deletes this action.
