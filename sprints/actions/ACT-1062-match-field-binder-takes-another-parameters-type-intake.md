---
id: ACT-1062
title: Consumers that pair a type's arguments with its field variables by first appearance give each field another parameter's type
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
  - src/display.rs::build_adt_subst
  - crates/cranelisp-backend/src/compiler/trace_codegen.rs
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

## Two consumers remain after row D1 (qa, 2026-11-18)

`target/debug/cranelisp` built from `24c42430`. The twelve REPRO-1062
subjects pass: the match and accessor legs are corrected by row D1
(`dab46869`, `3deee350`, `24c42430`). The accessor leg went green on D1
alone, and `design`(typecheck) confirms no accessor producer correction is
owed.

`shapes.cl`, imported at the REPL:

```clojure
(import [primitives [*]])
(deftype (P a b) (MkP [:b y :a x]))
(deftype (Q a b) (MkQ [:a x :b y]))
(defn obsp [:(P Int String) p] (match p [(MkP y x) (add-i64 1 x)]))
(defn obsq [:(Q Int String) q] (match q [(MkQ x y) (add-i64 1 x)]))
(defn obsps [:(P Int Int) p] (match p [(MkP y x) (add-i64 y x)]))
```

| Leg | Required | Observed |
|---|---|---|
| Display subject: `(MkP "s" 2000)` | `:(shapes/P primitives/Int primitives/String) (P.MkP "s" 2000)` | signal 11 in `display::push_field_value`, reading 2000 as a string |
| Display control: `(MkQ 2000 "s")`; `(MkP 7 2000)` | their values | as required |
| Trace subject: `(trace (obsp (MkP "s" 2000)))` | a frame whose argument is `(P.MkP "s" 2000)` and result `2001` | signal 11 |
| Trace control: `(trace (obsq (MkQ 2000 "s")))`; `(trace (obsps (MkP 7 2000)))` | their frames | as required |
| Untraced: `(obsp (MkP "s" 2000))` | 2001 | as required |

- **Mechanism, read at each seam and consistent with every leg.**
  `src/display.rs::build_adt_subst` and the backend's
  `schema::subst_for_ctor_fields`, which the trace descriptor baker in
  `compiler/trace_codegen.rs` calls, pair type arguments with field
  variables in order of first appearance. Found by `review` of B3 (trace)
  and by `qa` (display).
- **Predates S124.** The release build of 00:11 on 2026-11-18 faults on both
  subjects.
- **Lead, not executed:** the backend's schema generator
  (`schema.rs`, the helper's other caller) uses the same pairing. `dev`(backend)
  corrects the helper once for both callers or reports why the generator
  differs.
- **Owners:** `dev`(`src/`) for the display reader; `dev`(backend) for the
  descriptor baker, with row B10. The baker's one-word case left with value
  flattening (packet row D4, `441e31ea`).
- **Cells (`test`), REPRO-1062-e and REPRO-1062-f** of the evidence delta
  §9.1, in `tests/match_field_parameter_order.rs`, with this filing's
  `// defect:` class and the locus of each reader.

## The backend reader is corrected; the display reader remains (qa, 2026-11-19, `f8c55626`)

- **Backend, closed at `4d2bd8a4` (row B14).** The three REPRO-1062-f
  subjects pass: in `qa`'s full run, 10 of 10 alone and 10 of 10 with
  fourteen cells running at once. The helper pairs by declared parameter
  for the descriptor baker and the schema walk; its module rows are in
  `crates/cranelisp-backend/src/schema/tests.rs`, and
  `schema_walk_pairs_an_out_of_order_product_by_declared_parameter` closes
  the schema-generator lead above.
- **`src/`, open.** `match_field_parameter_order::s124_1062_e_subject_repl`
  still ends on signal 11 in `src/display.rs::build_adt_subst`. It is
  carried on that cell with `dev`(`src/`).

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
- The accessor leg passes after step 1. Met.
- REPRO-1062-e and REPRO-1062-f fail by signal before their corrections and
  pass after them; their controls pass throughout.
- `qa` adds the parameter-order axis to the definition-variants audit in
  `tests/plan/PLAN.md` and deletes this action.
