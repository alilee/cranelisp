---
id: ACT-1097
title: A trait method signature accepts a bare primitive type name the module has not imported
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-20
refers_to:
  - spec/03-types.md §3.1
  - spec/08-modules.md §8.9.1
  - spec/07-traits.md §7.1
  - crates/cranelisp-typecheck/src/resolve.rs::resolve_named
  - audits/cranelisp-typecheck-s124.md
---

## Origin

`audit`, typecheck assessment finding R6 (`8d983bae`). `qa` took it in on
2026-11-20.

## Observation

`qa`, 2026-11-20, the debug binary built from `39db1bb1` (source unchanged
at `8d983bae`), no prelude, `--run --no-cache`, scratch directories since
removed. Each file ends with `(defn main [] (primitives/Pure 0))` unless
shown.

| Declaration, with no import | Observed |
|---|---|
| `(deftrait T (f [self] Int))` | **Exit 0** |
| `(deftrait T (f [self :Int n] Bool))` | **Exit 0** |
| `(deftrait T (f [self] (Vec Int)))` | **Exit 0** |
| `(deftrait (F f) (cnt [:(f a) x] Int))` | **Exit 0** |
| `(deftrait (F f) (cnt [:(f Int) x] primitives/Bool))` | **Exit 0** |
| The first row, a type `D`, `(impl T D (defn f [self] 1))` and a `main` returning `(f Mk)` | **Exit 1, the method's value:** the bare `Int` was taken as the return type |
| `(deftrait T (f [self] primitives/Int))` | Exit 0, which conforms |
| `(import [primitives [Int]])`, then the first row | Exit 0, which conforms |
| `(defn f [] :Int 1)` | Refused: `unknown type` |
| `(deftype D (Mk [:Int n]))` | Refused |
| `(deftrait T (f [self :Strng n] primitives/Int))` | Refused: ``unknown type `Strng` `` |

## Classification: a defect against spec §3.1 and §8.9.1

- [§3.1](../../spec/03-types.md): a bare primitive type name "MUST come
  into scope through either prelude re-export or an explicit import;
  otherwise they are a compile-time 'unknown type' error". §8.9.1 says the
  same of every name in `primitives`. Neither excepts a trait signature.
- **The return position has a second reading that also refuses.** By
  [§7.1](../../spec/07-traits.md) a trailing element is a return type only
  if it resolves as a type. An unimported `Int` does not, so it is a body
  expression naming an undefined value. The program is refused under
  either reading; only the diagnostic's kind differs.
- **Severity: an illegal program is accepted.** No wrong value in a legal
  program and no memory hazard.
- **Not a regression.** The exception entered with the resolver's
  convergence (`5ed07d60`, 2026-07-16), which kept what the earlier
  resolvers did.

## Attribution: typecheck

- **In source.** `resolve_named` returns the intrinsic scalar before any
  lookup when its context sets `scalar_fastpath`, and the checker sets it
  for trait and higher-kinded signatures only. The field's comment states
  the purpose: a signature naming `Int` in a module that does not reach
  `primitives` "keeps working".
- **Control.** The last three rows: the same bare name in an annotation or
  a type field is refused, and a misspelt name in the same trait position
  is refused. The acceptance is the four scalars in the signature contexts.
- **Refuted if** a build with the flag false in those contexts still exits
  0 for the first row.
- **`(Vec Int)` is accepted too** and `Vec` is not one of the four scalars.
  That row's path is not read.

## Lead, not classified

`(deftrait T (f [self] (nosuch self)))`, with nothing implementing `T`,
exits 0: a default body naming an undefined function is not reported at
the declaration. `qa` did not find the requirement that decides it.

## Routing

- **`qa` holds this action.**
- **`test`:** T-TRAIT-SCALAR, in the
  [S124 evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test).
- **`design`(typecheck), then `dev`(typecheck):** the correction, carried on
  T-TRAIT-SCALAR unless the user schedules it.
  [Resolver convergence](../../design/typecheck/type-expr-resolver-convergence.md)
  records the fast path as built.

## Completion evidence

T-TRAIT-SCALAR is committed with `// spec: spec/03-types.md §3.1`, observed
RED on its refusal clauses, and passes on the corrected build with both
controls unchanged. `qa` edits the §3.1 band.
