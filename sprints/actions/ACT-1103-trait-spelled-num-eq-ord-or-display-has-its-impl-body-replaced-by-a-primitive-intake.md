---
id: ACT-1103
title: A trait spelled `Num`, `Eq`, `Ord` or `Display` has its implementation for a primitive type replaced by a primitive, whatever the implementation's body says
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-21
refers_to:
  - spec/07-traits.md §7.3
  - spec/07-traits.md §7.7
  - spec/08-modules.md §8.8.3
  - crates/cranelisp-typecheck/src/traits/dispatch.rs::primitive_for_trait_method
  - design/arch/core-library-boundary.md
---

## Origin

`arch`, [core/library boundary](../../design/arch/core-library-boundary.md),
consequence C1 (`38b4c34d`). `qa` took it in on 2026-11-21.

## Observation

`qa`, 2026-11-21, the debug binary built from `9bc97297` (no compiler source
has changed since), no prelude, `--run --no-cache`, a scratch directory
since removed. Each program declares the trait itself, in its own module.

| Program | The implementation says | Observed |
|---|---|---|
| `(deftrait Num (+ [a b] self))`, `(impl Num Int (defn + [a b] (sub-i64 a b)))`, `(+ 5 3)` | 2 | **8.** Also 8 linked, and at the REPL |
| The same, `+` taken as a value: `(let [f +] (f 5 3))` | 2 | **8** |
| The same, reached through `(defn twice [:Num x] (+ x x))`, `(twice 5)` | 0 | **10** |
| `(deftrait Eq (= [a b] Bool))`, `(impl Eq Int (defn = [a b] true))`, `(if (= 1 2) 7 9)` | 7 | **9** |
| `(deftrait Ord (< [a b] Bool))`, `(impl Ord Int (defn < [a b] true))`, `(if (< 2 1) 7 9)` | 7 | **9** |
| `(deftrait Display (show [self] String))`, `(impl Display Int (defn show [self] "xx"))`, `(str-len (show 12345))` | 2 | **5** |
| Control: the first row with the trait named `Numb` | 2 | 2 |
| Control: the first row with the method named `plus` | 2 | 2 |
| Control: the `Eq` row with the trait named `Eqq` | 7 | 7 |
| Control: the `Display` row with the trait named `Displayy` | 2 | 2 |

## Classification: a defect, wrong value

- [Spec §7.3](../../spec/07-traits.md): a call to a trait method at a type
  runs that type's implementation of it. The program's own implementation
  is not run.
- **It does not wait on S124-Q16.** Whether these four traits are core or
  library (inventory row CL04) is open. Under either answer the program
  above declares its own trait: either its implementation runs, or the
  declaration is refused. Silently running a primitive is neither.
- **Severity: wrong value,** in every mode, with no diagnostic.
- **It predates S124.** The table is in typecheck since 2026-06-21
  (`66a4d41e`, by pickaxe) and was in the backend before that.

## Attribution: typecheck

- **In source.** `primitive_for_trait_method` maps a triple of bare
  spellings (trait, method, implementing type) to a primitive's name. It
  consults neither the trait's home module nor the implementation's body.
- **Control.** Renaming the trait, or the method, restores the
  implementation's value with nothing else changed.
- **Refuted if** a trait spelled `Num` in a module of another name runs its
  own body.

## For `spec`, with S124-Q16

Spec §7.7's implementation note says the four traits are seeded in the
`primitives` module. `arch` reads that as false against source. It is row
CL04 of the inventory and is not `qa`'s to settle.

## Routing

- **`qa` holds this action.**
- **`test`:** T-TRAIT-SPELLING, in the
  [S124 evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test).
- **`arch`, then `design`(typecheck) and `dev`(typecheck):** the correction
  follows the confirmed core/library classification. Carried on
  T-TRAIT-SPELLING.

## Completion evidence

T-TRAIT-SPELLING is committed, observed RED on its value clauses, and
passes on the corrected build with its renamed controls unchanged.

## Evidence state (qa, 2026-11-21, full run at `11ea995e`)

T-TRAIT-SPELLING is committed (`3904fae8`) and accepted: six subjects fail
on the primitive's value (8, 8, 10, 9, 9, 5) and three renamed controls
pass.

## Narrowed after S124-Q16 was confirmed (qa, 2026-11-22)

The confirmed classification makes `Num`, `Eq`, `Ord` and `Display` library
content (inventory row CL04). A program's own trait of one of those names
runs its own implementation. T-TRAIT-SPELLING's clause loses its refusal
arm (evidence delta §14.3).
