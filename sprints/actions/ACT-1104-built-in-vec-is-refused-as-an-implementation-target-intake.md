---
id: ACT-1104
title: The built-in `Vec` is refused as an implementation target, applied or as a constructor
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-21
refers_to:
  - spec/07-traits.md §7.3
  - spec/07-traits.md §7.2.3
  - spec/03-types.md §3.2.7
  - spec/appendix-c-nfr.md §C.2.4
  - crates/cranelisp-typecheck/src/traits/impl_check.rs
  - design/arch/core-library-boundary.md
---

## Origin

`arch`, [core/library boundary](../../design/arch/core-library-boundary.md)
(`38b4c34d`): `(impl (Functor f) (Functor Vec) …)` is refused. `qa` took it
in on 2026-11-21.

## Observation

`qa`, 2026-11-21, the debug binary built from `9bc97297`, no prelude,
`--run --no-cache`, a scratch directory since removed. `Sz` is
`(deftrait Sz (sz [self] Int))`.

| Implementation | Observed |
|---|---|
| `(impl Sz (Vec Int) (defn sz [v] (vec-len v)))`, `(sz [1 2 3])` | **Refused:** ``Vec takes 0 type parameters but is applied to 1 here; apply it to exactly its arity: `(Vec )` `` |
| `(impl Sz (Vec a) …)` | **Refused,** the same |
| `(impl (Functor f) (Functor Vec) …)` | **Refused:** `Vec has 0 type parameters; trait Functor expects a constructor of arity 1` |
| `(impl Sz Vec …)` | Refused: `type argument count mismatch for primitives/Vec: expected 1, got 0` |
| Control: `(defn n [:(Vec Int) v] (vec-len v))`, `(n [1 2 3])` | 3 |
| Control: `(impl Sz (Option a) (defn sz [v] 4))`, `(sz (Some 1))` | 4 |
| Control: `(impl (Functor f) (Functor Option) …)` | Accepted |

## Classification: a defect for the applied targets

- [Spec §3.2.7](../../spec/03-types.md): `Vec` is "parameterized by element
  type", and `(Vec Int)` is a type everywhere else.
- [Spec §7.3, Case 1](../../spec/07-traits.md): a conventional
  implementation's target is any type of kind `*`. A concrete applied type
  and a polymorphic applied type are both accepted for `Option`. The first
  two rows are legal programs refused.
- **The diagnostic contradicts itself and the fourth row's:** one says
  `Vec` takes no parameter, the other that it expects one.
- **Severity: a legal program refused.** No implementation of any trait can
  be written for a vector type.
- **Age: not established.**

**The higher-kinded row is held, not classified.** §7.2.3 requires the
target's parameter count to match and names only the four scalar types as
refused, so its text reads for acceptance. Whether `Functor` over the
built-in collections is expressible is row CL05 and CL36 of the S124-Q16
inventory, which the user has not confirmed. No cell is allocated for it.

## Attribution: typecheck, provisional

- **In source.** `traits/impl_check.rs` reads the target's parameter count
  from its type declaration, and the built-in `Vec`'s declaration lists
  none. The type-expression resolver applies `Vec` at one argument by its
  own rule (the module rows cited at §3.2.7).
- **Not decided:** whether the fault is the declaration that lists no
  parameter or the checks that read it. Both are in typecheck.
- **Control.** The annotation row and the `Option` rows differ only in the
  type named.

## Routing

- **`qa` holds this action.**
- **`test`:** T-VEC-IMPL, in the
  [S124 evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test).
- **`design`(typecheck), then `dev`(typecheck):** the correction, carried on
  T-VEC-IMPL unless the user schedules it.

## Completion evidence

T-VEC-IMPL is committed, observed RED on its value clauses, and passes on
the corrected build with its controls unchanged. The higher-kinded cell is
allocated or declined once S124-Q16 is confirmed.
