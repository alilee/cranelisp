---
id: ACT-0985
title: Allocate evidence for four ruled typecheck requirements from the forward-reference, higher-kinded dispatch and impl-rigidity leads
status: deferred
priority: required
from: qa
to: qa
sprint: 125
filed_at: 2026-09-22
refers_to:
  - spec/05-definitions.md §5.4.5
  - spec/05-definitions.md §5.13.1
  - spec/03-types.md §3.7.6
  - spec/03-types.md §3.3.2
  - design/typecheck/traits.md
  - design/typecheck/hkt.md
  - design/typecheck/inference.md
  - tests/spec_09_macros.rs
---

## Status (qa, S125 W0)

All four questions are answered (appendix D): items 1 and 3 by the user's
rulings S125-Q2 and S125-Q3, items 2 and 4 by existing text. None has an
S125 cell; the work is carried to S126, the likely typecheck focus:

1. **Q2:** two `impl` forms for one pair in one cluster refuse the cluster
   (spec §5.4.5). Allocate the refusal cell and its later-turn replacement
   control.
2. **Item 2:** an implementation an expanded `begin` places before its type
   is within §5.13.1's rule.
   `tests/spec_09_macros.rs::macro_expanded_begin_impl_neg_before_deftype_is_rejected`
   asserts the superseded refusal; `test` repairs it to the acceptance, RED
   if the implementation still refuses.
3. **Q3:** a higher-kinded method whose constructor variable occurs only in
   its result is refused at the declaration (spec §7.2.2).
4. **Item 4:** a constraint on a non-`Self` method variable stays abstract
   in an impl-method body (spec §3.3.2). Reduce the source-read lead to a
   discriminating reproduction with a control.

The original questions follow for their record.

## Request

`spec` frames each question for the user's ruling or a deferral with its
rationale. `qa` then allocates the cell the ruling decides. Each is a
source-read or probed lead with no failing cell, because the expected
outcome is unruled.

1. **Two forms for one implementation pair in one cluster.** §5.4.5 states
   replacement for an `impl` re-entered in a later input; it does not say
   whether two forms for one `(trait, type)` pair in one cluster are a
   replacement or an error. Observed (S124): the earlier form's body is
   checked at the later form's position, so a body that dispatches to an
   implementation declared after the later form is refused. Under
   replacement that is a wrong reject; under an error, a refusal with
   another message. [Typecheck traits §11](../../design/typecheck/traits.md#11-open-items)
   records the shape.
2. **An implementation a macro-expanded `begin` places before its type.**
   `tests/spec_09_macros.rs::macro_expanded_begin_impl_neg_before_deftype_is_rejected`
   requires the refusal, citing §9.6 and §8.2. §5.13.1 admits forward
   references among non-macro definitions in one cluster. Whether an
   expansion's definitions are inside that rule is not stated.
3. **A higher-kinded method whose constructor variable occurs only in its
   result,** such as `(pure [:a x] (f a))`. §3.7.6 picks the dispatch
   parameter as the first parameter that applies the constructor; with none,
   `traits/type_resolve.rs::find_hkt_param_index` falls back to the first
   argument. Is such a method admissible (`design/typecheck/hkt.md`, open
   questions)?
4. **Constraint rigidity in impl-method bodies.** A constraint on a
   non-`Self` type variable of a trait-method signature is not held abstract
   in an impl-method body ([typecheck inference §6](../../design/typecheck/inference.md#6-open-item--constraint-rigidity-in-impl-method-bodies)).
   Does spec §3.3.2 require it to be?

## Disposition history

- Narrowed and re-targeted to `spec` by `qa` at S125 Phase 3
  ([S125 evidence §2.1](../../tests/plan/s125-evidence-delta.md#21-actions)).
  Its forward-reference lead was corrected at S124; its primitive-spelling
  lead is a defect with cells (T-0985); ACT-0987's rigidity question joined
  it as item 4.

## Completion evidence

Each question is ruled or deferred with a rationale. For a ruled question,
`qa` allocates the cell and `design`(typecheck) follows the ruling.
