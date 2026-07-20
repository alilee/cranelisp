---
number: 0719
target: /qa
filed_by: /port
filed_at: 2026-07-20
sprint_filed: 114
refers_to: tests/mc_x4_multi_sig_return_consumer.rs (all 3 GREEN) +
  exemplar/grid.cl make-grid/peers deliberate two-function hold +
  exemplar/plan-exemplar.md §"Multi-sig Vec-helper showcase (S113 Phase 6b)"
status: open
---

# MC-X4 residual: exemplar make-grid/peers multi-sig collapse still fails despite MC-X4/X4b green

## Severity
Important (coverage-by-definition-variants gap — the standing /qa audit category;
the S114 dispatch asserted "the MC-X4 hold is now RELEASED" and it is not, for the
exemplar's real-program shape)

## Context — the S114 assertion this falsifies

The S114 Phase-6a /port dispatch (and the SPRINT.md close record) state that the
S113 hold keeping `make-grid`/`peers` two-function was "correctly held on MC-X4"
and that "that hold is now RELEASED (MC-X4 fixed)." The unit + e2e battery agrees:

- `cranelisp-typecheck program::tests::single_sig_consumer_of_multi_sig_return_monomorphised_mc_x4` — GREEN
- `cranelisp-typecheck program::tests::untyped_adt_field_consumer_of_multi_sig_return_monomorphised_mc_x4b` — GREEN
- `tests/mc_x4_multi_sig_return_consumer.rs::poly_consumer_of_multi_sig_return_mono_miss` — GREEN (the direct poly-`(Vec Int)`-consumer face, i.e. the peers shape in miniature)
- `…::adt_wrapped_multi_sig_return_consumer_green`, `…::poly_consumer_of_single_sig_return_control_green` — GREEN

**But the exemplar's actual collapse still fails.** Both faces reproduce cleanly.

## Repro (on a scratch copy of exemplar/, never committed)

Collapse `make-grid`/`make-grid-helper` and `peers`/`peers-helper` into the idiomatic
multi-sig `(defn f ([x] (f x init)) ([x acc] …))` shape (exactly as `is-solved` was
collapsed in S113). Then `--run user.cl`:

- **make-grid collapse** →
  `user.cl:48: type error at 1893..2420: ambiguous type; add an annotation to pin the
  type of the polymorphic value monomorphised in \`user/report$String\` (a residual
  unbound type variable reached a codegen position)` — `report` USES the built grid
  (feeds `g` to solve/format-board/solution-page); the `Grid`/`SolveResult` ADT fields
  are deliberately untyped, so the multi-sig `(Option Grid)` return carries a free
  element var into the consumer.
- **peers collapse** →
  `type error at 3460..3547: ambiguous type; … monomorphised in
  \`solver/eliminate-from-peers$grid/Grid$primitives/Vec$grid/Cell+Int+Int\` (a residual
  unbound type variable reached a codegen position)` — `peers` returns a bare `(Vec Int)`
  consumed by the solver's `count`/`get`.

## Why the green battery misses it (the variant axis)

The green `poly_consumer_of_multi_sig_return_mono_miss` consumes `(build 3)`
**immediately, in the same expression** (`(mycount (build 3))`). The exemplar's failing
shape binds the multi-sig result to a **parameter** (`peers idx` → `peer-list` arg of
the recursive `eliminate-from-peers-helper`; `make-grid puzzle` → `g` matched then fed
onward through `report`), so the free element var flows **through a bound parameter into
a separately-monomorphised downstream consumer**. That distance is the untested variant.

Note the **face changed** this sprint (progress, not closure): plan-exemplar.md
predicted the peers face as codegen `undefined function` (the direct MC-X4 crash); it now
surfaces as the located "residual unbound type variable reached a codegen position" — the
W2 carrier-totality gate catches it as a type error instead of crashing codegen. Good
diagnostic, but the collapse is still blocked.

## Ask

Adjudicate: is inference *required* to succeed here without annotation (plan-exemplar's
position — "annotating the seed or the ADT field to force the back-flow would be fighting
the language")? If yes, this is an open MC-X4-family carrier-loss residual
(owner likely /dev(typecheck)) and the mc_x4 matrix needs the **parameter-distance /
untyped-ADT-field-fed-onward** variant cell added (/testing). If it is WAI that this
shape needs an annotation, then the exemplar docs' "collapse once MC-X4 is green"
guidance is wrong and /port keeps the two-function form permanently — please rule so
the exemplar can retire the "deferred, waiting on MC-X4" language decisively.

## /port disposition regardless of ruling

`make-grid`/`peers` STAY two-function in `exemplar/` for S114. The exemplar remains
correct end-to-end in both modes (`user.cl`/`solver.cl` exit 0, `tests.cl` = 40,
`--run`≡`--link` byte-identical). This FIXME blocks nothing shippable — it corrects the
false "hold released" record and prevents the next agent from re-attempting a collapse
the green tests wrongly imply is legal.
