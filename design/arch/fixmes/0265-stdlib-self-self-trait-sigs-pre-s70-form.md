---
number: 0265
target: /stdlib
filed_by: /sprint
filed_at: 2026-06-05
sprint_filed: 76
refers_to: stdlib/num/num.cl, stdlib/compare/eq.cl, stdlib/compare/ord.cl, spec/07-traits.md §7.1, design/arch/fixmes/0264-qa-trait-fixtures-self-self-pre-s70-form.md
status: open
---

# stdlib trait files carry the pre-S70 `[self self]` trait method-sig form — parse-rejected

## Issue

The S76 Wave-2 gate review confirmed: per spec §7.1 (post-S69 Sub-26, cascaded S70),
trait method-sig brackets carry param **names** (bare = implementing type), so
`(= [self self] Bool)` declares two params both named `self` and is correctly rejected
by the §5.1.1 duplicate-parameter check (`parse error: duplicate parameter name 'self'`).

The frontend's own unit tests were cascaded to the canonical distinct-name form
(`(+ [a b] self)`) in S70 ("S70 cascade row #9"), but the stdlib trait files missed
that cascade:

- `stdlib/num/num.cl`
- `stdlib/compare/eq.cl`
- `stdlib/compare/ord.cl`

Any program loading the real stdlib prelude fails at parse on these files. This is
half of the S76 e2e "Class B" failure block (~108 tests); the test-fixture half is
FIXME 0264 (/qa). Fix order matters: this stdlib half gates the `TestStandard`
prelude path that 0264's fixtures share.

## Proposed resolution

Rewrite the trait method signatures in the three files to the post-S70 canonical
form with distinct param names (e.g. `(+ [a b] self)`, `(= [a b] Bool)`), per the
spec §7.1 examples. Verify by piping a stdlib-prelude program through the real REPL
(per `memory/feedback_demos.md`) and confirming the Class-B `duplicate parameter
name 'self'` failures clear.

## Operational implication / Context

Identified by the S76 Wave-2 fire-C diagnosis + gate review (frontend verified
unchanged in W2 — the parser is spec-correct; the content is stale). Pairs with
FIXME 0264 (/qa fixtures). Together 0263+0264+0265 are expected to collapse the
S76 e2e failure count from ~403 to the declared macro wall (3) + baseline staleness.
