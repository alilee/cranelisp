---
number: 0264
target: /qa
filed_by: /dev
filed_at: 2026-06-05
sprint_filed: 76
refers_to: tests/fixtures/preludes/test-standard.cl, tests/fixtures/prelude.cl
status: open
---

# QA trait fixtures use pre-S70 `[self self]` method-sig form — `parse error: duplicate parameter name 'self'` (the 7 mode_equiv_* failures)

## Issue

The 7 `mode_equiv_*` failures (and any test using `PreludeVariant::TestStandard`
or `PreludeVariant::TestPrelude` with trait dispatch) fail at PARSE time:

```
parse error … duplicate parameter name 'self'
```

`tests/fixtures/preludes/test-standard.cl` and `tests/fixtures/prelude.cl`
declare trait method signatures in the **pre-S70** form:

```clojure
(deftrait Num
  (+ [self self] self)
  (- [self self] self)
  …)
(deftrait Eq
  (= [self self] Bool)
  …)
```

Per spec §5.3.1 (post-S69-Sub-26, cascaded in S70), trait method-signature
brackets carry **parameter NAMES** that default to type `self` (the EBNF is
`param = ':' type_expr symbol | symbol`; a bare name is a binding name that
defaults to `TypeExpr::SelfType`). Two bare `self` entries are therefore two
parameters both named `self` → the spec §5.1.1 duplicate-parameter check
(`crates/cranelisp-frontend/src/ast_builder.rs::build_annotated_params`, line
~1521) correctly rejects them.

The canonical post-S70 form uses **distinct binder names**:

```clojure
(deftrait Num
  (+ [a b] self)
  (- [a b] self))
(deftrait Eq
  (= [a b] Bool)
  (!= [a b] Bool))
```

The frontend's own unit tests were cascaded to this form in S70 — see
`ast_builder.rs::test_build_deftrait_multiple_methods` /
`test_build_deftrait_with_default` (comments: "S70 cascade row #9 — `[self self]`
pre-cascade input rewritten to spec conformant `[a b]`"). The QA fixtures were
not cascaded alongside them.

## Proposed resolution

Rewrite every trait method signature in the two fixtures from `[self self]` to
distinct binder names (`[a b]` for binary methods, `[x]`/`[self]` for unary —
a single `self` is fine; only duplicates collide). Mechanical:

- `(+ [self self] self)` → `(+ [a b] self)`
- `(= [self self] Bool)` → `(= [a b] Bool)`
- `(show [self] String)` → unchanged (single `self`, no duplicate)

Apply to `Num` (4 methods), `Eq` (2), `Ord` (4) in both files. The `impl`
bodies already use `[a b]` (`(defn + [a b] (add-i64 a b))`) and need no change.

## Operational implication / Context

- **Pre-existing, NOT a Wave-2 regression.** `crates/cranelisp-frontend/src/ast_builder.rs`
  is unchanged in the Wave-2 working tree (`git diff` empty). The duplicate-param
  check dates to Sprint 23a; the `build_method_sig → build_annotated_params`
  routing dates to Sprint 1/53; the spec form change + frontend-test cascade
  landed in S70. The fixtures simply missed the S70 cascade.
- Frontend behavior is correct per current spec — do NOT file this against
  frontend/relax the duplicate check; the fix is the fixture content.
- This error gates `test-standard.cl` entirely (prelude fails to parse → every
  TestStandard test fails before reaching its own assertions), so it compounds
  with §0263 on that fixture. Fix both in the same fixture pass.
- Spec refs: 05-definitions.md §5.3.1 (named trait params defaulting to SelfType),
  §5.1.1 (distinct param names), 02-grammar.md §2.2.3.
