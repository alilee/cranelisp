---
number: 0625
target: /testing
filed_by: /dev
filed_at: 2026-07-16
sprint_filed: 110
refers_to: tests/spec_07_traits.rs::trait_method_sig_bare_user_type_resolves (TX-1)
status: open
---

# TX-1 e2e is spec-ill-formed: it writes capital `Self`, which spec §7 says is an ordinary named type, not the self keyword

## Issue

The S110 W-TC (0590) convergence landed. The TX-1 behaviour it is meant to
prove — **a bare in-scope user type resolves in a trait-method sig** — is
CORRECT post-convergence: the user type `MyType` now resolves via the symbol
table. Verified directly:

```
(deftype MyType Mk)
(deftrait Tt (m [:MyType x] :MyType))   ; registers OK — :user/Tt ; deftrait
```

But the committed TX-1 test `trait_method_sig_bare_user_type_resolves` writes
the method **return type** as capital **`Self`**:

```
(deftrait Tt (m [:MyType x] Self))
```

Per **spec/07-traits.md §7 line 57** (the "Note on spelling", recently scribed,
"matches the as-built compiler"):

> The keyword for the implementing type is the lowercase token `self` … **There
> is no capitalized `Self`; writing `Self` denotes an ordinary named type and
> fails resolution unless such a type exists.**

The frontend (`ast_builder.rs::build_type_expr`) maps only lowercase `self` to
`TypeExpr::SelfType`; capital `Self` becomes `TypeExpr::Named("Self")`. Since no
type named `Self` exists, it correctly errors `unknown type 'Self'`. Before the
convergence this was masked — the `MyType` param (resolved first) errored first,
so the `Self` return type was never reached.

So TX-1 exercises TWO behaviours and only one is well-formed: the `MyType`
resolution (the convergence target — now GREEN) and a capital-`Self` return type
(spec-ill-formed — correctly errors). The test cannot flip GREEN against a
spec-conforming compiler without the compiler wrongly resolving capital `Self`.
Making capital `Self` resolve would violate §7 line 57 — out of the question.

This is the "verify-example-well-formed-before-framing-a-fork" class: the plan
row (PLAN.md §S110 C TX-1) and the design note (§3) both use `Self` loosely to
denote "the self type"; the language keyword is lowercase `self`.

## Proposed resolution

`/testing`: change the TX-1 return type from capital `Self` to lowercase
`self` in `tests/spec_07_traits.rs::trait_method_sig_bare_user_type_resolves`:

```
(deftype MyType Mk)
(deftrait Tt (m [:MyType x] self))
(impl Tt MyType (defn m [x] x))
(m Mk)
```

With lowercase `self` the return type is the implementing type (`MyType`), the
impl registers, and `(m Mk)` returns `Mk` — the intended TX-1 positive. This
change makes TX-1 flip GREEN against the landed convergence (no compiler change
needed; the `MyType` resolution — the actual behaviour under test — already
works). The assertion prose (`!contains("unknown type")` + `contains("Mk")`) is
unchanged.

TX-2/TX-3 (bare user type × HKT sig/impl) if authored should likewise use
lowercase `self` where a self-type return is intended.

## Context

Found by `/dev` (typecheck) during the S110 W-TC 0590 landing: after the
mirror-1 tightening made `MyType` resolve, TX-1 surfaced the capital-`Self`
return type as `unknown type 'Self'`. All other TX/FV rows behave as designed
(TX-5 flips GREEN — unknown HKT Named now errors; TX-8/TX-9 FV-13/FV-14 fences
hold GREEN; TX-6 covered by /dev typecheck unit tier per the plan deferral).
