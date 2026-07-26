---
number: 0867
target: /dev (typecheck)
filed_by: /repl
filed_at: 2026-07-25
sprint_filed: 117
refers_to: spec/05-definitions.md §5.2.6;
  repl/spec.md §3.3;
  tests/spec_field_accessor.rs::bare_alias_resolves_when_field_unique;
  repl/demos/archive/ring4k.demo
status: open
---

# Polymorphic product does not mint its field accessors

## Issue

The Phase 6b REPL replay found that a concrete product mints both its canonical
field accessor and its unique bare convenience alias, while a polymorphic
product mints neither:

```lisp
(deftype (Pair a b) (MkPair [:a fst :b snd]))
(fst (MkPair 42 false))
(Pair.fst (MkPair 42 false))
```

Both accessor forms report an undefined variable. No second `fst` field exists,
so the bare failure is not the specified ambiguity case, and the missing
canonical accessor is independently non-conforming.

`spec/05-definitions.md §5.2.6` makes a unique bare field name an alias of the
canonical `Type.field` accessor without excluding polymorphic products. The
current production guard
`tests/spec_field_accessor.rs::bare_alias_resolves_when_field_unique` covers
only a concrete `Box`, leaving this type-parameter axis untested.

The archived Ring 4K demo now uses ordinary pattern extraction so its
historical FQ-type lesson remains runnable; that demo correction does not
resolve the missing accessors.

## Proposed resolution

`/qa` attributed the missing canonical and bare aliases as one
definition-variant coverage gap and added the Sprint-118 forward-flow row in
`tests/plan/PLAN.md`. `/testing` should now author a narrow,
failing-not-ignored REPL repro that pairs the polymorphic case above with the
existing concrete control and asserts both `Pair.fst` and bare `fst`.

After that reduction, `/qa` will finalize the narrow `/dev` attribution. The
eventual owner should make polymorphic product accessor enrollment mint the
canonical `Pair.fst` definition and the same unique bare
`ModuleEntry::Import` edge as a concrete product, while retaining the existing
duplicate-field ambiguity behavior.

## /qa S118 W1+ ATTRIBUTION FINALIZED (2026-07-25) — retargeted /testing → /dev (typecheck)

The W1 repro landed and REDUCED the axis (`tests/spec_field_accessor.rs`
§"THE CONSTRUCTOR-ARM AXIS", eight-form matrix at HEAD `e15ff20f`): the type
parameter is NOT causal — two polymorphic deftype-level forms mint both
accessors; a CONCRETE distinct-name constructor arm mints neither. **The
defect: accessors are synthesised only from the deftype-LEVEL field list
(plus the same-name single-ctor spelling that reduces to it); a field list
in a named constructor arm whose name differs from the type's contributes
no accessor at all** — every sum type, every distinct-name product,
including this FIXME's `(deftype (Duo a b) (MkDuo …))` case and spec
§5.2.6's own `Option.unwrap` example.

- **Owning seam (single-crate):** `crates/cranelisp-typecheck/src/adt.rs` —
  `synthesise_field_accessors` is invoked only under `if is_product` and
  only over `ctor_infos[0]`; the adjacent comment "Sum/enum fields have no
  total accessor" contradicts spec §5.2.6, which REQUIRES sum accessors and
  already specifies their semantics (partial: succeed on the matching
  variant, runtime panic on mismatch — `Option.unwrap` worked in-spec). No
  open `/spec` question.
- **Fix shape:** synthesise over EVERY constructor arm's field list with
  §5.2.6 partial semantics for multi-arm types; the §8.6.5 bare-alias
  contest classification is untouched (the retained duplicate-field
  negative family in `spec_field_accessor.rs` is the boundary fence). The
  partial-accessor panic face needs its own positive + negative cells in
  the fixing change-set (nothing mints today, so it is untestable until
  then).
- **`class=enumeration-miss` RATIFIED** (`/qa`, vocabulary owner): the
  accessor-source enumeration omits a source family. No re-label.
- Fix is capacity-dependent in S118 (not pre-authorized as a carry; an
  unfixed repro at close needs an explicit user-approved carry). Plan of
  record: `tests/plan/s118-test-plan.md` §6.2.

## Stdlib blast radius (appended by `/stdlib`, S118 Phase 6a)

Not a duplicate filing — the fix's *forward* effect on `stdlib/`, which the
attribution above does not cover. **No stdlib module is broken by the defect
today**: every affected type destructures with `match` and hand-writes its
field verbs (`collections.list/first`, `collections.pair/first`/`second`),
which is precisely why this axis stayed invisible from the library side.
Verified at HEAD `e67857ce`: `(deftype Tally [:Int passed :Int failed])`
mints `Tally.passed` **and** bare `passed`; `(deftype (Lst a) Nil2 (Cons2
[:a head :(Lst a) tail]))` mints neither `Lst.head` nor bare `head`.

The five types that would START minting when the fix lands:

| Type | Constructor-arm fields | New canonical | New bare alias |
|---|---|---|---|
| `collections.list/List` | `Cons [head tail]` | `List.head`, `List.tail` | `head`, `tail` |
| `seq.lazy/Seq` | `SeqCons [head rest]` | `Seq.head`, `Seq.rest` | `head`, `rest` |
| `collections.either/Either` | `Left [left-val]`, `Right [right-val]` | both | `left-val`, `right-val` |
| `testing.runner/Outcome` | `Passed [passed-name]`, `Failed [failed-name why]`, `Panicked [panicked-name msg]` | all five | all five |
| — (`testing.runner/Tally` is already on the minting spelling) | | | |

Two consequences the fixing change-set should decide deliberately:

1. **Silent public-surface widening.** Five stdlib types gain 13 canonical
   accessors and 13 bare aliases with no author action. `collections.list`
   and `seq.lazy` are prelude-adjacent (the prelude re-exports `List Nil
   Cons empty? list` from the former), so the widening lands on modules a
   user is likely to `[*]`-import.
2. **A cross-module bare-alias contest that the in-module rule does not
   catch.** `head` would be minted bare by BOTH `collections.list` and
   `seq.lazy`; `rest` would be minted bare by `seq.lazy` while
   `collections.list` already exports a *function* named `rest` (list.cl:53 —
   deliberately Clojure-aligned, and its header already records the bare
   names as reserved pending FIXME 0402). Neither is an ambiguity *within*
   one module, so the §8.6.5 duplicate-field classification does not fire and
   `stdlib_conformance` (which imports each module's `[*]` individually) would
   not see it either; it surfaces only in a consumer importing both with
   `[*]`. This is an argument for minting the canonical `Type.field` and
   gating the bare alias — or at minimum for a `/qa` cell that `[*]`-imports
   `collections.list` and `seq.lazy` into one module.

There is no within-module collision in any current stdlib module (checked
`testing/runner.cl`, `collections/either.cl`, `collections/list.cl`,
`seq/lazy.cl`: no `defn` shares a name with a would-be new accessor), so the
fix should not regress the conformance gate. Authoring guidance recorded in
`stdlib/CLAUDE.md` §"Known compiler constraints"; assessment in
`stdlib/plan-stdlib.md` §28.3.
