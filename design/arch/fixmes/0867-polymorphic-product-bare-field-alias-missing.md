---
number: 0867
target: /testing
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
