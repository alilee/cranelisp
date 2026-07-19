---
number: 0648
target: /docs
filed_by: /docs
filed_at: 2026-07-18
sprint_filed: 112
refers_to: user/guide/ (no traits/impl page exists) — the settled trait/impl model (spec/07-traits.md §7.1–§7.3, spec/05-definitions.md §5.4)
status: open
---

# User guide has no traits / impl page — the settled S112 trait model has no user-facing home

## Context

`user/guide/` covers functions, constructors, field accessors, bitwise,
platforms, concurrency, parallel collections, and live development — but **there
is no traits/impl page at all**. Traits are listed only as a planned cheatsheet
topic (`user/syntax-cheatsheet-plan.md` rows `traits`/`impl`/`hkt`), not as
authored teaching. Grep of `user/` confirms zero `deftrait`/`impl` code anywhere.

S112 settled the trait/impl model (spec `c9f05b64` + the S112 wave), and none of
it is taught to users:

- **`deftrait` conventional form** — bare-head trait `(deftrait Name (method self …))`
  with `self` as the implementing type; no parenthesized never-applied head.
- **Echo-the-head HKT impl form** — `(impl (Functor f) (Functor Option) …)`: the
  slot-1 head introduces the type constructor variable, the slot-2 pairing head
  echoes the trait applied to the concrete constructor. This is the current form;
  the old bare-head HKT impl was retired.
- **Return-type dispatch** — an impl method selected by its *return* type when no
  argument pins it (spec §7.1.1 param-or-return); the `:Type` annotation is the
  user-facing disambiguator (ties into FIXME 0631's return-poly remedy).
- **Kind matching** — kind-`*` impl targets must be applied to exactly their
  arity; the pairing head must name the slot-1-resolved trait.

## Why this is a FIXME, not a Phase-6b edit

Authoring a traits/impl guide from scratch is a substantial new doc surface, well
beyond an S112 Phase-6b doc-delta pass (which corrected the one place S112 broke —
`user/guide/functions.md` multi-sig inference). This captures the content gap so a
traits guide, when authored, teaches the settled model and cross-links
`spec/07-traits.md §7.1–§7.3` + `spec/05-definitions.md §5.4`. No user doc
currently *contradicts* the trait model — this is a coverage gap, not an
inaccuracy (the staleness risk is nil because no trait content exists to drift).

## The ask (future /docs input)

When authoring `user/guide/traits.md` (or equivalent): teach `deftrait` + `self`,
the echo-the-head HKT impl form (with a worked `Functor`/`Option` example verified
against the binary), return-type dispatch and its `:Type` remedy, and the kind /
pairing-head rules. Verify every code example compiles on the current binary.
Coordinate with FIXME 0649 (the errors-catalog entries for the trait/impl
diagnostics) and FIXME 0631 (the return-poly `:Type` remedy).
