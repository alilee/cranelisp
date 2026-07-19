---
number: 0649
target: /docs
filed_by: /docs
filed_at: 2026-07-18
sprint_filed: 112
refers_to: user/errors/ (not yet authored) — the S112 trait/impl declaration diagnostics; sibling to FIXME 0631
status: open
---

# The errors catalogue should document the S112 trait/impl fix-naming diagnostics

## Context

`user/errors/` is listed "not yet authored" in `user/CLAUDE.md`. S112 added a
family of fix-naming diagnostics on the trait/impl declaration path (spec
`spec/07-traits.md §7.1–§7.3`, `spec/05-definitions.md §5.1.2/§5.4`), none of
which has a user-facing home:

- **Never-applied parenthesized head** — `(deftrait (Functor f) …)` where the head
  is never applied is rejected at declaration with a fix-naming message pointing at
  the bare-head + `self` form.
- **Echo mismatch** — an HKT impl whose slot-2 spelling does not echo the head.
- **Pairing-head mismatch** — the slot-2 pairing head does not name the
  slot-1-resolved trait (must resolve to the same trait identity).
- **Over-/under-applied kind-`*` target** — an impl target applied to the wrong
  arity (e.g. `(impl Disp (Option Int Int))`).
- **Definition-site same-arity dispatch ambiguity** — two same-arity `defn`
  clauses whose *written* signatures could both match (§5.1.2, judged on written
  signatures); remedy = annotate a clause so the written signatures no longer
  overlap. (`user/guide/functions.md` teaches this rule as of S112; the errors
  catalogue should carry the message + remedy.)

## Why this is a FIXME, not a Phase-6b edit

No `user/errors/` surface exists to write these into, and manufacturing the
errors catalogue is out of scope for the S112 doc-delta pass. This captures the
content items so the catalogue, when authored, includes them with the confirmed
message text (verify against the current binary) and the fix each names.

## The ask (future /docs input)

When authoring `user/errors/`, add entries for the diagnostics above, each showing
the message and the remedy it names, cross-linking the relevant spec section. This
is a sibling to FIXME 0631 (return-poly ambiguity `:Type` remedy) and FIXME 0648
(the traits/impl guide) — the three should land together when the trait/impl
user-facing surface is built.
