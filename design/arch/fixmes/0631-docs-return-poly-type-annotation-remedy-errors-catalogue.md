---
number: 0631
target: /docs
filed_by: /docs
filed_at: 2026-07-16
sprint_filed: 110
refers_to: user/errors/ (not yet authored) — the §3.11 return-type-polymorphic ambiguity message + the `:Type`-annotation remedy
status: open
---

# The errors catalogue should document the return-poly ambiguity + `:Type` remedy

## Context

S110 lifted error quality for unresolved return-type-polymorphic dispatch
(R16/R17): a codegen-reaching call whose return type no argument, annotation, or
context pins now surfaces a clean spec-§3.11 message instead of an opaque backend
error. The exact as-built text (verified in `src/exe.rs::unresolved_dispatch_error`,
line 549) is:

    ambiguous type: the return-type-polymorphic call to `<name>` selects no impl
    — no argument, annotation, or context pins its return type; add a `:Type`
    annotation to disambiguate (spec §3.11)

The user-facing remedy is the `:Type` annotation in value position (spec §3.3.3
MUST (d), §3.5.5 "Concrete-type ascription / context resolves return-type-
polymorphic dispatch"). This is a distinct ambiguity family from the two already
documented in `user/guide/`:

- `constructors.md` / `field-accessors.md` — ambiguous *bare name* (two members
  share a name); remedy = qualify.
- `functions.md` — an *unpinned multi-arity parameter* (each `defn` clause is
  checked independently); remedy = annotate the clause's parameter.

Return-type-polymorphic dispatch ambiguity has **no home** in `user/` today.

## Why this is a FIXME, not an S110 6b edit

There is currently no natural doc surface for it: `user/errors/` is listed
"not yet authored" in `user/CLAUDE.md`, and there is no type-annotations guide
page. Manufacturing a new doc surface is out of scope for S110's scoped Phase-6
(doc-observable-delta accuracy only). This captures the content item so the
errors catalogue — when authored — includes the return-poly entry with the
confirmed message text and the `:Type` remedy. No user doc currently contradicts
this behaviour; this is a coverage gap, not an inaccuracy.

## The ask (S111 Phase-1 input for /docs)

When authoring `user/errors/` (or a type-annotations guide page), add an entry
for the §3.11 return-type-polymorphic ambiguity: show the message, explain that
the return type is unpinned, and give the `:Type value` remedy — cross-linking
`spec/03-types.md` §3.11 and §3.5.5. A one-line pointer from `functions.md`'s
existing ambiguity discussion (which already teaches the `:Type` remedy pattern
for a sibling case) may be worth adding at the same time.
