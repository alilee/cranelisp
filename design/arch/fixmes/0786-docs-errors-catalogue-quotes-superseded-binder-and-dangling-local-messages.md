---
number: 0786
target: /docs
filed_by: /dev
filed_at: 2026-07-21
sprint_filed: 115
refers_to: user/errors/trait-impl-diagnostics.md:23,30,94 (+ the §"Qualified name in a binder position" prose)
status: open
---

# Errors catalogue quotes the pre-S115 binder-reject and dangling-local messages verbatim

## Severity
Minor (documentation drift — the catalogue's verbatim quotes no longer match emitted output)

## Issue

S115 W5b actioned FIXMEs 0710 and 0711 — both filed BY `/docs` asking for exactly
these message changes — so the two messages the catalogue quotes **verbatim** have
changed. The catalogue is `/docs`-owned; `/dev` does not edit it.

**1. Binder reject (0711, position-neutral wording).** The shared helper's message
dropped "definition head", which was wrong at `let`/`match`/param positions. Now
emitted (both the `/` and the new `.` arm):

```
'user/foo' is a qualified name, but a binder must be a bare (unqualified) name — write 'foo' (a binder introduces a name into the current module or scope; use an import or qualified reference to reach another module)
```

Catalogue lines 23 and 30 still quote the old "a definition head is a binder and
must be a bare (unqualified) name — write 'foo' (a definition binds into the
current module; …)".

**2. Dangling local half (0710, message parity).** `read_local_name`'s terse
reject was raised to the rich empty-module-half sibling's shape:

```
`/` here has no local name after it — a qualified name needs a non-empty local (`mod/name`); drop the trailing `/` to write a bare name
```

Catalogue line 94 still quotes `expected local name after '/'`.

## Also new — a `.` (dotted) binder column the catalogue does not yet teach

The S115 widening (spec §5 `[S115]`, user ruling 2026-07-21) makes a **dotted**
spelling in ANY binder position a located reject on the same footing as a
qualified one, with its own message:

```
'a.b' is a dotted name, but a binder must be a bare (unqualified) name — write 'b' ('.' is reserved for type/trait qualification)
```

It fires at every binder position the `/` rule covers: def-form heads, variant-
constructor names, field names, deftype type parameters, deftrait method-signature
names and con_vars, defmacro heads, and the value-level `let`/param/`match`
binders. **Reference** positions keep their dots and stay legal — the `Maybe.Some`
ctor-pattern head (§6.2.1), `Type.field` accessors, dotted type/trait references
(§8.5), and dotted module paths in imports. The catalogue's §"Qualified name in a
binder position" is the natural home for the twin, and the binder/reference line
is the thing worth teaching (it is what makes the two cases different).

## Suggested resolution

Re-quote the two messages from live output and add the dotted twin alongside the
qualified one, keeping the catalogue's own "exact wording can shift; the remedy is
the stable part" caveat. No compiler change is being requested — this is purely
the documentation half of 0710/0711, which are now closed on the frontend side.
