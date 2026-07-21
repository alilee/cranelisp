---
number: 0839
target: /dev (int — REPL introspection rendering)
filed_by: /docs
filed_at: 2026-07-21
sprint_filed: 115
refers_to: repl/spec.md §18.9 ("`/info <Trait>` and `/info <Type>` MUST list
  exactly one impl entry per (trait, target-type) pair")
status: open
---

# `/info <Type>` lists no impls at all — only the trait side of §18.9's introspection MUST is implemented

## Severity

Usability finding (`/info` on a type is silent about what it implements; the
trait-side half of the same MUST works correctly)

## Issue

`repl/spec.md` §18.9 requires **both** routes to report the impl set, and to
report exactly one entry per (trait, target-type) pair however many `impl` forms
were entered. The trait side does exactly that. The type side prints no impl
section at all.

Verified against `target/debug/cranelisp` (built 2026-07-21 11:22), scratch dir,
`CRANELISP_LIB=…/stdlib`:

```
user> (import [primitives [add-i64 mul-i64]])
user> (deftype Box [:Int w :Int h])
user> (deftrait Sizeable (size [x] Int) (tag [x] Int))
user> (impl Sizeable Box (defn size [b] (match b [(Box w h) (mul-i64 w h)])) (defn tag [b] 7))
impl user/Sizeable for user/Box
user> (impl Sizeable Box (defn size [b] (match b [(Box w h) (add-i64 w h)])) (defn tag [b] 7))
impl user/Sizeable for user/Box
```

`/info Sizeable` — correct, and correctly de-duplicated after two `impl` forms:

```
:user/Sizeable ; deftrait
; defn:
;  size tag
; impl:
;  Box
  (deftrait Sizeable
    (size [x] Int)
    (tag [x] Int))
```

`/info Box` — no `; impl:` section, in the same session:

```
:(Fn [primitives/Int primitives/Int] user/Box) user/Box ; deftype
  (deftype Box [:Int w :Int h])
  400 bytes
```

## Why it matters to a newcomer

"What can I do with this value?" is the question a user brings to `/info <Type>`,
and traits are most of the answer. The information is demonstrably present — the
trait-side listing is built from it — so this is a rendering gap on the type
branch, not missing data. It also breaks the symmetry §18.9 relies on: a user who
learns the impl set from `/info Sizeable` has to already know which traits to ask
about.

## Impact on `user/`

`user/guide/live-development.md` §"Redefining an impl" (S115 Phase 6b) teaches
the de-duplication guarantee using `/info <Trait>` only, and says nothing about
`/info <Type>`, precisely because the latter does not hold today. When this
lands, `/docs` adds the type-side transcript alongside.

## Ask

Render the impl set on the `/info <Type>` branch too, with the same one-entry-per-pair
de-duplication the trait branch already applies.
