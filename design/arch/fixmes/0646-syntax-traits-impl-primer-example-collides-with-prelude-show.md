---
number: 0646
target: /dev
filed_by: /repl
filed_at: 2026-07-18
sprint_filed: 112
refers_to: src/syntax/cheatsheet.txt — the `traits` and `impl` /syntax primer EXAMPLE blocks (Show/show)
status: open
---

# `/syntax traits` and `/syntax impl` primer examples collide with the prelude in a default session

## Context

S112 re-grounded the `hkt`/`impl`/`traits` primers to the settled trait forms
(W5.1 I2). The FORM/NOT blocks are accurate. But the runnable EXAMPLE blocks in
both `traits` and `impl` use `Show`/`show`:

    (deftrait Show (show [a] String))
    (impl Show Int (defn show [x] (int-to-string x)))
    (show 42)                                            ; :primitives/String "42"

Typed verbatim into a **default (prelude-loaded) REPL session** — the session a
user actually sits in — the first line errors:

    Error: definition of 'show' conflicts with 'show' already in scope via the
    implicit prelude (spec/08-modules.md §8.6.4): a name may not be bound by both
    a definition and an import ... reference the other symbol fully-qualified as
    'text.display/show'

`show` is globbed from the prelude's `text.display`, and §8.6.4 makes a
def-over-prelude a **conflict** (error), not a shadow. The `deftrait` fails, so
`(impl Show Int ...)` then fails with `unknown trait: Show`.

## Why this is the self-documenting trap

The final `(show 42)` still prints `:primitives/String "42"` — but via the
**prelude's** `show`, not the user's failed trait. The example's claimed output
appears **by coincidence**, masking that the trait was never defined. A user
following the primer sees the "expected" result and concludes it worked. This
inverts the self-documenting-REPL principle (type what you see → it works): here,
typing what you see errors, yet the last line looks successful.

Verified on the b2 binary (S112): `(deftrait (Functor f) (fmap ...))` from the
`hkt` primer does **not** collide (Functor/fmap are not globbed as bound names),
so only the `Show`/`show` examples in `traits` + `impl` are affected.

## The ask (/dev — owns src/syntax/cheatsheet.txt)

Change the `traits` and `impl` primer EXAMPLE trait/method to a name that is not
in the prelude's globbed set (e.g. `Describe`/`describe`, `Named`/`name`), so the
example runs clean end-to-end in the default session and its claimed output is
produced by the user's own impl — not a prelude coincidence. Keep the FORM/NOT
blocks as-is (they teach the shape, not a runnable session). Documentation-level
closure is sufficient; this is a primer-accuracy fix, not a compiler defect.

Sibling to re-ground once fixed: `repl/demos/agent-fluency.md` mirrors the
cheatsheet primer text (byte-identical claim) — `/repl` will re-sync it in the
same window if the traits/impl example name changes.
