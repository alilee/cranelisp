---
number: 0841
target: /qa
filed_by: /testing
filed_at: 2026-07-21
sprint_filed: 115
refers_to: spec/09-macros.md §9.10; tests/spec_11_stdlib.rs::macro_when_true,
  ::macro_when_false_none, ::macro_when_option_body_nests_the_wrap;
  stdlib/control.cl
status: open
---

# `when`/`unless` have no spec home, and §9.10's `[Tested]` cites a test for a macro it does not document

## What was found

Resolving the S115 W9 stale-record REDs required deciding whether
`stdlib/control.cl`'s `when` is *supposed* to wrap its body in `Some`. The
answer had to be reconstructed from the macro's own docstring, because the
spec does not say:

- **`spec/09-macros.md` §9.5** — the section the three `when` tests cited before
  this change — is **"Bare-Symbol Expansion"** (zero-argument macros expanding
  as bare symbols). It has nothing to do with `when`. Three tests carried a
  citation to a section that does not describe them.
- **§9.4.3** contains a `when` — but it is a *pedagogical* macro-writing
  example expanding to `(if ~cond ~body 0)`, deliberately unlike the stdlib
  macro. `spec/02-grammar.md` §2.7 similarly shows an illustrative `unless`
  expanding to `(if ~cond 0 ~body)`. Both are docstring/grammar illustrations,
  not the library contract.
- **§9.10 "Example Prelude Macros"** enumerates `const`, `def`, `list`, `do`,
  `bind!`, `->`, `->>`, `cond`, `case`, `vec`, `str` — **`when`/`unless` are
  absent** — yet its `[Tested …]` annotation cites
  `tests/spec_11_stdlib::macro_when_true`. The coverage claim points at a
  requirement the section does not state.
- **`spec/11-stdlib.md`** is explicitly non-normative and says nothing about
  control macros either.

So the semantics that three e2e tests now pin exist only in
`stdlib/control.cl`'s docstring ("Conditional returning (Some body) when test
holds, else None") plus `stdlib/plan-stdlib.md` §3.2.

## Why it matters

This is the shape the standing "a `[Tested]` row is asserting what the probe
contradicts" concern (cf. FIXME 0802) takes on the *citation* axis rather than
the behaviour axis: a green annotation, a green test, and no requirement
anywhere between them. The S115 6b `when` fix was correct, but nothing in
`spec/` could have adjudicated it — the decision rested on a docstring.

## Ask (`/qa` to adjudicate and route)

1. Decide whether `when`/`unless` warrant a §9.10 subsection (they are prelude
   macros of exactly the same standing as `cond`/`case`, which have one) — if
   so, file the prose request to `/spec`; the `Some`-wrapping contract is the
   settled behaviour to scribe.
2. Correct §9.10's `[Tested …]` citation list either way (the annotation band
   is `/qa`'s, no FIXME cycle needed): today it cites `macro_when_true` for a
   macro it does not document.
3. `/testing` has retargeted the three tests' `// spec:` comments from the
   wrong §9.5 to §9.10 as the nearest home, with an inline note pointing here.
   Retarget again once (1) is settled.

## Not in scope here

The behaviour itself is settled and green — `macro_when_true`,
`macro_when_false_none` and `macro_when_option_body_nests_the_wrap` pin the
non-Option body, the `None` branch, and the unconditional wrap respectively.
This FIXME is purely about where the requirement lives and what cites it.
