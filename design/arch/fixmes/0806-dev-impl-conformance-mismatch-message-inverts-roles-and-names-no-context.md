---
number: 0806
target: /dev (typecheck)
filed_by: /docs
filed_at: 2026-07-21
sprint_filed: 115
refers_to: spec/05-definitions.md §5.4 (impl conformance) / §5.4.5 [S115]
  (re-impl is rejected at the conformance seam); emitted message
  "type mismatch: expected <T>, got <U>"
status: open
---

# Impl conformance failure reports a bare `type mismatch` with the roles inverted and no trait/method context

## Severity

Usability finding (correct rejection, unhelpful diagnostic) — user-proxy find,
`/docs` Phase-6a probes 2026-07-21

## Issue

When an impl method's body does not conform to the trait's declared signature,
the rejection is correct but the message is a bare unification report:

```
user> (deftrait D2 (dsc [self] String))
user> (deftype Cow [:Int a])
user> (impl D2 Cow (defn dsc [self] 42))
Error: type error at 13..33: type mismatch: expected primitives/Int, got primitives/String
```

Two problems, both hit a newcomer immediately:

1. **The roles read inverted.** The trait declares the return type `String`;
   the body returns `42`, an `Int`. The user's model is "the signature is the
   expectation, the body is what I actually wrote", so the message they expect
   is *expected String, got Int*. The emitted text says the opposite, because
   the unifier's argument order happens to put the body's type first. A reader
   who trusts the message goes looking for the wrong bug.

2. **No conformance context.** The message names neither the trait (`D2`), the
   method (`dsc`), nor the fact that this is an *impl-conformance* failure
   rather than an ordinary expression-level mismatch. The span covers the whole
   `defn`, so there is nothing else to orient from.

The same message is what a **re-impl** hits under the §5.4.5 [S115] hot-reload
rule, where the reject is load-bearing: a type-changing re-`impl` must be
rejected with the prior impl intact (verified live — it is, and dispatch keeps
using the previous bodies). That behaviour is exactly right; only the message
lets it down at the moment the user most needs to understand what happened.

## Suggested resolution

Report conformance failures in trait terms and in the declaration's direction,
e.g.

```
impl of trait `D2` for `Cow`: method `dsc` does not conform — the trait declares
return type `primitives/String`, but the body has type `primitives/Int`
```

with the span on the offending method rather than the whole form. Whatever
wording lands, the *direction* (declared vs supplied) is the part that must be
right.

`/docs` will teach impl redefinition in `user/guide/live-development.md` in
S115 Phase 6b and will quote whatever message is live at that point; a
correction to the emitted text is welcome any time — the catalogue carries the
standing "exact wording can shift; the remedy is the stable part" caveat.
