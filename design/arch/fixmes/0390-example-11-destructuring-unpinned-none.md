---
number: 0390
target: /examples
filed_by: /dev
filed_at: 2026-06-16
sprint_filed: 84
refers_to: examples/11-destructuring.cl (test-count-some, ~line 85), spec/03-types.md §3.11.1, tests/examples.rs::every_example_runs_with_documented_exit
status: open
---

# `examples/11-destructuring.cl` `test-count-some` rejects under tightened §3.11.1 — annotate the bare `None`

## Issue

`examples/11-destructuring.cl` no longer compiles under the tightened §3.11.1
(S84 FIXME 0386 — full-concreteness verdict). The offending form (~line 85):

```clojure
(defn test-count-some []
  (count-some (Some 1) None (Some 3)))
```

The bare `None` argument is `(Option a)` with `a` unpinned at a codegen-reaching
position (an argument evaluated to a runtime value), which the tightened §3.11.1
now rejects:

```
type error at …: ambiguous type; add an annotation to pin the type of the
polymorphic value bound in `test-count-some`
```

This breaks `tests/examples.rs::every_example_runs_with_documented_exit` (1 of 28
examples now exits 1 instead of the documented code). GREEN at baseline (159f544),
RED after 0386 — the example encoded the OLD lenient behaviour.

## Proposed resolution

Annotate the bare `None` concrete, per the spec's directed remedy (§3.11.1 worked
example `(is-some :(Option Int) None)`):

```clojure
(count-some (Some 1) :(Option Int) None (Some 3))
```

(or whatever element type `count-some` expects). `/examples` owns
`examples/11-destructuring.cl`; this is a one-line annotation fix.

## Operational implication / Context

- This is the same tightening-driven class as FIXME 0388 (the /qa test realignment):
  a previously-lenient unpinned-`None` value that the full-concreteness verdict now
  correctly rejects. It is a correct rejection, not an over-fire.
- The directed remedy `:(Option Int) None` resolves in call-argument position (verified
  working). NOTE: if any example needs the annotation on a `match` SCRUTINEE, that
  position has a separate pre-existing parse bug (FIXME 0389) — call-argument and
  bare-value positions are unaffected.
