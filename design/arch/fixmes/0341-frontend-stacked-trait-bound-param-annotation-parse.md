---
number: 0341
target: /frontend
filed_by: /stdlib
filed_at: 2026-06-13
sprint_filed: 81
refers_to: stdlib/testing/assertions.cl (assert-eq, ~line 16), spec/07-traits.md (trait-bound param annotations), spec/02-grammar.md (param list grammar)
status: open
---

# Stacked trait-bound param annotations `[:Eq :Display a]` fail to parse — `duplicate parameter name ':Display'`

## Issue (S81 W-I-5 /stdlib finding)

A parameter with TWO stacked trait-bound annotations parses incorrectly:

```clojure
(defn f [:Eq :Display a :Eq :Display b] a)
;; parse error: duplicate parameter name ':Display'
```

The parser reads `:Eq :Display a` and treats `:Display` as a SECOND parameter
name rather than a second trait bound on `a`. With two such params (`a` and `b`)
the two `:Display` tokens collide and the parser reports a duplicate parameter.

This blocks `stdlib/testing/assertions.cl::assert-eq`, whose signature is
`[:Eq :Display a :Eq :Display b]` (a value that must be both comparable and
displayable). As a result `testing.assertions` does not parse at all on the
current toolchain, and stdlib `(mod test)` blocks cannot import its
`assert-eq`/`assert-true`/`assert-false` helpers — the S81 runner self-tests had
to use inline `(Option String)` checkers instead.

**Pre-existing** (predates S81; not a regression). A single trait bound
(`[:Eq a]`) parses fine; the defect is specifically TWO-OR-MORE stacked bounds
on one parameter.

## Proposed resolution

`/qa` authors a minimal failing repro (no stdlib): `(defn f [:Eq :Display a] a)`
with the two trait names imported, plus the two-param collision case. `// spec:`
→ spec/07-traits.md (trait-bound param annotations) + spec/02-grammar.md (param
list). `/frontend` fixes the param-list parser so a run of `:Trait` annotations
preceding a binder name all attach to that binder as bounds, rather than the last
being read as a separate parameter.

## Context

S81 W-I-5 /stdlib. The runner's `(mod test)` self-tests would normally import
`testing.assertions`; this defect (plus a separate `super`-import defect — FIXME
0342) forced the self-test validation onto the REPL demo path instead.
