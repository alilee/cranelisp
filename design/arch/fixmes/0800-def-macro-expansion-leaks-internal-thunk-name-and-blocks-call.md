---
number: 0800
target: /stdlib
filed_by: /repl
filed_at: 2026-07-21
sprint_filed: 115
refers_to: stdlib/defs.cl:27-34 (the `def` macro expansion); stdlib/plan-stdlib.md
  §6.1 (the three options and the obligations any choice carries)
status: deferred
deferred_at: 2026-11-27
deferred_reason: user decision at the S125 Phase 6a → 6b checkpoint; the API choice for a function-valued `def` stays open
deferred_trigger: the user selects option A, B or C in stdlib/plan-stdlib.md §6.1
target_sprint: TBD
---

# `def`: a function-valued binding cannot be applied directly

## Issue

`def` is a stdlib macro (`stdlib/defs.cl`). `(def k v)` expands to a
zero-argument function `k-def` and a zero-argument macro `k` that expands to
`(k-def)`. Bare `k` yields the stored value, but applying `k` reaches the
macro's arity check. Re-probed 2026-11-27 (debug build,
`CRANELISP_LIB` at the in-tree stdlib, `--no-cache`):

```
user> (defn mk [n] (fn [a b] (+ n (+ a b))))
user> (def k (mk 10))
user> k
:(Fn [primitives/Int primitives/Int] primitives/Int) #closure
user> (k 1 2)
Error: macro error at 0..7: macro `user/k` returned malformed sexp at 0..7: no
matching clause for macro `user/k` with 2 argument(s); clauses accept 0 argument(s)
```

The compiler's advice for applying an expression's result, "bind this
expression to a variable first", leads a user to `def`, which then gives this
error. Binding the value locally works: `(let [g (mk 10)] ((g 1) 2))` gives 13.

This is not a defect: `def` is specified as a zero-argument macro (spec §5.7,
§9.10). It is a stdlib API choice, and the error is a usability finding.

## Resolution

The user chooses among the options in `stdlib/plan-stdlib.md` §6.1: A
(value-only, with a deliberate diagnostic), B (a forwarding `def`) or C (a
separate callable binding macro). `dev` on `stdlib/` then implements the choice
with self-tests, and `qa` allocates its behavioural evidence. The plan section
lists the obligations any option carries.

## Narrowed

The original filing had two further faces, both verified on 2026-11-27 and no
longer carried. The REPL lists both definitions a `def` emits, `n-def` and
then `n`. `/info n` and `/sig n` describe the `defmacro` binding, which is
correct.
