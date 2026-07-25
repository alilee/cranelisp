# `def` function-value application options

**Status:** options for user decision; no option selected
**Scope:** stdlib `def` API only (FIXME 0800 face 3)

## Problem

`def` is a stdlib macro, not a core special form. It currently expands a
source binding such as:

```clojure
(def k (mk 10))
```

into a private implementation shape consisting of a zero-argument `k-def`
function and a zero-argument macro `k` that expands bare `k` to `(k-def)`.
Consequently, bare `k` evaluates to the stored closure, but `(k 1 2)` is parsed
as a two-argument call of the macro and fails its zero-argument clause before
the closure can be called.

This is independent of FIXME 0863. That compiler transaction will make echo,
`/info`, and `/sig` present the public value truthfully; it does not decide
what applications of a stdlib `def` mean.

## Option A — retain value-only `def`

Keep `def` as zero-argument substitution. Function values can be retrieved
bare and called only after an ordinary local binding:

```clojure
(def k (mk 10))
(defn use-k []
  (let [f k]
    (f 1 2)))
```

Properties:

- ordinary values preserve today's expansion and evaluation count;
- no macro forwarding or arity synthesis is needed;
- closures and currying work after a local binding, not directly at top level;
- direct `(k 1 2)` should receive a deliberate diagnostic explaining the
  value-only contract, rather than today's misleading macro-clause error;
- fully compatible with existing successful programs, but retains the
  ergonomic gap which surfaced the issue.

## Option B — make `def` forward application

Give the generated public macro a variadic application clause in addition to
its zero-argument value clause. Conceptually, `(k a b)` expands to
`((k-def) a b)`.

Properties:

- ordinary bare values retain the current spelling;
- stored closures become directly callable and participate in ordinary
  currying after expansion;
- `(k args...)` evaluates `k-def` once per application, then calls the result;
- non-function values used in application position reach the ordinary
  typecheck diagnostic rather than a macro-arity diagnostic;
- the macro must forward syntax without capturing names or changing argument
  evaluation order;
- compatibility risk is low for successful calls, but programs that relied on
  the current macro-arity failure receive a different, more semantic error.

Required proof includes zero, one, and multiple arguments; closure capture;
partial application; argument side effects/evaluation count; and non-function
application diagnostics.

## Option C — add a distinct callable-value binding macro

Keep `def` value-only and add a separately named stdlib macro whose contract
includes application forwarding.

Properties:

- preserves every aspect of existing `def`;
- makes callable intent explicit and allows focused documentation;
- duplicates top-level binding vocabulary and forces users to predict whether
  a value will later be called;
- changing a binding between data and function may require changing its
  declaration form;
- the name must be checked against the curated prelude and future naming
  reservations before adoption.

This option still needs the forwarding and evaluation-count proofs from
Option B, and adds migration, naming, search, and prelude-curation work.

## Comparison

| Concern | A: value-only | B: forwarding `def` | C: distinct macro |
|---|---|---|---|
| Ordinary values | unchanged | unchanged when bare | unchanged |
| Direct closure call | no | yes | yes, with new form |
| Currying | after local bind | direct | direct, with new form |
| Evaluation count | current | thunk once per application | thunk once per application |
| Bad-call diagnostic | needs explicit value-only error | ordinary type error | depends on chosen form |
| Compatibility | highest | high | highest for `def`, new vocabulary |
| API complexity | lowest | one richer form | two binding forms |

## Decision gate

The user should select the intended stdlib contract before implementation.
Whichever option is selected must:

1. remain a stdlib macro design rather than introducing a core `def` form;
2. preserve exactly-once evaluation of the stored expression per present
   `def` semantics;
3. specify closure, currying, and non-function diagnostics;
4. gain stdlib self-tests and, if compiler behavior fails the selected
   contract, a narrow failing-not-ignored `/testing` repro;
5. stay separate from FIXME 0863's presentation transaction.

## Next skills

- `/stdlib` — implement and self-test only the user-selected option.
- `/repl` — describe the selected call and diagnostic behavior.
- `/testing` — add compiler coverage only if the selected stdlib expansion
  exposes a language defect.
- `/dev` — retain FIXME 0863 as the independent presentation transaction.
