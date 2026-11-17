---
id: ACT-1074
title: An implementation body's call to a multi-signature function of its own cluster is refused as no overloaded function
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-18
refers_to:
  - spec/05-definitions.md §5.1.2
  - spec/05-definitions.md §5.13.1
  - crates/cranelisp-typecheck/src/traits/impl_check.rs
  - tests/plan/s124-evidence-delta.md
---

## Observation

`qa`, on `target/debug/cranelisp` built from `24c42430`, 2026-11-18. No
prelude; one file under `--run`.

```clojure
(deftype (Opt a) Nope (Yep [:a v]))
(deftrait Size (size [self] Int))
(defn h3 ([x] 1) ([x k] 2))
(impl Size (Opt a) (defn size [o] (match o [Nope 0 (Yep x) (h3 x)])))
(defn main [] (Pure (add-i64 40 (size (Yep 3)))))   ; required: 41
```

| Leg | Observed |
|---|---|
| Subject | refused: `impl of trait Size for p/Opt: method size does not conform: no overloaded function: h3` |
| The same from `(impl Size Bool …)` with a concrete argument | the same refusal |
| Control: the call from a free function, `(defn g [o] (match o [Nope 0 (Yep x) (h3 x)]))` | 41 |
| Control: at the REPL, `h3` entered in an earlier turn than the `impl` | 1 for `(size (Yep 3))` |
| Control: a single-signature helper in the subject's place | 43 for its program |

## Classification: a defect (`wrong-reject`)

A file is one cluster and a body may use any definition of its cluster (spec
§5.13.1). Predates S124 W3: the release build of 00:11 on 2026-11-18 refuses
the subject with the same message.

## Attribution: provisional

Owner typecheck. The multi-signature function's overload set is not
available when an implementation body of the same cluster is checked; the
free-function control shows it is available to a definition. Not observed at
a seam. Related: ACT-0981 and ACT-1068 are other consumers that omit
multi-signature definitions.

## Evidence allocation

`test`, in `tests/spec_05_definitions.rs`, citing
`// spec: spec/05-definitions.md §5.13.1` and
`// defect: class=wrong-reject locus=crates/cranelisp-typecheck/src/traits/impl_check.rs found=S124 owner=/dev`:
the subject in `--run`, `--link` and one REPL `begin`, in both declaration
orders, with the free-function and earlier-turn controls.

## Completion evidence

The subject fails on the refusal before the correction and yields 41 after
it in every mode; the controls pass throughout.
