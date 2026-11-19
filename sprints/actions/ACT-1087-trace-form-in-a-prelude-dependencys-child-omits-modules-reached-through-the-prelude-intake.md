---
id: ACT-1087
title: A trace form in a declared child of a prelude dependency records no call into a module it reaches only through the prelude, in any mode
status: open
priority: advisory
from: qa
to: qa
sprint: 124
filed_at: 2026-11-20
refers_to:
  - spec/04-expressions.md §4.12.3
  - spec/08-modules.md §8.8.1
  - design/arch/tracing.md §5.1
  - design/int/int.md §7.6.4
  - src/cache/dependency_record.rs::covered_set
---

## Observation

`qa`, 2026-11-20, `target/debug/cranelisp` built from `f8c55626`, in a
scratch directory. The fixture is the falsifier of
[tracing §5.1](../../design/arch/tracing.md#51-which-modules-a-form-covers),
*Not met in source*, with the library function's parameter type written so
that ACT-1086 does not confound it.

```clojure
;; prelude.cl
(export [primitives [*]])
(export [m [k]])
(export [p [f]])

;; m.cl
(import [prelude []])
(import [primitives [Int]])
(mod c)
(defn k [:Int n] n)

;; m/c.cl — a declared child; its implicit prelude import is active
(import [primitives [Int]])
(defn run [:(Fn [Int] Int) h] (trace (h 1)))

;; p.cl
(import [prelude []])
(import [primitives [Int add-i64]])
(defn f [:Int n] (add-i64 n 1))
```

The entry `app.cl` calls `(m.c/run f)` and returns 40 plus the number of
`p/f` frames in the trace.

| Launch | Required by tracing §5.1's reading of the specification | Observed |
|---|---|---|
| First `--run` (nothing cached) | 41 | 40 |
| Second and third `--run` (`prelude`, `m`, `m.c` and `p` restored) | 41 | 40 |
| `--link` | 41 | 40 |
| `--no-cache --run` | 41 | 40 |

- The scheduler trace of the first launch shows `m.c` typechecked before
  `prelude`, so the fixture reaches the state the design describes.
- **Control.** With `f` defined in the prelude itself and the same child, a
  `prelude/f` frame is recorded in every launch (41). The prelude is
  covered; the modules reached through it are not.

## Classification: a defect, wrong value, low harm

The implicit import has the effect of the written one (spec §8.8.1), so the
form's module imports the prelude, and through it `p` (spec §4.12.3). The
frame is missing. The face is a shorter diagnostic tree; no memory is read
or written that should not be.

**This differs from what tracing §5.1 states.** The design says the first
launch omits the frame and a restored object and `--link` record it. `qa`
observes that no launch records it. The modes agree, so spec §4.12.9 is met
and §4.12.3 is not.

## Attribution: provisional

The covered set is the binary's
(`src/cache/dependency_record.rs::covered_set`, which does not follow an
unpublished prelude's edges). Why the object pass and `--link` also omit `p`
is not observed. A hypothesis: the child's object pass also runs before the
prelude publishes. The backend reads the set it is passed.

## Evidence allocation

`test`, in `tests/trace.rs`, **REPRO-1087**: the fixture above in `--run`,
invoked twice in one directory with the second invocation asserting
`cache hit (.meta valid) for m.c`, and under `--link`. Assert 41. Control:
`f` defined in the prelude, asserting 41. Expected on arrival: the subject
legs RED on 40, the control green. Cite
`// spec: spec/04-expressions.md §4.12.3; spec/08-modules.md §8.8.1` and
`// defect: class=enumeration-miss locus=src/cache/dependency_record.rs::covered_set found=S124 owner=/dev`.

## Disposition

`arch` decided on 2026-11-19 that the residual stands and that a failing
cell is a defect of the binary carried on that test. `qa` retains this
intake. `arch` corrects the *What differs* statement of tracing §5.1
against the table above.

## Completion evidence

REPRO-1087's subject legs fail on 40, then pass with the control unchanged;
or the user rules the specification exception tracing §5.1 records, and the
cell is restated to it.
