---
id: ACT-1087
title: A trace form in a declared child of a prelude dependency records no call into a module it reaches only through the prelude, on the launch that first compiles it
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
`p/f` frames in the trace. Required in every launch: 41 (spec §4.12.3 with
§8.8.1, and §4.12.9).

| Launch | At `f8c55626`, by hand | At `4cef5784`, the committed cells, 20 readings |
|---|---|---|
| First `--run` (nothing cached) | 40 | **40**, 20 of 20 |
| Second `--run` (`m.c` restored) | 40 | 41, 20 of 20 |
| `--link` | 40 | 41, 20 of 20 |
| `--no-cache --run` | 40 | not run |

- **Control.** With `f` defined in the prelude itself and the same child, a
  `prelude/f` frame is recorded in every launch (41), at both trees.
- The 20 readings ran one cell at a time, not under load.

## What was corrected, and what remains

Two faults shared the fixture
([tracing §5.1](../../design/arch/tracing.md#51-which-modules-a-form-covers),
*Not met in source*).

- **Corrected at `fe385164` (C1): the object pass did not wait for the
  prelude.** The child's object was built against the prelude's partial
  table, and restores and `--link` inherited it. The restored and linked
  legs now record the frame.
- **Open: the first batch covers less.** The batch that first compiles the
  child reads the prelude as it stands and follows none of its edges,
  because waiting would close `prelude → parent → child → prelude`. A first
  `--run`, a `--no-cache --run` and a REPL start omit the frame.

## Classification: a defect, wrong value, low harm

The implicit import has the effect of the written one (spec §8.8.1), so the
form's module imports the prelude, and through it `p` (spec §4.12.3). The
first launch omits a frame that later launches record, against spec §4.12.9.
The face is a shorter diagnostic tree; no memory is read or written that
should not be. No shipped stdlib module holds a trace form.

## Attribution: the binary

`src/cache/dependency_record.rs::covered_set`, in the treatment commit
planning asks for: an unpublished prelude is covered as it stands. Module
row `an_unpublished_prelude_is_read_as_it_stands` pins that behaviour, so
the seam is observed. The backend reads the set it is passed.

## Disposition

- **`arch`, 2026-11-19: the residual stands.** Each control costs more than
  the missing frames (tracing §5.1). A failing cell for it is a defect of
  the binary, carried on that test.
- **Open with the user** (tracing §5.1, *Open, with the user*): one sentence
  in spec §4.12.3 would except these modules. Until it is ruled the
  specification makes no exception.

## Evidence allocation

`test` restates REPRO-1087's `--run` subject as two cells
([evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test)):
the first launch, RED on 40, and the restored launch, green. As one cell
the corrected leg cannot be seen to regress, because the cell fails either
way.

## Completion evidence

The first-launch cell passes with the control unchanged; or the user rules
the exception and `qa` restates the cell to it.
