---
id: ACT-1088
title: A function taken as a value in the unit that defines it is called past its slot, so a trace omits it and a redefinition does not reach it
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-20
refers_to:
  - spec/04-expressions.md §4.12.3
  - spec/04-expressions.md §4.12.9
  - repl/spec/18-redefinition.md §18
  - design/arch/tracing.md §3.5
  - design/backend/compile-to-module.md §12.2
  - crates/cranelisp-backend/src/compiler/control_flow/fn_as_value.rs::emit_wrapper_call
---

## Observation

`qa`, 2026-11-20, `target/debug/cranelisp` built from `4cef5784`, in scratch
directories, with `CRANELISP_NO_LENIENT=1`. The fixture is the falsifier of
[tracing §3.5](../../design/arch/tracing.md#35-got-copy-swap-and-completeness-by-construction).

**Trace face.** `app.cl` holds a frame counter and:

```clojure
(defn af [:Int n] n)
(defn hof [:(Fn [Int] Int) h] (h 1))
(defn main [] (Pure (match (trace (hof af)) [(TraceCall n p r c ns)
  (add-i64 40 (add-i64 (mul-i64 10 (count-named "app/hof" c)) (count-named "app/af" c)))])))
```

| Fixture | `--run` cold | `--run` warm | `--link` | REPL, file loaded, `(main)` | REPL, one turn per form |
|---|---|---|---|---|---|
| Subject: `af` defined in `app.cl` | 50 | 50 | 50 | 50 | 51 |
| Control: `af` defined in `x.cl`, imported | 51 | not run | 51 | not run | not run |
| Control: `(trace (hof2 1))`, where `hof2` calls `af` directly | 51 | not run | not run | not run | not run |
| Twin: `(trace (hof (add2 5)))`, `add2` of two parameters in `app.cl` | 50 | not run | not run | not run | not run |
| Twin's control: `add2` in `x.cl` | 51 | not run | not run | not run | not run |

The `hof` frame is recorded in every reading; the `af` frame is missing.

**Redefinition face.** `app.cl` holds `af`, `hof`, `(defn usev [] (hof af))`
and `(defn used [] (af 1))`. The REPL loads the file and is given `(usev)`,
`(used)`, `(defn af [:Int n] (add-i64 n 100))`, `(usev)`, `(used)`.

| Call | Before the redefinition | After it |
|---|---|---|
| `(usev)`, through the value | 1 | **1** |
| `(used)`, direct | 1 | 101 |

## Classification: a defect, wrong value

- Spec §4.12.3 requires a form to record calls into its own module, and
  §4.12.9 requires the same trace in every mode. The subject omits a frame,
  and the REPL records it when the forms arrive one turn at a time.
- REPL §18 requires that calls begun after a successful replacement see the
  new unit. `(usev)` reaches the replaced body.
- No memory is read or written that should not be.

It predates S124: the direct call is the wrapper's oldest arm. It is not a
regression.

## Attribution: the backend

- **At the seam.** `emit_wrapper_call` emits a direct `call` to the target's
  `FuncId` when the target is in the unit's `func_ids`, before any slot
  read. `design`(backend) records the same site
  ([compile-to-module §12.2](../../design/backend/compile-to-module.md#122-every-call-to-a-slotted-function-goes-through-its-slot)).
- **Control.** The two controls differ from their subjects only in which
  unit declares the function, and record the frame.
- **The partial-application twin** is read as the same site: the curry
  wrapper's dispatch arm calls `emit_wrapper_call`. Read in source, not
  observed apart.
- **Refuted if** a wrapper over a same-unit target loads the target's slot
  and the frame is still missing.

This also explains the observation ACT-1086 left open: `(run af)` in `main`
recorded no `app/af` frame in the batch modes and one at the prompt.

## Why coverage missed it

Every cell that takes a function value and then traces it or redefines it
takes the value in a later unit than the definition, or from another
module. `repl_redefinition::redefine_body_only_stale_closure_late_binds_new_body`
uses a lambda that calls the function directly. The axis "value taken in the
defining unit, or in a later one" was not enumerated.

`trace::s124_1086_entry_function_control_*` assert that a library form
records no frame for the entry's `af`. Until this defect is corrected they
cannot fail, because `af` is called past its slot.

## Evidence allocation

**REPRO-1088**, allocated to `test` in the
[evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-returned-to-test).
`dev`(backend) owes the module row of compile-to-module §12.2.

## Completion evidence

REPRO-1088's subject legs fail on 50 and on the stale `(usev)`, then pass
with the controls unchanged. `qa` restores the spec §4.12.3 and REPL §18.1
bands that name this action.
