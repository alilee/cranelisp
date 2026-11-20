---
id: ACT-1096
title: A declared child of a library module is loaded from a same-path file earlier on the search path, not from beside its declaring file
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-20
refers_to:
  - spec/08-modules.md §8.2.5
  - spec/08-modules.md §8.1.1
  - spec/08-modules.md §8.11.2
  - src/process_form/dependency.rs::enrol_declared_submodule
  - src/pipeline.rs::resolve_module_file
---

## Origin

`dev`(exemplar), by hand probes during the S124 Phase 6a assessment. `qa`
took it in on 2026-11-20.

## Observation

`qa`, 2026-11-20, the debug binary built from `39db1bb1` (source unchanged
at `8d983bae`), `lib/` on `CRANELISP_LIB`, run from `proj/`, scratch
directories since removed.

```clojure
;; lib/m.cl
(mod- t)
(import [t [v]])
(defn f [] (v))

;; lib/m/t.cl
(defn v [] 1)

;; proj/m/t.cl
(defn v [] 2)

;; proj/main.cl
(import [primitives [Pure]])
(import [m [f]])
(defn main [] (Pure (f)))
```

| Variant | `--run --no-cache` | `--link`, then run | REPL `(f)` |
|---|---|---|---|
| As above | **2** | **2** | **2** |
| Without `proj/m/t.cl` | 1 | 1 | — |
| The same, run once and cached, then `proj/m/t.cl` added | **2** | — | — |
| `(mod t)` in place of `(mod- t)` | **2** | — | — |
| No `proj/m/t.cl`; a second library directory, earlier on the path, holding only `m/t.cl` with `2` | **2** | — | — |
| `proj/m.cl` and `proj/m/t.cl` both present | 2, which conforms | — | — |

## Classification: a defect against spec §8.2.5

- [§8.2.5](../../spec/08-modules.md): a `(mod name)` declaration MUST
  resolve "to the child directory path only", `{parent_dir}/{stem}/{name}.cl`.
  For `lib/m.cl` that is `lib/m/t.cl`.
- **§8.11.2 does not compete in this shape.** Its project-root tier is for a
  name that is searched. Its first tier says a declared child needs no file
  search, and the only reference to `t` is the declaring module's own.
  The last row is the override §8.11.2 does describe: the project replaces
  the module `m`, and its own child comes with it.
- **Severity: wrong value.** A library runs code from a file its source
  does not name, including through a private declaration. No memory hazard.
- **Not established as a regression.** The resolving line dates from
  2026-06-21 (`66a4d41e`, by blame); `qa` ran no earlier tree.

## Attribution: the binary's module loading

- **In source.** `enrol_declared_submodule` resolves the child by calling
  `resolve_module_file` with the child's dotted path, which probes the
  project root and then each library directory. The declaring file's own
  directory is not consulted.
- **Control.** The fifth row differs from the second only by a file earlier
  on the search path that is not under the project root, and gives 2. The
  replacement follows the search order, not the project root as such.
- **Refuted if** a build that resolves the child from the declaring file's
  directory still gives 2 for the subject.
- **Not probed.** The other callers of `resolve_module_file` that are
  handed a child's path (cache restore, the dependency record, the index
  feed).

## One question for `spec`, blocking no test

By §8.1.1 the file `proj/m/t.cl` is itself named `m.t`, while `m` resolves
to the library. The specification does not say whether that file is a
module, an error, or ignored. No clause below reads it.

## Routing

- **`qa` holds this action.**
- **`test`:** T-MOD-CHILD, in the
  [S124 evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test).
- **`design`(int), then `dev`(`src/`):** the correction, carried on
  T-MOD-CHILD unless the user schedules it.

## Completion evidence

T-MOD-CHILD is committed with `// spec: spec/08-modules.md §8.2.5`,
observed RED on its value clauses, and passes on the corrected build with
its override control unchanged. `qa` restores the §8.2.5 band.

## Evidence state (qa, 2026-11-20, `b72742f7`)

T-MOD-CHILD is committed (`ccd7f2e4`) and accepted: four subjects fail on
their exit clause with 2 against 1, and the override control passes.
