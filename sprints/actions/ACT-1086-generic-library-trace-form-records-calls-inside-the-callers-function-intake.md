---
id: ACT-1086
title: A trace form in a generic library function records calls inside the function its caller passed
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-19
refers_to:
  - spec/04-expressions.md §4.12.3
  - design/arch/tracing.md §5.1
  - design/int/int.md §7.6.4
  - src/worker.rs::covered_set
  - tests/trace.rs
---

## Observation

`qa`, 2026-11-19, `target/debug/cranelisp` built from `f8c55626`, in a
scratch directory. Three files, no prelude:

```clojure
;; m.cl — the library. It imports nothing but primitives.
(import [primitives [Int]])
(defn run [h] (trace (h 1)))

;; z.cl
(import [primitives [Int add-i64]])
(defn zg [:Int n] (add-i64 n 1))
(defn zf [:Int n] (zg n))

;; app.cl — the entry
(import [primitives [Int Pure TraceCall add-i64]])
(import [macros [SCons SNil]])
(import [m [run]])
(import [z [zf]])
(defn frames [l] (match l [(SCons h t) (add-i64 (match h [(TraceCall n p r c ns) (add-i64 1 (frames c))]) (frames t)) SNil 0]))
(defn main [] (Pure (match (run zf) [(TraceCall n p r c ns) (add-i64 40 (frames c))])))
```

The control differs in one annotation: `(defn run [:(Fn [Int] Int) h] (trace (h 1)))`.

| Library function | Cold `--run` | Warm `--run` (`m` restored) | `--link` | REPL `(main)` |
|---|---|---|---|---|
| Subject: `run` generic in its parameter's result | 42 | 42 | 42 | 42 |
| Control: `run` with its parameter type written | 40 | 40 | 40 | 40 |

The subject's trace holds a `z/zf` frame and, inside it, a `z/zg` frame.
The control's holds none.

## Classification: a defect, wrong value

Spec §4.12.3: a trace form in a library module MUST NOT record calls inside
a function passed in by a caller. Its example is the generic spelling,
`(defn profile [f] (trace (f)))`. `m` does not import `z`, so `z` is outside
the form's coverage, and the `z/zg` frame is a call inside the caller's
function. Every mode agrees, cold and warm, so this is not a mode
divergence. No earlier tree was run. Source before row B10 read every loaded
table, so the rule the control follows was delivered by S124 and the
subject is the part it did not deliver.

## Attribution: provisional

- **Confirmed by the control:** the difference is whether the library
  function is generic. The same function with its parameter type written
  follows the rule.
- **Hypothesis, not observed at its seam.** The instance of a generic
  library function is compiled in the batch of the module that instantiates
  it, and that batch passes one covered set, rooted at its own module
  (`src/worker.rs::covered_set`, stored on the prepared turn). The form then
  covers the instantiating module's reference closure where the rule states
  the library's.
- **One observation the hypothesis must also explain.** With the entry's own
  function passed, `(run af)` in `main` records no `app/af` frame in any
  mode, while the same expression typed at the REPL prompt records one.
- **Candidate owners.** The binary, which owns the enumeration and its root
  (int §7.6.4). `arch`, if row B10's one set per `compile_to_module` call
  cannot state a per-defining-module set. Typecheck, if the instance's home
  module is the cause. The backend reads the set it is passed
  (`trace_codegen::discover_traced_fns_from_tables`, module row
  `discovery_covers_module_path_and_listed_modules_only`).
- **Refuted if** the instance is compiled with the library's own covered
  set and the frames still appear.

The receiving role probes before implementing.

## Why coverage missed it

T-1039-lib's library function is `(defn profile [f] (trace (add-i64 (own 10) (f))))`.
The addition fixes `f`'s type, so the cell holds the monomorphic variant
only. The definition-variants audit names generic against monomorphic as an
axis; the cell was written without `qa`'s allocation and that axis was not
applied.

## Evidence allocation

`test`, in `tests/trace.rs`, **REPRO-1086**:

- The three files above. Subject and control in `--run`, `--link` and the
  REPL, each invoked twice in one directory; the second invocation must
  restore `m` (assert `cache hit (.meta valid) for m`).
- Assert 40 for subject and control. Expected on arrival: the six subject
  legs RED on 42, the six control legs green.
- A second subject passes the entry's own function and asserts 40 in the
  three modes; expected green on arrival. It keeps a correction from
  recording the entry's functions.
- Cite `// spec: spec/04-expressions.md §4.12.3` and
  `// defect: class=wrong-scope-lookup locus=src/worker.rs::covered_set found=S124 owner=/dev`.
  The locus is provisional with the attribution.

## Completion evidence

REPRO-1086's subjects fail on 42, then pass with the controls unchanged.
`qa` restores the §4.12.3 bands that name this action.
