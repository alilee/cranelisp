---
id: ACT-1078
title: A cached module that holds a trace form fails to load in a program that imports fewer modules than the one that cached it
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-18
refers_to:
  - spec/04-expressions.md §4.12.3
  - design/arch/tracing.md §5.1
  - design/backend/trace-codegen.md §1.3
  - design/int/int.md §7.1
  - crates/cranelisp-backend/src/compiler/trace_codegen.rs
  - tests/plan/s124-evidence-delta.md
---

## Observation

Reported by `design`(backend). Re-run by `qa` on the debug build of
`7888c515`, 2026-11-18, each leg in a fresh directory.

```clojure
;; u.cl
(import [primitives [add-i64 Int Trace TraceCall]])
(defn inc [:Int n] (add-i64 n 1))
(defn traced [] (match (trace (inc 2)) [(TraceCall n p r c ns) 7]))
;; x.cl
(import [primitives [add-i64 Int]])
(defn xf [:Int n] (add-i64 n 2))
;; e1.cl
(import [primitives [Pure Int add-i64]]) (import [u [traced]]) (import [x [xf]])
(defn main [] (Pure (add-i64 (traced) (xf 0))))
;; e2.cl
(import [primitives [Pure]]) (import [u [traced]])
(defn main [] (Pure (traced)))
```

| Leg | Invocations | Observed |
|---|---|---|
| Subject, `--run` | `e1.cl`, then `e2.cl` | `e1` exits 9. `e2`: `module 'u' failed: codegen error: unresolved symbol: __cranelisp_got_x`, exit 1 |
| Subject, `--link` | `e1.cl`, then `e2.cl` | `e1` links and exits 9. `e2`: the same error; no executable |
| Control: cold | `e2.cl` alone, twice | exits 7 both times |
| Control: no cache | `e1.cl`, then `--run --no-cache e2.cl` | exits 7 |
| Control: no trace form | `traced` as `(match (inc 2) [n 7])`; `e1.cl`, then `e2.cl` | exits 7 |
| REPL | `e1.cl` as the entry, then `e2.cl` | `(main)` yields 7 (one run) |

The subject fails the same way on the release build of 2026-11-18 00:11
(the W2 tree), so it predates W3. Earlier trees were not run.

## Classification: a defect

- **Requirement.** `e2.cl` is a legal program and runs cold. A cached
  restart must not refuse what a fresh compile accepts
  ([int §7.1](../../design/int/int.md#71-cache-hit-flow-inside-register_module):
  every table an object references is reached by its restore walk).
- **Face.** A legal program is refused, under `--run` and `--link`, until
  the cache directory is removed. The error names a module the program
  never mentions, at location `0..0`.
- **Class:** `artifact-underkey`. The cached object's content depends on
  which modules were loaded when it compiled, and its validity record does
  not hold that set.

## Attribution

- **Mechanism, observed at its seam.** After the subject's first
  invocation, `nm` on the cached `u.o` lists `__cranelisp_got_x` as
  undefined, beside `__cranelisp_got_u` and `__cranelisp_got_primitives`.
  `u` does not import `x`. The no-trace control differs only in the form.
- **Owner:** backend, for the set a trace form swaps
  (`discover_traced_fns_from_tables`). The set is the open question of
  [tracing §5.1](../../design/arch/tracing.md#51-which-modules-a-form-covers--with-the-user-2026-11-18),
  which is with the user. No correction can be designed before that ruling.
- **Refuted if** the subject passes with the trace form present, or the
  cached `u.o` names only tables that `u` reaches.
- **Why coverage missed it.** No cell runs two entry files against one
  cache directory. T-1039-w repeats one program.

## Evidence allocation

`test`, in `tests/trace.rs`:

- **REPRO-1078.** The four files above. The subject invokes `e1.cl` and
  then `e2.cl` in one directory, under `--run` and under `--link`; the
  second invocation must restore `u` (assert `cache hit (.meta valid) for
  u`) and exit 7. Controls: the no-cache leg under `--run`, and the
  no-trace twin under both modes.
- Cite `// spec: spec/04-expressions.md §4.12.3` and
  `// defect: class=artifact-underkey locus=crates/cranelisp-backend/src/compiler/trace_codegen.rs::discover_traced_fns_from_tables found=S124 owner=/dev`.
- Expected on arrival: both subjects RED on `unresolved symbol`, every
  control green.

The cell holds under either answer to tracing §5.1: both candidates make
the object a function of its own module's load edges.

`dev`(backend) owes the module rows of
[trace codegen §1.3](../../design/backend/trace-codegen.md#13-blocked-on-arch-which-modules-contribute)
with the correction.

## Disposition

Blocked on the user's ruling on tracing §5.1, with ACT-1039. `qa` retains
this intake.

## Completion evidence

REPRO-1078's subjects fail on the unresolved symbol, then pass with the
controls unchanged.

## The subject cells are run-dependent (qa, 2026-11-19, `d30c70e9`)

In five runs of the cells alone, `s124_1078_subject_run` failed three
times and `s124_1078_subject_link` four; both passed in one run. Every
failure was the `unresolved symbol` this filing states. The fixture leaves
the order in which `u` and `x` compile to the scheduler. Returned to `test`
([evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-returned-to-test)).
