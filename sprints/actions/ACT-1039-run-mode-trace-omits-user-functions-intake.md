---
id: ACT-1039
title: Under --run, (trace …) records no user-function calls, while the REPL and --link do
status: open
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - spec/04-expressions.md §4.12.3
  - spec/04-expressions.md §4.12.9
  - crates/cranelisp-backend/src/compiler/trace_codegen.rs
  - tests/trace.rs
---

## Observation

QA found this on 2026-09-30 while attributing
[ACT-1038](ACT-1038-traced-calls-on-spark-workers-leak-and-go-unrecorded-intake.md)
with `target/debug/cranelisp`, built after `88bbbd12`. Each probe ran in a
fresh directory with `CRANELISP_NO_LENIENT=1`, so no spark was involved.
`main` returns the number of recorded frames as its exit code
(`.local/qa-s122-6a/vs/trace_run_frames2.py`).

```clojure
(import [primitives [add-i64 sub-i64 lt-i64 Int Pure Trace TraceCall]])
(import [macros [SCons SNil]])
(defn fib [n] (if (lt-i64 n 2) n (add-i64 (fib (sub-i64 n 1)) (fib (sub-i64 n 2)))))
(defn frames [l] (match l [(SCons h t) (add-i64 (match h [(TraceCall n p r c ns) (add-i64 1 (frames c))]) (frames t)) SNil 0]))
(defn main [] (Pure (match (trace (fib 3)) [(TraceCall n p r c ns) (frames c)])))
```

| Program | REPL | `--run` | §4.12.3 requires |
|---|---|---|---|
| `(trace (fib 3))` | 5 | 0 | 5 |
| `(trace (w2 5))`, with `w2` calling a polymorphic `id` | not probed | 0 | 2 |
| `(trace (work "ab"))`, with `work` calling `str-concat` and `str-len` | not probed | 2 | 3 |

- `--run` records the extern primitives but not the user functions.
- The committed `--link` cell
  `trace::trace_linked_binary_match_consumption_runs` finds `work` recorded
  with its two primitive children.
- Results match with and without the prelude and the cache.
- This violates §4.12.3 (every function holding an indirection-table slot is
  instrumented) and §4.12.9 (a trace behaves identically across modes).
- The fault is also present in a release binary built on 2026-09-29 at 09:31.
  It is not an S122 regression.

## Attribution

- **Status: confirmed by a control, 2026-11-16 at `4b58ab93`**
  ([S124 evidence delta §8.3](../../tests/plan/s124-evidence-delta.md#83-act-1039--the-traced-set-depends-on-slot-contents-at-codegen)).
- **Mechanism.** Trace discovery skips an entry whose GOT slot reads zero
  when the trace form is compiled. A batch compiles the entry module before
  publishing it, so its own functions are dropped from the traced set.
- **Control.** With `fib` in an imported module, published before the
  entry's codegen, the same `--run` records 5 frames; in the entry module it
  records 0. This refutes the earlier variant, that compilation order within
  the wrapper set decides it.
- **Owner: backend,** [trace codegen §1](../../design/backend/trace-codegen.md#1-the-traced-set-is-fixed-by-slot-claims-not-by-slot-contents).
- **Coverage gap.** `tests/trace.rs` observed user-function frames only in
  the REPL and `--link`.

## A second face: a callee restored from the cache (qa, 2026-11-18)

`qa`, `target/debug/cranelisp` at `1a3ab46e`, fresh directories,
`CRANELISP_NO_LENIENT` unset. `shapes.cl` defines
`(defn scalar [:Int n] (add-i64 n 1))`; the entry imports it and `main`
returns 7 when `(trace (scalar 2000))` has one child frame with the right
argument and result text, and 40 when it has no child.

| Leg | First invocation | Second invocation |
|---|---|---|
| `--run` | 7 | 40 |
| `--link`, each produced executable run once | 7 | 40 |
| `--run`, second invocation with `--no-cache` | 7 | 7 |
| `--run` of a new entry beside an import cached by an earlier entry | — | 40 |
| REPL in a directory whose import is cached | — | no `shapes/scalar` frame |

- **Requirement.** §4.12.3 and §4.12.9, as above. A cached restart must not
  change a program's value.
- **Mechanism, observed at its seam.** `CRANELISP_GOT_TRACE` on the fourth
  leg shows the entry's `main` written to its slot before the linker writes
  the restored import's slots. Discovery therefore reads them as zero and
  drops the import's functions: the mechanism recorded above, reached by
  every mode. The `--no-cache` leg differs only in whether the import is
  restored.
- **Extent.** The filed title understates it: `--link` and the REPL lose
  frames too once a traced callee is restored from the cache. The committed
  imported-module control passes because each cell starts cold.
- **Refuted if** the second invocation still records nothing once the
  traced set is fixed by slot claims.

## Evidence allocation

- **`test`, before W6 (T-1039-w of the
  [S124 evidence delta](../../tests/plan/s124-evidence-delta.md#96-get-to-green-item-7)):**
  the imported-module program invoked twice in one directory, in every mode,
  asserting the same frames on the second invocation; the `--no-cache`
  second invocation is its control. `class=mode-divergence`, the same locus.

- **`test` (allocated now):** a failing, un-ignored cell in `tests/trace.rs`
  that runs the program above through all three modes and asserts 5. Cite
  `// spec: spec/04-expressions.md §4.12.9` and use `class=mode-divergence`
  with `locus=crates/cranelisp-backend/src/compiler/trace_codegen.rs` and
  `found=S122`. The REPL leg is the passing control.
- **`test`:** add the imported-module leg as the control (T-1039 of the
  [S124 evidence delta](../../tests/plan/s124-evidence-delta.md#96-get-to-green-item-7)).
- **`dev`(backend)** adds the selection row of trace codegen §1.

## Disposition

Fix or carry is the user's decision under METHOD §2.4. QA retains this intake.

## Completion evidence

The cell goes RED in `--run` only, then GREEN in every mode; T-1039-w goes
RED on its second invocation, then GREEN. QA restores the
§4.12.3 and §4.12.9 bands.
