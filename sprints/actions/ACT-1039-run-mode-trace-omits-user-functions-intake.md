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

## Evidence allocation

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

The cell goes RED in `--run` only, then GREEN in every mode. QA restores the
§4.12.3 and §4.12.9 bands.
