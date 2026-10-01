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

- **Status: provisional.** The symptom and its mode discriminator are
  established; the mechanism is not observed.
- **Hypothesis.** Under `--run`, the trace's wrapper set omits the user
  module's slots. In the `--run` CLIF, `main` is compiled before the module's
  other functions, so a wrapper set fixed at `main`'s codegen would not
  include them. The primitives group is swapped.
- **Refuted if** `CRANELISP_GOT_TRACE` shows the user slots swapped during
  the `--run` trace, or the frame count changes when the user functions come
  from an imported module that is already compiled.
- **Coverage gap.** `tests/trace.rs` observes user-function frames only in the
  REPL and `--link`. The `--run` cells consume a trace without counting
  its user frames.

## Evidence allocation

- **`test` (allocated now):** a failing, un-ignored cell in `tests/trace.rs`
  that runs the program above through all three modes and asserts 5. Cite
  `// spec: spec/04-expressions.md §4.12.9` and use `class=mode-divergence`
  with `locus=crates/cranelisp-backend/src/compiler/trace_codegen.rs` and
  `found=S122`. The REPL leg is the passing control.
- **`design`(backend)** observes the swap set under `--run` and decides the
  fix. **`dev`** adds the unit row.

## Disposition

Fix or carry is the user's decision under METHOD §2.4. QA retains this intake.

## Completion evidence

The cell goes RED in `--run` only, then GREEN in every mode. QA restores the
§4.12.3 and §4.12.9 bands.
