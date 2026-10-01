---
id: ACT-1038
title: Traced calls that run on a spark worker are not recorded and leak their formatted argument and result Strings
status: open
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - spec/04-expressions.md §4.12.2
  - crates/cranelisp-intrinsics/src/trace.rs::cranelisp_trace_enter
  - crates/cranelisp-intrinsics/src/trace.rs::cranelisp_trace_exit
  - crates/cranelisp-backend/src/compiler/trace_codegen.rs
  - design/backend/lenient-eval.md §2.3
  - design/arch/tracing.md §4.2
  - design/arch/bounded-contexts.md
---

## Observation

`review` raised the leak from a source reading of the intrinsic-ownership
correction (finding 2). QA reproduced it on 2026-09-30 with
`target/debug/cranelisp` built after `88bbbd12`, in the REPL with
`tests/fixtures/preludes/primitives-only.cl`, one fresh directory per run and
`CRANELISP_ALLOC_PARITY_DUMP=1` (`.local/qa-s122-6a/vs/trace_probe3.py`).

```clojure
(import [primitives [Trace TraceCall]])
(defn fib [n] (if (lt-i64 n 2) n (add-i64 (fib (sub-i64 n 1)) (fib (sub-i64 n 2)))))
(trace (fib 12))              ; 465 calls of fib
```

| Run | `fib` frames recorded | allocs − deallocs |
|---|---|---|
| default (lenient) | 2 (three runs); 112 (one run) | 926; 706 |
| `CRANELISP_NO_LENIENT=1` control | 465 (four runs) | 0 |
| untraced `(fib 12)`, lenient control | — | 0 |

- **Violations.** §4.12.2 item 3 requires every instrumented call to be
  recorded, and the tree loses most of them. Item 2 requires normal strict
  evaluation of the body. The unreleased Strings violate §12.3.1 item 1.
- The leak equals the missing frames exactly: (465 − 2) × 2 = 926 and
  (465 − 112) × 2 = 706. Each missing call contributes one parameter String
  and one result String.
- The recorded tree varies from run to run.
- The fault is also present in a release binary built on 2026-09-29 at 09:31.
  It is not an S122 regression.

## Attribution

- **Status: confirmed.** The sibling runs differ only in whether sparks are
  admitted. The per-call arithmetic ties each lost frame to exactly two
  unreleased blocks.
- **Mechanism.**
  - `fib` is compiled outside the trace body, so its own apply site is
    spark-admitted. Its CLIF has a runtime create-gate whose parallel arm
    builds one thunk per recursive call and runs each through the
    IVar create, spark and force calls. Its sequential arm calls through the
    GOT.
  - `design/backend/lenient-eval.md` §2.3 excludes sparks only *lexically*
    inside `(trace …)`: `in_trace_body` is set while compiling the trace
    form. Callees still spark during the trace's dynamic extent.
  - The trace installs its wrappers in the process-global GOT, so a spark
    worker calling `fib` enters a wrapper. The wrapper formats the arguments
    (`cranelisp_trace_format` allocates), then calls
    `cranelisp_trace_enter`/`_exit`. Both return at once on a thread without
    `TRACE_THREAD_ID` and neither stores nor releases the Strings.
- **Entered at** the design: §2.3's stated purpose, deterministic trace
  output, is not realized for callees. The intrinsic early returns are the
  leak's seam. The named-intrinsic conventions table says those Strings are
  taken "into the trace frame", which holds only on the role thread.
- **Refuted if** frames go missing with sparks disabled, or the delta departs
  from two blocks per missing call for a one-parameter function.

## Evidence allocation

- **Class confirmed (QA, 2026-09-30):** `shared-state-write-race`. The trace
  writes the process-global GOT, spark workers read it, and the recorded tree
  varies by interleaving. Both cells class that mechanism; `test` drops the
  "provisional" suffix.
- **Premise leg (QA, 2026-09-30).** The cells discriminate only while `fib`
  is spark-admitted outside a trace. The lenient-eval design expects spark
  admission to change. `test` adds a premise to the frame-count cell: an
  untraced `(fib 12)` REPL child under `CRANELISP_SPARK_STATS=1` prints
  `[SPARK_STATS] spawns=N` with N > 0. A lost premise fails with its own
  message, never as the defect.
  - The premise stays true under either correction, because it observes the
    untraced run.
  - Measured: `spawns=14` in 3 of 3 runs. `CRANELISP_NO_LENIENT=1` prints no
    stats line (`.local/qa-s122-6b/sentinel/sparks.py`).
  - The leak cell shares the program, so it needs no second premise.
- **`test` (allocated now):** failing, un-ignored cells in `tests/trace.rs`
  citing `// spec: spec/04-expressions.md §4.12.2`, with
  `class=shared-state-write-race`,
  `locus=design/backend/lenient-eval.md §2.3 trace-body exclusion`, and
  `found=S122`.
  - The frame count of `(trace (fib 12))` equals 465, in every mode, once
    ACT-1039 lets batch record user functions. Until then, assert in the REPL.
  - Allocator balance through `helpers::marginal`: a traced and an untraced
    `fib` child as the pair, and the subject's residual is 0.
  - The `CRANELISP_NO_LENIENT=1` run is the passing control.
- **Design choice (`design`, backend or intrinsics as `arch` routes).** Either
  suppress sparks for the trace's dynamic extent (matching item 2's "strict
  evaluation"), or record worker frames. Either way, no wrapper allocates
  without a consumer. `dev` adds the unit row at the chosen seam.
- **`arch`:** qualify the two named-intrinsic rows, per review finding 2.

## Disposition

Fix or carry is the user's decision under METHOD §2.4. QA retains this intake.

## Completion evidence

The cells go RED for the intended reason, then GREEN, with the no-lenient
control unchanged. QA re-reads the §4.12.2 band.
