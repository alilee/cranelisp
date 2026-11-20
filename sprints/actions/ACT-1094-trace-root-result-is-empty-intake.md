---
id: ACT-1094
title: A trace root omits the expression's formatted result
status: resolved
priority: required
from: training
to: qa
sprint: 124
filed_at: 2026-11-20
refers_to:
  - spec/04-expressions.md §4.12.2
  - tests/trace.rs
---

## Request

Triage this suspected spec violation and allocate a permanent, minimal,
failing-not-ignored reproduction with its control to `test`. Attribute the
mechanism before routing a correction. If the result obligation conflicts with
an approved trace contract, route that question through `sprint` to `spec`;
the teaching material must not silently adopt a different result rule.

## Reproduction

`training` opened spec §4.12.2 during the S124 Phase 6a assessment at source
checkpoint `46e195c7`. It says the evaluated expression's value produces the
root trace node's formatted result string. The existing debug binary instead
returns an empty string, both for a literal and for a named call.

```clojure
(import [primitives [Pure TraceCall str-eq]])
(defn main []
  (Pure
    (match (trace 42)
      [(TraceCall n p r c ns) (if (str-eq r "42") 41 40)])))
```

Expected exit: 41. Observed: 40 under both `--run` and `--link` followed by
execution. At the REPL, define `score` with the match expression as its body
and call `(score)`: observed `:primitives/Int 40`, expected 41.

The named-call variant also returns 40 in all three modes: add
`(defn ident [x] x)` and replace `(trace 42)` with `(trace (ident 42))`.

**Discriminating control:** the named call's child frame contains the expected
formatted result. This returns 41 in all three modes:

```clojure
(import [primitives [Pure TraceCall str-eq]])
(import [macros [SCons SNil]])
(defn ident [x] x)
(defn main []
  (Pure
    (match (trace (ident 42))
      [(TraceCall n p r c ns)
       (match c
         [(SCons child rest)
          (match child
            [(TraceCall cn cp cr cc ct)
             (if (str-eq cr "42") 41 40)])
          SNil 39])])))
```

A direct REPL reading of `(trace (ident 42))` displayed a root named
`"::trace::"` with result `""`, containing the named call's child with result
`"42"`. This finding concerns the root result, not the root's synthetic name.
The child control distinguishes root omission from a general inability to
record or format the value; it does not establish the responsible module.

## Evidence and limits

- All probes used private `/tmp/cranelisp-training-s124-*` directories and
  the existing debug compiler, with inherited `CRANELISP_*` settings
  cleared, `CRANELISP_NO_ENV=1`, no stdlib path, and the workspace platform
  path. Scratch files and generated artifacts were deleted.
- No Cargo invocation, source edit, independent test, or attribution was
  performed. The binary was not rebuilt or proven to correspond exactly to
  the source checkpoint. Concurrent source history advanced to `21101921`
  with spec rulings during assessment; this result obligation was unchanged.
- This is a teaching probe, not acceptance evidence. No existing intake
  naming an empty root result was found in the open actions.

## Classification: a defect against spec §4.12.2

`qa`, 2026-11-20, the debug binary built from `39db1bb1` (no source under
`crates/`, `src/` or `stdlib/` differs at `a39bbb6f`), no prelude, scratch
directories since removed.

| Program | `--run` | `--link`, then run | REPL |
|---|---|---|---|
| The literal subject | 40 | 40 | — |
| The named-call subject | 40 | 40 | `(score)` gives 40 |
| The child control | 41 | 41 | — |
| The named-call subject, comparing the root's result with `""` | 41 | 41 | — |

At the REPL `(trace (ident 42))` displays
`(Trace.TraceCall "::trace::" SList.SNil "" (SList.SCons (Trace.TraceCall "user/ident" … "42" …) …) …)`.

- [Spec §4.12.2](../../spec/04-expressions.md#4122-semantics) closes: the
  value `v` "is used only to produce the root trace node's formatted result
  string". The root's result is the empty string.
- **Severity: wrong value, no memory hazard.** Every mode, every launch.
- **Not a regression.** The sentence and the discard below entered together
  at S20 (`01eff049`, 2026-03-20).

## Attribution: the backend, with the runtime's collect entry

Read in source; not observed in the emitted code.

- `crates/cranelisp-backend/src/compiler/trace_codegen.rs`: `compile_trace`
  and `compile_trace_no_swap` each compile the body, release its value with
  `emit_body_discard`, and call `cranelisp_collect_trace` with no argument.
  Nothing formats the value.
- `crates/cranelisp-intrinsics/src/trace.rs`: a frame's result is set only by
  `cranelisp_trace_exit`, which a wrapper calls. The root frame has no
  wrapper, so `build_trace_call` gives it an empty string; the empty-stack
  arm writes one directly.
- **Control.** The child frame of the same call holds `"42"`: its wrapper
  formats the value and passes it to `cranelisp_trace_exit`.
- **Refuted if** the emitted code for a trace form passes the body's value
  or a formatted string to the runtime before the discard.
- **It counts against the backend,** which holds the value and releases it.
  The correction also needs a way to hand the formatted string to the root
  frame, which changes the interface between the backend and intrinsics and
  goes to `arch` first. [Tracing §3.3](../../design/arch/tracing.md) records
  the discard as built.

## One question for `spec`

Spec §4.12.8's first example shows `(trace (fact 5))` as a `TraceCall` named
for `fact`, with `params="5"`. The compiler returns a root named `::trace::`
with no parameters and the call as its child, and the existing trace cells
assert that shape. The specification does not say what the root's name and
parameters are. Under either reading the root's result is the formatted
value, so the question blocks no clause here; no clause reads the root's
name or parameters.

## Routing

- **`qa` holds this action** until the correction lands and its coverage is
  judged.
- **`test`:** T-TRACE-ROOT, in the
  [S124 evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test).
- **`arch`, `design`(backend), `dev`(backend):** the correction, carried on
  T-TRACE-ROOT unless the user schedules it.
- **`spec`:** the question above.
- **`sprint`:** return this outcome to `training`.

## Completion evidence

T-TRACE-ROOT is committed with `// spec: spec/04-expressions.md §4.12.2`,
observed RED on its result clauses, and passes on the corrected build with
its child control unchanged. `qa` restores the §4.12.2 band.

## Evidence state (qa, 2026-11-20, `b72742f7`)

T-TRACE-ROOT is committed (`f1724229`) and accepted: nine subjects fail on
their result clause, in `--run` cold and restored, linked and at the REPL,
and the heap-valued subject fails with its allocations balanced. The four
child controls pass. The cells count against the backend.

## Corrected, awaiting acceptance (qa, 2026-11-20, `3c5e41ca`)

`arch` approved row B17 (`4a58af99`, `0d5cfe51`); the correction is in
intrinsics (`ecae99c9`) and the backend (`3c5e41ca`). `dev`(backend) reports
the nine subjects and four controls green. `qa` has not run the suite on
this tree.

**A second defect the same change closes.** The discard this filing
attributes released the body's value with no drop glue, so a body whose
value owns heap memory leaked what it holds. It is an `rc-miscount`,
performance only, present since S20, reported by `design`(backend) and
confirmed in source by `arch`.

- **No separate filing:** it is corrected, and nothing of it is carried.
- **Its evidence** is `dev`'s module row
  `trace_root_release_balances_an_owning_value`, which read 5 allocations
  against 4 releases with the old discard planted.
- **By hand on the corrected binary,** `--run`, a traced body returning a
  record holding a `String`, a vector of two `String`s, and a constructor
  applied in the body balance at 22, 32 and 16.
- **T-TRACE-OWNING** is allocated for the modes the module row cannot
  reach (evidence delta §14.3). It arrives green; `qa` saw the fault only
  through `dev`'s planted row.

**The cross-thread stack disturbance** recorded in
[trace runtime §7.1](../../design/intrinsics/trace-runtime.md) is corrected
in the same intrinsics commit. A recorded tree could depend on scheduling
when a second thread's form was skipped or swapped no slot. No memory
hazard, and no cell ever observed it. It gets no filing and no
solution-level cell: no fixture built from user commands selects the
interleaving, and `dev`'s module rows carry detection proofs.

**What acceptance needs, at the full run:**

1. The nine subjects pass with no assertion changed since `f1724229`, and
   the four controls still pass.
2. T-TRACE-OWNING passes in every mode.
3. `qa` reads the module rows of `ecae99c9` and `3c5e41ca` against their
   planted faults, and the two reviews' findings.
4. The category census is armed in that run and reads zero, since the
   release of a traced value now goes through drop glue.
5. The trace goldens are unchanged, and no test that passed at `b72742f7`
   fails.
6. `test` stamps the nine cells `fixed=S124/3c5e41ca` and puts their
   comments in the past tense. `qa` then restores the §4.12.2 band and
   deletes this filing.

Still open with `spec`: the root's name and parameters, above; and a
skipped form's result (trace runtime §7.3).

## Accepted (qa, 2026-11-20, full run at `121c5c9e`)

Read against the six needs above:

1. **Met.** The nine subjects pass, and `tests/trace.rs` has only additions
   since `f1724229`. The four controls pass.
2. **Met as run, with one fixture returned.** T-TRACE-OWNING's six cells
   pass. Their value is built outside the traced call and passed through
   it, so `qa` cannot say the traced value is its only owner; a release
   with no glue may still balance there. `test` adds a subject whose value
   is built inside the call (evidence delta §14.3). By hand under `--run`
   that shape balances.
3. **Met.** The five backend rows and seven intrinsics rows named in the two
   commits pass. Their reds and planted faults are as `dev` records them;
   `qa` did not replant. Both reviews returned no finding, as `sprint`
   reports.
4. **Met.** The armed census reads zero from every program, over 298,467
   frames.
5. **Met.** No golden changed, and no test that passed at `b72742f7` fails.
6. **Owed.** `test` stamps the nine cells; `qa` then deletes this file.

The §4.12.2 band is restored. The backend holds no failing test.
