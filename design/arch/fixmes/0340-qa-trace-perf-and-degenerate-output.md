---
number: 0340
target: /qa
filed_by: /sprint
filed_at: 2026-06-13
sprint_filed: 81
refers_to: design/arch/tracing.md, crates/cranelisp-intrinsics/src/ (trace bodies + table), crates/cranelisp-backend/src/ (trace DisplayDescriptor baker + discovery-in-codegen), repl demo sweep (Wave I-4 finding A)
status: open
---

# `(trace expr)` is ~31s per call AND produces degenerate output (args not captured)

## Issue (Phase-6b /repl Wave-I-4 finding)

Exercising `(trace (+ 1 2))` in the REPL (prebuilt S81 binary) surfaced two defects:

1. **Severe perf:** the call consistently takes **~31s** (the REPL self-reports `31327+0ms`)
   vs ~0.12s for a non-trace session. This makes `(trace …)` effectively undemoable live (a
   PTY demo player drains/times out on it).
2. **Degenerate output:** the result is
   `(Trace.TraceCall "::trace::" SList.SNil "" SList.SNil <num>)` — the **args list is `SNil`**
   (operands not captured), the **name is the `"::trace::"` placeholder** (not the traced
   call's name), and the operand/result fields are empty/degenerate. The trace ran without
   error but captured essentially nothing useful.

It is unclear whether this is a regression or a long-standing limitation — the /examples plan
notes example "25 — Trace" was *deferred* ("REPL-only; batch mode lacks formatted trace
fields"), suggesting trace output has known gaps; but the ~31s latency and the totally-empty
arg capture look like more than a formatting limitation.

## Proposed resolution

1. **/qa authors a minimal repro** characterizing both halves: (a) a timing assertion / note
   that `(trace (small-expr))` should be sub-second, and (b) an output assertion that the
   captured Trace ADT names the traced call + captures its operands (not `SNil`/`"::trace::"`).
   `// spec:` → the trace spec (`spec/` trace section / `design/arch/tracing.md`).
2. **Bisect / triage owner:** determine whether the perf + degenerate capture is a regression
   (when did `(trace …)` last produce good output?) and which crate owns it — the trace codegen
   discovery + `DisplayDescriptor` baking is **/backend**; the 12 trace bodies + table are
   **/intrinsics**. Hand the narrowed repro to the owning crate.

## Context

Phase-6b /repl Wave-I-4 demo sweep. The S81 trace work was the 0266 metadata move (root form)
+ the funnel's fork-join touching; neither obviously explains 31s + empty capture. Forward-flow
to a trace-owning sprint. The 0266 change (trace as a root form, no import) is correct and
unrelated — this is about what `(trace …)` actually CAPTURES + how long it takes.
