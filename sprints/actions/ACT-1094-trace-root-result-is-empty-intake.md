---
id: ACT-1094
title: A trace root omits the expression's formatted result
status: open
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

## Completion evidence

`qa` records the authority and attribution decision; `test` commits the narrow
subject and child control with `// spec: spec/04-expressions.md §4.12.2`.
The committed reproduction carries the issue until the owning correction or
an explicit user ruling resolves it. `sprint` returns the outcome to `training`
before a worked trace-result lesson is written.
