---
id: ACT-1036
title: The batch refusal of a non-IO `main` return is located at 0..0 instead of at `main`
status: open
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - src/exe.rs::classify_main_return_type
  - repl/spec/05-error-presentation.md §5.5
  - repl/spec/05-error-presentation.md §5.1
  - tests/spec_10_io.rs
  - design/arch/fixmes/0915-codegen-diagnostic-exposes-mangled-doubled-internal-subjects.md
  - tests/plan/s122-evidence-delta.md
---

## Observation

Verified by QA on 2026-09-30 at `88bbbd12` with `target/debug/cranelisp`.
The lead came from `training`'s Phase-6a assessment (F2).

```clojure
(import [primitives [Int]])
(defn main [] 5)             ; main on line 2
```

- `--run` and `--link` both print
  `p.cl:1:1: error: codegen error at 0..0: main must return `IO _` …`.
  The refusal and its wording are correct; the location is not.
- Both refusal arms of `classify_main_return_type` raise at
  `ErrorLocation::from_span(Span::SYNTHETIC)`. The definition's span is
  available to the caller.
- This violates the first bullet of REPL §5.5 (a compiler-stage diagnostic is
  located at the user's form) and §5.1.

## Attribution

- **Entered at** `src/exe.rs::classify_main_return_type`: the raise site has no
  span parameter. The mechanism is observed in source; the symptom is the
  synthetic span's rendering at `1:1` and `0..0`.
- **Not folded into FIXME 0915.** 0915 carries the backend registry spans and
  the `format_error` subject projection. This raise site is in the binary and
  needs its own span, so it has an independent fix and RED.
- **0915 witness.** This is a public codegen error with a `0..0` span. It is a
  witness for the falsifier of 0915's K9 carry, alongside ACT-1034's refusal.

## Evidence allocation

- **`test`:** extend `spec_10_io::batch_main_pure_int_return_is_rejected`, or
  add a sibling cell, with `main` on line 2. Assert a location on line 2 and no
  `0..0`, in `--run` and `--link`. RED now. Cite
  `// spec: repl/spec/05-error-presentation.md §5.5` and use
  `locus=src/exe.rs::classify_main_return_type`. The class is provisional
  `check-gate-leak`: a type property refused under the codegen category.
  QA confirms it once `design`(int) decides where the refusal belongs.
- **Coverage gap.** The existing cell checks the refusal and its wording, not
  its location.
- **`design`(int)** chooses the span source; **`dev`(src)** adds the unit row
  with the fix.

## S124: two sibling raise sites (qa, 2026-11-16, at `4b58ab93`)

Both are batch refusals the specification requires, reported at `1:1` and
`0..0` with the subject on line 3. `test` commits them as REPRO-0915-loc of
the [S124 evidence delta](../../tests/plan/s124-evidence-delta.md#34-repro-0915-loc--batch-refusals-located-at-00).

- **The arity arm of the same function.** `(defn main [x] …)` is refused
  with `main must be a zero-argument function returning IO _`. The committed
  cell covers only the non-`IO` arm.
- **The `discover-tests` refusal** (`src/exe.rs::refuse_dev_session_externs`,
  REPL §16.6): `` `p/main` references `discover-tests` `` is not located at
  the referencing function. Unlike ACT-1034's refusal, this diagnostic is
  required, so it is a durable public witness of FIXME 0915's location
  requirement.

## At the W8 exit (qa, 2026-11-18, `2d3a5b3e`)

- **Corrected (`e294852f`, with `98ea54a0`).** Every refusal about a bound
  `main` is located at its definition origin under `--run` and `--link`:
  the non-`IO` return, the arity arm, a macro `main`, a macro-produced
  `main` (at the written call, also across a dependency retry) and a
  multi-arity `main`. The committed cell and the `s124_main_location_*`
  cells pass; `qa` read each RED on the location before the correction
  ([evidence delta §14](../../tests/plan/s124-evidence-delta.md#14-the-standing-state-at-f8c55626)).
- **Not corrected: the `discover-tests` refusal.**
  `src/exe.rs::refuse_dev_session_externs` still reports
  `p.cl:1:1: error: codegen error at 0..0: `p/main` references `discover-tests` …`
  with the reference on line 3, in both batch modes.
  `tests/test_runner.rs::s124_discover_batch_location_run` and `_link` are
  RED on it. No design names a span source for this refusal:
  [test runner §7.3](../../design/int/test-runner.md#73-batch-refusal-of-discover-tests)
  states the detector and the wording only.
- **Open for:** `design`(int) to state the location (the referencing
  function's definition origin is available to the same session), then
  `dev`(`src/`) with a module row. Whether that lands in S124 or is carried
  is the user's decision.

## At `a205a29f` (qa, 2026-11-18)

- **Corrected (`52de1aad`).** The `discover-tests` refusal is located at
  the referencing function under `--run` and `--link`;
  `tests/test_runner.rs::s124_discover_batch_location_run` and `_link`
  were RED at `2d3a5b3e` and pass in `qa`'s full run.
- **One residual, with the user.** A macro-produced referencing function
  restored from cache is still reported at `0..0`
  ([test runner §7.3](../../design/int/test-runner.md#73-batch-refusal-of-discover-tests)).
  `design`(int) accepts it. No cell asserts it. This action stays open
  until the user accepts the residual or asks for its correction.

## Completion evidence

Every cell goes RED for the location, then GREEN after the correction in
both batch modes, with the refusal text unchanged: met. The residual above
is accepted by the user, or corrected against a cell `qa` allocates.
