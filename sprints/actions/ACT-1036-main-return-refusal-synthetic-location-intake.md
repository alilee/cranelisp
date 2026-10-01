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

## Disposition

Fix or carry is the user's decision under METHOD §2.4. QA retains this intake.

## Completion evidence

The cell goes RED for the location, then GREEN after the correction in both
batch modes, with the refusal text unchanged.
