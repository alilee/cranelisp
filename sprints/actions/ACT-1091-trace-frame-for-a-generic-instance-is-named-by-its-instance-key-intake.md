---
id: ACT-1091
title: A trace frame for an instance of a generic function is named by its instance key, where the template's name alone is required
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-20
refers_to:
  - spec/04-expressions.md §4.12.4
  - design/backend/trace-codegen.md §1.3
---

## Observation

`qa`, 2026-11-20, the debug binary built from `ee65d9aa`, at the REPL with
no prelude, in a scratch directory. The frame names, as printed:

```text
user/(m/helper [primitives/Int] primitives/Int)
user/(user/id2 [primitives/Int] primitives/Int)
user/af
```

- `m.cl` holds `(defn helper [x] x)` and
  `(defn run [h] (trace (helper (h 1))))`. `(m/run af)` at the prompt
  records one frame, the first name above.
- `(defn id2 [x] x)` and `(trace (id2 (af 2)))` at the prompt record the
  third name, for `af`, and the second, for the instance of `id2`.
- Control: the monomorphic `af` takes its module and name alone.

## Classification: a defect against a requirement ruled on 2026-11-20

The user ruled that the frame is named by the template's name alone
(`m/helper`), and spec §4.12.4 states it (`145b65c4`). The delivered
spelling predates the ruling. The face is a wrong diagnostic string; no
memory is read or written that should not be.

## Attribution: the backend, provisional

[Trace codegen §1.3](../../design/backend/trace-codegen.md#13-which-modules-a-form-covers)
states that a frame's name is `{module}/{entry}`, that an instance's entry
is its canonical key, and that the backend keeps that spelling until `spec`
states one. `qa` did not observe the name at its seam. The control differs
from the subject only in whether the function is an instance.

**Refuted if** the backend receives the name already spelled from the
binary.

## Evidence allocation

**T-FRAME-NAME**, allocated to `test` in the
[evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-returned-to-test).
`dev`(backend) owes a module row with the correction.

## Completion evidence

T-FRAME-NAME fails on the instance spelling, then passes. `qa` restores the
spec §4.12.4 band.
