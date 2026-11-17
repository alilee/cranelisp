---
id: ACT-1069
title: A trace formats a one-word single-constructor ADT argument as a tag or dereferences it as a pointer
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-18
refers_to:
  - spec/04-expressions.md §4.12.2
  - spec/12-runtime.md §12.9
  - crates/cranelisp-intrinsics/src/trace_format.rs::render_adt
  - src/display.rs::push_value_layout_adt
  - tests/ownership_reuse.rs
  - tests/plan/s124-evidence-delta.md
---

## Observation

`qa`, on `target/debug/cranelisp` at `1a3ab46e`, 2026-11-18. Each program ran
with `--run` in its own fresh directory. No prelude; `primitives` imported
whole and `macros` for `SCons` and `SNil`. Found by `test` as the three
`ownership_reuse::s124_d4_trace_*` cells, which end on signal 11.

`shapes.cl`, imported by the entry so that the callee is traced
([ACT-1039](ACT-1039-run-mode-trace-omits-user-functions-intake.md)):

```clojure
(import [primitives [*]])
(deftype Box [:Int value])
(deftype Two [:Int a :Int b])
(defn observe [:Box b] (match b [(Box n) (add-i64 1 n)]))
(defn observe2 [:Two t] (match t [(Two a b) (add-i64 a b)]))
(defn scalar [:Int n] (add-i64 n 1))
```

`main` matches the trace's first child frame and compares its first argument
string and its result string with the required text.

| Leg | Traced call | Required argument text | Observed |
|---|---|---|---|
| Subject | `(observe (Box 2000))` | `(Box 2000)` | signal 11 |
| Subject | `(observe (Box 1024))`, `(Box 4096)`, `(Box 100000)` | `(Box n)` | signal 11, each |
| Subject | `(observe (Box 4095))` | `(Box 4095)` | abort (134) |
| Subject, small payload | `(observe (Box 3))`, `(Box 255)`, `(Box 1023)` | `(Box n)` | no signal; the argument text is wrong (`<unknown-tag:3>` and `<unknown-tag:1023>`, read at the REPL); the result text is right |
| Control: two fields | `(observe2 (Two 2000 17))` | `(Two 2000 17)` | as required, result `2017` |
| Control: scalar | `(scalar 2000)` | `2000` | as required, result `2001` |
| Control: the display route | `(Box 3)` and `(observe (Box 2000))` entered at the REPL, untraced | `:shapes/Box (Box 3)`, `2001` | as required |

Every subject failed on each of its runs, with and without
`CRANELISP_RC_DEC_CHECK`, `CRANELISP_RC_STATS` and `CRANELISP_NO_LENIENT`.

## Classification: a defect, memory-unsafe

- **Requirement.** [Spec §4.12.2](../../spec/04-expressions.md#4122-semantics)
  item 3: a recorded call's arguments are formatted in the canonical value
  display format (§12.9). §12.9 gives `(Box 2000)`.
- **Faces.** A wrong argument string below 1024; a read through the payload
  as an address at or above it, which ends the process or reads whatever is
  mapped there.
- **Not an S124 regression.** `target/release/cranelisp` built 2026-11-15
  gives the same results for `(Box 3)`, `(Box 1023)`, `(Box 1024)`,
  `(Box 2000)` and the two-field control.

## Attribution

- **Mechanism, observed at its seam.** A single-constructor type with one
  value-eligible field is stored as that field's word
  (`cranelisp_types::value_layout`). `trace_format::render_adt` has no case
  for it. It compares the word with `NULLARY_TAG_THRESHOLD` (1024): below, it
  looks the word up as a constructor tag and prints `<unknown-tag:n>`; at or
  above, it loads a tag from the word plus 16.
- **The other display route has the case.** `src/display.rs` calls
  `push_value_layout_adt` before its tag read, and renders `(Box 3)`.
- **Controls differing only in the claimed cause.** The two-field product is
  not stored as one word and formats correctly. The payload on either side
  of 1024 changes the face from wrong text to a signal, as the threshold
  comparison predicts.
- **Class:** `display-envelope-mirror`, with a `scalar-as-pointer` face.
- **Entered** when the one-word representation was added without the trace
  formatter. No trace cell passed a one-word ADT as an argument, so coverage
  did not observe it.
- **Refuted if** a one-word ADT argument formats correctly through
  `render_adt` on this tree, or the subject still fails once no type is
  stored as one word.
- **Not probed.** A `Float` or `Bool` field; a one-word ADT as a traced
  result or nested inside another argument; a traced extern primitive.

## Correction

None of its own. Value flattening retires in S124 (packet row D4, backend
change-set B5, wave W5): a `Box` is then a heap value and `render_adt` is
right as written.

## Request

- `test`, before W5: on the three `s124_d4_trace_*` cells, cite
  `// spec: spec/04-expressions.md §4.12.2` and add the `// defect:` line
  (`class=display-envelope-mirror`,
  `locus=crates/cranelisp-intrinsics/src/trace_format.rs::render_adt`,
  `found=S124`, `owner=/dev`). Add a small-payload leg, `(Box 3)`, in every
  mode: it fails on the argument text and not on a signal. Add the two-field
  control in every mode.
- No scheduling decision is needed: the correction is in S124's approved
  scope.

## Completion evidence

The trace subjects and the small-payload leg fail as above, then pass in
every mode on the B5 tree with the two controls and no change made for them.
`qa` then deletes this record. If a leg is still RED on the B5 tree the
attribution is refuted and the cell returns to `qa`.
