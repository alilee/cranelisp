---
id: ACT-1063
title: A host-promised primitive used as a value is refused at codegen, and a partial `bind` aborts
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-16
refers_to:
  - spec/03-types.md
  - spec/10-io.md
  - repl/spec/05-error-presentation.md
  - design/backend/compile-to-module.md
  - tests/plan/s124-evidence-delta.md
---

## Observation

`qa`, on `target/debug/cranelisp` at `4b58ab93`, 2026-11-16 and 2026-11-17.
No prelude, `(import [primitives [*]])`, `--run`.

| Leg | `main` body | Observed |
|---|---|---|
| Subject | `(let [b bind] (b (Pure 5) (fn [v] (Pure v))))` | `codegen error at 48..52: fn-as-value wrapper for 'bind' reached codegen with no GOT-slot carrier` |
| Subject | `(ap bind)`, where `ap` calls its parameter | the same refusal |
| Subject | `(let [r race] (r (Pure 5) (Pure 6)))` | the same refusal, naming `race` |
| Control | `add-i64` and `Pure` bound by `let` and called | run correctly |

**Extent, observed 2026-11-17** (leads from `design`(backend) and
`design`(typecheck)).

| Leg | Program | Observed |
|---|---|---|
| Subject | `select`, `sleep`, `nanos` and `name` bound by `let` and called; `select` passed to a function | the same refusal, naming each |
| Subject, REPL | `discover-tests` and `sconcat` bound by `let` and called | the same refusal |
| Subject, partial | `(let [k (bind (Pure 5))] (k (fn [v] (Pure v))))` | abort (134), `misaligned pointer dereference` in `cranelisp-intrinsics` `heap_access.rs`; `--run`, the REPL and the linked executable, 3 of 3; unchanged with `CRANELISP_NO_IO_SCHEDULE` |
| Subject, partial | `(let [k (race (Pure 5))] (k (Pure 5)))` | the compile worker panics: `can't resolve symbol race`, reported at `1:1` and `0..0`; `--link` the same |
| Control: has a slot | `str-len` as a value; `(add-i64 2)` partially applied | run correctly |
| Control: no slot, has a wrapper rule | `vec-len` as a value | runs correctly |
| Control: host symbol exists | `(sconcat SNil)` partially applied, REPL | runs correctly |
| Control: a user function over the primitive | `(defn then [io f] (bind io f))`, partially applied | runs correctly |
| Not in the family | `quote-sexp` as a value runs correctly; its direct call aborted on a stack-placed operand until stack placement retired (ACT-1066, closed S124) | — |

## Classification: a defect

- **Requirement.** [Spec §3.2.1](../../spec/03-types.md#321-function-types):
  "All functions are first-class values." Spec §10.3 gives `bind` a function
  type, and no clause exempts it. Where a form is not a function the
  specification says so (§4.10: the vec literal "cannot be referenced as a
  value"). A legal program is refused.
- **Class:** `carrier-loss`. Second face: the refusal names a
  compiler-internal carrier, against REPL §5.5.
- **Attribution: the backend, alone.** The controls separate the cause:
  a slot-carrying primitive and a slot-less primitive with a wrapper rule
  both work as values, and every slot-less primitive without one is
  refused. `design`(backend) and `design`(typecheck) each read the source
  at `4b58ab93` and agree that the value reference arrives with its
  resolved entry and that no producer owes a carrier
  ([compile-to-module §12.1](../../design/backend/compile-to-module.md#121-host-promised-primitives-as-values-act-1063-s124)).
  The wrapper's rule selection was not observed at its own seam.
- **The partial `bind` face is memory-unsafe.** The program compiles and
  links, so some symbol answers the wrapper's by-name import of `bind`.
  Hypothesis, not observed: the C library's `bind`. The design predicted a
  link failure for both partial forms; that holds for `race` only.
- **Refuted if** the user rules that inline primitives are not values. That
  is a change to §3.2.1, not a reading of it, and the cell then asserts a
  typecheck rejection instead.

## Request

- `test` commits REPRO-1063
  ([evidence delta §3.9](../../tests/plan/s124-evidence-delta.md#39-repro-1063--a-host-promised-primitive-as-a-value))
  in the S124 evidence wave.
- The correction is in S124's scope by the user's 2026-11-17 decision, as
  backend row B12. It stays there: the correction is one surface, so the
  named-carry condition is not met.

## Completion evidence

REPRO-1063 and REPRO-1063-p fail on the refusal and the abort, then pass in
every mode with their controls; T-1063-b balances against the direct call;
`dev`(backend) lands M-1063.
