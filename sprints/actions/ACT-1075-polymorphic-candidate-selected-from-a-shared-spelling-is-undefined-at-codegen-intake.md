---
id: ACT-1075
title: A call that selects a polymorphic function from a spelling with several candidates is refused at codegen as an undefined function
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-18
refers_to:
  - spec/08-modules.md §8.6.4
  - spec/08-modules.md §8.6.5
  - crates/cranelisp-typecheck/src/program/mono_collect.rs::collect_mono_call_sites
  - design/typecheck/monomorphisation.md §3.1
  - tests/spec_08_modules.rs
  - tests/spec_10_io.rs
  - tests/plan/s124-evidence-delta.md
---

## Observation

`qa`, on the debug build of `8667a868`, 2026-11-18, in
scratch directories, every invocation with `--no-cache`. Found while
attributing T-1065-f, which stayed RED after ACT-1065's correction.

```clojure
;; m.cl
(defn conv [a f] (f (primitives/add-i64 a 100)))
;; n.cl
(defn conv [s] (primitives/str-len s))
;; p.cl — no prelude
(import [primitives [Pure add-i64]])
(import [m [conv]])
(import [n [conv]])
(defn main [] (Pure (conv 5 (fn [x] (add-i64 x 1)))))   ; required: 106
```

| Leg | Candidates for the spelling | Selected candidate | Observed |
|---|---|---|---|
| Subject, `--run` and `--link` | `m/conv`, `n/conv` | `m/conv`, polymorphic | `codegen error …: undefined function: conv` |
| Subject, REPL (the two imports, then the call) | the same | the same | the same error on the call; `(m/conv 5 (fn …))` in the next turn yields 106 |
| Control: one candidate (`n` not imported; T-1065-f's own program with a prelude that exports `race`) | `m/conv` | polymorphic | 106 |
| Control: `m/conv` is `(defn conv [a] (primitives/add-i64 a 100))`, called as `(conv 5)` | two | monomorphic | 105 |
| Control: a two-parameter `(defn conv [a b] (primitives/add-i64 a b))`, called as `(conv 5 100)` | two | monomorphic | 105 |
| A one-parameter identity `(defn str-len [a] a)` beside a prelude that exports the primitive `str-len` | two | polymorphic | `undefined function: str-len` |
| The polymorphic candidate defined in the calling module, beside the prelude's primitive | two | polymorphic | `undefined function` |
| The primitive imported by name instead of through a prelude | two | polymorphic | `undefined function` |
| T-1065-f's program, the selected name passed as a value (`(app bind)`) | two | polymorphic | `generic value reference 'bind' reached codegen without a mono` |
| Two same-shaped polymorphic candidates (`m/foo`, `prelude/foo`) | two | none | `type error: ambiguous bare name 'foo'`, as §8.6.5 requires |

## Classification: a defect

- **Requirement.** Spec §8.6.4: several declarations may share an
  unqualified spelling. Spec §8.6.5 rule 3: a call whose argument types
  leave one candidate is valid. The subject is a legal program.
- **Class:** `carrier-loss`. Face: a legal program refused, in every mode,
  with a codegen error.
- **Not the bind-chain pass.** No spelling the pass reads appears in the
  subject. T-1065-f's program fails identically with
  `CRANELISP_NO_IO_SCHEDULE=1` and with a three-parameter `bind`.

## Attribution

- **Predates S124 W3.** The release build of 00:11 on 2026-11-18, before
  T1, refuses the subject and the identity leg with the
  same text and passes the monomorphic control.
- **Confirmed by controls:** the failure needs both a second candidate for
  the spelling and a polymorphic selected candidate. Each control removes
  one of the two and passes. The origin of either candidate (prelude,
  import, local definition, primitive) does not matter.
- **Mechanism, read at its seam** by `dev`(typecheck), `design`(typecheck)
  and `qa` (2026-11-18, `84719eb6`). Candidate selection writes the selected
  identity to the callee's `var_refs` verdict. The monomorphisation
  collectors in `program/mono_collect.rs` require that verdict and then
  resolve the written spelling again to name the template. With two
  declarations sharing the spelling that second resolution does not return
  the selected one, so no instance is minted and the backend's keyed read
  misses. [Monomorphisation §3.1](../../design/typecheck/monomorphisation.md#31-components)
  states the rule the correction follows: a collector takes the callee's
  identity from its verdict.
- **Not dumped.** The collectors' output for the subject was read from
  source, not printed. `dev`'s module row at the collector is that
  observation.
- **Owner: typecheck.** The backend's read is correct for what it is given.
- **Refuted if** a monomorphic selected candidate fails the same way, a
  polymorphic candidate with no second candidate does, or the collector is
  shown to demand the selected template for the subject.
- **Why coverage missed it.** The §8.6.5 band is recorded as partly
  assessed. No cell selects a polymorphic function by rule 3; the
  committed candidate-set cells select monomorphic functions, accessors or
  trait methods. T-1065-f reached it by accident, and its Phase 3 control
  (`then` in all three places) removed the second candidate together with
  the spelling, so it could not separate this defect from ACT-1065.

## Evidence allocation

`test`, in `tests/spec_08_modules.rs`, citing
`// spec: spec/08-modules.md §8.6.5` and
`// defect: class=carrier-loss locus=crates/cranelisp-typecheck/src/program/mono_collect.rs::collect_mono_call_sites found=S124 owner=/dev`:

- the subject above in `--run`, `--link` and the REPL, value 106, asserting
  no `undefined function` text;
- the value leg (`(app conv)` with `(defn app [g] (g 5 (fn [x] (add-i64 x 1))))`),
  every mode, value 106;
- the one-candidate control and the monomorphic two-candidate control,
  every mode.

`test` also re-traces the three T-1065-f cells
(`s124_1065_prelude_bind_{run,link,repl}`) to this filing: the same class
and locus as above in place of `routing-misclassify` and `is_bind_var`.
Their assertions do not change.

The twelve cells are committed (`de60dc3c`): the six subject legs fail on
their assertion and the six control legs pass (`qa`, full run at
`84719eb6`). They and the three T-1065-f cells carry the earlier
`candidate_selection.rs` locus; `test` replaces it with the one above.

`dev`(typecheck) owes a module row at the collector: two declarations of
one spelling, the polymorphic one selected, its instance demanded.

## Disposition

Fix or carry is the user's decision under METHOD §2.4. It does not end a
program on a signal. `qa` retains this intake.

## Completion evidence

Each subject leg and the three T-1065-f cells fail on `undefined function`
(or the value leg's message) before the correction and yield 106 after it,
in every mode; the controls pass throughout. `qa` then assesses the §8.6.5
band's rule 3.
