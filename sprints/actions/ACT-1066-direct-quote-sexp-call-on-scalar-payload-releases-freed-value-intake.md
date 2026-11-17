---
id: ACT-1066
title: A direct `quote-sexp` call on a scalar-payload `Sexp` aborts the debug build on a stack-placed operand
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-17
refers_to:
  - spec/09-macros.md
  - crates/cranelisp-intrinsics/src/drop.rs
  - crates/cranelisp-primitives/src/marshal.rs
  - sprints/actions/ACT-1049-rc-dec-check-stops-on-stack-placed-value-intake.md
  - tests/plan/s124-evidence-delta.md
---

## Observation

`qa`, on `target/debug/cranelisp` at `4b58ab93`, 2026-11-17, in scratch
directories. No prelude; `(import [primitives [*]])` and
`(import [macros [*]])`. Found while enumerating ACT-1063's extent.

`k` is `(defn k [s] (match s [(SexpList xs) 5 _ 0]))`.

| Leg | Program | Required | Observed |
|---|---|---|---|
| Subject, `--run` | `(defn main [] (Pure (k (quote-sexp (SexpInt 3)))))` | exit 5 | abort (134): `STALE RC DEC (drop glue): dec of non-live heap pointer` |
| Subject, REPL | `(quote-sexp (SexpInt 3))` | the quoted form displayed | the same abort; the session ends |
| Subject, REPL | the operand `(SexpInt 3000)`, `(SexpBool true)`, `(SexpFloat 1.5)`, or `(SexpInt 3)` bound by `let` first | displayed | the same abort, each |
| Control: the payload | `(quote-sexp (SexpStr "abc"))`, `--run` | exit 5 | exit 5; 9 allocations, 9 frees |
| Control: the payload, REPL | `(quote-sexp (SexpSym "a"))`, entered twice | displayed | as required |
| Control: the call route | `(let [q quote-sexp] (Pure (k (q (SexpInt 3)))))`, `--run` | exit 5 | exit 5; 9 allocations, 9 frees |

Every subject failed on each run.

## Classification: a defect, not memory-unsafe

- **Requirement.** [Spec §9.11.1](../../spec/09-macros.md#9111-quote-sexp):
  `quote-sexp` converts a `Sexp` into the form that reconstructs it. The
  section's own example is `(quote-sexp (SexpInt 42))`. The debug build
  aborts on it.
- **The filed title was wrong.** No freed value is released. The record
  keeps its file name.

## Attribution (qa, 2026-11-17, re-attributed)

The lead is `design`(backend)'s reading and the coordinator's probe; `qa`
re-ran it at `4b58ab93`.

| Observation | Result |
|---|---|
| The `--run` subject with `CRANELISP_NO_STACK_ALLOC=1`, `CRANELISP_RC_DEC_CHECK=1` | exit 5; 8 allocations, 8 frees, `stack_slot=0` |
| `CRANELISP_CODEGEN_DUMP` of the subject's `main` | the `SexpInt` is built in `ss0`, its header is `0x4000_0000_0000_0000` (immortal), and `stack_addr ss0` is the shim's argument |
| The abort's pointer | a stack address |
| `target/release/cranelisp` (built 2026-11-15; commit not checked) on the subject | exit 5 |
| The two filed controls (`SexpStr` operand; the function-value route) | `stack_slot=0`: neither operand is stack-placed |

- **Mechanism, confirmed by a control differing only in placement.**
  `marshal.rs::quote_sexp` builds a fresh result and releases its operand.
  The operand is stack-placed, so that release reaches
  `drop.rs::atomic_dec_rc`, whose debug-build assertion requires a tracked
  live allocation. A stack slot is never tracked. The immortal header
  makes the release itself harmless.
- **It is [ACT-1049](ACT-1049-rc-dec-check-stops-on-stack-placed-value-intake.md)'s
  mechanism at a second check.** ACT-1049's check is armed by an
  environment variable; this one is always on in a debug build, so an
  ordinary program stops.
- **Correction: none of its own.** Stack placement retires in S124 (packet
  row D5, backend change-set B1). The drop-glue assertion is then right
  as written and stays.
- **Refuted if** the subject still aborts on the B1 tree, or the slot's
  header is found to reach zero.
- **Not probed.** `--link`; a call inside a macro body; which other
  consuming host primitives can receive a stack-placed operand. B1 removes
  the placement for all of them.

## Request

- `test` commits REPRO-1066
  ([evidence delta §3.10](../../tests/plan/s124-evidence-delta.md#310-repro-1066--a-direct-quote-sexp-call-aborts-the-debug-build))
  in the S124 evidence wave.
- No scheduling decision is needed: the correction is in S124's approved
  scope.

## Completion evidence

REPRO-1066 fails on the abort, then passes in every mode on the B1 tree
with its two controls and no change made for it. `qa` then deletes this
record.
