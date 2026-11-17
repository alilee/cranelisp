---
id: ACT-1067
title: An expression nested about 56 forms deep overflows the compile worker's stack and aborts the compiler
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-17
refers_to:
  - spec/12-runtime.md
  - tests/plan/s124-evidence-delta.md
---

## Observation

Found by `qa` on 2026-11-17 while building a fixture for the spec §3.10
instantiation depth limit. Checkpoint `main` at `4b58ab93`,
`target/debug/cranelisp`, scratch directories, no prelude,
`(import [primitives [*]])`.

`main` is `(defn main [] (Pure E))`, where `E` is `(add-i64 1 (add-i64 1 … 0))`
nested `n` deep.

| Leg | Program | Required | Observed |
|---|---|---|---|
| Subject | `n` = 56, 60, 64, 100, `--run` | exit `n` | abort, exit 134: `thread 'priority-worker-0' … has overflowed its stack` |
| Control | `n` = 48, 52 | exit `n` | as required |
| Subject, never compiled to code | the `n` = 100 expression as the body of an uncalled `(defn f [x] …)` | exit 5 from `main` | the same abort |
| Subject, never evaluated | the `n` = 100 expression quoted in the body of an uncalled `defmacro` | exit 5 | the same abort |
| Subject, constructors | `(Yep (Yep … 0))` over `(deftype (Opt a) Nope (Yep [:a v]))`, `n` = 56, 64 | exit 5 | the same abort |
| Control: the depth is syntactic, not the type's | the same `(Opt … Int)` value built by a flat `let` chain, type depth 64, 65 and 100 | exit 5 | as required |
| Control: stack size | subject `n` = 100 with `RUST_MIN_STACK=268435456` | exit 100 | exit 100 |
| Release build | `target/release/cranelisp` (built 2026-11-15, commit not checked), `n` = 64 | exit 64 | exit 64; `n` = 200, 1000 and 5000 abort the same way |

Each leg is one run.

## Classification

**A defect.** No specification clause limits the nesting depth of a source
expression, so each subject is a legal program. The compiler dies on a signal
with a Rust runtime message, where REPL §5.1 requires every refusal to carry
an error category and a location. [Spec §12.7.2.1](../../spec/12-runtime.md#12721-panic-sources)
covers stack exhaustion of the running program, not of the compiler.

## Attribution: provisional

- **Observed.** The failing thread is the compile worker. The threshold moves
  with the build profile and with the thread's stack size, so the fault is
  recursion depth proportional to the nesting of the source form against a
  fixed worker stack, not unbounded recursion.
- **Observed.** The form need not be typechecked into an instance, emitted or
  evaluated: the uncalled function and the quoted macro body abort alike.
- **Not observed: the stage.** Every stage that walks a form recursively is on
  that thread. The quoted leg points at or before the stage that first walks
  a quoted body. No backtrace was taken.
- **Refuted if** a build with the reader and the AST builder made iterative,
  or run on a larger stack only for those stages, still aborts at the same
  depth.
- The receiving role probes before placing a correction.

## Request

1. `sprint`: a scheduling decision. The correction is not in S124's scope.
2. `test`: REPRO-1067, in [the evidence delta §3.11](../../tests/plan/s124-evidence-delta.md#311-repro-1067--a-deeply-nested-expression-aborts-the-compiler).
3. Whether the language states a nesting limit, and its floor, is a normative
   question for `spec` to frame for the user. The reproduction asserts only
   that the compiler does not die on a signal.

## Completion evidence

The REPRO-1067 subjects yield their values, or a located diagnostic if a
ruled limit refuses them, in every mode and both build profiles; no leg ends
on a signal.
