---
number: 0915
target: /design (backend)
filed_by: /repl
filed_at: 2026-07-26
sprint_filed: 118
refers_to: crates/cranelisp-backend/src/error.rs;
  crates/cranelisp-backend/src/drop_glue.rs;
  design/backend/non-concrete-release-contract.md §3.4, §7.2;
  design/int/int.md §9.1;
  repl/spec/05-error-presentation.md;
  sprints/actions/ACT-0958-rearm-failed-turn-recovery-coverage.md
status: open
ruled_at: design/backend/non-concrete-release-contract.md §3.4 (R-4), §7.2
---

# A codegen-stage failure is presented with a `0..0` span, a doubled prefix and an internal subject

## Requirement

`repl/spec/05-error-presentation.md` §5.5: a compiler-stage diagnostic is
located at the user's form, names its subject as the user would write it, and
carries one located category prefix.

## Current state (verified 2026-09-24)

In the S118 specimen, `codegen error at 0..0:` appeared twice and the subject
rendered as the module-doubled, `$`-mangled instance of a user function
`then`. The frame defects remain in source:

- **Doubled prefix** — `CompilationError::CodegenFailed` carries a
  pre-rendered cause that already embeds the inner located prefix.
- **Doubled subject** — `error.rs` composes `"codegen failed for {}/{}"` over
  a monomorphised instance symbol that already carries its module.
- **`0..0`** — `drop_glue.rs` raises registry errors at
  `ErrorLocation::from_span(Span::SYNTHETIC)`; the spans exist on the
  `MonoExpr` nodes.
- **Internal subject** — `__expr` and `$`-mangled instance names reach the
  user.

## Remaining obligation

- **Backend** (contract §7.2): one prefix fixed structurally at the wrapping
  construction, never by re-parsing text; a real span on every registry error;
  no module re-composition over an already-qualified symbol.
- **Binary/int** (`design/int/int.md` §9.1): one subject-presentation
  projection at `format_error` (`__expr` → the entered form, `f$T…` → `f`),
  a projection and never a resolver; the carrier symbol stays unchanged.
- **Evidence.** Every public trigger of this frame was the since-delivered IO
  refusal (FIXME 0907). The S122 private Q1/D1 fixture now yields a real
  `CodegenFailed` at a prepared target but no public trigger exists;
  ACT-0958 owns returning the public-testability decision to the user.
  Once the frame lands, the contract's `/review` reject 7 applies.

## Closure

Backend and int halves land with unit rows, and the evidence decision under
ACT-0958 is recorded.
