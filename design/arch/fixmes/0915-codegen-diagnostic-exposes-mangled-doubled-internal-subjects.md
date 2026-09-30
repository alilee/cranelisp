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
  repl/spec/05-error-presentation.md
status: deferred
ruled_at: design/backend/non-concrete-release-contract.md §3.4 (R-4), §7.2
---

## S122 disposition (user-approved 2026-09-30)

Under the [approved S122 disposition](../../../tests/plan/s122-evidence-delta.md#final-disposition-proposal-2026-09-30):

- **Carried to S123 (K9, C5).** Owners: `design`(backend) and `design`(int).
  Falsifier: any public codegen error. No deferral count is recorded.

# A codegen-stage failure is presented with a `0..0` span, a doubled prefix and an internal subject

## Requirement

`repl/spec/05-error-presentation.md` §5.5: a compiler-stage diagnostic is
located at the user's form, names its subject as the user would write it, and
carries one located category prefix.

## Current state (backend loci re-verified 2026-09-30)

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
  refusal (FIXME 0907); no legitimate public trigger exists. The user's D1
  ruling (2026-09-10) accepts the private failed-turn witness in
  `src/worker/tests.rs` without public codegen-failure reachability. That
  witness obtains a production `CodegenFailed` at a prepared target and checks
  its module and symbol, not its presentation. Once the frame lands, the
  contract's `/review` reject 7 applies.

## Closure

Backend and int halves land with unit rows. If a public codegen error appears,
it becomes this frame's public witness.
