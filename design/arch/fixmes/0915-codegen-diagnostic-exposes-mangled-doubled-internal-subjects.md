---
number: 0915
target: /arch
filed_by: /repl
filed_at: 2026-07-26
sprint_filed: 118
refers_to: crates/cranelisp-backend/src/error.rs;
  src/main.rs;
  design/backend/non-concrete-release-contract.md §7.2.1;
  design/int/int.md §9.1;
  repl/spec/05-error-presentation.md
status: deferred
ruled_at: design/backend/non-concrete-release-contract.md §3.4 (R-4), §7.2
---

## S125 disposition (`design`(backend), 2026-11-27): re-targeted to `arch`

Verified against source in the working tree:

- **Backend half resolved.** `crates/cranelisp-backend/src/error.rs`:
  `codegen_failed` and `module_failed` split the inner error into
  `cause` and `location`, so the only located prefix is the one rendered
  outward (Rule 1). `CodegenFailed` renders `codegen failed for {symbol} in
  {module}`, with the module a separate noun and no `{module}/{symbol}`
  composition (Rule 3). `crates/cranelisp-backend/src/drop_glue.rs` uses
  `Span::SYNTHETIC` only inside its `#[cfg(test)]` modules (Rule 2). Landed
  at `a9a8c0c6` and `36e64f27`, with row B15 at `9bee5930`
  (release contract §7.2.1). Nothing remains for the backend.
- **Open: the subject face (item 4).** The rendered noun is still
  `__expr` or an instance key (`qa`, S124 evidence delta §14.8: `codegen
  failed for __expr in user: …`). The int §9.1 ruling puts the projection
  at the binary's formatter, but the subject reaches `src/` only as the
  backend's rendered text through `From<CompilationError> for
  CranelispError` (`error.rs`). A projection there would re-parse that
  text, which §9.1 forbids. Realising it needs the subject to travel as data
  on the outward error, a public change in types and the backend.
- **Re-targeted to `arch`** to decide that carrier. `design`(int) then
  designs the projection at the formatter. `dev`(`src/`) builds it with the
  module row `qa` allocated (S124 evidence delta §14.8). Trigger:
  scheduling of the binary's half. The falsifier is unchanged: a public
  codegen error whose subject is `__expr` or an instance key.
- Opened: `error.rs`, `drop_glue.rs` (its `Span::SYNTHETIC` sites and test
  boundary), release contract §7.2–§7.2.1, int.md §9.1, S124 evidence delta
  §14.8 and its backend row, S125 evidence delta.

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

Backend half designed 2026-11-20 at
`design/backend/non-concrete-release-contract.md` §7.2.1: the rules, three
RED rows and the correction. Its unattributed case (no failing member) is
returned to `arch` there.

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
