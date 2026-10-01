---
id: ACT-1017
title: Locate a failed-dependency refusal in the right file, with one located prefix
status: deferred
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - repl/spec/05-error-presentation.md
  - src/scheduler.rs
  - design/int/int.md
---

## Disposition

- User-approved carry from S122 to S123 on 2026-09-30: “yes” to carrying
  this diagnostic finding. First deferral; owner `qa`, revisit at S123 intake.
- The compiler correctly refuses the dependency, but the misleading source
  location and repeated prefix remain accepted residuals until correction.
  Requirements and the unresolved classification of the prefix are unchanged.
- Disposition verification: reopened REPL §5.1 and
  `src/scheduler.rs::refuse_failed_dependency_locked`; it copies the stored
  error's span and rendered message into a new error with no file.
- This carry covers ACT-1017 only. It does not dispose of ACT-1015.
- **Widened reach (qa, 2026-09-30, Phase-6a intake).** This was observed
  with the binary built after `88bbbd12`, on a fresh scratch project. It
  widens the evidence only; the carry and the open §5.5 reading are unchanged.
  - **Batch `--run`, dependency failure.** An entry imports a module `helper`
    that has a type error. The diagnostic prints
    `p.cl:1:14: error: module error at 13..22: module 'helper' failed: type error at 13..22: …`.
    That is `helper.cl`'s span rendered as a line and column of `p.cl`, the
    same location face.
  - **Batch `--link`, same program.** It prints
    `p.cl:1:1: error: module error at 0..0: module 'p' failed: module error at 0..0: dependency 'helper' failed: type error at 13..22: …`.
    That has three category prefixes and a `0..0` span. CLI §0.2.1 limits
    parity to execution output, so this difference between modes is not a
    parity defect.
  - **Entry-module failure** (reported by `training`). A type error in the
    entry itself prints
    `p.cl:1:21: error: module error at 20..29: module 'p' failed: type error at 20..29: …`.
    The location is correct. It repeats the span under two categories, and
    the prefix belongs to the same §5.5 scope question.
  - **REPL session end (qa, 2026-10-01, Phase-6b intake).** `docs` reported
    this and QA reproduced it. `user.cl` imports `sq` from `math.cl`, and
    `math.cl` is saved with a type error at 13..39. After `/quit`, stderr
    prints
    `user.cl:1:14: error: module error at 13..39: module 'user' failed: module error at 13..39: type error at 13..39: …`.
    That is `math.cl`'s span rendered as a line and column of `user.cl`, with
    three prefixes. The in-session `[errors: user.cl]` notice carries the same
    span under `user.cl`'s header. Whether the REPL should print this line and
    exit 1 at all is a separate spec question, routed through `sprint`. This
    record covers only its location and prefix.

## Request

The scheduler's fail-fast refuses an attempt that depends on a failed module.
Its diagnostic is mislocated and repeats its prefix. This intake is carried under the disposition above. It does not gate ACT-1014.

- **Source.** `refuse_failed_dependency_locked` in `src/scheduler.rs`, on
  source `f0d1006f…`, dirty on `e4062202`.
  - It builds its location from the failed module's own error span, with no
    file.
  - It wraps that stored error's `to_string()` in a new `ModuleError`.
- **Observed** in `dev`'s helper-end row output
  (`.local/s122-helper-followon-dev-result.md`):

  ```text
  [errors: prelude.cl] … module 'prelude' failed: module error at 0..15: module error at 0..15: circular dependency detected: x -> prelude -> x
  ```

  - `0..15` is a span of `x.cl`, shown under the `prelude.cl` header.
  - `module error at 0..15:` appears twice.
- **Reach.** The qualified-reference fail-fast and `block_for_typecheck`
  already had both behaviours. Since the ACT-1014 correction, every Pass-0
  `import` or `export` of a failed module has them too.
  - Before that correction, the `import` refusal was located at the
    declaration, in the dependent's own file.
- **Requirements.**
  - REPL §5.1: an error displays its source location. A span shown under
    another file's header does not locate the error.
  - REPL §5.5 forbids a nested wrapper that repeats a category-and-span
    prefix. That section names monomorphisation, code generation and
    linking. Whether it also governs module-load diagnostics is a reading for
    `spec`. If it does not, the prefix face is a usability finding.
- **Impact.** The refusal itself is correct and names the cycle or the
  failed module. A user is sent to the wrong offset in the wrong file.

## Completion evidence

1. `sprint` and the user dispose of this under METHOD §2.4.1: fix now or
   defer with a reason.
2. If it is fixed:
   - `design`(int) chooses the location: the reference site in the
     dependent's file, or the failed module's span with its own file.
     `design` also corrects §6.11's "only the message changes" wording.
   - `test` commits an e2e cell that is observed RED before the fix. A
     reload refuses an `import` of a failed module, and the notice must
     carry one located prefix and a location in the named file.
   - `dev` adds a unit row at `refuse_failed_dependency_locked` for the
     location and the single prefix.
3. `spec` rules on §5.5's scope before the prefix face is classed as a
   defect.
