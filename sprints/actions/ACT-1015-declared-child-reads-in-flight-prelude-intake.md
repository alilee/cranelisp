---
id: ACT-1015
title: Compile a declared child that keeps the implicit prelude import only after the prelude, in every mode
status: deferred
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - spec/08-modules.md
  - design/int/int.md
  - src/process_form.rs
---

## Disposition

- User-approved carry of the investigation from S122 to S123 on 2026-09-30:
  “agree carry for 1015”. First deferral; owner `qa`, revisit at S123 intake.
- This remains an unconfirmed scheduling concern, not a reproduced defect.
  Retain the reproduction plan below; requirements are unchanged.
- Disposition verification: reopened int §6.12's barrier/declared-child
  explanation and `src/process_form.rs`'s submodule-driving sequence after
  parent publication. These support the lead, not an execution claim.
- At S123 intake, QA routes the bounded reproduction before selecting a fix.

## Request

A suspected defect, reported by `design` and not yet measured. It is intake
carried to S123 under the disposition above. It does not gate ACT-1014.

- **Requirement.**
  - Spec §8.8.1: the implicit import has the effect of `(import [prelude [*]])`
    and is a dependency on `prelude`.
  - §8.8.2 and §8.10.3: the prelude is fully processed before a dependent
    begins.
  - The root memory: a fresh load and a reload of the same files must agree.
- **Suspected face.**
  - A module that the prelude depends on declares a child with `mod`, and the
    child keeps the implicit import. That child compiles while the prelude is
    in flight and reads the prelude's incomplete table.
  - A bare use of a prelude name that the prelude does not yet hold would
    fail unresolved at fresh load, while the same source compiles on reload.
  - The stdlib shape, where the prelude re-exports modules with `(mod- test)`
    children, is exposed.
- **Stated mechanism (a hypothesis).**
  - A parent waits for its declared children before it becomes terminal (the
    FIXME 0342 deferral at `src/process_form.rs`). The child therefore cannot
    wait for the prelude without deadlocking the path from the prelude
    through the parent to the child.
  - [Int §6.12](../../design/int/int.md#612-the-implicit-prelude-dependency)
    records the behaviour as predating the prelude ruling.
- **Open question.** How complete the in-flight table is may depend on
  interleaving. If it does, the class is `shared-state-write-race` rather
  than `wrong-reject`.

## Completion evidence

1. `test` reduces a spec-traced reproduction and reports whether it fails, and
   whether it fails deterministically. The reproduction shape:
   - the prelude re-exports `a` and defines `helper`;
   - `a` null-imports the prelude and declares `(mod- t)`;
   - `a.t` calls `helper` bare;
   - the entry loads `a.t`;
   - `--run` and REPL startup are compared with a reload of `a/t.cl`.
2. If it reproduces, QA attributes the defect with a discriminating control,
   and `sprint` disposes of it in Phase 5. If it does not reproduce, QA records
   the negative and resolves this action.
