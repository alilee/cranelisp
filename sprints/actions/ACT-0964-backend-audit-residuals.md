---
id: ACT-0964
title: Dispose the backend audit residuals — release-silent keying arms, drop-glue builder convergence, retired-facade citations
status: open
priority: advisory
from: audit
to: design
sprint: 122
filed_at: 2026-09-21
refers_to:
  - design/backend/backend.md
  - crates/cranelisp-backend/src/compiler/context.rs
  - crates/cranelisp-backend/src/compiler/match_codegen.rs
  - crates/cranelisp-backend/src/compiler/literals.rs
  - crates/cranelisp-backend/src/lib.rs
  - design/backend/compile-to-module.md
---

## Request

Provenance: the S110 `cranelisp-backend` whole-context assessment
([historical assessment](https://github.com/alilee/cranelisp/blob/57253cf2/audits/cranelisp-backend-s110.md), §3 R3, R4, R6, R8). Its
disposition trail was never written. `sprints/archive/sprint-111.md` records a
user "SHIP ALL" ruling for the fourth-audit items and a must-ship subset (R7,
R2, R4); R3 appears in neither list. R2, R4, R5 and R7 have since landed in
source (keyed-miss tests, single `build_isa`, split funnels, fallible GOT
allocation with `got_exhaustion_surfaces_error_not_ub`). What remains is
**pending disposition, not approved implementation**:

1. **R3 — two release-silent keying-drift arms.** Unchanged since S110:
   `constructor_metas` drops a constructor on a both-probes miss behind a
   `debug_assert!` (`compiler/context.rs`), and `concrete_field_types` returns
   an empty vector on an already-validated key miss (`compiler/match_codegen.rs`,
   two arms). The value-seam entry miss still reports "undefined variable"
   (`compiler/literals.rs`). The audit's concern: a keying drift feeding
   drop-glue/heap classification degrades to a leak in release builds rather
   than an error. No failing behaviour is observed, so this is not `qa` defect
   intake. `design/backend/backend.md` ("Two soft arms remain…") now records
   the opposite design position — it accepts the release-build skip under
   `design/arch/dotted-ctor-canonical-keys.md` §10.5. The audit recommendation
   and that design text disagree, and the user has ruled on neither. Question
   for `design` (backend) to put to the user through `sprint`: confirm the
   accepted-skip position (decline R3, recording why a leak-grade miss is
   tolerable), or harden both arms to fail in every profile.
2. **R6 — one drop-glue emission discipline.** Naming identity is single-homed
   (`compiler/resolution.rs` closure/curry glue names; the identity test calls
   the production functions), which closes the S107 caveat. Whether the
   closure, auto-curry and Vec glue *builders* should share one emission
   skeleton was not re-assessed after ADT glue moved to `drop_glue.rs`.
   `design` (backend) states converge-or-keep with a reason.
3. **Retired-facade citations and stale source rustdoc (R4/R8 residue, S87
   F9).** Backend source still cites the retired architecture-facade directory,
   including the four `jit.rs` sites identified by the audit. The crate-root
   rustdoc also needs reconciliation with current GOT publication, body access
   and object-loading behavior. The S122 design-side cleanup is complete:
   backend designs no longer cite retired facades, and
   `design/backend/compile-to-module.md` §8 describes the surviving private
   `FunctionArtifacts` carrier. The source-side obligation remains open.

## Completion evidence

- Item 1: a user decision recorded in `design/backend/backend.md` beside the
  soft-arms paragraph (accepted residual with its falsifier, or the hardened
  arms with a unit test per arm per `sprints/METHOD.md` §2.2).
- Item 2: converge-or-keep stated in the backend master with its reason.
- Item 3: no backend source or live `design/backend/` document cites a retired
  facade file; the `FunctionArtifacts` statement matches source.
