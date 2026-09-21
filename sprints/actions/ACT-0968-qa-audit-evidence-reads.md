---
id: ACT-0968
title: Pin the pattern-seam keyed-miss arms that backend S110 R2 left unguarded
status: open
priority: advisory
from: qa
to: dev
sprint: 122
filed_at: 2026-09-21
refers_to:
  - crates/cranelisp-backend/src/compiler/match_codegen.rs
  - crates/cranelisp-backend/src/compiler/apply/keyed_miss_tests.rs
  - crates/cranelisp-frontend/src/ast_builder.rs
  - tests/plan/s122-evidence-delta.md
---

## Request

`qa` read the two retired audit recommendations this action was filed for.
Frontend S113 R1 and R7 are discharged, and backend S110 R2 is discharged for
the call and value seams; the
[evidence read](../../tests/plan/s122-evidence-delta.md#retired-audit-evidence-reads--frontend-s113-r1r7-backend-s110-r2)
names the covering tests and states the allocation below. What survives:

1. **`dev` on `cranelisp-backend` — two module cells.** Neither hard-miss arm
   of `compile_constructor_pattern` is asserted by any test: carrier-`None`
   ("no resolved_ctor carrier") and entry-miss ("has no Def"). Add one cell per
   arm beside the `match_codegen.rs` fixture that populates `pattern_ctors`,
   in the shape of the KC-N1/N2 call-seam cells.
2. **Rider, `dev` on `cranelisp-frontend` — one assertion.** No cell names the
   bare-arm lowercase `deftype` head reject (`(deftype point …)`). Add it when
   `ast_builder/tests.rs` is next open; it does not warrant its own dispatch.

## Completion evidence

- Each backend cell asserts a `CodegenError` naming the constructor and its
  message family, and the unmodified fixture still compiles. If the harness
  refuses a carrier-less pattern before codegen, `dev` reports which seam
  fired and `qa` re-reads the allocation.
- The rider asserts a located reject with the uppercase twin accepted.
- `dev` reports the cells to `qa`, which removes the limit lines from the
  evidence read; `dev` deletes this action.
