---
id: ACT-0968
title: Pin the bare-arm lowercase `deftype` head reject (the backend pattern-seam arms are pinned)
status: open
priority: advisory
from: qa
to: dev
sprint: 122
filed_at: 2026-09-21
refers_to:
  - crates/cranelisp-frontend/src/ast_builder.rs
  - tests/plan/s122-evidence-delta.md
---

## Request

`qa` read the two retired audit recommendations this action was filed for.
Frontend S113 R1 and R7 are discharged, and backend S110 R2 is discharged for
the call and value seams; the
[evidence read](../../tests/plan/s122-evidence-delta.md#retired-audit-evidence-reads--frontend-s113-r1r7-backend-s110-r2)
names the covering tests and states the allocation below. What survives:

1. **`dev` on `cranelisp-backend` — discharged.** Both pattern-seam arms
   are asserted (`qa`, read at `4cef5784`):
   `match_codegen.rs::a_constructor_pattern_with_no_carrier_is_a_codegen_error`
   (`9bb1f0aa`) and
   `context/keyed_read_hardening_tests.rs::a_missed_pattern_constructor_key_is_an_error_not_no_fields`.
2. **Rider, `dev` on `cranelisp-frontend` — one assertion.** No cell names the
   bare-arm lowercase `deftype` head reject (`(deftype point …)`). Add it when
   `ast_builder/tests.rs` is next open; it does not warrant its own dispatch.

## Completion evidence

- The rider asserts a located reject with the uppercase twin accepted.
- `dev` reports the cell to `qa`, which removes the rider's limit line from
  the evidence read; `dev` deletes this action.
