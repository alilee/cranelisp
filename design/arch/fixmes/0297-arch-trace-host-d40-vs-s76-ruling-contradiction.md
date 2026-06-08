---
number: 0297
target: /arch
filed_by: /qa
filed_at: 2026-06-08
sprint_filed: 76
refers_to: design/arch/facades/cranelisp-intrinsics-audit-s69.md, design/arch/tracing.md §4.3, design/arch/decisions/0040-runtime-trace-io-trace-relocate-to-int.md (PARTIAL-RETRACTION BOX), tests/facade_pif_rows.rs::row_33_trace_bodies_hosted_in_intrinsics_pub_api
status: open
---

# Cascade: intrinsics facade is silent on the trace family (hosted there per tracing.md / D0040 retraction)

## Issue

The trace-host question is **already settled in the design** — this is a
cascade gap, not an open arbitration:

- **Decision 0040** carries a PARTIAL-RETRACTION BOX (S76, user-decided
  2026-06-04): the `(trace ...)` half is retracted; the 12 `cranelisp_trace_*`
  bodies + `trace_format` relocate **back to `cranelisp-intrinsics`** and
  publish via `intrinsics_table()`; `src/trace.rs` deletes.
- **`design/arch/tracing.md`** (§§1–6, §4.3) is the canonical target-state:
  the trace bodies/table/runtime-guard live in `crates/cranelisp-intrinsics/src/trace.rs`.
- The as-built agrees: `crates/cranelisp-intrinsics/public-api.txt` carries 43
  `cranelisp_intrinsics::trace::` lines (baseline regenerated this sprint, zero
  diff).

`/qa` has already fixed the conformance test to the settled contract —
`tests/facade_pif_rows.rs::row_33_trace_bodies_hosted_in_intrinsics_pub_api`
now asserts the trace family IS present in `cranelisp_intrinsics::trace`
(citing tracing.md §4.3), and it passes.

The residual gap: the **intrinsics facade** (`design/arch/facades/cranelisp-intrinsics-audit-s69.md`)
does **not document the trace family hosting** — a `grep -i trace` over it
returns nothing. The tracing.md ruling was never cascaded into the intrinsics
facade's surface description.

## Proposed resolution

`/arch` to cascade `tracing.md` §4.3 into the intrinsics facade (the
manifestation site a future reader expects — `feedback_manifestation_site_question`):
document that `cranelisp-intrinsics` hosts the trace family
(`cranelisp_intrinsics::trace::*`, the 12 `cranelisp_trace_*` bodies +
`trace_format` + `TRACE_STACK`/`TRACE_THREAD_ID` + the nesting guard),
published via `intrinsics_table()`. No test change is needed — row_33 already
asserts the settled contract.

## Operational implication / Context

Surfaced while `/qa` modernized `facade_pif_rows.rs` against cargo-public-api
0.51.0. Not a blocker — the design and as-built are unambiguous and the test
already matches them; this only closes the facade-prose cascade so the
intrinsics facade reflects the post-S76 trace hosting.
