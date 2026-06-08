---
number: 0297
target: /arch
filed_by: /qa
filed_at: 2026-06-08
sprint_filed: 76
refers_to: tests/facade_pif_rows.rs::row_33_trace_observer_absent_from_intrinsics_pub_api, src/CLAUDE.md §"Test discovery" (S76 trace ruling 2026-06-04), design/arch/facades/cranelisp-intrinsics-audit-s69.md, crates/cranelisp-intrinsics/public-api.txt
status: open
---

# Trace family host — Decision 40 ("trace in int") contradicts the S76 trace ruling ("trace in intrinsics")

## Issue

`tests/facade_pif_rows.rs::row_33_trace_observer_absent_from_intrinsics_pub_api`
asserts ZERO `cranelisp_intrinsics::trace::*` lines in the intrinsics
public-api baseline, on the basis of pre-S76 Decision 40 ("trace observer
relocates to `int`"). The S76 trace ruling reverses this:

> src/CLAUDE.md (S76 trace ruling 2026-06-04): "the trace family —
> `cranelisp_trace_format` + the 12 `cranelisp_trace_*` bodies — also LEFT
> int. It lives in `cranelisp_intrinsics::trace`, published via
> `intrinsics_table()`, registered by `Jit::new`. `src/trace.rs` is deleted."

`crates/cranelisp-intrinsics/public-api.txt` correctly reflects the ruling:
it carries 43 `cranelisp_intrinsics::trace::` lines. The committed baseline
was regenerated this sprint (`cargo +nightly public-api -s --omit
auto-derived-impls` → zero diff), so the baseline is current and authoritative.

So the test's expectation is **superseded** — trace lives in intrinsics, not
int. But flipping the assertion (`== 0` → `> 0`, or relocating it to assert
trace IS in intrinsics) is a facade-authority call, not a `/qa` call: it
depends on Decision 40's current disposition and whether the intrinsics
facade now hosts the trace family. `/qa` has left the test failing-not-ignored
rather than decide this.

## Proposed resolution

`/arch` to arbitrate:

1. Confirm Decision 40's current disposition — is "trace observer relocates
   to int" retracted/amended by the S76 trace ruling, and if so where is the
   amendment recorded (the manifestation site a future reader expects)?
2. Decide the intrinsics facade's host claim for the trace family
   (`cranelisp_intrinsics::trace::*`, 43 baseline lines).
3. Direct `/qa` on the test's correct form — most likely: invert row_33 to
   assert the trace family IS hosted in `cranelisp_intrinsics::trace` (the
   S76 target state), paired with a negative guard that `src/trace.rs` /
   `cranelisp_intrinsics::io_trace` shapes are absent. row_30
   (`io_trace` absent from intrinsics) is a separate concern and currently
   passes — confirm io_trace's disposition is unchanged by this.

Once `/arch` rules, `/qa` updates the test to match the ruled facade.

## Operational implication / Context

This is the only row in `facade_pif_rows.rs` whose failure is NOT
format-staleness or an unmet PIF that the test already correctly tracks. It
is a genuine facade-authority contradiction surfaced while modernizing the
file against cargo-public-api 0.51.0. The test stays failing-not-ignored
(per `memory/feedback_failing_not_ignored.md`) until `/arch` rules; it is the
durable record of the D40-vs-S76 contradiction.
