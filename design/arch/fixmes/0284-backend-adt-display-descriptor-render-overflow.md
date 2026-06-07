---
number: 0284
target: /dev (backend)
filed_by: /qa
filed_at: 2026-06-07
sprint_filed: 76
refers_to: tests/trace.rs::{trace_polymorphic_adt_result_renders,trace_adt_value_render_overflows_defect} (FAILING), crates/cranelisp-backend/src/compiler/trace_codegen.rs (bake_adt/bake_descriptor), crates/cranelisp-intrinsics/src/trace.rs (formatter walk), design/arch/tracing.md §3.4
status: open
---

# Tracing any fn returning a user ADT stack-overflows the DisplayDescriptor render

## Issue

Tracing a fn that returns a user ADT value — even nullary `None` — STACK
OVERFLOWS at trace-format time. The Wave-1.5 gate's NOTE-1 "production-baker
round-trip gap" turns out to be a crash, not merely an unverified path: the
production `bake_adt`/`bake_descriptor` ctor-table assembly (or the intrinsics
walk over its output) recurses unboundedly. The backend's in-crate round-trip
unit tests passed because they hand-built blobs with the low-level primitives
rather than exercising the production baker (exactly the gap NOTE-1 named).

Failing tests: tests/trace.rs::trace_polymorphic_adt_result_renders,
trace_adt_value_render_overflows_defect.

ALSO (possibly same root, possibly distinct):
tests/trace.rs::trace_trait_heavy_prelude_overflows_defect — trace swap-all
over the trait-heavy TestStandard prelude overflows on a nice-worker thread
(Num+Eq+Ord alone fine; full prelude not — bisection open). The worker-thread
signature may implicate descriptor baking at scale or the lenient spark path.

## Proposed resolution

Triage with a small CLIF/blob dump first (the depth-16 TypeVar degrade was
supposed to bound recursion — verify it actually fires in the production
baker; check whether the recursion is bake-side (cyclic TypeDefInfo
substitution — cf. FIXME 0279's cyclic-subst family in typecheck) or walk-side
(blob with self-referential offsets). Fix at the right layer; the in-crate unit
tests gain a production-baker round-trip (bake via the real entry points, not
hand-built blobs).

## Operational implication / Context

Blocks ADT rendering in trace trees (a core §4.12 capability). S76 W4 or S77.
The failing tests are the durable record.
