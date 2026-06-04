---
number: 0258
target: /qa
filed_by: /arch
filed_at: 2026-06-04
sprint_filed: 76
refers_to: design/arch/tracing.md §2.5 §3.5.1 §5.2 §6, tests/ring4_trace.rs, spec/04-expressions.md §4.12.5 §4.12.9 §4.12.3
status: open
---

# Trace integration tests: nested-trace runtime error, linked-binary trace e2e, swap-all visibility expectations

## Issue

The 2026-06-04 trace ruling changes three observable behaviours that the integration suite asserts.
Existing `tests/ring4_trace.rs` expectations must change, and new e2e coverage is needed for `--link`.

## Proposed resolution

1. **Nested-trace runtime error** (spec §4.12.5, `tracing.md` §6). The existing
   `tests/ring4_trace::trace_nested_single_trace` (which asserts "outermost wins, single tree") is now
   WRONG against the spec — rewrite it to assert that `(trace (trace expr))` raises a **runtime error**
   (the §12.7 panic path) with the "nested trace is not supported" message. Add a second test for the
   **dynamic** case — `(trace (f))` where `f`'s body contains `(trace …)` — which must also raise (the
   reason the guard is runtime, not lexical). Both `// spec: spec/04-expressions.md §4.12.5`.

2. **Linked-binary trace e2e** (spec §4.12.9, `tracing.md` §2.5). Trace now works in `--link`. Add an e2e
   test that builds a standalone binary with `--link` containing a `(trace …)` form and runs it,
   asserting the trace produces a real tree (NOT the prior "undefined symbol cranelisp_collect_trace"
   link failure). This is the inverse of whatever test currently asserts the `--link` rejection — that
   rejection test must be RETIRED (the rejection no longer exists). `// spec: spec/04-expressions.md
   §4.12.9`.

3. **Swap-all visibility expectations** (spec §4.12.3, `tracing.md` §3.5.1 + §5.2). Discovery now swaps
   ALL symbol tables — stdlib AND extern primitives appear in trace trees. Existing trace tests that
   asserted a trace tree's shape (e.g. `(trace (fact 5))`) now see additional child calls (prelude/
   primitive calls the body makes that are GOT-slotted). Update those expectations. Add positive coverage
   that a stdlib fn and an extern primitive (e.g. `str-concat`) appear in a tree when called from a traced
   body; add negative coverage that **inline-CLIF arithmetic** (`+`, `-`, comparisons) does NOT appear
   (the one structural invisibility) and that **anonymous lambdas** do not appear as named nodes. These
   are the `[Tested+Neg]` rows for §4.12.3. `// spec: spec/04-expressions.md §4.12.3`.

4. Keep reductions small (per `memory/feedback_repros_join_suite.md`) — small CLIF for the nested-guard
   and the descriptor-formatting paths is inspectable via `/clif` / `CRANELISP_CODEGEN_TRACE=1` if a
   descriptor-rendering defect surfaces during the /dev waves.

## Gate-review addenda (S76 Wave 1.5 /review — appended by /sprint)

The Wave 1.5 gate review (PASS-WITH-NOTES) surfaced three items whose durable owner is this FIXME's
test work:

- **(NOTE-1) Production-baker round-trip gap.** Backend's descriptor round-trip unit tests build blobs
  with the low-level `DescriptorBlob` primitives, hand-mirroring `bake_adt`'s layout — the production
  `bake_descriptor`/`bake_adt` ctor-table assembly + concrete-type substitution is verified by
  inspection only. The e2e descriptor-rendering coverage here (item 3's tree-shape assertions over ADT
  params/results) is what closes that gap — include at least one traced fn taking/returning a
  polymorphic ADT at a concrete instantiation (e.g. `(Option Int)`).
- **(NOTE-2) Panic-unwind stuck guard.** If a JIT body panics mid-trace while `TRACE_BODY_RUNNING` is
  set, the thread-local flag + trace role stay stuck — a later same-thread `(trace …)` would spuriously
  raise "nested trace". Same stuck-owner class as the pre-existing role CAS; no RAII cleanup exists.
  Add a test (or document the limitation with a failing-not-ignored test if it is judged a defect):
  `(trace (panicking-fn))` followed by a fresh `(trace (ok-fn))` on the same REPL thread.
- **(NOTE-4) `--link` baked-address risk — verify before declaring §4.12.9 satisfied.** The trace
  wrapper bakes `code_ptr`/`got_base` as codegen-time absolute `iconst`s read from the live GOT. Valid
  for REPL/`--run`; for `--link` standalone binaries those addresses belong to the compiling process.
  The descriptor blob is position-independent (fine), but the baked code/GOT addresses may not be.
  Item 2's linked-binary e2e is the decisive test — if it fails, the defect goes to /dev (backend)
  with the repro (object-mode wrapper must reference code/GOT via relocations, not baked `iconst`s).

## Operational implication / Context

These tests should land WITH or just-after the /dev waves (FIXMEs 0254/0255/0256) so they go green as the
implementation lands — but the nested-error + linked-binary tests can be authored as **failing** ahead of
the implementation (per `memory/feedback_failing_not_ignored.md` — failing, un-ignored, with `// spec:`
+ `// FIXME(/dev ...)` pointing at the resolver) to serve as the durable target. The swap-all expectation
updates are edits to existing passing tests and should land in the same wave as discovery (FIXME 0255) to
avoid a window of red. Sequencing is **/sprint + user's call**.
