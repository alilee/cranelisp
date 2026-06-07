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
- **(NOTE-4) `--link` baked-address risk — CONFIRMED at runtime (2026-06-06 /sprint probe) and
  user-decided FIX IN-SPRINT.** The linked trace binary (match-consumption shape) builds, links, and
  **SIGBUSes (exit 138)** — the baked compiling-process addresses are the cause. The fix is FIXME
  **0275** (/dev backend — object-mode relocations per the descriptor-blob template). Item 2's
  linked-binary e2e lands FAILING first (repros-join-suite) and is 0275's acceptance. A SECOND
  defect blocks the accessor-consumption shape (`can't resolve symbol nanos` + session park) —
  FIXME **0276** carries its repros; don't conflate the two when authoring item 2 (use the
  match-consumption shape for the 0275 acceptance test, the accessor shape for 0276's).

## /qa resolution status (S76 W3 — 2026-06-07)

The trace integration test work is COMPLETE. New active home: `tests/trace.rs`
(13 tests; supersedes `tests/legacy/ring4_trace.rs`). The 4 stale trace cases in
`tests/spec_12_runtime.rs` reconciled: `trace_returns_trace_value` rewritten to
match-based extraction (the `name` accessor is broken — see below);
`trace_nested_still_returns_trace` ("outermost wins") RETIRED. PLAN.md §"W3
trace + lenient + 0279 reduction" carries the full row ledger.

Item-by-item:

- **Item 1 (nested error).** Dynamic case `trace_nested_dynamic_raises_runtime_error`
  PASSES (Wave-1.5 guard). Lexical case `trace_nested_lexical_raises_runtime_error`
  FAILS — **DEFECT**: the pure-lexical `(trace (trace e))` does NOT raise. No
  wrapper fires before the inner `swap_got`, so `TRACE_BODY_RUNNING` is still
  `false` and the inner trace is treated as a legit multi-module swap (returns an
  empty trace). Resolver **/dev intrinsics** (the guard must also catch the
  no-wrapper-yet lexical case). Durable record: the failing test.
- **Item 2 (linked binary).** `trace_linked_binary_match_consumption_runs` PASSES
  — 0275 object-mode relocations landed; the match-consumption shape links + runs
  (exit 42), no SIGBUS. Asserts WITHOUT extern-primitive children per FIXME 0280
  (a). No `--link` rejection test existed to retire.
- **Item 3 (swap-all visibility).** Positives GREEN: `trace_extern_primitive_appears_as_child`
  (`primitives/str-concat` in REPL), `trace_stdlib_fixture_fn_appears_as_child`
  (`prelude/helper`). Negatives GREEN (`[Tested+Neg]`): inline arithmetic +
  anonymous lambda produce no node.
- **NOTE-1 (production-baker round-trip).** `trace_polymorphic_adt_result_renders`
  + `trace_adt_value_render_overflows_defect` FAIL — **DEFECT**: tracing ANY fn
  returning a user ADT value (even nullary `None`) STACK-OVERFLOWS the ADT
  DisplayDescriptor formatter. The round-trip gap is a CRASH, not merely an
  unverified path. Resolver **/dev backend** (production `bake_adt`/`bake_descriptor`
  ctor-table assembly bakes an unbounded descriptor; possibly the intrinsics
  `cranelisp_trace_format` walk). Also `trace_trait_heavy_prelude_overflows_defect`
  FAILS — **DEFECT**: trace swap-all over the trait-heavy `TestStandard` prelude
  overflows on a `nice-worker` thread (Num+Eq+Ord alone does not; full prelude
  does — open bisection handed to /dev). Resolver **/dev backend** (swap-all
  discovery / descriptor scaling; the worker-thread signature implicates the
  lenient spark path).
- **NOTE-2 (panic-unwind stuck guard).** `trace_panic_unwind_does_not_stick_guard`
  PASSES — the worry does NOT reproduce in REPL mode (probed both the simple and
  the precise instrumented-call-then-panic shapes; per-form panic recovery resets
  the flag). NOT a defect; landed as a positive regression guard, NOT
  failing-not-ignored. (Verdict overrides the work-order expectation of FAILING.)
- **NOTE-4 (--link baked-address / accessor).** Match-consumption confirmed
  working (item 2). The accessor-shape defect is FIXME 0276 (kept separate, not
  conflated).

NEW DEFECTS surfaced (no free FIXME number — max is 0282; the failing tests are
the durable record + trigger per `feedback_repros_join_suite`): lexical-guard gap
(/dev intrinsics), ADT-render overflow (/dev backend), trait-prelude swap-all
overflow (/dev backend). All carry `// FIXME(/dev …)` inline + a PLAN.md row.
This FIXME stays OPEN as the trace-defect tracker for the /dev waves (the /qa
test work itself is done).

## Operational implication / Context

These tests should land WITH or just-after the /dev waves (FIXMEs 0254/0255/0256) so they go green as the
implementation lands — but the nested-error + linked-binary tests can be authored as **failing** ahead of
the implementation (per `memory/feedback_failing_not_ignored.md` — failing, un-ignored, with `// spec:`
+ `// FIXME(/dev ...)` pointing at the resolver) to serve as the durable target. The swap-all expectation
updates are edits to existing passing tests and should land in the same wave as discovery (FIXME 0255) to
avoid a window of red. Sequencing is **/sprint + user's call**.
