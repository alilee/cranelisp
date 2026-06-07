---
number: 0272
target: /qa
filed_by: /arch
filed_at: 2026-06-06
sprint_filed: 76
target_sprint: 76
refers_to: design/arch/test-discovery.md §2 "the fork-join error-slot ferry obligation" + §5 + appendix-A rows, spec/12-runtime.md §12.4.3, spec/appendix-a-builtins.md §A.4, tests/spec_12_runtime.rs, tests/regression.rs
status: open
---

# QA: lenient/Par panic-swallow DEFECT repro (S76 Wave 4) + discover-tests / catch-runtime-error e2e (when implemented)

Two halves with different sprint placement.

## Half A — the pre-existing panic-swallow DEFECT repro (S76 Wave 4 — file now)

The settled test-discovery design surfaced a **pre-existing defect** independent of the
new primitives: NEITHER fork-join boundary ferries the runtime-error slot. `ivar_force`
(lenient-let spark/join) and `dispatch_par_branches_with_trace` (Par) both return a bare
i64 with no worker-side `take_runtime_error()` check, so a runtime panic inside a
parallelised binding is silently swallowed on the joining thread (the binding yields the
sentinel `0` instead of aborting the expression). This violates spec §12.4.3 —
lenient/parallel evaluation MUST be observationally equivalent to sequential, where the
first panic aborts the whole expression.

**Author a failing, un-ignored repro** (per `memory/feedback_failing_not_ignored.md`):
a pure `let` whose binding parallelises and panics (e.g. a div-by-zero or match
non-exhaustion inside a sparkable binding), asserting the whole expression panics rather
than yielding a sentinel — and a Par counterpart. `// spec: spec/12-runtime.md §12.4.3`
+ `// FIXME(/dev …)` pointing at the resolver (the intrinsics ferry — FIXME 0270). Keep
the reduction small (small CLIF is inspectable via `CRANELISP_CODEGEN_TRACE=1`). The
S76 Wave-4 ledger should carry this; sprint placement is **S76 Wave 4** because it is a
standing defect, not gated on the new feature.

## Half B — discover-tests / catch-runtime-error e2e (when implemented — S77)

When FIXMEs 0269–0271 + 0273 land, add e2e coverage that graduates the appendix-A rows
from `[R4]`:

- `catch-runtime-error` brackets a panicking thunk → `(Err …)`; a clean thunk → `(Ok …)`.
  Works in `--link` (self-contained intrinsic) AND in REPL/`--run`.
- `discover-tests` returns name+callable pairs for eligible `test-*` fns; a redefined
  test runs its new body through a discovered wrapper (freshness); a mis-typed `test-*`
  is excluded.
- Rewrite the existing literal forms — `tests/regression.rs:782` (`(run-test "html/...")`
  over discovered pairs + the combinator) and `tests/spec_12_runtime.rs:369/374`
  (re-target to pairs discovery + a `catch-runtime-error` bracket).
- `--link` of a `discover-tests` program: NO friendly compile-time rejection; the
  unresolved-symbol surfaces at link/load (interim — §4.5). Retire any test asserting a
  friendly compile-time rejection for discover-tests (there is none in the design).

`// spec:` annotations against spec/appendix-a-builtins.md §A.4 + spec/12-runtime.md
§12.4.3 (the propagation sentence the /spec cascade adds).

## /qa resolution status — Half A (S76 W3 — 2026-06-07)

DONE (failing-not-ignored repro landed). `tests/spec_12_runtime.rs`:

- `lenient_binding_panic_not_swallowed_neg` — FAILING. The minimal repro is
  `(let [a (div-i64 10 0) b (add-i64 1 2)] a)` → yields `:primitives/Int 0`
  (sentinel) with lenient eval ON (the default), deterministically across runs.
  The div-by-zero panic in the binding is silently swallowed.
- `lenient_binding_panic_surfaces_with_no_lenient_control` — PASSING control.
  The SAME expression under `CRANELISP_NO_LENIENT=1` DOES panic
  ("division by zero"), proving the lenient/spark path is the trigger.

**Spark-trigger finding.** No expensive recursive binding was needed — the
swallow happens for a TRIVIAL binding (`div-i64 10 0`) under lenient eval, so
the cost heuristic is not the gate; the lenient compile path's join does not
check the runtime-error slot at all. The `CRANELISP_NO_LENIENT=1` inversion is
clean and deterministic, exactly as the FIXME predicted. The Par-branch (IO)
variant is NOT yet authored — it needs IO/platform infra (`print`); deferred
with Half B (S77) where the IO surface is exercised.

Resolver: **/dev intrinsics** — the fork-join error-slot ferry obligation
(FIXME 0270). `// FIXME(/dev intrinsics)` on the test; PLAN.md §"W3 trace +
lenient + 0279 reduction" row L1. Half B (discover-tests / catch-runtime-error
e2e) remains S77, untouched.

## Operational implication / Context

Half A is the durable record of the swallowed-error defect (flagged in the design as
"file when actioned"). Half B graduates the feature's appendix-A rows. The /spec cascade
(parallel agent) re-types those rows + adds the §12.4.3 sentence; this FIXME tracks the
test side. Sequencing is /sprint + user's call.
