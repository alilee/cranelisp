---
number: 0487
target: /spec
filed_by: /sprint
filed_at: 2026-07-01
sprint_filed: 97
refers_to: spec/appendix-a-builtins.md §A.3 (catch-runtime-error brackets construction not run), spec/12-runtime.md §12.7.2, design/intrinsics/reactor.md §9, tests/concurrency_v9_select.rs::empty_select_caught_by_catch_runtime_error
status: open
---

# Is `(select [])` "recoverable" achievable? — empty-select raises at run-time, but `catch-runtime-error` brackets construction

## Issue

FIXME 0475's ruling said `(select [])` MUST raise a **recoverable** runtime error (§12.7.2). The `/int` mechanism (S97) raises it via `set_runtime_error` at effect-RUN time (`run_select_node`) — the **fatal** path works (guards 4.1/4.3/4.4 green). But the **catchable** guard `tests/concurrency_v9_select.rs::empty_select_caught_by_catch_runtime_error` (4.2) is RED and stays RED: `catch-runtime-error` brackets only **pure IO construction** (spec §A.3 — "effects run later, outside the bracket"), so `(catch-runtime-error (fn [] (empty-select-io)))` constructs the select inside the bracket but the error raises when the trampoline RUNS it, *outside* the bracket → `Ok` (exit 0), not caught.

So "recoverable" is not achievable via IO-wrapping under the effect model as specified. Making it catchable would need a **construction-time** raise (backend `compile_select` detecting the literal-empty vec) — but that only catches the *literal*-empty case; a runtime-empty `(select some-vec)` where `some-vec` is empty at runtime can only raise at run-time, which the construction bracket never catches.

## Proposed resolution (/spec to rule)

Rule the empty-select semantics honestly given the effect model:
1. **Is `(select [])` catchable at all?** If yes, only the literal-empty case (construction-time raise) — spell out that runtime-empty stays fatal-at-run. If no, qualify 0475's "recoverable" to "fatal runtime error" and re-point/retire guard 4.2.
2. Reconcile §A.3 (catch brackets construction) with §12.7.2 (recoverable) for effects whose error raises at run-time — this is the general question, not just empty-select (any run-time effect error is uncatchable via IO-wrapping).

Guard 4.2 (RED) is the durable record; this FIXME is the /spec ruling that resolves whether it can flip green or should be re-shaped.
