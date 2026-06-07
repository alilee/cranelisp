---
number: 0291
target: /dev
filed_by: /dev
filed_at: 2026-06-08
sprint_filed: 76
target_sprint: 77
refers_to: crates/cranelisp-frontend/src/ast_builder.rs:1021-1022 (keyword-dispatch arms) + :1080 build_discover_tests + :1115 build_run_or_trace_test (run-test half only), design/arch/test-discovery.md §"Frontend — nothing (zero special-casing)"
status: open
---

# Frontend: delete `discover-tests` / `run-test` head-position dispatch (zero special-casing)

Crate: `cranelisp-frontend` (`/dev` narrow, frontend mode).

## Issue

`test-discovery.md` §"Frontend — nothing (zero special-casing)" (SETTLED, fourth
convergence) requires both `discover-tests` and `run-test` to parse as a plain
`Expr::Apply` to an `Expr::Var` — "the bespoke head-position dispatch arms
`build_discover_tests` (`ast_builder.rs:1080`) and the `run-test` half of
`build_run_or_trace_test` (:1115), plus their keyword-match rows (:1021–1022),
**delete**. The `trace` half of `build_run_or_trace_test` is preserved."

As-built (HEAD with S76 W4b int landed), the two dispatch arms still intercept:

```rust
"discover-tests" => return build_discover_tests(children, span),
"run-test" => return build_run_or_trace_test(children, span, "run-test"),
```

`build_discover_tests` rejects a `(Vec String)` argument ("takes zero or one
argument") and emits an `Expr::Var` head with a bare-symbol module path — it
predates the fourth-convergence reshape where `discover-tests` is an ordinary
`primitives` `PrimitiveExtern` taking `(Vec String)`. Consequence: a user
program `(discover-tests ["user"])` fails at parse ("expected symbol") because
the special arm does not accept a vec-literal argument.

The int side of the test-discovery cascade is complete (FIXME 0271, S76 W4b):
`discover-tests` is seeded as `DefKind::PrimitiveExtern` in `src/bootstrap.rs`,
its body promised via `Jit::define_symbol("discover-tests", discover_tests_extern)`
in `worker::build_session_jit`, and the live-scan extern returns
`(Vec (Pair String (Fn [] (Option String))))`. The ONLY remaining blocker to
`discover-tests` e2e is this frontend interception. `catch-runtime-error` (the
other test-discovery primitive) already works e2e — it has no frontend arm.

## Proposed resolution

1. Delete the two keyword-dispatch arms (`ast_builder.rs:1021–1022`).
2. Delete `build_discover_tests` (`:1080`).
3. Delete the `run-test` half of `build_run_or_trace_test` (`:1115`): if `trace`
   is its only surviving caller, fold/rename to a `build_trace_test` (or merge
   into `build_trace`); keep the `trace` path intact (test-discovery.md keeps
   `trace`).
4. Update the frontend baseline + any frontend unit tests that asserted the old
   `discover-tests` / `run-test` parse shape.

## Acceptance

- `(discover-tests ["user"])` parses as `Apply(Var("discover-tests"), [VecLit])`.
- `(run-test …)` no longer parses as a special form (resolves as ordinary apply;
  fails at typecheck if no such symbol — `run-test` is retired, FIXME 0271).
- `(trace expr)` still parses as the trace form.
- `cargo nextest run -p cranelisp-frontend` green; frontend baseline regenerated.

## Context

Frontend half of the test-discovery cascade. Pairs with FIXME 0271 (int — landed
S76 W4b). test-discovery.md is normative.
