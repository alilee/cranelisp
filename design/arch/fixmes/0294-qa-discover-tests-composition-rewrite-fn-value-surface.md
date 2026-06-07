---
number: 0294
target: /qa
filed_by: /dev
filed_at: 2026-06-08
sprint_filed: 76
target_sprint: 77
refers_to: tests/spec_12_runtime.rs::discover_tests_and_run_test_user_composition (FAILING — tests a RETIRED API), design/arch/test-discovery.md §4.3 (the in-language runner) + §5 (the new surface), design/arch/fixmes/0271 (int landed) + 0291 (frontend dispatch deletion)
status: open
---

# QA: rewrite `discover_tests_and_run_test_user_composition` for the fn-value `discover-tests` surface

## Issue

`tests/spec_12_runtime.rs::discover_tests_and_run_test_user_composition` exercises
the **pre-convergence** test-discovery API:

- `(discover-tests)` returning `(IO (SList Sexp))` of names;
- `(run-test head)` returning `(IO TestResult)`;
- `(TestPass n ns)` / `(TestFail n ns r)` constructors.

The fourth-convergence test-discovery design (test-discovery.md, SETTLED, user
2026-06-06) **retires all of these**: `run-test` is subsumed (running = invoking a
discovered late-bound wrapper under `catch-runtime-error`); `TestResult` /
`TestPass` / `TestFail` retire; `discover-tests` returns
`(Vec (Pair String (Fn [] (Option String))))` (fn-value pairs). The int side
landed these retirements S76 W4b (FIXME 0271): bootstrap no longer seeds
`TestResult`/`run-test`; `discover-tests` is a `(Vec String) → (Vec (Pair …))`
`PrimitiveExtern`. The test consequently FAILS (it references retired symbols).

This is a **stale test against a retired API**, not a compiler defect — but it is
currently a red in `spec_12_runtime`, so it needs to be rewritten (not deleted —
the composition it exercises is still a spec requirement, just with the new shape).

## Proposed resolution

Rewrite the test to the §4.3 in-language runner shape over the fn-value pairs:

```clojure
(import [primitives [discover-tests catch-runtime-error]])
(defn test-passing [] None)
(defn run-one [pair]
  (match pair
    [(Pair name run)
     (match (catch-runtime-error run)
       [(Err _)       1]      ; or however the test tallies
       [(Ok None)     1]      ; passed
       [(Ok (Some _)) 0])]))  ; assertion-failed
(defn count-passes [] (... fold run-one over (discover-tests ["user"]) ...))
(count-passes)
```

Assert the pass count. Use `repl_prims` (PreludeVariant::None / PrimitivesOnly)
since `Pair`/`Result`/`Option`/`discover-tests`/`catch-runtime-error` are all in
`primitives`.

**Depends on FIXME 0291** (frontend: delete the `discover-tests`/`run-test`
head-position dispatch so `(discover-tests ["user"])` parses as an ordinary
apply). Until 0291 lands, `(discover-tests …)` fails at parse. `catch-runtime-error`
is already e2e-green and can be tested independently now.

## Context

This test is also the natural home for the §5 `discover-tests` e2e acceptance
named in FIXME 0271's status (fresh-set freshness, mis-typed `test-*` exclusion,
late-bound redefinition). Authoring belongs to /qa per the test-ownership split.
