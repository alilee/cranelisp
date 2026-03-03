# Test Strategy

How `/qa` manages quality across the Cranelisp reimplementation: quality model, skill interactions, pipeline wiring, and portability classification.

## Quality Model

Quality has three dimensions:

1. **Correctness**: does the compiler produce the right output for every input? (integration tests)
2. **Parity**: do batch and REPL produce identical results? (dual-mode tests)
3. **Soundness**: are memory, types, and modules internally consistent? (RC tests, type inference tests, module resolution tests)

Each ring must satisfy all three before the next ring begins. `/review` gates ring transitions.

## Pipeline Wiring Responsibility

`/qa` owns the pipeline orchestration — wiring frontend, typecheck, and backend into a working compiler:

- **Ring 0**: `/qa` writes `compile_unit()` in the binary crate, connecting `cranelisp-frontend` → `cranelisp-typecheck` → `cranelisp-backend`.
- **Ring 2**: `/qa` extends `compile_unit()` with module graph discovery and ordered compilation.
- **Ring 3**: `/qa` implements the `MacroExpander` trait in the binary crate (wiring frontend + typecheck + backend for macro bodies).
- **Ring 4**: `/qa` adds caching, linking, REPL session management, and file watching.

Each compiler skill implements its crate in isolation against interface stubs. `/qa` is the first to connect real implementations.

## Skill Interaction Model

```
Skill          /qa Provides                      /qa Receives
─────────────  ───────────────────────────────── ─────────────────────────────────
/arch          Test plan review                  Interface types, crate structure,
               Ring acceptance gate feedback     CompileMode design,
                                                 compile_unit() signature

/frontend      Integration tests validating      Reader (source → Sexp)
               parse correctness                 AST builder (Sexp → Expr)
               Error message quality reports     MacroExpander trait

/typecheck     Integration tests validating      CheckResult, type inference,
               type inference end-to-end         method resolution, exhaustiveness
               Regression reports                checking

/backend       RC correctness test results       Codegen, JIT execution,
               Performance measurements          RC emission, GOT management,
               Panic handler requirements        platform call dispatch

/stdlib        Standard library test runner      Library source files
               Test failures assigned back       Test patterns

/platform      Platform loading tests            DLL loading, C-ABI contract,
               IO integration tests              test-capture platform

/review        Ring completion test reports      Ring approval/rejection,
               Test coverage summaries           quality findings

/repl          REPL experience test harness      Experience spec,
               Smoke tests for slash commands    performance targets

/port          Exemplar project test suite       End-user validation,
               Integration with run-tests        stdlib gap reports

/examples      Example file compilation tests    Example programs to compile
               Output validation                 Idiomatic patterns

/docs          Error message catalog input       User-facing documentation
               Test failure examples             Learning path validation

/spec          Test-to-spec mapping              Spec section per test,
               Coverage gap reports              acceptance criteria
```

## Communication Protocol

1. **Test failure triage**: When a test fails, `/qa` identifies the responsible skill based on the failure location (parse → `/frontend`, type → `/typecheck`, codegen → `/backend`, module → `/typecheck` or `/arch`).

2. **Ring gate**: At ring completion, `/qa` produces a test report:
   - Total tests: N passing, M failing, K skipped
   - RC balance: all allocation tracking clean (yes/no)
   - Parity: batch and REPL agree on all tests (yes/no)
   - New coverage: tests added this ring
   - Regression: any Ring N-1 tests broken

3. **Blocked test tracking**: `/qa` maintains a list of tests blocked until a later ring. When a ring completes, `/qa` unblocks and runs newly eligible tests.

4. **Feedback to /spec**: When a test reveals ambiguous behavior, `/qa` reports to `/spec` with the test source, expected behavior, and actual behavior.

## Unit Test Ownership

Each source crate has `#[cfg(test)] mod tests` in every module. These are owned by the compiler skill that owns the module:

- `/frontend` owns reader and AST builder unit tests
- `/typecheck` owns inference, unification, trait resolution unit tests
- `/backend` owns codegen, RC emission, GOT management unit tests

`/qa` does not write unit tests for other skills. `/qa` owns integration tests that validate the pipeline end-to-end.

## Test Portability Classification

### Summary

| Classification | Count | Action |
|---|---|---|
| Directly portable | ~530 | Port source + expected value verbatim |
| Needs API adaptation | ~40 | Rewrite against new crate APIs |
| Rewrite | ~20 | Rewrite against new architecture |
| Total | ~591 | No test dropped silently |

### Directly Portable Pattern

Tests that compile source, run, and check output. Same source, same expected value:

```rust
#[test]
fn factorial() {
    let result = compile_and_run_simple(r#"
        (defn fact [n] (if (= n 0) 1 (* n (fact (- n 1)))))
        (defn main [] (pure (fact 10)))
    "#).unwrap();
    assert_eq!(result, 3628800);
}
```

### Needs API Adaptation Pattern

Tests that use prototype-specific types (`FnSlot`, `GotReference`, `CompiledModule`, `ReplSession`):

```rust
// Prototype:
let mut r = TestRepl::new();
r.defn("(defn add1 [x] (+ x 1))").unwrap();
assert_eq!(r.eval("(add1 5)").unwrap(), 6);

// Reimplementation:
let mut session = repl_session();
session.eval("(defn add1 [x] (+ x 1))").unwrap();
assert_eq!(session.eval("(add1 5)").unwrap(), 6);
```

### Rewrite

Tests tightly coupled to prototype internals (cache file structure, GOT layout, JIT details). Rewritten against the new architecture when the relevant ring is implemented.

## Ignored Test Disposition

| Prototype Test | Reason Ignored | Reimplementation Plan |
|---|---|---|
| `checked_division_by_zero_panics` | process::exit(1) | Fix panic handler; make normal test |
| `checked_add_overflow_panics` | process::exit(1) | Fix panic handler; make normal test |
| `checked_sub_overflow_panics` | process::exit(1) | Fix panic handler; make normal test |
| `checked_mul_overflow_panics` | process::exit(1) | Fix panic handler; make normal test |
| `checked_div_min_neg1_panics` | process::exit(1) | Fix panic handler; make normal test |
| `known_issue_vec_out_of_bounds` | process::exit(1) | Fix panic handler; make normal test |
| `vec_get_out_of_bounds_panics` | process::exit(1) | Fix panic handler; make normal test |
| `vec_get_negative_index_panics` | process::exit(1) | Fix panic handler; make normal test |
| `ambiguous_trait_method_dotted_name_works` | Known issue: method resolution | Fix in reimplementation; make normal test |
| `dotted_field_accessor_resolution` | Flaky: process::exit(1) | Fix panic handler + accessor resolution |

All 10 should become normal (non-ignored) tests in the reimplementation.

## Known Issue Test Disposition

| Prototype Test | Known Issue | Reimplementation Plan |
|---|---|---|
| `known_issue_adt_accessor_shadowing` | Accessor "first wins" | Fix: module-scoped accessors |
| `known_issue_qualified_name_resolution_error` | Qualified names parse but don't resolve | Fix: proper qualified name resolution |

Both should test the *correct* behavior in the reimplementation.

## Performance Baselines (to be captured)

Capture before Ring 0 implementation begins, running against the prototype:

| Metric | How to Measure | Target |
|---|---|---|
| Reader throughput | Parse `lib/prelude.cl` + `lib/core/*.cl` (N times) | Within 2x of prototype |
| Type inference time | Check all example files | Within 2x of prototype |
| Codegen time | Compile all example files | Within 2x of prototype |
| Test suite total | `just test` wall clock | Within 2x of prototype |
| REPL startup | Time to first prompt | <500ms |
| Expression eval | `(+ 1 2)` at REPL | <100ms |
