# Continue: REPL Module Rework — COMPLETE

## Summary

This rework extracted the file watcher, deleted ~5700 lines of dead v3 REPL code,
fixed trace to use a proper AST node, designed and implemented a test infrastructure
with special forms, and cleaned up the architecture.

## What was done

### Infrastructure
- **FileWatcher**: extracted `src/repl/watch.rs` → `src/watch.rs`, wired into REPL loop (init after prelude, sync+poll before prompt, reload on change), /reset clears state
- **src/repl/ deletion**: ~5300 lines of dead v3 code removed
- **error_modules**: wired into reload success/failure, eval blocked when non-empty

### Trace
- **Expr::Trace AST fix**: AST builder now produces `Expr::Trace` directly for `(trace expr)`. Removed name-based interception from typechecker and codegen — one representation, one code path.
- **Trace scope**: `build_traced_fns` filters to project-root modules only (spec §4.12.3)
- **Trace infrastructure**: `build_traced_fns`, `repl_trace_format` (JIT-callable), `TraceDisplayState` thread-local, `program_needs_trace` — all wired into `codegen_and_execute`
- **Grammar spec**: §2.3.10 updated — trace is a parser keyword, not module-resolved

### Test infrastructure
- **Expr::RunTests deletion**: AST variant + codegen removed (~420 lines). Replaced by special forms.
- **TestResult root type**: seeded in builtins (TestPass/TestFail), constructors seeded into all modules via `is_root_type_constructor`
- **discover-tests special form**: AST builder converts bare module path to string arg. Returns `(IO (SList Sexp))` of SexpSym values.
- **run-test special form**: AST builder converts bare qualified symbol to SexpSym constructor. Returns `(IO TestResult)`.
- **Shared core**: `discover_test_names()` + `run_test_by_name()` — used by both JIT externs and slash commands, no duplication
- **JIT externs**: `discover_tests_extern` + `run_test_extern` with `TestRunnerState` thread-local, heap ADT construction helpers (`alloc_heap_adt`, `alloc_io_pure`, `alloc_scons`, `test_outcome_to_heap`)
- **Slash commands**: `/run-tests [module]` (`/rt`), `/run-all-tests` — call shared core directly
- **Composition test**: `v4_repl_discover_and_run_test_via_bind` proves discover → bind → match SList → run-test with Sexp variable

### Design decisions
- Trace and test are **independent, composable** features. No trace-test form — use `(trace (test-fn))`.
- discover-tests/run-test are **extern primitives** (not new AST variants). Compile as normal `Expr::Apply`.
- TestResult is a **root type** (always in scope). discover-tests/run-test are **root primitives** (seeded into all modules).
- Arguments use **bare syntax**: `(discover-tests user.math)`, `(run-test user/test-add)`.
- discover-tests returns `SList Sexp` (SexpSym values), run-test accepts `Sexp` — **directly composable**.

### Spec updates
- `spec/02-grammar.md` §2.3.8, §2.3.10 — trace/discover-tests/run-test as parser keywords
- `spec/03-types.md` §3.2.5 — TestResult root type
- `spec/04-expressions.md` §4.12.3 — trace scope narrowed to project-root modules
- `spec/appendix-a-builtins.md` §A.2, §A.4 — TestResult type, test special forms
- `repl/spec.md` §16 — full test discovery and execution specification

## Architecture

```
Core (no heap allocation):
  discover_test_names(codegen_products, tc_modules, module) -> Vec<String>
  run_test_by_name(codegen_products, fq_name) -> TestOutcome

JIT externs (heap wrapper):
  discover_tests_extern: core -> SList<SexpSym> -> IO Pure
  run_test_extern: core -> TestResult -> IO Pure

Slash commands (string wrapper):
  /run-tests [module]: core -> formatted output
  /run-all-tests: core across project-root modules -> formatted output
```

## What remains (separate features)

- **Session persistence §15**: save-as-you-go for REPL definitions (not started)
- **File watcher manual testing**: needs end-to-end verification with actual file edits

## Verification

```bash
cargo nextest run -E "binary(ring0) | binary(ring1) | binary(ring2) | binary(ring3_repl) | binary(macros) | binary(modules) | binary(v4_pipeline) | binary(v4_repl_eval) | binary(rc)" --no-fail-fast
```

707 tests, 683 passed, 24 pre-existing failures (2 ring0, 4 macros, ~18 modules/ring2/v4_pipeline).
