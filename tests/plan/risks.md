# QA Risk Review

Risk assessment for quality assurance in the Cranelisp reimplementation. Based on analysis of:
- 591 prototype tests (502 integration + 57 RC + 14 trace + 9 run-tests + 9 platform)
- 10 ignored tests, 2 known-issue-documenting tests
- 16 spec sections, architecture docs, KNOWN_ISSUES.md
- The 7-crate architecture and ring model

## Risk Summary

| # | Risk | Severity | Ring | Mitigation |
|---|---|---|---|---|
| 1 | RC correctness is non-local | **HIGH** | 1–4 | Dedicated RC test harness from Ring 1; every later ring re-runs RC suite |
| 2 | Batch/REPL parity gap | **HIGH** | 0–4 | Single `compile_unit()` is architectural; /qa validates with dual-mode tests |
| 3 | Test catalog portability | **MEDIUM-HIGH** | 0–4 | ~90% of 591 tests are spec-validation; ~10% are implementation-specific |
| 4 | Macro pipeline testability gap | **MEDIUM-HIGH** | 3 | No macros until Ring 3; /qa must test Rings 0–2 without prelude macros |
| 5 | Module system combinatorial explosion | **MEDIUM** | 2 | 35 module tests cover basics; cross-module trait/constrained-poly under-tested |
| 6 | `process::exit(1)` kills test harness | **MEDIUM** | 0+ | Redesign panic handler; 10 ignored tests depend on it |
| 7 | E2E transcript tests are brittle | **MEDIUM** | 4 | Only 4 E2E pairs; output format changes break them |
| 8 | Performance regression invisible | **MEDIUM** | 0–4 | No perf baselines yet; prototype runs ~2min for 978 tests |
| 9 | REPL slash command coverage thin | **LOW-MEDIUM** | 4 | 8 of 16 commands tested; rest deferred to /repl experience suite |
| 10 | Error message quality untested | **LOW-MEDIUM** | 0–4 | Only ~20 error tests; no golden-master error output tests |

## Detailed Analysis

### Risk 1: RC Correctness is Non-Local (HIGH)

Reference counting interacts with every language feature. The prototype's 57 RC tests cover phases 2D–2F and step 11, but every new feature added in Rings 2–4 (traits, modules, macros, IO) can introduce RC bugs. The prototype discovered this the hard way — closures, ADT drop glue, vec COW, and match scrutinee dec were each separate debugging campaigns.

**Impact**: Memory leaks or use-after-free in any ring. RC bugs are silent (no immediate crash) and accumulate.

**Mitigation**:
- Ring 1 establishes the RC test harness with `CRANELISP_RC_TRACE=1` validation.
- Every subsequent ring adds RC-aware tests for its features (e.g., Ring 2 must test trait dispatch with heap-typed args).
- The RC test suite runs serially (`--test-threads=1`) and is never skipped.
- `/backend` owns RC correctness; `/qa` validates it via black-box allocation tracking.

### Risk 2: Batch/REPL Parity Gap (HIGH)

The prototype's worst structural debt was dual batch/REPL pipelines. The architecture addresses this with `compile_unit()` + `CompileMode`, but parity requires active validation. The prototype had 116+ REPL-specific tests because the REPL diverged from batch.

**Impact**: A feature works in batch but fails in the REPL (or vice versa). Users experience this as "it works in a file but not at the prompt."

**Mitigation**:
- Every integration test that validates language behavior runs in *both* batch and REPL modes.
- `/qa` maintains a `compile_and_eval()` helper that tests both paths and asserts identical results.
- Ring 0 wires the batch pipeline first; REPL mode is validated as soon as the pipeline exists.
- The `CompileMode::Interactive` path gets its own test coverage from Ring 0.

### Risk 3: Test Catalog Portability (MEDIUM-HIGH)

Of the 591 prototype tests, approximately 90% validate observable language behavior (spec-validation — directly portable). Approximately 10% test internal implementation details.

**Impact**: Implementation-specific tests can't be ported 1:1; some will need rewriting against the new API.

**Breakdown by portability**:
- **Directly portable** (~530): tests that compile source, run, and check output. Same source, same expected value.
- **Needs adaptation** (~40): tests that use prototype-specific types (`FnSlot`, `GotReference`, `CompiledModule`, `ReplSession`) or internal APIs.
- **Rewrite** (~20): tests tightly coupled to prototype internals (cache file structure, GOT layout, JIT details).

**Mitigation**:
- Portable tests are ported verbatim into `tests/` for each ring.
- Adaptation tests are rewritten against the new API when the relevant ring is implemented.
- No test is silently dropped — every prototype test gets a disposition.

### Risk 4: Macro Pipeline Testability Gap (MEDIUM-HIGH)

Rings 0–2 have no macros. The prototype's `compile_and_run()` helper loads the prelude (macros included). The reimplementation's Rings 0–2 must use `compile_and_run_simple()` equivalents.

**Impact**: Tests that use prelude macros (`list`, `vec`, `do`, `bind!`, `cond`, `case`, `->`, `->>`, `str`, `derive`, `const`, `def`) cannot run until Ring 3.

**Affected tests**: ~180 of 591 use macros (everything calling `compile_and_run` or `compile_and_run_with_macros`, plus all example file tests, all IO tests, all stdlib tests).

**Mitigation**:
- Ring 0–2 tests use only `compile_and_run_simple()` (no macros).
- The test catalog explicitly marks each test with its ring eligibility.
- Ring 3 unblocks the macro-dependent tests; Ring 4 unblocks IO-dependent tests.
- `/qa` maintains a "blocked tests" tracking list that shrinks as rings complete.

### Risk 5: Module System Combinatorial Explosion (MEDIUM)

The prototype has 35 module tests covering imports, visibility, exports, ambiguity, and qualified names. But cross-module interactions with traits, constrained polymorphism, and macros are under-tested. The prototype's KNOWN_ISSUES lists 12 module system limitations.

**Impact**: Module bugs surface late (Ring 2+) and are hard to diagnose because they involve interactions between the type system, symbol tables, and codegen GOT.

**Mitigation**:
- Ring 2 adds cross-module trait dispatch tests (not just import/export mechanics).
- Ring 2 adds cross-module constrained polymorphism tests (specialization in defining vs calling module).
- `/qa` works with `/typecheck` to define module-aware type inference tests.
- The 12 known module limitations each get a test that documents the behavior, with FIXME for those targeted for fixing in the reimplementation.

### Risk 6: `process::exit(1)` Kills Test Harness (MEDIUM)

10 integration tests are `#[ignore]` because `cranelisp_panic` calls `process::exit(1)`, which kills the entire test harness. These cover checked arithmetic overflow, vec out-of-bounds, and match exhaustiveness failure.

**Impact**: Panic-path tests can only run in isolation (`--test-threads=1 --ignored`). CI cannot catch regressions in these paths during normal test runs.

**Mitigation**:
- The reimplementation's `cranelisp_panic` should use `longjmp`/catch mechanism or return an error code rather than `process::exit(1)`.
- `/backend` + `/runtime` design this in Ring 0.
- If the redesign works, all 10 ignored tests become normal tests.
- If the redesign is deferred, `/qa` ensures these tests run in a separate CI step.

### Risk 7: E2E Transcript Tests are Brittle (MEDIUM)

Only 4 E2E transcript pairs exist (`basic_exprs`, `defn_and_call`, `reader_shortcuts`, `slash_help`). These compare exact output text.

**Impact**: E2E tests break on formatting changes, creating false negatives. Or they pass despite semantic regressions if the output accidentally matches.

**Mitigation**:
- E2E tests are Ring 4 (last); formatting stabilizes before they run.
- `/qa` writes E2E tests that match semantic content rather than exact byte-for-byte comparison where possible.
- `/repl` owns the experience test harness, which provides richer assertions than simple transcript comparison.

### Risk 8: Performance Regression Invisible (MEDIUM)

The prototype runs 978 tests in ~2 minutes. No performance baselines exist for individual operations.

**Impact**: The reimplementation could be 5x slower and no test would fail. Users notice at the REPL.

**Mitigation**:
- Ring 0 establishes performance baselines: reader throughput, inference time, codegen time, JIT execution.
- `/repl` defines performance targets (REPL startup <500ms, expression evaluation <100ms).
- Ring 4 adds benchmark tests comparing against prototype baselines.
- Use `criterion` or similar for repeatable benchmarks.

### Risk 9: REPL Slash Command Coverage Thin (LOW-MEDIUM)

8 of 16 slash commands are tested (`/sig`, `/info`, `/type`, `/list`). Untested: `/doc`, `/source`, `/sexp`, `/ast`, `/clif`, `/disasm`, `/time`, `/mem`, `/expand`, `/mod`, `/reload`.

**Mitigation**: `/repl` owns the experience test suite covering all 16 commands. `/qa` adds basic smoke tests in Ring 4.

### Risk 10: Error Message Quality Untested (LOW-MEDIUM)

Only ~20 dedicated error tests exist. No golden-master tests for error formatting.

**Mitigation**: Each ring adds error tests for its features. Error message testing uses substring matching, not exact comparison.

## Spec Coverage Gaps

| Spec Section | Tests | Coverage Assessment |
|---|---|---|
| 01-lexical | ~6 | **Thin** — reader shortcuts, whitespace, comments lightly tested |
| 02-grammar | ~7 | **Thin** — parser edge cases (nested brackets, operator precedence) |
| 03-types | ~55 | **Good** — ADTs, type annotations, polymorphism well covered |
| 04-expressions | ~45 | **Good** — let, if, lambda, closure, curry covered |
| 05-definitions | ~15 | **Adequate** — multi-sig covered; defn- visibility needs more |
| 06-pattern-matching | ~20 | **Good** — exhaustiveness, wildcards, var patterns |
| 07-traits | ~45 | **Good** — default methods, derive, HKT, ambiguity |
| 08-modules | ~35 | **Adequate** — import/export/visibility; cross-module interactions thin |
| 09-macros | ~35 | **Good** — quasiquote, multi-clause, bracket destructuring |
| 10-io | ~12 | **Adequate** — pure/bind/do covered; par-bind! light |
| 11-stdlib | ~40 | **Good** — list, vec, seq, map/reduce/filter |
| 12-runtime | ~280 | **Heavy** — RC, cache, REPL, trace dominate; lenient eval good |

Priority gaps to address:
1. **01-lexical** and **02-grammar**: need more parser edge case tests (Ring 0)
2. **08-modules**: need cross-module trait and constrained-poly tests (Ring 2)
3. **Error paths**: need systematic error message tests per ring
4. **10-io**: par-bind! and platform interaction tests (Ring 4)
