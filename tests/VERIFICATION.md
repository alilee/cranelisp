# Post-Refactor Test Verification Plan

Reusable procedure for restoring confidence after any major refactor. Run through this top-to-bottom. Do not skip phases or reorder suites within a phase.

## Rules

1. **Always use `cargo nextest run`** (alias: `cargo nt`), never `cargo test`.
2. **Run one test file at a time.** Never combine multiple `--test` flags.
3. **Never use `--no-fail-fast`.** Unreliable with this codebase — tests can block or loop.
4. **Foreground only.** Never run tests in the background. Wait for completion.
5. **30-second timeout.** If a test run exceeds 30s, something is wrong — kill it and investigate (likely a hang from `wait_object_complete` or a deadlock).
6. **Never run cargo while another cargo process is active.** Build locks cause contention.
7. **Investigate failures before moving on.** A ring0 failure may cascade to ring1+. Fix or document as known before proceeding.
8. **Stop at the first unexpected failure in a phase.** Fix it or add it to the known failures table before continuing.

## Phase 0: Build

Verify the project compiles cleanly before running any tests.

```bash
cargo build
cargo clippy
```

Expected: clean build, no errors. Warnings are acceptable.

## Phase 1: Unit Tests

Per-crate unit tests, ordered by dependency depth (leaves first). These are fast and isolated — failures here indicate fundamental breakage.

```bash
cargo nt -p cranelisp-types --lib
cargo nt -p cranelisp-frontend --lib
cargo nt -p cranelisp-typecheck --lib
cargo nt -p cranelisp-runtime --lib
cargo nt -p cranelisp-backend --lib
cargo nt --lib
```

Expected: all pass. No known unit test failures.

## Phase 2: Core Language (Ring 0-1)

Self-contained tests using primitive operations and special forms. No prelude, no macros.

```bash
cargo nt --test ring0 -E 'not test(checked_div)'
cargo nt --test ring1
cargo nt --test rc
```

| Suite | Tests | Expected |
|-------|-------|----------|
| ring0 | 108 | 106 pass, 2 fail (pre-existing: `checked_div_min_neg1_panics`, `checked_division_by_zero_panics`) |
| ring1 | 166 | all pass |
| rc | 81 | all pass |

## Phase 3: Advanced Language (Ring 2-3)

Traits, modules, constrained polymorphism, macros, stdlib.

```bash
cargo nt --test ring2
cargo nt --test modules
cargo nt --test macros
cargo nt --test ring3_repl
cargo nt --test stdlib
cargo nt --test lenient
```

| Suite | Tests | Expected |
|-------|-------|----------|
| ring2 | 197 | 189 pass, 8 fail (qualified names, primitives scoping, multi-sig panic, trait-as-value) |
| modules | 22 | 18 pass, 4 fail (qualified name resolution) |
| macros | 28 | 23 pass, 4 fail, 1 ignored (error recovery, depth limit, macro return type) |
| ring3_repl | 50 | 39 pass, 2 fail, 9 ignored (macro error recovery) |
| stdlib | 54 | all pass |
| lenient | 16 | 0 pass, 16 fail (scheduling/par-bind pipeline broken, 9s timeouts) |

## Phase 4: Infrastructure (Ring 4 + Scheduler)

Scheduler coordination, IO monad, tracing, caching.

```bash
cargo nt --test scheduler
cargo nt --test io
cargo nt --test ring4_trace
cargo nt --test cache
```

| Suite | Tests | Expected |
|-------|-------|----------|
| scheduler | 18 | all pass |
| io | 74 | 9 pass, 65 fail (IO execution hangs at 9s — platform/DLL pipeline broken) |
| ring4_trace | 29 | 5 pass, 24 fail (prelude fixture fails: "unknown trait: Functor") |
| cache | 51 | 31 pass, 20 fail (multi-module, prelude, pipeline, object, repl cache) |

## Phase 5: REPL Experience

Display formatting, slash commands, error recovery.

```bash
cargo nt --test repl_experience
cargo nt --test repl_negative
```

| Suite | Tests | Expected |
|-------|-------|----------|
| repl_experience | 181 | 179 pass, 2 fail (display_imported_option formatting) |
| repl_negative | 31 | 29 pass, 2 fail (primitive module scoping) |

## Phase 6: E2E and Integration

End-to-end subprocess tests, examples, sprint-specific features.

```bash
cargo nt --test e2e
cargo nt --test examples
cargo nt --test v4_repl_eval
cargo nt --test v4_pipeline
cargo nt --test sprint23
```

| Suite | Tests | Expected |
|-------|-------|----------|
| e2e | 133 | 87 pass, 46 fail (subprocess: prompts, /expand, run-tests, string prims, imports) |
| examples | 15 | all pass |
| v4_repl_eval | 13 | 11 pass, 2 fail |
| v4_pipeline | 47 | 26 pass, 20 fail, 1 ignored |
| sprint23 | 70 | 0 run (cfg-disabled: `__sprint47_reenable` feature gate) |

## Phase 7: Known-Problematic (Last)

Suites with documented pre-existing failures. Run these last so they don't block progress on other phases.

```bash
cargo nt --test sketch_port
cargo nt --test exemplar
```

| Suite | Tests | Expected |
|-------|-------|----------|
| sketch_port | 141 | 102 pass, 39 fail (11 pre-existing + 28 new regressions) |
| exemplar | 3 | all pass |

## Pre-Existing Known Failures

Update this table as failures are fixed or new ones discovered.

| Suite | Count | Tests | Reason |
|-------|-------|-------|--------|
| ring0 | 2 | `checked_div_min_neg1_panics`, `checked_division_by_zero_panics` | checked_div not implemented |
| sketch_port | 11 | various | prototype features not yet ported |
| v4_pipeline | 2 | `v4_cross_module_macro_calls_helper`, `v4_cross_module_macro_transitive` | cross-module macro resolution gap |
| sprint23 | 70 | all | cfg-disabled (`__sprint47_reenable` feature gate) |

## v4 Pipeline Regressions (Sprint 49)

Discovered 2026-04-05. ~215 new failures from v4 pipeline rearchitecture, clustered into root causes:

| Category | ~Count | Root Cause | Affected Suites |
|----------|--------|------------|-----------------|
| Qualified name resolution | ~20 | `foo/bar` cross-module refs fail as "undefined variable" | ring2, modules, sketch_port |
| Missing module file not detected | ~2 | `(mod nonexistent)` silently succeeds | ring2, modules |
| Synthetic primitives not scoped | ~6 | bare `add-i64` works without import | ring2, repl_negative |
| IO/platform execution hangs | ~65 | IO actions timeout at 9s; platform DLL pipeline broken | io, lenient |
| Lenient/par-bind scheduling | ~16 | all lenient eval tests fail or timeout | lenient |
| Prelude fixture loading | ~24 | "unknown trait: Functor" from fixture prelude | ring4_trace |
| E2E subprocess tests | ~46 | prompts, /expand not in v4, run-tests, imports | e2e |
| Cache pipeline | ~20 | multi-module/prelude caching broken | cache |
| Multi-sig panic | 1 | `Defn::params()` on `DefnMulti` without guard | ring2 |
| Macro error recovery | ~4 | REPL macro error handling regressions | macros, ring3_repl |
| Trait method as value | 2 | using trait method as bare value fails | ring2 |
| display_imported_option | 2 | imported Option display formatting | repl_experience |
| sketch_port new | ~28 | additional sketch_port regressions beyond pre-existing 11 | sketch_port |

## Ignored Tests

Tests marked `#[ignore]` due to infrastructure limitations, not spec violations.

| Suite | Count | Reason |
|-------|-------|--------|
| Various | ~10 | Panic-path tests — `cranelisp_panic` calls `process::exit(1)`, killing the test harness |

## Handling Failures

- **Expected failure (in known failures table):** Note it, continue to next suite.
- **New failure in a previously-passing suite:** STOP. Investigate. If it's a regression from the current work, fix before continuing. If environment-specific, document and continue.
- **Timeout (>30s):** Almost certainly a hang. Kill it. Check for `wait_object_complete` calls or deadlock in worker threads.
- **Compilation error:** Fix first. No point running tests that don't compile.

## After Verification

When all phases complete with only expected failures:

1. Update the known failures table above with any changes.
2. Update test counts if they've changed.
3. Note the "assess" suites' actual results so the next verification run has baselines.
