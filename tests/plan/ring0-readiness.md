# Ring 0 Test Plan Readiness

Cross-reference of `tests/plan/ring0.md` against Ring 0 acceptance criteria from `design/arch/roadmap.md`. Prepared by `/qa` during Sprint 0.

## Acceptance Criteria Coverage

| # | Criterion (display per `repl/spec.md`) | Test Plan Coverage | Status |
|---|---|---|---|
| 1 | `(+ 1 2)` → `:primitives/Int 3` | `arithmetic` (Core Batch) | covered |
| 2 | `(defn id [x] x)` → `:(Fn [a] a) user/id` | Not explicitly listed | **gap** |
| 3 | `(if true 1 2)` → `:primitives/Int 1` | `nested_if` (Core Batch) covers `if`; no test for this exact expression | covered (subsumes) |
| 4 | `(let [x 5] (+ x 1))` → `:primitives/Int 6` | `nested_let` (Core Batch) | covered |
| 5 | `(deftype Color Red Green Blue)` + `(match Color.Red [Color.Red 1 Color.Green 2 Color.Blue 3])` → `:primitives/Int 1` | `adt_enum_match` (ADT Enums) | covered |
| 6 | Factorial runs correctly (note: given formulation is NOT tail-recursive; TCO tested by accumulator variants) | `factorial` (Core Batch) + `tco_deep_countdown`, `tco_accumulator` (TCO) | covered |
| 7 | Batch and REPL produce identical results (shared `compile_unit()` pipeline via `CompileMode`) | Dual-mode parity tests (New Tests) + paired batch/REPL test variants | covered |
| 8 | ~50 integration tests green | Plan targets ~80 (50 ported + ~30 new) | covered (exceeds) |
| 9 | REPL experience tests: discoverability, value+type feedback (see `repl/spec.md`) | Not explicitly listed in ring0.md | **gap** |
| 10 | `cargo clippy` clean, no `unwrap()` in pipeline code | Listed in Acceptance Gate section | covered |

## Gaps

### Gap 1: Polymorphic type inference test (criterion 2)

The acceptance criterion `(defn id [x] x)` → `:(Fn [a] a) user/id` specifically tests let-polymorphism and type inference display. The Ring 0 test plan lists no test that asserts a polymorphic type scheme as output. Tests like `forward_reference` and the lambda tests exercise polymorphism indirectly (through usage), but no test explicitly checks that:

- The inferred type is polymorphic (quantified over a type variable)
- The REPL output displays the type in `:Type qualified-name` format per `repl/spec.md`

**Recommendation**: Add an explicit integration test `polymorphic_identity_inference` that defines `(defn id [x] x)`, calls `(id 42)` and `(id true)`, and asserts both the inferred scheme and the correct dispatch. Add a REPL variant that asserts the displayed output is `:(Fn [a] a) user/id`.

### Gap 2: REPL experience tests (criterion 9)

The roadmap requires "REPL experience tests pass: discoverability, value+type feedback." The ring0.md plan has REPL *functionality* tests (eval, define, call, redefinition) but no tests for:

- `/help` command produces useful output
- Value display includes type annotation (e.g. `:primitives/Int 3`, not just `3`)
- Error messages are recoverable (listed as `repl_type_error_recovers`, which partially covers this)
- Prompt appearance and basic UX flow

The `/repl` skill's Ring 0 deliverables in the roadmap are: "Basic REPL experience tests: prompt, `/help`, value+type display, error messages." These are not reflected in ring0.md.

**Recommendation**: Add a REPL experience subsection to ring0.md with tests:
- `repl_help_command` -- `/help` produces output listing available commands
- `repl_value_type_display` -- `(+ 1 2)` displays `:primitives/Int 3` (not just `3`)
- `repl_prompt_display` -- prompt appears correctly
- `repl_error_recovery` -- type error does not crash the session (partially covered by `repl_type_error_recovers`)

These may be E2E tests (Layer 4) rather than integration tests, since they test the user-visible experience.

## Test Helper Analysis

### `compile_and_run_simple(src)` vs `compile_unit()`

The test helper `compile_and_run_simple(src)` from `tests/CLAUDE.md` is the integration test entry point for Ring 0. It maps to the `compile_unit()` function defined in `design/arch/architecture.md`:

```rust
pub fn compile_unit(
    frontend: &Frontend,
    typechecker: &mut TypeChecker,
    backend: &mut Backend,
    source: &str,
    mode: CompileMode,
) -> Result<CompileResult, CranelispError>
```

`compile_and_run_simple(src)` should internally:
1. Construct a `Frontend`, `TypeChecker`, and `Backend`
2. Call `compile_unit(frontend, &mut typechecker, &mut backend, src, CompileMode::Batch)`
3. Execute the result and return the output value

This is consistent. The "simple" suffix indicates no macro support (MacroExpander is a no-op stub in Ring 0), which aligns with the architecture since `MacroExpander` is stubbed until Ring 3.

### `compile_both(src)` vs `CompileMode`

`compile_both(src)` runs the same source through both `CompileMode::Batch` and `CompileMode::Interactive`, asserting identical results. This directly validates acceptance criterion 7 (batch/REPL parity). The helper should:
1. Call `compile_unit()` with `CompileMode::Batch`, execute, record result
2. Call `compile_unit()` with `CompileMode::Interactive`, execute, record result
3. Assert both results are identical

This is consistent with the architecture's single-pipeline design.

### `assert_type_error(src, msg)` and `assert_parse_error(src, msg)`

These helpers exercise `CranelispError::TypeError` and `CranelispError::ParseError` respectively. They should:
1. Call `compile_unit()` (or the relevant stage for parse errors)
2. Assert the result is `Err` with the expected error variant
3. Assert the error message contains `msg` (substring match, per test standards)

Consistent with the error types in `design/arch/interfaces.md`. The substring matching approach (rather than exact string comparison) is correct for maintainability.

### `repl_session()` helper

Not listed in the acceptance criteria check but present in `tests/CLAUDE.md`. Creates a persistent session for multi-step REPL interaction tests. Consistent with the REPL architecture (thin loop over `compile_unit()` with persistent `TypeChecker` and `Backend` state).

### Consistency verdict

All four test helpers align with the architectural interfaces. No signature mismatches detected. The helpers abstract over `compile_unit()` correctly, and the `CompileMode` parameter is properly surfaced through `compile_both()`.

## Prototype Baseline

```
Prototype test suite (sketch/):
  500 passed, 2 failed, 10 ignored
  Total: 512 tests (500 passing)
  Failures: exe_build_and_run_with_platform, exe_build_and_run_without_platform
  Wall clock: ~14 seconds
```

The 2 failures are in executable-generation tests (`exe_build_and_run_*`), which are Ring 4 scope. The 10 ignored tests are deferred features. The 500 passing tests establish the acceptance baseline.

### Test mapping to Ring 0

The Ring 0 test plan targets ~80 integration tests. Of the 500 prototype passing tests, approximately 50 map directly to Ring 0 features (core expressions, basic types, simple functions, enums, TCO). The remaining ~450 tests cover Rings 1-4 features (heap, strings, ADTs with fields, closures, traits, modules, macros, IO, platforms).

The Ring 0 plan adds ~30 new tests not in the prototype (dual-mode parity, parser edge cases, boundary tests), bringing the total to ~80 -- exceeding the roadmap's ~50 target.

## Sprint 0 FIXME Resolution Impact

Changes made during Sprint 0 FIXME resolution that affect the test plan:

1. **`par-let` removed from spec**: No impact on Ring 0 tests (par-let was Ring 4). Ring 4 test plan should replace par-let tests with lenient evaluation tests.
2. **Interface newtypes**: All boundary types now use `Symbol`, `TypeName`, `TraitName`, etc. instead of bare `String`. Test helpers must construct newtypes (e.g., `Symbol::from("x")` not `"x".to_string()`).
3. **`CompileMode` has 3 variants**: `Interactive`, `Batch`, `Release`. Ring 0 exercises Interactive and Batch. `compile_both()` helper unchanged.
4. **REPL experience spec**: `repl/spec.md` now exists with testable requirements. REPL experience tests (Gap 2 above) should reference this spec.
5. **Roadmap match syntax corrected**: Tests using match should use bracket syntax `(match scrut [Pat body ...])`.
6. **Operators are builtins in Ring 0**: `+`, `-`, `*`, etc. are `ResolvedCall::BuiltinFn` in Ring 0. Test assertions about operator resolution should expect `BuiltinFn`, not `TraitMethod`.

## Summary

- **8 of 10** acceptance criteria are covered by the Ring 0 test plan
- **2 gaps** identified: polymorphic inference display test and REPL experience tests
- **Test helpers** are consistent with the architecture (updated for newtypes)
- **Prototype baseline**: 500 passing tests; ~50 map to Ring 0
- **Test count**: ring0.md targets ~80, roadmap requires ~50 -- plan exceeds target
