# Ring 0 Test Plan: Core

<!-- /learn tutorial engine (U0.2): Acknowledged. The /learn command requires REPL implementation
     work (watch mechanism, trigger evaluation, progress tracking). This is deferred to Ring 4+
     since it needs the full REPL infrastructure (slash commands, session state, IO). /qa will
     write acceptance tests for /learn when the feature is scoped into a sprint. Curriculum data
     lives in user/tutorial/curriculum.md. -->

**Features**: Int, Bool, Float, simple Fn, let, if, match (enums only), defn, forward references, TCO. No heap allocation, no reference counting.

**Test count target**: ~80 integration tests (ported from prototype + new).

## Tests to Port (from prototype, directly portable)

### Core Batch (spec: 04-expressions)
- `hello`, `factorial`, `fibonacci`, `nested_let`, `chained_function_calls`
- `comparison_operators`, `forward_reference`, `arithmetic`, `nested_if`

### REPL Basics (spec: 04-expressions, 12-runtime)
- `repl_eval_expression`, `repl_define_and_call`, `repl_chained_calls`
- `repl_redefinition_updates_callers`, `repl_recursive_function`
- `repl_type_error_recovers`, `repl_multiple_params`

### Lambdas (spec: 04-expressions)
- `lambda_immediate_call`, `lambda_in_let`, `lambda_passed_to_function`
- `named_function_as_value`, `lambda_zero_params`, `lambda_multi_params`
- `repl_lambda_immediate`, `repl_lambda_in_let`
- `repl_higher_order_function`, `repl_named_function_as_value`

### TCO (spec: 12-runtime)
- `tco_deep_countdown`, `tco_accumulator`, `tco_match_tail_position`
- `tco_let_body_tail_position`, `tco_non_tail_recursion_unchanged`

### Floats (spec: 03-types)
- `float_arithmetic`, `float_comparison`, `float_type_error_mixed`
- `repl_float_eval`, `repl_float_arithmetic`

### Errors (spec: various)
- `type_error_add_bool`, `error_type_error_int_plus_bool`, `error_type_error_bool_as_int`
- `error_parse_error_unclosed_paren`, `error_parse_error_extra_closing_paren`
- `error_unbound_symbol`, `error_wrong_arity_too_many_args`, `error_wrong_arity_too_few_args`
- `error_type_mismatch_if_branches`, `error_defn_body_type_mismatch`

### ADT Enums — no heap fields (spec: 03-types, 06-pattern-matching)
- `adt_enum_match`, `repl_adt_enum`, `repl_adt_enum_match`
- `error_non_exhaustive_match_caught_at_compile_time`

## New Tests (not in prototype)

- Dual-mode parity tests (every batch test also runs in REPL via `compile_both()`)
- Parser edge cases for spec 01-lexical and 02-grammar coverage:
  - Whitespace handling, comment stripping, nested parentheses
  - Operator symbol parsing (`+`, `-`, `*`, `/`, `=`, `<`, `>`, `<=`, `>=`)
  - Negative integer parsing (`-3` as integer, not operator)
- `CompileMode::Batch` vs `CompileMode::Interactive` produce identical results

## REPL Spec Compliance (repl/spec.md)

<!-- Acknowledged: These 10 REPL spec non-conformance items are tracked as U1.13 in tests/plan/usability.md (blocking severity). Tests will be written as part of the REPL implementation work. The table below documents the gap and expected behavior for each requirement. Resolved from FIXME at design/arch/roadmap.md:35. -->

| Spec Section | Requirement | Ring | Current Behavior | Priority |
|---|---|---|---|---|
| §1.3 | Definition result shows name: `:(Fn [Int] Int) user/double` | 0 | Shows `<closure>` instead of name | blocking |
| §1.4 | Type names fully qualified: `primitives/Int` | 0 | Shows bare `Int` | blocking |
| §1.5 | ADT constructors use `Type.Ctor` notation: `Color.Red` | 0 | Shows bare `Red` | blocking |
| §2.1 | Prompt shows `{compile}+{eval}ms; {module}>` | 0 | Shows bare `> ` | important |
| §3.1 | Slash commands work: `/help`, `/sig`, `/list`, etc. | 0 | `/` parsed as division → `error: undefined variable: /` | blocking |
| §4.1 | Bare function lookup shows type + qualified name | 0 | Shows `<closure>` for Fn types | blocking |
| §4.1 | Bare type name lookup (`Int`) shows type info | 0 | `error: undefined variable: Int` | blocking |
| §4.1 | Bare trait name lookup (`Num`) shows trait info | 0 | `error: undefined variable: Num` | blocking |
| §4.2 | Bare special form (`if`) shows shape | 0 | Error instead of shape display | blocking |
| §6.2 | Startup banner with name, version, `/help` hint | 0 | No banner | blocking |

## Acceptance Gate

- All ~80 tests pass in both batch and REPL
- `cargo clippy` clean
- No `unwrap()` in pipeline code
- `/review` approves Ring 0
