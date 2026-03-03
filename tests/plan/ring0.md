# Ring 0 Test Plan: Core

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

## Acceptance Gate

- All ~80 tests pass in both batch and REPL
- `cargo clippy` clean
- No `unwrap()` in pipeline code
- `/review` approves Ring 0
