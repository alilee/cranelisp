# Ring 1 Test Plan: Heap

**Features**: String, ADT product/sum types, closures, capturing, RC (alloc/inc/dec/drop glue). Heap management established as a clean layer over Ring 0.

**Test count target**: ~130 additional tests (~210 cumulative).

## Tests to Port

### Strings (spec: 03-types, 01-lexical)
- `string_literal_print`, `string_in_let`, `repl_string_literal`

### ADT Products/Sums (spec: 03-types, 06-pattern-matching)
- `adt_product_construct_and_match`, `adt_product_get_y`
- `adt_sum_type_some_none`, `adt_sum_type_none_case`
- `adt_match_wildcard`, `adt_match_var_pattern`, `adt_nested_match`, `adt_shortcut_syntax`
- `repl_adt_product`, `repl_adt_sum_type`, `repl_adt_constructor_describes`

### Accessors (spec: 03-types)
- `adt_product_accessor_x`, `adt_product_accessor_y`
- `adt_accessor_in_function`, `adt_first_class_accessor`
- `adt_first_class_constructor`, `adt_sum_accessor`
- `repl_adt_accessor`, `repl_adt_first_class_accessor`

### Closures (spec: 04-expressions)
- `closure_simple_capture`, `closure_multiple_captures`
- `closure_returned_from_function`, `closure_nested`
- `repl_closure_simple`, `repl_closure_multiple_captures`
- `closure_with_higher_order`
- `operator_as_value`, `operator_auto_curry`, `operator_higher_order`

### Exhaustiveness (spec: 06-pattern-matching)
- `non_exhaustive_match_is_compile_error`, `exhaustive_match_all_constructors`
- `exhaustive_match_with_wildcard`, `exhaustive_match_with_var_pattern`
- `non_exhaustive_option_missing_none`, `exhaustive_match_product_type`
- `exhaustive_match_non_adt_scrutinee`

### RC Tests — all 57 from `sketch/tests/rc.rs` (spec: 12-runtime)
- Phase 2D scope-level dec (4 tests)
- Phase 2E drop glue (5 tests)
- Phase 3 vec RC (4 tests)
- Step 11 sound RC (7 tests)
- Consuming calling convention (7 tests)
- Compound temp arg tests (3 tests)
- Liveness-based last-use optimization (5 tests)
- Vec element RC + COW step 11H (8 tests)
- Uniqueness tracking + borrowed reads step 11J-K (8 tests)
- Gap 1: closures escaping/stored in ADTs (4 tests)
- Gap 2: user-defined recursive ADTs (2 tests)

## New Tests

- RC tests for every heap-typed expression form
- String concatenation RC (alloc, use, free)
- ADT drop glue for nested heap types (e.g., `(Some "hello")` — drops both the Some and the String)
- Closure environment RC (captured heap values freed when closure is freed)

## Acceptance Gate

- `CRANELISP_RC_TRACE=1` shows balanced inc/dec for all tests
- No memory leaks detected by runtime tracking
- All Ring 0 tests still pass (regression)
- `/review` approves Ring 1
