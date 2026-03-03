# Ring 4 Test Plan: Effects

**Features**: IO model, platform DLLs, par-let, par-bind!, trace, run-tests, REPL slash commands, caching, linking, executable generation, hot-reload, lenient evaluation. Side effects and build infrastructure.

**Test count target**: ~120 additional tests (~591 cumulative, matching prototype).

## Tests to Port

### IO / do / pure / bind (spec: 10-io)
- `do_sequences_effects`, `pure_lifts_value`, `bind_extracts_and_continues`
- `do_with_pure_in_if`, `bind_chain`, `full_io_program`
- `repl_do_expression`, `repl_pure_expression`, `repl_bind_expression`
- `builtin_as_value`, `repl_builtin_as_value`

### bind! sugar (spec: 10-io)
- `bind_bang_single_binding`, `bind_bang_multiple_bindings`, `bind_bang_with_print`
- `repl_bind_bang`
- `parse_bind_bang_is_apply`, `parse_bind_bang_two_bindings_is_apply`

### parse-int (spec: appendix-a-builtins)
- `parse_int_valid`, `parse_int_invalid`, `parse_int_empty_string`
- `parse_int_negative`, `parse_int_whitespace`, `repl_parse_int`

### Platform (spec: 12-runtime) — all 9 from `sketch/tests/platform.rs`
- `test_stdio_dll_loads_and_provides_manifest`, `test_capture_dll_loads_and_provides_manifest`
- `test_abi_version_matches`, `test_capture_print_hello`
- `test_capture_print_multiple_lines`, `test_capture_read_input`
- `test_capture_multiple_reads`, `test_capture_reset_clears_state`
- `test_capture_empty_input_returns_empty_string`

### Platform declaration (spec: 12-runtime)
- `batch_platform_nonexistent_error`, `batch_platform_missing_argument_error`

### Trace — all 14 from `sketch/tests/trace.rs` (spec: 12-runtime)
- Phase 1: `trace_literal_returns_trace_call`, `trace_root_name_is_trace_sentinel`, `trace_literal_has_no_children`, `trace_factorial_has_children`, `trace_factorial_first_child_name`, `trace_nanos_is_positive`, `trace_depth_factorial_4`, `trace_flatten_nonempty`, `trace_fib_has_subtree`
- Phase 2: `trace_factorial_first_child_has_params`, `trace_factorial_first_child_param_value`, `trace_factorial_first_child_result_value`, `trace_call_string_correct_form`, `trace_show_tree_nonempty`

### Run-tests — all 9 from `sketch/tests/run_tests.rs` (spec: 12-runtime)
- `run_tests_pass_fn_called_for_passing_tests`, `run_tests_fail_fn_called_for_failing_tests`
- `run_tests_pass_fn_receives_positive_nanos`, `run_tests_fail_fn_receives_positive_nanos`
- `run_tests_fail_fn_receives_valid_trace`, `run_tests_fail_trace_has_depth`
- `run_tests_total_count_is_pass_plus_fail`
- `run_tests_pass_fn_name_is_nonempty`, `run_tests_fail_fn_reason_is_nonempty`

### Testing library (spec: 11-stdlib)
- `repl_run_tests_finds_test_functions`, `test_assertions_library`

### Cache (spec: 12-runtime)
- Write & structure: `cache_write_creates_files`, `cache_two_tier_separation`
- Hit correctness: `cache_hit_produces_same_output`, `cache_hit_with_macros`
- Source invalidation: `cache_adt_and_traits_from_cache`, `cache_source_invalidation`
- Error recovery: `cache_multimodule_partial_invalidation`, `cache_corrupted_meta_recovery`, `cache_missing_meta_file_recovery`, `cache_deleted_cache_dir_recovery`, `cache_manifest_version_mismatch`
- Multi-module: `cache_multimodule_project`, `cache_no_cache_dir_initially`
- Round-trip: `cache_macro_round_trip`, `cache_multisig_round_trip`
- REPL cache: `repl_cache_write_creates_files`, `repl_cache_hit_second_run`, `repl_cache_project_module`, `repl_restart_restores_user_definitions`

### Standalone executable (spec: 12-runtime)
- `exe_build_and_run_with_platform`, `exe_build_and_run_without_platform`

### Checked arithmetic (spec: 12-runtime)
- Normal ops: `checked_arithmetic_normal_add`, `checked_arithmetic_normal_sub`, `checked_arithmetic_normal_mul`, `checked_arithmetic_normal_div`, `checked_arithmetic_negative_values`, `checked_arithmetic_max_no_overflow`
- `raw_primitive_add_wraps`, `float_div_zero_returns_infinity`
- Panic ops (formerly ignored — should become normal tests with redesigned panic handler):
  - `checked_division_by_zero_panics`, `checked_add_overflow_panics`, `checked_sub_overflow_panics`, `checked_mul_overflow_panics`, `checked_div_min_neg1_panics`
- Vec bounds (formerly ignored): `vec_get_out_of_bounds_panics`, `vec_get_negative_index_panics`, `known_issue_vec_out_of_bounds`

### par-let / bind / par evaluation (spec: 04-expressions, 12-runtime)
- `par_let_basic`, `par_let_with_computation`, `par_let_with_captures`
- `par_let_independence_error`, `par_let_single_binding_error`, `par_let_three_bindings`
- `bind_two_io`, `bind_type_error_non_io`, `bind_body_must_be_io`, `bind_three_io`
- `par_let_example_file`

### Lenient evaluation (spec: 12-runtime)
- `lenient_two_independent_calls`, `lenient_dependent_bindings_not_sparked`
- `lenient_mixed_independent_dependent`, `lenient_trivial_bindings_not_sparked`
- `lenient_single_sparkable_not_sparked`, `lenient_heap_typed_results`
- `lenient_closures_with_captures`, `lenient_nested_let`
- `lenient_cheap_builtins_excluded`, `lenient_three_independent_calls`

### E2E transcript tests — all 4 pairs
- `basic_exprs`, `defn_and_call`, `reader_shortcuts`, `slash_help`

### REPL slash commands (spec: 12-runtime)
- Existing: `repl_slash_sig_user_fn`, `repl_slash_sig_builtin`, `repl_slash_type_expression`, `repl_slash_type_bool_expression`, `repl_slash_info_user_fn`, `repl_slash_info_constructor`, `repl_slash_list_finds_user_fn`, `repl_slash_list_prelude_symbols`
- New (8): `/doc`, `/source`, `/sexp`, `/ast`, `/clif`, `/disasm`, `/expand`, `/mod`

### Module system (spec: 08-modules)
- `example_modules` (now with IO support)
- `repl_full_session_print_not_visible_without_platform` (now with platform support)

### Known issue tests — rewritten for correct behavior
- `ambiguous_trait_method_dotted_name_works` (formerly ignored)
- `dotted_field_accessor_resolution` (formerly ignored)

## New Tests

- Performance benchmarks (reader, inference, codegen, JIT startup, REPL evaluation)
- Full REPL session tests (multi-definition, module navigation, hot-reload)
- Platform DLL error handling (missing DLL, ABI version mismatch, wrong ABI version)
- Hot-reload: file change triggers module reload, type-incompatible changes rejected
- IO trampoline: nested IO effects chain correctly
- Exemplar project compiles and runs (from `/port`)

## Acceptance Gate

- All ~591 tests pass (full parity with prototype)
- All E2E transcript tests pass
- Performance within 2x of prototype
- REPL experience tests pass (from `/repl`)
- Standard library passes all tests
- Example programs run correctly
- `cargo clippy` clean across all crates
- `/review` approves Ring 4
