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

## Sprint 25: Lenient Evaluation & Auto IO Scheduling

Derived from `design/backend/lenient-eval.md`, `design/backend/io-scheduling.md`,
`design/int/bind-chain-analysis.md`, `spec/12-runtime.md` §12.4.3, `spec/10-io.md` §10.12.

### Lenient Evaluation Tests (spec: 12-runtime §12.4.3)

These tests validate automatic parallelization of independent `let` bindings.
The existing sketch-ported tests (above, under "Lenient evaluation") cover
correctness of results. Sprint 25 adds tests for the design invariants:
sparkability analysis, IVar lifecycle, cost heuristic, opt-out, and timing.

#### Positive — Correctness

- `test_lenient_two_independent_calls` [EXISTING — port from sketch]
  // spec: spec/12-runtime.md §12.4.3 — independent let bindings parallelize
  Two independent function calls produce correct results.

- `test_lenient_mixed_independent_dependent` [EXISTING — port from sketch]
  // spec: spec/12-runtime.md §12.4.3 — mixed independent/dependent bindings
  Independent bindings sparkable, dependent binding sequential; correct result.

- `test_lenient_three_independent_calls` [EXISTING — port from sketch]
  // spec: spec/12-runtime.md §12.4.3 — three independent sparkable bindings
  Three independent function calls all produce correct results.

- `test_lenient_heap_typed_results` [EXISTING — port from sketch]
  // spec: spec/12-runtime.md §12.4.3 — heap-typed results survive parallel eval
  String (heap-typed) values correct after lenient evaluation.

- `test_lenient_closures_with_captures` [EXISTING — port from sketch]
  // spec: spec/12-runtime.md §12.4.3 — thunks capture enclosing scope
  Sparked thunks correctly capture variables from enclosing scope.

- `test_lenient_nested_let` [EXISTING — port from sketch]
  // spec: spec/12-runtime.md §12.4.3 — nested lets have independent sparkability
  Inner let block has its own spark group, independent of outer let.

#### Positive — Sparkability Analysis

- `test_lenient_sparkability_fn_calls_qualify` [NEW]
  // spec: spec/12-runtime.md §12.4.3 — function calls are sparkable
  Positive. User-defined function calls (Expr::Apply with non-cheap callee)
  are sparkable. Verify via correct parallel result with >=2 such bindings.

- `test_lenient_sparkability_computed_callee` [NEW]
  // spec: spec/12-runtime.md §12.4.3 — computed callees are sparkable
  Positive. Non-variable callees `((get-fn) arg)` are conservatively treated
  as worth sparking (cost unknown). Verify correct result.

- `test_lenient_sparkability_minimum_two_required` [NEW]
  // spec: spec/12-runtime.md §12.4.3 — at least 2 sparkable bindings required
  Positive. Exactly 2 sparkable, independent bindings activate lenient eval.
  Verify via timing: parallel should complete faster than 2x sequential for
  expensive computations (e.g., `fib 30`).

- `test_lenient_timing_parallel_faster_than_sequential` [NEW]
  // spec: spec/12-runtime.md §12.4.3 — parallel is faster than sequential
  Positive. Two independent expensive computations (e.g., `fib 30`) in a let.
  Measure wall-clock time. Compare against `CRANELISP_NO_LENIENT=1` sequential
  baseline. Parallel should be measurably faster (< 1.5x single computation,
  vs ~2x for sequential). This is the primary observability test for lenient
  eval actually happening.

#### Positive — Opt-Out

- `test_lenient_no_lenient_env_disables` [NEW]
  // spec: spec/12-runtime.md §12.4.3 — CRANELISP_NO_LENIENT=1 disables sparking
  Positive. Set `CRANELISP_NO_LENIENT=1` env var. Two independent expensive
  function calls in a let. Verify same correct result. Verify timing is
  sequential (approximately 2x single computation, not parallel).

#### Positive — Trace Exclusion

- `test_lenient_trace_body_no_sparking` [NEW]
  // spec: spec/12-runtime.md §12.4.3 — trace bodies disable sparkability
  Positive. Inside `(trace ...)`, independent let bindings are NOT sparked
  (to preserve deterministic trace output). Verify correct result with trace
  wrapping expensive let bindings.

#### Negative — No Sparking Cases

- `test_lenient_neg_single_sparkable_no_ivar` [NEW]
  // spec: spec/12-runtime.md §12.4.3 — single sparkable binding: no IVar
  Negative. Only one function call binding plus one literal binding. The
  single sparkable binding does not trigger IVar creation. Verify correct
  result (no crash, no overhead).

- `test_lenient_neg_all_cheap_no_ivar` [NEW]
  // spec: spec/12-runtime.md §12.4.3 — all cheap bindings: no IVar
  Negative. All bindings are cheap builtins (+, *, literals). No IVar
  creation. Verify correct result.

- `test_lenient_neg_dependent_binding_sequential` [NEW]
  // spec: spec/12-runtime.md §12.4.3 — dependent binding forces sequential
  Negative. Binding `b` references binding `a`. Even though both are function
  calls, they are NOT sparked because `b` depends on `a`. Verify correct
  result (sequential evaluation).

- `test_lenient_neg_cheap_builtins_not_sparkable` [NEW]
  // spec: spec/12-runtime.md §12.4.3 — cheap builtins excluded from sparking
  Negative. Bindings using `+`, `-`, `*`, `/`, `=`, `<`, `>`, `<=`, `>=`,
  `not`, `and`, `or` as callees are not sparkable even if independent.
  Verify correct result.

- `test_lenient_neg_literals_not_sparkable` [NEW]
  // spec: spec/12-runtime.md §12.4.3 — literals not sparkable
  Negative. Bindings whose expressions are literals (Int, Bool, String) or
  variable references are not sparkable. Verify correct result.

### Auto IO Scheduling Tests (spec: 10-io §10.12)

These tests validate automatic parallelization of commutative, data-independent
IO effects in `bind!` chains. Tests require a `test-capture` platform DLL with
commutative test functions (to be provided by `/platform` in Wave 2).

**Infrastructure needed (Wave 2 prerequisite from /platform):**
- A commutative test function in the test-capture platform DLL (e.g.,
  `test-sleep-ms` with `SchedulingClass::Commutative` + configurable delay).
- A `ResourceSerial` test function with configurable resource tokens.
- Timing-based test helper for parallelism verification.

#### Positive — Par Node Generation

- `test_io_schedule_commutative_pair_parallel` [NEW]
  // spec: spec/10-io.md §10.12.1 — commutative + data-independent => Par node
  Positive. Two data-independent calls to a Commutative platform function in
  a `bind!` chain produce a `Par` node. Verify via timing: two 50ms sleeps
  should complete in ~50ms (parallel) not ~100ms (sequential).

- `test_io_schedule_three_commutative_parallel` [NEW]
  // spec: spec/10-io.md §10.12.1 — three commutative bindings all parallelize
  Positive. Three data-independent Commutative calls. All three dispatched
  concurrently. Verify via timing.

- `test_io_schedule_mixed_sequential_commutative` [NEW]
  // spec: spec/10-io.md §10.12.1 — mixed chain segments correctly
  Positive. A `bind!` chain with: commutative pair, then a sequential call,
  then another commutative pair. The two commutative pairs form separate
  `Par` nodes; the sequential call separates them. Verify correct result
  ordering and timing.

- `test_io_schedule_result_ordering_preserved` [NEW]
  // spec: spec/10-io.md §10.12.5 — results array preserves binding order
  Positive. Two commutative calls returning distinct values. Regardless of
  which completes first, results are bound to the correct names (source order).

#### Positive — Resource Token Serialization (§10.12.4)

- `test_io_schedule_resource_serial_different_tokens_parallel` [NEW]
  // spec: spec/10-io.md §10.12.4 — different resource tokens run concurrently
  Positive. Two `ResourceSerial` calls with different resource tokens in a
  `bind!` chain. They are data-independent and have distinct tokens, so they
  run concurrently. Verify via timing.

- `test_io_schedule_resource_serial_same_token_sequential` [NEW]
  // spec: spec/10-io.md §10.12.4 — same resource token serializes
  Positive. Two `ResourceSerial` calls with the same non-zero resource token.
  They are serialized even though they are data-independent. Verify via timing:
  two 50ms calls should take ~100ms, not ~50ms.

- `test_io_schedule_resource_serial_mixed_tokens` [NEW]
  // spec: spec/10-io.md §10.12.4 — mixed tokens: group by token
  Positive. Four `ResourceSerial` calls: two with token A, two with token B.
  The two token-A calls are serialized as one work item; the two token-B calls
  are serialized as another work item. The two work items run concurrently.
  Verify via timing.

- `test_io_schedule_unrestricted_token_zero_parallel` [NEW]
  // spec: spec/10-io.md §10.12.4 — token=0 branches run independently
  Positive. Commutative calls (token=0) each dispatched as independent work
  items. Verify they run concurrently.

#### Positive — Sequential Preservation

- `test_io_schedule_sequential_platform_not_parallelized` [NEW]
  // spec: spec/10-io.md §10.12.2 — Sequential scheduling class preserves order
  Positive. Two calls to a Sequential platform function (e.g., `read-line`,
  `print`). They remain sequential even if data-independent. Verify via
  timing: two 50ms sequential calls take ~100ms.

#### Positive — Opt-Out

- `test_io_schedule_no_io_schedule_env_disables` [NEW]
  // spec: spec/10-io.md §10.12 — CRANELISP_NO_IO_SCHEDULE=1 disables
  Positive. Set `CRANELISP_NO_IO_SCHEDULE=1`. Two commutative, data-independent
  calls remain sequential. Verify same correct result. Verify timing is
  sequential.

#### Negative — No Par Node Cases

- `test_io_schedule_neg_data_dependent_no_par` [NEW]
  // spec: spec/10-io.md §10.12.1 — data-dependent pair: no Par node
  Negative. Two Commutative calls where the second uses the first's binding
  name. No `Par` node emitted even though both are Commutative. Verify
  correct result (sequential evaluation).

- `test_io_schedule_neg_single_binding_no_par` [NEW]
  // spec: spec/10-io.md §10.12.1 — single binding: no Par node
  Negative. A `bind!` chain with only one binding. No `Par` node (minimum 2
  required for parallelization). Verify correct result.

- `test_io_schedule_neg_no_platform_no_scheduling` [NEW]
  // spec: spec/10-io.md §10.12 — no platform functions: pass is skipped
  Negative. A program with no platform declarations. The bind chain analysis
  pass is skipped entirely (scheduling registry is empty). Pure `bind!` with
  `pure` calls remains sequential. Verify correct result.

- `test_io_schedule_neg_wrapper_fn_not_analyzed` [NEW]
  // spec: spec/10-io.md §10.12.1 — wrapper fns are conservatively Sequential
  Negative. A user-defined function that wraps a Commutative platform call.
  The analysis does not chase through function bodies, so the wrapper is
  classified as Sequential. The pair is NOT parallelized. Verify correct result.

### Bind Chain Analysis Unit-Level Tests (design: bind-chain-analysis.md)

These tests validate the AST transformation pass that produces `Expr::ParBind`
nodes. They test the analysis logic, not the runtime dispatch.

#### Pattern Recognition

- `test_io_schedule_pattern_bind_chain_recognized` [NEW]
  // spec: spec/10-io.md §10.12 — bind chain pattern detection
  Positive. Expanded `bind!` AST (nested Apply/Lambda) is recognized as a
  bind chain.

- `test_io_schedule_pattern_non_bind_ignored` [NEW]
  // spec: spec/10-io.md §10.12 — non-bind expressions pass through unchanged
  Negative. Expressions that are not bind chains pass through the analysis
  unchanged (no transformation).

#### Chain Flattening

- `test_io_schedule_chain_two_deep` [NEW]
  // spec: spec/10-io.md §10.12 — 2-deep bind chain collected correctly
  Positive. Two-element bind chain flattened to 2 bindings + body.

- `test_io_schedule_chain_three_deep` [NEW]
  // spec: spec/10-io.md §10.12 — 3-deep bind chain collected correctly
  Positive. Three-element bind chain flattened to 3 bindings + body.

#### Grouping

- `test_io_schedule_group_two_commutative_produces_parbind` [NEW]
  // spec: spec/10-io.md §10.12.1 — two commutative independent => ParBind
  Positive. Two Commutative, data-independent bindings produce one
  `Expr::ParBind` node with 2 bindings.

- `test_io_schedule_group_single_element_demoted` [NEW]
  // spec: spec/10-io.md §10.12.1 — single-element group demoted to sequential
  Negative. One Commutative binding in a group of 1 is demoted back to a
  sequential bind call. No ParBind node.

- `test_io_schedule_group_nested_bind_chains_transformed` [NEW]
  // spec: spec/10-io.md §10.12 — nested bind chains inside lambdas also transformed
  Positive. Bind chains nested inside lambda bodies are recursively transformed.

#### Scheduling Classification

- `test_io_schedule_classify_bare_name_lookup` [NEW]
  // spec: spec/10-io.md §10.12.2 — bare platform fn name lookup
  Positive. Platform function looked up by bare name in scheduling registry.

- `test_io_schedule_classify_qualified_name_stripped` [NEW]
  // spec: spec/10-io.md §10.12.2 — qualified name stripped for lookup
  Positive. Qualified name `platform.stdio/print` stripped to `print` for
  registry lookup.

- `test_io_schedule_classify_unknown_defaults_sequential` [NEW]
  // spec: spec/10-io.md §10.12.2 — unknown fn defaults to Sequential
  Negative. Unknown function name defaults to `Sequential` classification.

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
