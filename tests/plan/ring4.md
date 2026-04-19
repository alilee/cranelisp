# Ring 4 Test Plan: Effects

**Features**: IO model, platform DLLs, par-let, par-bind!, trace, `discover-tests`/`run-test` builtins, `/run-tests` slash command, REPL slash commands, caching, linking, executable generation, hot-reload, lenient evaluation. Side effects and build infrastructure.

<!-- S57 FIXME resolution: the former `(run-tests init pass-fn fail-fn)` special form has been retired from the language. The testable surfaces are: (1) the `discover-tests` builtin (primitives/`discover-tests`, IO (List Sexp)), (2) the `run-test` builtin (primitives/`run-test`, IO TestResult), (3) the `/run-tests` REPL slash command, (4) the `sketch_run_tests_pass_fn_called` user-composition test that wires those builtins into a user-defined `my-run-tests`. `tests/plan/risks.md:4`'s "9 run-tests prototype tests" is historical context; the ported behaviour lives under the four surfaces above. -->

**Test count target**: ~120 additional tests (~591 cumulative, matching prototype).

<!-- The RC-balance assertion adoption survey is completed inline at §G.8 below (landed Sprint 57 Wave 5). See that section for: which Ring 4 test classes currently use the helper, which could adopt, which shouldn't, and the adoption-policy text for migration into `tests/CLAUDE.md` post-close. -->

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

## Sprint 56 Phase 2: Single Codegen Entry Point

Derived from:
- `design/typecheck/ast-annotation.md` §9 (Wave 0 — pre-materialise `ast` on mangled + mono entries)
- `design/backend/compile-to-module.md` §2.1, §4, §16 (Step 2a — 4-param signature, symbol-table-sourced collection)
- `design/int/phase2-codegen-convergence.md` §5, §7, §9, §10 (Step 2b — delete `codegen_module_symbols`; converge JIT + object on one entry point)

Baseline: 1590 passed / 22 failed / 0 ignored. Sprint 56 target: flip 3 multi-sig JIT tests green (-> 1593/19) with no regressions in the other 1590.

### A. Wave 0 — Typecheck Unit Tests (in `crates/cranelisp-typecheck/src/program.rs` / `traits.rs` `#[cfg(test)] mod tests`)

`/typecheck` owns these; `/qa` tracks them here because they gate Step 2a and the `defined_symbols()` contract is the shared predicate both backend and integration rely on. All six trace back to `design/typecheck/ast-annotation.md` §9.7.

1. `wave0_mangled_variant_carries_ast` [NEW]
   // spec: design/typecheck/ast-annotation.md §9.1 row 3 — mangled multi-sig variants carry annotated ast
   Positive + negative. Check `(defn add ([:Int a :Int b] ...) ([:Float a :Float b] ...))`. Assert both `add$Int+Int` and `add$Float+Float` are present as `ModuleEntry::Def { ast: Some(d), kind: UserFn { constrained_fn: None }, .. }` with `d.name == <mangled form>`. Negative: `add__v0` / `add__v1` internal names are NOT present; no cross-variant entries like `add$Float+Int` exist.

2. `wave0_mangled_variant_ast_is_annotated` [NEW]
   // spec: design/typecheck/ast-annotation.md §3.3 + §9.3 — final substitution on mangled ast
   Positive + negative. Walk the mangled entry's `ast` recursively; assert every `Expr` has `inferred_type.is_some()` AND no `inferred_type` is a `Type::Var(_)`. Assert the inner `add-i64` `Expr::Apply` has `resolved_call == Some(ResolvedCall::BuiltinFn { name: "add-i64" })`. Negative: no `Type::Var` leaks.

3. `wave0_overloaded_base_has_no_ast` [NEW]
   // spec: design/typecheck/ast-annotation.md §9.2 — Overloaded base carries `ast: None`
   Positive. Look up `add` (base name). Assert `kind: DefKind::Overloaded { variants }` and `ast: None`. The base entry is a dispatch index, not a compilable defn.

4. `wave0_mono_entry_registered` [NEW]
   // spec: design/typecheck/ast-annotation.md §9.4 — mono specialisations carry ast with concrete types
   Positive + negative. Check `(defn add [x y] (+ x y))` (constrained polymorphic) with a caller `(defn use-add [] (add 1 2))`. Assert `add` has `kind: UserFn { constrained_fn: Some(_) }` AND `ast: None` (template). Assert `add$Int+Int` has `ast: Some(_)` with fully concrete types on every `Expr`, `resolved_call` set on the inner `+` apply, and a `got_slot: Some(_)` distinct from any other slot.

5. `wave0_defined_symbols_filters_correctly` [NEW]
   // spec: design/typecheck/ast-annotation.md §9.5 — SymbolTable::defined_symbols contract
   Positive + negative. A program combining: one regular defn, one multi-sig, one constrained-polymorphic defn with one mono call site, one trait impl, one `deftype`, and one `(import [...])`. Positive: assert `defined_symbols()` yields the regular defn, both mangled multi-sig variants, the single mono specialisation, and the trait impl's mangled method. Negative: assert the `Overloaded` base, the constrained-fn template, the `TypeDef` entry, the `Import` entry, and any `TraitDecl`/`TraitImpl` index entry are ALL absent from the iterator.

6. `wave0_repl_multi_sig_carries_ast` [NEW]
   // spec: design/typecheck/ast-annotation.md §9.3 — REPL path uses the same registration
   Positive. Drive `check_repl_input_inner` with a `TopLevel::Defn` that is multi-sig. Assert the mangled variants on the REPL module's symbol table carry `ast: Some(_)`. Guards the REPL path through `check_repl_multi_sig` → `register_mangled_variants` (program.rs:2444).

**Wave 0 exit gate**: all 6 pass; full nextest baseline remains 1590/22.

### B. Step 2a — Backend Tests (in `crates/cranelisp-backend/src/` or `tests/boundary/`)

`/backend` owns unit coverage in the crate; `/qa` owns boundary tests that call `compile_to_module` directly without pipeline wiring. All four trace back to `design/backend/compile-to-module.md`.

7. `boundary_compile_to_module_four_param_signature` [NEW]
   // spec: design/backend/compile-to-module.md §2.1 — PRESCRIPTIVE 4-param signature
   Positive. Construct a populated `SymbolTable` with one `ModuleEntry::Def { ast: Some(d), .. }` for a trivial zero-arg defn returning `42`. Call `compile_to_module(path, &[name.clone()], &symbol_tables, &mut jit_module)`. Assert the returned `CompilationResult::func_ids` contains `name -> FuncId`. Assert `entry_func_id.is_some()` for zero-arg defns. This is the minimum-viable contract test — if the signature ever drifts, this test fails to compile.

8. `boundary_compile_to_module_ast_none_returns_named_error` [NEW]
   // spec: design/backend/compile-to-module.md §16.4 — `ast: None` returns CodegenError naming the symbol
   Negative. Populate a symbol table with a `ModuleEntry::Def { ast: None, .. }` entry (e.g., an `Overloaded` base or a synthesised template). Call `compile_to_module` with that name in `names`. Assert the returned `Err(CranelispError::CodegenError { message, .. })` with `message.contains(name)` AND no panic. Asserts the fail-loud contract — the backend must not silently skip unannotated entries.

9. `boundary_compile_to_module_no_multi_sig_expansion` [NEW]
   // spec: design/backend/compile-to-module.md §4 — expand_multi_sig_defn deleted in Step 2b
   Positive + structural. After Step 2b, the function `expand_multi_sig_defn` no longer exists in the backend crate. Verify either by (a) a compile-fails-if-reintroduced guard — a `#[cfg(test)] fn expand_removed()` that references the old symbol path and is expected NOT to resolve, OR (b) direct assertion that passing two mangled names for the same base (e.g., `add$Int+Int` and `add$Float+Float`) compiles both as independent defns — same shape as compiling two unrelated regular defns. No base-name entry appears in `names`. Preferred: (b) — structural behaviour test rather than a negative-reference compile check.

10. `boundary_compile_to_module_no_constrained_template_scan` [NEW]
    // spec: design/backend/compile-to-module.md §2.3 + §4 — SymbolTable::defined_symbols owns the filter
    Positive + negative. Populate a symbol table with both a constrained-fn template (`UserFn { constrained_fn: Some(_) }`) and its mono specialisation (`UserFn { constrained_fn: None }`). Caller computes `names = symbol_table.defined_symbols().collect()`. Positive: assert the mono is in `names` and is compiled (present in `CompilationResult::func_ids`). Negative: assert the template is NOT in `names` (filter applied once, at the iterator) AND does NOT appear in `func_ids`. If a caller erroneously passes the template name, §16.4 says the call returns `CodegenError` — a complementary negative test (8b) covers that explicitly.

### C. Step 2b — Integration Tests (in `tests/v4_codegen/` and `tests/v4_repl_eval/`)

`/qa` owns these. They exercise the full pipeline through the unified `compile_to_module` entry point. Traceability per `design/int/phase2-codegen-convergence.md` §10.3 + §10.1.

11. `sketch_multi_sig_type_based_dispatch` [DEFERRED → FLIP GREEN]
    // spec: spec/05-definitions.md §5.2 (multi-sig defn) + design/int/phase2-codegen-convergence.md §10.1 — JIT path converges with object path
    Positive. Existing test in `tests/sketch_port/multi_sig.rs`. Expected to flip from FAIL to PASS after Step 2b.2 lands.

12. `sketch_multi_sig_different_arities` [DEFERRED → FLIP GREEN]
    // spec: spec/05-definitions.md §5.2 — multi-sig dispatch by arity
    Positive. Existing test in `tests/sketch_port/multi_sig.rs`. Same flip-green target as #11.

13. `sketch_repl_multi_sig_different_arities` [DEFERRED → FLIP GREEN]
    // spec: spec/05-definitions.md §5.2 + repl/spec.md §4.1 — multi-sig dispatch works in REPL path
    Positive. Existing test in `tests/sketch_port/repl_multi_sig.rs`. Flip-green target for REPL convergence.

14. `v4_repl_eval_expr_compiles_via_compile_to_module` [NEW]
    // spec: design/int/phase2-codegen-convergence.md §6 — REPL `__expr` path unified
    Positive. REPL session. Drive `(+ 1 2)` as a bare expression. Assert: (a) evaluation returns `3`; (b) after eval, `symbol_tables[repl_module].get("__expr")` returns a `ModuleEntry::Def { ast: Some(_), got_slot: Some(_), .. }`; (c) `codegen_products[repl_module].code["__expr"].ptr` is non-null. Guards the §6 end-to-end REPL path.

15. `v4_codegen_batch_regular_plus_multi_sig_via_priority_worker` [NEW]
    // spec: design/int/phase2-codegen-convergence.md §5 — priority worker single entry point
    Positive. Batch compile a `.cl` file containing one regular defn (`(defn inc [x] (add-i64 x 1))`) AND one multi-sig defn (`(defn add ([:Int a :Int b] ...) ([:Float a :Float b] ...))`) AND a main entry that calls both. Assert exit code 0 and correct stdout via `run_binary(["--run", path], "")`. Stress the priority worker loop (§5 pseudocode) against a non-trivial mix.

16. `v4_codegen_cross_module_multi_sig_call` [NEW]
    // spec: spec/08-modules.md + design/int/phase2-codegen-convergence.md §5 — cross-module multi-sig resolution
    Positive. Two-module project: module `b` exports a multi-sig `add`; module `a` imports `b` and calls `(add 1 2)` and `(add 1.0 2.0)`. Assert both calls resolve to the correct mangled variant across module boundaries via the unified path. Guards that Import-chain resolution for mangled names works after the `CompilationEnv` consolidation (§3 replacement map).

17. `v4_codegen_structural_symbol_set_matches_defined_symbols` [NEW, from §10.3]
    // spec: design/int/phase2-codegen-convergence.md §10.3 — structural invariant
    Positive. After any module compile, assert `codegen_products[module].code.keys()` is a subset of `symbol_tables[module].defined_symbols().map(|(name, _)| name)`. The two sets should match for fully-compiled modules (no skipped names). This catches both over-compilation (names compiled that `defined_symbols` doesn't yield) and under-compilation (`defined_symbols` yields names that failed to compile). Structural regression guard.

18. `v4_codegen_regression_guard_baseline` [NEW, meta-test]
    // spec: sprint 56 acceptance — 1590 baseline preserved
    Positive. Not a discrete test but a sprint-close checklist item: full `cargo nextest run` produces at minimum 1590 passed + 0 new failures. Any passing test that regresses is a Step 2b fault. Tracked as a wave-gate in `sprints/SPRINT.md`, not a standalone `#[test]`.

### D. Must-Not-Regress List

The following currently-passing categories MUST remain green through Sprint 56. Any regression here blocks sprint close.

| Category | Scope | Why it matters |
|---|---|---|
| Ring 0 tests | All tests tagged `ring0` or in `tests/ring0.rs` | Core expression / type inference / function compilation. Ring 0 is complete; regression = structural fault. |
| Ring 1 tests | `ring1.rs`, `rc.rs` | ADTs, closures, strings, RC balance. Regression in RC is a data-corruption risk. |
| Ring 2 tests | `ring2.rs`, module tests | Traits, modules, constrained polymorphism. Step 2a's symbol-table-sourced collection directly touches trait-impl and mono codegen. |
| Ring 3 tests | `ring3*.rs`, macro tests | Macros, prelude. Not directly touched, but the REPL `__expr` path (§6) shares infrastructure. |
| `v4_pipeline` tests | All currently passing | Pipeline scheduling. Step 2b changes the worker's `Complete` branch — high risk surface. |
| `v4_repl_eval` tests | All currently passing | REPL eval convergence. The `__expr` special case deletion (§7 item 10) is the single most regression-prone change. |
| Platform tests that currently pass | Excluding the 5 known failures | Platform function resolution moves from `SessionCompilationEnv::collect_jit_setup_for_module` to backend-internal discovery (§3, §9.4). |
| `sprint23` tests that currently pass | Excluding the 3 cache/link known failures | Cache tests inherit `compile_to_module`'s signature via `ObjectCompilationEnv`. |
| `cache` tests that currently pass | Excluding the 9 known multi-module SIGSEGVs | Object-path cache reconstruction reads `ast` and `got_slot` — Wave 0 doesn't change these fields, but new cache-write paths may exercise mono/mangled entries differently. |
| Examples suite | All `examples/*.cl` under `--run` | Owned by `/examples`; validates the full user surface. |
| Stdlib compile-and-load | `tests/stdlib.rs` | Owned by `/stdlib`; first line-of-defence against trait/module regressions. |
| Exemplar | Sudoku solver under `exemplar/` | Owned by `/port`; multi-module program at scale. |

### E. Risk-Targeted Coverage (from `design/int/phase2-codegen-convergence.md` §9)

19. `risk_got_slot_allocated_before_codegen` [NEW]
    // spec: design/int/phase2-codegen-convergence.md §9.2 — no GOT slot allocation race
    Positive + debug_assert. After Wave 0, every entry yielded by `defined_symbols()` must have `got_slot: Some(_)` at codegen time. Add a `debug_assert!` in the inline codegen block (per §9.2 mitigation) asserting this invariant, and a companion test that exercises a module with multi-sig + mono + regular defns and confirms all GOT slots are populated before `compile_to_module` is called. **Scheduler prevents the two-worker-per-module race** (§9.1 confirms `ModulePool` serialises); no additional test needed for that race — the scheduler's own tests cover it. If the scheduler gap is found, flag back to `/int` via a new FIXME.

20. `risk_introspection_preserved_after_step2b` [NEW]
    // spec: design/int/phase2-codegen-convergence.md §9.3 + repl/spec.md §3.1 — introspection survives convergence
    Positive. REPL session. Define `(defn foo [:Int x] (add-i64 x 1))`. Invoke `/sig foo`, `/clif foo`, `/disasm foo`, `/source foo`. Assert each produces non-empty output with the expected classifier (e.g., `/sig` returns `(Fn [Int] Int)`, `/clif` contains `v0 = iadd_imm`, `/disasm` is non-empty, `/source` returns the source text). Guards §9.3 — the priority worker must populate `Introspection[fq]` keyed by `FQSymbol` from `CompilationResult::artifacts` in the new inline path.

21. `risk_introspection_mangled_names_hidden_from_list` [NEW, per §9.5]
    // spec: repl/spec.md §3.1 + §3.3 — /list does not surface mangled/mono names
    Negative. REPL: define multi-sig `(defn add ([:Int a :Int b] ...) ([:Float a :Float b] ...))`. Invoke `/list`. Assert output contains `add` ONCE, does NOT contain `add$Int+Int` or `add$Float+Float`. The mangled names are first-class in `defined_symbols()` but `/list`'s display layer must continue to filter them — Step 2b must not inadvertently surface them.

22. `risk_platform_function_resolution_via_unified_path` [NEW, from §9.4]
    // spec: design/int/phase2-codegen-convergence.md §9.4 + spec/12-runtime.md §12 (platform) — platform fns resolve through the unified path
    Positive. Batch compile a program that calls `(print "hello")` (platform.stdio/print via prelude). Assert exit code 0 and stdout `hello`. Exercises that after `SessionCompilationEnv::collect_jit_setup_for_module` is deleted (§7 item 8, 9), the backend's internal platform-fn resolution path carries the load. **This test depends on `/arch`'s arbitration of `/platform` Finding 3 (platform function discoverability)** — if `/arch` concludes the backend should not discover platform fns directly, this test's path changes. Flagged for Wave 2 coordination.

### F. Sprint 56 Delta Summary

| Bucket | Count | Notes |
|---|---|---|
| Wave 0 (new typecheck unit tests) | 6 | In-crate under `#[cfg(test)] mod tests`; `/typecheck` writes, `/qa` tracks |
| Step 2a (new backend/boundary tests) | 4 | `/qa` writes boundary tests; `/backend` owns unit variants |
| Step 2b (new integration tests) | 5 new + 3 flip-green + 1 meta = 9 | `/qa` writes; flip-green covers `sketch_multi_sig_*` |
| Risk-targeted (§9 coverage) | 4 | `/qa` writes |
| **Sprint 56 total planned** | **~23 new + 3 flip-green** | Baseline after sprint: 1593 passed / 19 failed / 0 ignored (target) |

## Sprint 57 — Phase 3+4 Convergence Tests

Derived from:
- `design/backend/compile-to-module.md` §9.1 (G6 code-write path), §9.2 (`CodegenProduct` elimination)
- `design/backend/ring2-rc.md` §3.5 (IO trampoline intermediate-node leak fix; `rc::dec_shallow_io`)
- `design/int/phase2-codegen-convergence.md` §13 (G6 extension — 10 reader-site migration, deletion list items 17–25)
- `design/int/platform-registry-removal.md` (G8 — `platform_fn_ptr` + `scheduling_class` on symbol table; Option B variant-internal)
- `design/int/persistent-workers.md` (G9 spawn/park/wake/shutdown, G10 per-worker JIT, G11 reload via scheduler)
- `design/typecheck/ast-annotation.md` §10 (G6 code/ast ownership boundary, `CheckResult` slim to `{ warnings, display }`)
- `design/platform/platform-registry-removal.md` (confirms Option B placement, `crates/cranelisp-platform/` unchanged)

Baseline at sprint start: 1602 passed / 14 failed / 0 ignored (Sprint 56 close). Target at Sprint 57 close: ≤9 failures (5 v4_platform flip green under G8, at least single-module cache failures flip under G6; cross-module cache may remain Phase-5 dependent).

### Baseline 14-failure composition (from SPRINT.md §Direct failure-fixing opportunities)

| Category | Count | Expected fix wave |
|----------|-------|-------------------|
| cache SIGSEGV / cross-module GOT | 9 | Wave 2 (G6) partial, Phase 5 for cross-module |
| sprint23 cache/link | 3 | Wave 2 (G6) + Phase 5 |
| v4 cache-hit dep (`v4_cache_hit_dependency`) | 1 | Wave 2 (G6) |
| v4_platform (5 — see §G.5 below) | 5 | Wave 3 (G8) |
| `sketch_run_tests_pass_fn_called` | 1 | Wave 2/3 triage — see §G.7 |

### G.0. Wave 0 — Super-import fix (`/frontend` + `/int`) — LANDED

Gate criterion: exemplar `(mod test (import [super [*]]) …)` resolves correctly; negative case (super at root) errors with spec-mandated message.

**Status**: Implementation landed in Sprint 57 Wave 0.
- `/arch` arbitrated frontend capture-time rewrite (Decision 30 in `design/arch/CLAUDE.md` — dependency flows toward stability: module identity is a frontend concern).
- `/frontend` implemented rewrite at `crates/cranelisp-frontend/src/module_extract.rs::parse_import_entries` — `super` in `ImportSpec` module path is replaced with the parent of `containing_module` via `rsplit_once('.')`. Root-module use returns `CranelispError::ModuleError`.
- `/int` updated the worker caller to thread the containing module path into `parse_import_sexp` (see `src/worker.rs:573`).
- `/spec` added the known-limitation warning on parent↔child mutual imports to `spec/08-modules.md §8.3.7` and fixed a duplicate §8.3.7 numbering bug — Null Import remains §8.3.6, Super Import is §8.3.7.

**Unit tests** (owned by `/frontend`, in `crates/cranelisp-frontend/src/module_extract.rs::tests` under `#[cfg(test)]`):
- `test_import_super_rewrites_to_parent` — `(import [super [*]])` inside `math.test` rewrites to `ImportSpec { module_path: "math", ... }`; no `"super"` literal survives.
- `test_import_super_rewrites_nested_parent` — nested child path strips only the last component; deeper parents are untouched.
- `test_import_super_at_root_errors` — `super` at a root module yields `CranelispError::ModuleError` whose message names `super` and explains the no-parent condition.

**Integration tests** (owned by `/qa`, in `tests/modules.rs`):
- `super_import_rewrites_to_parent_end_to_end` — full pipeline (reader → frontend → worker → scheduler → typecheck): parent `proj.cl` defines `parent-val`; child `proj/child.cl` uses `(import [super [*]])` to call it from its own `main`. Asserts (a) child compiles and runs returning 42 — proving super resolved; (b) post-compile, no `ModuleEntry::Import` on `proj.child` carries `source.module == "super"`, and at least one names the parent (`proj`) absolutely — proving the rewrite is invisible downstream.
- `super_import_at_root_is_rejected_neg` — top-level module `root.cl` with `(import [super [*]])` fails with the spec-mandated error. Substring-matches "super" and either "top-level" or "no parent".

**Coverage contract** (Decision 30 + §8.3.7 known-limitation warning):
- After frontend extraction, no `ImportSpec.module_path` contains the literal `"super"` — enforced by the 3 frontend unit tests and cross-checked by the integration test's symbol-table scan.
- Parent↔child mutual imports are documented in spec §8.3.7 as a known limitation (deadlock); integration test structure deliberately avoids the cycle by using the child as the entry module so the parent never imports or qualify-refs into the child.
- Exemplar modules (`grid/`, `solver/`, `html/`, `form/` with inline `(mod test ...)` + `(import [super [*]])`) serve as the Wave 6 real-world acceptance; `/port` runs them against the Phase 3+4 build.

Approximate counts: 3 unit (`/frontend`), 2 integration (`/qa`).

### G.1. Wave 2 — Phase 3 G6 (Code on SymbolTable)

**Unit** (`/backend`, in `crates/cranelisp-backend/src/` under `#[cfg(test)]`):
- `compile_to_module_writes_code_post_finalize` — build a `SymbolTable` with one zero-arg defn; call `compile_to_module` against a `JITModule`; assert the entry's `code: Some(Code { ptr, jit, .. })` after return, and `code: None` before. Spec: §9.1.3.
- `compile_to_module_object_mode_skips_code_write` — same setup but with `ObjectModule`; assert entry `code` is still `None` after return (object mode has no finalised-ptr to store). Spec: §9.1.6.
- `compile_to_module_preserves_shared_arc_jit` — compile two symbols in one call; assert both entries carry `Code` whose `jit: Arc<Jit>` compares `Arc::ptr_eq`. Spec: §9.1.2.
- `compile_to_module_pre_finalize_error_leaves_code_none` — force a CLIF verifier error on one defn (synthetic malformed AST); assert `Err(_)` returned, AND every entry in `names` has `code: None` (no partial write). Spec: §9.1.4.
- `compile_to_module_write_loop_skips_missing_entry_with_codegen_error` — populate `names` with one symbol that has no `ast`; assert `CranelispError::CodegenError` with message containing that symbol name; assert no write was attempted on other entries. Spec: §9.1.4 + §16.4.

**Unit** (`/int`, in `src/` under `#[cfg(test)]`):
- `priority_worker_reads_code_from_entry_not_codegen_product` — after G6, priority worker's `inline_jit_codegen_for_names` writes to symbol-table entry, not `CodegenProduct`. Assert via grep that `product.code.insert` is gone.
- `reload_module_clears_code_on_entry_walk` — `reload_module` walks `symbol_tables[module]` setting `code = None` on every `Def`. Spec: §13.3 R8.
- `test_runner_externs_resolve_via_symbol_table` — `discover_tests_extern` / `run_test_by_name` resolve fn pointers through `symbol_tables[module].get(name).code.ptr`, not `codegen_products`. Spec: §13.3 R6+R7.
- `lookup_main_code_via_symbol_table` — entry-module `main` is resolved via `symbol_tables[module].get("main").code`. Spec: §13.3 R5.
- `already_compiled_dedup_uses_code_is_some` — `derive_codegen_batch` dedup checks `code.is_some()` on the entry, not `codegen_products.contains_key`. Spec: §13.3 R10.
- `repl_expr_code_written_on_entry` — synthetic `__expr` entry carries `code: Some(_)` after eval. Spec: §13.6.

**Unit** (`/typecheck`, in `crates/cranelisp-typecheck/src/` under `#[cfg(test)]`):
- `check_result_slimmed_to_warnings_and_display` — `CheckResult` has exactly two public fields after the slim. Compile-level check: a test that destructures `{ warnings, display }` must succeed, and any attempt to read the five legacy fields must fail to compile. Spec: design/typecheck/ast-annotation.md §10.2 + §10.2.3.
- `typecheck_does_not_write_code_field` — a negative test via grep or structural assertion: no source line in `crates/cranelisp-typecheck/` reads or writes `code` on `ModuleEntry::Def`. Spec: §10.1 "No typecheck-owned read of `code`".
- `test_check_result_local_helper_in_backend_tests_only` — the backend crate's test scaffolding uses a locally-defined `TestCheckResult` helper; the public `CheckResult` export from `cranelisp-types` only shows `{ warnings, display }`. Spec: §10.2.4.

**Integration** (`/qa`, in `tests/wave2_g6.rs` — Sprint 57 Wave 2 step 5 landed):
- `g6_code_on_entry_after_compile` [LANDED tests/wave2_g6.rs] — define a trivial zero-arg fn; assert `ModuleEntry::Def.code.is_some()` post-compile. Direct observation of the G6 write path.
  // spec: design/backend/compile-to-module.md §9.1 + design/int/phase2-codegen-convergence.md §13.2
- `g6_clif_introspection_reads_from_symbol_table` [LANDED tests/wave2_g6.rs] — define a fn; assert the introspection map's `clif_ir` is non-empty and contains Cranelift syntax. Validates `/clif` reads via the migrated path (§13.3 R3).
- `g6_source_introspection_reads_from_symbol_table` [LANDED tests/wave2_g6.rs] — define a fn; assert the introspection entry carries source or sexp payload. Consolidated with `/disasm` coverage — same migrated read path.
- `g6_codegen_product_regression_guard` [LANDED tests/wave2_g6.rs] — structural scan of `src/**/*.rs` (ignoring comments) for forbidden `CodegenProduct` / `codegen_products` live references. Wave 2 close gate.
- `g6_cross_module_call_via_symbol_table` [LANDED tests/wave2_g6.rs] — two-module project, main imports util.helper; cross-module call succeeds through symbol-table-driven GOT resolution.
- `g6_repl_expr_uses_compile_to_module_path` [LANDED tests/wave2_g6.rs] — REPL `(add-i64 17 25)` evaluates to 42; `__expr` entry (if retained) carries `code: Some(_)`. Indirect verification that the compile_and_execute_expr `&Program` fallback is gone.
- `g6_check_result_slim_shape` [LANDED tests/wave2_g6.rs] — compile-time assertion that `CheckResult` destructures cleanly to `{ warnings, display }` only. If the 5 retired fields are reintroduced, the test fails to compile.
  // spec: design/typecheck/ast-annotation.md §10.2.3
- `g6_multi_sig_type_based_dispatch_regression_guard` [LANDED tests/wave2_g6.rs] — S56 flip-green preserved under Wave 2.
- `g6_multi_sig_different_arities_regression_guard` [LANDED tests/wave2_g6.rs] — S56 flip-green preserved under Wave 2.

**Dropped / deferred:**
- `v4_cache_hit_dep_flips_green` — NOT landed. `/int` reports `v4_cache_hit_dependency` did NOT flip under G6 (cross-module cache resolution requires Phase 5). Baseline failure (14) preserved; no spurious flip assertion introduced.
- `v4_cache_hit_then_clif_populates_code` — deferred; depends on cache-hit regeneration path which is Phase 5.
- `v4_repl_redefine_retires_old_code` — not included in this Wave 2 batch; redefinition retention semantics are a separate surface.
- `v4_main_trampoline_via_symbol_table` — exercised implicitly by `g6_cross_module_call_via_symbol_table` (main trampoline lookup resolves through `lookup_main_code_ptr` → symbol-table read per R5 of §13.3). A dedicated test would be a near-duplicate; consolidated.
- `/disasm` dedicated test consolidated into `g6_clif_introspection_reads_from_symbol_table` (same code path — introspection map population via worker post-compile).
- One of the three multi-sig S56 flip-greens (`sketch_repl_multi_sig_different_arities`) is functionally equivalent to `g6_multi_sig_different_arities_regression_guard` and covered by the existing `sketch_port.rs` test. Two dedicated guards cover the distinct dispatch patterns (type-based vs arity-based).

Approximate counts: 5 unit (`/backend`) + 6 unit (`/int`) + 3 unit (`/typecheck`) = **14 unit**; **9 integration** landed (target was 11; consolidated per note above — quality over count per plan guidance).

### G.2. Wave 3 — Phase 4 G8 (Platform on SymbolTable) — LANDED

Gate criterion: 5 `v4_platform_*` flip-green targets all pass; `v4_platform_empty_registry` regression guard stays green; `PlatformRegistry` struct deleted from `src/`; IO-trampoline RC balance holds end-to-end (`/arch` Condition 6).

**Status**: Implementation landed in Sprint 57 Wave 3.
- `/int` step A: added `platform_fn_ptr: Option<*const u8>` on `ModuleEntry::Def` (Decision 26); `PrimitiveKind::PlatformEffect { scheduling_class: SchedulingClass }` (Option B); moved `SchedulingClass` into `cranelisp-types` (re-exported by `cranelisp-platform`).
- `/int` step B: deleted `src/platform_registry.rs` and `CompilerSession.platform_registry`; migrated 5 readers (`collect_jit_setup`, `bind_chain_analysis::classify_expr`, etc.) to symbol-table lookup; added `SharedState::kept_dlls` retention pool.
- `/backend`: IO-trampoline RC fix via `crate::drop::dec_shallow_io` (Decision 29); `call_continuation` closure-consume fix; 6 new unit tests in `crates/cranelisp-runtime/src/io.rs::tests` and `drop.rs::tests`.

**Unit** (`/int`, in `src/worker.rs::tests` and `src/bind_chain_analysis.rs::tests`) — landed:
- `collect_jit_setup_finds_platform_fn_via_entry` — Spec: design/int/platform-registry-removal.md §9.1.
- `collect_jit_setup_follows_import_chain` — Spec: §9.1.
- `classify_expr_reads_scheduling_class_from_variant` (a.k.a. `bind_chain_analysis_reads_scheduling_class_from_entry`) — Spec: §3.1 + §3.2.
- `handle_platform_writes_both_type_info_and_fn_ptr` — Spec: §4.1 + §4.3 invariant.
- `platform_registry_struct_does_not_exist` — compile-time regression guard. Spec: §10 Deletion List item 1.

**Unit** (`/backend` / `/runtime`, in `crates/cranelisp-runtime/src/io.rs::tests` and `crates/cranelisp-runtime/src/drop.rs::tests`) — landed:
- `dec_shallow_io_single_pure_balanced` — Spec: design/backend/ring2-rc.md §3.5.4 option (a).
- `dec_shallow_io_bind_does_not_double_dec_inner` — Spec: §3.5.4.
- `run_io_trampoline_rc_balanced` — 4-alloc/4-dealloc two-step chain; Spec: §3.5.7.
- `run_io_trampoline_deep_bind_chain_rc_balanced` — 100-deep Pure chain, balanced; was the O(N) leak shape. Spec: §3.5.7.
- `call_continuation_dec_closure` — closure consumed on fresh-tree branch, left alone on caller-tree branch. Spec: §3.5.4.

**Integration** (`/qa`, in `tests/wave3_g8.rs`) — landed:
- `g8_platform_fn_ptr_on_entry_after_form_handled` [LANDED tests/wave3_g8.rs] — test-capture DLL loaded; `ModuleEntry::Def.platform_fn_ptr` is `Some(_)` + `PlatformEffect` + `jit_name` invariant. Spec: design/int/platform-registry-removal.md §4.1 + Decision 26.
- `g8_scheduling_class_read_via_symbol_table` [LANDED tests/wave3_g8.rs] — synthetic symbol-table world: `bind_chain_analysis::scheduling_of` reads class via qualified + bare + Import-chain lookups; missing names fall back to Sequential. Option B placement validated. Spec: design/int/platform-registry-removal.md §3 + bind-chain-analysis.md.
- `g8_platform_registry_regression_guard` [LANDED tests/wave3_g8.rs] — structural grep over `src/**/*.rs`: no live references to `PlatformRegistry` / `platform_registry` (comments allowed). Wave 3 close gate. Spec: §2.4 + §10 Deletion List.
- `g8_cross_module_platform_fn_resolution` [LANDED tests/wave3_g8.rs] — user imports `print` from `platform.test-capture`; call walks Import chain to the defining entry; output captured end-to-end. Spec: §5.2.
- `g8_kept_dlls_retains_handles` [LANDED tests/wave3_g8.rs] — `SharedState.kept_dlls` contains the `test-capture` `LoadedPlatform` handle post-registration; DLL lifetime invariant holds. Spec: `src/session_v4.rs` `kept_dlls` doc-comment + design/int/platform-registry-removal.md §4.
- `g8_io_trampoline_rc_balanced` [LANDED tests/wave3_g8.rs] — **`/arch` Condition 6 gate**: 2-step `Pure`/`bind` chain through `cranelisp_run_io` — alloc/dealloc + bytes_current balanced. Spec: design/backend/ring2-rc.md §3.5 + Condition 6.
- `g8_scheduling_class_moved_to_types_regression_guard` [LANDED tests/wave3_g8.rs] — compile-time assertion that `cranelisp_types::SchedulingClass` and `cranelisp_platform::SchedulingClass` resolve to the same type. Spec: design/int/platform-registry-removal.md §3 + Decision 26.
- `g8_platform_effect_variant_carries_scheduling_class` [LANDED tests/wave3_g8.rs] — construct `PrimitiveKind::PlatformEffect { scheduling_class }` for each class; destructure and verify. Spec: Option B recommendation §3.1.
- `g8_rc_balance_bind_chain` [LANDED tests/wave3_g8.rs] — 4-step `Pure`/`bind` chain (`v4_platform_rc_balance_bind_chain` coverage without platform dependency — the fresh-Pure release code-path is identical). Spec: §3.5.7.

**Flip-green outcomes** (5 v4_platform tests pinned in §G.5 all landed green):
- `v4_platform_form` [LANDED tests/v4_pipeline.rs:560] — pass.
- `v4_platform_stdio_print` [LANDED tests/v4_pipeline.rs:751] — pass.
- `v4_platform_io_trampoline` [LANDED tests/v4_pipeline.rs:773] — pass.
- `v4_platform_import_and_use` [LANDED tests/v4_pipeline.rs:797] — pass.
- `v4_platform_multiple_calls` [LANDED tests/v4_pipeline.rs:835] — pass.
- `v4_platform_empty_registry` [LANDED tests/v4_pipeline.rs:819] — regression guard, stays green (not expected to flip — not in baseline failure set per §G.5).

**Deferred from Wave 3 scope**:
- `v4_platform_rc_balance_par_branches` — deferred; `par-bind!`/Par-branch coverage re-scoped as integration tests behind a DLL dependency. See §G.8 RC-balance adoption survey (Wave 5).
- `v4_platform_scheduling_class_commutative_parallelizes` / `_sequential_serializes` — deferred; wall-clock timing tests require workload control outside Wave 3 scope. Option B placement validated via `g8_platform_effect_variant_carries_scheduling_class` and `g8_scheduling_class_read_via_symbol_table` — the runtime parallelization behaviour is validated at integration via existing `scheduler.rs` tests and will gain dedicated tests alongside the Phase 4 G9 work.
- `v4_platform_cache_hit_platform_ptr_rewrite` — deferred to Phase 5 per /int §8 position (option a). Cache-restore platform rehydrate is out of G8 scope.

Baseline post-Wave-3: **1617 passed / 14 failed / 0 skipped** (composition per `/backend` end-of-wave report): 9 cache, 1 sketch_port, 3 sprint23, 1 v4_pipeline (`v4_cache_hit_dependency` — Phase-5-dependent cross-module cache).

Approximate counts: 5 unit (`/int`) + 5 unit (`/backend`/`/runtime`) = **10 unit**; **9 integration** (`/qa`).

### G.3. Wave 4 — Phase 4 G9 (Persistent Workers)

**Unit** (`/int`, in `src/session_v4.rs::tests` and `src/worker.rs::tests`):
- `persistent_worker_spawn_at_session_init` — `CompilerSession::new(settings)` spawns `settings.priority_workers` threads; assert `priority_worker_handles.len() == N`. Spec: design/int/persistent-workers.md §4.1.
- `persistent_worker_park_on_no_work` — spawn N workers; enqueue zero work; after 100ms of sleep, assert no CPU spin (workers parked on condvar). Instrumentation: per-worker atomic counter incremented inside loop body; assert counter stays at 0. Spec: §4.2.
- `persistent_worker_wake_on_work_submitted` — spawn N workers (all parked); enqueue one PriorityWork item via `scheduler.register_module`; assert exactly one worker wakes and processes it within 100ms, then parks again. Spec: §4.2.
- `persistent_worker_drain_on_shutdown` — spawn N workers; enqueue M > N work items; call `shutdown()`; assert all M items processed AND all N workers joined within 1 second bounded time. Spec: §5.2.
- `concurrent_register_module_no_lost_updates` — spawn N workers; from test thread, concurrently call `register_module` for K > N modules (using `std::thread::spawn` + barrier); assert all K modules reach `Complete` and their defn code is present. Spec: §9.1.
- `shutdown_race_mid_codegen_bounded_wait` — enqueue one work item that sleeps 200ms; call `shutdown()` mid-sleep; assert workers join after the work completes; bounded wait < 500ms. Spec: §5.2 + §8.2.
- `worker_count_bound_respected` — `CompilerSession::new` with `priority_workers: 16` clamps to 8; with `priority_workers: 0` clamps to 1. Spec: §5.1.
- `per_worker_jit_reused_across_work_items` — within one worker, compile two separate defns sequentially; assert the worker's thread-local `Jit` handle is the same `Arc::ptr_eq` across both compiles (JIT rotation not yet active). Spec: §4.5.
- `eval_submits_through_scheduler_not_inline` — REPL `eval` does NOT create a new `thread::scope`; it calls `scheduler.register_module_additive` + `scheduler.wait_module_complete`. Spec: §4.4.
- `reload_enqueues_not_spawn` — `reload_module` does NOT create a new `thread::scope`. Regression: grep on `src/session_v4.rs` outside `#[cfg(test)]` returns zero `thread::scope` hits. Spec: §4.6.
- `module_sexps_and_suspend_states_on_shared_state` — after G9, `SharedState` carries `module_sexps: Mutex<…>` and `suspend_states: Mutex<…>`; per-call locals are gone. Spec: §5.3.

**Integration** (`/qa`, in `tests/v4_persistent_workers/`):
- `v4_concurrent_modules_compile` — register 10 modules simultaneously via spawned threads (or via `/int`'s test harness that triggers concurrent registration); assert all 10 compile cleanly; no SIGSEGV or hang.
- `v4_reload_during_compile` — start a large-module compile (synthetic 100-defn module); from another thread, trigger file-watcher `reload_module` on a different module mid-compile; assert both complete without wedging. Regression guard for §8.4 deadlock risk.
- `v4_repl_eval_latency_no_regression` — REPL eval 100 trivial `(+ 1 2)` expressions in sequence; assert each completes in < 100ms median. Regression guard for §8.3.
- `v4_repl_eval_routes_through_persistent_worker` — REPL eval uses the persistent worker's per-worker JIT; instrumentation assertion: after 10 evals, `#[cfg(test)] priority_worker_eval_count` atomic > 0. Spec: §4.5.
- `v4_thread_scope_absent_for_workers` — structural grep: `grep -rn 'thread::scope' src/ --include='*.rs'` returns zero hits outside `#[cfg(test)]`. Wave 4 close gate.
- `v4_session_drop_joins_workers` — drop a `CompilerSession` while workers are mid-compile; assert process doesn't leak threads; assert Drop bounded wait < 1 second. Spec: §5.2.
- `v4_shutdown_race_no_deadlock` — stress: 100 iterations of (spawn session → submit 10 modules → shutdown mid-compile); assert zero hangs, zero panics. Spec: §5.2.
- `v4_persistent_worker_exemplar_parallel_compile` — exemplar Sudoku solver (`grid/`, `solver/`, `html/`, `form/` modules) compiles under persistent workers; correctness parity with pre-G9 state.

Approximate counts: 11 unit (`/int`); **8 integration** (`/qa`).

### G.4. Wave 5 — Prior-ring coverage gaps (`/qa` parallel work)

Resolves the 14 FIXME(/qa) entries listed in SPRINT.md §FIXME Debt and §Prior-ring coverage gaps (/qa):
- `spec/index.md` (×1) — traceability gap.
- `spec/12-runtime.md` (×1) — coverage gap.
- `spec/08-modules.md` (×1) — traceability gap.
- `spec/05-definitions.md` (×2) — traceability §5.4.2 / §5.4.3 (ADT impls).
- `spec/03-types.md` (×1) — traceability §3.7 (HKT).
- `repl/spec.md` (×6, excluding /mem) — coverage gaps §4.1 / §7.4 + traceability.
- `spec/appendix-a-builtins.md` (×3) — coverage + traceability for `vec-map`, `vec-reduce`, builtin shadowing.
- `tests/plan/ring4.md` — Ring 4 RC-balance assertion adoption survey (the original line-8 FIXME; results land in Wave 5 addendum below).

Approach per gap: enumerate FIXME → decide add-test vs. fix-annotation → if add-test, write to the correct integration file and update spec annotation to `[Tested tests/file::test_name]` (or `[Tested+Neg …]`). If fix-annotation, confirm test exists, update spec label.

### G.5. v4_platform Five-Failure Identification

Per SPRINT.md §Direct failure-fixing opportunities, 5 of the 6 `v4_platform_*` tests in `tests/v4_pipeline.rs` are in the Sprint 56 baseline-failure set. The enumeration of all 6 test names with file location:

| Test | File:line | `/platform`'s hypothesis (design/platform/platform-registry-removal.md §... / §G8) |
|------|-----------|-------------------------------------------------------------------------------------|
| `v4_platform_form` | tests/v4_pipeline.rs:560 | In baseline set — flips green under G8 (A-1 equivalent). |
| `v4_platform_stdio_print` | tests/v4_pipeline.rs:751 | In baseline set — flips green under G8 (A-1). |
| `v4_platform_io_trampoline` | tests/v4_pipeline.rs:773 | In baseline set — flips green under G8 + §3.5 RC fix (A-2). |
| `v4_platform_import_and_use` | tests/v4_pipeline.rs:797 | In baseline set — flips green under G8 (A-3). |
| `v4_platform_empty_registry` | tests/v4_pipeline.rs:819 | **NOT in baseline set** per hypothesis (A-4) — non-platform-semantic test. No `(platform ...)` form; failure cause would be different. |
| `v4_platform_multiple_calls` | tests/v4_pipeline.rs:835 | In baseline set — flips green under G8 (A-5). |

**`/qa` position**: the 5 baseline failures are `v4_platform_form`, `v4_platform_stdio_print`, `v4_platform_io_trampoline`, `v4_platform_import_and_use`, `v4_platform_multiple_calls`. `v4_platform_empty_registry` is NOT in the baseline (it does not exercise platform semantics). This aligns with `/platform`'s dominant hypothesis. Wave 3 acceptance: all 5 enumerated tests flip green AND `v4_platform_empty_registry` remains passing (it was passing in S56 and must not regress).

If Wave 3 implementation reveals a different 5 (e.g., `v4_platform_empty_registry` turns out to be in the failing set), `/qa` re-runs the baseline test set with Sprint 56 HEAD to pin the exact identity and files a FIXME(/int) naming the residual test and likely non-G8 root cause.

### G.6. Wave 6 — Showcase (sprint close gate)

Depends on Waves 2, 3, 4. Owned by `/repl`, `/port`, `/stdlib`, `/examples`, `/docs`, `/qa` close-time audit.

- `wave6_exemplar_sudoku_end_to_end` — Sudoku solver runs post-super-import-fix; all modules compile; correctness parity. Owned by `/port`.
- `wave6_mem_slash_command_spec_compliant` — `/mem` reports live alloc count / dealloc count / bytes_current. Owned by `/repl` spec + `/int` implementation.
- `wave6_ring4o_demo_plays` — `repl/demos/ring4o.demo` plays cleanly through the REPL harness.
- `wave6_prior_demos_regression_free` — all demos in `repl/demos/` replay green; regression gate.
- `wave6_examples_all_run` — 15/15 `examples/*.cl` under `--run` succeed.
- `wave6_stdlib_tests_pass` — 54/54 stdlib tests pass.
- `wave6_cargo_clippy_all_targets_clean` — global clippy gate.
- `wave6_cargo_nextest_full_green_minus_phase5` — full suite passes except legitimate Phase-5-dependent cache failures (tracked in Notes).

**Wave 6 /qa additions (Sprint 57 close)**:

- `tests/io.rs::io_do_print_sequence_with_pure_terminator_emits_all` — NEW failing test. Exact `repl/demos/ring4b.demo` + `ring4j.demo` pattern: `(do (print "one") (print "two") (Pure 42))`. Asserts both prints emit in order AND trampoline returns Pure(42). Currently **ABORT SIG 10** (SIGBUS) — reproduces the mid-execution crash `/repl` observed. Covers spec §10.4.1 + §10.4.2 (intermediate effects + last-expr type/value).
- `tests/io.rs::io_bind_bang_print_sequence_with_pure_terminator_emits_all` — NEW failing test. `bind!` analog: `(bind! [_ (print "one") _ (print "two")] (Pure 42))`. Currently **ABORT SIG 10** (SIGBUS). Covers spec §10.5.1 + §10.5.2.

Per `memory/feedback_failing_not_ignored.md` both tests are committed **failing, un-ignored** — they expose a real bind-chain-with-Pure-terminator regression in the Sprint 57 Wave-3 IO trampoline rework. Close-gate disposition pending `/int` + `/backend` investigation: carry to Sprint 58 if the regression proves non-trivial, or fix inside Wave 6 if /int bandwidth permits.

**Wave 6 /qa FIXMEs filed**:

- `FIXME(/qa) repl/spec.md §3.7` (4 rows) — `/mem` integration tests not yet written. Unit tests for `format_mem_snapshot` / `parse_slash_command("/mem")` live in `src/session_v4.rs` (`/int`-owned). Integration coverage through `run_repl` (E2E stdout assertions on `; live:` / `; allocs:` / `; delta:` lines) remains a gap — carry to Sprint 58.
- `FIXME(/qa) design/arch/pipeline-v4-roadmap.md` Decision 31 reclaim — Scenario 1 (REPL-eval fresh JIT drop) has no dedicated integration test (positive: `/mem` showing live-bytes decrease after eval; negative: bytes do NOT grow unbounded under repeated eval). Carry to Sprint 58 alongside `/mem` tests.

**Wave 6 full-suite regression finding (Sprint 57 close)**:

Full `cargo nextest run --max-fail=1000` across the workspace at Wave 6 start:

```
Summary [10.8s] 1688 tests run: 1644 passed, 44 failed, 0 skipped
```

Expected baseline was ~17 failing (14 Sprint 56 baseline + 2 Wave 5 /int gaps carried to S58 + 1 sprint23 documentation drift). **Observed: 44 failures — 27 excess vs. expected.** Categorization:

| Category | Count | Notes |
|---|---:|---|
| cache multi-module SIGSEGV + FAIL (Phase-5-dependent) | 10 | Pre-existing. Phase-5 cache work. |
| sprint23 cache/link FAIL | 4 | Pre-existing. Phase-5 cache work. |
| io.rs bind/do/then/triple SIGBUS (ABORT SIG 10) | 21 | **NEW regressions**: `io_bind_*` (10), `io_do_*` (3 incl. 2 new), `io_then_*` (4), `io_triple_bind_chain`, `io_values_are_deferred_data`, `io_repl_eval_bind_result`, `io_bind_print_sequence`, `io_read_line_bind_print_echo`. All SIGBUS after Wave-3 IO trampoline rework. |
| stdlib `macro_do_*` SIGBUS | 2 | NEW regression tracking same IO trampoline path. |
| sketch_port `sketch_platform_capture_read_input` SIGBUS | 1 | NEW regression tracking same IO trampoline path. |
| sketch_port `sketch_run_tests_pass_fn_called` FAIL | 1 | Pre-existing baseline failure; Wave-6 still unresolved. |
| repl_experience `display_overloaded_fn_shows_all_variants` FAIL | 1 | Wave-5 carried-to-S58 multi-sig display gap. |
| ring2 `neg_private_submodule_not_importable_from_peer` FAIL | 1 | Wave-5 carried-to-S58 private-submodule import gap. |
| v4_pipeline `v4_cache_hit_dependency` FAIL | 1 | Pre-existing Phase-5-dependent. |
| v4_repl_eval `v4_repl_discover_and_run_test_via_bind` FAIL | 1 | Same IO-trampoline-regression category as io.rs above. |
| cache_multi_module_transitive_imports FAIL | 1 | Pre-existing Phase-5 cache. |

**Blocker to sprint close**: the 24-25 SIGBUS / FAIL cluster in the IO trampoline / bind / do / then path (all io.rs, stdlib macro_do_*, v4_repl_discover_and_run_test_via_bind, sketch_platform_capture_read_input) is a **Sprint 57 regression** that did not exist at Sprint 56 close. Root cause hypothesis: the Wave-3 IO trampoline rework (`crates/cranelisp-runtime/src/io.rs` `run_io_trampoline` RC fix, /backend) combined with Wave-4 Decision 31 custom `Drop` on `Jit` (`crates/cranelisp-backend/src/jit.rs`). Both touch IO-result heap lifetime. FIXME(/backend) filed below.

**Wave 6 close status (Sprint 57 Wave 6)**: `/int` landed `unwrap_io_inline` in `src/pipeline.rs::compile_and_execute_expr` — trampolines IO before the per-eval `Jit` drops, replacing the old "return raw IO ptr; trampoline later" contract that the Sprint 57 Wave 4 custom-Drop made unsafe. `/qa` migrated all test sites in `tests/io.rs` (~70), `tests/io_minimal.rs` (5), `tests/wave3_g8.rs` (G8-4 + G8-6 + G8-9), `tests/stdlib.rs` (2 `macro_do_*`), and `tests/ring4_trace.rs` (`run_tests_discover_tests_form_type` + `run_tests_run_test_form_type`) to the new contract: `compile_and_run_typed` / `repl_eval_typed` now return the fully-reduced inner value and the unwrapped type — no manual `run_io_trampoline` call is required, and the raw IO pointer never escapes eval. Full-suite state at Wave 6 close: **1695 tests run: 1676 passed, 19 failed, 11.4s**. The 24-25 SIGBUS cluster has resolved; the remaining 19 failures split as: 14 pre-existing (9 cache SIGSEGVs, 4 sprint23 cache, 1 v4_cache_hit_dependency, 1 sketch_run_tests_pass_fn_called `can't resolve symbol run-test`), 2 Wave-5 carries (`display_overloaded_fn_shows_all_variants`, `neg_private_submodule_not_importable_from_peer`), and **2 new Condition 6 regressions** (`g8_io_trampoline_rc_balanced`, `g8_rc_balance_bind_chain`). The 2 new failures expose that `src/pipeline.rs::unwrap_io_inline` calls the *non-consuming* `cranelisp_runtime::run_io_trampoline` where Decision 24 requires the *consuming* `cranelisp_run_io` (or an equivalent `consume_io_tree` call) — the caller IO tree is trampolined but never released. Evidence: `g8_io_trampoline_rc_balanced` shows `7 allocs vs 4 deallocs` (3 unreleased caller-tree nodes) and `g8_rc_balance_bind_chain` shows `13 vs 10` (matching deeper chain). FIXME(/int) + FIXME(/backend) to land `consume_io_tree` in `unwrap_io_inline` (or switch the inline-trampoline call to `cranelisp_run_io`) in Sprint 58 — mirroring the existing `CompilerSession::trampoline` release path at `src/session_v4.rs:2800` and `format_eval_result` at `src/session_v4.rs:3118` which have the same gap.

### G.7. `sketch_run_tests_pass_fn_called` Triage

**Test location**: `tests/sketch_port.rs:1603`. **Baseline status**: failing in Sprint 56 close (1 of 14 failures).

**What the test does**: composes the in-language `discover-tests` and `run-test` primitives (confirmed registered in `crates/cranelisp-typecheck/src/builtins.rs:1066–1115`) into a user-defined `(defn my-run-tests [] (bind (discover-tests "") (fn [names] (count-passes 0 names))))`. The helper `count-passes` pattern-matches on the SList-of-Sexp returned by `discover-tests`, and for each Sexp calls `(run-test head)`, pattern-matches on the returned `TestResult` (`TestPass` / `TestFail`), and folds a counter. Asserts the display output contains `"1"` (one passing test).

**Primitives confirmed in the language**:
- `discover-tests : (Fn [String] (IO (SList Sexp)))` — `builtins.rs:1066`.
- `run-test : (Fn [Sexp] (IO TestResult))` — `builtins.rs:1091`.
- `TestResult` with `TestPass { name: String, nanos: Int }` and `TestFail { name: String, nanos: Int, reason: String }` constructors — `builtins.rs:1010–1045`.
- Extern implementations: `discover_tests_extern` at `src/session_v4.rs:3693`, `run_test_by_name` at `src/session_v4.rs:3572`.

**`/qa` triage call**: **IMPLEMENTATION DEFECT — route to `/int`** (with possible secondary `/backend` involvement).

**Rationale (one paragraph)**: All language-level primitives exist with correct types and ADT shape; the test composes them exactly as spec §4.11 envisions — `bind`, `match` on `TestResult`, IO trampoline forcing via `repl_eval_display`. The test-authoring is sound: it checks that a user program can weave the two builtins into a private test runner, which is exactly the composition the prelude / stdlib may eventually package as `run-tests`. The most likely failure site is in the integration layer — specifically, the `TestRunnerState` pointer plumbing between `discover_tests_extern` (which needs access to the session's symbol tables and current module) and `run_test_by_name` (which needs to resolve FQSymbol → code pointer). Under Sprint 57 G6 (§13.3 R6+R7), both externs migrate to reading `symbol_tables[module].get(name).code.ptr` instead of `codegen_products[module].code[name].ptr`, and `TestRunnerState` changes field type (R7). This is the reasonable hypothesis: the test's failure mode is likely *"pointer indirection currently broken in the eval-module REPL path"* and G6 fixes it for free. Alternate hypothesis — the IO trampoline on `(bind (run-test head) (fn [result] (match result ...)))` leaks or corrupts the `TestResult` ADT in the intermediate Pure/Effect node, which G8's §3.5 RC fix would address. Less likely: a test-authoring issue (e.g. `count-passes` recursion pattern). Close this failure **inside Sprint 57**: Wave 2 (G6) runs first and is expected to resolve it; if it doesn't, Wave 3 (G8 + RC fix) is the second candidate. If still failing after Wave 3, file FIXME(/int) with the concrete failure mode and re-triage in Wave 6 close.

**Action**: do NOT edit or delete the test. Run it after each wave; flip-green verification is part of sprint acceptance.

### G.8. Ring 4 RC-Balance Assertion Adoption Survey

(Resolves the line-9 FIXME(/qa) filed Sprint 56 close. Completed Sprint 57 Wave 5.)

**Infrastructure in place** (`tests/helpers/mod.rs:579`):
- `assert_rc_balanced(src)` — full pipeline eval + `(main)` invocation if defined.
- `assert_rc_balanced_with(preamble, src)` — same with explicit preamble (e.g. `PLATFORM_PREAMBLE`).

Semantic: snapshots `cranelisp_runtime::alloc_count()` / `dealloc_count()` / `bytes_current()` before the eval, evaluates, re-snapshots, asserts `new_allocs == new_deallocs` and zero bytes growth. Works for any source that compiles to one or more defs plus an optional `(defn main [] ...)` that then gets invoked.

**Observed use-counts (Sprint 57 close)**:

| File | Tests | `assert_rc_balanced*` call sites | Adoption level |
|------|------:|---------------------------------:|----------------|
| `tests/rc.rs`             | 81 |     38 | Heavy (primary RC test file) |
| `tests/sketch_port.rs`    | —  |      9 | Spot-use in RC-sensitive ported cases |
| `tests/io.rs`             | 74 |      2 (both as **"cannot use" notes** — IO trampoline leak, see io.rs:1134 / 1185) | Near-zero (blocked on io.rs leak) |
| `tests/wave3_g8.rs`       |  9 |      1 (condition-6 gate `g8_io_trampoline_rc_balanced`) | Gated |
| `tests/ring4_trace.rs`    | 31 |      0 | None |
| `tests/scheduler.rs`      | 18 |      0 | None |
| `tests/lenient.rs`        | 16 |      0 | None |
| `tests/v4_pipeline.rs`    | 47 |      0 | None (platform tests; Sprint 57 Wave 3 added condition-6 gate in `wave3_g8.rs` instead of in-place wrapping) |
| `tests/cache.rs`, `modules.rs`, `stdlib.rs`, `examples.rs`, `exemplar.rs` | — | 0 | None; RC is not the surface under test |
| Sprint 56 Wave 2c — unit tests inside `crates/cranelisp-runtime/` | 14 | 14 (extern-boundary `decision24_*` family) | Complementary lower-layer coverage |

**Ring 4 test classes surveyed** (from this file's existing sections):

| Class | Current assertion style | RC-balance adoption priority | Disposition |
|-------|-------------------------|------------------------------|-------------|
| IO / do / pure / bind (`tests/io.rs`) | Value-equality only; 2 "cannot use" notes | **HIGH — BLOCKED** | Blocked on `crates/cranelisp-runtime/src/io.rs` IO-trampoline intermediate Pure/Effect node leak. Adoption requires an IO-aware helper (see Extension requests below). Wave 3's `rc::dec_shallow_io` groundwork is in place; after io.rs is leak-clean the two "cannot use" notes become normal `assert_rc_balanced_with` calls. |
| bind! sugar | Value-equality only | **HIGH — BLOCKED** | Same root cause as above; bind! desugars to `apply` + closure, and the closure-env lifecycle flows through the trampoline. |
| Platform (capture DLL) | `capture.get_output().contains(...)` | **HIGH** | Adopted via `wave3_g8.rs::g8_io_trampoline_rc_balanced` (Condition 6 gate). In-place wrapping of the other `v4_platform_*` tests in `tests/v4_pipeline.rs` MAY adopt but is not mandatory given the single end-to-end gate. |
| Trace (`tests/ring4_trace.rs`) | Call-tree structural | **MEDIUM** | Currently 0 sites. Trace nodes are heap-allocated; trace scope cleanup was a historical bug class. Adoption recommended for the 8-10 tests that construct observable `Trace` ADT values. Non-blocking — test authoring has passed review without balance assertions. |
| Run-tests composition (`tests/sketch_port.rs::sketch_run_tests_pass_fn_called`) | Display substring | **HIGH** | Test remains failing post-Wave-4 (see §G.7). Before un-ignoring, wrap with `assert_rc_balanced_with` so that when it flips green we also verify no leak across the `discover-tests`/`run-test` primitive pair. |
| par-let / par-bind! | Value-equality + timing | **HIGH** | Currently 0 sites; `v4_platform_rc_balance_par_branches` deferred from Wave 3 to Phase 5 per §Known-issues. Once landed, adoption is mandatory. |
| Lenient evaluation (`tests/lenient.rs`) | Value-equality + timing | **MEDIUM** | 0 sites today. IVar lifecycle is the risk surface. MAY adopt as a regression guard. |
| Cache (`tests/cache.rs`) | Exit code / stdout | **LOW** | Cache read/write doesn't exercise heap in the code under test. MUST NOT adopt — false-positive cost. |
| Checked arithmetic | Value-equality / panic | **LOW** | No heap. MUST NOT adopt. |
| REPL slash commands (`tests/repl_experience.rs`, `tests/ring3_repl.rs`) | Text output substring | **LOW–MEDIUM** | `/info` / `/clif` / `/disasm` build heap strings for display. If adopted, wrap only the eval step, not the display step (display format strings are per-invocation temporaries). |

**Adoption summary (counts)**:
- **Currently adopted**: 50 call sites across 4 files (`rc.rs` 38, `sketch_port.rs` 9, `wave3_g8.rs` 1, `io.rs` 2-as-note). Ring 4-specific count (excluding `rc.rs`): ~12.
- **Could adopt (SHOULD)**: ~30 additional sites spread across `ring4_trace.rs` (heap-ADT assertions), `v4_pipeline.rs` (platform tests beyond the single Condition-6 gate), `sketch_port.rs::sketch_run_tests_pass_fn_called` once un-ignored, `repl_experience.rs` `/info` / `/clif` / `/disasm` eval steps.
- **Blocked (would require infrastructure)**: ~20 sites in `tests/io.rs` — blocked on io.rs trampoline leak cleanup (Wave 3 introduced `rc::dec_shallow_io`; full adoption waits on the remaining intermediate-node shallow-dec audit).
- **Shouldn't adopt (NOT RECOMMENDED)**: `cache.rs`, `modules.rs`, `stdlib.rs`, `examples.rs`, `exemplar.rs`, `scheduler.rs`, `lenient.rs`, `macros.rs`, most of `ring0.rs`/`ring1.rs`/`ring2.rs`/`ring3_repl.rs` (primitive-value or non-heap tests) — false-positive cost without coverage gain.

**Adoption policy (to be documented in `tests/CLAUDE.md` post-Wave 5)**:
- **MUST adopt** — tests whose observable surface includes heap-typed values (String, ADT, closure, Vec, List, Seq, Trace) and which directly exercise IO trampoline, platform calls, par-let/par-bind!, or `discover-tests`/`run-test` primitives.
- **MAY adopt** — other Ring 4 integration tests that incidentally construct heap values; adoption is a regression guard, not a required gate.
- **MUST NOT adopt** — synchronous arithmetic / primitive-only tests that use no heap (false-positive cost without coverage gain).

**Extension requests** (tracked here; `/qa` owns tests/helpers/mod.rs so no cross-skill FIXME needed):
- `assert_rc_balanced_eval(&mut session, src)` — per-eval wrapper for REPL-session tests doing incremental eval (separate from batch). Would unblock the `repl_experience.rs` `/info` / `/clif` / `/disasm` cases where we want to wrap a single eval inside a larger session without re-creating the session.
- Snapshot-guard RAII struct — `let _guard = RcBalanceGuard::new();` at the top of a test, assert-on-drop. Complementary to `assert_rc_balanced_eval`; lighter for tests that drive many operations.
- IO-aware variant `assert_rc_balanced_io(src)` — expects the IO trampoline to consume `Pure`/`Bind` intermediate nodes; filters out the known-leak bytes while io.rs cleanup lands. Wraps the existing helper with Wave-3's `rc::dec_shallow_io` accounting. Blocks adoption in `tests/io.rs`.

### G.9. Sprint 57 Delta Summary

| Bucket | Unit (owning skill) | Integration (`/qa`) | Notes |
|---|---|---|---|
| Wave 0 (super-import) | 3 | 5 | Owner for unit tests determined by `/arch` Wave 0 arbitration. |
| Wave 2 (G6 code-on-entry + CheckResult slim) | 14 (5 backend + 6 int + 3 typecheck) | 11 | `/qa` writes integration in `tests/v4_codegen/` + `tests/v4_repl_eval/`. |
| Wave 3 (G8 platform + IO RC fix) — **LANDED** | 10 (5 int + 5 backend/runtime) | 9 (tests/wave3_g8.rs) | 5 v4_platform flip-greens all pass; `v4_platform_empty_registry` stays green; Condition 6 RC-balance gate landed (`g8_io_trampoline_rc_balanced`). 4 planned integration tests deferred (par-branches, 2× timing tests, cache-hit-rehydrate → Phase 5). |
| Wave 4 (G9 persistent workers) | 11 | 8 | Stress and race-condition coverage; `#[cfg(test)]` instrumentation required. |
| Wave 5 (prior-ring gaps) | 0 | 14 FIXME resolutions + survey addendum | `/qa` parallel work. |
| Wave 6 (showcase) | 0 | 8 | Cross-skill close gate. |
| **Sprint 57 total** | **38 unit** | **~59 integration** | Baseline before: 1602/14. Target after: ≥1636/≤9. |

## Known issues / deferred

- **I-1 (MonoDefn dead-carrier fields)** — `MonoDefn.resolutions`, `MonoDefn.expr_types` are typecheck-internal dead carriers kept from Phase 1 (Sprint 56). Retained as dead state per `/review` Wave 2 I-1 + user approval; deferred to Sprint 58 Phase 5 cleanup. Cross-reference: `design/typecheck/ast-annotation.md` §10.3.
- **`v4_cache_hit_dependency`** — cross-module cache restore still fails; Phase-5-dependent. Not targeted by Wave 3. Stays in the 14-failure baseline.
- **`par-bind!` RC-balance coverage** (`v4_platform_rc_balance_par_branches`) — deferred from Wave 3 integration scope; see §G.8 adoption survey for Wave 5 adoption.
- **Platform scheduling timing tests** (Commutative parallelizes, Sequential serializes) — deferred; runtime scheduling validation is via `tests/scheduler.rs`. Dedicated wall-clock tests will land alongside G9 persistent-worker work.
- **Cache-hit platform-pointer rehydrate** (`v4_platform_cache_hit_platform_ptr_rewrite`) — option (a) chosen per design/int/platform-registry-removal.md §8; deferred to Phase 5.

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
