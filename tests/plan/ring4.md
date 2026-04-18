# Ring 4 Test Plan: Effects

**Features**: IO model, platform DLLs, par-let, par-bind!, trace, run-tests, REPL slash commands, caching, linking, executable generation, hot-reload, lenient evaluation. Side effects and build infrastructure.

**Test count target**: ~120 additional tests (~591 cumulative, matching prototype).

<!-- FIXME(/qa): RC-balance assertion adoption survey. The runtime exposes `cranelisp_runtime::alloc_count()` / `dealloc_count()` / `bytes_current()` as public fns; `tests/helpers/mod.rs:526+` already wraps them in `assert_rc_balanced(src)` and `assert_rc_balanced_with(preamble, src)`. Sprint 56 Wave 2c landed 14 `decision24_*` unit tests inside `crates/cranelisp-runtime/` (string, int, trace, io, marshal, drop helpers) that assert exact balance at the extern boundary. The integration-layer helpers are older and pre-date the Wave 2c convention.

Proposed actions:
1. **Survey** Ring 4 integration tests (especially IO, trace, platform, run-tests, par-let) for which would benefit from wrapping their assertions in `assert_rc_balanced_with(...)` instead of running bare. Expected payoff: IO trampoline leaks (see `crates/cranelisp-runtime/src/io.rs` FIXME on intermediate Pure/Effect nodes) would surface via this helper rather than only via `CRANELISP_RC_TRACE=1` inspection.
2. **Extend** `assert_rc_balanced` with a session-reset variant so tests that register prelude / platform DLLs don't count those one-time allocations as leaks. The current helper handles this via `allocs_before` / `deallocs_before` snapshot, but Ring 4 tests may hold state across multiple evals that needs a per-eval wrapper.
3. **Consider** a `#[rc_balanced]` attribute macro or a `assert_rc_balanced_eval(&mut session, src)` variant to make adoption low-friction inside REPL-session tests that do incremental eval.
4. **Document** the adoption policy in `tests/CLAUDE.md` — which kinds of Ring 4 tests MUST use RC balance assertions vs MAY.

Filed by /sprint during Sprint 56 close per user request (2026-04-18). The infrastructure is already in place; this is about systematic adoption and Ring 4-specific extension. -->

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
