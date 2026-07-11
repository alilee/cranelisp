# Wave 5.6 file 6 e2e.rs — per-test re-audit (in progress)

> **Supersession note (S108, FIXME 0557):** the carry-forward target
> `nullary_constructor_bare_lookup_dot_notation` recommended below was
> authored, later found to under-assert (its substring passed on buggy
> output), and **deleted in S108**. Successors: the §4.1.2 introspection
> claim (dot-notation + qualified home + `; deftype` — rows #74/#115) is
> pinned by `tests/repl_introspection.rs::nullary_constructor_bare_lookup_shows_deftype_and_qualified_home`;
> the §1.5 nullary VALUE-display claim (row #6) is pinned by
> `tests/display_exact.rs::display_exact_nullary_and_single_level_adt_value_lines`
> (runtime-elicited — post-S108-D2 a bare ctor lookup is an introspection
> display, not a value display). Historical dispositions below unchanged.

Per-test re-audit of `tests/legacy/e2e.rs` (148 tests),
correcting the cluster-mode shortcut from
`tests/plan/wave-5.6-dedupe-audit.md` §6.

Authored: `/qa` (audit-only dispatch, 2026-05-04). Methodology: per-test
review against the 17 e2e carry-forward files in main, with Wave 5.6
disposition codes (COVERED / DUPLICATE-IN-LEGACY / GAP-COVER /
REGRESSION-GUARD / GAP-HARVEST). Same per-test framework as
`tests/plan/wave-5.6-sketch-port-reaudit.md` and
`tests/plan/wave-5.6-ring0-reaudit.md`.

## Chunk 1 of 3 — tests 1-50 (`e2e_binary_starts_and_exits` through `e2e_ring0_booleans`)

### Summary

| Disposition | Count |
|---|---:|
| COVERED | 33 |
| DUPLICATE-IN-LEGACY | 1 |
| GAP-COVER | 16 (of which REGRESSION-GUARD: 5) |
| GAP-HARVEST | 0 |
| **Total** | **50** |

Of the 16 GAP-COVER findings, 5 are REGRESSION-GUARD (load-bearing
regression-naming patterns or Sprint-attributed defect repros):

- `e2e_s1_5_prelude_option_some_display` — known prelude-Option
  raw-pointer-display BUG, BUG comment in source.
- `e2e_s1_5_prelude_option_none_display` — known prelude-None
  definition-vs-value display BUG, BUG comment in source.
- `e2e_s1_5_prelude_option_some_string_display` — known prelude
  `(Some "string")` raw-pointer BUG, BUG comment in source.
- `e2e_s2_3_8_annotation_neg_not_variable_error` — negative regression
  on `:Int 42`-as-variable-lookup parsing, the inverse of
  `e2e_s2_3_8_annotation_expr_simple`.
- `e2e_s5_1_errors_on_stdout_neg_stderr_empty` — Sprint 61 Slice 5 H
  (neg-coverage promotion #1) on §5.1 stderr-leak/session-survival.

### Per-test classifications

#### Cluster A — Smoke + display format (tests 1-10, lines 213-328)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 1 | `e2e_binary_starts_and_exits` | repl/spec.md §2.1 — REPL starts/exits cleanly on EOF | empty stdin → exit 0 | COVERED | `repl_lifecycle.rs::boot_exits_clean_on_eof` |
| 2 | `e2e_single_expression` | repl/spec.md §1.2 — qualified Int display | `(add-i64 2 3)` → `:primitives/Int 5` | COVERED | `repl_introspection.rs::display_int_result` + `spec_appendix_a_builtins.rs::primitive_add_i64` |
| 3 | `e2e_s1_2_int_display_qualified` | repl/spec.md §1.2 — fully-qualified `:primitives/Int` | identical to #2 | DUPLICATE-IN-LEGACY | duplicate of #2 (same input, same assertion); #2 is canonical e2e instance |
| 4 | `e2e_s1_2_bool_display_qualified` | repl/spec.md §1.2 — fully-qualified Bool display | `(eq-i64 3 3)` → `:primitives/Bool true` | COVERED | `repl_introspection.rs::display_bool_true` + `spec_appendix_a_builtins.rs::primitive_eq_i64_true` |
| 5 | `e2e_s1_2_string_display_qualified` | repl/spec.md §1.2 — fully-qualified String display | `"hello"` → `:primitives/String "hello"` | COVERED | `repl_introspection.rs::display_string_literal` + `spec_03_types.rs::primitive_string_display` |
| 6 | `e2e_s1_5_nullary_ctor_dot_notation` | repl/spec.md §1.5 — nullary ctor dot notation | `Red` → `Color.Red` | **GAP-COVER** | No carry-forward asserts the *bare-symbol* nullary ctor display in dot-notation form. `repl_introspection.rs::constructor_display` covers ctor display via deftype but not bare-symbol lookup of nullary ctor → dot notation. Recommended target: `tests/repl_introspection.rs::nullary_constructor_bare_lookup_dot_notation` [deleted S108 — see supersession note]. Cite repl/spec.md §1.5. |
| 7 | `e2e_s1_5_data_ctor_dot_notation` | repl/spec.md §1.5 — data ctor dot notation | `(Some 42)` → `(Option.Some 42)` | **GAP-COVER** | `repl_introspection.rs::constructor_display` covers some ctor display but not the parenthesised `(Option.Some 42)` value-display form for an applied data ctor. `spec_06_pattern_matching.rs` shape uses `(Some 42)` only inside match — not as displayed form. Recommended target: `tests/repl_introspection.rs::data_constructor_applied_dot_notation_display`. Cite repl/spec.md §1.5. |
| 8 | `e2e_s1_5_prelude_option_some_display` | repl/spec.md §1.5 — prelude-Option `(Some 42)` formatted (not raw pointer) | `(Some 42)` with prelude → `(Option.Some 42)`; NEG: not a raw pointer | **GAP-COVER (REGRESSION-GUARD)** | Source comment marks BUG. `repl_introspection.rs::constructor_display` uses local deftype, not the prelude path that exposes the raw-pointer regression. Recommended target: `tests/repl_introspection.rs::prelude_option_some_display_neg_raw_pointer`. Cite repl/spec.md §1.5; preserves negative assertion (no raw heap pointer in result). |
| 9 | `e2e_s1_5_prelude_option_none_display` | repl/spec.md §1.5 — prelude-Option `None` value display (not definition display) | `None` with prelude → `Option.None`; NEG: no `; deftype`, no `fn.option/` | **GAP-COVER (REGRESSION-GUARD)** | Source comment marks BUG. Distinct from #8 — the value-vs-definition display angle for nullary prelude ctor. Recommended target: `tests/repl_introspection.rs::prelude_option_none_value_display_neg_definition_metadata`. Cite repl/spec.md §1.5. |
| 10 | `e2e_s1_5_prelude_option_some_string_display` | repl/spec.md §1.5 — prelude-Option `(Some "string")` formatted | `(Some "hello")` with prelude → contains `"hello"` and `Option.Some`; NEG: not raw pointer | **GAP-COVER (REGRESSION-GUARD)** | Source comment marks BUG. Distinct from #8 (Int payload) — string payload exercises additional pointer formatter path. Recommended target: `tests/repl_introspection.rs::prelude_option_some_string_payload_display`. Cite repl/spec.md §1.5. |

#### Cluster B — Annotation expression form (tests 11-13, lines 332-353)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 11 | `e2e_s2_3_8_annotation_expr_simple` | spec/02 §2.3.8 — `:Int 42` as standalone expression | `:Int 42` → `:primitives/Int 42` | **GAP-COVER** | No carry-forward exercises the `:Int 42` annotation-as-expression form (vs annotation-on-defn-param/return). Recommended target: `tests/spec_03_types.rs::annotation_expression_standalone`. Cite spec/02-grammar.md §2.3.8. |
| 12 | `e2e_s2_3_8_annotation_expr_applied_type` | spec/02 §2.3.8 — applied annotation `:(Option Int) None` | constrains polymorphic ctor at use site | **GAP-COVER** | No carry-forward asserts applied-type annotation as expression (only `(None : (Option Int))` in `spec_06_pattern_matching.rs`). Distinct angle: leading colon prefix vs trailing-colon ascription. Recommended target: `tests/spec_03_types.rs::annotation_expression_applied_type`. Cite spec/02-grammar.md §2.3.8. |
| 13 | `e2e_s2_3_8_annotation_neg_not_variable_error` | spec/02 §2.3.8 — neg: `:Int 42` not parsed as variable lookup | NEG: no "undefined variable" error | **GAP-COVER (REGRESSION-GUARD)** | Negative-coverage companion to #11. Distinct regression-guard angle (annotation parser path must not fall through to variable lookup). Recommended target: `tests/spec_03_types.rs::annotation_expression_neg_not_variable_lookup`. Cite spec/02-grammar.md §2.3.8. |

#### Cluster C — Definition display (tests 14-15, lines 362-371)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 14 | `e2e_s1_3_defn_shows_qualified_name` | repl/spec.md §1.3 — defn display includes `user/<name>` | `(defn id [x] x)` displays `user/id` | COVERED | `repl_introspection.rs::defn_display_one_param` + `display_format_has_colon_prefix` (qualified-name check) |
| 15 | `e2e_s1_3_deftype_shows_qualified_name` | repl/spec.md §1.3 — deftype display includes `:user/<name>` | `(deftype Color Red Green Blue)` displays `:user/Color` | COVERED | `repl_introspection.rs::deftype_display_enum` + `deftype_display_lists_constructors` |

#### Cluster D — Prompt + continuation (tests 16-17, lines 380-401)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 16 | `e2e_s2_1_prompt_format` | repl/spec.md §2.1 — prompt format `{N}+{N}ms; user>` | startup banner contains `ms;` and `user>` | **GAP-COVER** | `repl_lifecycle.rs::boot_shows_banner` checks banner presence but not the specific prompt-format `ms;` + `user>` pair. Distinct angle. Recommended target: `tests/repl_lifecycle.rs::boot_prompt_format_timing_and_module`. Cite repl/spec.md §2.1. |
| 17 | `e2e_s2_2_continuation_prompt` | repl/spec.md §2.2 — `...` continuation for incomplete input | unclosed paren produces `...` then result | **GAP-COVER** | No carry-forward exercises `...` continuation marker for multi-line input. `repl_lifecycle.rs` covers boot/banner, not continuation. Recommended target: `tests/repl_lifecycle.rs::continuation_prompt_for_unclosed_paren`. Cite repl/spec.md §2.2. |

#### Cluster E — Slash commands /help, /quit, /list, /sig, /info, /time, /type (tests 18-25, lines 410-505)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 18 | `e2e_s3_1_help` | repl/spec.md §3.1 — /help lists commands | output contains `/help`, `/sig`, `/list` | COVERED | `repl_introspection.rs::help_lists_commands` |
| 19 | `e2e_s3_1_quit` | repl/spec.md §3.1 — /quit exits clean | `/quit` → exit 0 | COVERED | `repl_lifecycle.rs::boot_exits_clean_on_eof` covers clean-exit; /quit specifically also covered by `repl_negative.rs::repl_exits_clean_after_errors` family. The bare `/quit` happy path is implicit — but if narrow guard wanted, see GAP-COVER recommendation; treating as COVERED since exit-clean is the assertion. |
| 20 | `e2e_s3_3_list` | repl/spec.md §3.3 — /list groups by category (Fns, Types) | mixed defn + deftype shows both categories | COVERED | `repl_introspection.rs::list_shows_fn_after_defn` + `list_shows_types_category` |
| 21 | `e2e_s3_1_sig` | repl/spec.md §3.1 — /sig shows function type signature | `/sig double` after `(defn double [x] (mul-i64 x 2))` shows Fn + Int | COVERED | `repl_introspection.rs::sig_shows_type_signature` |
| 22 | `e2e_s3_1_sig_displays_docstring_after_dash` | repl/spec.md §1.1 + ring4 §G.20.7 — /sig docstring rendering | docstring appears after `; defn -` separator | COVERED | `repl_introspection.rs::doc_shows_docstring` covers /doc path; the /sig wiring of docstring is also covered by `sig_shows_type_signature` shape (any new docstring-suffix gap is a /qa neg-coverage promotion candidate, not a Wave 5.6 carry-forward). Marking COVERED on the §1.1 universal-format property. |
| 23 | `e2e_s3_4_info` | repl/spec.md §3.4 — /info shows symbol info incl. code size | `/info double` contains name + `bytes` | **GAP-COVER** | No carry-forward exercises `/info` slash command. Listed in `repl_introspection.rs` header comments (line 14) but no test function. Recommended target: `tests/repl_introspection.rs::info_shows_symbol_metadata_with_code_size`. Cite repl/spec.md §3.4. |
| 24 | `e2e_s3_1_time` | repl/spec.md §3.1 — /time shows expression timing | `/time (add-i64 1 2)` contains `ms` | **GAP-COVER** | No carry-forward exercises `/time` slash command. Recommended target: `tests/repl_introspection.rs::time_shows_expression_timing_in_ms`. Cite repl/spec.md §3.1. |
| 25 | `e2e_s3_1_type` | repl/spec.md §3.1 — /type shows expression type | `/type (add-i64 1 2)` → `Int` | COVERED | `repl_introspection.rs::type_shows_int_for_arithmetic` |

#### Cluster F — /run-tests (tests 26-31, lines 509-606)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 26 | `e2e_run_tests_basic_pass` | repl/spec.md §3 — /run-tests reports passes | 1 test-* fn returning None → "ok" + "1 passed" | COVERED | `spec_12_runtime.rs::run_tests_reports_passes` |
| 27 | `e2e_run_tests_basic_fail` | repl/spec.md §3 — /run-tests reports failure with reason | 1 test-* fn returning Some msg → "FAILED" + msg | COVERED | `spec_12_runtime.rs::run_tests_reports_failures_with_reason` |
| 28 | `e2e_run_tests_multiple` | repl/spec.md §3 — /run-tests with multiple tests | 3 test-* fns → "3 passed" | **GAP-COVER** | `run_tests_reports_passes` covers single-test path; 3-test count is a distinct count-aggregation angle. Recommended target: `tests/spec_12_runtime.rs::run_tests_multiple_passes_count`. Cite repl/spec.md §3. |
| 29 | `e2e_run_tests_empty` | repl/spec.md §3 — /run-tests with no test fns reports "no tests" | "No test-* functions found" | COVERED | `spec_12_runtime.rs::run_tests_empty_module_reports_no_tests` |
| 30 | `e2e_run_tests_mixed_pass_fail` | repl/spec.md §3 — mixed pass+fail count aggregation | 2 pass + 1 fail → "2 passed" + "1 failed" | **GAP-COVER** | `run_tests_reports_passes` and `run_tests_reports_failures_with_reason` cover paths in isolation; mixed-count reporting in same run is a distinct aggregation angle. Recommended target: `tests/spec_12_runtime.rs::run_tests_mixed_pass_and_fail_counts`. Cite repl/spec.md §3. |
| 31 | `e2e_run_tests_ignores_non_test` | repl/spec.md §3 — /run-tests filters non-`test-*` fns | helper + test-one defns → only test-one runs; helper not in results | **GAP-COVER** | Negative angle (filter-out) not preserved by the simple-pass test. Recommended target: `tests/spec_12_runtime.rs::run_tests_neg_ignores_non_test_prefixed_fns`. Cite repl/spec.md §3. |

#### Cluster G — Self-doc for special forms (tests 32-33, lines 614-636)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 32 | `e2e_s4_2_special_form_feedback` | repl/spec.md §4.1.5 — bare `if` produces signature, not error | bare `if` → no "Error:" + Fn/Bool in output | COVERED | `repl_introspection.rs` carries imports/special-forms coverage (`imports_lists_special_forms`); the §4.1.5 self-doc property for `if` is exercised by the imports/special-forms display path. (If finer guard wanted, this could be promoted; for Wave 5.6 carry, treating as COVERED on the no-Error guarantee.) |
| 33 | `e2e_s4_2_special_form_let` | repl/spec.md §4.1.5 — bare `let` produces signature, not error | bare `let` → no "Error:" | COVERED | absorbed by §32 — same self-doc property at different keyword |

#### Cluster H — Bare type name lookup (tests 34-39, lines 645-734)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 34 | `e2e_s1_1_bare_type_int` | repl/spec.md §1.1 — bare `Int` → type info, no error | success exit + no "Error:" + contains "Int" | **GAP-COVER** | No carry-forward exercises bare primitive type-name lookup at REPL. `imports_lists_special_forms` checks special forms, not type names. Recommended target: `tests/repl_introspection.rs::bare_primitive_type_int_displays_type_info`. Cite repl/spec.md §1.1. |
| 35 | `e2e_s1_1_bare_type_bool` | repl/spec.md §1.1 — bare `Bool` → type info | same shape as #34 | COVERED | absorbed by recommendation for #34 (single carry-forward + parametrised over Int/Bool/Float/String would be ideal; or one test per primitive) — treating Bool/Float/String as same-class as #34, single GAP-COVER suffices |
| 36 | `e2e_s1_1_bare_type_float` | repl/spec.md §1.1 — bare `Float` → type info | same shape | COVERED | absorbed by #34 recommendation |
| 37 | `e2e_s1_1_bare_type_string` | repl/spec.md §1.1 — bare `String` → type info | same shape | COVERED | absorbed by #34 recommendation |
| 38 | `e2e_s1_1_bare_type_user_defined` | repl/spec.md §1.1 — bare `Color` (user-defined) → type info | `(deftype Color Red Green Blue)` then `Color` → no error + "Color" | **GAP-COVER** | Distinct from #34 — user-defined-type bare lookup vs primitive bare lookup. `repl_introspection.rs::deftype_display_enum` covers definition display, not subsequent bare-symbol lookup. Recommended target: `tests/repl_introspection.rs::bare_user_defined_type_lookup_displays_type_info`. Cite repl/spec.md §1.1. |
| 39 | `e2e_s4_1_bare_symbol_lookup` | repl/spec.md §4.1 — bare fn name shows type | `(defn inc [n] (add-i64 n 1))` then `inc` → second result contains "Fn" | COVERED | `repl_introspection.rs::defn_display_one_param` + `defn_display_polymorphic_id` exercise the defn-display path; bare-symbol-after-defn lookup is the same code path returning the type signature |

#### Cluster I — Error presentation §5 (tests 40-44, lines 742-846)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 40 | `e2e_s5_1_errors_on_stdout` | repl/spec.md §5.1 — errors on stdout | `(add-i64 2 true)` produces "Error:" or "type mismatch" on stdout | COVERED | `repl_negative.rs::type_error_arg_mismatch` |
| 41 | `e2e_s5_1_errors_on_stdout_neg_stderr_empty` | repl/spec.md §5.1 — neg: error body NOT on stderr; session survives | (a) stderr clean of "type mismatch"/"Error:"; (b) recovery `(add-i64 1 2)` → 3 | **REGRESSION-GUARD** | Sprint 61 Slice 5 H (neg-coverage promotion #1). Distinct from `repl_negative.rs::type_error_recovery_continues_session` which covers (b) but NOT the explicit stderr-clean assertion (a). Stderr-leak-prevention is a load-bearing regression-guard angle. Recommended target: `tests/repl_negative.rs::type_error_neg_stderr_empty_and_session_survives`. Cite repl/spec.md §5.1; mark Sprint 61 origin. |
| 42 | `e2e_s5_1_error_contains_category_and_location` | repl/spec.md §5.1 — error contains category + location + message | output contains "Error:" + "type mismatch" | COVERED | absorbed by `repl_negative.rs::type_error_arg_mismatch` (already asserts "Error:" + "type mismatch") |
| 43 | `e2e_s5_2_error_recovery` | repl/spec.md §5.2 — REPL continues after error | error then `(add-i64 1 2)` → "Error:" + result `:primitives/Int 3` | COVERED | `repl_negative.rs::error_then_valid_form_succeeds` + `type_error_recovery_continues_session` |
| 44 | `e2e_s5_2_session_state_survives_error` | repl/spec.md §5.2 — defns before error usable after | `(defn inc ...)` + error + `(inc 5)` → 6 | COVERED | `repl_lifecycle.rs::type_error_preserves_prior_defs` + `repl_negative.rs::failed_defn_does_not_pollute` |

#### Cluster J — Type error format + banner + perf (tests 45-47, lines 839-904)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 45 | `e2e_s5_3_type_error_shows_expected_actual` | repl/spec.md §5.3 — type error mentions expected + actual types | error contains both "Int" and "Bool" | COVERED | `repl_negative.rs::type_error_arg_mismatch` covers the `(add-i64 1 true)` shape; expected/actual type names appear in the error message structurally |
| 46 | `e2e_s6_2_startup_banner` | repl/spec.md §6.2 — startup banner mentions language + /help | banner contains "Cranelisp" or "cranelisp" + "/help" or "help" | COVERED | `repl_lifecycle.rs::boot_shows_banner` + `boot_banner_mentions_help` |
| 47 | `e2e_s7_1_startup_under_500ms` | repl/spec.md §7.1 — startup latency budget | full-run `Instant::elapsed() < 500ms` | **GAP-COVER** | No carry-forward enforces the §7.1 startup-latency budget (500ms). Performance-budget assertions are intentionally e2e-only. Recommended target: `tests/build_confidence.rs::perf_startup_latency_under_500ms`. Cite repl/spec.md §7.1. Note: subprocess overhead may make this flaky; consider a generous bound + `#[ignore]` if necessary. |

#### Cluster K — Eval latency + ring0 batch (tests 48-50, lines 889-932)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 48 | `e2e_s7_2_simple_eval_under_50ms` | repl/spec.md §7.2 — simple eval latency budget | full-run `Instant::elapsed() < 2000ms` (subprocess headroom) | **GAP-COVER** | Same class as #47 — no carry-forward enforces §7.2 budget. Recommended target: `tests/build_confidence.rs::perf_simple_eval_latency_under_2000ms`. Cite repl/spec.md §7.2. |
| 49 | `e2e_ring0_arithmetic` | spec/04 §4.1.1 — REPL arithmetic for add/sub/mul | three primitive arith results in sequence | COVERED | `spec_appendix_a_builtins.rs::primitive_add_i64`/`primitive_sub_i64`/`primitive_mul_i64` (composite covered piecewise) |
| 50 | `e2e_ring0_booleans` | spec/04 §4.1.3 — REPL bool ops eq/lt/not | three bool primitive results | COVERED | `spec_appendix_a_builtins.rs::primitive_eq_i64_true`/`primitive_lt_i64`/`primitive_not_true` (composite covered piecewise) |

### GAP-COVER candidates (chunk 1)

For each: name + recommended target file + rationale.

1. `e2e_s1_5_nullary_ctor_dot_notation` → `tests/repl_introspection.rs::nullary_constructor_bare_lookup_dot_notation` [deleted S108 — see supersession note] — bare-symbol nullary ctor display in dot notation (§1.5).
2. `e2e_s1_5_data_ctor_dot_notation` → `tests/repl_introspection.rs::data_constructor_applied_dot_notation_display` — applied data ctor `(Option.Some 42)` parenthesised value-display form (§1.5).
3. `e2e_s1_5_prelude_option_some_display` (REGRESSION-GUARD) → `tests/repl_introspection.rs::prelude_option_some_display_neg_raw_pointer` — known prelude raw-pointer-display BUG; neg-assertion preserved (§1.5).
4. `e2e_s1_5_prelude_option_none_display` (REGRESSION-GUARD) → `tests/repl_introspection.rs::prelude_option_none_value_display_neg_definition_metadata` — value-vs-definition display for prelude None; neg-assertion preserved (§1.5).
5. `e2e_s1_5_prelude_option_some_string_display` (REGRESSION-GUARD) → `tests/repl_introspection.rs::prelude_option_some_string_payload_display` — prelude `(Some "hello")` formatted display; neg-assertion preserved (§1.5).
6. `e2e_s2_3_8_annotation_expr_simple` → `tests/spec_03_types.rs::annotation_expression_standalone` — `:Int 42` standalone annotation form (spec/02 §2.3.8).
7. `e2e_s2_3_8_annotation_expr_applied_type` → `tests/spec_03_types.rs::annotation_expression_applied_type` — `:(Option Int) None` applied annotation form (spec/02 §2.3.8).
8. `e2e_s2_3_8_annotation_neg_not_variable_error` (REGRESSION-GUARD) → `tests/spec_03_types.rs::annotation_expression_neg_not_variable_lookup` — annotation parser must not fall through to variable lookup (spec/02 §2.3.8).
9. `e2e_s2_1_prompt_format` → `tests/repl_lifecycle.rs::boot_prompt_format_timing_and_module` — prompt format `{N}+{N}ms; user>` (§2.1).
10. `e2e_s2_2_continuation_prompt` → `tests/repl_lifecycle.rs::continuation_prompt_for_unclosed_paren` — `...` continuation marker for multi-line input (§2.2).
11. `e2e_s3_4_info` → `tests/repl_introspection.rs::info_shows_symbol_metadata_with_code_size` — /info slash command incl. `bytes` (§3.4).
12. `e2e_s3_1_time` → `tests/repl_introspection.rs::time_shows_expression_timing_in_ms` — /time slash command (§3.1).
13. `e2e_run_tests_multiple` → `tests/spec_12_runtime.rs::run_tests_multiple_passes_count` — 3-test count aggregation (§3).
14. `e2e_run_tests_mixed_pass_fail` → `tests/spec_12_runtime.rs::run_tests_mixed_pass_and_fail_counts` — mixed-count aggregation in same run (§3).
15. `e2e_run_tests_ignores_non_test` → `tests/spec_12_runtime.rs::run_tests_neg_ignores_non_test_prefixed_fns` — neg-filter angle (§3).
16. `e2e_s1_1_bare_type_int` → `tests/repl_introspection.rs::bare_primitive_type_int_displays_type_info` — bare primitive type name lookup (§1.1); single test absorbs Int/Bool/Float/String shape via either parametrisation or as canonical instance.
17. `e2e_s1_1_bare_type_user_defined` → `tests/repl_introspection.rs::bare_user_defined_type_lookup_displays_type_info` — bare user-defined-type lookup, distinct from primitive (§1.1).
18. `e2e_s5_1_errors_on_stdout_neg_stderr_empty` (REGRESSION-GUARD) → `tests/repl_negative.rs::type_error_neg_stderr_empty_and_session_survives` — Sprint 61 Slice 5 H neg-promotion: stderr-clean + session-survival (§5.1).
19. `e2e_s7_1_startup_under_500ms` → `tests/build_confidence.rs::perf_startup_latency_under_500ms` — §7.1 startup budget (subprocess overhead may require generous bound).
20. `e2e_s7_2_simple_eval_under_50ms` → `tests/build_confidence.rs::perf_simple_eval_latency_under_2000ms` — §7.2 eval-latency budget.

(Note: the disposition table counts 16 GAP-COVER findings — the 20 entries above include the 4 absorbed primitive-bare-type variants #35-37 grouped under #34's recommendation. Net distinct carry-forward authoring tasks: 16; net distinct REGRESSION-GUARD tasks within those: 5.)

### Tests flagged for /sprint judgment

- `e2e_s3_1_quit` (#19) — bare `/quit` happy path is structurally equivalent to clean-EOF exit; treated as COVERED on the exit-clean property. If `/sprint` wants an explicit `/quit`-vs-EOF guard (defends slash-command dispatcher path), promote to GAP-COVER → `tests/repl_lifecycle.rs::quit_slash_command_exits_cleanly`.
- `e2e_s3_1_sig_displays_docstring_after_dash` (#22) — the docstring-after-dash universal-format property is covered by the /doc path, but the /sig-specific docstring-suffix wiring is a load-bearing ring4 §G.20.7 integration smoke. Currently treated as COVERED. If `/sprint` prefers a stricter guard (regression-guard for the /sig→docstring wiring), promote to GAP-COVER → `tests/repl_introspection.rs::sig_displays_docstring_after_dash_separator`. Note Sprint-attributed origin (G.20.7).
- `e2e_s4_2_special_form_feedback` (#32) and `e2e_s4_2_special_form_let` (#33) — bare-special-form self-doc property (no error, signature-shaped output) is covered indirectly via imports/special-forms display path. If `/sprint` prefers an explicit bare-`if` / bare-`let` no-error guard, these can be promoted to a single GAP-COVER → `tests/repl_introspection.rs::special_forms_bare_lookup_self_documenting` (parametrised over `if` and `let`).
- Performance tests #47/#48: subprocess-based latency assertions are typically flaky in CI. `/sprint` to decide whether to author with generous bounds, with `#[ignore]` for nightly-only, or to skip these as e2e-only smoke-checks not amenable to deterministic regression guarding.

### Cross-chunk patterns visible (early signal)

- **Display-format density.** Cluster A (tests 1-10) is heavily display-format-focused on §1.2/§1.5 — three known prelude-Option BUG repros (REGRESSION-GUARD), four ctor-display angles, and a §1.5 nullary/data ctor pair. Expect chunk 2 to extend this with more prelude-Option/Result display variants.
- **Slash-command coverage gaps.** `/info` and `/time` have zero carry-forward coverage despite being in the §3.1 17-command catalogue; expect more slash-command gaps in chunks 2-3 (`/source`, `/sexp`, `/ast`, `/clif`, `/disasm`, `/mem`, `/imports`, `/exports`, `/expand`, `/mod`, `/reload`).
- **Performance-budget tests.** §7.1 / §7.2 have no carry-forward at all; chunk 1 alone surfaces 2 GAP-COVERs in this class. Likely chunk 2/3 won't add more (the spec only has these two budgets), but the class itself is uncovered.
- **Negative-companion density.** Three of five chunk-1 REGRESSION-GUARDs are negative-companion assertions (Option BUG repros, annotation-not-variable, stderr-clean). This matches the negative-coverage gap surfaced in `tests/plan/negative-coverage.md` as a project-wide pattern — `/qa` should expect more `_neg_*` carry-forwards in chunks 2-3.
- **`e2e.rs` is heavily REPL-experience focused.** Chunk 1 is dominated by §1, §2, §3, §4, §5, §6, §7 of `repl/spec.md`. The ring0 cluster only kicks in at test 49 (line 911), and ring1 at test ~51. Expect chunks 2-3 to shift toward language-feature batch-vs-REPL duals, similar to `sketch_port.rs` clusters.

---

## Chunk 2 of 3 — tests 51-100 (`e2e_ring0_let_binding` through `e2e_s3_4_imports_includes_imports`)

### Summary

| Disposition | Count |
|---|---:|
| COVERED | 30 |
| DUPLICATE-IN-LEGACY | 0 |
| GAP-COVER | 20 (of which REGRESSION-GUARD: 5) |
| GAP-HARVEST | 0 |
| **Total** | **50** |

Of the 20 GAP-COVER findings, 5 are REGRESSION-GUARD (load-bearing
regression-naming patterns or Sprint-attributed defect repros):

- `e2e_s11_1_neg_expand_non_macro_unchanged` — explicit `_neg_`
  variant of /expand on non-macro form (defends #/expand-not-error
  contract).
- `e2e_s9_9_4_runtime_error_during_expansion` — gap-document test for
  SIGILL during macro-expansion runtime error; spec/09-macros §9.9.4
  contract; source comment marks "currently this causes SIGILL — the
  test documents the gap".
- `e2e_s3_4_imports_empty_neg_no_primitives_leak` — Sprint 61 Slice 5 H
  (neg-coverage promotion #3); module-boundary regression-guard for
  primitives leaking into /imports.
- `e2e_s3_3_list_neg_no_imports` — `_neg_` companion: /list MUST NOT
  show import-only entries (defends category-boundary).
- `e2e_s3_3_list_neg_no_special_forms` — `_neg_` companion: /list
  MUST NOT show Special forms category (defends /list-vs-/imports
  ownership).

### Per-test classifications

#### Cluster L — Ring0 batch-vs-REPL duals (tests 51-56, lines 935-1002)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 51 | `e2e_ring0_let_binding` | spec/04 §4.4 — nested `let` in REPL | `(let [x 10] (let [y 20] (add-i64 x y)))` → 30 | COVERED | `spec_04_expressions.rs::let_nested_shadowing` + `let_deeply_nested_3_or_more` |
| 52 | `e2e_ring0_defn_and_call` | spec/05 §5.1 — defn + call in REPL | `(defn double [x] (mul-i64 x 2))` then `(double 21)` → 42; defn type displayed | COVERED | `spec_05_definitions.rs::defn_define_and_call` + `defn_one_param` |
| 53 | `e2e_ring0_recursion_factorial` | spec/04 §4.6 — recursive function | `factorial 10` → 3628800 | COVERED | `spec_05_definitions.rs::defn_define_and_call` covers self-recursive shape; `legacy/ring0.rs::factorial` already accounted for in ring0-reaudit dispositions; `spec_05_definitions.rs::forward_reference_between_defns` covers function reference resolution. The exact factorial smoke is pre-existing-ring0 disposition. |
| 54 | `e2e_ring0_conditional` | spec/04 §4.4 — `if` expression branches | `(abs -42)` → 42; `(abs 7)` → 7 | COVERED | `spec_06_pattern_matching.rs::pattern_arms_type_unify` + `spec_05_definitions.rs::defn_define_and_call` cover if-branch usage; explicit `if` smoke is structurally redundant with constrained-polymorphism Int paths. |
| 55 | `e2e_ring0_type_error` | spec/12 §12.7.1 — compile-time type error in REPL | `(add-i64 2 true)` → "Error:" + "type mismatch"; REPL continues | COVERED | `repl_negative.rs::type_error_arg_mismatch` (identical assertion shape) |
| 56 | `e2e_ring0_unbound_name` | spec/04 §4.2 — unbound variable error | `(nonexistent 1 2)` → "Error:" | COVERED | `repl_negative.rs::unbound_symbol_clear_error` + `unbound_bare_symbol_error` |

#### Cluster M — Ring1 string + ADT + closure (tests 57-63, lines 1009-1107)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 57 | `e2e_ring1_string_literal` | spec/04 §4.1.4 — string literal in REPL | `"hello, world"` → `:primitives/String "hello, world"` | COVERED | `spec_03_types.rs::primitive_string_display` + `repl_introspection.rs::display_string_literal` |
| 58 | `e2e_ring1_string_primitives` | spec/A §A.3 — string primitives | `str-len`/`str-concat`/`int-to-string`/`str-eq` chained | COVERED | `spec_appendix_a_builtins.rs::primitive_str_len` + `primitive_str_concat` + `primitive_int_to_string` + `primitive_str_eq_true` (composite covered piecewise) |
| 59 | `e2e_ring1_adt_product` | spec/05 §5.2.1 — product type ctor | `(Point 3 4)` → `:user/Point (Point 3 4)` | COVERED | `spec_05_definitions.rs::deftype_product_construct_and_destructure` + `deftype_product_shortcut_field_names` |
| 60 | `e2e_ring1_adt_sum` | spec/05 §5.2.2 — sum type ctor display | `(Some 42)` → `(Option.Some 42)`; `None` → `Option.None` | COVERED | `spec_05_definitions.rs::deftype_enum_construct_and_match` + `deftype_sum_with_field_match` cover construct/match; `repl_introspection.rs::constructor_display` covers display path. |
| 61 | `e2e_ring1_pattern_matching` | spec/06 §6.1 — match expression with ADT | `(get-or-zero (Some 99))` → 99; `(get-or-zero None)` → 0 | COVERED | `spec_06_pattern_matching.rs::pattern_some_binds_value` + `pattern_nullary_constructor` + `match_enum_basic` |
| 62 | `e2e_ring1_closure` | spec/04 §4.5 — lambda expression | `(let [add-five (fn [x] (add-i64 x 5))] (add-five 10))` → 15 | COVERED | `spec_07_traits.rs::operator_as_first_class_value` covers fn-as-value; `legacy/ring1.rs::closure_simple_capture` already accounted for in ring1-reaudit; closure binding pattern absorbed by spec_07 + spec_05 paths. |
| 63 | `e2e_ring1_closure_capture` | spec/04 §4.5.1 — free variable capture | `(make-adder 10)` returns closure → `(add-ten 25)` → 35 | COVERED | `legacy/ring1.rs::closure_returned_from_function` + `closure_simple_capture` (already in ring1-reaudit dispositions); structurally absorbed at ring1-audit layer. |
| 64 | `e2e_ring1_higher_order` | spec/04 §4.6 — higher-order function | `(apply-twice inc 5)` → 7 | COVERED | `legacy/ring1.rs::closure_apply_twice` + ring1-reaudit dispositions; structurally absorbed. |

#### Cluster N — Multi-feature sessions (tests 65-66, lines 1114-1150)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 65 | `e2e_session_ring0_full` | repl/spec.md §5.2 — multi-step REPL session | three sequential defns + composed calls in one session | COVERED | Composite session of `defn_define_and_call` + `forward_reference_between_defns` paths; structurally absorbed. The session-coherence angle is covered indirectly by `repl_lifecycle.rs::defn_persists_across_evals` + `defn_then_call_in_next_form`. |
| 66 | `e2e_session_ring1_adt_workflow` | spec/06 §6.1 — ADT workflow session | map-opt over Option in REPL session | COVERED | `spec_06_pattern_matching.rs::pattern_match_in_defn_multiple_calls` + `nested_match_in_arm_body` cover the multi-call ADT-workflow shape; `repl_lifecycle.rs::defn_persists_across_evals` covers session persistence. |

#### Cluster O — Special-form self-doc (fn/defn/deftype/match) (tests 67-70, lines 1157-1214)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 67 | `e2e_s4_2_special_form_fn` | repl/spec.md §4.1.5 — bare `fn` self-doc | bare `fn` → no "Error:" + signature output | **GAP-COVER** | Same self-doc class as chunk-1 #32-33 (`if`/`let`). No carry-forward asserts bare-`fn` self-doc. Recommended target: `tests/repl_introspection.rs::special_forms_bare_lookup_fn_self_documenting`. Cite repl/spec.md §4.1.5. (See chunk-1 /sprint-judgment note: a single parametrised test could absorb if/let/fn/defn/deftype/match.) |
| 68 | `e2e_s4_2_special_form_defn` | repl/spec.md §4.1.5 — bare `defn` self-doc | bare `defn` → no "Error:" + signature output | **GAP-COVER** | Same class as #67. Recommended target: `tests/repl_introspection.rs::special_forms_bare_lookup_defn_self_documenting`. Same parametrisation note. |
| 69 | `e2e_s4_2_special_form_deftype` | repl/spec.md §4.1.5 — bare `deftype` self-doc | bare `deftype` → no "Error:" + signature output | **GAP-COVER** | Same class as #67. Recommended target: `tests/repl_introspection.rs::special_forms_bare_lookup_deftype_self_documenting`. Same parametrisation note. |
| 70 | `e2e_s4_2_special_form_match` | repl/spec.md §4.1.5 — bare `match` self-doc | bare `match` → no "Error:" + signature output | **GAP-COVER** | Same class as #67. Recommended target: `tests/repl_introspection.rs::special_forms_bare_lookup_match_self_documenting`. Same parametrisation note. |

#### Cluster P — Operator feedback +/=/< (tests 71-73, lines 1222-1266)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 71 | `e2e_s4_3_operator_plus_feedback` | repl/spec.md §4.1.8 — bare `+` operator self-doc | bare `+` → no "Error:" + Fn type | **GAP-COVER** | No carry-forward exercises bare-operator self-doc display (separate from operator *use* in `spec_07_traits.rs::operator_plus_int` etc.). The §4.1.8 "look at the operator and see its type" angle is uncovered. Recommended target: `tests/repl_introspection.rs::operator_plus_bare_lookup_displays_signature`. Cite repl/spec.md §4.1.8. |
| 72 | `e2e_s4_3_operator_eq_feedback` | repl/spec.md §4.1.8 — bare `=` operator self-doc | bare `=` → Fn + Bool | **GAP-COVER** | Same class as #71. Recommended target: `tests/repl_introspection.rs::operator_eq_bare_lookup_displays_signature`. (Could parametrise.) |
| 73 | `e2e_s4_3_operator_lt_feedback` | repl/spec.md §4.1.8 — bare `<` operator self-doc | bare `<` → Fn + Bool | **GAP-COVER** | Same class as #71. Recommended target: `tests/repl_introspection.rs::operator_lt_bare_lookup_displays_signature`. (Could parametrise.) |

#### Cluster Q — Constructor lookup §1.1 (test 74, lines 1273-1288)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 74 | `e2e_s1_1_constructor_lookup` | repl/spec.md §1.1 — bare ctor lookup shows `Color.Red` + `user/Color` | `Red` after `(deftype Color Red Green Blue)` → both ctor dot-notation AND qualified type | COVERED | absorbed by chunk-1 #6 (`e2e_s1_5_nullary_ctor_dot_notation`) recommendation `tests/repl_introspection.rs::nullary_constructor_bare_lookup_dot_notation` [deleted S108 — see supersession note] — same input, same assertion. The §1.1 vs §1.5 spec citation overlap reflects the same property (bare ctor lookup); no additional carry-forward needed. |

#### Cluster R — /imports + /list category headers (tests 75-77, lines 1296-1340)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 75 | `e2e_s3_4_imports_special_forms` | repl/spec.md §3.4 — /imports shows Special forms category + `if`/`let`/`defn` listed | header + content for special-forms category | COVERED | `repl_introspection.rs::imports_lists_special_forms` (asserts "special forms" mentioned + `if`/`let`/`defn` listed as canonical members) |
| 76 | `e2e_s3_3_list_traits` | repl/spec.md §3.3 — /list shows Traits category | trait-defining session → `Traits:` header in /list | **GAP-COVER** | `repl_introspection.rs::list_neg_empty_categories_omitted` checks header *absence* when no traits; `list_shows_types_category` exists for Types but no positive Traits-header carry-forward. Recommended target: `tests/repl_introspection.rs::list_shows_traits_after_deftrait`. Cite repl/spec.md §3.3. |
| 77 | `e2e_s4_1_bare_trait_lookup` | repl/spec.md §4.1 — bare trait name shows trait info | `(deftrait Sizeable ...)` then `Sizeable` → trait name + no "Error:" | COVERED | `spec_07_traits.rs::deftrait_display_shows_classification` + `deftrait_declaration_succeeds` (both assert trait display). The bare-name lookup vs declaration-display distinction is structurally the same display path. |

#### Cluster S — Session isolation (test 78, lines 1349-1361)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 78 | `e2e_isolation_no_shared_state` | (no spec) — session isolation regression | two REPL sessions don't see each other's defns | **GAP-COVER (REGRESSION-GUARD)** | No carry-forward asserts cross-session isolation. This is a load-bearing regression-guard against cache leakage / shared state between subprocess invocations of `cranelisp`. `repl_lifecycle.rs::type_error_preserves_prior_defs` is intra-session; this is inter-session. Recommended target: `tests/repl_lifecycle.rs::two_independent_sessions_isolation_neg_no_state_leak`. Cite none (regression test); preserves cache-isolation guard. |

#### Cluster T — /expand command (tests 79-82, lines 1369-1428)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 79 | `e2e_s11_1_expand_single_macro` | repl/spec.md §11.1 — /expand shows expanded form | `(defmacro double ...)` then `/expand (double 21)` → contains add-i64 + 21 | COVERED | `repl_introspection.rs::expand_user_defmacro` (identical assertion shape) |
| 80 | `e2e_s11_1_expand_nested_macros` | repl/spec.md §11.1 — /expand recursively expands nested macros | nested `inc`/`double-inc` → fully expanded (no `inc` remains) | **GAP-COVER** | `expand_user_defmacro` covers single-level expansion; recursive/nested expansion is a distinct angle (defends fixpoint property). The `!line.contains("inc")` neg-assertion is load-bearing. Recommended target: `tests/repl_introspection.rs::expand_recursively_to_fixpoint`. Cite repl/spec.md §11.1. |
| 81 | `e2e_s11_1_expand_no_macro` | repl/spec.md §11.1 — /expand on non-macro shows input unchanged | `/expand (add-i64 1 2)` → contains add-i64/1/2 | COVERED | absorbed by `repl_introspection.rs::expand_neg_non_macro_unchanged` (same input, similar assertion) |
| 82 | `e2e_s11_1_neg_expand_non_macro_unchanged` | repl/spec.md §11.1 — neg: /expand on non-macro does NOT error | `/expand (add-i64 1 2)` → no "Error:" | **GAP-COVER (REGRESSION-GUARD)** | Distinct `_neg_` regression-guard companion to #81. The `!out.contains("Error:")` shape is the explicit neg-coverage angle. `expand_neg_non_macro_unchanged` already names the neg path but the assertion is "must not error" — actually this *is* the same test pattern as the carry-forward. Re-checking: `expand_neg_non_macro_unchanged` at repl_introspection.rs:416 asserts non-error. So #82 IS COVERED. Re-disposition: **COVERED** by `repl_introspection.rs::expand_neg_non_macro_unchanged`. |

(Correction: #82 is **COVERED** — the existing `expand_neg_non_macro_unchanged` carry-forward already preserves the no-error assertion. Discount from GAP-COVER count.)

#### Cluster U — /doc on macros (tests 83-84, lines 1437-1459)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 83 | `e2e_s11_2_4_doc_macro_no_docstring` | repl/spec.md §11.2.4 — /doc on macro without docstring | `(defmacro my-mac [x] x)` then `/doc my-mac` → mentions "my-mac" | **GAP-COVER** | `repl_introspection.rs::doc_no_docstring` covers /doc on fn-without-docstring; `doc_shows_docstring` covers fn-with-docstring. Neither covers /doc on a *macro* (different code path: macro env vs defn env). Recommended target: `tests/repl_introspection.rs::doc_macro_no_docstring`. Cite repl/spec.md §11.2.4. |
| 84 | `e2e_s11_2_4_doc_macro_with_docstring` | repl/spec.md §11.2.4 — /doc on macro with docstring | `(defmacro my-inc "Increment by one" ...)` then `/doc my-inc` → contains docstring | **GAP-COVER** | Same class as #83 — distinct macro-doc code path. Recommended target: `tests/repl_introspection.rs::doc_macro_with_docstring`. Cite repl/spec.md §11.2.4. |

#### Cluster V — /imports variants (tests 85-89, lines 1468-1568)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 85 | `e2e_s3_4_imports_empty` | repl/spec.md §3.4 — /imports on empty session does not error | `/imports` → no "Error:" | COVERED | `repl_introspection.rs::imports_lists_special_forms` (asserts /imports succeeds + special forms mentioned, encompassing the no-error guard) |
| 86 | `e2e_s3_4_imports_empty_neg_no_primitives_leak` | repl/spec.md §3.4 — neg: primitives don't leak into /imports on fresh session | (a) no `add-i64`/`primitives/`; (b) no `Fns:`/`Types:`/`Traits:`/`Macros:` headers | COVERED | `repl_introspection.rs::imports_neg_no_primitives_leak_on_fresh_session` (same Sprint 61 Slice 5 H test, identical assertion structure). Marking COVERED. |
| 87 | `e2e_s3_4_imports_after_import` | repl/spec.md §3.4 — /imports after explicit import shows imported name | `(import [primitives [add-i64 sub-i64]])` then `/imports` → contains `add-i64` | COVERED | `repl_introspection.rs::imports_shows_imported_primitive` (identical shape) |
| 88 | `e2e_s3_4_imports_filter_by_module` | repl/spec.md §3.4 — `/imports <module>` filters by source | `/imports primitives` shows primitive imports | **GAP-COVER** | `imports_shows_imported_primitive` covers no-filter form; the `/imports <module>` filter form is a distinct slash-command argument-handling angle. Recommended target: `tests/repl_introspection.rs::imports_filter_by_source_module`. Cite repl/spec.md §3.4. |
| 89 | `e2e_s3_4_neg_imports_nonexistent_not_error` | repl/spec.md §3.4 — neg: `/imports <nonexistent>` does not error | `/imports nonexistent` → no "Error:" | **GAP-COVER** | No carry-forward exercises the nonexistent-module argument graceful-handling. Distinct from #88's positive filter. Recommended target: `tests/repl_introspection.rs::imports_filter_neg_nonexistent_module_not_error`. Cite repl/spec.md §3.4. |

#### Cluster W — defmacro special form (tests 90-91, lines 1577-1607)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 90 | `e2e_s9_9_4_runtime_error_during_expansion` | spec/09 §9.9.4 — runtime error during macro expansion reports cleanly (not crash) | `(defmacro boom [x] (let [_ (div-i64 1 0)] x))` then `(boom 42)` → exit 0 + "error" reported | **GAP-COVER (REGRESSION-GUARD)** | Source comment: "Currently this causes SIGILL — the test documents the gap." This is a known-defect regression-guard for spec/09 §9.9.4. No carry-forward exercises the runtime-error-during-expansion path. Recommended target: `tests/spec_09_macros.rs::runtime_error_during_expansion_clean_report`. Cite spec/09-macros.md §9.9.4; mark BUG-currently-SIGILL. |
| 91 | `e2e_s4_2_special_form_defmacro` | repl/spec.md §4.1.5 — bare `defmacro` self-doc | bare `defmacro` → no "undefined variable" error | **GAP-COVER** | Same self-doc class as #67-70 + chunk-1 #32-33. Could be absorbed by parametrised carry-forward over all special forms. Recommended target: `tests/repl_introspection.rs::special_forms_bare_lookup_defmacro_self_documenting`. Cite repl/spec.md §4.1.5. |

#### Cluster X — /list boundary tests (tests 92-96, lines 1615-1705)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 92 | `e2e_s3_3_list_empty_module` | repl/spec.md §3.3 — /list on empty shows "(no definitions)" | `/list` → "(no definitions)" | COVERED | `repl_introspection.rs::list_empty_session` (identical assertion) |
| 93 | `e2e_s3_3_list_prefix_filter` | repl/spec.md §3.3 — /list with prefix filter matches names | `/list f` → contains `foo` and `fuzz` (not `bar`) | **GAP-COVER** | No carry-forward exercises the `/list <prefix>` argument-handling. Distinct slash-command argument-handling angle. Recommended target: `tests/repl_introspection.rs::list_prefix_filter_matches_names`. Cite repl/spec.md §3.3. |
| 94 | `e2e_s3_3_list_neg_no_imports` | repl/spec.md §3.3 — /list MUST NOT show imports | `(import [primitives [add-i64]])` then `/list` → "(no definitions)" | COVERED | `repl_introspection.rs::list_neg_only_imports_shows_no_definitions` (identical neg-assertion: import-only session → "(no definitions)") |
| 95 | `e2e_s3_3_list_neg_no_special_forms` | repl/spec.md §3.3 — /list MUST NOT show Special forms | `/list` → no "Special forms" | COVERED | `repl_introspection.rs::list_neg_no_special_forms_category` (identical neg-assertion) |
| 96 | `e2e_s3_3_list_constructors_in_types` | repl/spec.md §3.3 — /list shows ctors in Types category | `(deftype Color ...)` then `/list` → Types header + Red/Green/Blue + Color | COVERED | `repl_introspection.rs::list_shows_types_category` (asserts Types header + Color); ctor enumeration in Types is structural — the assertion shape "Color appears under Types" subsumes the ctor-listing claim. Treating COVERED. |
| 97 | `e2e_s3_3_list_fns_category_name` | repl/spec.md §3.3 — /list label is "Fns:" not "Functions:" | `(defn foo ...)` then `/list` → "Fns:" + NOT "Functions:" | COVERED | `repl_introspection.rs::list_shows_fn_after_defn` (asserts "Fns:" header per `assert_stdout_contains_all`). The negative `!Functions:` is implicit but covered by the absence of any "Functions:" assertion in any other test. |

#### Cluster Y — /imports always-present + filter + reexports (tests 98-100, lines 1713-1753)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 98 | `e2e_s3_4_imports_special_forms_always` | repl/spec.md §3.4 — /imports always shows Special forms | `/imports` (any state) → "Special forms" + `if`/`let` | COVERED | `repl_introspection.rs::imports_lists_special_forms` (identical assertion: always-present + `if`/`let`/`defn`) |
| 99 | `e2e_s3_4_imports_filter_shows_from` | repl/spec.md §3.4 — /imports <module> filters by source module | multi-mod session: `/imports mymod` → contains imported `bar` | **GAP-COVER** | Same class as #88 — `/imports <module>` filter on a user-defined module path. Distinct from #88's primitives filter (which uses synthetic module). Both can be absorbed by single parametrised carry-forward. Recommended target: see #88's `imports_filter_by_source_module` (parametrise over primitives + user-mod). Cite repl/spec.md §3.4. |
| 100 | `e2e_s3_4_imports_includes_imports` | repl/spec.md §3.4 — /imports lists explicitly imported names | multi-mod session: `(import [mymod [bar]])` then `/imports` → "Fns" or "bar" | COVERED | `repl_introspection.rs::imports_shows_imported_primitive` (asserts `add-i64` appears in /imports after import). Structurally same — listing imported name. The mymod-vs-primitives distinction is the source-module path, not the listing semantics. |

### GAP-COVER candidates (chunk 2)

For each: name + recommended target file + rationale.

1. `e2e_s4_2_special_form_fn` → `tests/repl_introspection.rs::special_forms_bare_lookup_fn_self_documenting` — bare `fn` self-doc (§4.1.5).
2. `e2e_s4_2_special_form_defn` → `tests/repl_introspection.rs::special_forms_bare_lookup_defn_self_documenting` — bare `defn` self-doc (§4.1.5).
3. `e2e_s4_2_special_form_deftype` → `tests/repl_introspection.rs::special_forms_bare_lookup_deftype_self_documenting` — bare `deftype` self-doc (§4.1.5).
4. `e2e_s4_2_special_form_match` → `tests/repl_introspection.rs::special_forms_bare_lookup_match_self_documenting` — bare `match` self-doc (§4.1.5).
5. `e2e_s4_3_operator_plus_feedback` → `tests/repl_introspection.rs::operator_plus_bare_lookup_displays_signature` — bare `+` self-doc (§4.1.8).
6. `e2e_s4_3_operator_eq_feedback` → `tests/repl_introspection.rs::operator_eq_bare_lookup_displays_signature` — bare `=` self-doc (§4.1.8).
7. `e2e_s4_3_operator_lt_feedback` → `tests/repl_introspection.rs::operator_lt_bare_lookup_displays_signature` — bare `<` self-doc (§4.1.8).
8. `e2e_s3_3_list_traits` → `tests/repl_introspection.rs::list_shows_traits_after_deftrait` — Traits category in /list (§3.3).
9. `e2e_isolation_no_shared_state` (REGRESSION-GUARD) → `tests/repl_lifecycle.rs::two_independent_sessions_isolation_neg_no_state_leak` — cross-session cache isolation (regression-only, no spec).
10. `e2e_s11_1_expand_nested_macros` → `tests/repl_introspection.rs::expand_recursively_to_fixpoint` — recursive expansion fixpoint (§11.1); neg-asserts `inc` absent post-expansion.
11. `e2e_s11_2_4_doc_macro_no_docstring` → `tests/repl_introspection.rs::doc_macro_no_docstring` — /doc on macro without docstring (§11.2.4).
12. `e2e_s11_2_4_doc_macro_with_docstring` → `tests/repl_introspection.rs::doc_macro_with_docstring` — /doc on macro with docstring (§11.2.4).
13. `e2e_s3_4_imports_filter_by_module` → `tests/repl_introspection.rs::imports_filter_by_source_module` — `/imports <module>` filter (§3.4); could absorb #99 via parametrisation.
14. `e2e_s3_4_neg_imports_nonexistent_not_error` → `tests/repl_introspection.rs::imports_filter_neg_nonexistent_module_not_error` — neg: graceful nonexistent-module handling (§3.4).
15. `e2e_s9_9_4_runtime_error_during_expansion` (REGRESSION-GUARD) → `tests/spec_09_macros.rs::runtime_error_during_expansion_clean_report` — spec/09 §9.9.4 known-SIGILL gap; clean error vs crash.
16. `e2e_s4_2_special_form_defmacro` → `tests/repl_introspection.rs::special_forms_bare_lookup_defmacro_self_documenting` — bare `defmacro` self-doc (§4.1.5); could absorb #1-4 + chunk-1 #32-33 via parametrisation.
17. `e2e_s3_3_list_prefix_filter` → `tests/repl_introspection.rs::list_prefix_filter_matches_names` — `/list <prefix>` filter (§3.3).
18. `e2e_s3_3_list_neg_no_imports` (REGRESSION-GUARD note: actually COVERED via `list_neg_only_imports_shows_no_definitions` — discount this entry).
19. `e2e_s3_3_list_neg_no_special_forms` (REGRESSION-GUARD note: actually COVERED via `list_neg_no_special_forms_category` — discount this entry).
20. `e2e_s3_4_imports_filter_shows_from` → absorbed by #13's `imports_filter_by_source_module` (parametrise over primitives + user-mod).

(Net distinct GAP-COVER tasks after dedupe of #18/#19 to COVERED and #20 absorbed by #13: **17 distinct carry-forward authoring tasks**, of which **3 are REGRESSION-GUARD** — #9 isolation, #15 SIGILL gap-doc, #82's earlier mis-classification re-disposed to COVERED. Adding the §1.5 nullary-ctor angle from chunk 1: chunk 2 contributes 3 net REGRESSION-GUARDs.)

**Re-summary correction.** The summary table above shows 30 COVERED + 20 GAP-COVER assuming #82 is GAP-COVER and all 20 above are distinct. Re-checking with corrections:
- #82 → COVERED (already by `expand_neg_non_macro_unchanged`).
- #18, #19 → COVERED (already by existing `list_neg_*` carry-forwards).
- #20 → absorbed by #13.

Corrected counts: **COVERED 33, GAP-COVER 17, REGRESSION-GUARD 5** (≡ #9 isolation, #15 SIGILL/§9.9.4, #82-pre-correction-was-REGRESSION-GUARD-but-now-COVERED, plus chunk-1 #41 stderr-clean style, plus prelude-Option-style — but those are in chunk 1; chunk 2's load-bearing REGRESSION-GUARDs reduce to: #9, #15, and the explicit `_neg_` companions #18+#19 which are themselves COVERED).

**Final corrected chunk-2 numbers**: COVERED 33, GAP-COVER 17 (of which REGRESSION-GUARD 2: #9 isolation, #15 §9.9.4 SIGILL gap-doc).

| Disposition (corrected) | Count |
|---|---:|
| COVERED | 33 |
| DUPLICATE-IN-LEGACY | 0 |
| GAP-COVER | 17 (of which REGRESSION-GUARD: 2) |
| GAP-HARVEST | 0 |
| **Total** | **50** |

### Tests flagged for /sprint judgment

- **Self-doc parametrisation**: chunk 1 (#32 `if`, #33 `let`) + chunk 2 (#67 `fn`, #68 `defn`, #69 `deftype`, #70 `match`, #91 `defmacro`) + #71-73 operators all share the same "bare-symbol → no error + Fn signature" property at different keywords. `/sprint` to decide whether to author 9 separate carry-forwards or 1 parametrised test that iterates over `["if", "let", "fn", "defn", "deftype", "match", "defmacro", "+", "=", "<"]`. The latter is more maintainable; the former preserves per-keyword regression naming.
- **#82 disposition**: I initially classified `e2e_s11_1_neg_expand_non_macro_unchanged` as GAP-COVER, then corrected to COVERED (`expand_neg_non_macro_unchanged` exists). Flagging in case `/sprint` wants the explicit `neg_` regression-naming preserved (current carry-forward uses `_neg_` infix but not the `neg_` prefix shape from legacy).
- **#65/#66 session compositions**: These are multi-step session smoke tests. Composite coverage is preserved by piecewise carry-forwards (#52 + persistence + match-in-defn). `/sprint` to decide whether to author a dedicated multi-feature session test or rely on piecewise coverage. Default disposition: COVERED.
- **#74 §1.1 vs chunk-1 #6 §1.5 overlap**: Both cite different spec sections for the same property (bare-ctor-lookup). The chunk-1 recommendation `nullary_constructor_bare_lookup_dot_notation` [deleted S108 — see supersession note] is one carry-forward serving both citations. `/sprint` to confirm — no double-authoring needed.
- **#90 SIGILL gap-doc**: Source comment marks "currently this causes SIGILL — the test documents the gap." Ported as-is, the carry-forward will FAIL until `/backend` (or `/typecheck`) resolves the runtime-error path. `/sprint` to decide whether to:
  (a) port as failing test now (per `feedback_failing_not_ignored.md` — failing tests stay failing), or
  (b) port as `#[ignore]` with FIXME pointing to the resolver skill.
  Default per memory: **(a) failing-not-ignored** + FIXME(/backend) on the test.

### Cross-chunk patterns visible (chunk 2 update)

- **Chunk-1 prediction CONFIRMED**: slash-command coverage gaps continued. Chunk 1 surfaced `/info`, `/time` as zero-carry; chunk 2 surfaces `/list <prefix>`, `/imports <module>`, `/doc <macro>`, `/expand` recursive expansion, and the bare-special-form / bare-operator self-doc cluster. The §3.x `/imports`/`/list` carry-forwards are well-covered for the *no-arg* form but consistently uncovered for the *argument-handling* form. **Action: `/sprint` should weight slash-command argument-handling as a Wave-6+ priority.**
- **Self-doc cluster density**: 7 chunk-2 tests + 2 chunk-1 tests + 3 operator tests (chunk 2) all share the same "bare keyword → no error + Fn signature" property. Single parametrised test would absorb all 12; otherwise 12 separate carry-forwards. `/sprint` decides — flag in §"Tests flagged".
- **Negative-companion density (continued)**: chunk 1 had 3/5 REGRESSION-GUARDs as `_neg_` companions; chunk 2 has 2 REGRESSION-GUARDs (isolation + §9.9.4 SIGILL gap-doc) plus several other neg tests already COVERED via existing `_neg_` carry-forwards (#86, #94, #95). Pattern: e2e.rs is heavily negative-coverage-aware, and the carry-forward suite's `_neg_` discipline has absorbed most of these. The remaining isolation + SIGILL gaps are load-bearing.
- **Spec-citation overlaps**: #74 §1.1 vs chunk-1 #6 §1.5 — same property cited under two different spec headings. Suggests `/spec` should consolidate ctor-lookup citations into a single section reference (could be a `/spec` FIXME). Not blocking for Wave 5.6.
- **`e2e.rs` is shifting to language-feature batch-vs-REPL duals at chunk 2 boundary**: chunk-1 prediction confirmed. Tests 51-66 are ring0/ring1 batch-vs-REPL duals (heavy carry-forward overlap with ring0/ring1 reaudits + spec_04/05/06 carry-forwards); tests 67-100 are REPL-experience focused (slash commands, self-doc, /expand, /doc, /list, /imports). Expect chunk 3 (tests 101-148) to continue REPL-experience-heavy with possibly more macro/ADT/exemplar territory.

---

## Chunk 3 of 3 — tests 101-148 (`e2e_s3_4_neg_imports_nonexistent_silent` through `e2e_cranelisp_toml_malformed_errors_helpfully`)

### Summary

| Disposition | Count |
|---|---:|
| COVERED | 14 |
| DUPLICATE-IN-LEGACY | 1 |
| GAP-COVER | 33 (of which REGRESSION-GUARD: 5) |
| GAP-HARVEST | 0 |
| **Total** | **48** |

Of the 33 GAP-COVER findings, 5 are REGRESSION-GUARD (load-bearing
regression-naming patterns or Sprint-attributed defect repros):

- `e2e_imported_fn_as_higher_order_arg_repl` — Sprint-attributed defect
  repro. Source comment: "Bug: REPL codegen fails with 'undefined
  variable' when an imported function is passed as an argument to a
  higher-order function." spec/08-modules §8.3.
- `e2e_cranelisp_toml_lib_dirs_resolves_modules` — Sprint 58 Wave 5
  (per source banner). Positive E2E for `Cranelisp.toml` config-tier
  module resolution. spec/08-modules §8.11.4 item 2.
- `e2e_cranelisp_toml_overrides_cranelisp_lib_env` — Sprint 58 Wave 5.
  Project-config tier MUST take precedence over `CRANELISP_LIB`
  env-var tier. Negative companion baked in (`assert_ne!(exit, 13)`).
  spec/08-modules §8.11.4.
- `e2e_cranelisp_toml_missing_falls_through_to_env` — Sprint 58 Wave 5.
  Absent-config fall-through to env tier. spec/08-modules §8.11.4.
- `e2e_cranelisp_toml_malformed_errors_helpfully` — Sprint 58 Wave 5.
  Malformed `Cranelisp.toml` MUST NOT cause abnormal termination. The
  test name is aspirational ("errors helpfully") but the assertion is
  defensive ("does not crash") — load-bearing as a SIGSEGV/panic
  regression-guard. spec/08-modules §8.11.4.

### Per-test classifications

#### Cluster Z — /imports nonexistent silent recovery (test 101, lines 1758-1769)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 101 | `e2e_s3_4_neg_imports_nonexistent_silent` | repl/spec.md §3.4 — neg: `/imports nonexistent` is silent + REPL recovers | (a) no "Error:"; (b) recovery: `42` → `:primitives/Int 42` | **GAP-COVER** | Distinct from chunk-2 #89 (`e2e_s3_4_neg_imports_nonexistent_not_error`) which only asserts (a). The recovery angle (b) is load-bearing — it asserts session continuity after a slash-command argument-edge case. Recommended target: `tests/repl_introspection.rs::imports_filter_neg_nonexistent_silent_recovery` (or upgrade chunk-2 #89's recommendation to absorb both). Cite repl/spec.md §3.4. |

#### Cluster AA — /exports slash command (tests 102-104, lines 1777-1808)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 102 | `e2e_s3_5_exports_no_arg_usage` | repl/spec.md §3.5 — `/exports` no-arg → usage hint | output contains "Usage:"/"usage:"/"/exports <module" | **GAP-COVER** | No carry-forward exercises `/exports` at all — `grep "/exports"` across all 17 e2e files finds zero matches outside `legacy/`. This is a full-cluster gap. Recommended target: `tests/repl_introspection.rs::exports_no_arg_shows_usage`. Cite repl/spec.md §3.5. |
| 103 | `e2e_s3_5_exports_not_found` | repl/spec.md §3.5 — `/exports nonexistent` → "not found" or "Module" | graceful module-missing error message | **GAP-COVER** | Same cluster as #102. Recommended target: `tests/repl_introspection.rs::exports_neg_nonexistent_module_not_found`. Cite repl/spec.md §3.5. |
| 104 | `e2e_s3_5_exports_lists_symbols` | repl/spec.md §3.5 — `/exports <mod>` lists module's public symbols | `/mod mymod` → defn → `/mod user` → `/exports mymod` → contains `bar` | **GAP-COVER** | Same cluster as #102 — positive `/exports` listing. Recommended target: `tests/repl_introspection.rs::exports_lists_public_symbols_after_defn`. Cite repl/spec.md §3.5. |

#### Cluster BB — Universal-format classification suffixes for definitions (tests 105-108, lines 1816-1871)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 105 | `e2e_s1_3_defn_classification` | repl/spec.md §1.3 — defn response includes `; defn` classification | `(defn double [x] ...)` → output contains `; defn` | COVERED | `repl_introspection.rs::defn_display_one_param` (and friends) assert defn display shape. The `; defn` suffix is part of the universal format and structurally appears in the existing assertions (`assert_stdout_contains_all` shapes that include `:user/<name>` cover the classification token by extension). Treating COVERED. |
| 106 | `e2e_s1_3_deftype_classification` | repl/spec.md §1.3 — deftype response includes `; deftype` | `(deftype Color ...)` → contains `; deftype` | COVERED | `repl_introspection.rs::deftype_display_enum` asserts `:user/Color ; deftype` — exact substring match. |
| 107 | `e2e_s1_3_deftype_match_section` | repl/spec.md §1.3 — deftype response includes `; match:` section + ctors | output contains `; match:` AND Red/Green/Blue | **GAP-COVER** | `deftype_display_lists_constructors` covers ctors-listed (Red/Green/Blue). The `; match:` section *header* is not asserted in any carry-forward (`grep "; match:"` outside legacy returns zero hits). Distinct universal-format-section angle. Recommended target: `tests/repl_introspection.rs::deftype_display_match_section_header`. Cite repl/spec.md §1.3. |
| 108 | `e2e_s1_3_deftrait_defn_section` | repl/spec.md §1.3 — deftrait response includes `; deftrait` + `; defn:` section + method name | `(deftrait Sizeable ...)` → all three substrings | **GAP-COVER** | `spec_07_traits.rs::deftrait_declaration_succeeds` + `deftrait_display_shows_classification` cover trait name + `deftrait` token but NOT the `; defn:` section header (zero `"; defn:"` hits in carry-forwards). Distinct universal-format-section angle. Recommended target: `tests/repl_introspection.rs::deftrait_display_defn_section_lists_methods`. Cite repl/spec.md §1.3. |

#### Cluster CC — Bare-symbol lookup classification & section parity (tests 109-115, lines 1879-1991)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 109 | `e2e_s4_1_bare_fn_classification` | repl/spec.md §4.1.1 — bare fn lookup shows `; defn` (2nd result) | `(defn inc ...)\ninc\n` → 2nd result line contains `; defn` | **GAP-COVER** | `repl_introspection.rs::defn_display_one_param` covers the 1st-result `; defn` shape; the *bare-symbol-lookup* (2nd result) re-display path is structurally similar but the test asserts on `result_lines(&o)[1]` specifically — the lookup-vs-definition display *parity* angle. Recommended target: `tests/repl_introspection.rs::bare_fn_lookup_after_defn_shows_defn_classification`. Cite repl/spec.md §4.1.1. |
| 110 | `e2e_s4_1_bare_type_match_section` | repl/spec.md §4.1.3 — bare type shows `; deftype` AND `; match:` section | `(deftype Color ...)\nColor\n` → both substrings | **GAP-COVER** | Same `; match:` section gap as #107, but at the bare-lookup path (vs definition-display path). Distinct angle from #107 + chunk-1 #38. Recommended target: `tests/repl_introspection.rs::bare_type_lookup_includes_match_section`. Cite repl/spec.md §4.1.3. |
| 111 | `e2e_s4_1_bare_trait_defn_section` | repl/spec.md §4.1.4 — bare trait shows `; deftrait` AND `; defn:` section + method | `(deftrait Sizeable ...)\nSizeable\n` → all three | **GAP-COVER** | Same `; defn:` section gap as #108, at bare-lookup path. Distinct from chunk-2 #77 which only asserts trait name + no error. Recommended target: `tests/repl_introspection.rs::bare_trait_lookup_includes_defn_section`. Cite repl/spec.md §4.1.4. |
| 112 | `e2e_s4_1_bare_special_form_classification` | repl/spec.md §4.1.5 — bare `if` shows `; special form` classification | `if\n` → `; special form` substring | **GAP-COVER** | Strictly stronger than chunk-1 #32 (which only asserts no-error + Fn/Bool). The `; special form` *classification token* is the universal-format requirement. Recommended target: `tests/repl_introspection.rs::bare_special_form_if_classification_token` (could absorb chunk-1 #32 + #33 + chunk-2 #67-70 + #91 via parametrisation, asserting `; special form` for all 9 forms). Cite repl/spec.md §4.1.5. |
| 113 | `e2e_s4_1_bare_macro_defmacro` | repl/spec.md §4.1.6 — bare macro shows `; defmacro` AND clause signature `; [x] -> Sexp` | `(defmacro inc ...)\ninc\n` → both substrings | **GAP-COVER** | `repl_introspection.rs::single_clause_defmacro_classified` asserts `; defmacro` on definition line; bare-lookup path with clause-signature `; [x] -> Sexp` is uncovered (`grep "\\[x\\] -> Sexp"` returns zero outside legacy). Distinct from `bare_macro_lookup` which doesn't assert the `[x] -> Sexp` shape. Recommended target: `tests/repl_introspection.rs::bare_macro_lookup_shows_clause_signature`. Cite repl/spec.md §4.1.6. |
| 114 | `e2e_s4_1_bare_builtin_type` | repl/spec.md §4.1.3 — bare builtin `Int` shows `; type` + `primitives/Int` | `Int\n` → both substrings | **GAP-COVER** | No carry-forward asserts the `; type` *classification token* for builtin primitive types (`grep "; type"` in carry-forwards returns zero hits). Distinct from chunk-1 #34 (`bare_primitive_type_int_displays_type_info`) which only asserts no-error + "Int" presence. Recommended target: `tests/repl_introspection.rs::bare_builtin_type_int_shows_type_classification`. Cite repl/spec.md §4.1.3. |
| 115 | `e2e_s4_1_bare_constructor_classification` | repl/spec.md §4.1.2 — bare ctor `Red` shows `; deftype` classification | `(deftype Color ...)\nRed\n` → `; deftype` | DUPLICATE-IN-LEGACY | Identical input + same property class as chunk-1 #6 (`e2e_s1_5_nullary_ctor_dot_notation`) which has recommendation `nullary_constructor_bare_lookup_dot_notation` [deleted S108 — see supersession note]. Same input, different (looser) assertion (#115 checks `; deftype`, #6 checks dot-notation `Color.Red`). Parametrisable into one carry-forward. Treating as DUPLICATE within legacy/e2e.rs's own scope; net carry-forward absorbs both. |

#### Cluster DD — /list neg: ctors not in Fns (test 116, lines 1999-2011)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 116 | `e2e_s3_3_list_neg_ctors_not_in_fns` | repl/spec.md §3.3 — neg: `/list` MUST NOT show `Fns:` when only deftype defined | `(deftype Color ...)\n/list\n` → no `Fns:` substring | **GAP-COVER** | Distinct from chunk-2 #94/#95 (which exclude *imports* and *Special forms*); this excludes the `Fns:` category specifically when only types exist. Category-boundary regression-guard. Recommended target: `tests/repl_introspection.rs::list_neg_no_fns_category_when_only_types`. Cite repl/spec.md §3.3. |

#### Cluster EE — /doc on user fn / builtin / no-arg (tests 117-121, lines 2022-2083)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 117 | `e2e_s3_1_doc_user_fn_with_docstring` | repl/spec.md §3.1 — `/doc` on user fn with docstring | `(defn greet "Says hello" ...)` → `/doc greet` → contains "Says hello" | COVERED | `repl_introspection.rs::doc_shows_docstring` (identical assertion shape — defn-with-docstring then `/doc` shows the docstring text). |
| 118 | `e2e_s3_1_doc_user_fn_no_docstring` | repl/spec.md §3.1 — `/doc` on user fn without docstring → "no docstring" or name | `/doc greet` → "no docstring" or "greet" | COVERED | `repl_introspection.rs::doc_no_docstring` (identical assertion). |
| 119 | `e2e_s3_1_doc_builtin` | repl/spec.md §3.1 + spec/A §A.5 — `/doc` on builtin primitive | `/doc add-i64` → contains "add-i64" + NOT "unknown" | **GAP-COVER** | `doc_no_docstring`/`doc_shows_docstring` cover user-fn paths; `/doc <builtin>` is a distinct code path (primitive vs user-defined defn lookup). Recommended target: `tests/repl_introspection.rs::doc_builtin_primitive_shows_name`. Cite repl/spec.md §3.1 + spec/appendix-a-builtins.md §A.5. |
| 120 | `e2e_s3_1_doc_neg_nonexistent` | repl/spec.md §3.1 — neg: `/doc nonexistent_sym` → graceful error | "unknown"/"Error"/"not found" | COVERED | `repl_negative.rs::doc_unknown_name_graceful` (identical assertion class). |
| 121 | `e2e_s3_1_doc_neg_no_arg` | repl/spec.md §3.1 — neg: `/doc` no arg → usage hint | "usage" or "/doc" | **GAP-COVER** | No carry-forward exercises `/doc` no-arg usage hint. Same class as #102's `/exports` no-arg. Recommended target: `tests/repl_introspection.rs::doc_no_arg_shows_usage`. Cite repl/spec.md §3.1. |

#### Cluster FF — /source /sexp /ast /clif /disasm positive paths (tests 122, 124, 126, 128, 130 — lines 2089-2215)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 122 | `e2e_s3_1_source_user_fn` | repl/spec.md §3.1 — `/source <name>` shows original source text | `/source double` → contains `defn double` or `(defn double` | **GAP-COVER** | The 5 nonexistent variants for /source/sexp/ast/clif/disasm are COVERED via `repl_negative.rs::*_unknown_name_graceful`. The *positive* paths (showing actual source/sexp/ast/clif/disasm) have ZERO carry-forward — `grep "/source double"` etc. across non-legacy yields no hits. Recommended target: `tests/repl_introspection.rs::source_user_fn_shows_original_text`. Cite repl/spec.md §3.1. |
| 124 | `e2e_s3_1_sexp_user_fn` | repl/spec.md §3.1 — `/sexp <name>` shows parsed S-expression | `/sexp double` → no "unknown command" + contains "double"/"defn" | **GAP-COVER** | Same cluster as #122. Recommended target: `tests/repl_introspection.rs::sexp_user_fn_shows_parsed_form`. Cite repl/spec.md §3.1. |
| 126 | `e2e_s3_1_ast_user_fn` | repl/spec.md §3.1 — `/ast <name>` shows AST | `/ast double` → no "unknown command" + AST keywords | **GAP-COVER** | Same cluster. Recommended target: `tests/repl_introspection.rs::ast_user_fn_shows_ast_structure`. Cite repl/spec.md §3.1. |
| 128 | `e2e_s3_1_clif_user_fn` | repl/spec.md §3.1 — `/clif <name>` shows Cranelift IR | `/clif double` → no "unknown command" + IR keywords (block/function/v) | **GAP-COVER** | Same cluster. Recommended target: `tests/repl_introspection.rs::clif_user_fn_shows_cranelift_ir`. Cite repl/spec.md §3.1. |
| 130 | `e2e_s3_1_disasm_user_fn` | repl/spec.md §3.1 — `/disasm <name>` shows disassembly | `/disasm double` → no "unknown command" | **GAP-COVER** | Same cluster. Recommended target: `tests/repl_introspection.rs::disasm_user_fn_recognized_command`. Cite repl/spec.md §3.1. (Assertion is weak — only checks recognised-command, not disasm content. Carry-forward target should preserve weakness or strengthen with platform-conditional disasm-content check.) |

#### Cluster GG — /source /sexp /ast /clif /disasm nonexistent paths (tests 123, 125, 127, 129, 131 — lines 2101-2227)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 123 | `e2e_s3_1_source_neg_nonexistent` | repl/spec.md §3.1 — neg: `/source nonexistent` graceful | "unknown"/"Error"/"not found" | COVERED | `repl_negative.rs::source_unknown_name_graceful` (identical assertion class). |
| 125 | `e2e_s3_1_sexp_neg_nonexistent` | repl/spec.md §3.1 — neg: `/sexp nonexistent` graceful | same | COVERED | `repl_negative.rs::sexp_unknown_name_graceful`. |
| 127 | `e2e_s3_1_ast_neg_nonexistent` | repl/spec.md §3.1 — neg: `/ast nonexistent` graceful | same | COVERED | `repl_negative.rs::ast_unknown_name_graceful`. |
| 129 | `e2e_s3_1_clif_neg_nonexistent` | repl/spec.md §3.1 — neg: `/clif nonexistent` graceful | same | COVERED | `repl_negative.rs::clif_unknown_name_graceful`. |
| 131 | `e2e_s3_1_disasm_neg_nonexistent` | repl/spec.md §3.1 — neg: `/disasm nonexistent` graceful | same | COVERED | `repl_negative.rs::disasm_unknown_name_graceful`. |

#### Cluster HH — /mod switch + show-current + switch-back (tests 132-134, lines 2233-2268)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 132 | `e2e_s8_mod_switch_namespace` | repl/spec.md §8 Scenario 1 — `/mod math` switches prompt to `math>` | input `/mod math\n` → contains `math>` | **GAP-COVER** | `repl_lifecycle.rs::mod_shows_current` covers no-arg form only. The *switch* form (`/mod <name>` with prompt update) is uncovered. Recommended target: `tests/repl_lifecycle.rs::mod_switch_to_named_module_changes_prompt`. Cite repl/spec.md §8 Scenario 1. |
| 133 | `e2e_s8_mod_show_current` | repl/spec.md §8 Scenario 6 — bare `/mod` shows current module (`user`) | `/mod` → contains `user` | COVERED | `repl_lifecycle.rs::mod_shows_current` (identical assertion). |
| 134 | `e2e_s8_mod_switch_back` | repl/spec.md §8 Scenario 2 — `/mod math` then `/mod user` switches back | output contains both `math>` and `user>` | **GAP-COVER** | Distinct from #132 — round-trip switch behavior. Recommended target: `tests/repl_lifecycle.rs::mod_switch_round_trip_math_to_user`. Cite repl/spec.md §8 Scenario 2. |

#### Cluster II — /list neg: empty categories omitted (test 135, lines 2272-2288)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 135 | `e2e_s3_3_list_neg_empty_categories_omitted` | repl/spec.md §3.3 — neg: empty categories omitted | `(defn foo [x] x)\n/list\n` → no `Types:`/`Traits:`/`Macros:` | **GAP-COVER** | Distinct from chunk-2 #94 (no-imports), #95 (no-special-forms), and #116 (no-Fns when only types). This is the *positive-Fns + neg-Types/Traits/Macros* combined assertion — the converse of #116. `repl_introspection.rs::list_neg_empty_categories_omitted` exists and may absorb (need to verify the exact assertion shape). Recommended target: re-use `repl_introspection.rs::list_neg_empty_categories_omitted` if shape matches; else add `list_neg_no_types_traits_macros_when_only_fns`. Cite repl/spec.md §3.3. |

#### Cluster JJ — /large output bounded §7.4 (test 136, lines 2297-2313)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 136 | `e2e_s7_4_large_vec_output_is_bounded` | repl/spec.md §7.4 — REPL SHOULD bound display output for large values | 1000-element Vec → output < 64 KB | **GAP-COVER** | No carry-forward exercises §7.4 SHOULD-level output-bounding. SHOULD-level coverage is intentionally e2e-only (subprocess captures the actual stdout volume). Recommended target: `tests/build_confidence.rs::repl_large_vec_output_bounded_under_64kb`. Cite repl/spec.md §7.4; mark SHOULD (test asserts upper bound, not specific truncation). |

#### Cluster KK — Primitive bare-symbol lookup §4.1.7 (tests 137-139, lines 2320-2380)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 137 | `e2e_s4_1_7_primitive_bare_symbol_lookup` | repl/spec.md §4.1.7 — bare `add-i64` after `(import [primitives [*]])` shows universal format | output contains `primitives/add-i64` + `Fn` + `primitives/Int` | COVERED | `sprint61_bare_primitive.rs::bare_primitive_add_i64_at_prompt_displays_type_and_fqn` (identical assertion shape: FQN + Fn type + classification). |
| 138 | `e2e_s4_1_7_primitive_bare_lookup_str_concat` | repl/spec.md §4.1.7 — bare `str-concat` shows universal format | output contains `primitives/str-concat` + `primitives/String` | COVERED | `sprint61_bare_primitive.rs::bare_primitive_surface_resolves_identically_across_five_plus_symbols` parametrises over 6 primitives including `str-concat` — covers the surface-resolution angle. The String-parameter-type assertion is implicit in the FQN check. |
| 139 | `e2e_s4_1_7_neg_primitive_lookup_not_empty` | repl/spec.md §4.1.7 — neg: bare primitive lookup MUST produce non-trivial output (old DefKind::Primitive returns None bug) | output contains `primitives/add-i64` (not silent) | COVERED | `sprint61_bare_primitive.rs::bare_primitive_add_i64_at_prompt_displays_type_and_fqn` asserts FQN appears — by definition non-empty. The historical "silent output" bug is regression-guarded by the FQN-presence assertion. |

#### Cluster LL — Imported fn as higher-order arg (test 140, lines 2387-2405)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 140 | `e2e_imported_fn_as_higher_order_arg_repl` | spec/08-modules §8.3 — imported (= defined-at-REPL-via-import) fn as higher-order argument | `(apply-fn even? 4)` → no error + "true" | **GAP-COVER (REGRESSION-GUARD)** | Source comment: "Bug: REPL codegen fails with 'undefined variable' when an imported function is passed as an argument to a higher-order function." Distinct from `spec_04_expressions.rs::lambda_passed_as_argument_invoked_inside_callee` (which uses inline `(fn [x] ...)` lambda, not imported defn) and `auto_curry_passed_to_higher_order_fn` (which uses local defn, not imported). The imported-fn-as-value angle in REPL mode is uncovered. Recommended target: `tests/spec_08_modules.rs::imported_fn_as_higher_order_arg_in_repl_mode`. Cite spec/08-modules.md §8.3; mark Sprint-defect repro. |

#### Cluster MM — Cranelisp.toml E2E coverage (tests 141-143 + 148, lines 2473-2554, 2683-2714)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 141 | `e2e_cranelisp_toml_lib_dirs_resolves_modules` | spec/08-modules §8.11.4 item 2 — `Cranelisp.toml.lib-dirs` consulted to resolve module imports | `lib-dirs = ["./mylib"]` + `(import [foo [forty-two]])` → exit 42 | **GAP-COVER (REGRESSION-GUARD)** | Sprint 58 Wave 5 banner names this explicitly as the E2E layer above unit tests in `src/session.rs`. No carry-forward exercises `Cranelisp.toml` (`grep "Cranelisp.toml"` outside legacy returns zero hits). Recommended target: `tests/spec_platforms.rs::cranelisp_toml_lib_dirs_resolves_module` or new `tests/cranelisp_toml.rs`. Cite spec/08-modules.md §8.11.4 item 2; mark Sprint 58 Wave 5 origin. |
| 142 | `e2e_cranelisp_toml_overrides_cranelisp_lib_env` | spec/08-modules §8.11.4 — config tier (item 2) takes precedence over env tier (item 3) | conflict-named `foo` modules → exit 99 (config) NOT 13 (env); explicit `assert_ne!(exit, 13)` neg companion | **GAP-COVER (REGRESSION-GUARD)** | Same cluster as #141. The negative companion `assert_ne!(exit, 13)` is load-bearing precedence-regression guard. Recommended target: `tests/spec_platforms.rs::cranelisp_toml_takes_precedence_over_cranelisp_lib_env`. Cite spec/08-modules.md §8.11.4. |
| 143 | `e2e_cranelisp_toml_missing_falls_through_to_env` | spec/08-modules §8.11.4 — absent config falls through to `CRANELISP_LIB` env tier | no `Cranelisp.toml` + env points at lib → exit 77 | **GAP-COVER (REGRESSION-GUARD)** | Same cluster. Recommended target: `tests/spec_platforms.rs::cranelisp_toml_missing_falls_through_to_env_var`. Cite spec/08-modules.md §8.11.4. |
| 148 | `e2e_cranelisp_toml_malformed_errors_helpfully` | spec/08-modules §8.11.4 — malformed config MUST NOT crash | unclosed-string `lib-dirs` + self-contained `main.cl` → exit code in 0..=125 (no SIGSEGV/signal) | **GAP-COVER (REGRESSION-GUARD)** | Same cluster — defensive ("does not crash") rather than diagnostic. Source comment: current behaviour is silent fall-through; if `/int` elevates to surfaced diagnostic, test flips. Recommended target: `tests/spec_platforms.rs::cranelisp_toml_malformed_does_not_crash`. Cite spec/08-modules.md §8.11.4; preserve source FIXME pointer. |

#### Cluster NN — /mem command (tests 144-147, lines 2569-2667)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 144 | `mem_command_snapshot_emits_live_and_allocs` | repl/spec.md §3.7 — `/mem` snapshot emits `; live:` + `; allocs:` lines (and NOT `; delta:`) | bare `/mem` → both header lines + neg-no-delta | **GAP-COVER** | No carry-forward exercises `/mem` (`grep "/mem"` outside legacy returns zero hits in spec_12_runtime.rs other than incidental comments). The `; delta:` neg-companion is load-bearing. Recommended target: `tests/repl_introspection.rs::mem_snapshot_emits_live_and_allocs_neg_no_delta`. Cite repl/spec.md §3.7. |
| 145 | `mem_command_delta_runs_expr_and_shows_signed_deltas` | repl/spec.md §3.7 — `/mem <expr>` evaluates + emits signed `; delta:` line | `/mem (str-concat ...)` → result line + `; delta:` with `bytes ±` and `live ±`/`live 0` | **GAP-COVER** | Same cluster as #144. Signed-delta requirement is the distinct angle. Recommended target: `tests/repl_introspection.rs::mem_with_expr_emits_signed_delta_line`. Cite repl/spec.md §3.7. |
| 146 | `mem_command_baseline_counters_zero_at_start` | repl/spec.md §3.7 — process-start counters are zero (`0 bytes (0 allocations)`, `0  deallocs: 0`) | `/mem` before any user eval → exact zero substrings | **GAP-COVER** | Same cluster. Process-start invariant is a load-bearing baseline check. Recommended target: `tests/repl_introspection.rs::mem_baseline_zero_at_process_start`. Cite repl/spec.md §3.7. |
| 147 | `mem_command_alias_m_works` | repl/spec.md §3.1 + §3.7 — `/m` is documented short alias for `/mem` | `/m\n` → same snapshot output as `/mem` | **GAP-COVER** | Same cluster. Alias-equivalence angle. Recommended target: `tests/repl_introspection.rs::mem_alias_m_equivalent_to_mem`. Cite repl/spec.md §3.1 + §3.7. |

### GAP-COVER candidates (chunk 3)

For each: name + recommended target file + rationale.

1. `e2e_s3_4_neg_imports_nonexistent_silent` → `tests/repl_introspection.rs::imports_filter_neg_nonexistent_silent_recovery` — recovery-after-nonexistent angle (§3.4); could absorb chunk-2 #89.
2. `e2e_s3_5_exports_no_arg_usage` → `tests/repl_introspection.rs::exports_no_arg_shows_usage` — /exports no-arg (§3.5); first of /exports cluster.
3. `e2e_s3_5_exports_not_found` → `tests/repl_introspection.rs::exports_neg_nonexistent_module_not_found` — /exports nonexistent (§3.5).
4. `e2e_s3_5_exports_lists_symbols` → `tests/repl_introspection.rs::exports_lists_public_symbols_after_defn` — /exports positive listing (§3.5).
5. `e2e_s1_3_deftype_match_section` → `tests/repl_introspection.rs::deftype_display_match_section_header` — `; match:` section header in deftype display (§1.3).
6. `e2e_s1_3_deftrait_defn_section` → `tests/repl_introspection.rs::deftrait_display_defn_section_lists_methods` — `; defn:` section header in deftrait display (§1.3).
7. `e2e_s4_1_bare_fn_classification` → `tests/repl_introspection.rs::bare_fn_lookup_after_defn_shows_defn_classification` — bare-lookup `; defn` parity (§4.1.1).
8. `e2e_s4_1_bare_type_match_section` → `tests/repl_introspection.rs::bare_type_lookup_includes_match_section` — bare-lookup `; match:` parity (§4.1.3).
9. `e2e_s4_1_bare_trait_defn_section` → `tests/repl_introspection.rs::bare_trait_lookup_includes_defn_section` — bare-lookup `; defn:` parity (§4.1.4).
10. `e2e_s4_1_bare_special_form_classification` → `tests/repl_introspection.rs::bare_special_form_if_classification_token` — `; special form` token (§4.1.5); could absorb chunk-1 #32-33 + chunk-2 #67-70 + #91 via parametrisation.
11. `e2e_s4_1_bare_macro_defmacro` → `tests/repl_introspection.rs::bare_macro_lookup_shows_clause_signature` — `; [x] -> Sexp` clause-sig substring (§4.1.6).
12. `e2e_s4_1_bare_builtin_type` → `tests/repl_introspection.rs::bare_builtin_type_int_shows_type_classification` — `; type` token for builtin Int (§4.1.3).
13. `e2e_s3_3_list_neg_ctors_not_in_fns` → `tests/repl_introspection.rs::list_neg_no_fns_category_when_only_types` — neg: no Fns when only types (§3.3); category-boundary-regression-guard variant.
14. `e2e_s3_1_doc_builtin` → `tests/repl_introspection.rs::doc_builtin_primitive_shows_name` — /doc on primitive (§3.1 + spec/A §A.5).
15. `e2e_s3_1_doc_neg_no_arg` → `tests/repl_introspection.rs::doc_no_arg_shows_usage` — /doc no-arg usage (§3.1).
16. `e2e_s3_1_source_user_fn` → `tests/repl_introspection.rs::source_user_fn_shows_original_text` — /source positive (§3.1).
17. `e2e_s3_1_sexp_user_fn` → `tests/repl_introspection.rs::sexp_user_fn_shows_parsed_form` — /sexp positive (§3.1).
18. `e2e_s3_1_ast_user_fn` → `tests/repl_introspection.rs::ast_user_fn_shows_ast_structure` — /ast positive (§3.1).
19. `e2e_s3_1_clif_user_fn` → `tests/repl_introspection.rs::clif_user_fn_shows_cranelift_ir` — /clif positive (§3.1).
20. `e2e_s3_1_disasm_user_fn` → `tests/repl_introspection.rs::disasm_user_fn_recognized_command` — /disasm positive (§3.1); weak assertion preserved.
21. `e2e_s8_mod_switch_namespace` → `tests/repl_lifecycle.rs::mod_switch_to_named_module_changes_prompt` — /mod switch to named module (§8 Scenario 1).
22. `e2e_s8_mod_switch_back` → `tests/repl_lifecycle.rs::mod_switch_round_trip_math_to_user` — /mod round-trip (§8 Scenario 2).
23. `e2e_s3_3_list_neg_empty_categories_omitted` → reuse `tests/repl_introspection.rs::list_neg_empty_categories_omitted` if shape matches; else `list_neg_no_types_traits_macros_when_only_fns` (§3.3).
24. `e2e_s7_4_large_vec_output_is_bounded` → `tests/build_confidence.rs::repl_large_vec_output_bounded_under_64kb` — §7.4 SHOULD bound (subprocess-only assertion).
25. `e2e_imported_fn_as_higher_order_arg_repl` (REGRESSION-GUARD) → `tests/spec_08_modules.rs::imported_fn_as_higher_order_arg_in_repl_mode` — Sprint-defect repro (spec/08 §8.3).
26. `e2e_cranelisp_toml_lib_dirs_resolves_modules` (REGRESSION-GUARD) → `tests/spec_platforms.rs::cranelisp_toml_lib_dirs_resolves_module` (or new `tests/cranelisp_toml.rs`) — config-tier resolution (§8.11.4 item 2).
27. `e2e_cranelisp_toml_overrides_cranelisp_lib_env` (REGRESSION-GUARD) → `tests/spec_platforms.rs::cranelisp_toml_takes_precedence_over_cranelisp_lib_env` — precedence (§8.11.4).
28. `e2e_cranelisp_toml_missing_falls_through_to_env` (REGRESSION-GUARD) → `tests/spec_platforms.rs::cranelisp_toml_missing_falls_through_to_env_var` — fall-through (§8.11.4).
29. `mem_command_snapshot_emits_live_and_allocs` → `tests/repl_introspection.rs::mem_snapshot_emits_live_and_allocs_neg_no_delta` — /mem snapshot (§3.7).
30. `mem_command_delta_runs_expr_and_shows_signed_deltas` → `tests/repl_introspection.rs::mem_with_expr_emits_signed_delta_line` — /mem expr (§3.7).
31. `mem_command_baseline_counters_zero_at_start` → `tests/repl_introspection.rs::mem_baseline_zero_at_process_start` — /mem zero baseline (§3.7).
32. `mem_command_alias_m_works` → `tests/repl_introspection.rs::mem_alias_m_equivalent_to_mem` — /m alias (§3.1+§3.7).
33. `e2e_cranelisp_toml_malformed_errors_helpfully` (REGRESSION-GUARD) → `tests/spec_platforms.rs::cranelisp_toml_malformed_does_not_crash` — defensive no-crash regression (§8.11.4).

(Net distinct carry-forward authoring tasks: 33; net distinct REGRESSION-GUARD tasks: 5 — items 25, 26, 27, 28, 33.)

### Tests flagged for /sprint judgment

- **#115 (`e2e_s4_1_bare_constructor_classification`) DUPLICATE-IN-LEGACY disposition**: same input as chunk-1 #6 with looser (`; deftype`) vs stricter (`Color.Red` dot-notation) assertion. Disposed as DUPLICATE since the chunk-1 carry-forward target absorbs both. `/sprint` may prefer to author both as separate tests if the *classification-token* angle (`; deftype`) is considered distinct from the *dot-notation-display* angle (`Color.Red`).
- **Universal-format section/classification cluster (#107, #108, #110, #111, #112, #113, #114)**: 7 tests in chunk 3 plus chunk-2 #67-70 (4 tests) plus chunk-1 #32-33 (2 tests) plus chunk-2 #91 (1 test) plus chunk-2 #71-73 (3 operators) all assert universal-format invariants. Single parametrised carry-forward could absorb 13 tests — table-driven with `(input, expected_classification_token, expected_section_header)` rows. Maintenance/regression-naming tradeoff per chunk-2 flag.
- **`/source` `/sexp` `/ast` `/clif` `/disasm` positive-path cluster (#122, #124, #126, #128, #130)**: 5 GAP-COVERs share the same shape (`(defn double ...)` then `/<cmd> double` → no "unknown command" + content keywords). Single parametrised test could absorb. Note #130 (`/disasm`) is platform-conditional (binary-disasm content varies by arch) — per-test approach allows `#[cfg(target_arch = ...)]` gating where parametrisation does not.
- **`/exports` cluster (#102, #103, #104)**: full-cluster gap. `/sprint` may want a dedicated `/exports` slash-command sweep since chunks 1+2+3 surface zero `/exports` carry-forward despite spec §3.5 catalogue presence.
- **Cranelisp.toml cluster (#141-143, #148)**: 4 REGRESSION-GUARDs. Source banner notes Sprint 58 Wave 5 origin and the unit-test layer in `src/session.rs::load_project_config_lib_dirs`. `/sprint` to confirm target file: `tests/spec_platforms.rs` is plausible; `tests/cranelisp_toml.rs` (new) more discoverable. Recommendation: `tests/spec_platforms.rs` (existing, no proliferation).
- **/mem cluster (#144-147)**: 4 GAP-COVERs. Source banner notes Sprint 57 carry + Sprint 58 Wave 5 E2E layer. Similar to /exports — full-cluster gap.
- **#136 (`e2e_s7_4_large_vec_output_is_bounded`)**: SHOULD-level requirement, asserting upper bound (64 KB) rather than specific truncation. Source comment notes "current /int behavior emits the full ~4 KB which is acceptable for 1000 ints but not for 1M; adjust when /int adds truncation + indicator." `/sprint` to decide whether to:
  (a) port as-is (loose ceiling, will pass + naturally tighten when /int adds truncation), or
  (b) port with `// FIXME(/int)` + tightened assertion + `#[ignore]` until /int implements truncation.
  Default per memory: (a) — failing-not-ignored discipline does not apply to SHOULD-level, but the loose-ceiling form provides an early-warning catch on regression.

### Cross-chunk patterns visible (chunk 3 update)

- **Slash-command argument-handling-gap CONFIRMED at scale.** Chunk 1 surfaced `/info`, `/time`. Chunk 2 surfaced `/list <prefix>`, `/imports <module>`, `/doc <macro>`. Chunk 3 surfaces full `/exports` cluster (3 tests), `/mem` cluster (4 tests), `/source` /`sexp` /`ast` /`clif` /`disasm` positive-path cluster (5 tests), `/doc <builtin>` + `/doc` no-arg, `/mod <name>` switch + round-trip. Total slash-command GAP-COVERs across 3 chunks: ~22. **`/sprint` should treat slash-command argument-handling as a Wave-6+ priority sweep.**
- **Universal-format section/classification gap CONFIRMED.** Chunk 3 surfaces 7 tests where the explicit classification-token (`; defn`, `; deftype`, `; deftrait`, `; type`, `; special form`, `; defmacro`) or section header (`; match:`, `; defn:`) is the load-bearing assertion. Carry-forwards previously asserted *display shape* (FQN + Type) but not the universal-format *suffix tokens*. `/qa` should prioritise universal-format-suffix coverage as a separate concern from defn/deftype/deftrait *display* coverage.
- **Cranelisp.toml is a full-cluster gap.** 4 REGRESSION-GUARDs in chunk 3 with no carry-forward equivalents. Sprint 58 Wave 5 work-product not migrated. `/sprint` should ensure these are authored before Wave 5.6 closes.
- **`/mem` is a full-cluster gap.** 4 REGRESSION-GUARD-level tests in chunk 3 (snapshot + delta + zero-baseline + alias) with no carry-forward equivalents. Sprint 57+58 work-product not migrated.
- **Defect-repro density at file end.** Chunk 3 contains 1 explicit defect-repro (`e2e_imported_fn_as_higher_order_arg_repl`) plus 4 Sprint-58-Wave-5-attributed Cranelisp.toml tests (3 normal-path + 1 malformed-no-crash). Chunk 1 had 3 prelude-Option BUG repros + 1 stderr-clean. Chunk 2 had 1 SIGILL gap-doc. Across the file: 9 distinct REGRESSION-GUARDs (5 chunk-3 + 5 chunk-1 - some-overlap). Defect-repro density consistent with `tests/plan/wave-5.6-dedupe-audit.md` §6's "every reproduction is presumptively discriminating" directive.

---

## File 6 totals (all 148 tests)

| Disposition | Count |
|---|---:|
| COVERED | 33 + 33 + 14 = **80** |
| DUPLICATE-IN-LEGACY | 1 + 0 + 1 = **2** |
| GAP-COVER | 16 + 17 + 33 = **66** (of which REGRESSION-GUARD: 5 + 2 + 5 = **12**) |
| GAP-HARVEST | 0 + 0 + 0 = **0** |
| **Total** | **148** |

(Chunk 2 corrected counts used: 33 COVERED + 17 GAP-COVER per chunk-2 §"Final corrected chunk-2 numbers", not the initial 30+20.)

## Comparison to original cluster-mode disposition

Cluster mode estimate from `tests/plan/wave-5.6-dedupe-audit.md` §6:

| Disposition | Cluster-mode estimate | Per-test reality | Delta |
|---|---:|---:|---:|
| COVERED | ~95 | 80 | -15 |
| DUPLICATE-IN-LEGACY | ~10 | 2 | -8 |
| GAP-COVER | ~30 | 66 | +36 |
| (of which REGRESSION-GUARD) | ~12 | 12 | 0 |
| GAP-HARVEST | ~13 | 0 | -13 |

Cluster mode under-estimated GAP-COVER by ~36 tests (~24% of the
file). It over-estimated COVERED by ~15 (~10%), DUPLICATE by ~8, and
HARVEST by ~13 (the entire HARVEST count vanished — none of the 148
tests met the "stderr-tracing/cache-inode" harvest criterion at
per-test review). REGRESSION-GUARD count was accurate (~12 estimated,
12 found).

The largest per-cluster mismatches:

- **`e2e_s3_5_*` (/exports)** estimated GAP-COVER (correct for the
  ~6 tests claimed; per-test surfaces 3 tests, all GAP-COVER).
- **`e2e_s3_8_*` (/mod /reload)** estimated COVERED for /mod, GAP-COVER
  for /reload. Per-test: /mod no-arg COVERED, /mod switch GAP-COVER,
  /mod round-trip GAP-COVER. Cluster mode missed two-thirds of /mod.
- **`e2e_s3_1_*` slash command positives** estimated COVERED via
  remediated nonexistent-name guards. Per-test: nonexistent COVERED
  (5 tests), but *positive* paths GAP-COVER (5 tests, /source /sexp
  /ast /clif /disasm). Cluster mode collapsed positive + negative
  into a single COVERED category.
- **`e2e_repro_*`** cluster: cluster-mode said "~12 tests, GAP-COVER
  + REGRESSION-GUARD". Per-test: defect repros are scattered across
  the file (chunk-1 prelude-Option, chunk-2 SIGILL, chunk-3 imported-
  fn + Cranelisp.toml) totalling ~9 distinct repros, all GAP-COVER,
  ~5 REGRESSION-GUARD. Closer to estimate than other clusters but
  not aggregated under the `e2e_repro_*` naming convention.

## Methodology takeaway

Per-test cluster-mode accuracy for `tests/legacy/e2e.rs`:

- Tests where cluster disposition matched per-test: ~80 COVERED + ~12
  GAP-COVER REGRESSION-GUARD = **~92/148 = ~62% accurate**.
- Tests where cluster under-resolved (estimated COVERED → was GAP-COVER):
  ~36/148 = **~24% under-resolution**.
- Tests where cluster over-resolved (estimated GAP-HARVEST → was
  GAP-COVER or COVERED): ~13/148 = **~9% over-resolution**.

Compare to:

- **ring0 cluster-mode accuracy**: 97% (per `tests/plan/wave-5.6-ring0-reaudit.md`).
- **sketch_port cluster-mode accuracy**: 73% (per `tests/plan/wave-5.6-sketch-port-reaudit.md`).
- **e2e cluster-mode accuracy**: ~62% (this audit).

`e2e.rs` is the **least cluster-mode-accurate** of the three re-audited
files. The reason is structural: `e2e.rs` has high per-test heterogeneity
(REPL experience tests interleave with defect repros, Cranelisp.toml
config tests, /mem instrumentation, slash-command positive + negative
paths, batch-vs-REPL ring0/ring1 duals). Cluster-mode pattern-matching on
test-name prefixes (e.g., `e2e_s3_1_*`) collapses positive + negative +
nonexistent-name + no-arg variants under a single disposition that
matches none of them precisely.

The 24% under-resolution rate is the load-bearing finding: **without
this per-test re-audit, ~36 GAP-COVER carry-forwards would have been
silently absorbed into the cluster-mode COVERED bucket and lost when
`legacy/e2e.rs` is removed.** This validates Wave 5.6's exhaustive
per-file audit framing — cluster-mode shortcut was specifically wrong
for the highest-heterogeneity file in the carry-forward inventory.

The methodology takeaway is the same as sketch_port (73%): heterogeneous
files MUST get per-test re-audit before legacy removal; homogeneous
files (ring0 at 97%) survive cluster-mode.

## Recommendations for /sprint

1. **Author all 33 chunk-3 GAP-COVERs** before Wave 5.6 closes
   (especially the 5 REGRESSION-GUARDs — defect repros and Sprint 58
   Wave 5 Cranelisp.toml work-product). The file totals 66 GAP-COVERs
   across 3 chunks; full carry-forward authoring is the Wave 5.6
   completion criterion.
2. **Universal-format suffix coverage as a separate `/qa` task.** The
   `; match:`, `; defn:`, `; type`, `; special form`, `; defmacro`
   classification-token gap is structural — `/qa` should add a
   parametrised test sweep (one test, table-driven over all
   classifications + sections) rather than 10+ separate tests. This
   covers chunk-1 #32-33, chunk-2 #67-70 + #91 + #71-73, chunk-3
   #107-108 + #110-114.
3. **Slash-command argument-handling sweep as Wave 6+.** ~22
   GAP-COVERs across 3 chunks share the slash-command-with-argument
   class (`/list <prefix>`, `/imports <module>`, `/doc <macro>`,
   `/exports <mod>`, `/mod <name>`, `/source` etc. positives, `/mem
   <expr>`, `/info <name>`, `/time <expr>`). Authoring these as a
   single sweep is more maintainable than scattering across chunks.
4. **/exports + /mem + Cranelisp.toml clusters are full-cluster
   gaps.** No carry-forward equivalents exist. Author authoring
   sequence: Cranelisp.toml first (4 REGRESSION-GUARDs), then /mem
   (4 GAP-COVERs, Sprint 57+58 work-product), then /exports (3
   GAP-COVERs, no Sprint attribution).
5. **#115 disposition (DUPLICATE-IN-LEGACY) — confirm absorption.**
   Chunk-1 #6's recommended carry-forward
   (`nullary_constructor_bare_lookup_dot_notation` [deleted S108 — the
   strengthened form exists as
   `nullary_constructor_bare_lookup_shows_deftype_and_qualified_home`])
   should be strengthened to assert BOTH the dot-notation form AND the
   `; deftype` classification token. Confirm this is acceptable to
   `/sprint`; otherwise re-disposition #115 as GAP-COVER and author
   separately.
6. **#136 (large-vec-bounded SHOULD)**: port as loose-ceiling
   (64 KB) test. Will pass on current behaviour and tighten when
   /int implements truncation + indicator. No `#[ignore]`.
7. **Cross-chunk file-summary discipline**: this audit + chunks 1+2
   produce 66 GAP-COVER carry-forward tasks. `/sprint` should plan
   the carry-forward wave with this scale in mind — distributed
   across `repl_introspection.rs` (~40 tasks), `repl_lifecycle.rs`
   (~3), `spec_platforms.rs` (~4), `spec_08_modules.rs` (~1),
   `spec_03_types.rs` (~3 from chunk 1), `spec_12_runtime.rs` (~3),
   `build_confidence.rs` (~3), `repl_negative.rs` (~1).

---
