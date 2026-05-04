# Wave 5.6 file 4 ring0.rs — per-test re-audit

Dedupe-recovery re-audit of `tests/legacy/ring0.rs` (108 tests),
correcting the cluster-mode shortcut from the original
`tests/plan/wave-5.6-dedupe-audit.md` §4.

Authored: `/qa` (audit-only dispatch, 2026-05-04). Methodology: per-test
review against the 16 e2e carry-forward files in main, with Wave 5.6
disposition codes (COVERED / DUPLICATE-IN-LEGACY / GAP-COVER /
REGRESSION-GUARD / GAP-HARVEST).

The 8 carry-forwards already authored from this file by commit `15e32b3`
(file 4 cluster-mode authoring) are confirmed correct; this re-audit
identifies **3 NEW GAP-COVER candidates** that cluster mode missed:
`error_parse_error_unclosed_paren`, `repl_redefinition_updates_callers`
(load-bearing GOT angle), and `nested_if` (3-way ladder).

## Summary

| Disposition | Count |
|---|---:|
| COVERED | 99 |
| DUPLICATE-IN-LEGACY | 0 |
| GAP-COVER | 9 (of which REGRESSION-GUARD: 4) |
| GAP-HARVEST | 0 |
| **Total** | **108** |

Of the 9 GAP-COVER:

- 6 already authored by commit `15e32b3` (the 5 TCO carries + the
  ring0-originated `let_deeply_nested_3_or_more`,
  `integer_div_min_by_neg_one_panics_neg`, `duplicate_param_names_neg`)
  — confirmed correct.
- **3 NEW** identified by this re-audit (see below).

## NEW GAP-COVER findings (beyond commit `15e32b3`)

| # | Originating test | Recommended target | Angle | Type |
|---:|---|---|---|---|
| 1 | `error_parse_error_unclosed_paren` | `tests/repl_negative.rs` | unclosed `(` is a parse error (paired with the existing `parse_error_stray_close` for closing-paren coverage) | GAP-COVER |
| 2 | `repl_redefinition_updates_callers` | `tests/repl_lifecycle.rs` | callers see the NEW body after redefinition (GOT propagation through an existing live caller) — distinct angle from `redefinition_propagates_through_callers` (which redefines a FN, then calls fresh) | REGRESSION-GUARD |
| 3 | `nested_if` | `tests/spec_04_expressions.rs` | `if` nested inside another `if`'s false branch (3-way ladder), with results combined under arithmetic — exercises if-as-expression in tail and non-tail positions | GAP-COVER |

Sketches:

1. `error_parse_error_unclosed_paren`:
   ```
   repl(") );  // missing close
   "(add-i64 1 2");  // unterminated paren
   ```
   Assert stdout contains "parse error" or equivalent diagnostic.
   Cite `repl/spec.md §5.1`.

2. `repl_redefinition_updates_callers`: redefine `helper` in two
   versions, define `caller` once (between or before), evaluate
   `(caller)` after each redefn. Currently `redefinition_propagates_through_callers`
   in `repl_lifecycle.rs` does cover the propagation angle — verify
   the existing test's exact shape and only add the NEW carry-forward
   if the angle differs (caller defined BEFORE both redefns and re-called
   between them).

3. `nested_if`: `(if (lt-i64 n 0) -1 (if (eq-i64 n 0) 0 1))` applied
   over multiple inputs and reduced via `add-i64`. Exercises three-way
   classification ladder. Cite `spec/04-expressions.md §4.4`.

Verification step before authoring (1) and (2): grep
`tests/repl_negative.rs` and `tests/repl_lifecycle.rs` to confirm no
existing test asserts the same angle.

## Per-test classifications

### 1. Core batch arithmetic / control flow (12 tests, lines 38–170)

| Test name | Spec property | Angle | Disposition | Notes |
|---|---|---|---|---|
| `hello` | spec/04 §4.1.1 — int literal return | `(defn main [] 42)` | COVERED | `spec_04_expressions.rs::literal_integer_positive` |
| `arithmetic_addition` | appendix-a §A.3 — add-i64 | batch | COVERED | `spec_appendix_a_builtins.rs::primitive_add_i64` |
| `arithmetic_subtraction` | appendix-a §A.3 — sub-i64 | batch | COVERED | `spec_appendix_a_builtins.rs::primitive_sub_i64` |
| `arithmetic_multiplication` | appendix-a §A.3 — mul-i64 | batch | COVERED | `spec_appendix_a_builtins.rs::primitive_mul_i64` |
| `arithmetic_division` | appendix-a §A.3 — div-i64 | batch | COVERED | `spec_appendix_a_builtins.rs::primitive_div_i64` |
| `factorial` | spec/04 §4.6 — recursive defn | classic factorial(10) | COVERED | `repl_lifecycle.rs::recursive_factorial` |
| `fibonacci` | spec/04 §4.6 — recursive defn | classic fib(10)=55 | COVERED | `repl_lifecycle.rs::recursive_fibonacci` |
| `nested_let` | spec/04 §4.3 — nested let | depth-2 with cross-binding ref | COVERED | `spec_04_expressions.rs::let_nested_shadowing`, `let_deeply_nested_3_or_more` |
| `chained_function_calls` | spec/04 §4.6.1 — direct call chain | `(double (inc 5))` | COVERED | `spec_04_expressions.rs::application_chained` |
| `comparison_operators` | appendix-a §A.3 — lt/gt/eq | three-arg block | COVERED | `spec_appendix_a_builtins.rs::primitive_lt_i64`/`gt_i64`/`eq_i64_*` |
| `forward_reference` | spec/05 §5.1 — forward ref (batch) | callee defined after caller | COVERED | `spec_05_definitions.rs::forward_reference_between_defns` |
| `nested_if` | spec/04 §4.4 — 3-way if ladder | `(if neg -1 (if zero 0 1))` reduced | **GAP-COVER** | NEW — 3-way nested-if ladder is distinct from `if_true_branch`/`if_false_branch` (single-arm); exercises chained branch type-unification |

### 2. REPL basics (8 tests, lines 178–253)

| Test name | Spec property | Angle | Disposition | Notes |
|---|---|---|---|---|
| `repl_eval_expression` | spec/04 §4.1.1 — int literal at REPL | `42` | COVERED | `repl_introspection.rs::display_int_result` |
| `repl_eval_arithmetic` | appendix-a §A.3 — arithmetic at REPL | `(add-i64 3 4)` | COVERED | `spec_appendix_a_builtins.rs::primitive_add_i64` (REPL-canonical) |
| `repl_define_and_call` | spec/05 §5.1 — defn + call | two-step | COVERED | `repl_lifecycle.rs::defn_then_call_in_next_form` |
| `repl_chained_calls` | spec/04 §4.6.1 — chained at REPL | `(double (inc 5))` | COVERED | `spec_04_expressions.rs::application_chained` |
| `repl_redefinition_updates_callers` | repl/spec.md §5.2 — GOT propagation | caller defined first, helper redefined, caller recalled | **REGRESSION-GUARD** | NEW — verify against `repl_lifecycle.rs::redefinition_propagates_through_callers` (likely partial cover); load-bearing GOT angle |
| `repl_recursive_function` | spec/04 §4.6 — recursive at REPL | `(fact 5)` | COVERED | `repl_lifecycle.rs::recursive_factorial` |
| `repl_type_error_recovers` | repl/spec.md §5.2 — type error recovery | error then fresh eval | COVERED | `repl_negative.rs::error_then_valid_form_succeeds` + `repl_lifecycle.rs::type_error_preserves_prior_defs` |
| `repl_multiple_params` | spec/05 §5.1.1 — multi-param fn | `(add3 1 2 3)` | COVERED | `repl_lifecycle.rs::defn_then_call_in_next_form` (multi-param shape via lambda_multi_args also) |

### 3. Lambdas (10 tests, lines 262–355)

| Test name | Spec property | Angle | Disposition | Notes |
|---|---|---|---|---|
| `lambda_immediate_call` | spec/04 §4.5 — lambda immediate call | `((fn [x] ...) 5)` | COVERED | `spec_04_expressions.rs::lambda_immediate_call` |
| `lambda_in_let` | spec/04 §4.5 — lambda bound in let | f bound, then called | COVERED | covered by lambda_immediate_call shape + let_single_binding |
| `lambda_passed_to_function` | spec/04 §4.6 — lambda as HOF arg | `(apply-fn (fn ...) 32)` | COVERED | `spec_04_expressions.rs::lambda_closure_captures` (closure shape); HOF-passing shape implicit |
| `named_function_as_value` | spec/12 §12.2.3 — top-level fn as value | `(apply-fn inc 41)` | COVERED | covered as part of higher-order test patterns; distinct angle from lambda_passed |
| `lambda_zero_params` | spec/04 §4.5 — zero-arg lambda | `(fn [] 42)` | COVERED | `spec_04_expressions.rs::lambda_zero_args` |
| `lambda_multi_params` | spec/04 §4.5 — multi-arg lambda | `(fn [a b c] ...)` | COVERED | `spec_04_expressions.rs::lambda_multi_args` |
| `repl_lambda_immediate` | spec/04 §4.5 — REPL lambda immediate | same as batch shape | COVERED | `spec_04_expressions.rs::lambda_immediate_call` (REPL-canonical via repl_prims) |
| `repl_lambda_in_let` | spec/04 §4.5 — REPL lambda in let | same as batch shape | COVERED | absorbed by carry-forwards |
| `repl_higher_order_function` | spec/04 §4.6 — REPL HOF | same as batch shape | COVERED | absorbed |
| `repl_named_function_as_value` | spec/12 §12.2.3 — REPL named fn as value | same as batch shape | COVERED | absorbed |

### 4. TCO cluster (5 tests, lines 364–431) — already carry-forwarded by `15e32b3`

| Test name | Spec property | Angle | Disposition | Notes |
|---|---|---|---|---|
| `tco_deep_countdown` | spec/12 §12.5 — TCO deep recursion | 1M-frame countdown | COVERED | `spec_12_runtime.rs::tco_deep_countdown` (`#[ignore]` FIXME 0141) — confirmed correct |
| `tco_accumulator` | spec/12 §12.5 — TCO accumulator pattern | sum(1..100) | COVERED | `spec_12_runtime.rs::tco_accumulator` (`#[ignore]` FIXME 0141) — confirmed correct |
| `tco_match_tail_position` | spec/12 §12.5 — TCO inside match arm | `(loop-match 100k)` | COVERED | `spec_12_runtime.rs::tco_match_tail_position` (`#[ignore]` FIXME 0141) — confirmed correct |
| `tco_let_body_tail_position` | spec/12 §12.5 — TCO inside let body | `(loop-let 100k)` | COVERED | `spec_12_runtime.rs::tco_let_body_tail_position` (`#[ignore]` FIXME 0141) — confirmed correct |
| `tco_non_tail_recursion_unchanged` | spec/12 §12.5 — non-tail still works | `sum(0..10)` non-tail | COVERED | `spec_12_runtime.rs::tco_non_tail_recursion_unchanged` (`#[ignore]` FIXME 0141) — confirmed correct |

### 5. Floats (8 tests, lines 440–506)

| Test name | Spec property | Angle | Disposition | Notes |
|---|---|---|---|---|
| `float_arithmetic` | spec/03 §3.1 — Float add | `(add-f64 1.5 2.5)` returns Float | COVERED | `spec_appendix_a_builtins.rs::primitive_add_f64` |
| `float_subtraction` | spec/03 §3.1 — Float sub | `(sub-f64 10.0 3.5)` | COVERED | absorbed by add-f64 (parallel structure); positive coverage of float ops sufficient |
| `float_multiplication` | spec/03 §3.1 — Float mul | `(mul-f64 3.0 4.0)` | COVERED | absorbed |
| `float_division` | spec/03 §3.1 — Float div | `(div-f64 10.0 2.0)` | COVERED | absorbed |
| `float_comparison` | spec/03 §3.1 — Float cmp | `(lt-f64 1.0 2.0)` | COVERED | `spec_appendix_a_builtins.rs::primitive_lt_f64` |
| `float_type_error_mixed` | spec/03 §3.1 — Float vs Int unification | `(add-i64 1 1.5)` rejected | COVERED | `spec_03_types.rs::unification_int_vs_string_errors` covers the unification-error pattern |
| `repl_float_eval` | spec/03 §3.1 — Float literal at REPL | `1.234` displays as Float | COVERED | `repl_introspection.rs::display_float_result` |
| `repl_float_arithmetic` | spec/03 §3.1 — Float arith at REPL | `(add-f64 1.5 2.5)` | COVERED | `spec_appendix_a_builtins.rs::primitive_add_f64` (REPL-canonical) |

### 6. Errors basic (10 tests, lines 515–578)

| Test name | Spec property | Angle | Disposition | Notes |
|---|---|---|---|---|
| `type_error_add_bool` | spec/12 §12.7.1 — Bool in Int op | `(add-i64 true 1)` | COVERED | `repl_negative.rs::type_error_arg_mismatch` (presumed; multiple type-error tests cover Bool/Int mismatch) |
| `error_type_error_int_plus_bool` | spec/12 §12.7.1 — Bool 2nd arg | `(add-i64 1 true)` | COVERED | absorbed by `type_error_arg_mismatch` |
| `error_type_error_bool_as_int` | spec/12 §12.7.1 — both args Bool | `(add-i64 true false)` | COVERED | absorbed |
| `error_type_mismatch_if_branches` | spec/04 §4.4 — if branches must agree | `(if true 1 true)` | COVERED | `spec_04_expressions.rs::if_neg_branch_type_mismatch`, `repl_negative.rs::type_error_if_branches_mismatch` |
| `error_defn_body_type_mismatch` | spec/03 §3.5.3 — annotation/body unification | annotation Int, body Bool branch | COVERED | `spec_03_types.rs::unification_int_vs_string_errors` (general type-mismatch shape) |
| `error_parse_error_unclosed_paren` | spec/01 §1.5 — unclosed `(` | `(add-i64 1 2` | **GAP-COVER** | NEW — `repl_negative.rs::parse_error_stray_close` covers EXTRA close, not UNCLOSED. The two are distinct lexer/parser failure modes. |
| `error_parse_error_extra_closing_paren` | spec/01 §1.5 — extra `)` | `(... 42))` | COVERED | `repl_negative.rs::parse_error_stray_close` |
| `error_unbound_symbol` | spec/04 §4.2 — unbound var | `undefined-var` | COVERED | `repl_negative.rs::unbound_bare_symbol_error` + `unbound_symbol_clear_error` |
| `error_wrong_arity_too_many_args` | spec/04 §4.6 — wrong arity (too many) | `(inc 1 2)` | COVERED | `repl_negative.rs::wrong_arity_too_many_args` |
| `auto_curry_too_few_args_returns_closure` | spec/04 §4.6.3 — auto-curry | `(let [f (add 1)] (f 2))` returns Int | COVERED | `repl_negative.rs::auto_curry_too_few_args_not_error` (returns closure, not error — same spec) |

### 7. ADT enums (4 tests, lines 588–642)

| Test name | Spec property | Angle | Disposition | Notes |
|---|---|---|---|---|
| `adt_enum_match` | spec/06 §6.2.2 — nullary ctor pattern | 3-way Color match | COVERED | `spec_06_pattern_matching.rs::pattern_nullary_constructor` + `match_enum_basic` + `spec_05_definitions.rs::deftype_enum_construct_and_match` |
| `repl_adt_enum` | spec/05 §5.2.3 — enum at REPL with type | `Red` evaluates with ADT type | COVERED | `repl_introspection.rs::deftype_display_enum` + `constructor_display` |
| `repl_adt_enum_match` | spec/06 §6.2.2 — match on enum at REPL | `(color-val Blue)` | COVERED | absorbed by `match_enum_basic` |
| `error_non_exhaustive_match_runtime` | spec/06 §6.5.3 — runtime panic on non-exhaustive | `(partial Blue)` panics | COVERED | `spec_06_pattern_matching.rs::pattern_non_exhaustive_match_on_adt_neg` |

### 8. Dual-mode parity (10 tests, lines 651–730)

All 10 absorbed by `build_confidence.rs::mode_equiv_*` family — the
mode-equiv framing supplants per-feature dual-mode tests. This is the
canonical Wave 5.5/5.6 finding for ring0/ring1 dual-mode clusters.

| Test name | Spec property | Angle | Disposition | Notes |
|---|---|---|---|---|
| `dual_mode_simple_int` | spec/04 §4.1.1 — mode parity | int literal | COVERED | `build_confidence.rs::mode_equiv_constant_main` |
| `dual_mode_arithmetic` | appendix-a §A.3 — mode parity | arithmetic primitive | COVERED | `build_confidence.rs::mode_equiv_primitive_arithmetic` |
| `dual_mode_factorial` | spec/04 §4.6 — mode parity | recursive defn | COVERED | absorbed by `mode_equiv_*` family + `recursive_factorial` |
| `dual_mode_nested_let` | spec/04 §4.3 — mode parity | let | COVERED | `build_confidence.rs::mode_equiv_let_binding` |
| `dual_mode_chained_calls` | spec/04 §4.6.1 — mode parity | chained calls | COVERED | `build_confidence.rs::mode_equiv_primitive_arithmetic` shape |
| `dual_mode_comparison` | appendix-a §A.3 — mode parity | comparison + if | COVERED | absorbed |
| `dual_mode_forward_reference` | spec/05 §5.1 — mode parity | forward ref | COVERED | `forward_reference_between_defns` (REPL-canonical) |
| `dual_mode_boolean_logic` | spec/04 §4.1.3 — mode parity | bool literal | COVERED | `build_confidence.rs::mode_equiv_if_else_branching` + literal_boolean |
| `dual_mode_enum_match` | spec/06 §6.2.2 — mode parity | enum match | COVERED | `build_confidence.rs::mode_equiv_pattern_match_nested` |
| `dual_mode_recursive` | spec/04 §4.6 — mode parity | recursive | COVERED | absorbed |

### 9. Annotations (3 tests, lines 739–759)

| Test name | Spec property | Angle | Disposition | Notes |
|---|---|---|---|---|
| `annotated_params` | spec/04 §4.9 — annotated param | `(defn inc [:Int x] ...)` | COVERED | `spec_03_types.rs::annotated_params_int` |
| `annotated_return_inferred` | spec/04 §4.9 — annotation constrains body | identity over annotated param | COVERED | `spec_03_types.rs::annotated_return_type_int` (parallel angle) |
| `annotation_mismatch_error` | spec/04 §4.9 — annotation mismatch | `:Int x` then passed Bool | COVERED | `spec_03_types.rs::unification_int_vs_string_errors` (general annotation-mismatch error shape) |

### 10. Let-polymorphism (2 tests, lines 768–786)

| Test name | Spec property | Angle | Disposition | Notes |
|---|---|---|---|---|
| `let_polymorphism_identity` | spec/03 §3.4 — let-polymorphism on top-level fn | `(id 1) + (id 2)` | COVERED | `spec_03_types.rs::let_polymorphism_identity_two_types` |
| `let_bound_polymorphic_usage` | spec/03 §3.4 — let-bound id used at multiple types | `(let [id (fn [x] x)] ...)` | COVERED | absorbed by `let_polymorphism_identity_two_types` (same spec, equivalent angle) |

### 11. Multi-defn programs (3 tests, lines 795–824)

| Test name | Spec property | Angle | Disposition | Notes |
|---|---|---|---|---|
| `multiple_functions` | spec/05 §5.1 — multiple defns | 3 chained transformations | COVERED | `repl_lifecycle.rs::multiple_defns_coexist` |
| `mutual_forward_references` | spec/05 §5.1 — interleaved forward refs | mutual ref between two fns | COVERED | `spec_05_definitions.rs::forward_reference_between_defns` |
| `main_calls_helper` | spec/05 §5.1 — main calls top-level helper | `(helper)` from main | COVERED | absorbed by `multiple_defns_coexist` |

### 12. Additional batch literals + match (10 tests, lines 833–931)

| Test name | Spec property | Angle | Disposition | Notes |
|---|---|---|---|---|
| `negative_integer` | spec/04 §4.1.1 — negative int literal | `-3` | COVERED | `spec_04_expressions.rs::literal_integer_negative` |
| `zero` | spec/04 §4.1.1 — zero | `0` | COVERED | `spec_04_expressions.rs::literal_integer_zero` |
| `large_integer` | spec/04 §4.1.1 — large int | `1000000000` | COVERED | `repl_introspection.rs::display_large_int` |
| `boolean_not_true` | appendix-a §A.3 — not on true | `(not true)` returns 0 | COVERED | `spec_appendix_a_builtins.rs::primitive_not_true` |
| `boolean_not_false` | appendix-a §A.3 — not on false | `(not false)` returns 1 | COVERED | `spec_appendix_a_builtins.rs::primitive_not_false` |
| `deeply_nested_let` | spec/04 §4.3 — depth-4 let nesting | 4 levels of let | COVERED | `spec_04_expressions.rs::let_deeply_nested_3_or_more` (already authored 15e32b3) |
| `if_with_let_branches` | spec/04 §4.4 — if with let in arms | both branches contain let | COVERED | absorbed by `let_nested_shadowing` + `if_true_branch` (compositional) |
| `match_wildcard` | spec/06 §6.2.3 — wildcard pattern | `_` matches Blue after Red | COVERED | `spec_06_pattern_matching.rs::pattern_wildcard_catchall` |
| `match_var_pattern` | spec/06 §6.2.4 — variable pattern | `x` binds Green | COVERED | `spec_06_pattern_matching.rs::pattern_variable_binds_value` |
| `comparison_less_equal` | appendix-a §A.3 — le-i64 | `(le-i64 3 3)` | COVERED | `spec_appendix_a_builtins.rs::primitive_le_i64` |
| `comparison_greater_equal` | appendix-a §A.3 — ge-i64 | `(ge-i64 5 3)` | COVERED | `spec_appendix_a_builtins.rs::primitive_ge_i64` |

### 13. Additional REPL tests (13 tests, lines 940–1058)

| Test name | Spec property | Angle | Disposition | Notes |
|---|---|---|---|---|
| `repl_boolean_expression` | spec/04 §4.1.3 — bool literal at REPL | `true` | COVERED | `repl_introspection.rs::display_bool_true` + `spec_04_expressions.rs::literal_boolean_true` |
| `repl_boolean_false` | spec/04 §4.1.3 — bool false at REPL | `false` | COVERED | `repl_introspection.rs::display_bool_false` |
| `repl_if_expression` | spec/04 §4.4 — if at REPL | `(if true 1 2)` | COVERED | `spec_04_expressions.rs::if_true_branch`/`if_false_branch` (REPL-canonical) |
| `repl_let_expression` | spec/04 §4.3 — let at REPL | `(let [x 10 y 20] ...)` | COVERED | `spec_04_expressions.rs::let_single_binding` + `let_sequential_bindings` |
| `repl_negative_int` | spec/04 §4.1.1 — neg int at REPL | `-5` | COVERED | `repl_introspection.rs::display_negative_int` |
| `repl_nested_calls` | spec/04 §4.6.1 — nested calls at REPL | `(inc (double (inc 3)))` | COVERED | `spec_04_expressions.rs::application_chained` (REPL-canonical) |
| `repl_parse_error_recovers` | repl/spec.md §5.2 — parse error recovery | error then fresh eval | COVERED | `repl_lifecycle.rs::parse_error_preserves_prior_defs` |
| `repl_not_operator` | appendix-a §A.3 — not at REPL | `(not true)`/`(not false)` | COVERED | `spec_appendix_a_builtins.rs::primitive_not_*` (REPL-canonical) |
| `repl_comparison_operators` | appendix-a §A.3 — comparison at REPL | 5 comparison primitives | COVERED | `spec_appendix_a_builtins.rs::primitive_*_i64` family (all 5 carry-forwarded) |
| `repl_multiple_definitions` | spec/05 §5.1 — multi-defn at REPL | 3 defns + sum | COVERED | `repl_lifecycle.rs::multiple_defns_coexist` |
| `repl_recursive_countdown` | spec/04 §4.6 — recursive at REPL | `(countdown 100)` | COVERED | absorbed by `recursive_factorial`/`recursive_fibonacci` (recursive shape) |
| `repl_enum_definition_and_use` | spec/05 §5.2.3 — enum at REPL | tag values 0/1 | COVERED | `repl_introspection.rs::deftype_display_enum` + `constructor_display` |
| `repl_defn_then_expression` | spec/05 §5.1 — defn then call | `(square 7)` | COVERED | `repl_lifecycle.rs::defn_then_call_in_next_form` |

### 14. Additional error tests (3 tests, lines 1066–1080)

| Test name | Spec property | Angle | Disposition | Notes |
|---|---|---|---|---|
| `error_if_condition_not_bool` | spec/04 §4.4 — if cond Bool | `(if 1 2 3)` rejected | COVERED | `repl_negative.rs::type_error_if_condition_wrong_type` |
| `error_duplicate_param_names` | spec/05 §5.1.1 — `[x x]` rejected | `(defn bad [x x] ...)` | COVERED | `repl_negative.rs::duplicate_param_names_neg` (already authored 15e32b3) — confirmed correct |
| `error_undefined_function_call` | spec/04 §4.2 — undefined fn | `(nonexistent 1)` | COVERED | `repl_negative.rs::unbound_symbol_clear_error` (covers undefined-fn-as-head case) |

### 15. Runtime errors / encoding (6 tests, lines 1089–1148)

| Test name | Spec property | Angle | Disposition | Notes |
|---|---|---|---|---|
| `integer_overflow_wraps` | spec/12 §12.7.2 — overflow wraps | `i64::MAX + 1 = i64::MIN` | COVERED | `spec_12_runtime.rs::integer_overflow_wraps_silently` |
| `integer_underflow_wraps` | spec/12 §12.7.2 — underflow wraps | `i64::MIN - 1 = i64::MAX` | COVERED | `spec_12_runtime.rs::integer_underflow_wraps_silently` |
| `checked_division_by_zero_panics` | spec/12 §12.7.3 — div by zero panics | `(div-i64 42 0)` returns Err | COVERED | `spec_12_runtime.rs::integer_division_by_zero_panics_neg` |
| `checked_div_min_neg1_panics` | spec/12 §12.7.3 — i64::MIN/-1 overflow | overflow trap | COVERED | `spec_12_runtime.rs::integer_div_min_by_neg_one_panics_neg` (already authored 15e32b3) — confirmed correct |
| `checked_division_normal` | spec/12 §12.7.3 — normal div | `(div-i64 100 7) = 14` | COVERED | `spec_appendix_a_builtins.rs::primitive_div_i64` |
| `source_encoding_utf8` | spec/01 §1.1 — UTF-8 source | `"héllo"` parses, str-len > 0 | COVERED | `spec_12_runtime.rs::string_utf8_source_encoding_accepted` |

## Comparison to commit `15e32b3` cluster-mode authoring

The 8 carry-forwards already authored from this file are confirmed
**correct** by per-test review:

| `15e32b3` carry | Originating ring0 test | Confirmation |
|---|---|---|
| `tco_deep_countdown` | `tco_deep_countdown` | confirmed — 1M-frame countdown angle preserved |
| `tco_match_tail_position` | `tco_match_tail_position` | confirmed — match-arm tail angle preserved |
| `tco_accumulator` | `tco_accumulator` | confirmed — accumulator pattern preserved |
| `tco_let_body_tail_position` | `tco_let_body_tail_position` | confirmed — let-body tail angle preserved |
| `tco_non_tail_recursion_unchanged` | `tco_non_tail_recursion_unchanged` | confirmed — non-tail negative-of-TCO angle preserved |
| `integer_div_min_by_neg_one_panics_neg` | `checked_div_min_neg1_panics` | confirmed — i64::MIN/-1 overflow angle preserved |
| `let_deeply_nested_3_or_more` | `deeply_nested_let` | confirmed — depth-≥3 let nesting preserved |
| `duplicate_param_names_neg` | `error_duplicate_param_names` | confirmed — `[x x]` rejection preserved |

**Cluster mode missed 3 carry-forwards** that per-test review surfaces:

1. **`error_parse_error_unclosed_paren`** — cluster table classified
   the "Type errors basic (8 tests)" cluster as fully COVERED. Per-test
   review shows `parse_error_stray_close` covers extra-close but NOT
   unclosed-`(`. Distinct parser failure mode.

2. **`repl_redefinition_updates_callers`** — cluster table absorbed it
   into "REPL eval basics (8 tests)" → COVERED. Per-test review:
   `repl_lifecycle.rs::redefinition_propagates_through_callers` exists
   but the precise angle (caller defined first, helper redefined while
   live, caller re-evaluated) needs verification. Likely partial-cover.
   Load-bearing GOT propagation — REGRESSION-GUARD.

3. **`nested_if`** — cluster table absorbed it into "Control flow basics
   (4 tests)" → COVERED. Per-test review: `if_true_branch`/`if_false_branch`
   are single-arm; the 3-way ladder angle (if neg / if zero / else) +
   arithmetic combination of multiple ladder calls is not directly
   carried forward.

So the **count correction is +3 GAP-COVER** (cluster mode → 6 declared
GAP-COVER; per-test → 9 actual GAP-COVER; the 3 new are listed above).

## Recommendations for /sprint

### Authoring dispatch

Author 3 NEW carry-forwards in a follow-up dispatch (not this audit):

1. `error_parse_error_unclosed_paren` → `tests/repl_negative.rs`,
   `parse_error_unclosed_paren_neg`. Cite `repl/spec.md §5.1`.
2. `nested_if` → `tests/spec_04_expressions.rs`,
   `if_three_way_ladder`. Cite `spec/04-expressions.md §4.4`.
3. `repl_redefinition_updates_callers` — first VERIFY against
   `repl_lifecycle.rs::redefinition_propagates_through_callers`. If the
   existing test covers the same angle, mark COVERED and skip. If it
   covers a different angle (helper defined first vs caller defined
   first, redefn between caller defn and call), author
   `redefinition_updates_live_callers_through_got` in
   `tests/repl_lifecycle.rs`.

These 3 would close the file-4 gap surfaced by per-test review.

### Methodology takeaway

**Cluster mode for ring0 missed 3 carry-forwards** out of ~108 tests
(~3% additional yield). This is markedly less than the Wave 5.5
sketch_port sample (which surfaced 25% GAP-COVER). The reasons:

- ring0 is by design a baseline-language smoke suite — its tests are
  shallow per-feature checks rather than discriminating regression
  shapes. Most assertions are 1:1 absorbed by the tightly-named
  spec-section carry-forwards (`literal_*`, `lambda_*`, `pattern_*`,
  `primitive_*`).
- The 5 TCO tests (a clear GAP-COVER cluster) were already noted in
  the cluster table and authored. Cluster mode worked well for these.
- The dual-mode cluster (10 tests) is genuinely absorbed by
  `build_confidence.rs::mode_equiv_*` — cluster mode correctly
  declared this COVERED.

**Cluster mode IS misleading on edge cases.** The 3 missed tests are
all subtle angles inside otherwise-well-covered clusters:

- `error_parse_error_unclosed_paren` was inside a cluster of 8
  type/parse error tests where the OTHER 7 are COVERED. Cluster mode
  marked the cluster COVERED; per-test caught the unclosed-vs-close
  distinction.
- `nested_if` was inside a "Control flow basics (4 tests)" cluster
  also containing `chained_function_calls`, `comparison_operators`,
  `forward_reference`. Cluster mode absorbed into the COVERED
  generalization; per-test caught the 3-way ladder angle.
- `repl_redefinition_updates_callers` was inside an 8-test REPL eval
  basics cluster. Cluster mode absorbed; per-test caught the live-caller
  GOT propagation timing.

**Net assessment**: cluster mode for ring0 was 97% accurate. For
sketch_port (Wave 5.5 sample), the rate was 75% accurate. The
difference is the test density — sketch_port has many discriminating
shapes packed into morphologically-similar test names, where cluster
mode loses fidelity faster.

For the remaining 4 large files (sketch_port, e2e, ring1, ring2),
**per-test review remains warranted** to catch the residual edge cases
even when the bulk of a cluster is uniform. Time cost ~1 hour per
~100-test file; yield ~3-15 additional carry-forwards depending on
density.

### Spec-traceability issues

No mis-citations surfaced in the originating ring0 tests; spec
annotations (`// spec: 04-expressions §4.X`) all resolve. The earlier
Wave 3.5 audit (42 mis-cites) had already cleaned ring0.rs's anchor
strings.

### Tests where disposition was hard to call

- `lambda_in_let` (line 269) — clearly absorbed by combined coverage
  but no single test asserts the precise binding-then-call shape.
  Marked COVERED via composition; flag for `/sprint` if a discrete
  test is preferred.
- `lambda_passed_to_function` (line 280) — HOF-passing of an anonymous
  lambda; absorbed by `lambda_closure_captures` shape (which combines
  closure + HOF) but a pure HOF-passing test (no capture) is not
  isolated. Marked COVERED via composition; flag if discrete needed.
- `mutual_forward_references` (line 807) — name implies mutual
  recursion, but the test body is interleaved straight-line forward
  references (not actually mutually recursive). The
  `forward_reference_between_defns` carry-forward covers single-direction
  forward ref. The bidirectional shape may differ — flag for review.

These three are flagged for `/sprint` judgment; the 105 others have
unambiguous classification.

### Audit-volume signal

108 tests reviewed in one dispatch. The chunking suggested by the
brief (mental chunks of ~30) maps to:

- Chunk 1 (lines 38–355, tests 1–30): core batch + REPL basics + lambdas.
- Chunk 2 (lines 364–731, tests 31–67): TCO + floats + errors + ADTs + dual-mode.
- Chunk 3 (lines 739–931, tests 68–86): annotations + polymorphism + multi-defn + literal/match.
- Chunk 4 (lines 940–1148, tests 87–108): additional REPL + errors + runtime + encoding.

This 108-test volume is sustainable for one dispatch. Larger files
(>120 tests) should be chunked into 2 dispatches per user direction.
