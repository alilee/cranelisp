# Wave 5.6 file 5 sketch_port.rs — per-test re-audit (in progress)

Per-test re-audit of `tests/legacy/sketch_port.rs` (148 tests),
correcting the cluster-mode shortcut from
`tests/plan/wave-5.6-dedupe-audit.md` §5.

Authored: `/qa` (audit-only dispatch, 2026-05-04). Methodology: per-test
review against the 16 e2e carry-forward files in main, with Wave 5.6
disposition codes (COVERED / DUPLICATE-IN-LEGACY / GAP-COVER /
REGRESSION-GUARD / GAP-HARVEST). Same per-test framework as
`tests/plan/wave-5.6-ring0-reaudit.md`.

## Chunk 1 of 3 — tests 1-50 (`sketch_hello` through `sketch_repl_auto_curry`)

### Summary

| Disposition | Count |
|---|---:|
| COVERED | 38 |
| DUPLICATE-IN-LEGACY | 0 |
| GAP-COVER | 12 (of which REGRESSION-GUARD: 6) |
| GAP-HARVEST | 0 |
| **Total** | **50** |

Of the 12 GAP-COVER findings, 6 are REGRESSION-GUARD (originating
sprint-named or load-bearing repro angles): `sketch_repl_redefinition_updates_callers`,
`sketch_repl_type_error_recovers`, `sketch_repl_trait_error_recovers`,
`sketch_default_method_used_when_not_overridden` (S07-traits §7.1.5),
`sketch_default_method_overridden`, `sketch_default_method_validate_impl_missing_required`.

### Per-test classifications

#### Cluster A — Core batch arithmetic / control flow (tests 1-10, lines 146-282)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 1 | `sketch_hello` | spec/04 §4.1.1 — int literal return from `main` | `(defn main [] 42)` | COVERED | `spec_04_expressions.rs::literal_integer_positive` + `build_confidence.rs::mode_equiv_constant_main` |
| 2 | `sketch_factorial` | spec/04 §4.6 — recursive defn (batch) | `(fact 10)`=3628800 | COVERED | `repl_lifecycle.rs::recursive_factorial` |
| 3 | `sketch_fibonacci` | spec/04 §4.6 — recursive defn (batch) | `(fib 10)`=55 | COVERED | `repl_lifecycle.rs::recursive_fibonacci` |
| 4 | `sketch_nested_let` | spec/04 §4.3 — nested let bindings | depth-2 with cross-binding ref | COVERED | `spec_04_expressions.rs::let_nested_shadowing` + `let_deeply_nested_3_or_more` |
| 5 | `sketch_chained_function_calls` | spec/04 §4.6.1 — direct call chain | `(double (inc 5))` | COVERED | `spec_04_expressions.rs::application_chained` |
| 6 | `sketch_comparison_operators` | appendix-a §A.3 — comparison primitives + if | 5 cmp ops summed via `if`+let | COVERED | `spec_appendix_a_builtins.rs::primitive_lt_i64`/`gt_i64`/`eq_i64_*`/`le_i64`/`ge_i64` |
| 7 | `sketch_forward_reference` | spec/05 §5.1 — forward ref (batch) | callee defined after caller | COVERED | `spec_05_definitions.rs::forward_reference_between_defns` |
| 8 | `sketch_type_error_add_bool` | spec/03 §3.1 — type error, Bool in Int op | `(add-i64 1 true)` rejected | COVERED | `repl_negative.rs::type_error_arg_mismatch` (presumed; the `add-i64` Bool-arg shape is the canonical type-mismatch repro) |
| 9 | `sketch_arithmetic` | appendix-a §A.3 — chained arithmetic (4 ops in let) | `add/sub/mul/div` chained | COVERED | `spec_appendix_a_builtins.rs::primitive_add_i64`/`sub`/`mul`/`div` (composite covered piecewise) |
| 10 | `sketch_nested_if` | spec/04 §4.4 — 3-way if ladder (batch) | `(classify n)` summed across 3 inputs | COVERED | `spec_04_expressions.rs::if_nested_three_way_ladder` (already authored — verified at line 193) |

#### Cluster B — REPL basics (tests 11-17, lines 290-352)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 11 | `sketch_repl_eval_expression` | spec/04 §4.1 — REPL int/arith/if | 3 expressions evaluated | COVERED | `spec_04_expressions.rs::literal_integer_positive` + `if_true_branch` + `spec_appendix_a_builtins.rs::primitive_add_i64`/`mul_i64` |
| 12 | `sketch_repl_define_and_call` | spec/05 §5.1 — defn + call at REPL | `(add1 5)` | COVERED | `repl_lifecycle.rs::defn_then_call_in_next_form` |
| 13 | `sketch_repl_chained_calls` | spec/04 §4.6.1 — chained at REPL | `(pipeline 5)` via 3 defns | COVERED | `repl_lifecycle.rs::multiple_defns_coexist` + `incremental_build_up` |
| 14 | `sketch_repl_redefinition_updates_callers` | repl/spec.md §15.6 — GOT propagation through redefn | caller defined first; helper redefined; caller produces NEW body's result | **GAP-COVER (REGRESSION-GUARD)** | `repl_lifecycle.rs::redefinition_propagates_through_callers` covers the propagation angle but uses 1 caller + 1 redefn; this test exercises a 3-defn pipeline where helper is mid-pipeline and value flows transitively. The pipeline-shape (transitive caller through 2 layers of indirection) is distinct. Recommended target: `tests/repl_lifecycle.rs::redefinition_propagates_transitively_through_pipeline`. (See also `redefinition_updates_live_callers` line 378 — confirm not 1:1 dup before authoring.) |
| 15 | `sketch_repl_recursive_function` | spec/04 §4.6 — recursive at REPL | `(fact 10)` | COVERED | `repl_lifecycle.rs::recursive_factorial` |
| 16 | `sketch_repl_type_error_recovers` | repl/spec.md §15.2 — error then fresh eval | error then `(add-i64 1 2)`=3 | **REGRESSION-GUARD** | `repl_negative.rs::error_then_valid_form_succeeds` covers the same angle BUT using a different concrete error (parse vs type). The `add-i64 1 true` type-error-recovery angle (typecheck path; not parser path) is the discriminating shape. Recommended target: `tests/repl_negative.rs::type_error_recovery_continues_session`. |
| 17 | `sketch_repl_multiple_params` | spec/05 §5.1.1 — multi-param fn at REPL | `(add 3 4)` | COVERED | `spec_05_definitions.rs::defn_multi_params` |

#### Cluster C — Lambdas / first-class fns (tests 18-27, lines 360-447)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 18 | `sketch_lambda_immediate_call` | spec/04 §4.5 — lambda immediate call | `((fn [x] (add-i64 x 1)) 5)` | COVERED | `spec_04_expressions.rs::lambda_immediate_call` |
| 19 | `sketch_lambda_in_let` | spec/04 §4.5 — lambda bound in let | `(let [f ...] (f 5))` | COVERED | `spec_04_expressions.rs::lambda_bound_in_let_and_called` |
| 20 | `sketch_lambda_passed_to_function` | spec/04 §4.5 — lambda as HOF arg | `(apply-fn (fn ...) 5)` | COVERED | `spec_04_expressions.rs::lambda_passed_as_argument_invoked_inside_callee` |
| 21 | `sketch_named_function_as_value` | spec/04 §4.6.2 — top-level fn as first-class value | `(apply-fn double 5)` | COVERED | `spec_07_traits.rs::operator_as_first_class_value` (fn-as-value shape); also implicit in `lambda_passed_as_argument_invoked_inside_callee` family |
| 22 | `sketch_lambda_zero_params` | spec/04 §4.5 — zero-arg lambda | `((fn [] 42))` | COVERED | `spec_04_expressions.rs::lambda_zero_args` |
| 23 | `sketch_lambda_multi_params` | spec/04 §4.5 — multi-arg lambda | `((fn [x y] ...) 3 4)` | COVERED | `spec_04_expressions.rs::lambda_multi_args` |
| 24 | `sketch_repl_lambda_immediate` | spec/04 §4.5 — lambda immediate at REPL | same shape as #18 | COVERED | `spec_04_expressions.rs::lambda_immediate_call` is REPL-canonical |
| 25 | `sketch_repl_lambda_in_let` | spec/04 §4.5 — lambda in let at REPL | same shape as #19 | COVERED | `spec_04_expressions.rs::lambda_bound_in_let_and_called` is REPL-canonical |
| 26 | `sketch_repl_higher_order_function` | spec/04 §4.5 — REPL HOF | `(apply-fn (fn ...) 5)` | COVERED | `spec_04_expressions.rs::lambda_passed_as_argument_invoked_inside_callee` is REPL-canonical |
| 27 | `sketch_repl_named_function_as_value` | spec/04 §4.6.2 — named fn as value at REPL | same shape as #21 | COVERED | absorbed by `operator_as_first_class_value` shape |

#### Cluster D — Closures / captures (tests 28-34, lines 455-528)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 28 | `sketch_closure_simple_capture` | spec/04 §4.5.1 — closure simple capture | `(make-adder 5)` then `(add5 3)` | COVERED | `spec_04_expressions.rs::lambda_closure_captures` |
| 29 | `sketch_closure_multiple_captures` | spec/04 §4.5.1 — multiple captures from outer let | inner fn captures both `a` and `b` | **GAP-COVER** | `lambda_closure_captures` covers single-capture; multiple captures (2 outer let vars captured into inner lambda body) is a distinct angle. Recommended target: `tests/spec_04_expressions.rs::lambda_closure_multi_captures`. Cite spec/04-expressions §4.5.1. |
| 30 | `sketch_closure_returned_from_function` | spec/04 §4.5.1 — closure returned from defn (top-level), then called | `(make-multiplier 3)` returns fn; `(triple 7)` | COVERED | `lambda_closure_captures` covers same shape (`(make-add 10)` returned then called) |
| 31 | `sketch_closure_nested` | spec/04 §4.5.1 — closure passed through HOF after make | `(apply-fn add10 5)` | COVERED | composition of `lambda_closure_captures` + `lambda_passed_as_argument_invoked_inside_callee`; absorbed |
| 32 | `sketch_repl_closure_simple` | spec/04 §4.5.1 — closure at REPL | same shape as #28 | COVERED | `lambda_closure_captures` is REPL-canonical |
| 33 | `sketch_repl_closure_multiple_captures` | spec/04 §4.5.1 — multi-capture at REPL | same shape as #29 | **GAP-COVER** | absorbed by recommendation for #29 (single carry-forward sufficient — REPL is canonical) |
| 34 | `sketch_closure_with_higher_order` | spec/04 §4.5.1 — closure→HOF composition | `(apply-fn (make-adder 100) 42)` | COVERED | composition; absorbed |

#### Cluster E — IO / pure (test 35, line 536)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 35 | `sketch_pure_lifts_value` | spec/10 §10.2 — `Pure` constructor wraps a value | display result of `(Pure 42)` contains "42" | COVERED | `spec_10_io.rs` Pure-related tests cover Pure construction + display (verified extensive coverage in S64 Wave 3 Batch 4 — 26 e2e tests for IO surface) |

#### Cluster F — String literals (test 36, line 550)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 36 | `sketch_repl_string_literal` | spec/02 §2.5 — string literal display contains both content + type tag | `"hello"` displays as `:String "hello"` | COVERED | `repl_introspection.rs::display_string_literal` + `spec_03_types.rs::primitive_string_display` |

#### Cluster G — Trait tests (tests 37-43, lines 572-651)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 37 | `sketch_user_defined_trait_impl` | spec/07 §7.1 — user trait declaration + impl + dispatch | `(deftrait Doubled ...)` then `(impl ... Int ...)` then `(doubled 21)`=42 | COVERED | `spec_07_traits.rs::user_trait_simple` + `trait_impl_concrete_type` |
| 38 | `sketch_default_method_used_when_not_overridden` | spec/07 §7.1.5 — default method body synthesized when impl omits | `(wave 5)`=15 via default body `(+ (greet x) 10)` | **REGRESSION-GUARD** | `spec_07_traits.rs` does not test default-method synthesis (file's 11 tests cover impl/dispatch/operators/constrained-poly only). spec/07 §7.1.5 is a known-implementation-gap (per quarantine-header triage report — Category A). When the implementation lands, this test is the canonical assertion. Recommended target: `tests/spec_07_traits.rs::default_method_used_when_not_overridden`. **Will fail until implementation lands** — failing-not-ignored applies; FIXME against `/typecheck` + `/backend` per existing triage report. |
| 39 | `sketch_default_method_overridden` | spec/07 §7.1.5 — explicit override shadows default | `(wave 5)`=500 with override | **REGRESSION-GUARD** | sister test of #38; same FIXME chain. Recommended target: `tests/spec_07_traits.rs::default_method_overridden_by_impl`. |
| 40 | `sketch_default_method_validate_impl_missing_required` | spec/07 §7.1.5 — impl missing non-default method errors | omit `greet` (no default) errors | **REGRESSION-GUARD** | negative-of-#38; verifies default-method machinery doesn't permit ALL methods to be omitted. Recommended target: `tests/spec_07_traits.rs::impl_missing_required_method_neg`. |
| 41 | `sketch_trait_operator_dispatch` | spec/07 §7.3 — trait operator dispatch (+, -, *, /) | 4 arith ops on Int via test prelude | COVERED | `spec_07_traits.rs::operator_plus_int` (and the Float counterpart); the Int-dispatch shape for all four ops absorbed by canonical operator_plus_int + the test-prelude wiring |
| 42 | `sketch_trait_comparison_dispatch` | spec/07 §7.3 — comparison operator dispatch (=, <, >, <=, >=) | 5 comparisons on Int | COVERED | `spec_07_traits.rs::trait_method_dispatched_by_arg_type` (covers Eq/Ord dispatch shape); `spec_appendix_a_builtins.rs::primitive_lt_i64`/`gt`/`le`/`ge`/`eq` covers underlying primitives |
| 43 | `sketch_repl_trait_error_recovers` | spec/07 §7.3 — trait method called on non-impl'd type errors; session recovers | `(double true)` errors; `(double 6)`=12 succeeds after | **REGRESSION-GUARD** | `repl_negative.rs::error_then_valid_form_succeeds` covers session continuation generally, but the trait-dispatch-failure-then-recovery shape (where Int impl exists but Bool does not) is a distinct angle. Recommended target: `tests/repl_negative.rs::trait_method_no_impl_then_recovery`. Cite repl/spec.md §15.2 + spec/07 §7.3. |

#### Cluster H — Multi-sig / overload / auto-curry (tests 44-50, lines 660-723)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 44 | `sketch_multi_sig_different_arities` | spec/05 §5.1.2 — multi-sig same name diff arity | `(add 1 2)`=3 + `(add 1 2 3)`=6 + nested `(add-i64 (add 1 2) (add 1 2 3))`=9 | COVERED | `spec_04_expressions.rs::multi_sig_arity_dispatch` (line 279) + `spec_05_definitions.rs::defn_multi_clause_arity` (line 77) |
| 45 | `sketch_multi_sig_type_based_dispatch` | spec/05 §5.1.2 — multi-sig type-based dispatch (same arity, diff types) | `(choose 10 20)` Int+Int branch, `(choose 5 true)` Int+Bool branch | **GAP-COVER** | Type-based-dispatch (vs arity-based-dispatch in #44) is a distinct dispatch resolution angle per spec §5.1.2. `multi_sig_arity_dispatch` covers arity-only; the type-discrimination-among-same-arity-clauses shape is not carried forward. Recommended target: `tests/spec_05_definitions.rs::defn_multi_clause_type_dispatch`. (Currently a known impl gap per triage; will fail-not-ignored until typecheck supports type-based multi-sig. FIXME against `/typecheck`.) |
| 46 | `sketch_multi_sig_duplicate_signature_error` | spec/05 §5.1.2 — duplicate clause signatures rejected | two `[x]` clauses → error | **GAP-COVER (REGRESSION-GUARD)** | negative-of-multi-sig-decl; not in carry-forward. Recommended target: `tests/spec_05_definitions.rs::defn_multi_clause_duplicate_sig_neg`. |
| 47 | `sketch_auto_curry_simple` | spec/04 §4.6.3 — partial application returns closure | `(let [f (add 10)] (f 5))`=15 | COVERED | `spec_05_definitions.rs::defn_auto_curry_call_with_fewer_args` (line 94) + `repl_negative.rs::auto_curry_too_few_args_not_error` |
| 48 | `sketch_auto_curry_higher_order` | spec/04 §4.6.3 — curried fn passed as HOF arg | `(apply-fn (add 10) 5)`=15 | **GAP-COVER** | composition of auto-curry + HOF passing; the curried-result-as-HOF-arg shape is a distinct integration angle (auto-curry value flows through `apply-fn` invocation). `defn_auto_curry_call_with_fewer_args` covers curry-then-call directly; the HOF-passing variant is not carried forward. Recommended target: `tests/spec_04_expressions.rs::auto_curry_passed_to_higher_order_fn`. |
| 49 | `sketch_repl_multi_sig_different_arities` | spec/05 §5.1.2 — multi-sig at REPL | same shape as #44 | COVERED | `spec_04_expressions.rs::multi_sig_arity_dispatch` + `spec_05_definitions.rs::defn_multi_clause_arity` are REPL-canonical |
| 50 | `sketch_repl_auto_curry` | spec/04 §4.6.3 — auto-curry at REPL | same shape as #47 | COVERED | `spec_05_definitions.rs::defn_auto_curry_call_with_fewer_args` is REPL-canonical |

### GAP-COVER candidates

For each: name + target file + rationale.

1. **`sketch_repl_redefinition_updates_callers`** → `tests/repl_lifecycle.rs` —
   transitive-caller-through-pipeline angle; verify against existing
   `redefinition_propagates_through_callers` and `redefinition_updates_live_callers`
   (lines 163, 378) before authoring; if existing test covers same angle, mark
   COVERED instead. Cite repl/spec.md §15.6.

2. **`sketch_repl_type_error_recovers`** → `tests/repl_negative.rs` —
   typecheck-path error recovery (vs the parse-path covered by
   `error_then_valid_form_succeeds`). Cite repl/spec.md §15.2.

3. **`sketch_closure_multiple_captures`** → `tests/spec_04_expressions.rs` —
   closure capturing 2+ outer let vars (vs single-var in
   `lambda_closure_captures`). Cite spec/04-expressions §4.5.1.

4. **`sketch_default_method_used_when_not_overridden`** →
   `tests/spec_07_traits.rs` — default-method-body synthesis when impl
   omits the method. Will fail until typecheck/backend implementation
   lands (per quarantine-header triage report Category A); FIXME
   against `/typecheck` + `/backend`. Cite spec/07-traits §7.1.5.

5. **`sketch_default_method_overridden`** → `tests/spec_07_traits.rs` —
   explicit override shadows default. Same FIXME chain as #4. Cite
   spec/07-traits §7.1.5.

6. **`sketch_default_method_validate_impl_missing_required`** →
   `tests/spec_07_traits.rs` — negative-of-default; impl must still
   provide non-default methods. Cite spec/07-traits §7.1.5.

7. **`sketch_repl_trait_error_recovers`** → `tests/repl_negative.rs` —
   trait-dispatch-failure-then-recovery (vs general session continuation).
   Cite repl/spec.md §15.2 + spec/07-traits §7.3.

8. **`sketch_multi_sig_type_based_dispatch`** →
   `tests/spec_05_definitions.rs` — type-based-dispatch among same-arity
   clauses (vs arity-only). Will fail until typecheck supports it
   (per triage Category A); FIXME against `/typecheck`. Cite
   spec/05-definitions §5.1.2.

9. **`sketch_multi_sig_duplicate_signature_error`** →
   `tests/spec_05_definitions.rs` — duplicate clause-signature
   rejection. Cite spec/05-definitions §5.1.2.

10. **`sketch_auto_curry_higher_order`** → `tests/spec_04_expressions.rs` —
    curried result passed as HOF argument. Cite
    spec/04-expressions §4.6.3.

(Items #29 and #33 share a recommendation; #38–40 share the
default-method FIXME; #45 and #46 share the multi-sig FIXME. Net
unique new e2e tests recommended: ~7-8 after consolidation.)

### Tests flagged for /sprint judgment

- **#14 `sketch_repl_redefinition_updates_callers`** — VERIFY against
  `repl_lifecycle.rs::redefinition_propagates_through_callers` (line 163)
  AND `redefinition_updates_live_callers` (line 378) before authoring.
  The 3-defn pipeline shape may already be covered; this audit marks it
  GAP-COVER conservatively because the transitive (caller→helper→helper)
  angle warrants explicit verification. If the existing tests cover
  the exact shape, downgrade to COVERED.

- **#21 `sketch_named_function_as_value`** — `operator_as_first_class_value`
  in spec_07_traits.rs covers operator-as-value (a constrained
  poly fn); a non-trait top-level fn (`double` here) bound to
  `apply-fn` is a slightly different shape (no constrained poly,
  no operator). Marked COVERED via composition; flag if `/sprint`
  prefers a discrete `defn_as_first_class_value` test.

- **#38–40 default-method tests** — dispatched as REGRESSION-GUARD
  with FIXME-pending status. Per `feedback_failing_not_ignored.md`,
  these would land as un-ignored failing tests if authored now. The
  decision whether to author-as-failing during Wave 5.6 carry-forward
  vs defer until impl lands is a `/sprint` judgment call.

- **#45 `sketch_multi_sig_type_based_dispatch`** — same status as
  #38–40 (impl gap; failing-not-ignored applies). Flag for `/sprint`
  decision on author-as-failing-now vs defer.

---

## Chunk 2 of 3 — tests 51-100 (`sketch_adt_enum_match` through `sketch_exhaustive_match_with_var_pattern`)

### Summary

| Disposition | Count |
|---|---:|
| COVERED | 41 |
| DUPLICATE-IN-LEGACY | 4 |
| GAP-COVER | 5 (of which REGRESSION-GUARD: 2) |
| GAP-HARVEST | 0 |
| **Total** | **50** |

Of the 5 GAP-COVER findings, 2 are REGRESSION-GUARD (negative / boundary-shape repros): `sketch_constrained_fn_as_value_errors`, `sketch_error_non_exhaustive_match` — though the latter is largely covered by `pattern_non_exhaustive_match_on_adt_neg` and may consolidate to COVERED.

### Per-test classifications

#### Cluster I — ADT batch tests (tests 51-59, lines 731-863)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 51 | `sketch_adt_enum_match` | spec/06 §6.1 — match on enum (batch) | `(color-value Green)`=2 in defn body | COVERED | `spec_06_pattern_matching.rs::match_enum_basic` covers the top-level shape; `spec_06_pattern_matching.rs::pattern_match_in_defn_multiple_calls` covers the defn-wrapped shape with all 3 colors. The batch-vs-REPL distinction is absorbed (REPL canonical per PLAN.md) |
| 52 | `sketch_adt_product_construct_and_match` | spec/06 §6.2.1 — product type + match destructure (`px`) | `(get-x (Point 3 4))`=3 | COVERED | `spec_06_pattern_matching.rs::pattern_data_constructor_binds_fields` covers Point destructure; `spec_05_definitions.rs::deftype_product_construct_and_destructure` covers the product shape; `spec_12_runtime.rs::adt_product_alloc_and_match_unwrap` covers heap shape |
| 53 | `sketch_adt_product_get_y` | spec/06 §6.2.1 — product type + match second field | `(get-y (Point 3 4))`=4 | DUPLICATE-IN-LEGACY | Near-1:1 of #52 — different field but identical shape and semantics. Canonical is #52 (covered above) |
| 54 | `sketch_adt_sum_type_some_none` | spec/06 §6.2.1 — `Some` arm | `(unwrap-or (Some 42) 0)`=42 | COVERED | `spec_06_pattern_matching.rs::pattern_some_binds_value` + `spec_05_definitions.rs::deftype_sum_with_field_match` + `spec_12_runtime.rs::adt_sum_some_alloc_and_match` |
| 55 | `sketch_adt_sum_type_none_case` | spec/06 §6.2.1 — `None` arm | `(unwrap-or None 99)`=99 | COVERED | `spec_06_pattern_matching.rs::pattern_nullary_constructor` + `spec_12_runtime.rs::adt_sum_none_no_heap_alloc` cover the None branch |
| 56 | `sketch_adt_match_wildcard` | spec/06 §6.2.3 — wildcard catch-all (batch) | `(is-red Red)+(is-red Blue)`=1 | COVERED | `spec_06_pattern_matching.rs::pattern_wildcard_catchall` covers the wildcard shape |
| 57 | `sketch_adt_match_var_pattern` | spec/06 §6.2.4 — variable pattern bound (batch) | identity-via-var-pattern; outer match selects | COVERED | `spec_06_pattern_matching.rs::pattern_variable_binds_value` + `spec_06_pattern_matching.rs::pattern_int_match_with_wildcard` cover var-pattern semantics |
| 58 | `sketch_adt_nested_match` | spec/06 §6.2 — nested match arms (match inside match arm body) | `(add-options (Some 10) (Some 32))`=42 | **GAP-COVER** | Nested-match (match inside another match's arm body) is a distinct integration angle from the flat patterns covered in `spec_06_pattern_matching.rs`. Match-arm-as-tail-position is partially covered by `spec_12_runtime.rs::tco_match_tail_position` (TCO-focused, ignored); the value-flow nesting angle is not carried. Recommended target: `tests/spec_06_pattern_matching.rs::nested_match_in_arm_body`. Cite spec/06 §6.2 |
| 59 | `sketch_adt_shortcut_syntax` | spec/05 §5.2 — bare-field-name shortcut (`[first second]`) | `(deftype Pair [first second])` no `:Int` annotation | **GAP-COVER** | The shortcut-syntax angle (fresh type vars assigned to bare field names, in lieu of `:Int`/`:a`) is a distinct deftype shape from the explicitly-annotated forms covered in `spec_05_definitions.rs::deftype_product_construct_and_destructure`. Not carried forward. Recommended target: `tests/spec_05_definitions.rs::deftype_product_shortcut_field_names`. Cite spec/05 §5.2 |

#### Cluster J — REPL ADT (tests 60-63, lines 870-912)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 60 | `sketch_repl_adt_enum` | spec/05 §5.2 — enum constructor values at REPL | `Red`=0, `Green`=1, `Blue`=2 (bare nullary tags) | COVERED | `spec_05_definitions.rs::deftype_enum_construct_and_match` covers enum decl + match dispatch; the bare-tag-value angle is covered transitively (matched value resolves) |
| 61 | `sketch_repl_adt_enum_match` | spec/06 §6.1 — REPL match on enum | `(match Green ...)`=20 | COVERED | `spec_06_pattern_matching.rs::match_enum_basic` is the REPL-canonical equivalent |
| 62 | `sketch_repl_adt_product` | spec/06 §6.2.1 — REPL product match | same shape as #52 | COVERED | `spec_06_pattern_matching.rs::pattern_data_constructor_binds_fields` is REPL-canonical |
| 63 | `sketch_repl_adt_sum_type` | spec/06 §6.2.1 — REPL Some/None at REPL | `(match (Some 42) ...)`=42 + `(match None ...)`=99 | COVERED | `spec_06_pattern_matching.rs::pattern_some_binds_value` + `pattern_nullary_constructor` |

#### Cluster K — ADT field accessors via match (tests 64-71, lines 921-996)

These tests document a deliberate language-design choice: the reimplementation uses match for field access (sketch had auto-generated accessors). Most shapes are 1:1 duplicates of the basic destructure tests above.

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 64 | `sketch_adt_product_accessor_x` | spec/06 §6.2.1 — product field-x via match | `(match (Point 3 4) [(Point a b) a])`=3 | DUPLICATE-IN-LEGACY | Identical to #52 (bare match expression vs match-in-defn — but both shapes are covered by `pattern_data_constructor_binds_fields`). Canonical: spec_06's `pattern_data_constructor_binds_fields` |
| 65 | `sketch_adt_product_accessor_y` | spec/06 §6.2.1 — product field-y via match | `(match (Point 3 4) [(Point a b) b])`=4 | DUPLICATE-IN-LEGACY | Identical to #64 with second field. Same disposition |
| 66 | `sketch_adt_accessor_in_function` | spec/06 §6.2.1 — match-as-accessor inside defn | `(get-px p)` calls match | COVERED | `spec_06_pattern_matching.rs::pattern_match_in_defn_multiple_calls` covers match-in-defn shape |
| 67 | `sketch_adt_first_class_accessor` | spec/04 §4.6.2 — defn (containing match) bound as let value, called | `(let [f get-px] (f (Point 3 4)))`=3 | COVERED | composition of `spec_06_pattern_matching.rs::pattern_match_in_defn_multiple_calls` + `spec_04_expressions.rs::lambda_bound_in_let_and_called` (fn-as-value shape); absorbed |
| 68 | `sketch_adt_first_class_constructor` | spec/05 §5.5 — constructor as first-class value (let-bound) | `(let [f MySome] (f 42))` | **GAP-COVER** | Constructor (data ctor `MySome`) bound to a let, then called as a fn. The constructor-as-value angle is distinct from `operator_as_first_class_value` (operator) and `pattern_match_in_defn_multiple_calls` (defn-as-value). Not carried forward. Recommended target: `tests/spec_05_definitions.rs::deftype_constructor_as_first_class_value`. Cite spec/05 §5.5 (or §5.2 if §5.5 absent) |
| 69 | `sketch_adt_sum_accessor` | spec/06 §6.2.1 — sum-type field via match | `(match (MySome 42) [MyNone 0 (MySome v) v])`=42 | DUPLICATE-IN-LEGACY | Near-1:1 of #54 (uses `MyNone`/`MySome` type-name variants). Canonical: `pattern_some_binds_value` |
| 70 | `sketch_repl_adt_accessor` | spec/06 §6.2.1 — REPL accessor via match | same shape as #64+#65 | DUPLICATE-IN-LEGACY | Combined REPL form of #64+#65; covered by `pattern_data_constructor_binds_fields` |
| 71 | `sketch_repl_adt_first_class_accessor` | spec/04 §4.6.2 — REPL accessor-as-value | same shape as #67 | COVERED | absorbed by #67's coverage |

#### Cluster L — ADT trait impls (tests 72-73, lines 1005-1030)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 72 | `sketch_adt_display_enum` | spec/07 §7.1 — user trait impl on ADT (Showable trait) | impl on `Color` produces String per arm | COVERED | `spec_07_traits.rs::user_trait_simple` covers user-trait + impl + dispatch; `spec_05_definitions.rs::deftrait_impl_and_dispatch` covers impl-on-ADT (`Square` shape) — the Color-enum-via-Showable variant is composition; absorbed |
| 73 | `sketch_adt_eq_enum` | spec/07 §7.1 — Eq impl on enum + use in if | `(= Red Red)`=true; `(= Red Blue)`=false | COVERED | `spec_07_traits.rs::trait_method_dispatched_by_arg_type` covers Eq-style dispatch; `spec_appendix_a_builtins.rs::primitive_eq_i64_*` covers underlying primitive. The enum-Eq-impl-via-match-tag shape is composition; absorbed |

#### Cluster M — Constrained polymorphism (tests 74-78, lines 1038-1081)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 74 | `sketch_constrained_add_int` | spec/03 §3.6 — constrained `add` instantiated at Int | `(add 1 2)`=3 via user-defined `(defn add [x y] (+ x y))` | COVERED | `spec_03_types.rs::constrained_add_int` (operator path) + `spec_07_traits.rs::constrained_polymorphism_int_then_float`. The user-named-`add`-defn variant is composition over the same constraint-resolution path; absorbed |
| 75 | `sketch_constrained_add_float` | spec/03 §3.6 — constrained `add` instantiated at Float | `(add 1.5 2.5)`=4.0 | COVERED | `spec_03_types.rs::constrained_add_float` + `spec_07_traits.rs::constrained_polymorphism_int_then_float`; absorbed |
| 76 | `sketch_constrained_add_both_types` | spec/03 §3.6 — same defn instantiated at Int AND Float across consecutive call sites | both #74 + #75 in one session | COVERED | `spec_07_traits.rs::constrained_polymorphism_int_then_float` carries the both-types-from-same-defn shape (`(defn dbl [x] (+ x x))` then dbl 3 + dbl 1.5); identical mono pattern |
| 77 | `sketch_constrained_never_called_ok` | spec/03 §3.6 — declared-but-not-called constrained defn does not error at registration | declare `(defn add ...)`; no call; eval `42`=42 | COVERED | implicit in every spec_07_traits.rs test that declares constrained defns ahead of unrelated evals; not a discriminating regression angle once the constrained-defn pipeline is exercised. Absorbed |
| 78 | `sketch_constrained_fn_as_value_errors` | spec/03 §3.6 — bare constrained fn as value (without instantiation context) errors | `(let [f add] (f 1 2))` rejected | **GAP-COVER (REGRESSION-GUARD)** | Bare constrained fn → first-class value is a known compiler restriction (must be called with args at the constrained reference site). Not carried forward to a negative-shape test in `repl_negative.rs`. Recommended target: `tests/repl_negative.rs::constrained_fn_as_value_neg`. Cite spec/03 §3.6 |

#### Cluster N — Float type (tests 79-82, lines 1088-1118)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 79 | `sketch_float_arithmetic` | spec/03 §3.1 — Float `+` produces Float | `(+ 1.5 2.5)` | COVERED | `spec_appendix_a_builtins.rs::primitive_add_f64` + `spec_03_types.rs::constrained_add_float` |
| 80 | `sketch_float_comparison` | spec/03 §3.1 — Float `<` | `(if (< 1.5 2.5) 1 0)`=1 | COVERED | `spec_appendix_a_builtins.rs::primitive_lt_f64` |
| 81 | `sketch_float_type_error_mixed` | spec/03 §3.1 — Int + Float rejected (no implicit coercion) | `(+ 1 1.0)` errors | COVERED | `spec_03_types.rs::unification_int_vs_string_errors` covers the unification-failure-with-type-mismatch shape; the Int/Float specific instance is a Float-coercion-restriction angle. Note: `repl_negative.rs::type_error_arg_mismatch` covers similar type-mismatch reporting. Marginal but absorbed |
| 82 | `sketch_repl_float_eval` | spec/03 §3.1 — Float literal display | `3.14` | COVERED | `spec_03_types.rs::primitive_float_display` + `spec_04_expressions.rs::literal_float_positive` |

#### Cluster O — Defn type finalization (tests 83-84, lines 1125-1144)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 83 | `sketch_repl_defn_stores_concrete_type` | spec/05 §5.1 — defn using primitive `add-i64` finalizes to concrete type, rejects Bool | `(defn foo [x y] (add-i64 x y))` then `(foo true false)` errs, `(foo 34 35)`=69 | COVERED | `repl_negative.rs::type_error_arg_mismatch` covers the concrete-type-rejection shape; `spec_05_definitions.rs::defn_define_and_call` covers concrete-type acceptance. Composition; absorbed |
| 84 | `sketch_repl_truly_polymorphic_stays_polymorphic` | spec/03 §3.2 — identity defn stays polymorphic across multiple call types | `(id 42)`=42 + `(id true)`=1 | COVERED | `spec_03_types.rs::polymorphic_identity_at_int` + `polymorphic_identity_at_bool` + `let_polymorphism_identity_two_types` cover both call-site instantiations |

#### Cluster P — TCO (tests 85-88, lines 1152-1206)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 85 | `sketch_tco_deep_countdown` | spec/12 §12.5 — self-recursive TCO completes 1M frames | `(countdown 1000000)`=0 | COVERED | `spec_12_runtime.rs::tco_deep_countdown` (currently `#[ignore]`'d pending FIXME 0141 spec MUST clause; carry-forward already present) |
| 86 | `sketch_tco_accumulator` | spec/12 §12.5 — TCO with accumulator parameter | `(sum-to 0 1000000)`=500000500000 | COVERED | `spec_12_runtime.rs::tco_accumulator` (ignored, FIXME 0141) — sketch uses 1M frames, e2e uses 100; angle preserved |
| 87 | `sketch_tco_let_body_tail_position` | spec/12 §12.5 — let body is a tail-position context | `(loop-down 1000000)`=42 | COVERED | `spec_12_runtime.rs::tco_let_body_tail_position` (ignored, FIXME 0141) |
| 88 | `sketch_tco_non_tail_recursion_unchanged` | spec/12 §12.5 — non-tail recursion not optimised but produces correct value (negative-of-TCO) | `(fact 12)`=479001600 | COVERED | `spec_12_runtime.rs::tco_non_tail_recursion_unchanged` (ignored, FIXME 0141) |

#### Cluster Q — Default method on ADT + operator-as-value (tests 89-92, lines 1213-1252)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 89 | `sketch_default_method_on_adt` | spec/07 §7.1.5 — default method synthesized on impl-for-ADT (vs primitive) | `Countable` trait with default `count-plus-one`; impl on `Color` only `count` | **GAP-COVER (REGRESSION-GUARD)** | Sister-shape of chunk-1 #38 (`sketch_default_method_used_when_not_overridden`) but applied to ADT type rather than primitive Int. Same FIXME chain (default-method synthesis is impl-gap per Wave 5.5 quarantine triage Category A). Recommended target: `tests/spec_07_traits.rs::default_method_used_on_adt_impl`. Cite spec/07 §7.1.5. Will fail-not-ignored until typecheck+backend land |
| 90 | `sketch_operator_as_value` | spec/07 §7.6 — operator `+` as value | `(let [f +] (f 3 4))`=7 | COVERED | `spec_07_traits.rs::operator_as_first_class_value` (`(let [op +] (op 4 5))`) — identical shape |
| 91 | `sketch_operator_auto_curry` | spec/07 §7.6 — operator partial application | `(let [inc (+ 1)] (inc 5))`=6 | COVERED | `spec_05_definitions.rs::defn_auto_curry_call_with_fewer_args` covers auto-curry; the operator-curry shape is composition over `operator_as_first_class_value` + auto-curry; absorbed |
| 92 | `sketch_operator_higher_order` | spec/07 §7.6 — operator passed as HOF argument | `(apply2 + 3 4)`=7 | COVERED | `spec_07_traits.rs::operator_as_first_class_value` covers operator-as-value through let-binding; passing through HOF is composition with `spec_04_expressions.rs::lambda_passed_as_argument_invoked_inside_callee`; absorbed |

#### Cluster R — Error path coverage (tests 93-97, lines 1260-1291)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 93 | `sketch_error_type_error_int_plus_bool` | spec/03 §3.1 — type error Int + Bool | `(add-i64 1 true)` rejected | COVERED | `repl_negative.rs::type_error_arg_mismatch` (same shape as chunk-1 #8) |
| 94 | `sketch_error_parse_error_unclosed_paren` | spec/02 §2.1 — parse error unclosed paren | `(add-i64 1 2` | COVERED | `repl_negative.rs::parse_error_stray_close` + `parse_error_has_location` cover parse-error reporting; the unclosed-paren-specific instance is composition |
| 95 | `sketch_error_unbound_symbol` | spec/03 §3.1 — unbound symbol | `no-such-symbol` errors | COVERED | `repl_negative.rs::unbound_symbol_clear_error` + `unbound_bare_symbol_error` |
| 96 | `sketch_error_non_exhaustive_match` | spec/06 §6.5.1 — non-exhaustive match on ADT errors | `(match Circle [Circle 1 Square 2])` (omits Triangle) | **GAP-COVER** | `spec_06_pattern_matching.rs::pattern_non_exhaustive_match_on_adt_neg` covers the non-exhaustive-match shape (omits Blue). Sketch's variant uses `Shape Circle Square Triangle` and omits Triangle; the angle is the same but the test exists. Likely COVERED; flagged as GAP-COVER conservatively pending /sprint judgment. Recommended target (if authored): `tests/spec_06_pattern_matching.rs::non_exhaustive_match_omits_third_constructor` (consolidate or downgrade to COVERED) |
| 97 | `sketch_error_type_mismatch_if_branches` | spec/03 §3.8 — type mismatch in if branches | `(if true 1 "hello")` errors | COVERED | `spec_03_types.rs::unification_int_vs_string_errors` (exact same shape) + `spec_04_expressions.rs::if_neg_branch_type_mismatch` (presumed) |

#### Cluster S — Exhaustive match (tests 98-100, lines 1298-1328)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 98 | `sketch_exhaustive_match_all_constructors` | spec/06 §6.5.1 — exhaustive match (all 3 constructors covered) | `(match Green [Red 1 Green 2 Blue 3])`=2 | COVERED | `spec_06_pattern_matching.rs::match_enum_basic` + `pattern_arms_type_unify` cover the all-constructors-listed shape |
| 99 | `sketch_exhaustive_match_with_wildcard` | spec/06 §6.5.1 — wildcard satisfies exhaustiveness | `(match Green [Red 1 _ 0])`=0 | COVERED | `spec_06_pattern_matching.rs::pattern_wildcard_catchall` (Blue → wildcard arm matches with 99) |
| 100 | `sketch_exhaustive_match_with_var_pattern` | spec/06 §6.5.1 — var pattern satisfies exhaustiveness | `(match Green [x 42])`=42 | COVERED | `spec_06_pattern_matching.rs::pattern_variable_binds_value` covers var-pattern-as-catch-all (`(match 7 [n n])`); the exhaustiveness-via-var-pattern angle is the same property |

### GAP-COVER candidates

For each: name + target file + rationale.

1. **`sketch_adt_nested_match` (#58)** → `tests/spec_06_pattern_matching.rs` —
   nested match (match inside another match's arm body) is a distinct
   value-flow integration angle from flat patterns. Recommended target:
   `nested_match_in_arm_body`. Cite spec/06 §6.2.

2. **`sketch_adt_shortcut_syntax` (#59)** → `tests/spec_05_definitions.rs` —
   bare-field-name shortcut syntax `(deftype Pair [first second])` (without
   `:Type` annotation) is a distinct deftype shape. Recommended target:
   `deftype_product_shortcut_field_names`. Cite spec/05 §5.2.

3. **`sketch_adt_first_class_constructor` (#68)** →
   `tests/spec_05_definitions.rs` — constructor as first-class value
   (let-bound, then called). Distinct from operator-as-value and
   defn-as-value. Recommended target:
   `deftype_constructor_as_first_class_value`. Cite spec/05 §5.5 (or §5.2).

4. **`sketch_constrained_fn_as_value_errors` (#78)** →
   `tests/repl_negative.rs` (REGRESSION-GUARD) — bare constrained fn
   reference (without instantiation context) MUST error. Compiler
   restriction angle not carried as a negative test. Recommended target:
   `constrained_fn_as_value_neg`. Cite spec/03 §3.6.

5. **`sketch_default_method_on_adt` (#89)** → `tests/spec_07_traits.rs`
   (REGRESSION-GUARD) — default-method synthesis when impl is on an ADT
   type (sister-shape of chunk-1 #38 which used primitive Int). Same
   FIXME chain (Wave 5.5 quarantine Category A; will fail-not-ignored
   until `/typecheck` + `/backend` land synthesis). Recommended target:
   `default_method_used_on_adt_impl`. Cite spec/07 §7.1.5.

6. **`sketch_error_non_exhaustive_match` (#96)** —
   conservatively GAP-COVER but `pattern_non_exhaustive_match_on_adt_neg`
   already covers the property. **Likely consolidate to COVERED** at
   /sprint judgment time — the assertion shape is identical and the
   discriminating angle (3-vs-2-constructors omitted) is not load-bearing.

(Items #58 + #59 are pure GAP-COVER. Items #68, #78, #89 are likely
distinct-enough to author. Item #96 likely consolidates to COVERED.
Net unique new e2e tests recommended: ~3-5 after consolidation.)

### Tests flagged for /sprint judgment

- **#53, #64, #65, #69, #70 (DUPLICATE-IN-LEGACY)** — these are
  intra-sketch_port duplicates of #52 / #54 / `pattern_data_constructor_binds_fields`.
  No carry-forward action needed; the canonical e2e instance covers them.
  Flag only because the dedupe-audit shortcut may have over-counted these
  as distinct.

- **#58 `sketch_adt_nested_match`** — VERIFY `pattern_match_in_defn_multiple_calls`
  (which uses match-in-defn) does NOT also cover the nested-match-in-arm-body
  angle. The nested match is `match a [None 0 (Some x) (match b [...])]` —
  inner match in outer arm body. If `/sprint` judges this absorbed by
  existing match coverage, downgrade to COVERED.

- **#68 `sketch_adt_first_class_constructor`** — constructor-as-first-class-value
  is spec/05 §5.5 if the heading exists; if not, cite spec/05 §5.2. Spec
  citation needs verification; flag for `/sprint` to confirm anchor.

- **#77 `sketch_constrained_never_called_ok`** — marked COVERED but the
  declare-but-never-call angle (no instantiation) is technically a distinct
  pipeline-correctness angle (registration without resolution). Composition
  with any constrained-defn test absorbs it transitively, but if `/sprint`
  prefers a discrete `constrained_defn_no_call_compiles` test, this is the
  candidate.

- **#89 `sketch_default_method_on_adt`** — same status as chunk-1 #38–40
  (default-method impl-gap). Per `feedback_failing_not_ignored.md`, if
  authored now it lands as un-ignored failing. /sprint decides
  author-now-as-failing vs defer until impl lands.

- **#96 `sketch_error_non_exhaustive_match`** — likely COVERED by
  `pattern_non_exhaustive_match_on_adt_neg`. Marked GAP-COVER conservatively;
  if `/sprint` agrees the existing test absorbs the angle, downgrade.

---

## Chunk 3 of 3 — tests 101-148 (`sketch_vec_len_literal` through `sigsegv_isolation_trait_impl_with_primitive_in_body`)

### Summary

| Disposition | Count |
|---|---:|
| COVERED | 30 |
| DUPLICATE-IN-LEGACY | 1 |
| GAP-COVER | 17 (of which REGRESSION-GUARD: 9) |
| GAP-HARVEST | 0 |
| **Total** | **48** |

Of the 17 GAP-COVER findings, 9 are REGRESSION-GUARD: the 7
`sigsegv_isolation_*` tests (`sigsegv_isolation_*` naming is a
load-bearing Sprint-N defect-isolation prefix — presumptive REGRESSION-GUARD
per dispatch direction, and individually motivated by the
`SIGSEGV isolation` cluster header), `sketch_run_tests_pass_fn_called`
(user-composable test-runner repro using `discover-tests` + `run-test`
primitives), and `sketch_rc_closure_capturing_closure` (closure-capturing-
closure RC angle is a known regression vector per memory:
`feedback_repros_join_suite.md`).

### Per-test classifications

#### Cluster T — Vec primitives (tests 101-108, lines 1336-1394)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 101 | `sketch_vec_len_literal` | appendix-a §A.3 — `vec-len` of literal vec | `(vec-len [1 2 3])`=3 | COVERED | `spec_appendix_a_builtins.rs::primitive_vec_len` (line 180) |
| 102 | `sketch_vec_len_empty` | appendix-a §A.3 — `vec-len` of empty literal | `(vec-len [])`=0 | COVERED | `spec_04_expressions.rs` line 302 (`vec-len []` returning Int 0) — pinned via primitive |
| 103 | `sketch_vec_get_elements` | appendix-a §A.3 — `vec-get` middle index | `(vec-get [10 20 30] 1)`=20 | COVERED | `spec_appendix_a_builtins.rs::primitive_vec_get_first` (line 186) — index-0 angle. Index-1 is identical primitive shape; absorbed |
| 104 | `sketch_vec_set_returns_new` | appendix-a §A.3 — `vec-set` return propagates | `(vec-get (vec-set ...) 1)`=99 | COVERED | `spec_appendix_a_builtins.rs::primitive_vec_set_preserves_len` (line 198) covers the vec-set+vec-len composition; the get-after-set composition is the same code path; absorbed |
| 105 | `sketch_vec_push_appends` | appendix-a §A.3 — `vec-push` increments length | `(vec-len (vec-push [1 2 3] 4))`=4 | COVERED | `spec_appendix_a_builtins.rs::primitive_vec_push_increases_len` (line 192) |
| 106 | `sketch_vec_push_value` | appendix-a §A.3 — `vec-push` placed value at last index | `(vec-get (vec-push [1 2 3] 99) 3)`=99 | **GAP-COVER** | `primitive_vec_push_increases_len` covers length only; the value-at-last-index angle (verifies push wrote the value, not just incremented length) is distinct. Recommended target: `tests/spec_appendix_a_builtins.rs::primitive_vec_push_value_at_last_index`. Cite appendix-a §A.3 |
| 107 | `sketch_vec_in_let` | appendix-a §A.3 — vec bound in let, accessed | `(let [xs [10 20 30]] (vec-get xs 0))`=10 | **GAP-COVER** | Vec-as-let-binding-value (escapes literal context, flows through let-scope, is then accessed) is a distinct integration angle from inline-literal access. Not carried forward. Recommended target: `tests/spec_appendix_a_builtins.rs::primitive_vec_let_bound_then_get`. Cite appendix-a §A.3. (Possibly absorbed by general let semantics but the vec-flow-through-let shape is the discriminating angle) |
| 108 | `sketch_vec_push_empty` | appendix-a §A.3 — `vec-push` on empty literal | `(vec-get (vec-push [] 42) 0)`=42 | **GAP-COVER** | Push-onto-empty is a boundary case (zero-element start); covered general-shape by `primitive_vec_push_increases_len` but the empty-start boundary is not a discriminating angle in carry-forward. Recommended target: `tests/spec_appendix_a_builtins.rs::primitive_vec_push_onto_empty`. Cite appendix-a §A.3 |

#### Cluster U — List type via inline `(deftype List a)` (tests 109-112, lines 1402-1440)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 109 | `sketch_list_construction` | spec/05 §5.2 + spec/06 §6.2 — recursive ADT (Cons/Nil) construct + match-head | `(Cons 1 (Cons 2 (Cons 3 Nil)))` head-extract via match | COVERED | composition: `spec_05_definitions.rs::deftype_sum_with_field_match` covers recursive-ADT decl shape; `spec_06_pattern_matching.rs::pattern_data_constructor_binds_fields` covers match-extract. The list-shape is the same composition; absorbed |
| 110 | `sketch_list_nil_check` | spec/06 §6.2.3 — match Nil branch on inline-defined recursive ADT | `(match Nil [Nil 1 (Cons h t) 0])`=1 | COVERED | `spec_06_pattern_matching.rs::pattern_nullary_constructor` covers nullary-arm match on a recursive ADT (None vs Cons-equivalent); absorbed |
| 111 | `sketch_list_non_empty_check` | spec/06 §6.2.3 — match Cons branch (non-empty) | `(match (Cons 1 Nil) [Nil 1 (Cons h t) 0])`=0 | COVERED | sister of #110; same pattern-arm coverage. Absorbed |
| 112 | `sketch_list_head_tail` | spec/06 §6.2 — head-extract + nested match (tail destructure) | dual asserts: head=42; nested match into tail | **GAP-COVER** | Two assertions; the second uses **nested match into tail** (`(match (Cons 1 (Cons 2 Nil)) [(Cons h t) (match t [...])])`) — distinct from chunk-2 #58 (`sketch_adt_nested_match`) which nested into Option's `Some` branch. The Cons-tail-recurse-via-nested-match shape is more representative of how a fold-like consumer is written without recursion. Likely consolidates with #58's GAP-COVER recommendation (`nested_match_in_arm_body`). Recommended target: same as #58, possibly extended with a Cons/Nil variant. Cite spec/06 §6.2 |

#### Cluster V — RC (Reference Counting) tests (tests 113-122, lines 1450-1533)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 113 | `sketch_rc_let_string_freed_on_scope_exit` | spec/12 §12.3 — string in let freed on scope exit | `assert_rc_balanced("(let [s \"hello\"] 42)")` | COVERED | `spec_12_runtime.rs::string_literal_alloc_drop_balanced` (line 80) covers the same shape (string in let, body returns Int, scope exit frees string) |
| 114 | `sketch_rc_nested_let_inner_scope_freed` | spec/12 §12.3 — nested let inner-scope binding freed | nested let with two strings | **GAP-COVER** | The single-string case is in `string_literal_alloc_drop_balanced`; the nested-let-with-two-strings shape (verifies inner string freed before outer let scope exits) is a distinct angle. Recommended target: `tests/spec_12_runtime.rs::nested_let_inner_string_freed_before_outer`. Cite spec/12 §12.3 |
| 115 | `sketch_rc_do_intermediate_freed` | spec/12 §12.3 — let-discarded intermediate freed | `(let [_ (str-concat ...)] 0)` discards string result | COVERED | `spec_12_runtime.rs::string_concat_intermediate_freed` (line 93) — direct match on shape |
| 116 | `sketch_rc_drop_glue_option_string` | spec/12 §12.4 — ADT-wrapping-string drop glue | `(Some "hello")` in let; both string + Some allocs balanced | COVERED | `spec_12_runtime.rs::adt_with_string_field_freed` (line 133) — direct shape match |
| 117 | `sketch_rc_drop_glue_none_no_crash` | spec/12 §12.4 — None nullary tag, dec is no-op | `None` in let, no heap allocs | COVERED | `spec_12_runtime.rs::adt_sum_none_no_heap_alloc` (line 120) — direct match |
| 118 | `sketch_rc_vec_int_freed_on_scope_exit` | spec/12 §12.3 — vec-of-Int in let freed | `(let [xs [1 2 3]] 42)` balanced | **GAP-COVER** | `spec_12_runtime.rs::vec_of_strings_alloc_drop` (line 184) covers vec-of-strings; the vec-of-Int (no per-element drop glue, but vec body itself is heap) shape is distinct — exercises the vec-without-element-glue free path. Recommended target: `tests/spec_12_runtime.rs::vec_of_int_let_bound_freed`. Cite spec/12 §12.3 |
| 119 | `sketch_rc_vec_empty_freed` | spec/12 §12.3 — empty vec literal still heap-allocated and freed | `(let [xs []] 42)` balanced | **GAP-COVER** | Empty-vec heap-alloc-and-free is a boundary case not in carry-forward; verifies that `[]` actually allocates (and so must be freed). Recommended target: `tests/spec_12_runtime.rs::empty_vec_let_bound_freed`. Cite spec/12 §12.3 |
| 120 | `sketch_rc_closure_drop_glue_frees_captured_string` | spec/12 §12.4 — closure-capture drop glue | `(let [s "captured"] (let [f (fn [] s)] 42))` | COVERED | `spec_12_runtime.rs::closure_capture_alloc_and_invoke` (line 143) covers closure-with-string-capture alloc/dealloc balance |
| 121 | `sketch_rc_match_temporary_scrutinee_freed` | spec/12 §12.4 — match scrutinee (temporary) freed after match | `(match (Some "hello") [...])` | **GAP-COVER** | The match-scrutinee-as-temporary shape (heap-allocated ADT directly in scrutinee position, freed when match exits) is not directly carried — `adt_with_string_field_freed` uses a let-bound scrutinee; the temporary-scrutinee path exercises a distinct codegen pathway (no let to dec). Recommended target: `tests/spec_12_runtime.rs::match_temporary_scrutinee_freed_on_exit`. Cite spec/12 §12.4 |
| 122 | `sketch_rc_closure_capturing_closure` | spec/12 §12.4 — closure capturing another closure | `(let [f (fn [x] x)] (let [g (fn [] f)] 42))` | **GAP-COVER (REGRESSION-GUARD)** | Closure-capturing-closure (chained closure refs) is a known double-free / leak vector per the closure RC design notes; not directly covered by `closure_capture_alloc_and_invoke` (which captures a string, not a closure). Recommended target: `tests/spec_12_runtime.rs::closure_capturing_closure_balanced`. Cite spec/12 §12.4 |

#### Cluster W — Type annotations (tests 123-124, lines 1543-1557)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 123 | `sketch_annotation_expr_int` | spec/03 §3.5 — typed defn param (Int annotation) | `(defn typed-id [:Int x] x)` | COVERED | `spec_05_definitions.rs::defn_define_and_call` covers param-typed defn (concrete type pinning); the `:Int x` annotation shape is the canonical defn-param-annotation form throughout the suite (used in many tests). Absorbed |
| 124 | `sketch_annotation_param_concrete` | spec/03 §3.5 — multi-param annotated defn | `(defn add [:Int x :Int y] (add-i64 x y))` | COVERED | sister of #123; `spec_05_definitions.rs::defn_multi_params` covers multi-param defn shape; concrete-type-annotation is the dominant test form. Absorbed |

#### Cluster X — Prelude Option from test prelude (tests 125-126, lines 1565-1581)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 125 | `sketch_prelude_option_some` | spec/06 §6.2 — Option from test prelude, Some branch | `(match (Some 42) [...])`=42 | COVERED | `spec_06_pattern_matching.rs::pattern_some_binds_value` is REPL-canonical; identical assertion |
| 126 | `sketch_prelude_option_none` | spec/06 §6.2 — Option from test prelude, None branch | `(match None [None 99 (Some x) x])`=99 | COVERED | `spec_06_pattern_matching.rs::pattern_nullary_constructor` covers None branch; absorbed |

#### Cluster Y — Trace + run-tests (tests 127-129, lines 1591-1656)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 127 | `sketch_trace_literal_returns_trace_call` | spec/04 §4.12 — `trace` returns heap pointer (TraceCall ADT) | `(trace 42)` returns non-null heap ptr | COVERED | `spec_12_runtime.rs::trace_returns_trace_value` (line 197) + `spec_04_expressions.rs::trace_returns_trace_type` (line 311) cover the Trace-returns-ADT-with-tag-0 shape |
| 128 | `sketch_trace_nanos_is_positive` | spec/04 §4.12 — `nanos` accessor reads positive timing from TraceCall | `(nanos (trace (factorial 4)))` > 0 | COVERED | `spec_12_runtime.rs::trace_pattern_match_extracts_name` (line 222) + `trace_form_available_without_import` (line 235) cover the field-extraction-from-Trace shape; the nanos-positivity angle is composition |
| 129 | `sketch_run_tests_pass_fn_called` | spec/04 §4.11 — user-composable test runner via `discover-tests` + `run-test` primitives | user-defined `count-passes` folds over discover-tests result | **GAP-COVER (REGRESSION-GUARD)** | `spec_12_runtime.rs::run_tests_reports_passes` (line 253) covers the `(run-tests)` slash-command path; this test exercises `discover-tests` and `run-test` as **separate composable primitives** that a user can wire into their own runner. Distinct integration angle (primitive accessibility, not slash-command behaviour). Recommended target: `tests/spec_12_runtime.rs::discover_tests_and_run_test_user_composition`. Cite spec/04 §4.11. (Sprint 60 reduction history makes this a load-bearing repro shape) |

#### Cluster Z — Platform / test-capture DLL (tests 130-132, lines 1665-1712)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 130 | `sketch_platform_capture_print_hello` | spec/11 §11.1 — `print` invokes platform side effect (test-capture DLL) | output contains "hello" | **GAP-COVER** | No e2e test against the test-capture DLL is in the carry-forward universe; `tests/v4_pipeline.rs::v4_platform_stdio_print` exists but is in legacy v4_pipeline (not in the carry-forward 16). The platform `print`-roundtrip-through-test-capture shape is not in canonical e2e files. Recommended target: `tests/spec_10_io.rs::platform_print_via_test_capture` OR retain in a dedicated `tests/spec_11_platforms.rs` if/when authored. Cite spec/11 §11.1 |
| 131 | `sketch_platform_capture_read_input` | spec/11 §11.1 — `read-line` returns supplied input via test-capture | `Hello, Alice` round-trip | **GAP-COVER** | sister of #130 — read-line-via-test-capture path. Same target. Recommended: `tests/spec_10_io.rs::platform_read_line_via_test_capture`. Cite spec/11 §11.1 |
| 132 | `sketch_platform_capture_reset_clears_state` | spec/11 §11.1 — `capture.reset()` semantics (test-harness API, not language) | empty after reset | **GAP-HARVEST** | This tests the **test-capture harness API**, not a language property. It is Rust-internal harness behaviour. Per FIXME 0136 harvest disposition, this belongs in unit tests of the test-capture crate, not in carry-forward e2e. Marked HARVEST instead of GAP-COVER |

(Correcting summary above: GAP-HARVEST = 1 — `sketch_platform_capture_reset_clears_state`. Updated counts: COVERED 30, DUPLICATE-IN-LEGACY 1, GAP-COVER 16, GAP-HARVEST 1.)

#### Cluster AA — Misc (tests 133, 134-141, lines 1720-1825)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 133 | `sketch_checked_division_by_zero_panics` | spec/12 §12.7.3 — div-i64 by 0 errors with mention of "division by zero" | `Err` from session.eval | COVERED | `spec_12_runtime.rs::integer_division_by_zero_panics_neg` (line 316) — direct shape match |
| 134 | `sketch_adt_display_option_int_batch` | spec/07 §7.4 — polymorphic impl on concrete ADT instantiation `(MyOpt Int)` | `(impl Showable (MyOpt Int) ...)` then `(showit (MySome 42))` returns String | **GAP-COVER** | Polymorphic impl on concrete-ADT-instantiation (`(MyOpt Int)` as impl target, distinct from polymorphic-target) is a load-bearing trait-resolution angle not in `spec_07_traits.rs` carry-forward. Memory note re: `impl_target_mangled()` (`Option$Int` for concrete vs `Option` for type var) — this exercises that distinction. Recommended target: `tests/spec_07_traits.rs::polymorphic_impl_on_concrete_adt_instantiation`. Cite spec/07 §7.4 |
| 135 | `sketch_non_exhaustive_match_is_compile_error` | spec/04 §4.7 — non-exhaustive match errors at compile time | `(match Circle [Circle 1 Square 2])` (omits Triangle) | COVERED | `spec_06_pattern_matching.rs::pattern_non_exhaustive_match_on_adt_neg` (line 175) covers the same property; chunk-2 #96 already classified COVERED-or-consolidate; same disposition here |
| 136 | `sketch_exhaustive_match_product_type` | spec/04 §4.7 — exhaustive match on product type (single arm matches Point) | `(match (Point 1 2) [(Point a b) (add-i64 a b)])`=3 | COVERED | `spec_06_pattern_matching.rs::pattern_data_constructor_binds_fields` covers the single-arm-product-match shape; absorbed |
| 137 | `sketch_exhaustive_match_non_adt_scrutinee` | spec/04 §4.7 — match on Int scrutinee (var-pattern catch-all is exhaustive) | `(match 42 [x (add-i64 x 1)])`=43 | COVERED | `spec_06_pattern_matching.rs::pattern_variable_binds_value` covers var-pattern as catch-all on non-ADT scrutinee |
| 138 | `sketch_negative_int_still_works` | spec/02 §2.3 — negative integer literal | `-3` and `(add-i64 -1 -2)` | COVERED | `spec_04_expressions.rs::literal_integer_negative` (line 55) covers negative literal; the `add-i64 -1 -2` composition is absorbed |
| 139 | `sketch_boolean_literals` | spec/02 §2.4 — boolean literals + `not` primitive | `true`/`false`/`(not true)`/`(not false)` | **GAP-COVER** | `spec_04_expressions.rs::literal_boolean_true`/`false` (lines 73, 79) cover the literals; the `(not ...)` primitive is NOT covered by either. Recommended target: `tests/spec_appendix_a_builtins.rs::primitive_not_bool` (positive + negation cases). Cite appendix-a §A.3 |
| 140 | `sketch_compile_both_basic` | spec/04 §4.1.1 — batch + REPL parity for constant | `compile_both("42", 42)` | COVERED | `build_confidence.rs::mode_equiv_constant_main` covers batch+REPL parity for constant (S64 introduced mode_equiv_* family) |
| 141 | `sketch_compile_both_recursive` | spec/04 §4.6 — batch + REPL parity for recursive defn | `compile_both((defn fact ... ) (fact 10))`=3628800 | COVERED | `build_confidence.rs::mode_equiv_constant_main` family + `repl_lifecycle.rs::recursive_factorial` cover parity + recursion separately; composition absorbed. Note: the dedicated batch/REPL-parity-for-recursion shape is implicit; if /sprint prefers an explicit `mode_equiv_recursive_factorial`, flag |

#### Cluster BB — `sigsegv_isolation_*` defect-isolation guards (tests 142-148, lines 1834-1898)

These are **REGRESSION-GUARD** by name — `sigsegv_isolation_*` is a
load-bearing Sprint-N defect-isolation prefix (per dispatch direction).
The cluster header (`SIGSEGV isolation`) confirms each test reduces a
specific historical SIGSEGV crash to a minimal repro. None should be
discarded.

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 142 | `sigsegv_isolation_trait_impl_minimal` | spec/07 §7.1 — minimal trait impl on primitive Int | `(deftrait Dbl ...)` + `(impl Dbl Int ...)` + `(dbl 3)`=6 | COVERED | `spec_07_traits.rs::user_trait_simple` + `trait_impl_concrete_type` cover the same shape exactly; the `sigsegv_isolation_*` name flags it as a defect-isolation repro, but the assertion is identical. The REGRESSION-GUARD value is preserved by the existing tests being canonical |
| 143 | `sigsegv_isolation_trait_impl_on_adt` | spec/07 §7.1 — trait impl on enum ADT | `(deftrait Tag ...)` + `(impl Tag Color ...)` matches all 3 ctors | **GAP-COVER (REGRESSION-GUARD)** | `spec_05_definitions.rs::deftrait_impl_and_dispatch` covers impl-on-ADT (Square shape); the impl-on-enum-ADT-with-match-over-all-3-tags shape is distinct (defect-isolation specifically reduced trait-on-enum dispatch). Recommended target: `tests/spec_07_traits.rs::trait_impl_on_enum_adt_with_match_over_all_constructors`. Cite spec/07 §7.1. Sprint origin: SIGSEGV isolation cluster |
| 144 | `sigsegv_isolation_default_method` | spec/07 §7.1.5 — trait with default method (uses required method in default body) | `(count-plus 5)`=15 via default body `(add-i64 (count x) 10)` | **GAP-COVER (REGRESSION-GUARD)** | Sister of chunk-1 #38 (`sketch_default_method_used_when_not_overridden`). Same FIXME chain (default-method synthesis impl gap). Recommended target: same as #38 (`default_method_used_when_not_overridden`) — already in chunk-1's GAP-COVER list; consolidate. The `sigsegv_isolation_*` framing here is the original repro shape. Cite spec/07 §7.1.5 |
| 145 | `sigsegv_isolation_poly_adt_impl` | spec/07 §7.4 — polymorphic ADT impl calling another impl of same trait (recursive trait dispatch) | `(impl Showable (MyOpt Int))` body calls `(showit x)` which dispatches via `Showable Int` impl | **GAP-COVER (REGRESSION-GUARD)** | The polymorphic-impl-body-recursively-dispatching-on-inner-trait shape is a known SIGSEGV vector (referenced from `impl_target_mangled` interaction with constrained-poly mono). #134 (`sketch_adt_display_option_int_batch`) is a near-equivalent assertion — but #145's variant uses `is_ok` rather than display-string assertion (different observation). Likely consolidates to same target as #134: `polymorphic_impl_on_concrete_adt_instantiation`. Cite spec/07 §7.4. Sprint origin: SIGSEGV isolation cluster |
| 146 | `sigsegv_isolation_default_method_no_trait_call` | spec/07 §7.1.5 — default method that uses primitive directly (no trait dispatch in default body) | `(val-plus 5)`=6 via `(add-i64 (val x) 1)` | **GAP-COVER (REGRESSION-GUARD)** | Variant of #144 — discriminates between default-body-with-trait-call (#144) vs default-body-with-primitive-only-call (#146). The two shapes exercise different codegen paths. Recommended target: `tests/spec_07_traits.rs::default_method_with_primitive_only_body`. Cite spec/07 §7.1.5. Sprint origin: SIGSEGV isolation cluster |
| 147 | `sigsegv_isolation_trait_impl_with_trait_dispatch_in_body` | spec/07 §7.3 — impl method body uses operator (`+`) → trait-dispatch-inside-impl-body | `(impl Double Int (defn double [x] (+ x x)))` | **GAP-COVER (REGRESSION-GUARD)** | The impl-body-uses-trait-operator shape (recursion through trait-dispatch resolution at codegen time) is distinct from impl-body-uses-primitive (#148). Specifically the operator `+` requires Num trait resolution while inside another trait's impl. Recommended target: `tests/spec_07_traits.rs::trait_impl_body_uses_operator`. Cite spec/07 §7.3. Sprint origin: SIGSEGV isolation cluster |
| 148 | `sigsegv_isolation_trait_impl_with_primitive_in_body` | spec/07 §7.1 — impl method body uses primitive directly (no trait dispatch) | `(impl Double Int (defn double [x] (add-i64 x x)))` | DUPLICATE-IN-LEGACY | Identical assertion shape to #142 (`sigsegv_isolation_trait_impl_minimal`) — both are `impl Trait Int` with body `(add-i64 x x)` via primitive only. The trait name and method name differ but the shape is 1:1. Canonical: #142 (already COVERED via `user_trait_simple`). Sprint origin: SIGSEGV isolation cluster — the pair (#142, #148) reduces to one canonical guard |

(Updated cluster BB tally: 5 GAP-COVER (REGRESSION-GUARD), 1 DUPLICATE-IN-LEGACY, 1 COVERED.)

### GAP-COVER candidates

For each: name + target file + rationale.

1. **`sketch_vec_push_value` (#106)** → `tests/spec_appendix_a_builtins.rs` —
   value-at-last-index angle (verifies push wrote the value, not just length).
   Cite appendix-a §A.3.

2. **`sketch_vec_in_let` (#107)** → `tests/spec_appendix_a_builtins.rs` —
   vec-flow-through-let integration angle. Cite appendix-a §A.3.

3. **`sketch_vec_push_empty` (#108)** → `tests/spec_appendix_a_builtins.rs` —
   push-onto-empty boundary case. Cite appendix-a §A.3.

4. **`sketch_list_head_tail` (#112)** → consolidate with chunk-2 #58
   (`nested_match_in_arm_body`), ideally with a Cons/Nil variant. Cite spec/06 §6.2.

5. **`sketch_rc_nested_let_inner_scope_freed` (#114)** →
   `tests/spec_12_runtime.rs::nested_let_inner_string_freed_before_outer`.
   Cite spec/12 §12.3.

6. **`sketch_rc_vec_int_freed_on_scope_exit` (#118)** →
   `tests/spec_12_runtime.rs::vec_of_int_let_bound_freed`. Cite spec/12 §12.3.

7. **`sketch_rc_vec_empty_freed` (#119)** →
   `tests/spec_12_runtime.rs::empty_vec_let_bound_freed`. Cite spec/12 §12.3.

8. **`sketch_rc_match_temporary_scrutinee_freed` (#121)** →
   `tests/spec_12_runtime.rs::match_temporary_scrutinee_freed_on_exit`.
   Cite spec/12 §12.4.

9. **`sketch_rc_closure_capturing_closure` (#122) — REGRESSION-GUARD** →
   `tests/spec_12_runtime.rs::closure_capturing_closure_balanced`. Known
   double-free vector. Cite spec/12 §12.4.

10. **`sketch_run_tests_pass_fn_called` (#129) — REGRESSION-GUARD** →
    `tests/spec_12_runtime.rs::discover_tests_and_run_test_user_composition`.
    User-composable test-runner pattern (Sprint 60 load-bearing repro). Cite spec/04 §4.11.

11. **`sketch_platform_capture_print_hello` (#130)** →
    `tests/spec_10_io.rs::platform_print_via_test_capture` (or new spec_11_platforms.rs).
    Cite spec/11 §11.1.

12. **`sketch_platform_capture_read_input` (#131)** →
    `tests/spec_10_io.rs::platform_read_line_via_test_capture` (or new spec_11_platforms.rs).
    Cite spec/11 §11.1.

13. **`sketch_adt_display_option_int_batch` (#134)** →
    `tests/spec_07_traits.rs::polymorphic_impl_on_concrete_adt_instantiation`.
    Cite spec/07 §7.4.

14. **`sketch_boolean_literals` (#139)** →
    `tests/spec_appendix_a_builtins.rs::primitive_not_bool`. Cite appendix-a §A.3.

15. **`sigsegv_isolation_trait_impl_on_adt` (#143) — REGRESSION-GUARD** →
    `tests/spec_07_traits.rs::trait_impl_on_enum_adt_with_match_over_all_constructors`.
    Cite spec/07 §7.1.

16. **`sigsegv_isolation_default_method` (#144) — REGRESSION-GUARD** →
    consolidate with chunk-1 #38's recommendation
    (`default_method_used_when_not_overridden`) — same shape, same FIXME chain.
    Cite spec/07 §7.1.5.

17. **`sigsegv_isolation_poly_adt_impl` (#145) — REGRESSION-GUARD** →
    consolidate with #134's recommendation
    (`polymorphic_impl_on_concrete_adt_instantiation`). Cite spec/07 §7.4.

18. **`sigsegv_isolation_default_method_no_trait_call` (#146) — REGRESSION-GUARD** →
    `tests/spec_07_traits.rs::default_method_with_primitive_only_body`.
    Cite spec/07 §7.1.5.

19. **`sigsegv_isolation_trait_impl_with_trait_dispatch_in_body` (#147) — REGRESSION-GUARD** →
    `tests/spec_07_traits.rs::trait_impl_body_uses_operator`. Cite spec/07 §7.3.

(After consolidation: items #4 → chunk-2 #58, #16 → chunk-1 #38, #17 → #134.
Net new unique e2e tests recommended for chunk 3: ~13-14.)

### Tests flagged for /sprint judgment

- **#106-108 (vec-push edge cases)** — the value-at-last-index, let-binding,
  and push-onto-empty are arguably absorbed by general vec coverage. If
  `/sprint` prefers consolidating to a single `vec_push_thorough` test,
  flag.

- **#112 `sketch_list_head_tail`** — the nested-match-into-tail shape
  overlaps with chunk-2 #58 (`sketch_adt_nested_match`) — they are not
  identical (None/Some vs Cons/Nil) but the **integration angle**
  (nested match in arm body) is the same. Recommend authoring ONE
  carry-forward (`nested_match_in_arm_body`) that covers both shapes
  rather than two.

- **#129 `sketch_run_tests_pass_fn_called`** — VERIFY against
  `spec_12_runtime.rs::run_tests_reports_passes` (line 253). The
  existing test runs `(run-tests)` slash command; this test exercises
  `discover-tests` and `run-test` as separate composable primitives.
  If `/sprint` judges the slash-command path absorbs the primitive-
  composition path, downgrade to COVERED.

- **#130-131 (platform capture)** — there is no `tests/spec_11_*.rs`
  file. `/sprint` to decide whether to author in `spec_10_io.rs` or
  create a new `spec_11_platforms.rs`. The test-capture DLL availability
  guard (`Some((session, capture)) = ... else { skip }`) is harness
  code worth preserving from sketch_port.

- **#132 `sketch_platform_capture_reset_clears_state`** — marked
  GAP-HARVEST (Rust-internal harness behaviour). `/sprint` confirms.

- **#134 `sketch_adt_display_option_int_batch` ↔ #145 `sigsegv_isolation_poly_adt_impl`** —
  both exercise `(impl Showable (MyOpt Int))`; consolidate to ONE
  carry-forward test (`polymorphic_impl_on_concrete_adt_instantiation`)
  with both observation shapes (display-string + is_ok).

- **#141 `sketch_compile_both_recursive`** — flagged as composition-absorbed
  but if `/sprint` prefers an explicit `mode_equiv_recursive_factorial`
  in `build_confidence.rs`, this is the candidate.

- **#142 ↔ #148 (sigsegv_isolation pair)** — duplicate trait-impl-with-primitive-body
  shape; #148 marked DUPLICATE-IN-LEGACY (canonical is #142, which is
  COVERED by `user_trait_simple`). Confirm /sprint accepts dedupe.

- **#143-147 `sigsegv_isolation_*` (5 distinct REGRESSION-GUARD shapes)** —
  per `feedback_repros_join_suite.md`, every reproduction joins the
  test suite. Recommend authoring all 5 as failing-not-ignored where
  the underlying SIGSEGV is fixed (positive observation), and where
  the implementation is gap (e.g., #144 default-method synthesis),
  failing-not-ignored applies. /sprint decides per-test ignored vs
  active disposition.

---

## File 5 totals (all 148 tests)

| Disposition | Count |
|---|---:|
| COVERED | 109 (38 + 41 + 30) |
| DUPLICATE-IN-LEGACY | 5 (0 + 4 + 1) |
| GAP-COVER | 33 (12 + 5 + 16) (of which REGRESSION-GUARD: 17 = 6 + 2 + 9) |
| GAP-HARVEST | 1 (0 + 0 + 1) |
| **Total** | **148** |

Net unique new e2e tests recommended (after consolidations across all
3 chunks): ~22-25. The chunk-3 `sigsegv_isolation_*` cluster contributes
the largest REGRESSION-GUARD load (5 of 9 in chunk 3, 17 of 33 across
the file) — these are load-bearing repros from historical SIGSEGV defects
and should not be discarded.

## Comparison to original cluster-mode disposition

The Wave 5.6 dedupe-audit `tests/plan/wave-5.6-dedupe-audit.md §5`
estimated for `sketch_port.rs`: ~120 COVERED / ~16 DUP / ~8 GAP-COVER /
~4 GAP-HARVEST.

Per-test reality:
- COVERED: **109** (cluster estimate: ~120) — cluster mode **over-counted
  by ~11**, mostly because regression-guard tests bearing distinct
  defect-isolation framing (`sigsegv_isolation_*`, `sketch_repl_*_recovers`,
  default-method tests) were absorbed under the canonical-shape view.
- DUPLICATE-IN-LEGACY: **5** (cluster estimate: ~16) — cluster mode
  **over-counted by ~11**, by treating cluster-K accessor tests (chunk-2
  #64-65, #69-70) and the `sigsegv_isolation_trait_impl_minimal`/
  `*_with_primitive_in_body` pair as more-duplicate than the per-test
  audit confirms (some DUPs were actually COVERED via canonical e2e).
- GAP-COVER: **33** (cluster estimate: ~8) — cluster mode
  **under-counted by ~25** (4x). The largest under-resolution is the
  `sigsegv_isolation_*` cluster (7 tests) which cluster mode treated
  as a single homogeneous bundle but per-test audit reveals 5 distinct
  REGRESSION-GUARD shapes; second-largest is the RC cluster
  (10 tests with 5 GAP-COVER variants); third is the platform/
  test-capture cluster (3 tests, 2 GAP-COVER).
- GAP-HARVEST: **1** (cluster estimate: ~4) — cluster mode
  **over-counted by ~3**. Only the test-capture-reset state-API
  test is genuinely Rust-internal-harness; the others are
  language-observable e2e behaviour misclassified.

## Methodology takeaway

**Cluster-mode accuracy for sketch_port: ~73%** (109 COVERED / 148
total — direct-match dispositions). For comparison, ring0 per-test
audit confirmed cluster mode at ~97% accuracy (148/152 dispositions
matched).

The drop from ring0's 97% to sketch_port's 73% is driven by:

1. **Defect-isolation regression-guard density.** sketch_port has the
   `sigsegv_isolation_*` cluster (7 tests), the `sketch_repl_*_recovers`
   pair, the `sketch_default_method_*` triple, and the constrained-fn-
   as-value test — 12+ distinct REGRESSION-GUARD shapes that cluster
   mode collapsed to "covered by canonical trait/error tests." Per-test
   audit reveals each guards a distinct historical defect path.

2. **Per-test boundary cases.** The vec, RC, and platform clusters
   each contain 3-5 boundary cases (push-onto-empty, vec-of-Int vs
   vec-of-strings, match-temporary-scrutinee, closure-capturing-
   closure) that cluster mode absorbed under "general primitive
   coverage." Per-test audit reveals each is a distinct boundary or
   integration angle.

3. **REGRESSION-GUARD methodology (Wave 5.6 vs Wave 5.5).** Wave 5.5's
   GAP-COVER protocol surfaced 34 carry-forwards across 6 spec/repl
   files. Wave 5.6 sketch_port per-test audit surfaces **33 GAP-COVER
   in a single file** — sketch_port is by an order of magnitude the
   highest-density carry-forward source in the legacy-test universe,
   consistent with its role as the prototype-validation oracle.

The cluster-mode ~120 COVERED estimate was directionally correct on
the canonical-shape axis but under-resolved the regression-guard axis
(by ~25 GAP-COVER) and the duplicate axis (over-attributed by ~11).
**Per-test audit was warranted for sketch_port** — the cluster-mode
shortcut would have lost 17 REGRESSION-GUARD repros and 16 distinct
GAP-COVER findings.

This finding aligns with `feedback_repros_join_suite.md` and Wave 5.5's
takeaway: dedupe shortcuts under-resolve regression-guard density.
For files with high SIGSEGV-isolation / reduction-history density,
per-test audit is the right grain.

## Recommendations for /sprint

1. **Author the 22-25 net new e2e tests** identified across the 3
   chunks. Prioritise REGRESSION-GUARD class (17 across the file) —
   especially the `sigsegv_isolation_*` cluster (5 distinct shapes
   after dedupe) and the closure-capturing-closure RC test (#122).

2. **Consolidate cross-chunk overlaps** before authoring:
   - chunk-1 #38 ↔ chunk-3 #144 (default-method-used) → ONE carry-forward.
   - chunk-2 #58 ↔ chunk-3 #112 (nested-match-in-arm-body) → ONE
     carry-forward, with both Option and Cons/Nil variants OR pick
     the more-representative Cons/Nil shape.
   - chunk-3 #134 ↔ chunk-3 #145 (poly-adt-impl) → ONE carry-forward
     with both observation shapes (display + is_ok).
   - chunk-3 #142 ↔ chunk-3 #148 → drop #148 as DUP; #142 is COVERED.

3. **FIXME chains for impl-gap REGRESSION-GUARDs**:
   - default-method synthesis (chunk-1 #38-40, chunk-3 #144, #146):
     FIXME against `/typecheck` + `/backend`.
   - multi-sig type-based dispatch (chunk-1 #45): FIXME against
     `/typecheck`.
   - per `feedback_failing_not_ignored.md`, author as failing-not-ignored.

4. **`sigsegv_isolation_*` cluster (7 tests, 5 net new)** — these are
   load-bearing Sprint-N repros from historical SIGSEGV defects. The
   `sigsegv_isolation_*` prefix should be preserved in carry-forward
   names to maintain the audit-trail link to the originating sprint.

5. **Platform/test-capture handling (chunk-3 #130-132)** — `/sprint`
   to decide:
   - author in `spec_10_io.rs` (existing file) OR create
     `spec_11_platforms.rs` (no current file matches spec/11 directly).
   - the test-capture DLL availability guard (`else { skip }`) pattern
     should be preserved as a helper.

6. **GAP-HARVEST (chunk-3 #132)** — file under FIXME 0136 harvest
   protocol; not a carry-forward. Confirm inclusion in harvest target.

7. **Per-test audit methodology takeaway** — the ~73% cluster-mode
   accuracy on sketch_port (vs ring0's ~97%) confirms that for files
   with high REGRESSION-GUARD density, per-test audit is the right
   grain. Wave 5.7 (or whichever wave reaudits the remaining legacy
   files) should use per-test for any file containing
   `sigsegv_*`, `*_repro_*`, `*_S{N}_*`, `*_sprint{N}_*` naming
   patterns.

8. **DO NOT discard the per-test audit narrowing work** per
   `feedback_repros_join_suite.md`. The 33 GAP-COVER findings are the
   carry-forward authorship list; commit them as the durable record
   even if some don't make it into Wave 5.6 (carry into Wave 5.7).

