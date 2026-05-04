# Wave 5.6 file 7 ring1.rs — per-test re-audit (in progress)

Per-test re-audit of `tests/legacy/ring1.rs` (190 tests),
correcting the cluster-mode shortcut from
`tests/plan/wave-5.6-dedupe-audit.md` §7.

Authored: `/qa` (audit-only dispatch, 2026-05-04). Methodology: per-test
review against the 17 e2e carry-forward files in main, with Wave 5.6
disposition codes (COVERED / DUPLICATE-IN-LEGACY / GAP-COVER /
REGRESSION-GUARD / GAP-HARVEST). Same per-test framework as the
sketch_port, ring0, and e2e re-audits.

## Chunk 1 of 4 — tests 1-48 (`string_literal` through `adt_sum_option_none`)

Lines ~38-485. Covers:

- Strings: literals, primitives (str-concat, str-eq, str-len,
  int-to-string, float-to-string, bool-to-string), let/arg/return/if
  flow (15 tests).
- REPL strings: literal, concat, eq, int-to-string (4 tests).
- String slicing/introspection: substring, char-at, trim, to-upper/lower,
  starts-with?/ends-with?/contains?, replace, split/join (20 tests).
- ADT products: construct + match + field access + scope/arg/return
  flow + shortcut syntax (7 tests).
- ADT sums: Option Some/None constructors (2 tests).

### Summary

| Disposition | Count |
|---|---:|
| COVERED | 46 |
| DUPLICATE-IN-LEGACY | 0 |
| GAP-COVER | 2 (of which REGRESSION-GUARD: 0) |
| GAP-HARVEST | 0 |
| **Total** | **48** |

The 20 string-slicing/introspection tests in this chunk are **all
1:1 absorbed** by `tests/spec_appendix_a_builtins.rs::primitive_*`
(20 tests, all explicitly marked `(carry: legacy/ring1.rs::...)` in
their headers). This is the highest-density cluster-mode-correct
absorption visible across all four re-audits — confirms that
appendix-A-mechanically-named primitives have very tight 1:1
carry-forward shape with no edge-case angles to lose.

The 7 ADT product tests and 2 ADT sum tests are likewise tightly
absorbed by `spec_05_definitions.rs::deftype_product_*` /
`spec_06_pattern_matching.rs::pattern_*` /
`spec_12_runtime.rs::adt_*` — the ADT primitives carry forward
cleanly.

The 2 GAP-COVER candidates surface in the **string-flow** cluster
(15 string tests at lines 39-176) where some flow shapes (chained
str-concat, if-with-string-branches) are not directly carried.
These are not regression-naming patterns — they are
positive-coverage gaps surfaced by per-test review.

### NEW GAP-COVER findings

| # | Originating test | Recommended target | Angle | Type |
|---:|---|---|---|---|
| 1 | `string_concat_chained` | `tests/spec_appendix_a_builtins.rs` | nested str-concat: `(str-concat (str-concat "a" "b") "c")` — chained intermediate heap allocations through two invocations | GAP-COVER |
| 2 | `string_in_if_branches` | `tests/spec_04_expressions.rs` | `if` returning a heap-typed (String) result: `(str-len (if true "hello" "hi"))` — exercises heap-typed `if` result-value unification (distinct from int-branch tests) | GAP-COVER |

Sketches:

1. `string_concat_chained` → `primitive_str_concat_chained_two_levels`:
   ```
   repl_prims("(str-len (str-concat (str-concat \"a\" \"b\") \"c\"))\n")
       .assert_stdout_contains(":primitives/Int 3");
   ```
   Cite `spec/appendix-a-builtins.md §A.3`. Distinct from
   `primitive_str_concat` (single invocation) and from
   `let_heap_typed_results_string_concat` (let-bound composition,
   not chained inline).

2. `string_in_if_branches` → `if_branches_heap_typed_string_result`:
   ```
   repl_prims("(str-len (if true \"hello\" \"hi\"))\n")
       .assert_stdout_contains(":primitives/Int 5");
   ```
   Cite `spec/04-expressions.md §4.4`. Distinct from `if_true_branch`
   (int branches), `if_false_branch` (int branches), and
   `if_neg_branch_type_mismatch` (negative — type mismatch). The
   heap-typed if-result branches angle is not isolated elsewhere.

Verification step before authoring: grep `tests/spec_04_expressions.rs`
and `tests/spec_appendix_a_builtins.rs` to confirm the recommended
test names don't collide with existing tests.

### Per-test classifications

#### Cluster A — String literals + flow (15 tests, lines 39-176)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 1 | `string_literal` | spec/04 §4.1.4 — string literal | `(defn main [] "hello")` returns String, value "hello" | COVERED | `spec_04_expressions.rs::literal_string_basic` + `repl_introspection.rs::display_string_literal` + `spec_03_types.rs::primitive_string_display` |
| 2 | `string_empty_literal` | spec/04 §4.1.4 — empty string literal | `""` returns String, value "" | COVERED | `spec_04_expressions.rs::literal_string_empty` |
| 3 | `string_in_let` | spec/04 §4.3 — string in let scope | `(let [s "world"] (str-len s))` = 5 | COVERED | `spec_12_runtime.rs::nested_let_inner_string_freed_before_outer` covers let-scoped string lifecycle |
| 4 | `string_as_function_argument` | spec/04 §4.6 — string as fn arg | `(length "hello")` where `length` calls `str-len` | COVERED | absorbed by RC consuming-convention shape; `primitive_str_len` exercises arg-passing implicitly via the str-len call form |
| 5 | `string_as_function_return` | spec/03 §3.1 — string return type | `(greet)` returns "hello", caller `str-len`s it | COVERED | `spec_12_runtime.rs::string_returned_from_function_freed` — exact angle |
| 6 | `string_concat` | appendix-a §A.3 — str-concat primitive | `(str-len (str-concat "hello" " world"))` = 11 | COVERED | `spec_appendix_a_builtins.rs::primitive_str_concat` + `spec_12_runtime.rs::string_concat_intermediate_freed` |
| 7 | `string_eq_true` | appendix-a §A.3 — str-eq true | `(str-eq "abc" "abc")` returns 1 | COVERED | `spec_appendix_a_builtins.rs::primitive_str_eq_true` |
| 8 | `string_eq_false` | appendix-a §A.3 — str-eq false | `(str-eq "abc" "xyz")` returns 0 | COVERED | `spec_appendix_a_builtins.rs::primitive_str_eq_false` |
| 9 | `string_int_to_string` | appendix-a §A.3 — int-to-string | `(str-len (int-to-string 42))` = 2 | COVERED | `spec_appendix_a_builtins.rs::primitive_int_to_string` |
| 10 | `string_float_to_string` | appendix-a §A.3 — float-to-string | `(str-len (float-to-string 3.14))` > 0 | COVERED | absorbed by `primitive_int_to_string` parallel structure (both produce String); appendix-A coverage of int-to-string is canonical instance |
| 11 | `string_bool_to_string` | appendix-a §A.3 — bool-to-string | `(str-eq (bool-to-string true) "true")` returns 1 | COVERED | `spec_appendix_a_builtins.rs::primitive_bool_to_string` |
| 12 | `string_concat_chained` | appendix-a §A.3 — chained str-concat | `(str-concat (str-concat "a" "b") "c")` = "abc" | **GAP-COVER** | NEW — nested str-concat (two-level chained intermediate heap alloc) is not directly carried. `let_heap_typed_results_string_concat` covers let-bound composition; `primitive_str_concat` covers single invocation. The chained-inline angle is distinct. |
| 13 | `string_len` | appendix-a §A.3 — str-len primitive | `(str-len "hello")` = 5 | COVERED | `spec_appendix_a_builtins.rs::primitive_str_len` |
| 14 | `string_len_empty` | appendix-a §A.3 — str-len empty | `(str-len "")` = 0 | COVERED | absorbed by `primitive_str_len` (boundary case implicit in str-len + `literal_string_empty`); empty-string-len is a 1-line variant |
| 15 | `string_in_if_branches` | spec/04 §4.4 — if returning heap-typed value | `(str-len (if true "hello" "hi"))` = 5 | **GAP-COVER** | NEW — heap-typed (String) `if` result branches is not isolated. `if_true_branch`/`if_false_branch` use int branches; `if_neg_branch_type_mismatch` is negative. The heap-result if-unification angle is a distinct positive-coverage shape. |

#### Cluster B — REPL strings (4 tests, lines 184-218)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 16 | `repl_string_literal` | spec/04 §4.1.4 — string literal in REPL | `"hello"` returns String value "hello" | COVERED | `repl_introspection.rs::display_string_literal` (REPL-canonical shape) |
| 17 | `repl_string_concat` | appendix-a §A.3 — str-concat in REPL | `(str-concat "hello" " world")` returns "hello world" | COVERED | `spec_appendix_a_builtins.rs::primitive_str_concat` (REPL-canonical via repl_prims) |
| 18 | `repl_string_eq` | appendix-a §A.3 — str-eq in REPL | both true/false branches | COVERED | `spec_appendix_a_builtins.rs::primitive_str_eq_true` + `primitive_str_eq_false` (REPL-canonical) |
| 19 | `repl_int_to_string` | appendix-a §A.3 — int-to-string in REPL | returns String "42" | COVERED | `spec_appendix_a_builtins.rs::primitive_int_to_string` (REPL-canonical) |

#### Cluster C — String slicing / introspection (20 tests, lines 228-368)

All 20 are **explicitly marked** `(carry: legacy/ring1.rs::<name>)` in
the headers of `spec_appendix_a_builtins.rs::primitive_*` — verified
1:1 by inspection of lines 240-382. This is the densest tight-absorption
cluster across all four re-audits.

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 20 | `string_substring_basic` | appendix-a §A.3 — substring extracts range | `(substring "hello world" 6 11)` len 5 | COVERED | `primitive_substring_basic` |
| 21 | `string_substring_empty_range` | appendix-a §A.3 — substring matching idx | `(substring "hello" 2 2)` len 0 | COVERED | absorbed by `primitive_substring_basic`+`primitive_substring_clamps_end` (boundary forms); empty-range is implicit |
| 22 | `string_substring_clamps_end` | appendix-a §A.3 — substring clamps OOB end | `(substring "hello" 0 100)` len 5 | COVERED | `primitive_substring_clamps_end` |
| 23 | `string_substring_clamps_start_negative` | appendix-a §A.3 — substring clamps neg start | `(substring "hello" -5 3)` len 3 | COVERED | absorbed by `primitive_substring_clamps_end` (clamp shape covered; negative-clamp variant is symmetric); single test sufficient for clamp semantics |
| 24 | `string_char_at_valid_index` | appendix-a §A.3 — char-at | `(char-at "hello" 1)` = "e" | COVERED | `primitive_char_at_valid` |
| 25 | `string_char_at_out_of_bounds_empty` | appendix-a §A.3 — char-at OOB | `(char-at "hello" 100)` len 0 | COVERED | `primitive_char_at_out_of_bounds_empty` |
| 26 | `string_trim_whitespace` | appendix-a §A.3 — trim leading/trailing | `(trim "  hello  ")` = "hello" | COVERED | `primitive_trim_whitespace` |
| 27 | `string_trim_interior_preserved` | appendix-a §A.3 — trim interior preserved | `(trim "  hi there  ")` len 8 | COVERED | `primitive_trim_interior_preserved` |
| 28 | `string_to_upper_ascii` | appendix-a §A.3 — to-upper | `(to-upper "hello")` = "HELLO" | COVERED | `primitive_to_upper_ascii` |
| 29 | `string_to_lower_ascii` | appendix-a §A.3 — to-lower | `(to-lower "HELLO")` = "hello" | COVERED | `primitive_to_lower_ascii` |
| 30 | `string_starts_with_true` | appendix-a §A.3 — starts-with? prefix | true | COVERED | `primitive_starts_with_true` |
| 31 | `string_starts_with_false` | appendix-a §A.3 — starts-with? non-prefix | false | COVERED | `primitive_starts_with_false` |
| 32 | `string_ends_with_true` | appendix-a §A.3 — ends-with? suffix | true | COVERED | `primitive_ends_with_true` |
| 33 | `string_ends_with_false` | appendix-a §A.3 — ends-with? non-suffix | false | COVERED | `primitive_ends_with_false` |
| 34 | `string_contains_true` | appendix-a §A.3 — contains? present | true | COVERED | `primitive_contains_true` |
| 35 | `string_contains_false` | appendix-a §A.3 — contains? absent | false | COVERED | `primitive_contains_false` |
| 36 | `string_replace_multiple` | appendix-a §A.3 — replace all occurrences | `(replace "aaa" "a" "bb")` = "bbbbbb" | COVERED | `primitive_replace_multiple` |
| 37 | `string_replace_missing_needle` | appendix-a §A.3 — replace absent needle | identity | COVERED | `primitive_replace_missing_needle` |
| 38 | `string_split_produces_parts` | appendix-a §A.3 — split partitions | `(vec-len (split "a,b,c" ","))` = 3 | COVERED | `primitive_split_produces_parts` |
| 39 | `string_join_reassembles` | appendix-a §A.3 — join inverse of split | roundtrip | COVERED | `primitive_join_reassembles` |

#### Cluster D — ADT products (7 tests, lines 376-453)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 40 | `adt_product_construct_and_match` | spec/05 §5.2.1 — product type ctor + match | `(get-x (Point 3 4))` = 3 | COVERED | `spec_05_definitions.rs::deftype_product_construct_and_destructure` (canonical product carry-forward) + `spec_06_pattern_matching.rs::pattern_data_constructor_binds_fields` |
| 41 | `adt_product_get_y` | spec/05 §5.2.1 — product field access (y) | `(get-y (Point 3 4))` = 4 | COVERED | absorbed by `pattern_data_constructor_binds_fields` (which exercises both field bindings via `(add-i64 a b)`); single-field selection is parallel angle to single-field x |
| 42 | `adt_product_multi_field` | spec/05 §5.2.1 — product 3+ fields | `(sum-triple (Triple 10 20 30))` = 60 | COVERED | absorbed by `deftype_product_construct_and_destructure` (2-field) + arithmetic composition; 3-field is not a distinct spec angle (n-field is generalized) |
| 43 | `adt_product_in_let` | spec/05 §5.2.1 — product in let scope | `(let [p (Point 5 10)] (match p ...))` | COVERED | `spec_12_runtime.rs::adt_product_alloc_and_match_unwrap` covers let-anchor + match shape |
| 44 | `adt_product_as_function_arg` | spec/05 §5.2.1 — product as fn arg | `(extract-x (Point 42 99))` = 42 | COVERED | absorbed by `deftype_product_construct_and_destructure` (which threads through a destructure) + `pattern_match_in_defn_multiple_calls` |
| 45 | `adt_product_as_function_return` | spec/05 §5.2.1 — product as fn return | `(origin)` returns Point, caller matches it | COVERED | absorbed — fn-return is the dual of fn-arg, both implicit in `pattern_match_in_defn_multiple_calls` shape; calling-convention parity holds |
| 46 | `adt_shortcut_syntax` | spec/05 §5.2.4 — shortcut bare-field-name | `(deftype Pair [first second])` no `:Type` | COVERED | `spec_05_definitions.rs::deftype_product_shortcut_field_names` — exact angle |

#### Cluster E — ADT sums (2 tests, lines 461-485)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 47 | `adt_sum_option_some` | spec/05 §5.2.2 — Some constructor | `(unwrap (Some 42))` = 42 | COVERED | `spec_06_pattern_matching.rs::pattern_some_binds_value` + `spec_12_runtime.rs::adt_sum_some_alloc_and_match` (canonical Some carry-forward, exact angle) |
| 48 | `adt_sum_option_none` | spec/05 §5.2.2 — None constructor | `(unwrap None)` = 0 | COVERED | `spec_12_runtime.rs::adt_sum_none_no_heap_alloc` covers None-tag-no-heap angle (with type anchor); spec_05 + spec_06 None-branch coverage via `pattern_some_binds_value` (which has `None 0` arm). |

### GAP-COVER candidates

For follow-up authoring dispatch (NOT this audit). 2 candidates:

1. **`string_concat_chained`** → `tests/spec_appendix_a_builtins.rs`
   - Test name: `primitive_str_concat_chained_two_levels`
   - Rationale: nested str-concat through two invocations exercises
     chained intermediate heap allocations; single-invocation
     `primitive_str_concat` does not isolate this. The
     `let_heap_typed_results_string_concat` test in
     `spec_04_expressions.rs` covers let-bound composition (different
     shape — value flows through bindings, not through nested calls).
   - Cite `spec/appendix-a-builtins.md §A.3`.

2. **`string_in_if_branches`** → `tests/spec_04_expressions.rs`
   - Test name: `if_branches_heap_typed_string_result`
   - Rationale: `if` returning a heap-typed (String) value where both
     branches return String constants. `if_true_branch`/`if_false_branch`
     test int branches only; `if_neg_branch_type_mismatch` is the
     negative companion. The heap-typed positive-result if-unification
     shape is unique — exercises RC tracking on the if-result and
     unification of two heap branches.
   - Cite `spec/04-expressions.md §4.4`.

Both are pure positive-coverage gaps (not regression-naming patterns
— no `_neg_` or `_not_` shape, no source `BUG` comment, no Sprint-N
defect attribution). They are not REGRESSION-GUARD.

### Tests flagged for /sprint judgment

A small number of tests had subtle disposition calls — all marked
COVERED via composition / parallel structure rather than single-test
1:1 absorption. `/sprint` should review whether discrete carry-forward
is preferable for these:

- **#21 `string_substring_empty_range`** — empty-range substring
  (idx 2..2). Marked COVERED (boundary case implicit in
  `primitive_substring_basic` + `primitive_substring_clamps_end`).
  Discrete test would be `primitive_substring_empty_range`. Low
  importance — empty-range falls out of clamp semantics.
- **#23 `string_substring_clamps_start_negative`** — negative start
  index. Marked COVERED (clamp semantics covered by
  `primitive_substring_clamps_end`; negative-clamp is symmetric).
  Discrete test would be `primitive_substring_clamps_negative_start`.
  Note: this exercises an explicit negative-int input passed to
  substring, distinct from start>=0 + end>len. Mild ambiguity.
- **#10 `string_float_to_string`** — float-to-string primitive. Marked
  COVERED via `primitive_int_to_string` parallel structure (both
  produce String; appendix-A coverage of int variant is canonical).
  Discrete test would be `primitive_float_to_string`. Mild ambiguity
  — `primitive_int_to_string` and `primitive_bool_to_string` exist as
  discrete carries; `primitive_float_to_string` is the missing third.
  Worth flagging — likely a pre-existing GAP-COVER if the family is
  meant to be parallel.
- **#42 `adt_product_multi_field`** — 3-field product. Marked COVERED
  (n-field generalization implicit in 2-field shape). Discrete test
  would be `deftype_product_three_fields_construct_and_match`. Low
  importance.

If `/sprint` decides any of these warrant discrete carries, mark them
as additional GAP-COVER candidates and add them to the authoring
dispatch. The most-defensible candidate is **`string_float_to_string`**
(item 10) — appears to be a missing parallel-structure test for the
appendix-A `*-to-string` family.

### Cross-chunk pattern (chunk 1 signal)

Compared to ring0 (97% cluster-mode accuracy → 3 GAP-COVER),
sketch_port (75% → 25% GAP-COVER), and e2e (62% → 38% GAP-COVER)
re-audits, **chunk 1 of ring1.rs shows 96% cluster-mode accuracy**
(2 GAP-COVER out of 48). The reasons:

- 20 of 48 tests (cluster C, slicing/introspection) are
  appendix-A-mechanically-named primitives where the test names map
  1:1 to spec primitives, and `spec_appendix_a_builtins.rs` was
  authored with explicit `(carry: legacy/ring1.rs::...)` headers for
  each. Cluster mode worked perfectly here.
- 7+2 tests in clusters D/E (ADT product/sum) are absorbed by the
  tight ADT carry-forwards in `spec_05_definitions.rs` and
  `spec_06_pattern_matching.rs` plus the `spec_12_runtime.rs` ADT
  lifecycle tests. Cluster mode also worked here.
- The 2 GAP-COVER candidates are both in the **string-flow cluster**
  (cluster A, lines 39-176) where the property under test is *not* a
  primitive but a *composition* (chained call, if-result-type) that
  the spec-section files don't isolate.

**Hypothesis for remaining chunks (2-4):** ring1.rs structure is
likely "primitive-bound clusters" (string/ADT/closure primitives) +
"composition clusters" (RC, capture, scope-flow). Chunk 1 signals
that primitive-bound clusters absorb tightly (96-100%); composition
clusters likely have the GAP-COVER yield. Chunks 2-4 will show
whether closures, RC tests, and Vec/List composition tests follow
the same pattern.

If this hypothesis holds, total ring1.rs GAP-COVER yield should be
in the **5-15 range** (vs sketch_port's 25 and e2e's ~50+). Lower
density than the user-facing files, higher than ring0's pure-baseline
tests.

---

## Chunk 2 of 4 — tests 49-96 (`adt_sum_wildcard_pattern` through `dual_mode_closure_capture`)

Lines ~489-1085. Covers:

- ADT sums extended (6 tests): wildcard/var patterns, nested match, polymorphic instantiation, Either, mixed nullary+data
- REPL ADTs (5 tests): product display, sum Some/None display, REPL match
- Closures (14 tests): simple/multi/zero/multi-param capture, returned-from-fn,
  nested, with-HOF, capture-Bool, apply-twice, compose, named-fn-as-value,
  capturing-fn-arg, closure-in-if, recursive-with-HOF
- REPL closures (4 tests): simple, multi-cap, returned, display
- ADT+closure (3 tests): closure-returning-ADT, closure-with-match, ADT-with-closure-result
- String+ADT (2 tests): string-in-ADT, int-to-string-in-match-arm
- Exhaustiveness (6 tests): all-ctors, wildcard, var-pattern, non-exhaustive-panic,
  product-type, three-ctors
- Dual-mode parity (8 tests): str-len, str-eq, str-concat, int-to-string,
  ADT product/sum-some/sum-none, closure-capture

### Summary

| Disposition | Count |
|---|---:|
| COVERED | 39 |
| DUPLICATE-IN-LEGACY | 0 |
| GAP-COVER | 9 (of which REGRESSION-GUARD: 0) |
| GAP-HARVEST | 0 |
| **Total** | **48** |

The yield is **markedly higher** than chunk 1 (9 GAP-COVER vs 2). The
cluster shifts from primitive-bound (string introspection) to
composition-heavy (closure shapes, HOF combinators), and the
composition cluster has the GAP-COVER yield exactly as the chunk-1
hypothesis predicted.

The closure cluster (H, 14 tests) yields 5 of the 9 GAP-COVERs — these
are HOF combinator angles (`apply-twice`, `compose`, named-fn-as-value,
recursive-HOF, closure-in-if) that are not isolated in any
`spec_04_expressions.rs` / `spec_12_runtime.rs` carry-forward. The
existing closure carry-forwards (`lambda_closure_captures`,
`closure_capture_alloc_and_invoke`, `closure_multiple_captures`,
`lambda_passed_as_argument_invoked_inside_callee`) cover single-shot
capture + single-shot HOF only.

The REPL ADT cluster (G, 5 tests) yields 1 GAP-COVER —
`repl_adt_product` checks the **product** display format
`:user/Point (Point 3 4)` (note: parenthesised, no dot notation),
distinct from `data_constructor_applied_dot_notation_display` which
covers **sum** ctors `(Option.Some 42)`. Product ctors apparently
display without dot notation; that distinction is not isolated
elsewhere.

The REPL closure cluster (I, 4 tests) yields 1 GAP-COVER —
`repl_closure_display` checks for the literal `<closure>` token in the
value-display position. No other test asserts the `<closure>`
formatter.

The ADT+closure cluster (J, 3 tests) and string+ADT cluster (K, 2
tests) yield 1-2 GAP-COVERs each — `closure_capturing_int_returning_match_result`
exercises the `map-opt` HOF-over-Option shape (one of the canonical
Functor compositions), distinct from any covered shape;
`adt_containing_closure_result` is a closure-call inside ctor-arg
position.

The dual-mode cluster (M, 8 tests) is **all COVERED** via the
`build_confidence.rs::mode_equiv_*` framing per the canonical Wave 5.5/5.6
finding: per-feature `dual_mode_*` tests are systematically supplanted
by the mode-equiv first-class framing in `build_confidence.rs`. The
exemplars (str-concat, ADT product, closure-capture) are all covered
by `mode_equiv_primitive_arithmetic`, `mode_equiv_adt_option_match`,
`mode_equiv_let_binding`, etc.

The exhaustiveness cluster (L, 6 tests) is **all COVERED**:
`exhaustive_match_with_wildcard` ↔ `pattern_wildcard_catchall`;
`exhaustive_match_with_var_pattern` ↔ `pattern_variable_binds_value` /
`pattern_int_match_with_wildcard`; `non_exhaustive_match_panics` is
explicitly carried as `pattern_non_exhaustive_match_on_adt_neg`
(noted in its source `(carry: legacy/ring1.rs::non_exhaustive_match_panics)`);
`exhaustive_product_type` ↔ `deftype_product_construct_and_destructure`;
`match_three_constructors` ↔ `pattern_arms_type_unify` (3-arm Color match);
`exhaustive_match_all_constructors` ↔ `pattern_some_binds_value` (with
None arm).

### NEW GAP-COVER findings

| # | Originating test | Recommended target | Angle | Type |
|---:|---|---|---|---|
| 1 | `closure_apply_twice` | `tests/spec_04_expressions.rs` | HOF applies callback twice: `f(f(x))`. The double-application shape exercises closure-as-value passed through a single fn-arg slot but invoked twice in the body. Distinct from `lambda_passed_as_argument_invoked_inside_callee` (single application). | GAP-COVER |
| 2 | `closure_compose` | `tests/spec_04_expressions.rs` | Function composition `(compose f g) → λx.f(g(x))` returns a closure that captures and invokes two fn parameters. Functor-composition shape. Distinct from any single-fn HOF and from `closure_returned_from_function` (which captures only an int). | GAP-COVER |
| 3 | `named_function_as_value_apply` | `tests/spec_04_expressions.rs` | A **named defn** (not a lambda) passed as a fn-typed value to a HOF. Distinct from `lambda_passed_as_argument_invoked_inside_callee` (lambda passed) — the named-defn path may use a different code-pointer-as-value shape (closure trampoline vs direct fn-ptr). | GAP-COVER |
| 4 | `closure_in_if_branch` | `tests/spec_04_expressions.rs` | `if` returning a closure value: `(if pick (fn [x] ...) (fn [x] ...))`. Heap-typed-if-result for closure type. Distinct from chunk-1's `string_in_if_branches` GAP-COVER (heap-String-result) and from `if_*_branch` (Int-result). The closure-result shape exercises if-branch unification with closures. | GAP-COVER |
| 5 | `closure_recursive_with_higher_order` | `tests/spec_04_expressions.rs` or `tests/spec_12_runtime.rs` | Self-recursive HOF: `(repeat-fn f n x)` recurses with `f` as parameter passed through. Distinct from TCO tests (none of which thread a fn-typed parameter through self-recursion) and from any HOF test (none recurse). The fn-arg-through-self-recursion shape is unique. | GAP-COVER |
| 6 | `repl_adt_product` | `tests/repl_introspection.rs` | Product ADT value display format `:user/Point (Point 3 4)` — parenthesised, **no dot notation** for product constructors. Distinct from `data_constructor_applied_dot_notation_display` (which covers sum ctor `(Option.Some 42)`). The product-vs-sum display distinction is not isolated. | GAP-COVER |
| 7 | `repl_closure_display` | `tests/repl_introspection.rs` | Closure-as-value display: a fn returning a closure (`(make-adder 5)`) MUST display with the literal `<closure>` token. No other test asserts the `<closure>` formatter; `repl_negative.rs::display_neg_defn_not_closure` only asserts top-level defns do NOT show "closure". The positive `<closure>` display is uncovered. | GAP-COVER |
| 8 | `closure_capturing_int_returning_match_result` | `tests/spec_04_expressions.rs` or `tests/spec_06_pattern_matching.rs` | `map-opt`: Functor `(Option a → (a → b) → Option b)` — HOF over an Option. Canonical Functor.fmap shape. Distinct from any covered HOF (none operate over an ADT-shaped value with pattern matching internal). | GAP-COVER |
| 9 | `adt_containing_closure_result` | `tests/spec_05_definitions.rs` or `tests/spec_12_runtime.rs` | Closure-call result used as ctor arg: `(Some (f 41))`. Exercises the eval-order of arg vs ctor wrap, plus the heap-allocation interaction between the closure-call result temp and the ctor-allocation. Distinct from `closure_returning_adt` (closure body wraps; this has the closure call OUTSIDE the body). | GAP-COVER |

### Per-test classifications

#### Cluster F — ADT sums extended (6 tests, lines 489-574)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 49 | `adt_sum_wildcard_pattern` | spec/06 §6.2.3 — wildcard in sum match | `(match opt [(Some x) 1 _ 0])` | COVERED | `spec_06_pattern_matching.rs::pattern_wildcard_catchall` (Color/_ shape covers same wildcard semantics on a sum match) |
| 50 | `adt_sum_var_pattern` | spec/06 §6.2.4 — variable pattern in sum | `(match opt [(Some x) x other default])` | COVERED | `spec_06_pattern_matching.rs::pattern_variable_binds_value` + `pattern_int_match_with_wildcard` cover the var-pattern as a fallback arm |
| 51 | `adt_sum_nested_match` | spec/06 §6.1 — nested match | match on a in arm body matches on b | COVERED | `spec_06_pattern_matching.rs::nested_match_in_arm_body` — exact same shape (Option/Some-None nested match), explicitly carried |
| 52 | `adt_polymorphic_type` | spec/03 §3.3 — polymorphic ADT instantiation | `(Some 42)` and `(Some true)` defined as separate fns; main matches Some Int | COVERED | absorbed by `spec_03_types.rs::polymorphic_identity_at_int` + `polymorphic_identity_at_bool` (poly-instantiation shape) + `spec_05_definitions.rs::deftype_sum_with_field_match` (sum at concrete Int). Polymorphic-ADT-at-multiple-types is the composition; no isolated single-test angle missing. |
| 53 | `adt_either_type` | spec/05 §5.2.2 — sum with two data ctors | `(deftype (Either a b) (Left ...) (Right ...))` 2-type-param | COVERED | absorbed by `spec_05_definitions.rs::deftype_sum_with_field_match` (1-param sum) + the polymorphic-impl shape in `spec_07_traits.rs::polymorphic_impl_on_concrete_adt_instantiation` (multi-ctor poly). 2-type-param Either is composition of 1-param sum behaviour with poly machinery; no distinct sub-spec angle. |
| 54 | `adt_enum_mixed_nullary_and_data` | spec/05 §5.2.2 — mixed nullary+data | `(deftype (Result a) Ok (Err [:a val]))` Ok=nullary, Err=data | COVERED | `spec_05_definitions.rs::deftype_sum_with_field_match` covers data ctor; `deftype_enum_construct_and_match` covers nullary ctor; the mixed shape is implicit in the standard Option/Some-None shape (None=nullary, Some=data) extensively covered. |

#### Cluster G — REPL ADTs (5 tests, lines 582-634)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 55 | `repl_adt_product` | repl/spec.md §1.5 — product value display | `:user/Point (Point 3 4)` parenthesised, no dot notation | **GAP-COVER** | NEW — product-ctor value display format is **distinct** from sum-ctor display. `data_constructor_applied_dot_notation_display` covers `(Option.Some 42)` (sum, dot-notation). Product display `(Point 3 4)` (no dot) is not isolated. |
| 56 | `repl_adt_sum_some` | repl/spec.md §1.5 — sum Some value display | `:(user/Option primitives/Int) (Option.Some 42)` | COVERED | `repl_introspection.rs::data_constructor_applied_dot_notation_display` — exact same angle |
| 57 | `repl_adt_sum_none` | repl/spec.md §1.5 — sum None value display | `Option.None` | COVERED | `repl_introspection.rs::nullary_constructor_bare_lookup_dot_notation` (Color.Red same shape) + `prelude_option_none_value_display_neg_definition_metadata` |
| 58 | `repl_adt_match` | spec/06 §6.1 — match in REPL | `(match (Some 99) ...)` returns 99 | COVERED | `spec_06_pattern_matching.rs::pattern_some_binds_value` is REPL-canonical via `repl_prims`; same shape |
| 59 | `repl_adt_product_match` | spec/06 §6.2.1 — Point match in REPL | `(match (Point 7 8) [(Point x y) x])` returns 7 | COVERED | `spec_05_definitions.rs::deftype_product_construct_and_destructure` is REPL-canonical via `repl_prims` (Point match → 7); exact angle |

#### Cluster H — Closures (14 tests, lines 642-799)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 60 | `closure_simple_capture` | spec/04 §4.5.1 — simple capture | `(let [n 10] ((fn [x] (add-i64 n x)) 32))` | COVERED | `spec_12_runtime.rs::closure_capture_alloc_and_invoke` — exact source body, exact shape |
| 61 | `closure_multiple_captures` | spec/04 §4.5.1 — multiple captures | 3 captures (a/b/c) | COVERED | `spec_12_runtime.rs::closure_multiple_captures` — exact 3-capture shape |
| 62 | `closure_returned_from_function` | spec/04 §4.5.1 — closure returned from fn | `make-adder` pattern | COVERED | `spec_04_expressions.rs::lambda_closure_captures` — exact `make-add`/`make-adder` pattern |
| 63 | `closure_nested` | spec/04 §4.5.1 — nested closures | three nesting levels (let / let / let f / let g) | COVERED | absorbed by `lambda_closure_captures` (closure-from-let) + `lambda_bound_in_let_and_called` (let-bound lambda); 3-level nesting is composition |
| 64 | `closure_with_higher_order` | spec/04 §4.6 — closure to HOF | `apply-fn` + capture | COVERED | absorbed by `lambda_passed_as_argument_invoked_inside_callee` (lambda to HOF) + `lambda_closure_captures` (capture); composition shape |
| 65 | `closure_zero_param` | spec/04 §4.5 — zero-param closure with capture | `((fn [] x))` capturing x=42 | COVERED | absorbed by `lambda_zero_args` (zero-arg lambda) + `closure_capture_alloc_and_invoke` (capture); zero-arg-with-capture is composition |
| 66 | `closure_multi_param` | spec/04 §4.5 — multi-param closure with capture | `((fn [a b] ...) 1 2)` capturing base=100 | COVERED | absorbed by `lambda_multi_args` (multi-param lambda) + `closure_capture_alloc_and_invoke` (capture); composition |
| 67 | `closure_capturing_bool` | spec/04 §4.5.1 — closure capturing Bool | flag=true used in `if` inside closure | COVERED | absorbed by `closure_capture_alloc_and_invoke` (Int capture) — Bool capture is the same i64-typed slot at runtime; spec angle "captured value type" not distinct |
| 68 | `closure_apply_twice` | spec/04 §4.6 — HOF applies closure twice | `(apply-twice f x) → (f (f x))` | **GAP-COVER** | NEW — double-application shape not isolated. `lambda_passed_as_argument_invoked_inside_callee` is single application. The f(f(x)) form exercises closure invariance + repeat-invocation. |
| 69 | `closure_compose` | spec/04 §4.5.1 — function composition | `(compose f g) → (fn [x] (f (g x)))` returns closure | **GAP-COVER** | NEW — composition shape (Functor.compose) not isolated. Returns a closure that captures TWO fn-typed values. Distinct from any covered HOF. |
| 70 | `named_function_as_value_apply` | spec/12 §12.2.3 — named fn as value | `(apply-fn inc 41)` where `inc` is a named defn | **GAP-COVER** | NEW — named-defn-passed-as-value path may differ from lambda-passed (closure-trampoline vs direct fn-ptr). `lambda_passed_as_argument_invoked_inside_callee` is lambda-passed; the named-fn-as-value angle is uncovered. |
| 71 | `closure_capturing_function_arg` | spec/04 §4.5.1 — closure capturing fn arg | `make-fn` + apply twice | COVERED | absorbed by `lambda_closure_captures` (`make-add` shape) + apply-twice angle (which is GAP-COVER #1, but at the closure-creation level this test is covered) |
| 72 | `closure_in_if_branch` | spec/04 §4.4 — `if` returning closure value | `(if pick (fn ...) (fn ...))` | **GAP-COVER** | NEW — heap-typed (closure) `if` result is distinct from chunk-1 GAP-COVER `string_in_if_branches` (String-typed) and from `if_*_branch` (Int-typed). Closure-result if-unification is uncovered. |
| 73 | `closure_recursive_with_higher_order` | spec/04 §4.6 — recursive HOF | `repeat-fn` self-recurses with `f` as param | **GAP-COVER** | NEW — fn-arg threaded through self-recursion. TCO tests don't pass fn through; HOF tests don't recurse. The combined shape is uncovered. |

#### Cluster I — REPL closures (4 tests, lines 808-849)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 74 | `repl_closure_simple` | spec/04 §4.5.1 — simple closure in REPL | `(let [n 10] ((fn [x] (add-i64 n x)) 32))` | COVERED | `spec_12_runtime.rs::closure_capture_alloc_and_invoke` is REPL-canonical via repl_prims; same shape |
| 75 | `repl_closure_multiple_captures` | spec/04 §4.5.1 — multi-cap REPL | `(let [a 1 b 2] ...)` | COVERED | `spec_04_expressions.rs::lambda_closure_multi_captures` — REPL-canonical, exact shape |
| 76 | `repl_closure_returned` | spec/04 §4.5.1 — closure returned in REPL | `make-adder` | COVERED | `spec_04_expressions.rs::lambda_closure_captures` — REPL-canonical via repl_prims, same `make-add` shape |
| 77 | `repl_closure_display` | repl/spec.md §1.2 — closure display format | `<closure>` token in display | **GAP-COVER** | NEW — positive `<closure>` formatter assertion. Only `repl_negative.rs::display_neg_defn_not_closure` exists, asserting absence on top-level defn. The positive shape (closure-from-make-adder displays `<closure>`) is uncovered. |

#### Cluster J — ADT + closure interactions (3 tests, lines 858-898)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 78 | `closure_returning_adt` | spec/04 §4.5.1 — closure returning ADT | `(make-some n) → (fn [] (Some n))` | COVERED | absorbed by `lambda_closure_captures` (closure capturing) + `pattern_some_binds_value` (ADT match unwrap); composition shape |
| 79 | `closure_capturing_int_returning_match_result` | spec/04 §4.5.1 — HOF over ADT (map-opt) | `(map-opt opt f)` Functor.fmap | **GAP-COVER** | NEW — Functor.fmap shape over Option. Distinct from any covered HOF (none operate over an ADT with internal pattern match) and from any covered closure shape (none flow a closure into an ADT-aware fn). Canonical Functor angle. |
| 80 | `adt_containing_closure_result` | spec/05 §5.2.2 — ADT containing closure-call result | `(Some (f 41))` ctor-arg is closure call | **GAP-COVER** | NEW — closure-call result as ctor arg position. Distinct from `closure_returning_adt` (closure body wraps in ctor, here ctor is OUTSIDE the closure body). Exercises eval-order + heap-temp lifetime through ctor wrap. |

#### Cluster K — String + ADT interactions (2 tests, lines 907-929)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 81 | `string_in_adt` | spec/05 §5.2.2 — String field in ADT | `(Some "hello")` then match | COVERED | `spec_12_runtime.rs::adt_with_string_field_freed` — exact `(Some "hello")` shape, includes RC angle |
| 82 | `string_from_int_to_string_in_match` | spec/06 §6.1 — int-to-string in match arm | `(int-to-string n)` inside arm body | COVERED | absorbed by `spec_appendix_a_builtins.rs::primitive_int_to_string` + `pattern_some_binds_value`; composition shape, no distinct sub-spec angle |

#### Cluster L — Exhaustiveness (6 tests, lines 938-1018)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 83 | `exhaustive_match_all_constructors` | spec/06 §6.5.1 — exhaustive all ctors | None + Some both covered | COVERED | `spec_06_pattern_matching.rs::pattern_some_binds_value` (which has both arms) + `pattern_match_in_defn_multiple_calls`; standard exhaustive shape |
| 84 | `exhaustive_match_with_wildcard` | spec/06 §6.5.1 — exhaustive via wildcard | `[Red 1 _ 0]` | COVERED | `spec_06_pattern_matching.rs::pattern_wildcard_catchall` — exact shape |
| 85 | `exhaustive_match_with_var_pattern` | spec/06 §6.5.1 — exhaustive via var-pattern | `[Red 0 other 1]` | COVERED | `pattern_variable_binds_value` (var binds scrutinee) + `pattern_int_match_with_wildcard` (var-as-fallback shape); composition |
| 86 | `non_exhaustive_match_panics` | spec/06 §6.5.3 — runtime safety net | `(match opt [(Some x) x])` no None arm; expects panic | COVERED | `spec_06_pattern_matching.rs::pattern_non_exhaustive_match_on_adt_neg` — explicitly carries `(carry: legacy/ring1.rs::non_exhaustive_match_panics)`; recategorised to compile-time error per §6.5.1 with §6.5.3 fallback |
| 87 | `exhaustive_product_type` | spec/06 §6.5.1 — product exhaustive (1 ctor) | `(match p [(Point x y) ...])` | COVERED | `spec_05_definitions.rs::deftype_product_construct_and_destructure` (Point match) — same shape |
| 88 | `match_three_constructors` | spec/06 §6.5.1 — 3-ctor exhaustive | Color Red/Green/Blue all covered | COVERED | `spec_06_pattern_matching.rs::pattern_arms_type_unify` (Color all-3-arm match) — exact shape |

#### Cluster M — Dual-mode parity (8 tests, lines 1026-1085)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 89 | `dual_mode_string_len` | mode-equiv str-len | batch+REPL parity | COVERED | absorbed by `build_confidence.rs::mode_equiv_*` framing per the canonical Wave 5.5/5.6 finding (per-feature `dual_mode_*` tests are systematically supplanted) |
| 90 | `dual_mode_string_eq` | mode-equiv str-eq | batch+REPL parity | COVERED | absorbed by `build_confidence.rs::mode_equiv_*` framing |
| 91 | `dual_mode_string_concat` | mode-equiv str-concat | batch+REPL parity | COVERED | absorbed by `build_confidence.rs::mode_equiv_*` framing |
| 92 | `dual_mode_int_to_string` | mode-equiv int-to-string | batch+REPL parity | COVERED | absorbed by `build_confidence.rs::mode_equiv_*` framing |
| 93 | `dual_mode_adt_product` | mode-equiv product type | batch+REPL parity | COVERED | absorbed by `build_confidence.rs::mode_equiv_adt_option_match` (ADT mode-equiv covered; product is parallel) |
| 94 | `dual_mode_adt_sum_some` | mode-equiv sum Some | batch+REPL parity | COVERED | absorbed by `build_confidence.rs::mode_equiv_adt_option_match` — exact Some/None shape |
| 95 | `dual_mode_adt_sum_none` | mode-equiv sum None | batch+REPL parity | COVERED | absorbed by `build_confidence.rs::mode_equiv_adt_option_match` |
| 96 | `dual_mode_closure_capture` | mode-equiv closure | batch+REPL parity | COVERED | absorbed by `build_confidence.rs::mode_equiv_let_binding` + `closure_capture_alloc_and_invoke` (REPL via repl_prims, same body); the dual-mode framing is supplanted |

### GAP-COVER candidates

For follow-up authoring dispatch (NOT this audit). 9 candidates:

1. **`closure_apply_twice`** → `tests/spec_04_expressions.rs`
   - Test name: `lambda_passed_as_argument_invoked_twice_inside_callee`
   - Rationale: HOF that invokes its fn-typed parameter **twice**:
     `(apply-twice f x) → (f (f x))`. Distinct from the single-shot
     `lambda_passed_as_argument_invoked_inside_callee`. The double-call
     shape exercises closure-as-value invariance under repeat invocation
     (no per-call cleanup in the HOF body must drop or shadow the
     captured values).
   - Cite `spec/04-expressions.md §4.6`.

2. **`closure_compose`** → `tests/spec_04_expressions.rs`
   - Test name: `closure_composition_returns_capturing_two_fn_args`
   - Rationale: `(compose f g) → (fn [x] (f (g x)))` — Functor
     composition. The returned closure captures **two fn-typed values**.
     Distinct from `lambda_closure_captures` (Int capture) and from
     `closure_returned_from_function` shape; the multi-fn-typed-capture
     angle is uncovered.
   - Cite `spec/04-expressions.md §4.5.1`.

3. **`named_function_as_value_apply`** → `tests/spec_04_expressions.rs`
   - Test name: `named_defn_passed_as_value_to_higher_order_fn`
   - Rationale: a **named defn** (not a lambda) used as a fn-typed
     value at a HOF call site. The codegen path for defn-as-value may
     differ from lambda-as-value (direct code-pointer vs closure
     trampoline), so this exercises a distinct reification path.
   - Cite `spec/12-runtime.md §12.2.3` or `spec/04-expressions.md §4.5`.

4. **`closure_in_if_branch`** → `tests/spec_04_expressions.rs`
   - Test name: `if_branches_heap_typed_closure_result`
   - Rationale: `(if pick (fn [x] ...) (fn [x] ...))` returns a closure;
     both branches have closure type. Heap-typed if-result for
     **closure** type — distinct from chunk-1's GAP-COVER
     `if_branches_heap_typed_string_result` (String result) and from
     `if_*_branch` (Int result). Closure-result branches exercise
     closure-pointer unification.
   - Cite `spec/04-expressions.md §4.4`.

5. **`closure_recursive_with_higher_order`** → `tests/spec_12_runtime.rs`
   - Test name: `tco_self_recursion_with_fn_typed_parameter`
   - Rationale: self-recursive HOF threading a fn-typed parameter
     through each call: `(repeat-fn f n x) → (repeat-fn f (sub-i64 n
     1) (f x))`. None of the existing TCO tests pass a fn through
     self-recursion; none of the HOF tests recurse. The combined
     shape exercises TCO interaction with fn-arg layout (the closure
     value must survive across the loop-back jump).
   - Cite `spec/12-runtime.md §12.5` or `spec/04-expressions.md §4.6`.

6. **`repl_adt_product`** → `tests/repl_introspection.rs`
   - Test name: `data_constructor_product_no_dot_notation_display`
   - Rationale: product ADT value displays as
     `:user/Point (Point 3 4)` — parenthesised, **no dot notation**
     (contrast `(Option.Some 42)` for sum ctors). The product-vs-sum
     display distinction is not isolated in any existing test.
   - Cite `repl/spec.md §1.5`.

7. **`repl_closure_display`** → `tests/repl_introspection.rs`
   - Test name: `closure_value_display_shows_closure_token`
   - Rationale: a closure-as-value MUST display with `<closure>` in
     the value position. Only the negative companion exists
     (`display_neg_defn_not_closure`); the positive shape is
     uncovered.
   - Cite `repl/spec.md §1.2`.

8. **`closure_capturing_int_returning_match_result`** → `tests/spec_06_pattern_matching.rs` or `tests/spec_04_expressions.rs`
   - Test name: `higher_order_fn_over_option_functor_map_shape`
   - Rationale: `(map-opt opt f) → (match opt [(Some x) (Some (f x)) None None])`
     is the Functor.fmap canonical shape. HOF that traverses an ADT
     with internal pattern match. Distinct from any covered HOF
     (none traverse an ADT) and from any covered match (none invoke
     a fn-typed parameter inside an arm body).
   - Cite `spec/06-pattern-matching.md §6.1` or `spec/04-expressions.md §4.6`.

9. **`adt_containing_closure_result`** → `tests/spec_05_definitions.rs` or `tests/spec_12_runtime.rs`
   - Test name: `data_constructor_arg_from_closure_call_result`
   - Rationale: `(Some (f 41))` — closure-call result as ctor arg
     position. Exercises temp-lifetime + heap-allocation interaction
     (the closure-call result is consumed by ctor wrap before the
     match is reached). Distinct from `closure_returning_adt`
     (closure body wraps in ctor — opposite ordering: ctor wrap
     happens INSIDE the closure call here).
   - Cite `spec/05-definitions.md §5.2.2` or `spec/12-runtime.md §12.3.1`.

All 9 are pure positive-coverage gaps (no `_neg_` shape, no source `BUG`
comment, no Sprint-N defect attribution). They are not REGRESSION-GUARD.

Verification step before authoring: grep target files for the
recommended test names to confirm no collisions with existing tests.

### Tests flagged for /sprint judgment

A small number of tests had subtle disposition calls; `/sprint` should
review whether the COVERED disposition is sufficient or whether
discrete carry-forward is preferable:

- **#52 `adt_polymorphic_type`** — polymorphic ADT instantiated at
  Int and Bool via two separate defns. Marked COVERED via
  composition (`polymorphic_identity_at_int/bool` for poly + Option
  shape for ADT). Discrete test would be
  `polymorphic_adt_instantiated_at_two_concrete_types`. Mild
  ambiguity — the spec/03 §3.3 angle is exercised by
  `polymorphic_identity_at_int/bool`, but the two-defn-with-different-Option-types
  shape is a distinct compile-time-monomorphisation angle for ADTs.
- **#53 `adt_either_type`** — 2-type-param sum (Either a b). Marked
  COVERED via composition. Discrete test would be
  `deftype_sum_two_type_parameters`. Mild ambiguity — the
  type-param-arity-2 boundary is not isolated.
- **#54 `adt_enum_mixed_nullary_and_data`** — Result a = Ok | (Err a).
  Marked COVERED — Option/Some-None has the same nullary+data shape.
  Low importance.
- **#67 `closure_capturing_bool`** — closure capturing a Bool. Marked
  COVERED — at the runtime level, Bool occupies the same i64 slot as
  Int, so the capture path is identical. If `/sprint` thinks captured
  type-shape distinctions matter at the spec level, a discrete carry
  would be `closure_capturing_bool_value_preserved`. Mild ambiguity.
- **#82 `string_from_int_to_string_in_match`** — int-to-string inside
  a match arm body. Marked COVERED via composition. Discrete test
  would be `int_to_string_in_match_arm_body`. Low importance.

### Cross-chunk pattern (chunk 2 signal)

Chunk 1 (tests 1-48): 96% cluster-mode accuracy → 2 GAP-COVER (4%).
Chunk 2 (tests 49-96): 81% cluster-mode accuracy → 9 GAP-COVER (19%).

The chunk-1 hypothesis ("primitive-bound clusters absorb tightly,
composition clusters yield GAP-COVER") is **strongly confirmed**:

- Cluster F (ADT sums extended): 0 GAP-COVER — primitive-bound (each
  test maps to a single spec-defined pattern shape). 100% cluster-mode.
- Cluster G (REPL ADTs): 1 GAP-COVER — primitive-bound except for the
  product-vs-sum display distinction.
- Cluster H (closures, 14 tests): 5 GAP-COVER — composition-heavy,
  HOF combinator angles. **64% cluster-mode accuracy** — the lowest
  in the chunk.
- Cluster I (REPL closures): 1 GAP-COVER — primitive-bound except for
  the `<closure>` formatter assertion.
- Cluster J (ADT+closure): 2 GAP-COVER — composition cluster.
- Cluster K (String+ADT): 0 GAP-COVER — composition shape that maps
  exactly to `adt_with_string_field_freed`.
- Cluster L (exhaustiveness, 6 tests): 0 GAP-COVER — all map 1:1 to
  pattern_* in spec_06.
- Cluster M (dual-mode, 8 tests): 0 GAP-COVER — all systematically
  supplanted by `mode_equiv_*` framing.

**Hypothesis adjustment for chunks 3-4:** the GAP-COVER yield is
driven by **closure HOF combinator angles** (5 of 9 in chunk 2). If
chunks 3-4 contain comparable closure/HOF clusters, expect another
~5 GAP-COVERs per chunk; if chunks 3-4 are mostly RC, TCO, error,
or polymorphism tests (more primitive-bound), expect 1-3 GAP-COVERs
per chunk.

**Updated total ring1.rs GAP-COVER yield estimate:** chunk 1 (2) +
chunk 2 (9) = 11 so far. Chunks 3-4 likely add 3-10 more, putting
the total in the **14-21 range** — at the high end of the chunk-1
"5-15" hypothesis or slightly above. This is comparable to
sketch_port (25 GAP-COVER) but higher than ring0 (3 GAP-COVER),
consistent with ring1.rs having more composition coverage than
ring0's pure-baseline tests.

---

## Chunk 3 of 4 — tests 97-144 (`dual_mode_closure_returned` through `vec_set_first`)

Lines ~1089-1631. Covers:

- Dual-mode parity (7 tests): closure-returned, HOF, named-fn-as-value,
  match-with-field-bindings, enum-match, lambda-immediate, lambda-in-let
- Error paths (7 tests): type-mismatch String/Int both directions, ADT
  ctor wrong arg count + wrong type, if-branches mismatch, closure arity,
  undefined ctor
- Let-polymorphism with closures (6 tests): let-bound id at multiple types,
  polymorphic HOF, let-bound λ with capture, identity on String / on ADT,
  HOF on ADT
- parse-int (2 tests): valid input, invalid input
- Misc / TCO / composition (6 tests): closure+TCO (fold), ADT-in-TCO,
  string-in-recursive-fn, multiple-ADT-defs, closure-over-closure,
  let-bound-ADT-and-closure
- Vec (20 tests): literals (Int/empty/Strings), get (first/last/middle),
  set/set-preserves-others, push (appends/value/empty), len (zero/three),
  in-let, in-defn, of-Strings (×2), of-ADTs (×2), set-first

### Summary

| Disposition | Count |
|---|---:|
| COVERED | 32 |
| DUPLICATE-IN-LEGACY | 1 |
| GAP-COVER | 15 (of which REGRESSION-GUARD: 0) |
| GAP-HARVEST | 0 |
| **Total** | **48** |

The yield is **the highest of any chunk so far** (15 GAP-COVER vs
chunk 1's 2 and chunk 2's 9). The cluster shifts again — this chunk
contains the **error-paths cluster** (cluster O, 7 tests) and the
**parse-int cluster** (cluster Q, 2 tests), neither of which has tight
1:1 carry-forward in the spec-anchored e2e suite. The error-paths
cluster yields 5 of the 15 GAP-COVERs (the negative-coverage tests for
ADT-ctor-arity, ADT-ctor-wrong-type, closure-arity, undefined-ctor,
str-len-on-Int), and the parse-int cluster yields both tests as
GAP-COVER (zero parse-int coverage in any e2e file).

The vec cluster (S, 20 tests) yields 5 GAP-COVERs — heap-typed-vec
shapes (Vec of String, Vec of ADT) and middle-vs-last positional
discrimination are not isolated. The vec-primitives 1:1 carry-forward
shape (cluster A in chunk 1) only covered len/get-first/push/set with
Int-typed elements; Vec-of-heap-element angles are uncovered.

The polymorphism-with-closures cluster (P, 6 tests) yields 3 GAP-COVERs
— `id` applied to String, `id` applied to ADT, and HOF on ADT all
exercise polymorphism at heap types. `polymorphic_identity_at_int/bool`
cover only Int/Bool; the heap-type instantiations are a distinct angle.

One **DUPLICATE-IN-LEGACY** finding: `closure_and_tco` (test 119,
fold pattern via TCO with HOF) **duplicates** the chunk-2 GAP-COVER
candidate `closure_recursive_with_higher_order` (test 73). Both
exercise self-recursion threading a fn parameter; `closure_and_tco`
adds the deep-recursion (n=100) angle but is otherwise the same
shape. Recommend consolidation in any follow-up dispatch — the
combined test should cover both shapes.

The dual-mode cluster (N, 7 tests) is **all COVERED** via the
`build_confidence.rs::mode_equiv_*` framing (consistent with
chunk 2). The TCO sub-cluster within Misc (R) is mostly COVERED via
`spec_12_runtime.rs::tco_*` tests (currently `#[ignore]` pending FIXME
0141 — TCO MUST clause not yet in spec — but the shapes are present).

### NEW GAP-COVER findings

| # | Originating test | Recommended target | Angle | Type |
|---:|---|---|---|---|
| 1 | `error_int_where_string_expected` | `tests/spec_03_types.rs` | `(str-len 42)` — passing Int where String expected. Mirror of `unification_int_vs_string_errors` (which is if-branches Int vs String). The fn-arg-type-mismatch direction (Int → String slot) is not isolated; only the if-branches form is covered. | GAP-COVER |
| 2 | `error_adt_constructor_wrong_arg_count` | `tests/spec_05_definitions.rs` | `(Point 1)` where Point expects 2 args. Constructor arity mismatch. No spec_05 test exercises ADT constructor arity rejection; `defn_multi_clause_arity` covers multi-clause defn arity, not ctor arity. | GAP-COVER |
| 3 | `error_adt_constructor_wrong_type` | `tests/spec_05_definitions.rs` | `(Point true 2)` where Point expects `:Int x :Int y`. Constructor argument type mismatch. The product-ctor-type-check angle is not isolated — `deftype_product_construct_and_destructure` is positive only. | GAP-COVER |
| 4 | `error_closure_arity_mismatch` | `tests/spec_04_expressions.rs` | `((fn [x] x) 1 2)` — calling 1-arg closure with 2 args. Application-arity rejection for closures. Distinct from `defn_multi_clause_arity` (which dispatches between clauses, not rejects). | GAP-COVER |
| 5 | `error_undefined_constructor` | `tests/spec_05_definitions.rs` | `(Foo 1 2)` — Foo never defined. Undefined-constructor lookup error. Distinct from `variable_reference_unbound_errors` — constructor lookup is a different code path (constructor table vs symbol table). | GAP-COVER |
| 6 | `let_bound_lambda_with_capture` | `tests/spec_04_expressions.rs` | `(let [base 100 f (fn [x] (add-i64 base x))] (add-i64 (f 1) (f 2)))` — let-bound captured closure invoked **twice with different args** (not f(f(x)); two independent calls). Distinct from chunk-2's `closure_apply_twice` (f(f(x)) shape) — this is f(a) + f(b). Captured-closure-invariance under independent calls. | GAP-COVER |
| 7 | `identity_on_string` | `tests/spec_03_types.rs` | `(id "hello")` — polymorphic identity at String. `polymorphic_identity_at_int/bool` cover Int/Bool; String is the heap-type counterpart. Distinct angle (heap-typed instantiation). | GAP-COVER |
| 8 | `identity_on_adt` | `tests/spec_03_types.rs` | `(id (Some 42))` — polymorphic identity at ADT type. Distinct from String identity (Vec/closure are also heap but ctor-driven, not literal-driven). The id-at-ADT angle exercises poly instantiation at a user-defined type. | GAP-COVER |
| 9 | `higher_order_on_adt` | `tests/spec_03_types.rs` or `tests/spec_04_expressions.rs` | `(apply-fn (fn [x] (Some x)) 42)` — HOF returning ADT. Composition: poly HOF + ADT-returning closure. Distinct from any covered HOF (none return ADTs). | GAP-COVER |
| 10 | `parse_int_valid` | `tests/spec_appendix_a_builtins.rs` | `(parse-int "42")` returns `(Some 42)`. Zero parse-int coverage in any e2e file. Per spec/appendix-a-builtins.md §A.3, parse-int is a primitive returning `(Option Int)`. | GAP-COVER |
| 11 | `parse_int_invalid` | `tests/spec_appendix_a_builtins.rs` | `(parse-int "not-a-number")` returns None. Negative companion to #10. | GAP-COVER |
| 12 | `vec_set_preserves_other_elements` | `tests/spec_appendix_a_builtins.rs` or `tests/spec_12_runtime.rs` | After `(vec-set [10 20 30] 1 99)`, position 0 still holds 10 and position 2 still holds 30. Distinct from `primitive_vec_set_preserves_len` (asserts length only) and from `vec_set_cow_preserves_original` (asserts original-vec untouched, not new-vec other-positions). The other-positions-of-the-set-result angle is a distinct positive shape. | GAP-COVER |
| 13 | `vec_of_strings_get` | `tests/spec_03_types.rs` or `tests/spec_appendix_a_builtins.rs` | `(vec-get ["hello" "world"] 0)` returns "hello"; `str-len` of result = 5. Vec-of-heap-typed-element-access. The `Vec<String>` shape is not isolated — `primitive_vec_get_first` uses Int elements. Heap-element-vec is a distinct RC-aware angle. | GAP-COVER |
| 14 | `vec_of_adts` | `tests/spec_05_definitions.rs` or `tests/spec_12_runtime.rs` | Vec containing ADT values: `[(Some 1) None (Some 3)]`, vec-get + match. Heap-element vec with mixed-tag ADTs. Distinct from all covered shapes. Exercises ADT-in-vec lifetime + dispatch through match after vec-get. | GAP-COVER |
| 15 | `vec_get_middle` | `tests/spec_appendix_a_builtins.rs` | `(vec-get [10 20 30] 1)` — middle index. `primitive_vec_get_first` covers index 0 only. Middle-vs-end positional indexing is not asserted; the get-by-index code path is the same but the test family (first/middle/last) is conventionally coverage-distinct. **Mild ambiguity** — flagged for /sprint judgment. | GAP-COVER |

Sketches:

1. `error_int_where_string_expected` → `unification_int_passed_to_string_arg_errors`:
   ```
   let out = repl_prims("(str-len 42)\n");
   assert!(out.stdout.contains("Int") || out.stdout.contains("String") || out.stderr.contains("type"));
   ```
   Cite `spec/03-types.md §3.5` or `§3.8`.

2. `error_adt_constructor_wrong_arg_count` → `deftype_product_constructor_arity_mismatch_neg`:
   ```
   let out = repl_prims("(deftype Point [:Int x :Int y])\n(Point 1)\n");
   assert!(out.stderr.contains("error") || out.stdout.contains("error") || out.stdout.contains("arg"));
   ```
   Cite `spec/05-definitions.md §5.2.7`.

3. `error_adt_constructor_wrong_type` → `deftype_product_constructor_wrong_arg_type_neg`:
   ```
   let out = repl_prims("(deftype Point [:Int x :Int y])\n(Point true 2)\n");
   assert!(out.stdout.contains("Bool") || out.stdout.contains("Int") || out.stderr.contains("type"));
   ```
   Cite `spec/05-definitions.md §5.2.7`.

4. `error_closure_arity_mismatch` → `lambda_call_with_wrong_arg_count_neg`:
   ```
   let out = repl_prims("(let [f (fn [x] x)] (f 1 2))\n");
   assert!(out.stderr.contains("error") || out.stdout.contains("arity") || out.stdout.contains("arg"));
   ```
   Cite `spec/04-expressions.md §4.5`.

5. `error_undefined_constructor` → `data_constructor_undefined_lookup_neg`:
   ```
   let out = repl_prims("(Foo 1 2)\n");
   assert!(out.stderr.contains("Foo") || out.stdout.contains("Foo") || out.stdout.contains("undefined") || out.stderr.contains("error"));
   ```
   Cite `spec/04-expressions.md §4.2.1` or `spec/05-definitions.md §5.2`.

6. `let_bound_lambda_with_capture` → `let_bound_capturing_lambda_invoked_with_independent_args`:
   ```
   repl_prims("(let [base 100 f (fn [x] (add-i64 base x))] (add-i64 (f 1) (f 2)))\n")
       .assert_stdout_contains(":primitives/Int 203");
   ```
   Cite `spec/04-expressions.md §4.5.1`.

7. `identity_on_string` → `polymorphic_identity_at_string`:
   ```
   repl_prims("(defn id [x] x)\n(str-len (id \"hello\"))\n")
       .assert_stdout_contains(":primitives/Int 5");
   ```
   Cite `spec/03-types.md §3.3`.

8. `identity_on_adt` → `polymorphic_identity_at_adt`:
   ```
   repl_prims("(deftype (Option a) None (Some [:a val]))\n(defn id [x] x)\n(match (id (Some 42)) [(Some x) x None 0])\n")
       .assert_stdout_contains(":primitives/Int 42");
   ```
   Cite `spec/03-types.md §3.3`.

9. `higher_order_on_adt` → `polymorphic_higher_order_returning_adt`:
   ```
   repl_prims("(deftype (Option a) None (Some [:a val]))\n(defn apply-fn [f x] (f x))\n(match (apply-fn (fn [x] (Some x)) 42) [(Some x) x None 0])\n")
       .assert_stdout_contains(":primitives/Int 42");
   ```
   Cite `spec/04-expressions.md §4.6` or `spec/03-types.md §3.3`.

10. `parse_int_valid` → `primitive_parse_int_valid`:
    ```
    repl_prims("(match (parse-int \"42\") [(Some n) n None 0])\n")
        .assert_stdout_contains(":primitives/Int 42");
    ```
    Cite `spec/appendix-a-builtins.md §A.3`.

11. `parse_int_invalid` → `primitive_parse_int_invalid`:
    ```
    repl_prims("(match (parse-int \"not-a-number\") [(Some n) n None (sub-i64 0 1)])\n")
        .assert_stdout_contains(":primitives/Int -1");
    ```
    Cite `spec/appendix-a-builtins.md §A.3`.

12. `vec_set_preserves_other_elements` → `primitive_vec_set_other_positions_preserved`:
    ```
    repl_prims("(let [v (vec-set [10 20 30] 1 99)] (add-i64 (vec-get v 0) (vec-get v 2)))\n")
        .assert_stdout_contains(":primitives/Int 40");
    ```
    Cite `spec/appendix-a-builtins.md §A.3`.

13. `vec_of_strings_get` → `primitive_vec_get_string_element`:
    ```
    repl_prims("(str-len (vec-get [\"hello\" \"world\"] 0))\n")
        .assert_stdout_contains(":primitives/Int 5");
    ```
    Cite `spec/03-types.md §3.2.4` or `spec/appendix-a-builtins.md §A.3`.

14. `vec_of_adts` → `vec_containing_adt_elements_get_and_match`:
    ```
    repl_prims("(deftype (Option a) None (Some [:a val]))\n(match (vec-get [(Some 1) None (Some 3)] 0) [(Some x) x None 0])\n")
        .assert_stdout_contains(":primitives/Int 1");
    ```
    Cite `spec/03-types.md §3.2.4` or `spec/05-definitions.md §5.2.2`.

15. `vec_get_middle` → `primitive_vec_get_middle_index`:
    ```
    repl_prims("(vec-get [10 20 30] 1)\n")
        .assert_stdout_contains(":primitives/Int 20");
    ```
    Cite `spec/appendix-a-builtins.md §A.3`. **Mild ambiguity** — see /sprint flags.

Verification step before authoring: grep `tests/spec_*` for the
recommended test names to confirm no collisions. None of these names
appeared in the carry-forward files at audit time.

### Per-test classifications

#### Cluster N — Dual-mode parity (7 tests, lines 1089-1153)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 97 | `dual_mode_closure_returned` | mode-equiv closure-returned | batch+REPL parity | COVERED | absorbed by `build_confidence.rs::mode_equiv_*` framing per Wave 5.5/5.6 finding (per-feature `dual_mode_*` tests systematically supplanted) |
| 98 | `dual_mode_higher_order` | mode-equiv HOF | batch+REPL parity | COVERED | absorbed by `build_confidence.rs::mode_equiv_*` framing |
| 99 | `dual_mode_named_fn_value` | mode-equiv named-fn-as-value | batch+REPL parity | COVERED | absorbed by `build_confidence.rs::mode_equiv_*` framing — this dual-mode form is supplanted; the underlying named-fn-as-value angle is GAP-COVER chunk-2 #3 (separate finding) |
| 100 | `dual_mode_match_with_field_bindings` | mode-equiv ctor-pattern | batch+REPL parity | COVERED | absorbed by `build_confidence.rs::mode_equiv_adt_option_match` (Point parallel) |
| 101 | `dual_mode_enum_match` | mode-equiv enum-match | batch+REPL parity | COVERED | absorbed by `build_confidence.rs::mode_equiv_*` framing |
| 102 | `dual_mode_lambda_immediate` | mode-equiv lambda-immediate | batch+REPL parity | COVERED | absorbed by `build_confidence.rs::mode_equiv_*` framing |
| 103 | `dual_mode_lambda_in_let` | mode-equiv lambda-in-let | batch+REPL parity | COVERED | absorbed by `build_confidence.rs::mode_equiv_let_binding` (exact lambda-in-let shape) |

#### Cluster O — Error paths (7 tests, lines 1162-1217)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 104 | `error_string_where_int_expected` | spec/03 §3.5 — type mismatch (String→Int) | `(add-i64 "hello" 1)` | COVERED | `spec_03_types.rs::unification_int_vs_string_errors` (which uses if-branches Int/String) covers the Int-vs-String unification angle; this is a fn-arg variant of the same unification mismatch — same diagnostic shape |
| 105 | `error_int_where_string_expected` | spec/03 §3.5 — type mismatch (Int→String) | `(str-len 42)` | **GAP-COVER** | NEW — fn-arg-type-mismatch at a String-typed slot. Distinct direction from #104 (which is Int-typed slot rejecting String); the Int→String slot direction exercises the symmetric path. |
| 106 | `error_adt_constructor_wrong_arg_count` | spec/05 §5.2.7 — ctor arity | `(Point 1)` 1 of 2 | **GAP-COVER** | NEW — no spec_05 test isolates ADT constructor arity rejection. `defn_multi_clause_arity` covers defn arity (positive); `defn_multi_clause_duplicate_sig_neg` is duplicate-sig negative. Ctor arity is a distinct lookup path. |
| 107 | `error_adt_constructor_wrong_type` | spec/05 §5.2.7 — ctor arg type | `(Point true 2)` Bool→Int slot | **GAP-COVER** | NEW — ctor argument type-checking is not isolated. `deftype_product_construct_and_destructure` is positive; the negative-type-check angle for product ctors is uncovered. |
| 108 | `error_if_branches_type_mismatch_string_int` | spec/04 §4.4 — if branches mismatch | `(if true "hello" 42)` | COVERED | `spec_04_expressions.rs::if_neg_branch_type_mismatch` and `spec_03_types.rs::unification_int_vs_string_errors` (same `(if true 1 "hello")` form) — exact angle |
| 109 | `error_closure_arity_mismatch` | spec/04 §4.5 — closure arity | `((fn [x] x) 1 2)` | **GAP-COVER** | NEW — closure arity rejection at application is not isolated. `defn_multi_clause_arity` is for defns and is positive. The "calling closure with too many args" rejection path is distinct. |
| 110 | `error_undefined_constructor` | spec/04 §4.2.1 — undefined ctor | `(Foo 1 2)` Foo undefined | **GAP-COVER** | NEW — `variable_reference_unbound_errors` covers unbound symbol; constructor lookup table is distinct. |

#### Cluster P — Let-polymorphism with closures (6 tests, lines 1225-1290)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 111 | `let_bound_identity_at_multiple_types` | spec/03 §3.4 — let-poly | `(let [id (fn [x] x)] (add-i64 (id 1) (id 2)))` — both at Int | COVERED | absorbed by `let_polymorphism_identity_two_types` (defn-bound id at Int+Bool covers the more-general poly shape; let-bound at same type is a strict subset). The let-vs-defn binding distinction is not a separate spec angle in §3.4. |
| 112 | `polymorphic_higher_order` | spec/03 §3.4 — poly HOF | `(apply-fn (fn [x] x) 1)` and `(apply-fn (fn [x] x) 2)` | COVERED | absorbed by `lambda_passed_as_argument_invoked_inside_callee` (single application of identity) + `polymorphic_identity_at_int/bool` (poly instantiation). Composition. |
| 113 | `let_bound_lambda_with_capture` | spec/04 §4.5.1 — captured λ called twice | `(let [base 100 f (fn [x] (add-i64 base x))] (add-i64 (f 1) (f 2)))` | **GAP-COVER** | NEW — let-bound capturing closure invoked twice with **independent args** (f(1) and f(2), not f(f(x))). Distinct from chunk-2's `closure_apply_twice` (f(f(x)) shape) and from `lambda_closure_captures` (single call). The capture-invariance-under-independent-calls angle exercises that the captured value is not consumed/dropped after first call. |
| 114 | `identity_on_string` | spec/03 §3.3 — poly id at String | `(str-len (id "hello"))` | **GAP-COVER** | NEW — polymorphic identity instantiated at a heap-typed value. `polymorphic_identity_at_int/bool` cover scalar; String is the heap counterpart with distinct codegen path (RC-aware). |
| 115 | `identity_on_adt` | spec/03 §3.3 — poly id at ADT | `(id (Some 42))` then match | **GAP-COVER** | NEW — id at user-defined ADT type. Distinct from #114 (literal-driven heap) — ADT is ctor-driven heap. The user-defined-type instantiation angle is uncovered. |
| 116 | `higher_order_on_adt` | spec/03 §3.3 — poly HOF + ADT | `(apply-fn (fn [x] (Some x)) 42)` then match | **GAP-COVER** | NEW — HOF returning ADT. Distinct from any covered HOF (none return ADTs) and from any covered ADT shape (none flow through HOF return position). The Functor.return-into-Option shape. |

#### Cluster Q — parse-int (2 tests, lines 1298-1322)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 117 | `parse_int_valid` | appendix-a §A.3 — parse-int Some | `(parse-int "42")` returns `(Some 42)` | **GAP-COVER** | NEW — zero parse-int coverage in any e2e file. parse-int is normatively a primitive per §A.3 returning `(Option Int)`. |
| 118 | `parse_int_invalid` | appendix-a §A.3 — parse-int None | `(parse-int "not-a-number")` returns None | **GAP-COVER** | NEW — negative companion to #117. The None-returning path is the spec-mandated failure mode. |

#### Cluster R — Misc / TCO / composition (6 tests, lines 1332-1425)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 119 | `closure_and_tco` | spec/12 §12.5 — TCO with HOF (fold) | self-recursive fold threading f param | DUPLICATE-IN-LEGACY | duplicates chunk-2 GAP-COVER #5 (`closure_recursive_with_higher_order` test 73 — same self-recursion-with-fn-typed-parameter shape). The fold-pattern wrapper is an alternate framing of the same angle; consolidation recommended in any follow-up authoring. **Note**: subprocess-driven (out-of-process) due to historical SIGBUS in REPL — relevant context for any consolidated test. |
| 120 | `adt_in_tco` | spec/12 §12.5 — TCO with match (Stop/Continue) | self-recursive match-loop | COVERED | `spec_12_runtime.rs::tco_match_tail_position` (currently `#[ignore]` pending TCO MUST clause via FIXME 0141) — exact Stop/Continue shape. |
| 121 | `string_in_recursive_function` | spec/03 §3.1 — recursive fn with string body | `(count-down ... (str-len "done"))` recursion, str-len in tail-base | COVERED | absorbed by `tco_deep_countdown` (countdown shape) + `primitive_str_len` (str-len primitive) — composition of covered shapes; no distinct sub-spec angle. |
| 122 | `multiple_adt_definitions` | spec/05 §5.2 — coexisting ADTs | Color + Option together, nested match | COVERED | absorbed by `pattern_arms_type_unify` (Color match) + `pattern_some_binds_value` (Option match) + `nested_match_in_arm_body` (nested match) — composition of three covered shapes. |
| 123 | `closure_over_closure` | spec/04 §4.5.1 — make-counter | `(make-counter 100)` shape with multiple invocations | COVERED | absorbed by `lambda_closure_captures` (`make-add` shape — exact pattern) + `closure_capture_alloc_and_invoke` (RC angle). The two-invocations-of-the-result is the same angle as `let_bound_lambda_with_capture` GAP-COVER #6 above; that GAP-COVER subsumes this. |
| 124 | `let_bound_adt_and_closure` | spec/04 §4.5.1 — closure + ADT in let | `(let [f ... result (f 42)] (match result ...))` | COVERED | absorbed by `closure_returning_adt` (chunk-2 covered) + `pattern_some_binds_value` (Option match) — composition |

#### Cluster S — Vec literals + primitives (20 tests, lines 1434-1631)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 125 | `vec_literal_int` | spec/03 §3.2.4 — Vec literal Int | `(vec-len [1 2 3])` = 3 | COVERED | `spec_04_expressions.rs::vec_literal_int` + `spec_appendix_a_builtins.rs::primitive_vec_len` — both covered. Exact angle. |
| 126 | `vec_literal_empty` | spec/03 §3.2.4 — empty Vec literal | `(vec-len [])` = 0 | COVERED | `spec_04_expressions.rs::vec_literal_empty` — exact angle |
| 127 | `vec_literal_strings` | spec/03 §3.2.4 — Vec literal of String | `(vec-len ["a" "b"])` = 2 | COVERED | absorbed by `vec_literal_int` (vec-len shape) + `primitive_str_len` (String literal). The Vec-of-String-literal angle is implicit; vec-len is type-agnostic at the spec level. |
| 128 | `vec_get_first` | appendix-a §A.3 — vec-get index 0 | `(vec-get [10 20 30] 0)` = 10 | COVERED | `primitive_vec_get_first` — exact angle |
| 129 | `vec_get_last` | appendix-a §A.3 — vec-get last index | `(vec-get [10 20 30] 2)` = 30 | COVERED | absorbed by `primitive_vec_get_first` (positional indexing is generalized; first-vs-last is symmetric, no distinct spec angle for `index = len-1`) |
| 130 | `vec_get_middle` | appendix-a §A.3 — vec-get middle index | `(vec-get [10 20 30] 1)` = 20 | **GAP-COVER** | NEW (mild ambiguity — see /sprint flags). The first/middle/last indexing-family is conventional triple coverage; only first is isolated. The middle-vs-end distinction may matter for cache-line / array-traversal consideration. Discrete carry would be `primitive_vec_get_middle_index`. |
| 131 | `vec_set_element` | appendix-a §A.3 — vec-set | `(vec-get (vec-set [10 20 30] 1 99) 1)` = 99 | COVERED | absorbed by `primitive_vec_set_preserves_len` (which exercises vec-set + vec-get of the modified position implicitly via len-preservation; the get-back-the-set-value angle is implicit in the structural assertion that the vec is still well-formed) |
| 132 | `vec_set_preserves_other_elements` | spec/12 §12.3.3 — vec-set non-disturbing | other positions preserved after set | **GAP-COVER** | NEW — distinct from `primitive_vec_set_preserves_len` (asserts length only) and `vec_set_cow_preserves_original` (asserts ORIGINAL untouched, not new-vec other positions). The other-positions-of-the-set-result angle is uncovered. |
| 133 | `vec_push_appends` | appendix-a §A.3 — vec-push len | `(vec-len (vec-push [1 2] 3))` = 3 | COVERED | `primitive_vec_push_increases_len` — exact angle |
| 134 | `vec_push_value` | appendix-a §A.3 — vec-push value at end | `(vec-get (vec-push [1 2] 3) 2)` = 3 | COVERED | `primitive_vec_push_value_at_last_index` — exact angle |
| 135 | `vec_len_zero` | appendix-a §A.3 — vec-len empty | `(vec-len [])` = 0 | COVERED | absorbed by `vec_literal_empty` + `primitive_vec_len` — same shape (already covered) |
| 136 | `vec_len_three` | appendix-a §A.3 — vec-len three | `(vec-len [1 2 3])` = 3 | COVERED | absorbed by `vec_literal_int` + `primitive_vec_len` — same shape |
| 137 | `vec_in_let` | spec/04 §4.3 — Vec in let | `(let [v [1 2 3]] (vec-get v 0))` | COVERED | `primitive_vec_let_bound_then_get` — exact angle |
| 138 | `vec_in_defn` | spec/04 §4.6 — Vec as fn arg | `(first v)` defn called with `[10 20]` | COVERED | absorbed by RC consuming-convention (heap-arg passed through fn boundary) + `primitive_vec_get_first`; the fn-arg angle is implicit |
| 139 | `vec_of_strings_get` | spec/03 §3.2.4 — Vec of String elem access | `(str-len (vec-get ["hello" "world"] 0))` = 5 | **GAP-COVER** | NEW — Vec-of-String element access. `primitive_vec_get_first` uses Int elements; the heap-typed-element vec is a distinct RC-aware angle (the get must increment the String's RC and pass ownership to caller). |
| 140 | `vec_of_strings_get_second` | spec/03 §3.2.4 — Vec of String elem 1 | `(str-len (vec-get ["hello" "world"] 1))` = 5 | COVERED | absorbed by #139 GAP-COVER (single test for Vec-of-String suffices; first-vs-second is positional symmetry) |
| 141 | `vec_of_adts` | spec/03 §3.2.4 — Vec of ADT elem | vec-get + match on `(Some 1)` element | **GAP-COVER** | NEW — Vec containing ADT values. Heap-element-vec with ctor-driven elements + match after vec-get. Distinct from any covered shape. |
| 142 | `vec_of_adts_none` | spec/03 §3.2.4 — Vec of ADT, None elem | vec-get index 1 = None | COVERED | absorbed by #141 GAP-COVER (single test for Vec-of-ADT covers Some/None mixed dispatch via the same vec-get + match shape) |
| 143 | `vec_push_to_empty` | appendix-a §A.3 — vec-push to `[]` | `(vec-get (vec-push [] 42) 0)` = 42 | COVERED | `primitive_vec_push_onto_empty` — exact angle |
| 144 | `vec_set_first` | appendix-a §A.3 — vec-set index 0 | `(vec-get (vec-set [1 2 3] 0 99) 0)` = 99 | COVERED | absorbed by `vec_set_element` (same vec-set-then-vec-get shape; index 0 vs index 1 is positional symmetry — no distinct spec angle) |

### GAP-COVER candidates

For follow-up authoring dispatch (NOT this audit). 15 candidates summarised above; full sketches inline. Distribution:

- **Error-paths cluster (5 candidates, all negative-coverage)** — #2-5 for ADT/closure/undef-ctor errors; #1 for Int→String type-mismatch direction.
- **Polymorphism-with-closures cluster (3 candidates)** — #7-9 for poly id at String/ADT and HOF-on-ADT.
- **parse-int cluster (2 candidates)** — #10-11 for both valid and invalid paths (zero coverage exists).
- **Let-bound-capture cluster (1 candidate)** — #6 for capture-invariance-under-independent-calls.
- **Vec cluster (4 candidates)** — #12 for set-other-positions; #13 for Vec-of-String; #14 for Vec-of-ADT; #15 for vec-get-middle (mild ambiguity).

All 15 are pure positive- or negative-coverage gaps surfaced by per-test
review. None are REGRESSION-GUARD (no `_neg_` shape in source name beyond
the standard error-path naming, no source `BUG` comment, no Sprint-N
defect attribution).

Verification step before authoring: grep target files for the
recommended test names. None collided at audit time.

### Tests flagged for /sprint judgment

- **#127 `vec_literal_strings`** — Vec of String literals. Marked
  COVERED via composition (vec-len shape + String-literal coverage).
  Discrete test would be `primitive_vec_len_string_elements`. Mild
  ambiguity — heap-element vec literals may matter for codegen
  (initial-RC-of-string-literal + pushed into vec). If `/sprint`
  thinks the heap-element-literal shape is distinct from the heap-
  element-runtime-construction (covered by #139), promote to
  GAP-COVER.
- **#129 `vec_get_last`** — index = len-1 indexing. Marked COVERED via
  positional symmetry with `primitive_vec_get_first`. Low importance.
- **#130 `vec_get_middle`** — flagged GAP-COVER but with mild
  ambiguity. Discrete test would be `primitive_vec_get_middle_index`.
  If `/sprint` thinks the first/middle/last triple is conventional
  but redundant given get-by-index is generalized, demote to COVERED.
- **#138 `vec_in_defn`** — Vec passed as fn arg. Marked COVERED via
  composition. Discrete test would be `vec_argument_passed_to_fn`.
  Possibly worth flagging — fn-arg-with-heap-type angle exercises
  consuming-convention + RC.
- **#142 `vec_of_adts_none`** — None element in Vec-of-ADT. Marked
  COVERED via #141 GAP-COVER. If `/sprint` thinks the None-element-no-
  heap-allocation distinction is worth isolating, promote.
- **#119 `closure_and_tco`** — DUPLICATE-IN-LEGACY of chunk-2's
  `closure_recursive_with_higher_order` (test 73). The fold-via-TCO
  shape is the same angle as repeat-fn. Recommend consolidation in any
  follow-up: a single test covering self-recursion threading a
  fn-typed parameter, with both the `repeat-fn` style and the `fold`
  style as in-source variants. Alternatively, take `closure_and_tco`
  (the deeper-recursion + subprocess wrap) as the canonical
  consolidated form.

### Cross-chunk pattern (chunk 3 signal)

Chunk 1 (tests 1-48): 96% cluster-mode accuracy → 2 GAP-COVER (4%).
Chunk 2 (tests 49-96): 81% cluster-mode accuracy → 9 GAP-COVER (19%).
Chunk 3 (tests 97-144): 67% cluster-mode accuracy → 15 GAP-COVER (31%) + 1 DUPLICATE-IN-LEGACY (2%).

The composition-cluster hypothesis from chunk 2 is **further
confirmed**: chunk 3 contains the **error-paths cluster** (cluster O,
no isolated negative-coverage in spec-anchored e2e for ADT-ctor or
closure-arity errors) and the **parse-int cluster** (cluster Q, zero
parse-int coverage anywhere in e2e). These two pure-yield-clusters
account for 7 of the 15 GAP-COVERs.

The vec cluster (S, 20 tests) yields a respectable 5 GAP-COVERs at
75% cluster-mode accuracy — heap-typed-element vec shapes (Vec of
String, Vec of ADT) are missing across the suite, and the conventional
first/middle/last positional-indexing triple is incomplete.

The polymorphism-with-closures cluster (P, 6 tests) yields 3
GAP-COVERs at 50% cluster-mode accuracy — `polymorphic_identity_at_int/bool`
covers only scalar instantiations; the heap-typed (String, ADT)
instantiations are uncovered. This is a gap that aligns with the
chunk-2 hypothesis that composition-heavy clusters yield the most
GAP-COVERs.

The dual-mode cluster (N, 7 tests, all COVERED) and the misc/TCO
cluster (R, 6 tests, mostly COVERED) follow the cluster-1 / cluster-2
pattern of "primitive-bound or framework-supplanted clusters absorb
tightly".

**Updated total ring1.rs GAP-COVER yield estimate:** chunk 1 (2) +
chunk 2 (9) + chunk 3 (15) = **26 so far**. With chunk 4 covering
~46 tests (vec_set_last through end), the projected final yield is
likely in the **30-40 range** — substantially exceeding the chunk-1
"5-15 range" hypothesis and chunk-2's "14-21 range" updated
estimate. ring1.rs is now plausibly the **highest-yield file in the
re-audit campaign** (vs sketch_port's 25 and e2e's ~50+; note e2e
ported assertion-by-assertion, ring1.rs is a cluster file).

The chunk-3 yield concentration in error-paths (5 of 15) and parse-int
(2 of 15) is structural — these are clusters where the spec has clear
content but the spec-anchored e2e files were authored without explicit
negative-coverage targeting. The error-path GAP-COVERs are
particularly load-bearing: they test that the compiler **rejects**
specific malformed programs, which is the negative-coverage payload
the user has emphasized as load-bearing in the audit framework.

**Hypothesis adjustment for chunk 4:** chunk 4 covers tests 145-190
(vec_set_last through end of file). The remaining vec tests
(vec_set_last, vec_returned_from_function, vec_passed_to_function,
vec_in_if_branch, vec_push_chain), more dual-mode-vec, REPL vec, and
then a final cluster of error/match/scope tests. Expected yield: 3-7
GAP-COVERs (similar density to chunk-3-vec-subset but with the final
match/error cluster likely contributing 1-3 more).

### Running total — chunks 1+2+3

| Chunk | COVERED | DUPLICATE-IN-LEGACY | GAP-COVER | GAP-HARVEST | Total |
|---:|---:|---:|---:|---:|---:|
| 1 | 46 | 0 | 2 | 0 | 48 |
| 2 | 39 | 0 | 9 | 0 | 48 |
| 3 | 32 | 1 | 15 | 0 | 48 |
| **Sum** | **117** | **1** | **26** | **0** | **144** |

Chunks 1+2+3 cluster-mode accuracy: **81%** (117/144). Total GAP-COVER
yield: **26 of 144 (18%)**. The cluster-1 mode-accuracy of 96%
overrepresented the file — composition-heavy clusters in chunks 2 and
3 substantially lower the actual cluster-mode discount. The full
ring1.rs re-audit yield is on track to substantially exceed the
original estimate.

---

## Chunk 4 of 4 — tests 145-190 (`vec_set_last` through `neg_pattern_too_many_bindings`)

Lines ~1636-2266. Covers:

- Vec extended (5 tests): set-last, returned-from-fn, passed-to-fn, in-if-branch, push-chain
- Dual-mode Vec (3 tests): literal, get, push
- REPL Vec (5 tests): literal, get, set, push, display
- Error message quality U1.7 Wave 0 (2 tests): type-mismatch-names-both-types, if-branch-mismatch
- Pattern-matching semantics §6.3 (3 tests): eval-order-top-to-bottom, binding-scope-limited, arm-type-disagreement
- Type checking patterns §6.4 (4 tests): constructor-pattern-typecheck, var-pattern-scrutinee-type, wildcard-no-constraints, return-type-unified
- Non-ADT scrutinee §6.5.2 (2 tests): int-var-pattern, bool-wildcard
- Negative §6.5 + §6.6 (5 tests): exhaustive-missing-ctor, single-arm-lists-all-missing, empty-arms, non-adt-scrut-with-adt-ctor, nested-pattern
- Match in trait impl (1 test)
- string-identity primitive (1 test)
- Auto-curry / arity errors / undef variable (4 tests): auto-curry-partial, fn-arity-too-many, undef-var, adt-type-mismatch-names-Option
- Error message quality U1.7 Wave 3 (8 tests): str-where-int names String + names Int, int-where-str names Int + names String, ctor-wrong-type names Bool, if-branch names types, undef-ctor names it, match-arm-type-mismatch names types
- D5 P5-MED Negative (3 tests): nested-pattern-rejected, pattern-wrong-binding-count, pattern-too-many-bindings

### Summary

| Disposition | Count |
|---|---:|
| COVERED | 19 |
| DUPLICATE-IN-LEGACY | 2 |
| GAP-COVER | 25 (of which REGRESSION-GUARD: 0) |
| GAP-HARVEST | 0 |
| **Total** | **46** |

The yield is **the highest of any chunk** (25 GAP-COVER vs chunk 1's 2,
chunk 2's 9, chunk 3's 15). The cluster shifts decisively into
**negative-coverage / error-message-quality territory** — the U1.7
clusters (T, Z) plus the §6.5 / §6.6 negative-coverage cluster (X)
together yield 18 of the 25 GAP-COVERs. This chunk is dominated by
"the spec says the error MUST mention X" assertions that the
spec-anchored e2e files do not isolate.

The vec extended cluster (T, 5 tests) yields 4 GAP-COVERs — vec
flowing through fn-arg, fn-return, if-branch, and push-chain are all
uncovered shapes (`primitive_vec_*` covers single-shot primitives; the
flow-through-shapes are absent). Chunk 3 already flagged Vec-of-String
and Vec-of-ADT as GAP-COVERs; this chunk extends that pattern to
fn-flow + if-branch + chained-push.

The REPL Vec cluster (V, 5 tests) yields 1 GAP-COVER — `repl_vec_display`
asserts the literal `[1 2 3]` or `[1, 2, 3]` content of the value
display. `vec_literal_int` only asserts `primitives/Vec` type prefix,
not the value content. The actual element-rendering format is not
isolated.

The pattern-matching semantics cluster (X, §6.3 + §6.4 + §6.5.2 — 9
tests) is **mostly COVERED** — `pattern_first_match_wins`,
`pattern_some_binds_value`, `pattern_variable_binds_value`,
`pattern_wildcard_catchall`, `pattern_arms_type_unify`,
`pattern_int_match_with_wildcard` collectively cover top-to-bottom
order, ctor-pattern type, var-pattern, wildcard-no-constraint,
return-type-unified, and non-ADT-int-var. Two GAP-COVERs:
`error_match_arm_type_disagreement` (negative-coverage for arm-body-type
mismatch — uncovered) and `match_non_adt_bool_wildcard` (Bool scrutinee
+ wildcard — distinct from Int+var).

The §6.5/§6.6 negative cluster (Y, 5 tests) yields 4 GAP-COVERs —
`neg_exhaustive_match_missing_constructor_compile_error` (Color+Blue
omitted, error names "Color" + "Blue"),
`neg_exhaustive_match_single_arm_lists_all_missing` (single Red arm,
error lists Green AND Blue),
`neg_match_empty_arms_rejected` (empty arms list rejected),
`neg_match_non_adt_scrut_with_adt_constructor_rejected` (Int scrut with
None ctor pattern). One COVERED: `error_nested_pattern` is duplicated
inline (chunk 4 has both `error_nested_pattern` and
`neg_nested_pattern_rejected` — see DUPLICATE-IN-LEGACY).

The U1.7 Wave 0 + Wave 3 error quality clusters (T, Z — 10 tests)
yield 9 GAP-COVERs. The existing carry-forward
`unification_int_vs_string_errors` only asserts ONE of
`Int|String|type|mismatch` is present (`||`); the `error_quality_*`
tests assert specific names appear in specific directions
(String→Int direction names "String" AND "Int"; Int→String direction
names "Int" AND "String"; ctor-wrong-type names "Bool"; undef-ctor
names "Foo"). These are stricter contracts. None are isolated in the
spec-anchored e2e files.

The D5 P5-MED Negative cluster (AA, 3 tests) yields 2 GAP-COVERs —
`neg_pattern_wrong_binding_count` (Point with 1-binding pattern) and
`neg_pattern_too_many_bindings` (Point with 3-binding pattern). One
DUPLICATE-IN-LEGACY: `neg_nested_pattern_rejected` is the same shape
as `error_nested_pattern` immediately above it (both reject `(Some
(Point x y))` nested constructor pattern). The legacy file has both
the original "throws error" version (line 2034) and the "neg
companion" (line 2217) — these are duplicates within the same file.

The match-in-trait-impl cluster (W, 1 test) is COVERED via
`spec_07_traits.rs::trait_impl_on_enum_adt_with_match_over_all_constructors`
— exact Color/Red/Green/Blue match-in-impl shape.

The string-identity cluster (Y, 1 test) yields 1 GAP-COVER —
`string-identity` is a normative primitive per
`spec/appendix-a-builtins.md §A.3` (line 92) explicitly cited as
`[Tested tests/ring1.rs::string_identity_returns_same]`. No
spec-anchored e2e test exists.

The dual-mode Vec cluster (U, 3 tests) is **all COVERED** via
`build_confidence.rs::mode_equiv_*` framing per the canonical
Wave 5.5/5.6 finding (consistent with chunks 2 and 3).

The auto-curry / arity / undef-variable cluster (Z, 4 tests) is
**all COVERED** — `defn_auto_curry_call_with_fewer_args` covers
auto-curry-partial; `wrong_arity_too_many_args` (in repl_negative.rs)
covers fn-arity-too-many; `variable_reference_unbound_errors` covers
undef-var; `error_adt_type_mismatch_includes_type_name` (Option) is
covered by composition (any test that mismatches an ADT-typed param
will name the ADT — but **mild ambiguity**: the specific assertion
that the error names the ADT type literal "Option" is not isolated;
flagged for /sprint).

### NEW GAP-COVER findings

| # | Originating test | Recommended target | Angle | Type |
|---:|---|---|---|---|
| 1 | `vec_set_last` | `tests/spec_appendix_a_builtins.rs` | `(vec-set [1 2 3] 2 99)` — set last index. `primitive_vec_set_preserves_len` covers index 1; first/last/middle positional triple is conventional. **Mild ambiguity** — flagged for /sprint. | GAP-COVER |
| 2 | `vec_returned_from_function` | `tests/spec_03_types.rs` or `tests/spec_appendix_a_builtins.rs` | `(make-vec)` returns `[10 20 30]`, caller does vec-get. Vec as fn-return-type. Distinct from `string_returned_from_function_freed` (String) — Vec has different RC semantics + literal allocation in callee body. | GAP-COVER |
| 3 | `vec_passed_to_function` | `tests/spec_03_types.rs` or `tests/spec_appendix_a_builtins.rs` | `(sum-first-two [3 4 5])` — Vec as fn-arg. Distinct from `string_in_let` and `vec_in_let` shapes. The fn-arg-with-Vec-typed-slot exercises consuming-convention + RC. | GAP-COVER |
| 4 | `vec_in_if_branch` | `tests/spec_04_expressions.rs` | `(vec-len (if true [1 2 3] [4 5]))` — `if` returning Vec value. Distinct from chunk-1 `string_in_if_branches` (String) and chunk-2 `closure_in_if_branch` (closure) GAP-COVERs. Vec-result if-branch unification with **different lengths** is uncovered. | GAP-COVER |
| 5 | `vec_push_chain` | `tests/spec_appendix_a_builtins.rs` | `(vec-push (vec-push (vec-push [] 1) 2) 3)` — three nested push-onto-empty calls. Distinct from `primitive_vec_push_onto_empty` (single push) — chained pushes exercise repeat allocation through the empty-Vec → 1-elem → 2-elem → 3-elem chain (RC + cap-growth). | GAP-COVER |
| 6 | `repl_vec_display` | `tests/repl_introspection.rs` | Vec display shows literal element content `[1 2 3]` or `[1, 2, 3]`. `vec_literal_int` only asserts `primitives/Vec` type prefix. The element-content-rendering shape is uncovered. | GAP-COVER |
| 7 | `error_type_mismatch_names_both_types` | `tests/spec_03_types.rs` | `(add-i64 1 "hello")` — error MUST name **both** "Int" AND "String" (two assertions). `unification_int_vs_string_errors` uses `\|\|` (any of the names suffices), not strict naming of both. The "names-both-types" contract is not enforced. | GAP-COVER |
| 8 | `error_if_branch_type_mismatch` | `tests/spec_04_expressions.rs` | `(if true 42 "hello")` error MUST name both "Int" and "String". `if_neg_branch_type_mismatch` exists but doesn't assert specific type names. | GAP-COVER |
| 9 | `error_match_arm_type_disagreement` | `tests/spec_06_pattern_matching.rs` | Color/Red→1, Green→"two", Blue→3 — mismatched arm bodies (Int vs String). Spec §6.3.3 says arm types MUST agree. No spec_06 negative test exists for arm-type disagreement. | GAP-COVER |
| 10 | `match_non_adt_bool_wildcard` | `tests/spec_06_pattern_matching.rs` | `(match b [_ (if b 1 0)])` — Bool scrutinee with wildcard. `pattern_int_match_with_wildcard` covers Int+var; `pattern_wildcard_catchall` covers ADT+wildcard. The Bool+wildcard shape is uncovered. | GAP-COVER |
| 11 | `neg_exhaustive_match_missing_constructor_compile_error` | `tests/spec_06_pattern_matching.rs` | Color (Red+Green only, missing Blue) — error MUST name BOTH the type "Color" AND missing ctor "Blue". `pattern_non_exhaustive_match_on_adt_neg` is the loose version (any of "Blue\|exhaustive\|missing\|match failed\|error"). The strict-naming variant is uncovered. | GAP-COVER |
| 12 | `neg_exhaustive_match_single_arm_lists_all_missing` | `tests/spec_06_pattern_matching.rs` | Color match with single Red arm — error MUST list Green AND Blue (both missing ctors). Distinct from #11 (which omits 1 ctor; this omits 2). The "lists ALL missing constructors" angle is uncovered. | GAP-COVER |
| 13 | `neg_match_empty_arms_rejected` | `tests/spec_06_pattern_matching.rs` | `(match b [])` — empty arms list. Per §6.5.2 a match must have at least one arm. The empty-arms rejection is uncovered. | GAP-COVER |
| 14 | `neg_match_non_adt_scrut_with_adt_constructor_rejected` | `tests/spec_06_pattern_matching.rs` | `(match n [None 1 (Some _) 2])` where n is Int — using Option ctor patterns on Int scrutinee. Per §6.5.2 only wildcard/var allowed on non-ADT scrut. The cross-type ctor-pattern rejection is uncovered. | GAP-COVER |
| 15 | `error_nested_pattern` | `tests/spec_06_pattern_matching.rs` | Nested ctor pattern `(Some (Point x y))` rejected. **Note**: chunk 4 has both this and `neg_nested_pattern_rejected` covering the same source shape — DUPLICATE-IN-LEGACY pair (the carry should be one test, not two). | GAP-COVER |
| 16 | `string_identity_returns_same` | `tests/spec_appendix_a_builtins.rs` | `string-identity` is a normative primitive per appendix-a-builtins §A.3 explicitly used by the Display impl. Spec line 92 cites this exact test. Zero spec-anchored e2e coverage. | GAP-COVER |
| 17 | `error_quality_string_where_int_names_string` | `tests/spec_03_types.rs` | `(add-i64 "hello" 1)` — error MUST name "String" specifically. The strict-naming contract distinct from `unification_int_vs_string_errors` weak-`\|\|` form. | GAP-COVER |
| 18 | `error_quality_string_where_int_names_int` | `tests/spec_03_types.rs` | Same source, error MUST name "Int". Companion to #17. | GAP-COVER |
| 19 | `error_quality_int_where_string_names_int` | `tests/spec_03_types.rs` | `(str-len 42)` — error MUST name "Int". Distinct from chunk-3 GAP-COVER `error_int_where_string_expected` (which checked any error indicator) — this asserts specific naming. | GAP-COVER |
| 20 | `error_quality_int_where_string_names_string` | `tests/spec_03_types.rs` | Same source, error MUST name "String". Companion to #19. | GAP-COVER |
| 21 | `error_quality_constructor_wrong_type_names_bool` | `tests/spec_05_definitions.rs` | `(Point true 2)` where Point [:Int x :Int y] — error MUST name "Bool". Distinct from chunk-3 GAP-COVER `error_adt_constructor_wrong_type` (which asserted any of Bool/Int/type) — this is strict-Bool-naming. | GAP-COVER |
| 22 | `error_quality_if_branch_mismatch_names_types` | `tests/spec_04_expressions.rs` | `(if true "hello" 42)` — strict naming of both Int AND String. Same source as #8 with assertions explicitly for Int+String. Effectively the strict variant of `if_neg_branch_type_mismatch`. | GAP-COVER (subsumes #8) |
| 23 | `error_quality_undefined_constructor_names_it` | `tests/spec_05_definitions.rs` or `tests/spec_04_expressions.rs` | `(Foo 1 2)` — error MUST name "Foo". Distinct from chunk-3 GAP-COVER `error_undefined_constructor` (which asserted any of Foo/undefined/error) — this is strict "Foo" naming. | GAP-COVER |
| 24 | `error_quality_match_arm_type_mismatch` | `tests/spec_06_pattern_matching.rs` | Color match with Int/String arm bodies — error MUST name both Int AND String. Effectively the strict variant of #9 `error_match_arm_type_disagreement`. | GAP-COVER (subsumes #9) |
| 25 | `neg_pattern_wrong_binding_count` + `neg_pattern_too_many_bindings` | `tests/spec_06_pattern_matching.rs` | Constructor pattern with too few bindings (`(Point x)`) and too many (`(Point a b c)`) — both rejected. Pattern-arity-mismatch error. The wrong-binding-count rejection per §6.2.1 is uncovered. | GAP-COVER (consolidated test) |

Sketches:

1. `vec_set_last` → `primitive_vec_set_last_index`:
   ```
   repl_prims("(vec-get (vec-set [1 2 3] 2 99) 2)\n")
       .assert_stdout_contains(":primitives/Int 99");
   ```
   Cite `spec/appendix-a-builtins.md §A.3`. **Mild ambiguity**.

2. `vec_returned_from_function` → `vec_as_function_return_type`:
   ```
   repl_prims("(defn make-vec [] [10 20 30])\n(vec-get (make-vec) 1)\n")
       .assert_stdout_contains(":primitives/Int 20");
   ```
   Cite `spec/03-types.md §3.2.4`.

3. `vec_passed_to_function` → `vec_as_function_argument`:
   ```
   repl_prims("(defn sum-first-two [v] (add-i64 (vec-get v 0) (vec-get v 1)))\n(sum-first-two [3 4 5])\n")
       .assert_stdout_contains(":primitives/Int 7");
   ```
   Cite `spec/03-types.md §3.2.4`.

4. `vec_in_if_branch` → `if_branches_heap_typed_vec_result`:
   ```
   repl_prims("(vec-len (if true [1 2 3] [4 5]))\n")
       .assert_stdout_contains(":primitives/Int 3");
   ```
   Cite `spec/04-expressions.md §4.4`.

5. `vec_push_chain` → `primitive_vec_push_chain_three_levels`:
   ```
   repl_prims("(vec-len (vec-push (vec-push (vec-push [] 1) 2) 3))\n")
       .assert_stdout_contains(":primitives/Int 3");
   ```
   Cite `spec/appendix-a-builtins.md §A.3`.

6. `repl_vec_display` → `vec_value_display_shows_element_content`:
   ```
   let out = repl_prims("[1 2 3]\n");
   assert!(out.stdout.contains("[1 2 3]") || out.stdout.contains("[1, 2, 3]"));
   ```
   Cite `repl/spec.md §1.5`.

7. `error_type_mismatch_names_both_types` → `unification_error_names_both_types_strict`:
   ```
   let out = repl_prims("(add-i64 1 \"hello\")\n");
   assert!(out.stdout.contains("Int") || out.stderr.contains("Int"));
   assert!(out.stdout.contains("String") || out.stderr.contains("String"));
   ```
   Cite `spec/03-types.md §3.8`.

8. `error_if_branch_type_mismatch` → `if_branch_mismatch_names_both_types_strict`:
   ```
   let out = repl_prims("(if true 42 \"hello\")\n");
   assert!(out.stdout.contains("Int") || out.stderr.contains("Int"));
   assert!(out.stdout.contains("String") || out.stderr.contains("String"));
   ```
   Cite `spec/04-expressions.md §4.4` or `spec/03-types.md §3.8`.

9. `error_match_arm_type_disagreement` → `match_arm_body_type_mismatch_neg`:
   ```
   let out = repl_prims("(deftype Color Red Green Blue)\n(match Red [Red 1 Green \"two\" Blue 3])\n");
   assert!(out.stdout.to_lowercase().contains("error") || out.stdout.contains("type"));
   ```
   Cite `spec/06-pattern-matching.md §6.3.3`.

10. `match_non_adt_bool_wildcard` → `pattern_bool_match_with_wildcard`:
    ```
    repl_prims("(match true [_ (if true 1 0)])\n")
        .assert_stdout_contains(":primitives/Int 1");
    ```
    Cite `spec/06-pattern-matching.md §6.5.2`.

11. `neg_exhaustive_match_missing_constructor_compile_error` → `pattern_exhaustive_error_names_type_and_missing_ctor_strict`:
    ```
    let out = repl_prims("(deftype Color Red Green Blue)\n(defn pick [c] (match c [Red 1 Green 2]))\n(pick Blue)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(combined.contains("Color"));
    assert!(combined.contains("Blue"));
    ```
    Cite `spec/06-pattern-matching.md §6.5.1`.

12. `neg_exhaustive_match_single_arm_lists_all_missing` → `pattern_exhaustive_error_lists_all_missing_ctors`:
    ```
    let out = repl_prims("(deftype Color Red Green Blue)\n(defn pick [c] (match c [Red 1]))\n(pick Green)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(combined.contains("Green") && combined.contains("Blue"));
    ```
    Cite `spec/06-pattern-matching.md §6.5.1`.

13. `neg_match_empty_arms_rejected` → `pattern_empty_arms_rejected_neg`:
    ```
    let out = repl_prims("(defn pick [b] (match b []))\n(pick true)\n");
    assert!(out.stdout.to_lowercase().contains("error") || out.stderr.to_lowercase().contains("error"));
    ```
    Cite `spec/06-pattern-matching.md §6.5.2`.

14. `neg_match_non_adt_scrut_with_adt_constructor_rejected` → `pattern_non_adt_scrut_rejects_adt_ctor_pattern_neg`:
    ```
    let out = repl_prims("(deftype (Option a) None (Some [:a val]))\n(defn pick [n] (match n [None 1 (Some _) 2]))\n(pick 5)\n");
    assert!(out.stdout.to_lowercase().contains("error") || out.stderr.to_lowercase().contains("error"));
    ```
    Cite `spec/06-pattern-matching.md §6.5.2`.

15. `error_nested_pattern` + `neg_nested_pattern_rejected` (consolidated) → `pattern_nested_constructor_rejected_neg`:
    ```
    let out = repl_prims("(deftype (Option a) None (Some [:a val]))\n(deftype Point [:Int x :Int y])\n(defn bad [opt] (match opt [(Some (Point x y)) (add-i64 x y) None 0]))\n(bad None)\n");
    assert!(out.stdout.to_lowercase().contains("error") || out.stderr.to_lowercase().contains("error"));
    ```
    Cite `spec/06-pattern-matching.md §6.6.1`.

16. `string_identity_returns_same` → `primitive_string_identity_returns_same`:
    ```
    repl_prims("(str-len (string-identity \"hello\"))\n")
        .assert_stdout_contains(":primitives/Int 5");
    ```
    Cite `spec/appendix-a-builtins.md §A.3`.

17-20. `error_quality_*_names_*` → strict-naming variants, sketched as #7/#8 with explicit `assert!(combined.contains("X"))` per type name.

21. `error_quality_constructor_wrong_type_names_bool` → `deftype_product_ctor_wrong_arg_type_names_bool_neg`:
    ```
    let out = repl_prims("(deftype Point [:Int x :Int y])\n(match (Point true 2) [(Point x y) x])\n");
    assert!(out.stdout.contains("Bool") || out.stderr.contains("Bool"));
    ```
    Cite `spec/05-definitions.md §5.2.7`.

23. `error_quality_undefined_constructor_names_it` → `data_constructor_undefined_error_names_it_strict`:
    ```
    let out = repl_prims("(Foo 1 2)\n");
    assert!(out.stdout.contains("Foo") || out.stderr.contains("Foo"));
    ```
    Cite `spec/04-expressions.md §4.2.1` or `spec/05-definitions.md §5.2`.

25. Consolidated `pattern_constructor_arity_mismatch_neg`:
    ```
    let out_few = repl_prims("(deftype Point [:Int x :Int y])\n(match (Point 3 4) [(Point x) x])\n");
    let out_many = repl_prims("(deftype Point [:Int x :Int y])\n(match (Point 3 4) [(Point a b c) a])\n");
    assert!(out_few.stdout.to_lowercase().contains("error") || out_few.stderr.to_lowercase().contains("error"));
    assert!(out_many.stdout.to_lowercase().contains("error") || out_many.stderr.to_lowercase().contains("error"));
    ```
    Cite `spec/06-pattern-matching.md §6.2.1`.

Verification step before authoring: grep target files for the
recommended test names to confirm no collisions. None collided at audit
time.

### Per-test classifications

#### Cluster T — Vec extended (5 tests, lines 1636-1688)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 145 | `vec_set_last` | appendix-a §A.3 — vec-set last index | `(vec-set [1 2 3] 2 99)` then get index 2 | **GAP-COVER** | NEW (mild ambiguity — same family as chunk-3 #15 vec_get_middle). first/middle/last positional triple convention; `primitive_vec_set_preserves_len` covers index 1. |
| 146 | `vec_returned_from_function` | spec/03 §3.2.4 — Vec as fn return | `(make-vec)` returns `[10 20 30]`, caller does vec-get | **GAP-COVER** | NEW — Vec as fn-return-type. `vec_of_strings_alloc_drop` covers Vec-of-Strings allocation; the fn-return-position angle exercises consuming-convention transfer + RC at boundary. Distinct from `string_returned_from_function_freed` (String — different RC semantics). |
| 147 | `vec_passed_to_function` | spec/03 §3.2.4 — Vec as fn arg | `(sum-first-two [3 4 5])` defn body does vec-get | **GAP-COVER** | NEW — Vec as fn-arg slot. Distinct from `vec_in_let` (let-anchor), `primitive_vec_let_bound_then_get` (let). The fn-arg consuming-convention shape is uncovered. |
| 148 | `vec_in_if_branch` | spec/04 §4.4 — `if` returning Vec | `(if true [1 2 3] [4 5])` — both branches Vec, different lengths | **GAP-COVER** | NEW — Vec-result if-branch. Distinct from chunk-1 #15 `string_in_if_branches`, chunk-2 #72 `closure_in_if_branch` (closure-result). The Vec-result with **different lengths** in branches is a unique unification angle. |
| 149 | `vec_push_chain` | appendix-a §A.3 — chained vec-push | `(vec-push (vec-push (vec-push [] 1) 2) 3)` 3-level chain | **GAP-COVER** | NEW — chained pushes through empty-vec start. `primitive_vec_push_onto_empty` covers single push. The 3-level chain exercises repeat allocation + RC growth through the chain. Mirror of chunk-1 #12 `string_concat_chained` for vec-push. |

#### Cluster U — Dual-mode Vec (3 tests, lines 1697-1713)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 150 | `dual_mode_vec_literal` | mode-equiv vec-literal | batch+REPL parity | COVERED | absorbed by `build_confidence.rs::mode_equiv_*` framing (per Wave 5.5/5.6 finding) |
| 151 | `dual_mode_vec_get` | mode-equiv vec-get | batch+REPL parity | COVERED | absorbed by `build_confidence.rs::mode_equiv_*` framing |
| 152 | `dual_mode_vec_push` | mode-equiv vec-push | batch+REPL parity | COVERED | absorbed by `build_confidence.rs::mode_equiv_*` framing |

#### Cluster V — REPL Vec (5 tests, lines 1722-1766)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 153 | `repl_vec_literal` | spec/03 §3.2.4 — vec literal in REPL | `(vec-len [1 2 3])` = 3 | COVERED | `spec_appendix_a_builtins.rs::primitive_vec_len` is REPL-canonical via repl_prims; same shape |
| 154 | `repl_vec_get` | appendix-a §A.3 — vec-get in REPL | `(vec-get [10 20 30] 0)` | COVERED | `primitive_vec_get_first` REPL-canonical |
| 155 | `repl_vec_set` | appendix-a §A.3 — vec-set in REPL | `(vec-get (vec-set [10 20 30] 1 99) 1)` | COVERED | `primitive_vec_set_preserves_len` REPL-canonical (same vec-set shape) |
| 156 | `repl_vec_push` | appendix-a §A.3 — vec-push in REPL | `(vec-len (vec-push [1 2] 3))` | COVERED | `primitive_vec_push_increases_len` REPL-canonical |
| 157 | `repl_vec_display` | repl/spec.md §1.5 — Vec display content | `[1 2 3]` shows `[1 2 3]` or `[1, 2, 3]` | **GAP-COVER** | NEW — `vec_literal_int` only asserts `primitives/Vec` type prefix. The element-content rendering format is not isolated. |

#### Cluster T2 — Error message quality U1.7 Wave 0 (2 tests, lines 1779-1798)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 158 | `error_type_mismatch_names_both_types` | spec/03 §3.8 — names BOTH types | `(add-i64 1 "hello")` error has Int AND String | **GAP-COVER** | NEW — strict naming of both types. `unification_int_vs_string_errors` uses `\|\|` (any of names suffices). The "names both" contract is uncovered. |
| 159 | `error_if_branch_type_mismatch` | spec/04 §4.4 / spec/03 §3.8 — names BOTH types in if branches | `(if true 42 "hello")` error has Int AND String | **GAP-COVER** | NEW — strict naming. `if_neg_branch_type_mismatch` exists but doesn't enforce specific naming. |

#### Cluster X — Pattern-matching semantics §6.3 (3 tests, lines 1806-1849)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 160 | `match_eval_order_top_to_bottom` | spec/06 §6.3.1 — top-to-bottom | Color/Red 1, Red 2 — first wins | COVERED | `spec_06_pattern_matching.rs::pattern_first_match_wins` — exact angle (wildcard before specific case; first wins) |
| 161 | `match_binding_scope_limited_to_arm` | spec/06 §6.3.2 — binding scope per arm | Some-binding `x` only in arm body | COVERED | `spec_06_pattern_matching.rs::pattern_some_binds_value` — exact Some-binding shape (covers same scope-limited semantics) |
| 162 | `error_match_arm_type_disagreement` | spec/06 §6.3.3 — arm bodies type-agree (NEG) | Color arm bodies Int/String mismatch | **GAP-COVER** | NEW — no spec_06 negative test for arm-body-type mismatch. The §6.3.3 MUST clause has no isolated negative carry. |

#### Cluster X2 — Type checking patterns §6.4 (4 tests, lines 1857-1911)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 163 | `match_constructor_pattern_type_checking` | spec/06 §6.4.1 — ctor pattern instantiates poly | `(Some 42)` match | COVERED | `spec_06_pattern_matching.rs::pattern_some_binds_value` — exact shape |
| 164 | `match_variable_pattern_gets_scrutinee_type` | spec/06 §6.4.2 — var pattern type | `(let [n 42] (match n [v (add-i64 v 1)]))` | COVERED | `spec_06_pattern_matching.rs::pattern_int_match_with_wildcard` (uses `n` binding on Int scrut) — exact angle |
| 165 | `match_wildcard_no_constraints` | spec/06 §6.4.3 — wildcard adds no constraints | Color match `_` | COVERED | `spec_06_pattern_matching.rs::pattern_wildcard_catchall` — exact angle |
| 166 | `match_return_type_unified` | spec/06 §6.4.4 — match expr type unified | Color → Int via 3 arms, sum two calls | COVERED | `spec_06_pattern_matching.rs::pattern_arms_type_unify` (Color all-3-arm match returns unified Int) — exact angle |

#### Cluster X3 — Non-ADT scrutinee §6.5.2 (2 tests, lines 1919-1937)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 167 | `match_non_adt_int_var_pattern` | spec/06 §6.5.2 — Int + var pattern | `(match n [x (add-i64 x 1)])` | COVERED | `spec_06_pattern_matching.rs::pattern_int_match_with_wildcard` — exact angle |
| 168 | `match_non_adt_bool_wildcard` | spec/06 §6.5.2 — Bool + wildcard | `(match b [_ (if b 1 0)])` | **GAP-COVER** | NEW — Bool scrutinee distinct angle from Int scrutinee. `pattern_int_match_with_wildcard` covers Int+var; `pattern_wildcard_catchall` covers ADT+wildcard. Bool+wildcard is distinct. |

#### Cluster Y — §6.5 negative coverage (4 tests, lines 1953-2030)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 169 | `neg_exhaustive_match_missing_constructor_compile_error` | spec/06 §6.5.1 — names type + missing ctor | Color, missing Blue, error names "Color" + "Blue" | **GAP-COVER** | NEW — strict naming. `pattern_non_exhaustive_match_on_adt_neg` is loose-or form; the strict-naming variant is uncovered. |
| 170 | `neg_exhaustive_match_single_arm_lists_all_missing` | spec/06 §6.5.1 — lists ALL missing | single Red arm; error has both Green AND Blue | **GAP-COVER** | NEW — multi-missing-ctor enumeration is distinct from #169 (1-missing). The "lists ALL missing" angle is uncovered. |
| 171 | `neg_match_empty_arms_rejected` | spec/06 §6.5.2 — empty arms | `(match b [])` | **GAP-COVER** | NEW — empty-arms rejection is uncovered in spec_06. |
| 172 | `neg_match_non_adt_scrut_with_adt_constructor_rejected` | spec/06 §6.5.2 — non-ADT + ADT ctor | Int scrut + None/Some ctor patterns | **GAP-COVER** | NEW — cross-type ctor-pattern rejection is uncovered. |

#### Cluster Y2 — §6.6 negative + match-in-trait (2 tests, lines 2034-2071)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 173 | `error_nested_pattern` | spec/06 §6.6.1 — nested ctor rejected | `(Some (Point x y))` rejected | DUPLICATE-IN-LEGACY | duplicates #189 `neg_nested_pattern_rejected` (lines 2217-2232) — same source, same shape, same assertion. The "neg companion" was authored without checking the existing same-shape test was already present at line 2034. **Recommendation**: consolidate as one carry. Listed under GAP-COVER #15. |
| 174 | `match_in_trait_impl` | spec/06 §6.7.8 — match in impl | Sizeable Color match-in-defn | COVERED | `spec_07_traits.rs::trait_impl_on_enum_adt_with_match_over_all_constructors` — exact Color/Red/Green/Blue match-in-impl shape |

#### Cluster Y3 — string-identity primitive (1 test, lines 2079-2084)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 175 | `string_identity_returns_same` | appendix-a §A.3 — string-identity primitive | `(str-len (string-identity "hello"))` = 5 | **GAP-COVER** | NEW — `string-identity` is a normative primitive per appendix-a-builtins §A.3 line 92, used by Display impl. Zero spec-anchored e2e test exists. |

#### Cluster Z — Auto-curry / arity / undef (4 tests, lines 2092-2128)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 176 | `error_adt_type_mismatch_includes_type_name` | spec/03 §3.8 — ADT type name in error | passing String to fn expecting Option, error names "Option" | COVERED | absorbed by `unification_int_vs_string_errors` (type-mismatch diagnostic shape) — **mild ambiguity**: the specific assertion that the error names the ADT type literal "Option" is not strictly carried; flagged for /sprint judgment. |
| 177 | `auto_curry_function_arity_partial` | spec/04 §4.6.3 — auto-curry partial | `(let [f (add2 1)] (f 2))` | COVERED | `spec_05_definitions.rs::defn_auto_curry_call_with_fewer_args` — exact `(let [inc (add 1)] (inc 4))` shape |
| 178 | `error_function_arity_too_many` | spec/03 §3.8 — too many args is arity error | `(add2 1 2 3)` | COVERED | `repl_negative.rs::wrong_arity_too_many_args` — exact angle |
| 179 | `error_undefined_variable_names_variable` | spec/03 §3.8 — undef var name in error | `nonexistent` error contains "nonexistent" | COVERED | `spec_04_expressions.rs::variable_reference_unbound_errors` — variable-reference-unbound error shape |

#### Cluster Z2 — U1.7 Wave 3 error quality (8 tests, lines 2140-2208)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 180 | `error_quality_string_where_int_names_string` | spec/03 §3.8 — names "String" | `(add-i64 "hello" 1)` error has "String" | **GAP-COVER** | NEW — strict-naming-of-String. `unification_int_vs_string_errors` uses or-form. |
| 181 | `error_quality_string_where_int_names_int` | spec/03 §3.8 — names "Int" | same source, error has "Int" | **GAP-COVER** | NEW — strict-naming-of-Int companion. |
| 182 | `error_quality_int_where_string_names_int` | spec/03 §3.8 — names "Int" (Int→String) | `(str-len 42)` error has "Int" | **GAP-COVER** | NEW — strict-Int-naming. Distinct from chunk-3 GAP-COVER #1 `error_int_where_string_expected` (any error indicator). |
| 183 | `error_quality_int_where_string_names_string` | spec/03 §3.8 — names "String" | same source, error has "String" | **GAP-COVER** | NEW — strict-String-naming companion. |
| 184 | `error_quality_constructor_wrong_type_names_bool` | spec/05 §5.2.7 — names "Bool" | `(Point true 2)` error has "Bool" | **GAP-COVER** | NEW — strict-Bool-naming. Distinct from chunk-3 GAP-COVER #3 `error_adt_constructor_wrong_type` (any of Bool/Int/type). |
| 185 | `error_quality_if_branch_mismatch_names_types` | spec/04 §4.4 — names both | `(if true "hello" 42)` error has Int AND String | **GAP-COVER** | NEW — same source as #159 strict variant (subsumes #159). |
| 186 | `error_quality_undefined_constructor_names_it` | spec/04 §4.2.1 — names ctor | `(Foo 1 2)` error has "Foo" | **GAP-COVER** | NEW — strict-Foo-naming. Distinct from chunk-3 GAP-COVER #5 `error_undefined_constructor` (any of Foo/undefined/error). |
| 187 | `error_quality_match_arm_type_mismatch` | spec/06 §6.3.3 — names both types | Color Int/String arm mismatch error has Int AND String | **GAP-COVER** | NEW — strict variant of #162 `error_match_arm_type_disagreement` (subsumes #162). |

#### Cluster AA — D5 P5-MED Negative (3 tests, lines 2217-2266)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 188 | `neg_nested_pattern_rejected` | spec/06 §6.6.1 — nested ctor rejected | same source as #173 `error_nested_pattern` | DUPLICATE-IN-LEGACY | duplicates #173. The two tests have identical source and identical assertion (compile error). Sprint 16 added this as "companion to existing error_nested_pattern" without consolidating. |
| 189 | `neg_pattern_wrong_binding_count` | spec/06 §6.2.1 — too few bindings | `(Point x)` for Point[2 fields] | **GAP-COVER** | NEW — pattern-arity-mismatch (too few). No spec_06 test exists. |
| 190 | `neg_pattern_too_many_bindings` | spec/06 §6.2.1 — too many bindings | `(Point a b c)` for Point[2 fields] | **GAP-COVER** | NEW — pattern-arity-mismatch (too many). Companion to #189; consolidated into one carry per #25 above. |

### GAP-COVER candidates

For follow-up authoring dispatch (NOT this audit). 25 candidates. Distribution:

- **Vec extended cluster (5 candidates)** — #1-5 for set-last (mild),
  return-position, arg-position, if-branch, push-chain.
- **REPL Vec cluster (1 candidate)** — #6 for vec value display content.
- **U1.7 Wave 0 cluster (2 candidates)** — #7 for type-mismatch
  names-both-types, #8 for if-branch names-both-types (subsumed by
  Wave 3 #22).
- **§6.3 / §6.5.2 negative + Bool wildcard (2 candidates)** — #9 for
  arm-body-type disagreement, #10 for Bool+wildcard.
- **§6.5 negative cluster (4 candidates)** — #11-14 for missing-ctor
  names-Color+Blue, lists-all-missing, empty-arms, non-ADT-scrut-ADT-ctor.
- **§6.6 nested-pattern (1 candidate)** — #15 (consolidates #173 + #188
  legacy duplicate pair).
- **string-identity (1 candidate)** — #16, normative primitive zero
  e2e coverage.
- **U1.7 Wave 3 strict-naming cluster (8 candidates)** — #17-24 for
  strict naming of String/Int/Bool/ctor/types in 7 distinct error
  shapes (#22 subsumes #8, #24 subsumes #9).
- **D5 pattern-arity (1 candidate)** — #25 consolidating #189 + #190
  too-few + too-many binding counts.

All 25 are pure positive- or negative-coverage gaps. None are
REGRESSION-GUARD (no `_neg_` shape beyond standard error-path naming,
no source `BUG` comment, no Sprint-N defect attribution beyond U1.7
Sprint-7-Wave-0 / Sprint-8-Wave-3 / Sprint-16 framing — these are
spec-promise tests, not regression-naming).

Verification step before authoring: grep target files for the
recommended test names. None collided at audit time.

### Tests flagged for /sprint judgment

A small number of tests had subtle disposition calls; `/sprint` should
review:

- **#145 `vec_set_last`** — flagged GAP-COVER but with mild ambiguity
  (same family as chunk-3 #15 `vec_get_middle`). first/middle/last
  positional triple is conventional but redundant given indexing is
  generalized. If `/sprint` thinks the convention is redundant, demote
  both to COVERED.
- **#176 `error_adt_type_mismatch_includes_type_name`** — marked
  COVERED via composition with `unification_int_vs_string_errors`.
  The specific assertion that the error names the ADT type literal
  "Option" is not strictly carried. Discrete test would be
  `unification_error_names_adt_type_strict`. If `/sprint` thinks the
  ADT-type-name-in-error angle is distinct, promote to GAP-COVER.
- **#173 + #188 nested-pattern duplicate pair** — DUPLICATE-IN-LEGACY.
  Recommend consolidating into one carry-forward per #15.
  Alternatively if `/sprint` thinks the two were authored to test
  distinct behaviors (the second was framed as a companion), keep
  them as two separate but identical tests — but that adds no value.
- **GAP-COVER subsume relationships**: #22 subsumes #8, #24 subsumes
  #9 (the Wave 3 strict variants are stricter than the Wave 0
  asserts-anything variants). The author may consolidate #8/#9 into
  #22/#24 and drop the originals — or carry both as the Wave 0
  versions exercise weaker contracts (any-of-types) while Wave 3
  asserts strict naming.
- **chunk-3 GAP-COVER #1, #3, #5 vs chunk-4 GAP-COVER #19, #21, #23**:
  the chunk-3 versions assert "any error indicator"; the chunk-4
  versions assert specific type names. If `/sprint` thinks the
  any-error variants are strictly weaker, consolidate by promoting
  the chunk-4 strict variants only; otherwise both have value (a
  weak-form companion is the regression guard for the type-name-
  agnostic error, the strict-form is the spec-message-quality guard).

### Cross-chunk pattern (chunk 4 signal)

Chunk 1 (tests 1-48): 96% cluster-mode accuracy → 2 GAP-COVER (4%).
Chunk 2 (tests 49-96): 81% cluster-mode accuracy → 9 GAP-COVER (19%).
Chunk 3 (tests 97-144): 67% cluster-mode accuracy → 15 GAP-COVER (31%) + 1 DUPLICATE-IN-LEGACY (2%).
Chunk 4 (tests 145-190): 41% cluster-mode accuracy → 25 GAP-COVER (54%) + 2 DUPLICATE-IN-LEGACY (4%).

The composition-cluster hypothesis from chunks 1-3 is **decisively
confirmed and extended**: chunk 4 is dominated by the **U1.7
error-message-quality clusters** (10 tests yielding 9 GAP-COVERs) and
the **§6.5 / §6.6 negative-coverage cluster** (5 tests yielding 4
GAP-COVERs + 1 duplicate). Together these "spec-MUST-clause
negative-coverage" clusters yield 13 of the 25 GAP-COVERs — over half.

The Vec extended cluster (T) yields 5 of 5 — every Vec flow shape
(fn-arg, fn-return, if-branch, chained-push, set-last) is uncovered
in the spec-anchored e2e files. The vec-primitive carry-forwards
(`primitive_vec_*`) cover single-shot primitives only; the
flow-through-shapes are absent across the suite.

The DUPLICATE-IN-LEGACY count (2: `error_nested_pattern` /
`neg_nested_pattern_rejected`) reflects intra-file duplication added
by Sprint 16 D5 work that didn't audit existing same-shape tests
before authoring "neg companions". This is a methodology finding —
chunk 3 also flagged 1 duplicate (`closure_and_tco` ↔ chunk-2's
`closure_recursive_with_higher_order`). Cross-chunk + intra-chunk
duplication is structural in ring1.rs as the file accumulated test
clusters across multiple sprints without consolidation passes.

### Running total — chunks 1+2+3+4

| Chunk | COVERED | DUPLICATE-IN-LEGACY | GAP-COVER | GAP-HARVEST | Total |
|---:|---:|---:|---:|---:|---:|
| 1 | 46 | 0 | 2 | 0 | 48 |
| 2 | 39 | 0 | 9 | 0 | 48 |
| 3 | 32 | 1 | 15 | 0 | 48 |
| 4 | 19 | 2 | 25 | 0 | 46 |
| **Sum** | **136** | **3** | **51** | **0** | **190** |

Chunks 1+2+3+4 cluster-mode accuracy: **72%** (136/190). Total
GAP-COVER yield: **51 of 190 (27%)**. Plus 3 duplicates representing
1.6% of the file. The chunk-mode-accuracy decline is monotonic
(96% → 81% → 67% → 41%), reflecting the structural shift from
primitive-bound clusters (chunk 1: strings + ADT primitives) through
composition clusters (chunk 2: closure/HOF) into negative-coverage
clusters (chunk 3: error paths + parse-int + Vec heap) and finally
**spec-MUST-clause clusters** (chunk 4: error-message-quality + §6.5
/ §6.6 negative + Vec flow shapes).

---

## File 7 totals (all 190 tests)

| Disposition | Count |
|---|---:|
| COVERED | 136 |
| DUPLICATE-IN-LEGACY | 3 |
| GAP-COVER | 51 (of which REGRESSION-GUARD: 0) |
| GAP-HARVEST | 0 |
| **Total** | **190** |

## Comparison to original cluster-mode disposition

Cluster-mode estimate from `tests/plan/wave-5.6-dedupe-audit.md` §7:

> ring1.rs (190 tests): file is "ring 1 = strings + ADTs + closures +
> Vec" — fully absorbed by spec_03 (strings), spec_05 (deftype + ADT),
> spec_06 (pattern matching), spec_07 (traits over ADTs), spec_appendix_a
> (Vec primitives), spec_12 (RC), and `build_confidence.rs` (mode-equiv).
> Disposition: COVERED — entire file. Recommendation: delete after
> moving to legacy.

**Cluster-mode estimate**: 190 COVERED, 0 GAP-COVER, 0 DUPLICATE.

**Per-test reality**: 136 COVERED, 51 GAP-COVER, 3 DUPLICATE-IN-LEGACY.

**Gap**: 51 of 190 tests (27%) were silently absorbed by cluster-mode
without per-test verification; 3 of 190 (1.6%) were intra-/cross-chunk
duplicates. The cluster-mode disposition would have **lost 51 distinct
spec-promise / negative-coverage / flow-shape angles** if the file
were deleted post-cluster-audit without per-test re-verification.

The composition-heavy nature of ring1.rs (strings × ADTs × closures ×
Vec × error-message-quality) produced clusters where the spec-anchored
e2e files cover the primitives but not the compositions. The spec
itself has explicit MUST clauses (§3.8 names-both-types, §6.5.1
exhaustiveness-error-naming, §6.5.2 non-ADT-scrut, §6.6.1 nested-pattern,
§4.4 if-branch-naming, etc.) that the spec-anchored e2e files **do not
verify**, even though the cluster-mode disposition assumed they did.

## Methodology takeaway

**Cluster-mode accuracy for ring1.rs: 72%** (136 / 190 tests
correctly classified).

Comparison to other Wave 5.6 re-audits:

| File | Tests | Cluster-mode accuracy | GAP-COVER yield | Duplicate yield |
|---|---:|---:|---:|---:|
| ring0.rs | 92 | **97%** | 3 (3%) | 0 |
| sketch_port.rs | 100 | **75%** | 25 (25%) | 0 |
| e2e.rs | ~145 | **62%** | ~55 (38%) | ? |
| **ring1.rs** | **190** | **72%** | **51 (27%)** | **3 (1.6%)** |

ring1.rs sits between sketch_port (75%) and e2e (62%) in cluster-mode
accuracy. The file is the **highest-yield in the campaign by absolute
count** (51 GAP-COVER vs e2e's ~55, but per-test density is lower).

The chunk-by-chunk yield concentration (4% → 19% → 31% → 54%) is the
clearest signal that **cluster-mode accuracy degrades sharply as a
file's clusters shift from primitive-bound to composition-heavy to
negative-coverage**. Files structured as primitive-suite-then-edge-cases
reveal this inversion: the early chunks confirm the cluster
disposition; the later chunks expose its blind spot.

**Methodology conclusion**: cluster-mode dispositions on
composition-heavy / negative-coverage-heavy files are **unsafe to
treat as final**. Per-test reverification is required before any
cluster-disposed file is deleted or absorbed. The 27% GAP-COVER yield
on ring1.rs (51 distinct angles) would have been silently lost without
this re-audit.

## Recommendations for /sprint

1. **Authoring dispatch for the 51 GAP-COVER candidates**: the targets
   are concentrated in `tests/spec_03_types.rs` (10 candidates),
   `tests/spec_06_pattern_matching.rs` (12 candidates),
   `tests/spec_appendix_a_builtins.rs` (8 candidates),
   `tests/spec_04_expressions.rs` (8 candidates),
   `tests/spec_05_definitions.rs` (6 candidates),
   `tests/spec_12_runtime.rs` (3 candidates),
   `tests/repl_introspection.rs` (3 candidates),
   `tests/spec_07_traits.rs` (1 candidate). A single-skill `/qa`
   authoring wave can land all 51 in one or two sub-waves.

2. **Subsumption decisions** before authoring:
   - chunk-4 #22 subsumes chunk-4 #8 (Wave 3 strict if-branch
     subsumes Wave 0 if-branch). Author #22 only.
   - chunk-4 #24 subsumes chunk-4 #9 (Wave 3 strict match-arm
     subsumes Wave 0 match-arm). Author #24 only.
   - chunk-4 #19, #21, #23 are strict variants of chunk-3 #1, #3, #5
     (any-error-indicator). Decide whether the weak-form carry has
     value as a regression guard or only the strict-form is needed.
   - chunk-4 #25 consolidates #189 + #190 (too-few + too-many
     binding counts as one test).
   - chunk-4 #15 consolidates the legacy duplicate pair #173 + #188.
   - chunk-3 DUPLICATE-IN-LEGACY #119 (`closure_and_tco`) consolidates
     with chunk-2 #5 (`closure_recursive_with_higher_order`).
   After all subsumptions: ~46 net new carry-forwards across the
   ring1.rs file (51 GAP-COVER findings minus 5 consolidations).

3. **Mild-ambiguity flags** for /sprint pre-authoring review:
   - chunk-3 #15 `vec_get_middle` and chunk-4 #1 `vec_set_last` —
     first/middle/last positional triple convention. Author all
     three (incl. existing first-only) or demote both to COVERED.
   - chunk-4 #176 `error_adt_type_mismatch_includes_type_name` —
     promote to GAP-COVER if the ADT-type-name-in-error angle is
     distinct from generic type-mismatch.
   - chunk-3 #127 `vec_literal_strings` — heap-element-literal vs
     heap-element-runtime-construction.
   - chunk-2 flags #52, #53, #54, #67, #82 — mostly low importance.

4. **Hard-to-classify tests** (none from chunk 4) — chunk 4 had clear
   dispositions throughout. Chunk 3's `closure_and_tco` was the
   sole DUPLICATE-IN-LEGACY across chunks 1-3; chunk 4 contributes
   the intra-file `error_nested_pattern` / `neg_nested_pattern_rejected`
   pair.

5. **Cluster-mode methodology revision**: future Wave 5.6+ audits
   on composition-heavy / U1.7-heavy files MUST treat cluster-mode
   dispositions as **upper bounds** subject to per-test reverification.
   The ring1.rs result (51 GAP-COVER from 190 cluster-COVERED tests)
   is the methodology's strongest counter-example. Recommend updating
   `tests/plan/wave-5.6-dedupe-audit.md` §7 with a methodology
   addendum: "cluster-mode dispositions on legacy ring1.rs / e2e.rs /
   sketch_port.rs are upper-bound estimates; per-test reverification
   yielded substantial GAP-COVER findings (3% / 25% / 27% / 38%
   respectively)".

6. **Spec annotation updates**: the 51 GAP-COVER candidates trace to
   spec sections 03 §3.8 (×7), 04 §4.4 + §4.6.3 (×4), 05 §5.2.7 (×3),
   06 §6.2.1 + §6.3.3 + §6.5.1 + §6.5.2 + §6.6.1 (×11), 12 §12.3.3
   (×3), repl §1.5 + §1.2 (×3), appendix-a §A.3 (×8). Spec annotation
   updates per `tests/plan/PLAN.md §"Requirements/Test Traceability"`
   should follow the authoring dispatch.
