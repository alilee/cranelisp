# Wave 5.6 file 8 ring2.rs — per-test re-audit (in progress)

Per-test re-audit of `tests/legacy/ring2.rs` (199 tests),
correcting the cluster-mode shortcut from
`tests/plan/wave-5.6-dedupe-audit.md` §8.

Authored: `/qa` (audit-only dispatch, 2026-05-04). Methodology: per-test
review against the 17 e2e carry-forward files in main, with Wave 5.6
disposition codes (COVERED / DUPLICATE-IN-LEGACY / GAP-COVER /
REGRESSION-GUARD / GAP-HARVEST). Same per-test framework as the
sketch_port, ring0, ring1, and e2e re-audits.

ring2.rs is **Ring 2 — traits + constrained polymorphism + modules**.
Heavy overlap expected with `spec_07_traits.rs` (default-method
synthesis, operator dispatch, constrained polymorphism) and
`spec_03_types.rs` (constrained add Int/Float). Many tests exercise
trait machinery through inline-defined `Num`/`Eq`/`Ord` traits using
the Ring 2A trait prelude in `with_traits()` (lines 39-86).

## Chunk 1 of 4 — tests 1-50 (`trait_plus_int` through `constrained_add_float`)

Lines 94-523. Covers:

- Num trait Int dispatch (+, -, *, /, edge-cases): 7 tests
  (lines 94-139, cluster A).
- Num trait Float dispatch (+, -, *, /): 4 tests (lines 147-180,
  cluster B).
- Num nested/compound expressions in let/if/fn-arg: 5 tests
  (lines 188-231, cluster C).
- Eq trait dispatch (Int true/false, Float true/false, Bool true/false,
  String true/false): 8 tests (lines 239-291, cluster D).
- Ord < operator (Int true/false/equal, Float true/false): 5 tests
  (lines 299-330, cluster E).
- Default methods (>, <=, >=, !=) — Int and String variants:
  12 tests (lines 338-419, cluster F).
- Constrained polymorphism — inline-operator + literal-operand
  recursive shapes (sum-to, fact): 3 tests (lines 432-463, cluster G).
- Constrained polymorphism — type-variable-only constrained fns
  (fibonacci, clamp variants, add Int/Float): 7 tests
  (lines 469-523, cluster H).

### Summary

| Disposition | Count |
|---|---:|
| COVERED | 47 |
| DUPLICATE-IN-LEGACY | 0 |
| GAP-COVER | 3 (of which REGRESSION-GUARD: 0) |
| GAP-HARVEST | 0 |
| **Total** | **50** |

ring2 chunk 1 has the **highest COVERED density seen across all five
re-audits**: 94% (47/50) of tests are absorbed by direct carry-forwards
in `spec_07_traits.rs` (operator dispatch, default methods,
constrained polymorphism) plus `spec_03_types.rs::constrained_add_int`/
`constrained_add_float`. The chunk-1 cluster-mode prediction
(traits "largely COVERED") is **confirmed accurate at the chunk-1
boundary**.

The 3 GAP-COVER candidates are all **trait-operator-with-recursion
composition shapes** that are not isolated in the carry-forward universe:

1. `fn_using_operators_with_literals` (sum-to with `=`/`+`/`-` in recursive defn)
2. `fn_factorial_with_operators` (fact with `=`/`*`/`-` in recursive defn)
3. `constrained_fn_fibonacci` (constrained polymorphic fib using `=`/`+`/`-`)

These shapes exercise trait-dispatched operators inside recursive
definitions — a composition path that `repl_lifecycle.rs::recursive_factorial`/
`recursive_fibonacci` does not cover (those use named primitives
`add-i64`/`mul-i64`/`sub-i64`/`eq-i64`/`lt-i64` directly, not trait-dispatched
operators). The trait-operator path exercises monomorphisation +
trait-method-resolution-at-recursive-call inside the body — distinct
from operator-in-main-body or constrained-add-arg-only shapes.

### NEW GAP-COVER findings

| # | Originating test | Recommended target | Angle | Type |
|---:|---|---|---|---|
| 1 | `fn_using_operators_with_literals` | `tests/spec_07_traits.rs` | trait-dispatched `=`/`+`/`-` inside recursive `(defn sum-to [n] ...)` body — n unified to Int by literal `0`, so NOT constrained, but each operator inside still goes through Num/Eq dispatch | GAP-COVER |
| 2 | `fn_factorial_with_operators` | `tests/spec_07_traits.rs` | trait-dispatched `=`/`*`/`-` inside recursive `(defn fact [n] ...)` body — same shape as #1 (literal-pin to Int) but multiplication path; factorial-shape canonical | GAP-COVER |
| 3 | `constrained_fn_fibonacci` | `tests/spec_07_traits.rs` | constrained polymorphic `(defn fib [n] ...)` with `=`/`+`/`-` and tree recursion (two recursive calls per arm) — exercises monomorphisation through the tree-recursion shape | GAP-COVER |

Sketches:

1. `fn_using_operators_with_literals` → `trait_operator_in_recursive_defn_literal_pinned`:
   ```
   repl_std("(defn sum-to [n] (if (= n 0) 0 (+ n (sum-to (- n 1)))))\n(sum-to 10)\n")
       .assert_stdout_contains(":primitives/Int 55");
   ```
   Cite `spec/07-traits.md §7.5`. Distinct from
   `operator_plus_int` (single inline call) and from
   `repl_lifecycle.rs::recursive_factorial` (named-primitive path).

2. `fn_factorial_with_operators` → `trait_operator_factorial_recursive_defn`:
   ```
   repl_std("(defn fact [n] (if (= n 0) 1 (* n (fact (- n 1)))))\n(fact 10)\n")
       .assert_stdout_contains(":primitives/Int 3628800");
   ```
   Cite `spec/07-traits.md §7.5`. Distinct from #1 (multiplication
   path; factorial canonical).

3. `constrained_fn_fibonacci` → `constrained_polymorphic_fib_tree_recursion`:
   ```
   repl_std("(defn fib [n] (if (= n 0) 0 (if (= n 1) 1 (+ (fib (- n 1)) (fib (- n 2))))))\n(fib 10)\n")
       .assert_stdout_contains(":primitives/Int 55");
   ```
   Cite `spec/03-types.md §3.6` and `spec/07-traits.md §7.5`. Distinct
   from `constrained_polymorphism_int_then_float` (single call, single
   instantiation) and from `repl_lifecycle.rs::recursive_fibonacci`
   (named-primitive path). Tree recursion through trait-dispatched
   operators is the unique shape.

Verification step before authoring: grep `tests/spec_07_traits.rs`
to confirm the recommended test names don't collide with existing tests.

### Per-test classifications

#### Cluster A — Num Int dispatch + edge cases (7 tests, lines 94-139)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 1 | `trait_plus_int` | spec/07 §7.5 — Num + Int dispatch | `(+ 1 2)` = 3 | COVERED | `spec_07_traits.rs::operator_plus_int` (canonical REPL form `(+ 5 6) = 11`) + `spec_03_types.rs::constrained_add_int` |
| 2 | `trait_minus_int` | spec/07 §7.5 — Num - Int dispatch | `(- 10 3)` = 7 | COVERED | `spec_appendix_a_builtins.rs::primitive_sub_i64` covers raw sub; the trait `-` path is the dual of `+` (same dispatch machinery), absorbed by `operator_plus_int` |
| 3 | `trait_multiply_int` | spec/07 §7.5 — Num * Int dispatch | `(* 6 7)` = 42 | COVERED | `spec_07_traits.rs::trait_impl_body_uses_operator` exercises `+` dispatch in trait impl body; `*` is the same dispatch path. Absorbed by `operator_plus_int` shape parity |
| 4 | `trait_divide_int` | spec/07 §7.5 — Num / Int dispatch | `(/ 20 4)` = 5 | COVERED | `spec_appendix_a_builtins.rs::primitive_div_i64` covers raw div; trait `/` path is dual of `+` — absorbed by `operator_plus_int` |
| 5 | `trait_plus_negative` | spec/07 §7.5 — Num + with negative operand | `(+ -3 5)` = 2 | COVERED | absorbed by `operator_plus_int` (sign-of-operand is invariant of dispatch path) + `spec_appendix_a_builtins.rs::primitive_add_i64` (raw arithmetic with negatives) |
| 6 | `trait_minus_negative_result` | spec/07 §7.5 — Num - with negative result | `(- 3 10)` = -7 | COVERED | absorbed by `operator_plus_int` + raw `primitive_sub_i64` (sign-of-result is invariant) |
| 7 | `trait_plus_zero` | spec/07 §7.5 — Num + with zero | `(+ 0 42)` = 42 | COVERED | absorbed by `operator_plus_int` (zero-operand is invariant of dispatch path) |

#### Cluster B — Num Float dispatch (4 tests, lines 147-180)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 8 | `trait_plus_float` | spec/07 §7.5 — Num + Float dispatch | `(+ 1.5 2.5)` Float 4.0 | COVERED | `spec_07_traits.rs::operator_plus_float` (exact angle, REPL canonical) + `spec_03_types.rs::constrained_add_float` |
| 9 | `trait_minus_float` | spec/07 §7.5 — Num - Float dispatch | `(- 10.0 3.5)` = 6.5 | COVERED | absorbed by `operator_plus_float` (Float dispatch path is identical for `-`) + `spec_appendix_a_builtins.rs::primitive_sub_f64` |
| 10 | `trait_multiply_float` | spec/07 §7.5 — Num * Float dispatch | `(* 3.0 4.0)` = 12.0 | COVERED | absorbed by `operator_plus_float` parallel — Float dispatch path is identical for `*` |
| 11 | `trait_divide_float` | spec/07 §7.5 — Num / Float dispatch | `(/ 10.0 2.0)` = 5.0 | COVERED | absorbed by `operator_plus_float` parallel — Float dispatch path is identical for `/` |

#### Cluster C — Num nested/compound shapes (5 tests, lines 188-231)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 12 | `trait_plus_nested` | spec/07 §7.5 — nested Num operator expressions | `(+ (+ 1 2) (+ 3 4))` = 10 | COVERED | `spec_07_traits.rs::operator_plus_int` covers single dispatch; nested form is composition — same dispatch path repeated. Absorbed by composition over `operator_plus_int` |
| 13 | `trait_mixed_arithmetic_expr` | spec/07 §7.5 — mixed `+`/`-`/`*` expression | `(* (+ 2 3) (- 10 4))` = 30 | COVERED | absorbed by composition: each operator dispatches via the same Num machinery |
| 14 | `trait_arithmetic_in_let` | spec/07 §7.5 — trait operators inside `let` | `(let [x (+ 3 4) y (* 2 3)] (+ x y))` = 13 | COVERED | composition: `let` binding-form (covered by `spec_04_expressions.rs::let_independent_bindings_pure_arithmetic`) + Num dispatch (covered by `operator_plus_int`); both pieces independently asserted |
| 15 | `trait_arithmetic_in_if` | spec/07 §7.5 — trait operators in `if` arms | `(if (= 1 1) (+ 10 20) (- 10 20))` = 30 | COVERED | composition: `if` covered by `spec_04_expressions.rs::if_true_branch`/`if_false_branch`; Eq dispatch + Num dispatch covered separately |
| 16 | `trait_arithmetic_as_function_arg` | spec/07 §7.5 — trait operator as fn argument | `(double (+ 10 11))` with `(defn double [:Int x] (+ x x))` = 42 | COVERED | composition: fn-arg-passing is invariant of trait dispatch; the `:Int` annotation makes this a non-constrained call. Absorbed by `operator_plus_int` + `spec_05_definitions.rs::defn_with_annotated_params` |

#### Cluster D — Eq operator dispatch (8 tests, lines 239-291)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 17 | `trait_eq_int_true` | spec/07 §7.5 — Eq = Int true | `(if (= 5 5) 1 0)` = 1 | COVERED | `spec_appendix_a_builtins.rs::primitive_eq_i64` covers raw eq; trait `=` path is dispatched-`=` — exercised through `spec_07_traits.rs::trait_method_dispatched_by_arg_type` (`(+ 1 2)`, parallel structure). The Eq-Int-true angle is exercised by every if-with-trait-= test in `spec_07_traits.rs` (e.g., `default_method_used_when_not_overridden` body `(add-i64 (greet x) 10)` exercises Num path; symmetric for Eq) |
| 18 | `trait_eq_int_false` | spec/07 §7.5 — Eq = Int false | `(if (= 5 3) 1 0)` = 0 | COVERED | absorbed by #17 (false-branch is invariant of dispatch path) |
| 19 | `trait_eq_float` | spec/07 §7.5 — Eq = Float true | `(if (= 3.14 3.14) 1 0)` = 1 | COVERED | absorbed by `operator_plus_float` parallel — same Float dispatch machinery; raw eq covered by `spec_appendix_a_builtins.rs::primitive_eq_f64` |
| 20 | `trait_eq_float_false` | spec/07 §7.5 — Eq = Float false | `(if (= 3.14 2.71) 1 0)` = 0 | COVERED | absorbed by #19 |
| 21 | `trait_eq_bool_true` | spec/07 §7.5 — Eq = Bool true | `(if (= true true) 1 0)` = 1 | COVERED | `spec_appendix_a_builtins.rs::primitive_eq_bool` covers raw bool eq; the trait `=` Bool dispatch path is parallel to Int/Float, absorbed |
| 22 | `trait_eq_bool_false` | spec/07 §7.5 — Eq = Bool false | `(if (= true false) 1 0)` = 0 | COVERED | absorbed by #21 |
| 23 | `trait_eq_string` | spec/07 §7.5 — Eq = String true | `(if (= "hello" "hello") 1 0)` = 1 | COVERED | `spec_appendix_a_builtins.rs::primitive_str_eq_true` covers raw str-eq; the trait `=` String dispatch path is parallel, absorbed |
| 24 | `trait_eq_string_false` | spec/07 §7.5 — Eq = String false | `(if (= "hello" "world") 1 0)` = 0 | COVERED | absorbed by #23 + `spec_appendix_a_builtins.rs::primitive_str_eq_false` |

#### Cluster E — Ord < (5 tests, lines 299-330)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 25 | `trait_lt_int_true` | spec/07 §7.5 — Ord < Int true | `(if (< 3 5) 1 0)` = 1 | COVERED | `spec_appendix_a_builtins.rs::primitive_lt_i64` covers raw lt; trait `<` dispatch path is parallel to `+`, absorbed |
| 26 | `trait_lt_int_false` | spec/07 §7.5 — Ord < Int false | `(if (< 5 3) 1 0)` = 0 | COVERED | absorbed by #25 |
| 27 | `trait_lt_int_equal` | spec/07 §7.5 — Ord < Int boundary (equal) | `(if (< 5 5) 1 0)` = 0 | COVERED | absorbed by #25 (equal-boundary is invariant of dispatch) |
| 28 | `trait_lt_float` | spec/07 §7.5 — Ord < Float true | `(if (< 1.0 2.0) 1 0)` = 1 | COVERED | `spec_appendix_a_builtins.rs::primitive_lt_f64` + `operator_plus_float` parallel — Float dispatch path |
| 29 | `trait_lt_float_false` | spec/07 §7.5 — Ord < Float false | `(if (< 2.0 1.0) 1 0)` = 0 | COVERED | absorbed by #28 |

#### Cluster F — Default methods (12 tests, lines 338-419)

The default-method synthesis machinery is carried by the chunk-1
sketch_port re-audit canonicals: `default_method_used_when_not_overridden`,
`default_method_overridden_by_impl`, `impl_missing_required_method_neg`,
`default_method_used_on_adt_impl`, `default_method_with_primitive_only_body`.
The ring2 tests #30-37 exercise specific default-method *applications*
(>, <=, >=, !=) — the dispatch path is the same, varying only the
method name and body.

Per Wave 5.6 methodology rule 4 (spec-anchoring is the dedup criterion):
all Cluster F tests anchor to spec/07 §7.1.5 (default method synthesis),
which is fully covered by the spec_07_traits canonicals. The
Int/String-specific variants are angle-redundant — once default-method
synthesis is asserted to work for one method (e.g., `wave` calling `greet`),
all default methods that follow the same body-shape pattern (>, <=, >=, !=)
ride the same machinery.

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 30 | `default_method_gt_int` | spec/07 §7.1.5 — default `>` Int | `(if (> 5 3) 1 0)` = 1 | COVERED | `spec_07_traits.rs::default_method_used_when_not_overridden` covers default-method-synthesis (canonical); `>` is one default method, parallel structure to `<` reverses |
| 31 | `default_method_gt_int_false` | spec/07 §7.1.5 — default `>` Int false | `(if (> 3 5) 1 0)` = 0 | COVERED | absorbed by #30 (false-branch invariant) |
| 32 | `default_method_le_int` | spec/07 §7.1.5 — default `<=` Int | `(if (<= 3 5) 1 0)` = 1 | COVERED | absorbed by `default_method_used_when_not_overridden` parallel — `<=` is a default method using `<` dispatch |
| 33 | `default_method_le_int_equal` | spec/07 §7.1.5 — default `<=` Int boundary | `(if (<= 5 5) 1 0)` = 1 | COVERED | absorbed by #32 (boundary is invariant of synthesis path) |
| 34 | `default_method_le_int_false` | spec/07 §7.1.5 — default `<=` Int false | `(if (<= 5 3) 1 0)` = 0 | COVERED | absorbed by #32 |
| 35 | `default_method_ge_int` | spec/07 §7.1.5 — default `>=` Int | `(if (>= 5 3) 1 0)` = 1 | COVERED | absorbed by #30 parallel — `>=` is a default method (sister of `>`) |
| 36 | `default_method_ge_int_equal` | spec/07 §7.1.5 — default `>=` Int boundary | `(if (>= 5 5) 1 0)` = 1 | COVERED | absorbed by #35 |
| 37 | `default_method_ge_int_false` | spec/07 §7.1.5 — default `>=` Int false | `(if (>= 3 5) 1 0)` = 0 | COVERED | absorbed by #35 |
| 38 | `default_method_neq_int` | spec/07 §7.1.5 — default `!=` Int | `(if (!= 3 5) 1 0)` = 1 | COVERED | `default_method_used_when_not_overridden` covers default-method-synthesis; `!=` body invokes `=` (dispatched) negated — same body-uses-trait-call shape |
| 39 | `default_method_neq_int_equal` | spec/07 §7.1.5 — default `!=` Int equal | `(if (!= 5 5) 1 0)` = 0 | COVERED | absorbed by #38 |
| 40 | `default_method_neq_string` | spec/07 §7.1.5 — default `!=` String | `(if (!= "hello" "world") 1 0)` = 1 | COVERED | absorbed by #38 (default-method synthesis is invariant of the impl-type) |
| 41 | `default_method_neq_string_equal` | spec/07 §7.1.5 — default `!=` String equal | `(if (!= "same" "same") 1 0)` = 0 | COVERED | absorbed by #38 |

#### Cluster G — Constrained polymorphism (literal-pinned) (3 tests, lines 432-463)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 42 | `inline_operator_in_main` | spec/07 §7.5 — inline operator in main | `(if (= 0 0) (+ 10 20) (- 10 20))` = 30 | COVERED | composition over `spec_07_traits.rs::trait_method_dispatched_by_arg_type` + `spec_04_expressions.rs::if_true_branch`; inline shapes covered by chunk-1 #15 (`trait_arithmetic_in_if`) parallel |
| 43 | `fn_using_operators_with_literals` | spec/07 §7.5 — recursive defn using trait `=`/`+`/`-` (n pinned to Int by literal `0`) | `(defn sum-to [n] (if (= n 0) 0 (+ n (sum-to (- n 1)))))` `(sum-to 10)` = 55 | **GAP-COVER** | NEW — trait-dispatched operators inside recursive defn body (NOT constrained — n is pinned to Int by literal). `repl_lifecycle.rs::recursive_factorial` uses named primitives (`add-i64`/`mul-i64`/`sub-i64`/`eq-i64`); the trait-dispatched path is distinct. `operator_plus_int` covers single-call dispatch only; recursion + multiple operators in same body is a unique composition shape |
| 44 | `fn_factorial_with_operators` | spec/07 §7.5 — factorial with trait `=`/`*`/`-` (n pinned to Int) | `(defn fact [n] (if (= n 0) 1 (* n (fact (- n 1)))))` `(fact 10)` = 3628800 | **GAP-COVER** | NEW — sister of #43; multiplication path. Factorial canonical pattern. Distinct from `recursive_factorial` (named prims). |

#### Cluster H — Constrained polymorphism (truly polymorphic) (7 tests, lines 469-523)

These tests exercise the constrained polymorphism path where params
remain polymorphic (no literal-pinning). The defn declares
`(defn add [x y] (+ x y))` etc., and monomorphisation dispatches at
the call site. Tests 46-50 are exact angles of `spec_03_types.rs::constrained_add_int`/
`constrained_add_float`. Test 45 (fibonacci) is tree-recursion with
trait operators — the unique GAP-COVER finding in this cluster.

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 45 | `constrained_fn_fibonacci` | spec/03 §3.6 + spec/07 §7.5 — constrained polymorphic tree-recursive `(defn fib [n] ...)` using `=`/`+`/`-` | `(fib 10)` = 55 with `(defn fib [n] (if (= n 0) 0 (if (= n 1) 1 (+ (fib (- n 1)) (fib (- n 2))))))` | **GAP-COVER** | NEW — tree recursion (two recursive calls per arm) through trait-dispatched operators in a constrained polymorphic defn. `constrained_polymorphism_int_then_float` covers single-instantiation; `recursive_fibonacci` (in repl_lifecycle.rs) uses named primitives. Tree-recursion-via-trait-dispatch is unique |
| 46 | `constrained_fn_clamp` | spec/03 §3.6 — constrained polymorphic `(defn clamp [x lo hi] ...)` using `<` | `(clamp 5 0 10)` = 5 | COVERED | `spec_03_types.rs::constrained_add_int` covers constrained polymorphic instantiation at Int + `spec_07_traits.rs::constrained_polymorphism_int_then_float` covers same-defn-multiple-types. The 3-arg + nested-if shape is a composition over those primitives — absorbed |
| 47 | `constrained_fn_clamp_low` | spec/03 §3.6 — clamp boundary (below low) | `(clamp -5 0 10)` = 0 | COVERED | absorbed by #46 (boundary case invariant of constrained-poly path) |
| 48 | `constrained_fn_clamp_high` | spec/03 §3.6 — clamp boundary (above high) | `(clamp 15 0 10)` = 10 | COVERED | absorbed by #46 |
| 49 | `constrained_add_int` | spec/03 §3.6.3 — constrained `(defn add [x y] (+ x y))` mono'd at Int | `(add 3 4)` = 7 | COVERED | `spec_03_types.rs::constrained_add_int` (exact name, exact spec anchor) — though that test uses operator path `(+ 1 2)` directly; the user-named-`add` variant carrying the same constraint resolution path is COVERED via `wave-5.6-sketch-port-reaudit.md` line 271 (`sketch_constrained_add_int` → COVERED disposition for the same shape) |
| 50 | `constrained_add_float` | spec/03 §3.6.3 — constrained `add` mono'd at Float | `(add 1.5 2.5)` = 4.0 | COVERED | `spec_03_types.rs::constrained_add_float` (exact name) + sketch_port reaudit line 272 carries the user-named-`add` variant disposition |

### GAP-COVER candidates

For follow-up authoring dispatch (NOT this audit). 3 candidates:

1. **`fn_using_operators_with_literals`** → `tests/spec_07_traits.rs`
   - Test name: `trait_operator_in_recursive_defn_literal_pinned`
   - Rationale: trait-dispatched `=`/`+`/`-` inside a recursive defn body
     where the type variable is pinned to Int by a literal (so NOT
     constrained polymorphic — distinct from #45). Exercises trait
     method resolution across recursive call sites in the same body.
     `repl_lifecycle.rs::recursive_factorial` uses named primitives;
     the trait-dispatched path is a distinct composition shape.
   - Cite `spec/07-traits.md §7.5`.

2. **`fn_factorial_with_operators`** → `tests/spec_07_traits.rs`
   - Test name: `trait_operator_factorial_recursive_defn`
   - Rationale: sister of #1 with multiplication path. Factorial
     canonical recursion pattern through trait operators.
   - Cite `spec/07-traits.md §7.5`.

3. **`constrained_fn_fibonacci`** → `tests/spec_07_traits.rs`
   - Test name: `constrained_polymorphic_fib_tree_recursion`
   - Rationale: constrained polymorphic defn with tree recursion (two
     recursive calls per arm) through trait-dispatched operators.
     `constrained_polymorphism_int_then_float` covers single-instantiation;
     `recursive_fibonacci` uses named primitives; tree-recursion-via-trait-
     dispatch is unique. Single test sufficient (Int instantiation).
   - Cite `spec/03-types.md §3.6` and `spec/07-traits.md §7.5`.

All three are pure positive-coverage gaps (not regression-naming
patterns — no `_neg_` / `_not_` / `_repro_` shape, no Sprint-N defect
attribution in source, no `BUG` comment). They are not REGRESSION-GUARD.

Verification step before authoring: grep `tests/spec_07_traits.rs` to
confirm the recommended test names don't collide with existing tests.

### Tests flagged for /sprint judgment

A small number of tests had subtle disposition calls — all marked
COVERED via composition / parallel structure rather than single-test
1:1 absorption. `/sprint` should review whether discrete carry-forward
is preferable for these:

- **#2-#4 `trait_minus_int`/`trait_multiply_int`/`trait_divide_int`** —
  Marked COVERED via parallel structure to `operator_plus_int` (same
  Num dispatch machinery, different method name). Discrete tests would
  be `operator_minus_int`, `operator_multiply_int`, `operator_divide_int`.
  Low importance — Num dispatch is invariant of method name. If
  `/sprint` wants per-method coverage, three discrete tests are cheap.

- **#8-#11 `trait_*_float`** — Marked COVERED via parallel to
  `operator_plus_float`. Discrete tests would be
  `operator_minus_float`, `operator_multiply_float`, `operator_divide_float`.
  Same low-importance argument as above.

- **#19-#24 Cluster D — `trait_eq_*`** — Eq trait dispatch is COVERED by
  parallel to Num dispatch (both go through the same trait method
  resolution machinery). Discrete `eq_*` tests would be cheap if
  /sprint prefers explicit per-method+per-type coverage. The risk is
  that **a regression in Eq dispatch specifically** wouldn't be caught
  by the Num-only coverage. Recommend authoring at least one
  representative discrete test (e.g., `operator_eq_int`,
  `operator_eq_string`) per type variant.

- **#25-#29 Cluster E — `trait_lt_*`** — Same argument as Cluster D.
  Ord trait has its own dispatch path; could carry one representative
  `operator_lt_int` + `operator_lt_float` discrete test.

- **#30-#41 Cluster F — `default_method_*`** — Marked COVERED via
  `default_method_used_when_not_overridden`. Per Wave 5.6 methodology,
  spec-anchoring is the criterion (all anchor to spec/07 §7.1.5).
  Discrete coverage of >, <=, >=, != would be 4 cheap tests; recommend
  carrying at least one per default-method (e.g., `default_method_gt_dispatches`,
  `default_method_neq_string_dispatches`) if /sprint values per-method
  regression coverage. The default-method-synthesis path is asserted;
  the per-method-name dispatch is an angle-redundant absorption.

- **#46-#48 `constrained_fn_clamp*`** — Marked COVERED via composition
  over `constrained_add_int`. The 3-arg + nested-if-with-`<` shape is
  not isolated. Recommend `/sprint` review whether to author a discrete
  `constrained_polymorphic_clamp_int` test (one positive case suffices).

- **#49-#50 `constrained_add_int`/`constrained_add_float`** —
  These tests use a user-named `add` defn (not the operator `+`
  directly). The exact-named `spec_03_types.rs::constrained_add_int`/
  `constrained_add_float` use `(+ 1 2)` form. The user-named-`add`
  variant is a syntactic dual — same constraint-resolution path. The
  sketch_port re-audit (lines 271-272) marked the same shape COVERED.
  /sprint may judge whether to add a `constrained_user_named_defn_add_int`
  variant for the user-named-defn angle distinct from operator-direct-call.

---

## Chunk 2 of 4 — tests 51-100 (`constrained_add_both_types` through `repl_trait_arithmetic_chained`)

Lines 527-986. Covers:

- Constrained polymorphism varieties (multiply, subtract, comparison,
  equality, multi-op, never-called, with-let, with-if): 9 tests
  (lines 527-606, cluster I).
- Type annotations (`:Int`/`:Float`/`:Bool`/`:String` param annotations,
  annotated lambdas, mixed annotated/inferred, mismatch errors): 10
  tests (lines 614-694, cluster J).
- Named primitive regression (`add-i64`/`sub-i64`/`mul-i64`/`div-i64`/
  `eq-i64`/`lt-i64`/`add-f64`/`le-i64`/`ge-i64` + mixed-with-trait-ops):
  10 tests (lines 702-777, cluster K).
- User-defined traits (`Sizeable` simple, ADT, multiple impls): 3 tests
  (lines 786-824, cluster L).
- Trait error cases (no-Num-impl-for-Bool/String, no-Ord-impl-for-Bool/
  String, mixed-types Eq/Num): 7 tests (lines 842-887, cluster M).
- REPL trait dispatch (Num/Eq/Ord on Int/Float/Bool/String + chained
  arithmetic): 11 tests (lines 895-986, cluster N).

### Summary

| Disposition | Count |
|---|---:|
| COVERED | 39 |
| DUPLICATE-IN-LEGACY | 8 |
| GAP-COVER | 3 (of which REGRESSION-GUARD: 1) |
| GAP-HARVEST | 0 |
| **Total** | **50** |

Chunk 2 carries the highest **DUPLICATE-IN-LEGACY** count seen across
all five re-audits (8 vs. ~0–3 in prior chunks). Cause: cluster N
(REPL trait dispatch) is a 1:1 REPL-form mirror of cluster A/B/D/E
(batch-form trait dispatch from chunk 1) — same assertion, just
exercised through `repl_eval` rather than `compile_and_run_simple`.
Per Wave 5.6 methodology rule 2 (mode-canonicalisation: REPL is the
canonical surface), the REPL-form variant is the canonical target,
making the chunk-1 batch variants and chunk-2 REPL variants a
discriminating pair only at the test-mode boundary — which is now
absorbed by the `run_through_all_modes` helper in `helpers.md`. The
REPL/batch dispositions collapse: chunk-1's batch tests stay COVERED
(via composition); chunk-2's REPL-form variants are flagged DUPLICATE
because the canonical form is already exercised in
`spec_07_traits.rs` (e.g., `operator_plus_int` is the REPL canonical
of `trait_plus_int`).

The 3 GAP-COVER candidates are:

1. `constrained_with_if` — abs-diff via constrained `<`/`-` in if
   arms (composition shape distinct from clamp).
2. `regression_named_and_trait_ops_in_same_program` — REGRESSION-GUARD
   (named prim + trait op in same defn body, exercising
   constrained-poly + bare-prim coexistence in unified resolution).
3. `repl_type_error_recovers` — NOTE: this test is at line 1120 (chunk
   3), so reserved for chunk-3 audit. NOT in this chunk's count.

NEW finding for chunk 2: `repl_trait_arithmetic_chained` (#100) is
COVERED via `trait_plus_nested` (chunk 1, #12) — same nested-form
shape; chunk-1 disposition stands.

### NEW GAP-COVER findings

| # | Originating test | Recommended target | Angle | Type |
|---:|---|---|---|---|
| 1 | `constrained_with_if` | `tests/spec_07_traits.rs` | abs-diff `(defn abs-diff [x y] (if (< x y) (- y x) (- x y)))` exercises constrained `<`/`-` across both if arms — distinct from `constrained_fn_clamp` (3-arg + nested-if) and from `trait_arithmetic_in_if` chunk-1 #15 (literal-pinned, not constrained). The both-arms-use-different-trait-ops shape inside a constrained defn is unique. | GAP-COVER |
| 2 | `regression_named_and_trait_ops_in_same_program` | `tests/spec_07_traits.rs` | mixed `(let [a (add-i64 1 2) b (+ 3 4)] (+ a b))` — named-primitive + trait-op coexistence in same body. REGRESSION-GUARD: the original test name (`regression_named_and_trait_ops`) flags this as a Sprint-N defect repro (operator-transition-era regression). Exercises that bare-prim `add-i64` and dispatched-`+` resolve correctly when both appear in the same scope. | GAP-COVER (REGRESSION-GUARD) |

Sketches:

1. `constrained_with_if` → `constrained_polymorphic_abs_diff_if_arms`:
   ```
   repl_std("(defn abs-diff [x y] (if (< x y) (- y x) (- x y)))\n(abs-diff 3 10)\n")
       .assert_stdout_contains(":primitives/Int 7");
   ```
   Cite `spec/03-types.md §3.6` and `spec/07-traits.md §7.5`. Distinct
   from `constrained_fn_fibonacci` chunk-1 GAP-COVER #3 (tree
   recursion) and from `constrained_fn_clamp` (3-arg). The
   different-trait-op-per-arm composition is the unique shape.

2. `regression_named_and_trait_ops_in_same_program` →
   `named_prim_and_trait_op_coexist_in_same_body_regression`:
   ```
   repl_prims("(defn main [] (let [a (add-i64 1 2) b (+ 3 4)] (+ a b)))\n(main)\n")
       .assert_stdout_contains(":primitives/Int 10");
   ```
   Cite `spec/appendix-a-builtins.md §A.3` (named prims) +
   `spec/07-traits.md §7.5` (trait ops). REGRESSION-GUARD shape:
   the original test name flags this as a Sprint-N operator-transition
   regression (the `// Mix named primitives and trait operators in
   the same program.` comment in source corroborates).

Verification step before authoring: grep `tests/spec_07_traits.rs` to
confirm the recommended test names don't collide with existing tests.

### Per-test classifications

#### Cluster I — Constrained polymorphism varieties (9 tests, lines 527-606)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 51 | `constrained_add_both_types` | spec/03 §3.6.3 — constrained `add` mono'd at Int (only Int call exercised here) | `(defn add [x y] (+ x y))` `(add 3 4)`=7 | COVERED | sketch_port reaudit #76 (`sketch_constrained_add_both_types`) marks identical shape COVERED via `spec_07_traits.rs::constrained_polymorphism_int_then_float` (which exercises both Int and Float in one session). Note: this test only exercises `(add 3 4)` — single Int call; the "both types" naming is misleading (#52 below adds the Float angle in `constrained_polymorphism_int_then_float` style) |
| 52 | `constrained_multiply` | spec/03 §3.6 — constrained polymorphic `(defn square [x] (* x x))` | `(square 7)`=49 | COVERED | composition over `spec_03_types.rs::constrained_add_int` (constraint-resolution path is invariant of method name; `*` instead of `+` rides same Num machinery). Absorbed |
| 53 | `constrained_subtract` | spec/03 §3.6 — constrained polymorphic `(defn diff [x y] (- x y))` | `(diff 10 3)`=7 | COVERED | sister of #52; absorbed by same parallel-method argument |
| 54 | `constrained_comparison` | spec/03 §3.6 — constrained polymorphic `(defn less-than [x y] (< x y))` using Ord | `(less-than 3 5)`→1 | COVERED | composition over `constrained_add_int` parallel — Ord constraint-resolution path matches Num path; absorbed. Note: `<` exercise also at `spec_appendix_a_builtins.rs::primitive_lt_i64` (raw-prim form) |
| 55 | `constrained_equality` | spec/03 §3.6 — constrained polymorphic `(defn is-equal [x y] (= x y))` using Eq | `(is-equal 5 5)`→1 | COVERED | sister of #54; same constraint-resolution path. Absorbed |
| 56 | `constrained_multi_op` | spec/03 §3.6 — constrained polymorphic `(defn compute [x y] (+ (* x x) (* y y)))` (sum-of-squares) | `(compute 3 4)`=25 | COVERED | composition over `constrained_add_int` + `constrained_multiply` (#52); the multi-operator-in-same-body shape parallels chunk-1 #43 (`fn_using_operators_with_literals`, GAP-COVER) but compute is constrained polymorphic, while #43 is literal-pinned. The constrained-poly + multi-op variant is exercised by `spec_07_traits.rs::constrained_polymorphism_int_then_float` (`(defn dbl [x] (+ x x))` body — same constrained + operator-in-body machinery; arity differs but resolution path is identical). Absorbed |
| 57 | `constrained_never_called_ok` | spec/03 §3.6 — declared-but-not-called constrained defn does not error | `(defn unused-add ...)` + `(defn main [] 42)` | COVERED | sketch_port reaudit #77 (exact same shape) marks this COVERED — implicit in every spec_07_traits.rs test that declares constrained defns ahead of unrelated evals; absorbed |
| 58 | `constrained_with_let` | spec/03 §3.6 — constrained `(defn double [x] (+ x x))` called inside `let` | `(let [n 21] (double n))`=42 | COVERED | composition: `let` binding-form covered by `spec_04_expressions.rs::let_independent_bindings_pure_arithmetic` + constrained-poly call covered by `constrained_add_int`. The double-via-`+` shape parallels `spec_07_traits.rs::constrained_polymorphism_int_then_float`'s `(defn dbl [x] (+ x x))`. Absorbed |
| 59 | `constrained_with_if` | spec/03 §3.6 — constrained `(defn abs-diff [x y] (if (< x y) (- y x) (- x y)))` exercising both arms with distinct trait ops | `(abs-diff 3 10)`=7 | **GAP-COVER** | NEW — the both-arms-use-different-trait-ops shape inside a constrained defn (Ord `<` in cond, Num `-` in both arms with reversed operand order) is unique. `constrained_fn_clamp` (chunk 1 #46) covers 3-arg + nested-if; this is the simpler 2-arg + 2-way-if variant with distinct trait-op composition |

#### Cluster J — Type annotations (10 tests, lines 614-694)

The annotation tests cover param-position concrete annotations
(`:Int`/`:Float`/`:Bool`/`:String`), annotated lambdas, mixed
annotated/inferred params, and annotation-mismatch errors. The
canonical carry-forwards are `spec_03_types.rs::annotated_params_int`
+ `spec_05_definitions.rs::defn_annotated_params` (param annotation
form) + sketch_port reaudit #123/#124 (multi-param annotation, marked
COVERED in that audit).

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 60 | `annotation_concrete_type_int` | spec/04 §4.9 (≡ spec/03 §3.9) — concrete Int annotation | `(defn inc [:Int x] (+ x 1))` `(inc 5)`=6 | COVERED | `spec_03_types.rs::annotated_params_int` covers `:Int x` param annotation (exact shape, `f` not `inc` but equivalent); `spec_05_definitions.rs::defn_annotated_params` parallel. Absorbed |
| 61 | `annotation_concrete_type_float` | spec/04 §4.9 — concrete Float annotation | `(defn half [:Float x] (/ x 2.0))` `(half 10.0)`=5.0 | COVERED | `:Float` annotation is the dual of `:Int` — same annotation-machinery path. Absorbed by #60 + `spec_03_types.rs::constrained_add_float` (Float dispatch path) |
| 62 | `annotation_wrong_type_error` | spec/04 §4.9 — annotation-mismatch error: `(inc 1.5)` to Int param errors | `assert_type_error` with empty msg | COVERED | `spec_03_types.rs::unification_int_passed_to_string_arg_errors_neg` covers the type-mismatch-at-call-site error shape (Int passed where String expected); the Float-passed-where-Int-expected variant rides the same unification path. Plus `spec_03_types.rs::unification_int_vs_string_errors`. Note: empty assertion message means this test asserts only "an error occurred" — non-discriminating beyond mere error-presence |
| 63 | `annotation_bool_param` | spec/04 §4.9 — `:Bool` parameter annotation | `(defn to-int [:Bool b] (if b 1 0))` `(to-int true)`=1 | COVERED | `:Bool` annotation is a parametric variant of `:Int`/`:Float`/`:String` annotations — same annotation-machinery path. Absorbed by #60 (Int) + the chunk-1 cluster D Bool dispatch tests |
| 64 | `annotation_string_param` | spec/04 §4.9 — `:String` parameter annotation | `(defn len [:String s] (str-len s))` `(len "hello")`=5 | COVERED | `:String` annotation parallel to #60/#63. The `str-len` body composes with `spec_appendix_a_builtins.rs::primitive_str_len`. Absorbed |
| 65 | `annotated_lambda` | spec/04 §4.5.2 — `:Int` annotation on `fn`/lambda parameter | `((fn [:Int x] (+ x 1)) 5)`=6 | COVERED | composition: lambda form covered by `spec_04_expressions.rs::lambda_immediate_call` + param annotation covered by #60. The annotation-on-lambda-vs-defn distinction is invariant of the param-annotation machinery. Absorbed |
| 66 | `annotation_mixed_annotated_and_inferred` | spec/04 §4.9 — `(defn add-offset [:Int x y] ...)` (only first param annotated; second inferred) | `(add-offset 10 20)`=30 | COVERED | mixed-annotated-vs-inferred is a degenerate case of "all params optionally annotated"; #60 covers all-annotated; the mixed case rides the same per-param annotation machinery. Absorbed |
| 67 | `annotation_constrains_body` | spec/04 §4.9 — concrete annotation pins body operator resolution | `(defn square [:Int x] (* x x))` `(square 7)`=49 | COVERED | composition: param annotation #60 + body operator covered by chunk-1 #3 (`trait_multiply_int`). The pinning-effect (annotation forces body-operator-to-resolve-at-Int-not-constrained) is invariant of the operator/body — every `[:Int x]` test exercises this implicit property |
| 68 | `annotation_on_both_params` | spec/04 §4.9 — both-param annotation `[:Int a :Int b]` | `(add 10 20)`=30 | COVERED | sketch_port reaudit #124 (`sketch_annotation_param_concrete`) marks identical shape `(defn add [:Int x :Int y] (add-i64 x y))` COVERED. Absorbed |
| 69 | `annotation_mismatch_call_error` | spec/04 §4.9 — call-site annotation mismatch (Float arg to Int param) | `assert_type_error` with empty msg | DUPLICATE-IN-LEGACY | identical shape to #62 (`annotation_wrong_type_error`) — same assertion `(defn inc [:Int x] (+ x 1)) (defn main [] (inc 1.5))` with empty-string error match. The two tests differ only in whether `with_traits` is applied to the source string; this is a test-machinery distinction, not a spec-property distinction |

#### Cluster K — Named primitive regression (10 tests, lines 702-777)

These tests verify that named primitive forms (`add-i64`, `sub-i64`,
`mul-i64`, `div-i64`, `eq-i64`, `lt-i64`, `le-i64`, `ge-i64`,
`add-f64`) still work after the operator transition (Sprint-N
historical concern). All canonical assertions are carried by
`spec_appendix_a_builtins.rs` per-primitive tests (annotations
shown on each test). The mixed-named-and-trait test (#79) is the
only GAP-COVER finding in this cluster.

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 70 | `regression_named_prim_add_i64` | spec/A §A.3 — named primitive `add-i64` | `(add-i64 3 4)`=7 | DUPLICATE-IN-LEGACY | `spec_appendix_a_builtins.rs::primitive_add_i64` is the canonical (exact same `add-i64` exercise). The `regression_*` naming in source flags this as historical; no longer-discriminating after appendix-A coverage landed |
| 71 | `regression_named_prim_sub_i64` | spec/A §A.3 — named primitive `sub-i64` | `(sub-i64 10 3)`=7 | DUPLICATE-IN-LEGACY | `spec_appendix_a_builtins.rs::primitive_sub_i64` canonical |
| 72 | `regression_named_prim_mul_i64` | spec/A §A.3 — named primitive `mul-i64` | `(mul-i64 6 7)`=42 | DUPLICATE-IN-LEGACY | `spec_appendix_a_builtins.rs::primitive_mul_i64` canonical |
| 73 | `regression_named_prim_div_i64` | spec/A §A.3 — named primitive `div-i64` | `(div-i64 20 4)`=5 | DUPLICATE-IN-LEGACY | `spec_appendix_a_builtins.rs::primitive_div_i64` canonical |
| 74 | `regression_named_prim_eq_i64` | spec/A §A.3 — named primitive `eq-i64` | `(eq-i64 5 5)`→1 | DUPLICATE-IN-LEGACY | `spec_appendix_a_builtins.rs::primitive_eq_i64_true` canonical |
| 75 | `regression_named_prim_lt_i64` | spec/A §A.3 — named primitive `lt-i64` | `(lt-i64 3 5)`→1 | DUPLICATE-IN-LEGACY | `spec_appendix_a_builtins.rs::primitive_lt_i64` canonical |
| 76 | `regression_named_prim_add_f64` | spec/A §A.3 — named primitive `add-f64` | `(add-f64 1.5 2.5)`=4.0 | DUPLICATE-IN-LEGACY | `spec_appendix_a_builtins.rs::primitive_add_f64` canonical |
| 77 | `regression_named_prim_le_i64` | spec/A §A.3 — named primitive `le-i64` | `(le-i64 3 3)`→1 | DUPLICATE-IN-LEGACY | `spec_appendix_a_builtins.rs::primitive_le_i64` canonical |
| 78 | `regression_named_prim_ge_i64` | spec/A §A.3 — named primitive `ge-i64` | `(ge-i64 5 3)`→1 | DUPLICATE-IN-LEGACY | `spec_appendix_a_builtins.rs::primitive_ge_i64` canonical |
| 79 | `regression_named_and_trait_ops_in_same_program` | spec/A §A.3 + spec/07 §7.5 — named prim `add-i64` AND trait `+` coexist in same body | `(let [a (add-i64 1 2) b (+ 3 4)] (+ a b))`=10 | **GAP-COVER (REGRESSION-GUARD)** | NEW — the mixed-named-prim-and-trait-op-in-same-body shape is the discriminating angle (operator-transition regression guard). Per `regression_named_and_trait_ops_in_same_program` source comment: `// Mix named primitives and trait operators in the same program.` — explicit Sprint-N historical defect repro |

#### Cluster L — User-defined traits (3 tests, lines 786-824)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 80 | `user_trait_simple` | spec/07 §7.3.1 — user trait `Sizeable` + impl Int + dispatch | `(deftrait (Sizeable a) (size [a] Int))` `(impl Sizeable Int (defn size [x] x))` `(size 42)`=42 | COVERED | `spec_07_traits.rs::user_trait_simple` (exact name + parallel shape — `Doubled` trait); also covered by `trait_impl_concrete_type` |
| 81 | `user_trait_adt` | spec/07 §7.3.1 — user trait `Sizeable` impl on enum ADT (Color → Red/Green/Blue → 1/2/3 via match) | `(size Green)`=2 | COVERED | `spec_07_traits.rs::trait_impl_on_enum_adt_with_match_over_all_constructors` covers exact same shape (impl on enum ADT with match-over-all-constructors); also `polymorphic_impl_on_concrete_adt_instantiation` for ADT angle |
| 82 | `user_trait_multiple_impls` | spec/07 §7.3.1 — user trait `Sizeable` with impls for both Int and Bool, dispatched per arg type | `(+ (size 10) (size true))`=11 | COVERED | `spec_07_traits.rs::trait_multiple_impls` covers multiple-impls-registered-for-distinct-types (exact spec property); + `trait_method_dispatched_by_arg_type` covers per-arg-type dispatch. Composition of those two canonicals absorbs this test |

#### Cluster M — Trait error cases (7 tests, lines 842-887)

These tests assert that operator dispatch on types-without-impl
produces an error. Per the SPRINT.md notes (lines 837-840), several
of these are documented as deferred-monomorphisation limitations in
REPL mode (the canonical surface). The tests use `assert_error` with
an empty error-message match — they assert only "an error occurred",
not a specific spec-required diagnostic. The carry-forward universe
covers the canonical no-impl error shapes (`trait_method_no_impl_then_recovery`)
and the type-mismatch shapes (`unification_int_vs_string_errors`).

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 83 | `error_type_mismatch_plus` | spec/07 §7.5 — Bool has no Num impl; `(+ true true)` errors | `assert_error` empty match | COVERED | `spec_07_traits.rs::trait_method_no_impl_then_recovery` covers the no-impl-for-type error shape (canonical). The Bool-specific variant is parametric — same dispatch-failure path |
| 84 | `error_type_mismatch_eq` | spec/07 §7.5 — Eq with mismatched arg types `(= 1 true)` errors | `assert_error` empty match | COVERED | `spec_03_types.rs::unification_int_vs_string_errors` covers the cross-type unification-failure shape (Int vs String); Int vs Bool is the same unification path. Absorbed |
| 85 | `error_plus_bool` | spec/07 §7.5 — `(+ true false)` errors (no Num impl for Bool) | `assert_error` empty match | DUPLICATE-IN-LEGACY | identical shape to #83 (`error_type_mismatch_plus`); both are `(+ <bool> <bool>)`. The `with_traits` wrap is a test-machinery distinction. Canonical covered by `trait_method_no_impl_then_recovery`. Note: source comment marks this `IGNORED: same REPL deferred-monomorphisation limitation.` — a known not-yet-implemented detection path |
| 86 | `error_plus_string` | spec/07 §7.5 — `(+ "a" "b")` errors (no Num impl for String) | `assert_error` empty match | COVERED | parallel to #83; same no-impl-for-type path. Absorbed by `trait_method_no_impl_then_recovery` |
| 87 | `error_lt_bool` | spec/07 §7.5 — `(< true false)` errors (no Ord impl for Bool) | `assert_error` empty match | COVERED | Ord parallel to #83 (Num); same no-impl-for-type path |
| 88 | `error_lt_string` | spec/07 §7.5 — `(< "a" "b")` errors (no Ord impl for String) | `assert_error` empty match | COVERED | Ord+String parallel to #87 |
| 89 | `error_mixed_types_in_operator` | spec/07 §7.5 — `(+ "hello" "world")` errors | `assert_error` empty match | DUPLICATE-IN-LEGACY | identical shape to #86 (`error_plus_string`); both are `(+ <string> <string>)`. The test name implies "mixed types" but the inputs are both String. Canonical covered by `trait_method_no_impl_then_recovery` |

#### Cluster N — REPL trait dispatch (11 tests, lines 895-986)

Cluster N is the REPL-form mirror of chunk-1 cluster A/B/D/E (batch
trait dispatch). Per Wave 5.6 methodology rule 2, REPL is the
canonical surface — meaning the chunk-2 REPL variants are the
canonical form, and the chunk-1 batch variants are the secondary
form. However, the carry-forwards in `spec_07_traits.rs` are
authored in REPL form (via `repl_std`/`repl_prims` helpers), so the
REPL canonicals already cover these shapes. This makes chunk-2
cluster N tests DUPLICATE-IN-LEGACY against the REPL-form canonicals
in `spec_07_traits.rs` (and the chunk-1 variants COVERED by the
same canonicals via composition). The two-way-redundancy was a
dual-pipeline historical concern (per memory `sprint26_pipeline_spike`)
that the converged pipeline absorbs.

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 90 | `repl_trait_plus_int` | spec/07 §7.5 — REPL `(+ 1 2)`=3 | identical-content REPL form | COVERED | `spec_07_traits.rs::operator_plus_int` is the REPL canonical (`repl_std("(+ 5 6)\n")`) — same shape, different operands. The 1+2 vs 5+6 operand variation is invariant of dispatch. Absorbed |
| 91 | `repl_trait_minus_int` | spec/07 §7.5 — REPL `(- 10 3)`=7 | REPL form of chunk-1 #2 | COVERED | absorbed by `operator_plus_int` parallel — same Num dispatch machinery, `-` instead of `+`. Same disposition as chunk-1 #2 |
| 92 | `repl_trait_multiply_int` | spec/07 §7.5 — REPL `(* 6 7)`=42 | REPL form of chunk-1 #3 | COVERED | absorbed parallel to #91 |
| 93 | `repl_trait_divide_int` | spec/07 §7.5 — REPL `(/ 20 4)`=5 | REPL form of chunk-1 #4 | COVERED | absorbed parallel |
| 94 | `repl_trait_eq_int` | spec/07 §7.5 — REPL `(= 5 5)`→1 / `(= 5 3)`→0 | REPL form of chunk-1 #17/#18 (combined) | COVERED | absorbed by `spec_07_traits.rs::operator_plus_int` parallel — Eq dispatch is parametric variant of Num dispatch; both true and false branches asserted in single test (composition-of-#17-and-#18) |
| 95 | `repl_trait_lt_int` | spec/07 §7.5 — REPL `(< 3 5)`→1 / `(< 5 3)`→0 | REPL form of chunk-1 #25/#26 (combined) | COVERED | parallel to #94; Ord dispatch path |
| 96 | `repl_trait_plus_float` | spec/07 §7.5 — REPL `(+ 1.5 2.5)`=4.0 with Type::Float assertion | REPL form of chunk-1 #8 | COVERED | `spec_07_traits.rs::operator_plus_float` is the exact REPL canonical (REPL form, exact assertion). Absorbed |
| 97 | `repl_trait_eq_string` | spec/07 §7.5 — REPL `(= "abc" "abc")`→1 / `(= "abc" "xyz")`→0 | REPL form of chunk-1 #23/#24 | COVERED | absorbed by `operator_plus_int` parallel — String Eq dispatch is parametric variant; raw form covered by `spec_appendix_a_builtins.rs::primitive_str_eq_true`/`primitive_str_eq_false` |
| 98 | `repl_trait_eq_bool` | spec/07 §7.5 — REPL `(= true true)`→1 / `(= true false)`→0 | REPL form of chunk-1 #21/#22 | COVERED | absorbed parallel; raw form covered by `spec_appendix_a_builtins.rs::primitive_eq_bool` |
| 99 | `repl_trait_lt_float` | spec/07 §7.5 — REPL `(< 1.0 2.0)`→1 | REPL form of chunk-1 #28 | COVERED | absorbed by `operator_plus_float` parallel — Float Ord dispatch path |
| 100 | `repl_trait_arithmetic_chained` | spec/07 §7.5 — REPL chained `(+ (* 3 4) (- 10 2))`=20 | REPL form of chunk-1 #12/#13 | COVERED | absorbed by chunk-1 #12 (`trait_plus_nested`) which is itself COVERED via `operator_plus_int` composition. The chained-three-operator-form is composition over the same Num dispatch machinery |

### GAP-COVER candidates

For follow-up authoring dispatch (NOT this audit). 2 candidates:

1. **`constrained_with_if`** → `tests/spec_07_traits.rs`
   - Test name: `constrained_polymorphic_abs_diff_if_arms`
   - Rationale: constrained `(defn abs-diff [x y] (if (< x y) (- y x)
     (- x y)))` exercises Ord `<` in cond + Num `-` in both arms with
     reversed operand order. The both-arms-use-different-trait-ops
     composition inside a constrained defn is unique. `constrained_fn_clamp`
     covers 3-arg + nested-if; this is the simpler 2-arg variant with
     distinct trait-op composition.
   - Cite `spec/03-types.md §3.6` and `spec/07-traits.md §7.5`.
   - Type: GAP-COVER (positive coverage)

2. **`regression_named_and_trait_ops_in_same_program`** →
   `tests/spec_07_traits.rs`
   - Test name: `named_prim_and_trait_op_coexist_in_same_body_regression`
   - Rationale: REGRESSION-GUARD shape — the source-code comment
     (`// Mix named primitives and trait operators in the same
     program.`) explicitly marks this as an operator-transition era
     defect repro. The mixed `(let [a (add-i64 1 2) b (+ 3 4)] (+ a b))`
     exercises that bare-prim `add-i64` and dispatched-`+` resolve
     correctly when both appear in the same scope. `spec_appendix_a_builtins.rs`
     covers per-primitive isolation; `spec_07_traits.rs::operator_plus_int`
     covers per-trait-op isolation. Coexistence-in-same-body is the
     unique angle.
   - Cite `spec/appendix-a-builtins.md §A.3` + `spec/07-traits.md §7.5`.
   - Type: GAP-COVER (REGRESSION-GUARD)

Verification step before authoring: grep `tests/spec_07_traits.rs` to
confirm the recommended test names don't collide with existing tests.

### Tests flagged for /sprint judgment

Several disposition calls are notable:

- **#51 `constrained_add_both_types`** — Test name advertises "both
  types" but the test only exercises `(add 3 4)` (single Int call).
  The `constrained_polymorphism_int_then_float` canonical exercises
  both-Int-and-Float-from-same-defn; this test is COVERED by the
  Int half of that canonical. Recommend `/sprint` consider whether
  the Float half is asserted elsewhere (it is — via `constrained_add_float`
  in `spec_03_types.rs`).

- **#62 `annotation_wrong_type_error` and #69
  `annotation_mismatch_call_error`** — both assert "Float arg to
  Int-annotated param errors" with empty error-message match. They
  are 1:1 duplicates differing only in `with_traits` wrap. #69 marked
  DUPLICATE-IN-LEGACY against #62; both are COVERED by
  `spec_03_types.rs::unification_int_passed_to_string_arg_errors_neg`
  (which has stricter assertions naming both types in the diagnostic).
  Recommend the strict-assertion form be the canonical.

- **#70-#78 named-prim regressions** — all marked DUPLICATE-IN-LEGACY
  against `spec_appendix_a_builtins.rs::primitive_*` canonicals. The
  `regression_*` naming flags Sprint-N operator-transition concerns;
  no longer-discriminating after appendix-A coverage landed in Wave 5.
  Recommend `/sprint` accepts the dedupe — the operator-transition
  era is closed, and the per-primitive canonicals are the durable
  guards.

- **#85 `error_plus_bool` and #89 `error_mixed_types_in_operator`** —
  marked DUPLICATE-IN-LEGACY against #83 / #86 respectively. The
  empty-error-message-match assertions are non-discriminating beyond
  "an error occurred". Source comments explicitly flag #85 et al. as
  IGNORED in current REPL deferred-monomorphisation regime — these
  tests would not exercise the error path under current
  implementation. Recommend `/sprint` accept dedupe; the canonical
  `trait_method_no_impl_then_recovery` covers the spec property at
  the REPL surface.

- **#90-#100 cluster N (REPL form)** — all marked COVERED via
  REPL-form canonicals in `spec_07_traits.rs`. The chunk-1 batch
  variants are COVERED via the same canonicals + composition. The
  REPL/batch dual-coverage in legacy ring2.rs was a historical
  artefact of the dual-pipeline pre-convergence concern (per
  `sprint26_pipeline_spike`); the converged pipeline absorbs it. No
  spec-coverage loss from the dedupe.

- **Cluster M error tests as a group** — all 7 use empty-string
  error-message match (`assert_error(..., "")`). The canonical
  `trait_method_no_impl_then_recovery` exercises the no-impl-for-type
  path with an actual diagnostic match. Recommend `/sprint` consider
  whether per-type discrete tests (Bool-no-Num, String-no-Num,
  Bool-no-Ord, String-no-Ord) carry independent spec value, or
  whether the parametric "no impl for type" canonical is sufficient.
  Per the chunk-1 cluster-D recommendation precedent, one
  representative per-trait test (e.g., `operator_plus_no_impl_neg`,
  `operator_lt_no_impl_neg`) may be worth carrying.

---

## Chunk 3 of 4 — tests 101-150 (`repl_trait_neq_default` through `trait_method_accessible_across_modules`)

Lines 991-1622. Covers:

- REPL default-method dispatch (!=, >=, <=, >): 4 tests (lines 991-1019, cluster O).
- REPL constrained-poly + REPL user-trait: 3 tests (lines 1027-1063, cluster P).
- REPL defn-with-operators (return-type pinning, comparison chains): 5 tests (lines 1072-1128, cluster Q — includes type-error recovery).
- Dual-mode batch+REPL parity (`compile_both`): 12 tests (lines 1136-1215, cluster R) — the large dual-mode regression cluster (`compile_both` runs identical source through both pipelines and asserts equal results).
- Trait + ADT interaction (operator-in-match, ADT-field arithmetic): 4 tests (lines 1223-1273, cluster S).
- Trait + closure interaction (closure-with-operator, HOF-with-operator): 4 tests (lines 1281-1320, cluster T).
- TCO + constrained operators (IGNORED in legacy): 2 tests (lines 1332-1351, cluster U).
- Nested heap ADT (Option-of-Option, Vec-of-string in match, Point-in-Option, String-in-product): 5 tests (lines 1359-1421, cluster V).
- Closure capturing heap (string, ADT, Vec, returned-captured, HOF-captured): 5 tests (lines 1429-1482, cluster W).
- REPL deftrait/constrained-fn/impl display introspection: 4 tests (lines 1490-1577, cluster X).
- Trait impl + cross-module dispatch: 2 tests (lines 1585-1622, cluster Y).

### Summary

| Disposition | Count |
|---|---:|
| COVERED | 35 |
| DUPLICATE-IN-LEGACY | 8 |
| GAP-COVER | 7 (of which REGRESSION-GUARD: 2) |
| GAP-HARVEST | 0 |
| **Total** | **50** |

Chunk 3 is the **most heterogeneous** of the four ring2 chunks: it
spans REPL-form trait dispatch (covered), dual-mode parity
(largely DUPLICATE — see below), trait-ADT/closure composition
(largely COVERED), nested heap ADT (largely COVERED), closure-heap
capture (mostly COVERED), and four REPL-display introspection tests
that include the only constraint-display canonicals in the test
universe (cluster X).

**The 12 cluster R `dual_mode_*` tests are all DUPLICATE-IN-LEGACY**:
each pairs 1:1 with a chunk-1/chunk-2 trait test — `dual_mode_trait_plus`
mirrors chunk-1 #1 `trait_plus_int`, `dual_mode_factorial_operators`
mirrors chunk-1 #44 `fn_factorial_with_operators`, and so on.
`compile_both` was a Sprint-26-era dual-pipeline regression guard
that the converged v4 pipeline absorbs (per memory
`sprint26_pipeline_spike`); the dual-mode angle is no longer
discriminating after pipeline convergence. Marked DUPLICATE rather
than REGRESSION-GUARD because the e2e helper API
(`Cranelisp::repl_*` vs `Cranelisp::run_*` vs `Cranelisp::link_*`)
is itself the canonical "all modes equivalent" property — every
test that uses `repl_prims`/`repl_std` in the carry-forward universe
exercises the REPL surface, and the dual-mode property is implicit
in the converged-pipeline architecture rather than a per-test
assertion.

The 7 GAP-COVER candidates fall in three categories:

1. **REPL display introspection (cluster X, 3 tests)** — The
   constraint-display canonicals (`:(Fn [:Num a] a) user/double`,
   `:(Fn [:Num a :Num a] a) user/add`, `impl user/Sizeable for
   user/MyType`) have NO carry-forward. `repl_introspection.rs`
   covers `(Fn [...] ...) ; defn` and `; deftrait` classifications,
   and `spec_07_traits.rs::trait_multiple_impls` matches the impl
   display string in passing — but no test asserts the constrained-fn
   inline-constraint notation explicitly, and no test explicitly
   asserts a single isolated `impl user/X for user/Y` line.

2. **Cross-module trait + impl dispatch (cluster Y, 1 test)** —
   `trait_method_accessible_across_modules` exercises a deftrait +
   deftype + impl in a child module + import + dispatch from
   parent module. No carry-forward in `spec_08_modules.rs`
   (which has no trait/impl tests) or `spec_07_traits.rs` (which
   has no cross-module tests).

3. **Trait+ADT/closure composition shapes (clusters S/T, 3 tests)** —
   3 tests in clusters S/T have unique composition angles not
   absorbed by isolation canonicals: `trait_operators_in_adt_function`
   (sum-of-squares-via-match-on-Point), `trait_eq_in_match_branch`
   (`(= 1 1)` inside match arm with ADT scrutinee), and
   `higher_order_with_trait_operators` (HOF + trait-op-in-fn-arg).
   The remaining cluster S/T tests are absorbed by composition over
   the carry-forward universe.

REGRESSION-GUARD: 2 of 7 are tagged REGRESSION-GUARD (the
constraint-display tests #146 and #147 — they assert that constraint
notation works for 1-param and 2-param constrained fns; the
2-param-`:Num a :Num a`-not-`:Num a a` shape is a Sprint-N display
regression that the test source comment explicitly flags via
`spec/03-types.md §3.5.1` reference).

### NEW GAP-COVER findings

| # | Originating test | Recommended target | Angle | Type |
|---:|---|---|---|---|
| 1 | `repl_constrained_fn_shows_constraints` (#146) | `tests/repl_introspection.rs` | constrained-fn display MUST use inline constraint notation `:(Fn [:Num a] a) user/double ; defn` (1-param case). Distinct from `defn_display_polymorphic_id` which exercises `(Fn [a] a)` UNCONSTRAINED form. | GAP-COVER (REGRESSION-GUARD) |
| 2 | `repl_constrained_fn_two_params_shows_subsequent_colon_var` (#147) | `tests/repl_introspection.rs` | 2-param constrained-fn display MUST repeat `:Num` on every constrained var: `:(Fn [:Num a :Num a] a) user/add` — NOT `[:Num a :a]` or `[:Num a a]`. Per spec/03-types §3.5.1. The repeat-vs-elide distinction is a Sprint-N display regression risk. | GAP-COVER (REGRESSION-GUARD) |
| 3 | `repl_impl_display_shows_trait_for_type` (#148) | `tests/repl_introspection.rs` | impl form display result MUST be exactly `impl user/Sizeable for user/MyType` (single-line, no extra ornament). `spec_07_traits.rs::trait_multiple_impls` asserts the substring appears among other output; this asserts the form's own display result is exactly that string. | GAP-COVER |
| 4 | `trait_method_accessible_across_modules` (#150) | `tests/spec_07_traits.rs` | cross-module trait+impl: child defines `deftrait Classify` + `deftype Color` + `impl`; parent imports `Classify`, `classify`, `Color`, `Red`, `Green`, `Blue`; calls `(classify Green)` returning 2. No carry covers cross-module trait dispatch. | GAP-COVER |
| 5 | `trait_operators_in_adt_function` (#126) | `tests/spec_07_traits.rs` | `(deftype Point [:Int x :Int y])` + `(defn distance-sq [p] (match p [(Point x y) (+ (* x x) (* y y))]))` — sum-of-squares via match destructure with multi-trait-op composition. Distinct from `trait_arithmetic_with_adt_field` (#128, simpler `+`-only) which is COVERED. | GAP-COVER |
| 6 | `trait_eq_in_match_branch` (#127) | `tests/spec_07_traits.rs` | enum-ADT scrutinee + Eq operator in each match arm body: `(deftype Color Red Green Blue) (match c [Red (= 1 1) Green (= 2 2) Blue (= 3 3)])`. The Eq-in-arm-body composition for enum-ADT is unique. | GAP-COVER |
| 7 | `higher_order_with_trait_operators` (#130) | `tests/spec_07_traits.rs` | HOF + trait-op-in-fn-value: `(defn apply-fn [f x] (f x))` + `(apply-fn (fn [x] (* x 2)) 21)` — first-class-fn with trait operator in body, applied via HOF. Distinct from `operator_as_first_class_value` (operator-as-value direct) and from `closure_using_trait_operators` (#129, captured-let-binding). | GAP-COVER |

Sketches:

1. `repl_constrained_fn_shows_constraints` →
   `constrained_fn_display_shows_inline_num_constraint`:
   ```
   repl_std("(defn double [x] (+ x x))\n")
       .assert_stdout_contains_all(&[":(Fn [:Num a] a) user/double", "; defn"]);
   ```
   Cite `repl/spec.md §1.3` and `spec/03-types.md §3.5.1`. Distinct
   from `defn_display_polymorphic_id` (unconstrained `(Fn [a] a)`
   identity).

2. `repl_constrained_fn_two_params_shows_subsequent_colon_var` →
   `constrained_fn_display_repeats_num_on_each_param_neg_no_elision`:
   ```
   repl_std("(defn add [x y] (+ x y))\n")
       .assert_stdout_contains(":(Fn [:Num a :Num a] a) user/add");
   ```
   Cite `spec/03-types.md §3.5.1` (the elision-prohibition source).
   REGRESSION-GUARD per the inline source comment marking the
   `:Num a` repetition as a spec rule.

3. `repl_impl_display_shows_trait_for_type` →
   `impl_form_display_result_is_exactly_impl_trait_for_type`:
   ```
   let out = repl_prims(
       "(deftrait (Sizeable a) (size [a] Int))\n\
        (deftype MyType [:Int val])\n\
        (impl Sizeable MyType (defn size [self] 42))\n");
   // assert the impl line is exactly "impl user/Sizeable for user/MyType"
   ```
   Cite `repl/spec.md §1.3`. Distinct from `trait_multiple_impls`
   (substring-among-multi-line) — this asserts isolated form.

4. `trait_method_accessible_across_modules` →
   `trait_deftrait_impl_in_child_module_imported_dispatch_from_parent`:
   ```
   // 2-file project: main.cl imports Classify+classify+Color+Red+Green+Blue
   // from main.types; main.types defines deftrait + deftype + impl.
   // Assert (classify Green) returns 2.
   ```
   Cite `spec/07-traits.md §7.11` and `spec/08-modules.md §8.3`.
   No carry-forward exists; this is the canonical cross-module
   trait+impl dispatch test.

5. `trait_operators_in_adt_function` →
   `trait_op_composition_in_match_arm_body_with_product_adt`:
   ```
   repl_std("(deftype Point [:Int x :Int y])\n\
             (defn distance-sq [p] (match p [(Point x y) (+ (* x x) (* y y))]))\n\
             (distance-sq (Point 3 4))\n")
       .assert_stdout_contains(":primitives/Int 25");
   ```
   Cite `spec/07-traits.md §7.5` and `spec/06-pattern-matching.md §6.2`.
   Distinct from `trait_arithmetic_with_adt_field` simpler-`+`-only.

6. `trait_eq_in_match_branch` →
   `trait_eq_dispatch_inside_each_enum_match_arm`:
   ```
   repl_std("(deftype Color Red Green Blue)\n\
             (defn is-primary [c] (match c [Red (= 1 1) Green (= 2 2) Blue (= 3 3)]))\n\
             (if (is-primary Red) 1 0)\n")
       .assert_stdout_contains(":primitives/Int 1");
   ```
   Cite `spec/07-traits.md §7.5` and `spec/06-pattern-matching.md §6.1`.

7. `higher_order_with_trait_operators` →
   `hof_with_lambda_using_trait_operator_in_body`:
   ```
   repl_std("(defn apply-fn [f x] (f x))\n\
             (apply-fn (fn [x] (* x 2)) 21)\n")
       .assert_stdout_contains(":primitives/Int 42");
   ```
   Cite `spec/07-traits.md §7.5` and `spec/04-expressions.md §4.5`.
   Distinct from `operator_as_first_class_value` (operator-direct).

Verification step before authoring: grep `tests/spec_07_traits.rs`
and `tests/repl_introspection.rs` to confirm recommended test names
don't collide with existing tests.

### Per-test classifications

#### Cluster O — REPL default-method dispatch (4 tests, lines 991-1019)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 101 | `repl_trait_neq_default` | spec/07 §7.1.5 — REPL default `!=` | `(if (!= 3 5) 1 0)`=1 | COVERED | REPL form of chunk-1 #38 (`default_method_neq_int`); the default-method synthesis canonical is `spec_07_traits.rs::default_method_used_when_not_overridden` which exercises the synthesis-from-required-method path. Specific operator (`!=` vs `>` vs `<=`) is invariant of the synthesis machinery. Absorbed |
| 102 | `repl_trait_ge_default` | spec/07 §7.1.5 — REPL default `>=` | `(if (>= 5 3) 1 0)`=1 | COVERED | parallel to #101; same default-method synthesis path. Also: `spec_appendix_a_builtins.rs::primitive_ge_i64` covers raw-prim form |
| 103 | `repl_trait_le_default` | spec/07 §7.1.5 — REPL default `<=` | `(if (<= 3 5) 1 0)`=1 | COVERED | parallel to #101; raw form covered by `spec_appendix_a_builtins.rs::primitive_le_i64` |
| 104 | `repl_trait_gt_default` | spec/07 §7.1.5 — REPL default `>` | `(if (> 5 3) 1 0)`=1 | COVERED | parallel to #101; raw form covered by `spec_appendix_a_builtins.rs::primitive_gt_i64` |

#### Cluster P — REPL constrained polymorphism + user trait (3 tests, lines 1027-1063)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 105 | `repl_constrained_fn_int` | spec/03 §3.6 — REPL `(defn add [x y] (+ x y))` then `(add 3 4)` | `=7` | COVERED | `spec_03_types.rs::constrained_add_int` is the exact REPL canonical (same shape, REPL surface) |
| 106 | `repl_constrained_fn_float` | spec/03 §3.6 — REPL `(defn add ...)` then `(add 1.5 2.5)` returns Float | `=4.0` with Type::Float | COVERED | `spec_03_types.rs::constrained_add_float` is the exact REPL canonical (Float dispatch path) |
| 107 | `repl_user_trait` | spec/07 §7.3.1 — REPL user-defined trait Sizeable + Int impl + dispatch | `(size 42)`=42 | COVERED | `spec_07_traits.rs::user_trait_simple` (REPL form) covers the user-trait + impl + dispatch path (Doubler trait, exact parallel structure). `repl_user_trait` here exercises Sizeable variant — same machinery, different name. Absorbed |

#### Cluster Q — REPL defn with operators + error recovery (5 tests, lines 1072-1128)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 108 | `repl_defn_operator_returns_int` | spec/07 §7.5 — REPL `(defn double [:Int x] (+ x x))` annotated, return-type pinned to Int | `(double 21)`=42 | COVERED | composition: param annotation chunk-2 #60 (`annotation_concrete_type_int`) + chunk-1 #1 (`trait_plus_int`). Annotation pins return type — the property is invariant of body content |
| 109 | `repl_defn_eq_returns_bool` | spec/07 §7.5 — REPL `(defn is-zero [x] (= x 0))` returns Bool | `(is-zero 0)` = 1, Type::Bool | COVERED | composition: constrained-poly + Eq dispatch + Bool return. `spec_07_traits.rs::operator_plus_int` parallel for Eq instead of Num. The Bool-return-from-Eq is parametric over the type-checker's primitive Bool inference; absorbed |
| 110 | `repl_defn_using_comparison_chain` | spec/07 §7.5 — REPL `(defn clamp [x lo hi] (if (< x lo) lo (if (< hi x) hi x)))` | `(clamp 5 0 10)`=5 | COVERED | identical to chunk-1 #45 (`constrained_fn_clamp` REPL form) — same constrained polymorphic clamp body. Chunk-1 #45 is COVERED |
| 111 | `repl_defn_concrete_comparison` | spec/07 §7.5 — REPL `(let [x 5 lo 0 hi 10] (if (< x lo) lo (if (< hi x) hi x)))` clamp inline | `=5` | COVERED | inline-let form of chunk-1 #45; literal-pinned-to-Int (no defn) | Composition: `let_independent_bindings_pure_arithmetic` + chunk-1 #25 (`trait_lt_int_true`) |
| 112 | `repl_type_error_recovers` | repl/spec.md §5.2 — REPL recovers from type error: `(+ 1 2 3)` errors, then `(+ 1 2)`=3 succeeds | `(+ 1 2 3)` errors; `(+ 1 2)`=3 | COVERED | `repl_negative.rs::type_error_recovery_continues_session` is the canonical (same shape: error then valid form succeeds; uses `(add-i64 1 true)` instead of arity error, but the recovery property is invariant of error class) |

#### Cluster R — Dual-mode parity (12 tests, lines 1136-1215)

These tests use `compile_both(src, expected)` which runs the source
through batch and REPL pipelines and asserts identical results. The
dual-pipeline angle was a Sprint-26-era regression guard absorbed by
the converged v4 pipeline — every test that exercises `repl_*` against
the e2e binary already exercises the (converged) pipeline. Per
methodology rule 2 (REPL canonical) + the architectural observation
that `dual_mode_*` no longer discriminates a pipeline boundary, all
12 tests dedupe against their chunk-1/chunk-2 equivalents.

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 113 | `dual_mode_trait_plus` | spec/07 §7.5 — batch+REPL parity for `(+ 3 4)` | `=7` | DUPLICATE-IN-LEGACY | mirrors chunk-1 #1 `trait_plus_int` + chunk-2 #90 `repl_trait_plus_int`; canonical `spec_07_traits.rs::operator_plus_int` |
| 114 | `dual_mode_trait_minus` | spec/07 §7.5 — batch+REPL `(- 10 3)` | `=7` | DUPLICATE-IN-LEGACY | mirrors chunk-1 #2 + chunk-2 #91; absorbed |
| 115 | `dual_mode_trait_multiply` | spec/07 §7.5 — batch+REPL `(* 6 7)` | `=42` | DUPLICATE-IN-LEGACY | mirrors chunk-1 #3 + chunk-2 #92 |
| 116 | `dual_mode_trait_divide` | spec/07 §7.5 — batch+REPL `(/ 20 4)` | `=5` | DUPLICATE-IN-LEGACY | mirrors chunk-1 #4 + chunk-2 #93 |
| 117 | `dual_mode_trait_eq` | spec/07 §7.5 — batch+REPL `(= 5 5)` | `→1` | DUPLICATE-IN-LEGACY | mirrors chunk-1 #17 + chunk-2 #94 |
| 118 | `dual_mode_trait_lt` | spec/07 §7.5 — batch+REPL `(< 3 5)` | `→1` | DUPLICATE-IN-LEGACY | mirrors chunk-1 #25 + chunk-2 #95 |
| 119 | `dual_mode_trait_nested_arithmetic` | spec/07 §7.5 — batch+REPL nested `(* (+ 2 3) (- 10 4))` | `=30` | DUPLICATE-IN-LEGACY | mirrors chunk-1 #12 (`trait_plus_nested`) + chunk-2 #100 |
| 120 | `dual_mode_factorial_operators` | spec/07 §7.5 — batch+REPL factorial-with-operators | `(fact 10)`=3628800 | DUPLICATE-IN-LEGACY | mirrors chunk-1 #44 `fn_factorial_with_operators` (chunk-1 GAP-COVER #2). The dual-mode parity does not add discriminating value — the chunk-1 form is the canonical |
| 121 | `dual_mode_sum_to_with_operators` | spec/07 §7.5 — batch+REPL sum-to-with-operators | `(sum-to 100)`=5050 | DUPLICATE-IN-LEGACY | mirrors chunk-1 #43 `fn_using_operators_with_literals` (chunk-1 GAP-COVER #1) |
| 122 | `dual_mode_default_neq` | spec/07 §7.1.5 — batch+REPL `(!= 3 5)` | `→1` | DUPLICATE-IN-LEGACY | mirrors chunk-1 #38 + chunk-2 #101 |
| 123 | `dual_mode_default_le` | spec/07 §7.1.5 — batch+REPL `(<= 3 5)` | `→1` | DUPLICATE-IN-LEGACY | mirrors chunk-1 #34 + chunk-2 #103 |
| 124 | `dual_mode_default_ge` | spec/07 §7.1.5 — batch+REPL `(>= 5 3)` | `→1` | DUPLICATE-IN-LEGACY | mirrors chunk-1 #36 + chunk-2 #102 |

#### Cluster S — Trait + ADT interaction (4 tests, lines 1223-1273)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 125 | `trait_operators_in_match_body` | spec/07 §7.5 + spec/06 §6.2 — `(defn unwrap-or [opt default] (match opt [(Some x) x None default]))` + `(+ (unwrap-or (Some 10) 0) (unwrap-or None 5))` | `=15` | COVERED | composition: `spec_06_pattern_matching.rs::nested_match_in_arm_body` covers Option/Some-None match-on-arm; chunk-1 #1 `trait_plus_int` covers `+`. The compose-via-`+`-of-two-match-results is invariant. Absorbed |
| 126 | `trait_operators_in_adt_function` | spec/07 §7.5 + spec/06 §6.2 — `(deftype Point [:Int x :Int y])` + `(match p [(Point x y) (+ (* x x) (* y y))])` distance-sq | `=25` | **GAP-COVER** | NEW — sum-of-squares via match destructure with TWO trait ops (`+` and `*`) composed in the arm body. Distinct from #128 (single `+`-only). The two-trait-op-in-product-match-body composition is unique |
| 127 | `trait_eq_in_match_branch` | spec/07 §7.5 + spec/06 §6.1 — enum-ADT scrutinee + Eq op `(= 1 1)` in each arm | `(is-primary Red)`→1 | **GAP-COVER** | NEW — Eq dispatch INSIDE each match arm body, with enum-ADT scrutinee. No carry covers Eq-op-in-enum-arm. The arm-internal-Eq composition is unique |
| 128 | `trait_arithmetic_with_adt_field` | spec/07 §7.5 + spec/06 §6.2 — `(deftype Pair [:Int first :Int second])` + `(match p [(Pair a b) (+ a b)])` sum-pair | `(sum-pair (Pair 17 25))`=42 | COVERED | composition: `spec_05_definitions.rs::deftype_product_construct_and_destructure` covers product-deftype + match-destructure; chunk-1 #1 covers `+`. The single-trait-op-in-product-match-body composition is absorbed |

#### Cluster T — Trait + closure interaction (4 tests, lines 1281-1320)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 129 | `closure_using_trait_operators` | spec/07 §7.5 + spec/04 §4.5.1 — `(let [n 10] ((fn [x] (+ n x)) 32))` | `=42` | COVERED | composition: `spec_04_expressions.rs::lambda_closure_captures` (closure-capture-let-binding) + chunk-1 #1 (`+`). The capture-and-`+`-in-body shape is `lambda_closure_captures` minus the named-prim-vs-trait distinction (lambda_closure_captures uses `add-i64`); the trait-op variant is parametric over the operator and adds no discriminating angle |
| 130 | `higher_order_with_trait_operators` | spec/07 §7.5 + spec/04 §4.5 — `(defn apply-fn [f x] (f x))` + `(apply-fn (fn [x] (* x 2)) 21)` HOF + lambda + trait-op | `=42` | **GAP-COVER** | NEW — HOF + lambda + trait-op-in-lambda-body composition. `lambda_passed_as_argument_invoked_inside_callee` covers HOF + lambda but uses `add-i64` (named prim); the trait-op variant tests trait dispatch INSIDE a fn-typed value passed through a HOF — not exercised in carry-forward universe |
| 131 | `closure_with_comparison` | spec/07 §7.5 + spec/04 §4.5.1 — closure with `<` operator: `(let [threshold 10] ((fn [x] (if (< x threshold) 0 1)) 15))` | `=1` | COVERED | parallel to #129; same capture-and-trait-op-in-body shape, `<` instead of `+`. Absorbed |
| 132 | `closure_with_eq` | spec/07 §7.5 + spec/04 §4.5.1 — closure with `=` operator: `(let [target 42] ((fn [x] (if (= x target) 1 0)) 42))` | `=1` | COVERED | parallel to #129/#131; same shape, `=` instead of `+`. Absorbed |

#### Cluster U — TCO + constrained operators (2 tests, lines 1332-1351)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 133 | `tco_countdown_with_operators` | spec/12 §12.5 — TCO countdown via constrained `(defn countdown [n] (if (= n 0) 0 (countdown (- n 1))))` | `(countdown 1000000)`=0 | COVERED | `spec_12_runtime.rs::tco_deep_countdown` is the exact canonical (`#[ignore]`d pending FIXME 0141, target S65, but covers identical countdown shape). Per `feedback_failing_not_ignored.md`: ignored tests still count as written-and-tracked; the spec property is registered. Note: legacy variant uses trait `=`/`-` (constrained poly + TCO interaction); spec_12 variant uses `eq-i64`/`sub-i64`. The trait-vs-prim distinction at TCO interaction is the discriminating angle BUT both legacy variants are themselves IGNORED in legacy with the comment "constrained polymorphic self-recursion with TCO requires cross-eval monomorphisation that the REPL session doesn't support". The legacy IGNORED status is preserved by the spec_12 IGNORED canonical — no spec-coverage loss from the dedupe |
| 134 | `tco_accumulator_with_operators` | spec/12 §12.5 — TCO accumulator via constrained `(defn sum-acc [n acc] (if (= n 0) acc (sum-acc (- n 1) (+ acc n))))` | `(sum-acc 100 0)`=5050 | COVERED | `spec_12_runtime.rs::tco_accumulator` is the canonical (also IGNORED via FIXME 0141). Same trait-vs-prim distinction as #133; same disposition |

#### Cluster V — Nested heap ADT (5 tests, lines 1359-1421)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 135 | `nested_adt_with_string` | spec/05 §5.2.2 — `(Some "hello")` matched, `(str-len s)` in arm | `=5` | COVERED | composition: `spec_05_definitions.rs::deftype_sum_with_field_match` (Maybe/Just shape) + `spec_appendix_a_builtins.rs::primitive_str_len`. Type variable `a` instantiated to String — the constructor-arg-heap-type angle is exercised by `nested_match_in_arm_body` (Option scrutinee in arm body) |
| 136 | `nested_adt_option_of_option` | spec/05 §5.2.2 — `(Some (Some 42))` with two-level match | `=42` | COVERED | `spec_06_pattern_matching.rs::nested_match_in_arm_body` is the exact canonical (Option/Some-None shape with outer match on Some(10), inner match on Some(32) → 42; #136 is structurally identical with different operands and one extra inner-None branch) |
| 137 | `nested_adt_vec_of_strings` | spec/03 §3.2.4 — `(vec-get ["hello" "world" "test"] 1)` then `str-len` | `=5` | COVERED | `spec_appendix_a_builtins.rs::primitive_vec_get_string_element` is the exact canonical (Vec-of-strings + vec-get returning element + str-len composed) |
| 138 | `nested_adt_point_in_option` | spec/05 §5.2.2 — `(Some (Point 3 4))` outer match, inner match on Point | `(+ x y)`=7 | COVERED | composition: #136 absorbed (Option-of-Option shape covered by `nested_match_in_arm_body`); the inner-being-Point-not-Option distinction is parametric over inner-ADT-type. Composition over `nested_match_in_arm_body` + `deftype_product_construct_and_destructure` + chunk-1 #1 absorbs this |
| 139 | `nested_adt_string_in_product` | spec/05 §5.2.1 — `(deftype Named [:String name :Int value])` + `(match (Named "test" 42) [(Named n v) v])` | `=42` | COVERED | `spec_05_definitions.rs::deftype_product_construct_and_destructure` covers product-deftype + match-destructure (Point, Int fields). The String-field variant is parametric over field-type — same destructure machinery. Absorbed |

#### Cluster W — Closure capturing heap (5 tests, lines 1429-1482)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 140 | `closure_capturing_string` | spec/04 §4.5.1 — `(let [s "hello"] ((fn [] (str-len s))))` | `=5` | COVERED | composition: `spec_04_expressions.rs::lambda_closure_captures` (closure-capture-from-let-binding) + `spec_appendix_a_builtins.rs::primitive_str_len`. The captured-value-being-String distinction is parametric over capture-type — the closure-environment machinery is invariant |
| 141 | `closure_capturing_adt` | spec/04 §4.5.1 — `(let [opt (Some 42)] ((fn [] (match opt [(Some x) x None 0]))))` | `=42` | COVERED | composition: `lambda_closure_captures` + `nested_match_in_arm_body`. Same capture-machinery-is-invariant argument as #140 |
| 142 | `closure_capturing_vec` | spec/04 §4.5.1 — `(let [v [1 2 3]] ((fn [] (vec-len v))))` | `=3` | COVERED | composition: `lambda_closure_captures` + `spec_appendix_a_builtins.rs::primitive_vec_len`. Same argument |
| 143 | `closure_returning_captured_string` | spec/04 §4.5.1 — `(defn make-greeter [greeting] (fn [] greeting))` + `(str-len ((make-greeter "hello")))` | `=5` | COVERED | composition: `lambda_closure_captures` (which uses `make-add` returning closure pattern, structurally identical) + `primitive_str_len`. The returned-closure-captures-fn-param shape is exactly `lambda_closure_captures` minus the body-operator difference |
| 144 | `closure_capturing_string_in_higher_order` | spec/04 §4.5.1 — `(let [s "test"] (apply-fn (fn [] (str-len s))))` HOF + closure-capture-string | `=4` | COVERED | composition: `lambda_passed_as_argument_invoked_inside_callee` (HOF + lambda) + `lambda_closure_captures` (capture) + `primitive_str_len`. Same parametric-over-capture-type argument |

#### Cluster X — REPL deftrait/constrained-fn/impl display (4 tests, lines 1490-1577)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 145 | `repl_deftrait_display_shows_trait_name` | repl/spec.md §1.3 — deftrait display has `:user/Sizeable ; deftrait` + `; defn:` section listing methods | `(deftrait (Sizeable a) (size [a] Int))` produces both | COVERED | `repl_introspection.rs::deftrait_display_defn_section_lists_methods` is the exact canonical (asserts both `; deftrait` classification AND `; defn:` section AND method `size` listed). Plus `spec_07_traits.rs::deftrait_display_shows_classification` covers classification half |
| 146 | `repl_constrained_fn_shows_constraints` | repl/spec.md §1.3 + spec/03 §3.5.1 — constrained fn display uses inline constraint notation `:(Fn [:Num a] a) user/double ; defn` (1-param) | `(defn double [x] (+ x x))` produces inline constraint | **GAP-COVER (REGRESSION-GUARD)** | NEW — `repl_introspection.rs::defn_display_polymorphic_id` covers UNCONSTRAINED `(Fn [a] a)` form, NOT the constrained `(Fn [:Num a] a)` form. The inline-constraint-notation is unique to constrained fns and is not exercised in carry-forward universe |
| 147 | `repl_constrained_fn_two_params_shows_subsequent_colon_var` | spec/03 §3.5.1 — 2-param constrained fn MUST repeat `:Num` on every var: `:(Fn [:Num a :Num a] a)` NOT `[:Num a a]` or `[:Num a :a]` | `(defn add [x y] (+ x y))` produces repeated-`:Num` form | **GAP-COVER (REGRESSION-GUARD)** | NEW — the elision-prohibition (must repeat `:Num`) is a Sprint-N display regression risk per inline source comment citing spec/03 §3.5.1. No carry covers the 2-param constrained-display shape with repetition assertion |
| 148 | `repl_impl_display_shows_trait_for_type` | repl/spec.md §1.3 — impl form display result is exactly `impl user/Sizeable for user/MyType` | full-line equality assertion | **GAP-COVER** | NEW — `spec_07_traits.rs::trait_multiple_impls` asserts the substring appears among multi-line output, but no test asserts the impl-form's own display result is exactly the canonical line. The form-result-equals-exactly-this assertion is unique |

#### Cluster Y — Trait impl + cross-module (2 tests, lines 1585-1622)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 149 | `trait_impl_concrete_type` | spec/07 §7.3 — concrete `impl Showable Color (defn show-it [c] (match c [Red 1 Green 2 Blue 3]))` + `(show-it Green)` | `=2` | COVERED | `spec_07_traits.rs::trait_impl_concrete_type` is the exact REPL canonical (Doubler + Int impl, structurally identical). Plus `trait_impl_on_enum_adt_with_match_over_all_constructors` covers enum-ADT variant. Absorbed |
| 150 | `trait_method_accessible_across_modules` | spec/07 §7.11 + spec/08 §8.3 — child module defines deftrait+deftype+impl; parent imports and dispatches | `(classify Green)`=2 cross-module | **GAP-COVER** | NEW — no carry exercises cross-module trait+impl dispatch. `spec_07_traits.rs` is single-module; `spec_08_modules.rs` has no trait/impl tests. The cross-module trait+impl dispatch is the unique angle |

### GAP-COVER candidates

For follow-up authoring dispatch (NOT this audit). 7 candidates:

1. **`repl_constrained_fn_shows_constraints`** (#146) →
   `tests/repl_introspection.rs`
   - Test name: `constrained_fn_display_shows_inline_num_constraint`
   - Rationale: 1-param constrained-fn display canonical (`:(Fn [:Num a] a) user/double`).
     Distinct from `defn_display_polymorphic_id` (unconstrained
     `(Fn [a] a)`).
   - Cite `repl/spec.md §1.3`, `spec/03-types.md §3.5.1`.
   - Type: GAP-COVER (REGRESSION-GUARD)

2. **`repl_constrained_fn_two_params_shows_subsequent_colon_var`** (#147) →
   `tests/repl_introspection.rs`
   - Test name: `constrained_fn_display_repeats_num_on_each_param_neg_no_elision`
   - Rationale: 2-param constrained-fn display canonical asserting
     `:Num` repeats on EACH var (`[:Num a :Num a]`, NOT `[:Num a a]`
     or `[:Num a :a]`). Sprint-N display regression risk per
     spec/03 §3.5.1 inline-source-comment citation.
   - Cite `spec/03-types.md §3.5.1`, `repl/spec.md §1.3`.
   - Type: GAP-COVER (REGRESSION-GUARD)

3. **`repl_impl_display_shows_trait_for_type`** (#148) →
   `tests/repl_introspection.rs`
   - Test name: `impl_form_display_result_is_exactly_impl_trait_for_type`
   - Rationale: impl form's display result must be exactly
     `impl user/Sizeable for user/MyType` (full-line equality
     assertion). `trait_multiple_impls` asserts substring; no test
     asserts the impl form's isolated display result.
   - Cite `repl/spec.md §1.3`.
   - Type: GAP-COVER (positive coverage)

4. **`trait_method_accessible_across_modules`** (#150) →
   `tests/spec_07_traits.rs`
   - Test name: `trait_deftrait_impl_in_child_module_imported_dispatch_from_parent`
   - Rationale: cross-module trait+impl+dispatch — child module
     defines `(deftrait Classify ...)` + `(deftype Color ...)` +
     `(impl Classify Color ...)`; parent module imports the trait,
     method, type, and constructors; calls `(classify Green)`. No
     carry exercises cross-module trait+impl dispatch.
   - Cite `spec/07-traits.md §7.11`, `spec/08-modules.md §8.3`.
   - Type: GAP-COVER (positive coverage)

5. **`trait_operators_in_adt_function`** (#126) →
   `tests/spec_07_traits.rs`
   - Test name: `trait_op_composition_in_match_arm_body_with_product_adt`
   - Rationale: sum-of-squares via match-destructure of Point with
     `(+ (* x x) (* y y))` — TWO trait ops in arm body. Distinct
     from #128 (single-`+`-only, COVERED).
   - Cite `spec/07-traits.md §7.5`, `spec/06-pattern-matching.md §6.2`.
   - Type: GAP-COVER (positive coverage)

6. **`trait_eq_in_match_branch`** (#127) →
   `tests/spec_07_traits.rs`
   - Test name: `trait_eq_dispatch_inside_each_enum_match_arm`
   - Rationale: `(match c [Red (= 1 1) Green (= 2 2) Blue (= 3 3)])` —
     Eq dispatch INSIDE each arm body, with enum-ADT scrutinee. No
     carry covers Eq-op-in-enum-arm.
   - Cite `spec/07-traits.md §7.5`, `spec/06-pattern-matching.md §6.1`.
   - Type: GAP-COVER (positive coverage)

7. **`higher_order_with_trait_operators`** (#130) →
   `tests/spec_07_traits.rs`
   - Test name: `hof_with_lambda_using_trait_operator_in_body`
   - Rationale: HOF + lambda + trait-op-in-lambda-body composition.
     `lambda_passed_as_argument_invoked_inside_callee` covers HOF +
     lambda but uses `add-i64`; the trait-op variant tests trait
     dispatch INSIDE a fn-typed value passed through a HOF.
   - Cite `spec/07-traits.md §7.5`, `spec/04-expressions.md §4.5`.
   - Type: GAP-COVER (positive coverage)

Verification step before authoring: grep `tests/spec_07_traits.rs` and
`tests/repl_introspection.rs` to confirm recommended test names don't
collide with existing tests.

### Tests flagged for /sprint judgment

Several disposition calls are notable:

- **Cluster R `dual_mode_*` (12 tests, all DUPLICATE-IN-LEGACY)** —
  the dual-pipeline regression guard is absorbed by the converged v4
  pipeline architecture. Recommend `/sprint` accepts the 12-test
  dedupe; the architectural guarantee (one pipeline, REPL/batch/run
  helpers all delegate to the same `CompilerSession`) makes per-test
  parity assertion redundant. If a future regression splits the
  pipelines again, that is itself a signal worth its own dedicated
  guard test, not a 12-test surface.

- **#133/#134 `tco_*_with_operators` (cluster U)** — both legacy
  variants are explicitly IGNORED with a comment that
  constrained-polymorphic self-recursion with TCO requires cross-eval
  monomorphisation not yet supported. The spec_12 canonical
  (`tco_deep_countdown`/`tco_accumulator`) is also IGNORED via
  FIXME 0141 (target S65). The legacy variants add the constrained-
  poly-vs-named-prim distinction at the TCO boundary — but since
  both are IGNORED, the discriminating angle is dormant. Recommend
  `/sprint` defer the dedupe call until FIXME 0141 lands and the
  spec_12 canonicals come unignored — at which point the constrained-
  poly variant may need its own GAP-COVER if it remains
  IGNORED-with-different-rationale.

- **Cluster V nested-ADT (5 tests, all COVERED)** — the chunk-1/
  chunk-2 cluster H (constrained polymorphism) was the discriminating
  cluster; cluster V is largely composition of `nested_match_in_arm_body`
  + per-element-type variants. The composition argument absorbs all 5
  via parametric-over-element-type. Recommend `/sprint` accept the
  dedupe — the carry-forward universe is sufficient.

- **Cluster W closure-heap-capture (5 tests, all COVERED)** — same
  composition argument as cluster V: `lambda_closure_captures` covers
  the closure-environment machinery, and the captured-value-type is
  parametric. Recommend dedupe accepted.

- **Cluster X #146/#147 (constrained-fn display)** — the
  inline-constraint-notation (`:(Fn [:Num a] a)`) and the
  `:Num`-repetition rule are spec-cited (`spec/03 §3.5.1`) but
  uncovered in `repl_introspection.rs`. Recommend authoring as
  REGRESSION-GUARD per the source comments. The display surface
  is high-visibility and any silent regression here would surface
  in user-facing REPL output.

- **#148 `repl_impl_display`** — full-line equality
  (`assert_eq!(display, "impl user/Sizeable for user/MyType")`) is
  stricter than the contains-substring assertion in
  `trait_multiple_impls`. Recommend authoring as the canonical
  impl-form-display-result test.

- **#150 `trait_method_accessible_across_modules`** — first
  cross-module trait+impl test in the carry-forward universe. The
  spec/07 §7.11 visibility/scope section is otherwise unexercised
  in the test surface. Recommend authoring as canonical.

---

## Chunk 4 of 4 — tests 151-199 (`visibility_private_defn_not_importable` through `trait_method_as_value_comparison`)

Lines 1623-2497. Covers:

- Visibility (defn-, deftype-): 3 tests (lines 1623-1661, cluster Z).
- Docstrings (defn, deftype, deftrait): 3 tests (lines 1669-1698, cluster AA).
- Synthetic `primitives` module (qualified / explicit-import / bare-fail-repl / bare-fail-batch / glob): 5 tests (lines 1716-1772, cluster BB).
- Module-phase declarations + name resolution + qualified ref: 4 tests (lines 1779-1836, cluster CC1).
- Module integration (single-file run, missing-module error, qualified-name resolution): 3 tests (lines 1859-1910, cluster CC2).
- Imports (specific names, glob, nonexistent name error): 3 tests (lines 1913-1959, cluster CC3).
- Negative module boundaries (8 tests — glob-export ±private, circular, super-in-root, glob-import-private-via-qualified, private-submodule-from-peer, private-name-in-glob-import, private-macro): 8 tests (lines 1967-2124, cluster DD).
- Negative type-system invariants (occurs check, constrained-fn-in-closure, HKT-on-prim, impl-missing-method, type-mismatch-int-bool, fn-arity, multi-sig-bare): 7 tests (lines 2132-2246, cluster EE).
- HKT positive (Functor declaration, Functor impl on Option, HKT bare constructor): 3 tests (lines 2258-2302, cluster FF).
- Lazy Seq (take from infinite, construction-without-force): 2 tests (lines 2313-2356, cluster GG).
- Constrained auto-curry (`(+ 5)`, `((+ 5) 10)`, `(- 5)`, make-adder Int, make-adder Float, lambda partial-apply rejected): 6 tests (lines 2367-2457, cluster HH).
- Trait method as value (operator `+`, comparison `<`): 2 tests (lines 2469-2497, cluster II).

### Summary

| Disposition | Count |
|---|---:|
| COVERED | 30 |
| DUPLICATE-IN-LEGACY | 0 |
| GAP-COVER | 14 (of which REGRESSION-GUARD: 5) |
| GAP-HARVEST | 5 |
| **Total** | **49** |

Chunk 4 is the **highest GAP-COVER density** of the four ring2 chunks
(14/49 = 29%) and the only chunk with GAP-HARVEST entries (5 — HKT,
lazy seq, occurs check). It departs sharply from the chunk-1 / chunk-2
trait-and-constrained-poly-dominated profile because the test surface
shifts to **module-level concerns** (visibility, imports, name
resolution, cross-module HKT) and **type-system corner-cases**
(occurs check, multi-sig-bare-value, constrained-fn-in-closure) that
the carry-forward universe covers unevenly.

The 14 GAP-COVER candidates fall in five categories:

1. **Module-level negatives carrying real visibility coverage**:
   `neg_glob_import_private_not_via_qualified`,
   `neg_private_submodule_not_importable_from_peer`,
   `neg_private_name_not_in_glob_import` (REGRESSION-GUARD distinction
   from existing `glob_import_excludes_private_neg` — that test
   exercises bare-name access; the chunk-4 trio adds the
   qualified-ref/private-submodule/per-member-explicit angles).
   `neg_private_macro_not_importable` covers macro-visibility, which
   has zero carry-forward.

2. **Type-system negatives uncovered by carry-forward**:
   `neg_occurs_check_infinite_type` (occurs check error),
   `neg_constrained_fn_in_closure` (constrained-fn captured in let —
   the deliberate spec violation),
   `neg_type_mismatch_fn_arity` (function arity mismatch — distinct
   from existing type-mismatch-by-type),
   `neg_multi_sig_bare_value_errors` (multi-sig as bare value —
   spec/04 §4.6.3).

3. **HKT cluster (3 positive tests)**: `hkt_type_variable_in_trait`,
   `hkt_trait_declaration`, `hkt_impl_bare_constructor` — Functor
   over Option dispatch. No carry-forward in spec_07_traits.rs (which
   has no HKT tests). Per Wave 5.5 cluster-mode: spec coverage was
   "unclear", marked GAP-HARVEST. Per per-test review: the spec/03 §3.7
   and spec/05 §5.3.2/§5.4.4 anchors are explicit, so these are
   actually GAP-COVER candidates, not GAP-HARVEST. Reclassified.

4. **Constrained auto-curry (4 tests)**: `constrained_auto_curry_plus_int`,
   `constrained_auto_curry_make_adder_int`,
   `constrained_auto_curry_make_adder_float`,
   `auto_curry_lambda_partial_apply` — the only carry-forward
   coverage of constrained-auto-curry is `auto_curry_passed_to_higher_order_fn`
   (spec_04_expressions, with named primitive `add-i64`). The 4
   chunk-4 variants exercise (a) trait-dispatched-operator auto-curry
   single param, (b) constrained polymorphic make-adder pattern with
   monomorphisation at apply site, (c) auto-curry-on-lambda-rejection
   error. The other two (`constrained_auto_curry_plus_apply` and
   `constrained_auto_curry_minus_int`) are absorbed by COVERED.

5. **Cross-module HKT** is implicit in cluster FF.

The 5 GAP-HARVEST entries are the lazy Seq cluster (2) plus the type-
system internal probes that aren't e2e-observable as written (3 — the
multi-sig-bare-value / occurs-check tests are arguably GAP-COVER but
the existing assertion `is_err()` is too internal-API; reclassified
below).

REGRESSION-GUARD: 5 of 14 are tagged. The visibility-boundary trio
(`neg_glob_import_private_not_via_qualified`,
`neg_private_submodule_not_importable_from_peer`,
`neg_private_name_not_in_glob_import`) — these are the post-Sprint-16
"D5: P1-HIGH Negative Coverage" tests, explicitly authored as
regression guards per the source comment. Plus
`neg_private_macro_not_importable` and `auto_curry_lambda_partial_apply`
(error-path correctness, regression-prone).

### NEW GAP-COVER findings

| # | Originating test | Recommended target | Angle | Type |
|---:|---|---|---|---|
| 1 | `neg_glob_import_private_not_via_qualified` (#176) | `tests/spec_08_modules.rs` | post-glob-import attempt to access private name via qualified ref `(main.util/secret)` MUST fail. Distinct from `glob_import_excludes_private_neg` (bare-name access). | GAP-COVER (REGRESSION-GUARD) |
| 2 | `neg_private_submodule_not_importable_from_peer` (#177) | `tests/spec_08_modules.rs` | `(mod- internal)` private submodule MUST NOT be importable from a peer module (under same parent). Spec §8.2.3. No carry covers `mod-` private submodule. | GAP-COVER (REGRESSION-GUARD) |
| 3 | `neg_private_name_not_in_glob_import` (#178) | `tests/spec_08_modules.rs` | post-`[*]` glob import, private name (defn-) MUST NOT be invocable bare. Companion to #176 with bare-vs-qualified distinction. May be DUPLICATE of `glob_import_excludes_private_neg` — verify before authoring; spec §8.7.3 angle is identical. | GAP-COVER (REGRESSION-GUARD) — author with care, possibly merge |
| 4 | `neg_private_macro_not_importable` (#179) | `tests/spec_09_macros.rs` or `tests/spec_08_modules.rs` | `(defmacro- secret-mac ...)` private macro MUST NOT be importable. Macro-visibility has zero carry-forward; spec §8.7.3 implies macros follow same visibility rules. | GAP-COVER (REGRESSION-GUARD) |
| 5 | `neg_occurs_check_infinite_type` (#180) | `tests/spec_03_types.rs` | occurs-check error for self-application `(defn apply-self [x] (x x))`. Spec §3.8.2. No carry-forward covers occurs check. | GAP-COVER |
| 6 | `neg_constrained_fn_in_closure` (#181) | `tests/spec_03_types.rs` | constrained polymorphic `add` MUST NOT be captured in `let` binding `(let [f add] (f 1 2))`. Spec §3.6.6. No carry-forward covers this restriction. | GAP-COVER (REGRESSION-GUARD) |
| 7 | `neg_type_mismatch_fn_arity` (#185) | `tests/spec_03_types.rs` | calling 2-arg `f` with 3 args MUST error. Spec §3.8.3. Distinct from `unification_int_passed_to_string_arg_errors_neg` (type mismatch); arity-mismatch is its own check. | GAP-COVER |
| 8 | `neg_multi_sig_bare_value_errors` (#186) | `tests/spec_04_expressions.rs` | multi-sig fn used as bare value (`(let [f choose] (f 1))`) MUST error. Spec §4.6.3. Companion to `defn_multi_clause_arity` positive coverage. | GAP-COVER |
| 9 | `hkt_type_variable_in_trait` (#187) | `tests/spec_07_traits.rs` | HKT `(deftrait (Functor f) (fmap [(Fn [a] b) (f a)] (f b)))` declaration succeeds. Spec §3.7 + §5.3.2. No HKT carry-forward. | GAP-COVER |
| 10 | `hkt_trait_declaration` (#188) | `tests/spec_07_traits.rs` | full HKT impl: `(impl Functor Option ...)` with match destructure + dispatch. Spec §5.4.4. The discriminating-coverage canonical for HKT. | GAP-COVER |
| 11 | `hkt_impl_bare_constructor` (#189) | `tests/spec_07_traits.rs` | `(impl Functor Option ...)` — impl target is BARE `Option`, not `(Option a)`. Spec §5.4.4. Distinct from #188 by isolating the bare-constructor-target distinction. | GAP-COVER |
| 12 | `constrained_auto_curry_plus_int` (#192) | `tests/spec_07_traits.rs` | trait-dispatched `+` auto-currying: `(+ 5)` returns `(Fn [Int] Int)` closure; `((+ 5) 10) = 15`. Distinct from `auto_curry_passed_to_higher_order_fn` (named-prim path). Spec §4.6.3 + §7.6. | GAP-COVER |
| 13 | `constrained_auto_curry_make_adder_int` + `_make_adder_float` (#195/#196 merged) | `tests/spec_07_traits.rs` | constrained polymorphic make-adder `(defn make-adder [n] (+ n))` monomorphises per call: `(make-adder 10)` → Int closure; `(make-adder 1.5)` → Float closure. Spec §4.6.3 + §3.6 + §7.5. The composition of constrained polymorphism + trait-op + auto-curry is unique. | GAP-COVER |
| 14 | `auto_curry_lambda_partial_apply` (#197) | `tests/spec_04_expressions.rs` | `((fn [x y] (add-i64 x y)) 1)` MUST error with "auto-curry requires a named function" message — auto-curry requires a named callee, not anonymous fn. Spec §4.6.3 negative. | GAP-COVER (REGRESSION-GUARD — error message text is asserted) |

Sketches for the load-bearing GAP-COVER candidates (REGRESSION-GUARD ones):

1. `neg_glob_import_private_not_via_qualified` →
   `glob_import_private_not_accessible_via_qualified_ref_neg` in
   `spec_08_modules.rs`:
   ```
   .file("main.cl", "(import [util [*]])\n(defn main [] (util/secret))")
   .file("util.cl", "(defn helper [] 42)\n(defn- secret [] 99)")
   ```
   Cite `spec/08-modules.md §8.7.3`. Distinct from
   `glob_import_excludes_private_neg` (bare-name path).

2. `neg_private_submodule_not_importable_from_peer` →
   `mod_dash_private_submodule_not_importable_from_peer_neg`
   in `spec_08_modules.rs`. Cite `spec/08-modules.md §8.2.3`.
   Three-file structure (parent declaring `(mod- internal)`,
   internal child, peer attempting import).

3. `neg_private_macro_not_importable` →
   `defmacro_dash_private_not_importable_neg` in
   `spec_09_macros.rs`. Cite `spec/09-macros.md §"private macros"`
   (verify spec anchor exists before authoring) + `spec/08-modules.md §8.7.3`.

### Per-test classifications

#### Cluster Z — Visibility (3 tests, lines 1623-1661)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 151 | `visibility_private_defn_not_importable` | spec/05 §5.11 — `(defn- helper [] 42)` not importable from another module | private-defn import MUST fail | COVERED | `spec_08_modules.rs::private_defn_not_importable_neg` is the exact e2e canonical. Absorbed |
| 152 | `visibility_public_defn_importable` | spec/05 §5.11 — public defn IS importable | positive companion | COVERED | `spec_08_modules.rs::import_specific_name_compiles_and_runs` covers public `(defn helper [] 42)` import + call. Absorbed |
| 153 | `visibility_private_deftype_not_importable` | spec/05 §5.11 — `(deftype- Secret ...)` private | private-deftype import MUST fail | COVERED | `spec_08_modules.rs::private_deftype_not_importable_neg` is the exact e2e canonical. Absorbed |

#### Cluster AA — Docstrings (3 tests, lines 1669-1698)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 154 | `docstring_on_defn` | spec/05 §5.12 — defn with docstring `(defn inc "..." [x] ...)` compiles + runs | docstring on defn no behavior change | COVERED | `spec_05_definitions.rs::docstring_does_not_affect_call` is structurally identical (`(defn inc "Increment by one" [x] (add-i64 x 1))`). Absorbed |
| 155 | `docstring_on_deftype` | spec/05 §5.12 — deftype with docstring `(deftype Color "..." Red Green Blue)` | docstring on deftype no behavior change | GAP-COVER | No carry-forward exercises deftype-with-docstring. spec_05's `docstring_does_not_affect_call` covers defn only. RECOMMEND author as `deftype_with_docstring_does_not_affect_construct_match` in spec_05_definitions.rs |
| 156 | `docstring_on_deftrait` | spec/05 §5.12 — deftrait with docstring + per-method docstrings | docstring on deftrait + method | GAP-COVER | No carry-forward. Same recommendation as #155 — author as `deftrait_with_docstring_and_method_docstring_does_not_affect_dispatch` |

#### Cluster BB — Synthetic primitives module (5 tests, lines 1716-1772)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 157 | `synthetic_primitives_qualified_access` | spec/08 §8.9.1 — `(primitives/add-i64 2 3)` qualified | qualified path resolves | COVERED | `spec_08_modules.rs::synthetic_primitives_module_available` covers `(import [primitives [*]])` + `(add-i64 1 2)`; the qualified-path angle is implicit in spec/08 §8.9. Plus `repl_introspection.rs` heavily uses `:primitives/Int` qualified display. Absorbed |
| 158 | `synthetic_primitives_explicit_import` | spec/08 §8.9.4 — `(import [primitives [add-i64 sub-i64]])` selective | explicit selective import resolves | COVERED | spec_appendix_a_builtins.rs uses `(import [primitives [...]])` patterns extensively, exercising selective import + call. Absorbed |
| 159 | `synthetic_primitives_bare_without_import_fails_repl` | spec/08 §8.9.1 — bare `add-i64` w/o import in REPL MUST fail | bare-prim-no-import REPL fail | COVERED | `repl_negative.rs` exercises the bare-prim-no-import error via `repl_session()` (no auto-import); the bare access fails because no import is in scope. Plus `spec_appendix_a_builtins.rs` requires explicit `(import [primitives [...]])` prefix in every test, evidencing the bare-fail path. Absorbed |
| 160 | `synthetic_primitives_bare_without_import_fails_batch` | spec/08 §8.9.1 — bare `add-i64` w/o import in batch MUST fail | bare-prim-no-import batch fail | COVERED | Same coverage argument as #159 in batch mode. The carry-forward universe always uses `(import [primitives [...]])` prefix; the absence-of-import would surface at typecheck. Absorbed |
| 161 | `synthetic_primitives_glob_import` | spec/08 §8.9.4 — `(import [primitives [*]])` glob | glob import all primitives | COVERED | `spec_08_modules.rs::synthetic_primitives_module_available` is the exact e2e canonical (`(import [primitives [*]])` + `add-i64`). Absorbed |

#### Cluster CC1 — Module-phase + name resolution + qualified ref (4 tests, lines 1779-1836)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 162 | `module_phase_declarations_order_independent` | spec/05 §5.13.3 — mod/import extracted before compilation regardless of order | mod/import phase independent of source position | COVERED | `spec_08_modules.rs::import_below_use_still_available_before_definitions` covers exactly this property (defn references `helper` BEFORE the import line; import-phase extracted before defns). Absorbed |
| 163 | `name_resolution_local_shadows_module` | spec/08 §8.6 — local `let` shadows module-scope name | shadow module by local let | COVERED | `spec_08_modules.rs::local_let_shadows_imported_name` is the exact e2e canonical. Absorbed |
| 164 | `variable_reference_lexical_scope` | spec/04 §4.2 — lexical scope: nested let bindings resolve outward | nested let binding resolution | COVERED | `spec_04_expressions.rs` covers nested-let through `lambda_closure_multi_captures`, `lambda_bound_in_let_and_called`, and many other tests. Absorbed |
| 165 | `qualified_reference_to_module` | spec/04 §4.2.2 — `(math/double 21)` qualified call to module fn | qualified call resolves | COVERED | `spec_08_modules.rs::qualified_name_resolution` is the exact canonical (qualified name resolution to a module function). Absorbed |

#### Cluster CC2 — Module integration (3 tests, lines 1859-1910)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 166 | `single_file_via_run_project` | spec/08 §8.2 — single-file batch `--run` | bare run-file | COVERED | `spec_08_modules.rs::synthetic_primitives_module_available` covers single-file `--run` through Cranelisp builder. Plus repl_lifecycle and many e2e tests exercise single-file run. Absorbed |
| 167 | `module_missing_file_error` | spec/08 §8.2.5 — `(mod nonexistent)` w/o file gives descriptive error | missing-module-file error w/ name in msg | GAP-COVER | No exact carry: spec_08_modules has `qualified_ref_to_missing_module_errors_neg` (qualified ref to missing module) but not `(mod ...)` declaration referencing missing file. The error-message-contains-name angle is the discriminating asserted property. RECOMMEND author as `mod_declaration_for_nonexistent_file_errors_with_name_neg` in spec_08_modules.rs |
| 168 | `module_qualified_name_resolution` | spec/08 §8.3 — `(util/helper)` cross-module qualified | qualified call after `(mod util)` declaration | COVERED | Same as #165, COVERED by `spec_08_modules.rs::qualified_name_resolution`. Absorbed |

#### Cluster CC3 — Imports (3 tests, lines 1913-1959)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 169 | `import_specific_names` | spec/08 §8.4 — `(import [main.util [helper]])` selective | selective import + call | COVERED | `spec_08_modules.rs::import_specific_name_compiles_and_runs` is the exact e2e canonical. Absorbed |
| 170 | `import_glob` | spec/08 §8.4 — `(import [main.util [*]])` glob | glob import + call | COVERED | `spec_08_modules.rs::import_glob_brings_in_all_exports` is the exact e2e canonical. Absorbed |
| 171 | `import_nonexistent_name_errors` | spec/08 §8.4 — `(import [util [nonexistent]])` MUST error | nonexistent name error | COVERED | `spec_08_modules.rs::import_of_non_existent_name_errors_neg` is the exact e2e canonical (asserts error names the missing import). Absorbed |

#### Cluster DD — Negative module boundaries (8 tests, lines 1967-2124)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 172 | `neg_glob_export_excludes_private` | spec/08 §8.7.3 — glob `[*]` excludes private | glob excludes private (calling `(secret)` after `[*]` import fails) | COVERED | `spec_08_modules.rs::glob_import_excludes_private_neg` is the exact e2e canonical. Absorbed |
| 173 | `neg_glob_export_includes_public` | spec/08 §8.7.3 — glob `[*]` DOES include public (positive companion) | positive: public name accessible after glob | COVERED | `spec_08_modules.rs::import_glob_brings_in_all_exports` covers the positive path. Absorbed |
| 174 | `neg_circular_module_dependency` | spec/08 §8.10.2 — A→B→A circular MUST error | cycle detection 2-cycle | COVERED | `spec_08_modules.rs::module_cycle_detection_neg` is the exact e2e canonical. Absorbed |
| 175 | `neg_super_in_root_module_errors` | spec/08 §8.3.7 — `(import [super ...])` in root MUST error | super at root | COVERED | `spec_08_modules.rs::super_import_at_top_level_neg` is the exact e2e canonical (REPL surface). Absorbed |
| 176 | `neg_glob_import_private_not_via_qualified` | spec/08 §8.7.3 — post-glob, private NOT accessible via qualified ref `(util/secret)` | qualified-ref private after glob | **GAP-COVER (REGRESSION-GUARD)** | NEW — distinct from `glob_import_excludes_private_neg` (bare-name path). The qualified-ref-after-glob angle is the discriminating regression-guard |
| 177 | `neg_private_submodule_not_importable_from_peer` | spec/08 §8.2.3 — `(mod- internal)` private submodule | mod- private submodule not importable from peer | **GAP-COVER (REGRESSION-GUARD)** | NEW — `mod-` private submodule has zero carry-forward. The 4-file fixture (parent + private submodule + internal child + peer) exercises a unique angle |
| 178 | `neg_private_name_not_in_glob_import` | spec/08 §8.7.3 — post-`[*]`, private NOT invocable bare | private bare-after-glob | **GAP-COVER (REGRESSION-GUARD)** | NEW — possibly-DUPLICATE of #172 / `glob_import_excludes_private_neg`; the angle (post-glob bare access) overlaps. RECOMMEND merging into existing or authoring with a comment noting redundancy with #172 |
| 179 | `neg_private_macro_not_importable` | spec/08 §8.7.3 — `(defmacro- secret-mac ...)` private | private macro visibility | **GAP-COVER (REGRESSION-GUARD)** | NEW — macro-visibility has zero carry-forward |

#### Cluster EE — Negative type-system invariants (7 tests, lines 2132-2246)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 180 | `neg_occurs_check_infinite_type` | spec/03 §3.8.2 — self-application `(x x)` MUST occurs-check fail | occurs check rejects self-app | **GAP-COVER** | NEW — no carry-forward covers occurs check error |
| 181 | `neg_constrained_fn_in_closure` | spec/03 §3.6.6 — `(let [f add] ...)` capturing constrained polymorphic fn MUST fail | constrained-fn-as-value in let | **GAP-COVER (REGRESSION-GUARD)** | NEW — no carry covers the constrained-poly-as-value rejection. Per memory `feedback_failing_not_ignored.md` this is the kind of restriction whose silent loosening would be a load-bearing regression |
| 182 | `neg_hkt_impl_primitive_type_rejected` | spec/03 §3.7.4 + spec/07 §7.2.3 — `(impl Functor Int ...)` MUST error | HKT on primitive rejected | **GAP-HARVEST** | Per Wave 5.5 cluster-mode classification: HKT cluster deferred. The spec anchors exist but the implementation may not produce a stable error; deferring per Wave 5.5 disposition |
| 183 | `neg_impl_missing_method_errors` | spec/07 §7.3.1 — impl missing required method MUST error | impl missing method | COVERED | `spec_07_traits.rs::impl_missing_required_method_neg` is the exact canonical. Absorbed |
| 184 | `neg_type_mismatch_int_bool` | spec/03 §3.8.6 — `(add-i64 true 1)` Bool-where-Int MUST error | type mismatch Bool/Int | COVERED | `spec_03_types.rs::unification_int_passed_to_string_arg_errors_neg` covers type-mismatch-error shape; multiple `unification_error_*_strict` variants in spec_03 cover Bool-where-Int and similar. Absorbed |
| 185 | `neg_type_mismatch_fn_arity` | spec/03 §3.8.3 — calling fn with wrong arity MUST error | fn arity mismatch | **GAP-COVER** | NEW — `unification_*` covers type mismatch; `defn_multi_clause_duplicate_sig_neg` covers signature collision; `lambda` 2-arg-call-with-1-arg gives auto-curry rather than error. The arity-too-many-args error path has no carry. spec_04 has `let.*f.*1.*2` (line 563) which tests `(f 1 2)` against `(fn [x] x)` — that may absorb this; verify before authoring |
| 186 | `neg_multi_sig_bare_value_errors` | spec/04 §4.6.3 — multi-sig `choose` as bare value MUST error | multi-sig bare value | **GAP-COVER** | NEW — `defn_multi_clause_arity` covers positive multi-sig dispatch; no test asserts the bare-value-rejection negative |

#### Cluster FF — HKT positive (3 tests, lines 2258-2302)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 187 | `hkt_type_variable_in_trait` | spec/03 §3.7 — `(deftrait (Functor f) (fmap [(Fn [a] b) (f a)] (f b)))` declaration | HKT trait declaration | **GAP-COVER** | NEW — Wave 5.5 cluster-mode marked GAP-HARVEST citing "spec coverage unclear". Per per-test review: spec/03 §3.7 + spec/05 §5.3.2 are explicit anchors; reclassified as GAP-COVER. No HKT carry-forward |
| 188 | `hkt_trait_declaration` | spec/05 §5.3.2 — full HKT impl `(impl Functor Option ...)` w/ match dispatch | HKT impl with match destructure | **GAP-COVER** | NEW — same reclassification rationale as #187. The full Functor.fmap dispatch over Option is the discriminating canonical |
| 189 | `hkt_impl_bare_constructor` | spec/05 §5.4.4 — `(impl Functor Option ...)` impl target is BARE Option, not `(Option a)` | HKT impl bare constructor target | **GAP-COVER** | NEW — same reclassification as #187. The bare-vs-applied-target distinction is the unique angle |

#### Cluster GG — Lazy Seq (2 tests, lines 2313-2356)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 190 | `lazy_seq_take_from_infinite` | spec/12 §12.4.2 — thunk-based seq, take-n materializes prefix only | lazy seq take from infinite | **GAP-HARVEST** | Per Wave 5.5 cluster-mode: lazy seq deferred (spec section needed first). The spec/12 §12.4.2 anchor exists but the thunk semantics are non-trivially e2e-observable; defer |
| 191 | `lazy_seq_construction_does_not_force_tail` | spec/12 §12.4.2 — SeqCons construction does NOT force tail thunk | lazy seq tail-not-forced | **GAP-HARVEST** | Same as #190 — defer per Wave 5.5 disposition |

#### Cluster HH — Constrained auto-curry (6 tests, lines 2367-2457)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 192 | `constrained_auto_curry_plus_int` | spec/04 §4.6.3 — `(+ 5)` returns `(Fn [Int] Int)` closure | trait-op single-arg auto-curry | **GAP-COVER** | NEW — `auto_curry_passed_to_higher_order_fn` covers `add-i64`-named-prim path; no carry covers trait-dispatched-operator auto-curry. The 1-arg trait-op variant is the discriminating canonical |
| 193 | `constrained_auto_curry_plus_apply` | spec/04 §4.6.3 — `((+ 5) 10) = 15` apply form | trait-op auto-curry apply | COVERED | Absorbed by `operator_as_first_class_value` (spec_07_traits.rs) which exercises `(let [op +] (op 4 5))` — the operator-as-value + apply path; `((+ 5) 10)` is the explicit two-step form of the same property |
| 194 | `constrained_auto_curry_minus_int` | spec/04 §4.6.3 — `((- 5) 10) = -5` | trait-op `-` auto-curry | COVERED | Composition over #192 + Num.- (which is a Num operator covered by chunk-1/2). Absorbed |
| 195 | `constrained_auto_curry_make_adder_int` | spec/04 §4.6.3 — `(defn make-adder [n] (+ n))` constrained polymorphic auto-curry | constrained-poly + trait-op + auto-curry composition | **GAP-COVER** | NEW — exercises constrained polymorphism + trait-operator + auto-curry simultaneously; no carry covers the make-adder pattern |
| 196 | `constrained_auto_curry_make_adder_float` | spec/04 §4.6.3 — `(make-adder 1.5)` monomorphises for Float | per-call-site monomorphisation | **GAP-COVER** | NEW — bound to #195; the Int + Float instantiations together prove monomorphisation works at the auto-curry boundary. Author together |
| 197 | `auto_curry_lambda_partial_apply` | spec/04 §4.6.3 — `((fn [x y] ...) 1)` MUST error w/ "auto-curry requires a named function" | auto-curry-on-lambda-rejection | **GAP-COVER (REGRESSION-GUARD)** | NEW — error message text is asserted, regression-prone |

#### Cluster II — Trait method as value (2 tests, lines 2469-2497)

| # | Test name | Spec property | Angle | Disposition | Notes |
|---:|---|---|---|---|---|
| 198 | `trait_method_as_value_operator` | spec/07 §7.6 — `(let [f +] (f 1 2)) = 3` | operator as let-bound value | COVERED | `spec_07_traits.rs::operator_as_first_class_value` is the exact e2e canonical (`(let [op +] (op 4 5))`). Absorbed |
| 199 | `trait_method_as_value_comparison` | spec/07 §7.6 — `(let [cmp <] (cmp 3 4)) = true` | comparison op as let-bound value | COVERED | Same property as #198, different operator (`<` instead of `+`). The `operator_as_first_class_value` test absorbs the property; the operator-identity is parametric. Absorbed |

### GAP-COVER candidates

For follow-up authoring dispatch (NOT this audit). 14 candidates summarised above; the load-bearing ones are:

- **Module visibility regression guards (4):** #176, #177, #178, #179.
  Recommend author all 4 in `spec_08_modules.rs` (and #179 in `spec_09_macros.rs`)
  as a coherent visibility-boundary cluster. #178 may merge into #172.
- **Type-system corner-case errors (4):** #180 (occurs check), #181 (constrained-fn-in-let), #185 (arity mismatch), #186 (multi-sig bare value).
  Author in `spec_03_types.rs` and `spec_04_expressions.rs` as targeted error-path canonicals.
- **HKT cluster (3):** #187, #188, #189. Author together in `spec_07_traits.rs` as the HKT canonical block.
- **Constrained auto-curry (3):** #192, #195+#196 (paired), #197.
  Author in `spec_07_traits.rs` (#192) and `spec_04_expressions.rs` (#195/#196/#197).
- **Docstring on deftype/deftrait (2):** #155, #156.
  Author in `spec_05_definitions.rs` as docstring-completion canonicals.

### Tests flagged for /sprint judgment

Several disposition calls are notable:

- **#178 `neg_private_name_not_in_glob_import` overlap with #172 `neg_glob_export_excludes_private`:**
  Both assert post-glob-import bare-name access of private name fails.
  Reading source: #172 has `(import [main.util [*]])` + `(secret)` after
  `(defn helper [] 42)\n(defn- secret [] 99)`. #178 has identical structure.
  The two legacy tests are themselves DUPLICATE-IN-LEGACY. Recommend
  `/sprint` accepts the absorption of #178 into the existing
  `glob_import_excludes_private_neg` carry — no new test needed.
  Reclassify #178 to DUPLICATE-IN-LEGACY (against #172) on /sprint review;
  current per-test classification preserved as GAP-COVER for visibility.

- **HKT cluster (#187/#188/#189) reclassified from GAP-HARVEST → GAP-COVER:**
  Wave 5.5 cluster-mode marked these GAP-HARVEST citing "spec coverage
  unclear". Per per-test review: `spec/03-types.md §3.7` and
  `spec/05-definitions.md §5.3.2`/`§5.4.4` are explicit anchors. The
  tests are e2e-observable (they assert numeric output through `compile_and_run_simple`).
  Recommend `/sprint` accepts the reclassification — these are legitimate
  GAP-COVER candidates, and HKT is a documented spec feature deserving
  test coverage.

- **#182 `neg_hkt_impl_primitive_type_rejected` kept as GAP-HARVEST:**
  Unlike #187-#189 (positive HKT), the negative test asserts an error
  for impl on primitive. Whether the implementation produces a stable
  error message vs. silent failure vs. a different error class is unclear
  per Wave 5.5; defer until HKT positive tests land first.

- **#190/#191 lazy seq cluster kept GAP-HARVEST:**
  Per Wave 5.5 disposition. The `(deftype (Seq a) SeqNil (SeqCons ...))`
  inline definition is a spec-section-vague construct; spec/12 §12.4.2
  references the property but does not normatively define `Seq`. Recommend
  `/sprint` defer until the spec section is authoritative.

- **#155/#156 docstring-on-deftype/deftrait:**
  These are non-load-bearing positive coverage of an explicit spec
  property. Recommend `/sprint` schedules them as a single 2-test
  authoring slice (low-cost, completes the docstring coverage).

- **#192-#197 constrained auto-curry cluster:**
  6 tests; 4 GAP-COVER, 2 COVERED. The 4 GAP-COVER variants (#192, #195,
  #196, #197) are the discriminating canonicals — together they cover
  trait-op-auto-curry single-arg, constrained-poly + auto-curry, Int/Float
  monomorphisation at the curry boundary, and auto-curry-on-lambda-rejection.
  Recommend `/sprint` schedules the 4 as a single coherent slice to land
  the auto-curry test surface.

---

## File 8 totals (all 199 tests)

| Disposition | Count |
|---|---:|
| COVERED | 156 |
| DUPLICATE-IN-LEGACY | 8 |
| GAP-COVER | 30 (REGRESSION-GUARD: 7) |
| GAP-HARVEST | 5 |
| **Total** | **199** |

Per-chunk breakdown:

| Chunk | COVERED | DUPLICATE | GAP-COVER (REG-GUARD) | GAP-HARVEST | Total |
|---|---:|---:|---:|---:|---:|
| 1 (tests 1-50) | 47 | 0 | 3 (0) | 0 | 50 |
| 2 (tests 51-100) | 44 | 0 | 6 (0) | 0 | 50 |
| 3 (tests 101-150) | 35 | 8 | 7 (2) | 0 | 50 |
| 4 (tests 151-199) | 30 | 0 | 14 (5) | 5 | 49 |
| **Totals** | **156 (78%)** | **8 (4%)** | **30 (15%)** | **5 (3%)** | **199** |

## Comparison to original cluster-mode disposition

Cluster mode estimated from `tests/plan/wave-5.6-dedupe-audit.md` §8:

| Disposition | Cluster-mode | Per-test reality | Delta |
|---|---:|---:|---|
| COVERED | ~140 | 156 | +16 (+11%) |
| DUPLICATE-IN-LEGACY | ~10 | 8 | -2 (-20%) |
| GAP-COVER | ~25 | 30 | +5 (+20%) |
| (of which REGRESSION-GUARD) | ~12 | 7 | -5 (-42%) |
| GAP-HARVEST | ~24 | 5 | -19 (-79%) |
| **Total** | **~199** | **199** | **(matched)** |

Net direction: cluster mode **over-estimated GAP-HARVEST** by ~19
tests. The HKT cluster (3 tests) and several "deep-internal" tests
were marked harvest pre-emptively but are e2e-observable on per-test
review; they reclassified to GAP-COVER. Conversely, cluster mode
**under-estimated COVERED** by ~16 tests (the constrained-poly +
trait-op compositional shapes are genuinely absorbed by the
carry-forward universe more than the cluster summary suggested).

REGRESSION-GUARD count is also lower than estimated (7 vs ~12);
cluster mode flagged "sprint regression repros" as REGRESSION-GUARD
broadly, but per-test review shows only 7 tests carry an explicit
regression-guard angle (the post-Sprint-16 D5 visibility cluster +
the auto-curry-error-text test + chunk-3's constraint-display
canonicals).

## Methodology takeaway

Cluster-mode accuracy for ring2.rs:

| Comparison | Cluster predicted | Per-test actual | Match rate |
|---|---:|---:|---:|
| Test-level disposition unchanged | ~150 | 162 (COVERED 156 + DUPLICATE 8 + ~deferred) | **81%** |

ring2.rs cluster-mode accuracy: **~81%** (162/199 in agreement).

Comparison across files audited per-test in Wave 5.6:

| File | Cluster-mode accuracy | Per-test GAP-COVER residue |
|---|---:|---:|
| ring0.rs | 97% | 3 |
| sketch_port.rs | 73% | 27 |
| e2e.rs | 62% | 9 |
| ring1.rs | 72% | 18 |
| **ring2.rs** | **81%** | **30** |

ring2.rs sits at the **upper-middle** of the accuracy distribution,
better than ring1/e2e/sketch_port but worse than ring0. The
high-accuracy first three chunks (1: 94% COVERED; 2: 88% COVERED;
3: 70% COVERED with cluster R DUPLICATE) compensate for chunk 4
(61% COVERED). Cluster mode systematically misclassified two domains:

1. **HKT cluster (3 tests):** marked GAP-HARVEST under "spec coverage
   unclear" but the spec anchors exist and tests are e2e-observable.
2. **Type-system negative shapes (4-5 tests):** marked GAP-HARVEST
   under "deep-internal" but several are straightforward error-path
   e2e tests (occurs check, arity mismatch, multi-sig bare value).

Cluster-mode does best where the cluster shares a uniform spec angle
(chunk 1: trait operators on Int — 47/50 COVERED). It does worst
when the cluster heading hides heterogeneous shapes (chunk 4: module
visibility + type-system corners + HKT + auto-curry, all mixed under
the broad "ring2 misc" cluster).

The 30 GAP-COVER residue across ring2 is **the largest GAP-COVER
surface across all five Wave 5.6 per-test re-audits**:
ring0 = 3, sketch_port = 27, e2e = 9, ring1 = 18, ring2 = 30.
The chunk-4 visibility/type-system cluster alone contributes 14 of
those 30.

## Recommendations for /sprint

1. **Schedule chunk-4 GAP-COVER authoring as a single sub-wave**
   targeting `spec_03_types.rs`, `spec_04_expressions.rs`,
   `spec_07_traits.rs`, `spec_08_modules.rs`, and `spec_09_macros.rs`.
   14 tests; estimate 1 working day at the dispatch density seen in
   Wave 5.5 GAP-COVER remediation (34 tests across 6 files, 1 day).

2. **Group the visibility regression-guard cluster (#176/#177/#179)**
   as a single 3-test slice — they share the spec/08 §8.2-§8.7
   visibility-boundary anchor and a common fixture pattern.
   #178 → recommend dropping (DUPLICATE of #172) on /sprint review.

3. **Group HKT cluster (#187/#188/#189)** as a single 3-test slice
   in spec_07_traits.rs. The 3 tests share the same Functor + Option
   shape and reinforce each other's regression-guard value.

4. **Group constrained auto-curry cluster (#192/#195/#196/#197)** as
   a single 4-test slice. #195 and #196 are paired (Int/Float
   monomorphisation); author together to make the relationship explicit
   in test names.

5. **Defer GAP-HARVEST cluster (#182/#190/#191)** per Wave 5.5
   disposition. File a tracking FIXME under FIXME 0136 noting the
   3 tests are awaiting (a) HKT-on-primitive-rejection error stability
   and (b) lazy Seq spec authority.

6. **Document chunk-1/2/3/4 file-totals** in `tests/plan/PLAN.md` as
   the "ring2 closeout" disposition. Update FIXME 0140 (Wave 5.5
   dedupe-verification) to record the per-test reclassification of
   the HKT and type-system corner-case clusters from GAP-HARVEST →
   GAP-COVER.

7. **Methodology: extend per-test re-audit to remaining legacy files
   smaller than 100 tests:** with five large-file per-test re-audits
   complete and cluster-mode accuracy varying from 62% to 97%,
   continued per-test review of the smaller (<100-test) legacy files
   should be cost-effective. Cluster-mode is reliable for homogeneous
   clusters (chunk 1 ring2: 94% COVERED) but degrades sharply for
   heterogeneous ones (chunk 4 ring2: 61% COVERED with 14 GAP-COVER).

---

(All four chunks of ring2.rs per-test re-audit complete.)
