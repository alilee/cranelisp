<!-- lib/ renamed to stdlib/ (Sprint 11): Reviewed. All test plan references now use
     stdlib/ paths (stdlib/core/syntax.cl, stdlib/prelude.cl, stdlib/core/*.cl).
     Verified: no integration tests (tests/*.rs) import from or depend on stdlib/.
     All tests are free-standing per the stdlib separation principle. -->

# Ring 3 Test Plan: Meta

<!-- Decision 17: RESOLVED. Compiler-seeded traits (Num, Eq, Ord, Display) were removed
     from builtins.rs (Sprint 9). All integration tests that use operators now define
     traits inline via shared helpers in ring2.rs (num_trait_prelude(), eq_trait_prelude(),
     ord_trait_prelude()). Tests that don't need operator dispatch use named primitives
     (add-i64, etc.) directly. -->

**Features**: defmacro, quasiquote, multi-clause macros, bracket destructuring, gensym, reader shortcuts, prelude macros, standard library. Metaprogramming layer.

**Test count target**: ~100 additional tests (~470 cumulative).

**Note**: This ring unblocks the ~180 macro-dependent tests that were blocked in Rings 0–2.

## Tests to Port

### Macro integration (spec: 09-macros)
- `macro_identity`, `macro_constant_constructor`, `macro_sexp_building`
- `macro_two_params`, `macro_two_params_false_branch`
- `macro_variadic`, `macro_chained`, `macro_with_string_arg`
- `macro_no_macros_fast_path`, `macro_expansion_depth_limit`
- `macro_repl_compile_and_register`, `macro_repl_expand_sexp`

### Quasiquote (spec: 09-macros)
- `macro_quasiquote_simple_form`, `macro_quasiquote_false_branch`
- `macro_quasiquote_bracket`, `macro_quasiquote_atom`
- `macro_quasiquote_splicing`, `macro_quasiquote_inc`
- `macro_quasiquote_nested_usage`

### Multi-clause defmacro (spec: 09-macros)
- `multi_clause_arity_dispatch`, `multi_clause_three_clauses`
- `multi_clause_recursive`, `multi_clause_with_docstring`
- `multi_clause_no_match_error`, `multi_clause_zero_arg_clause`

### Bracket destructuring (spec: 09-macros)
- `bracket_destructure_simple`, `bracket_destructure_with_rest`
- `bracket_destructure_empty`, `multi_clause_private`

### Reader shortcuts (spec: 09-macros)
- `quote_symbol_produces_sexp`, `quote_int_produces_sexp`
- `quote_list_produces_sexp`, `quote_bool_produces_sexp`
- `quote_nested_structure`
- `gensym_macro_binds_correctly`, `gensym_no_capture`
- `gensym_different_calls_different_names`
- `anon_fn_single_param`, `anon_fn_two_params`, `anon_fn_zero_params`
- `anon_fn_with_map`

### Thread-first macro `->` (spec: 09-macros, 11-stdlib)
- `thread_first_single_value`, `thread_first_bare_symbol`
- `thread_first_multi_form`, `thread_first_nested`

### Thread-last macro `->>` (spec: 09-macros, 11-stdlib)
- `thread_last_single_value`, `thread_last_bare_symbol`, `thread_last_multi_form`

### Cond macro (spec: 09-macros, 11-stdlib)
- `cond_first_match`, `cond_second_match`, `cond_default`, `cond_with_comparison`

### Case macro (spec: 09-macros, 11-stdlib)
- `case_first_match`, `case_second_match`, `case_default`, `case_with_expression`

### Vec macro (spec: 09-macros, 11-stdlib)
- `vec_macro_elements`, `vec_macro_empty`, `vec_macro_access`

### Sexp parser — `->` and `->>` as symbols (spec: 01-lexical, 02-grammar)
- `sexp_thread_first_is_symbol`, `sexp_thread_last_is_symbol`
- `sexp_minus_still_works`, `sexp_negative_int_still_works`

### Full-prelude batch tests (spec: 05-definitions, 09-macros)
- `batch_const_int`, `batch_const_float`, `batch_const_string`
- `batch_def_basic`, `batch_def_expression`, `batch_def_got_call`
- `batch_defmacro_bad_return_type`
- `batch_bare_symbol_expansion`, `batch_begin_expansion`
- `batch_str_concat`, `batch_str_macro_mixed_types`, `batch_str_macro_empty`

### Derive trait (spec: 07-traits)
- `derive_eq_enum`, `derive_eq_product`, `derive_eq_sum`
- `derive_ord_enum`, `derive_display_enum`, `derive_multiple_traits`
- `derive_eq_direct`, `derive_eq_enum_all_variants`, `derive_ord_enum_leq_geq`
- `derive_example_file`

### Example files (spec: appendix-b-examples)
- `example_hello`, `example_factorial`, `example_strings`, `example_closure`
- `example_float`, `example_traits`, `example_adt`, `example_list`
- `example_vec`, `example_seq`, `example_curry`, `example_mapfold`
- `example_threading`, `example_functor`, `example_macro`, `example_dot_notation`

### Stdlib: List, Vec, Seq, multi-sig (spec: 11-stdlib)
- All ~40 list/vec/seq tests (now unlocked by macro availability)
- All ~13 multi-sig dispatch tests (seq variants)

### Introspection (spec: 12-runtime)
- `repl_sexp_prelude_defn`, `repl_sexp_prelude_multisig`
- `repl_sexp_prelude_trait_impl`, `repl_sexp_prelude_source`

## Phase 1-4 Infrastructure Tests (Sprint 10)

Test cases derived from `design/arch/macro-pipeline.md` and `design/frontend/macro-plan.md`, organized by implementation phase. These validate the macro infrastructure before prelude macros and stdlib integration.

### Phase 1: Synthetic `macros` Module + Marshal (spec: 09-macros §9.1)

#### Constructor type resolution [R3 S10]
- `macros_sexp_sym_resolves` — `macros/SexpSym` resolves to constructor type `(Fn [String] Sexp)` [R3 S10]
- `macros_sexp_int_resolves` — `macros/SexpInt` resolves to `(Fn [Int] Sexp)` [R3 S10]
- `macros_sexp_float_resolves` — `macros/SexpFloat` resolves to `(Fn [Float] Sexp)` [R3 S10]
- `macros_sexp_bool_resolves` — `macros/SexpBool` resolves to `(Fn [Bool] Sexp)` [R3 S10]
- `macros_sexp_str_resolves` — `macros/SexpStr` resolves to `(Fn [String] Sexp)` [R3 S10]
- `macros_sexp_list_resolves` — `macros/SexpList` resolves to `(Fn [(SList Sexp)] Sexp)` [R3 S10]
- `macros_sexp_bracket_resolves` — `macros/SexpBracket` resolves to `(Fn [(SList Sexp)] Sexp)` [R3 S10]

#### SList type structure [R3 S10]
- `macros_snil_is_nullary` — `macros/SNil` is a nullary constructor (tag 0), usable without fields [R3 S10]
- `macros_scons_has_fields` — `macros/SCons` has `shead` and `stail` fields; `(macros/SCons x macros/SNil)` typechecks [R3 S10]
- `macros_slist_is_polymorphic` — `(SList Sexp)` and `(SList Int)` are distinct instantiations [R3 S10]

#### Sexp type structure [R3 S10]
- `macros_sexp_has_seven_constructors` — Sexp has exactly 7 data constructors: SexpInt, SexpFloat, SexpBool, SexpStr, SexpSym, SexpList, SexpBracket [R3 S10]
- `macros_sexp_field_names_prefixed` — All Sexp field names are `s`-prefixed: `sval`, `sname`, `sitems` [R3 S10]

#### Qualified access [R3 S10]
- `macros_qualified_access_without_import` — `macros/SexpSym`, `macros/SCons`, `macros/SNil` usable from `user` module without `(import [macros [*]])` [R3 S10]
- `macros_explicit_import_enables_bare_names` — After `(import [macros [*]])`, bare `SexpSym`, `SCons`, `SNil` resolve correctly [R3 S10]

#### Marshal round-trip (unit-level) [R3 S10]
- `marshal_roundtrip_sexp_int` — `sexp_to_runtime(Sexp::Int(42))` then `runtime_to_sexp` yields `Sexp::Int(42)` [R3 S10]
- `marshal_roundtrip_sexp_float` — Float round-trips through marshal preserving bit representation [R3 S10]
- `marshal_roundtrip_sexp_bool_true` — Bool `true` round-trips [R3 S10]
- `marshal_roundtrip_sexp_bool_false` — Bool `false` round-trips [R3 S10]
- `marshal_roundtrip_sexp_str` — String round-trips preserving content [R3 S10]
- `marshal_roundtrip_sexp_sym` — Symbol round-trips preserving name [R3 S10]
- `marshal_roundtrip_sexp_list` — `Sexp::List` with children round-trips preserving structure [R3 S10]
- `marshal_roundtrip_sexp_bracket` — `Sexp::Bracket` with children round-trips preserving structure [R3 S10]
- `marshal_roundtrip_nested` — Nested structure `(SexpList [SexpInt 1, SexpList [SexpSym "x"]])` round-trips correctly [R3 S10]
- `marshal_roundtrip_slist_nil` — Empty SList (`SNil`) round-trips as tag 0 [R3 S10]
- `marshal_roundtrip_slist_chain` — Multi-element SCons chain round-trips preserving order [R3 S10]

### Phase 2: Quasiquote Expansion Engine (spec: 09-macros §9.4)

#### Literal atom expansion [R3 S10]
- `qq_integer_becomes_sexp_int` — `` `42 `` expands to `(macros/SexpInt 42)` [R3 S10]
- `qq_float_becomes_sexp_float` — `` `3.14 `` expands to `(macros/SexpFloat 3.14)` [R3 S10]
- `qq_bool_becomes_sexp_bool` — `` `true `` expands to `(macros/SexpBool true)` [R3 S10]
- `qq_string_becomes_sexp_str` — `` `"hello" `` expands to `(macros/SexpStr "hello")` [R3 S10]
- `qq_symbol_becomes_sexp_sym` — `` `foo `` expands to `(macros/SexpSym "foo")` [R3 S10]

#### Compound form expansion [R3 S10]
- `qq_list_becomes_sexp_list` — `` `(a b c) `` expands to `(macros/SexpList (macros/SCons <a> (macros/SCons <b> (macros/SCons <c> macros/SNil))))` [R3 S10]
- `qq_bracket_becomes_sexp_bracket` — `` `[a b c] `` expands to `(macros/SexpBracket (macros/SCons <a> (macros/SCons <b> (macros/SCons <c> macros/SNil))))` [R3 S10]
- `qq_empty_list` — `` `() `` expands to `(macros/SexpList macros/SNil)` [R3 S10]
- `qq_empty_bracket` — `` `[] `` expands to `(macros/SexpBracket macros/SNil)` [R3 S10]

#### Unquote and unquote-splicing [R3 S10]
- `qq_unquote_passes_through` — `` `(foo ~expr) `` passes `expr` through as-is (not wrapped in constructor) [R3 S10]
- `qq_unquote_splicing_generates_sconcat` — `` `(foo ~@xs) `` generates `sconcat` call to splice list elements [R3 S10]
- `qq_unquote_splicing_in_bracket` — `` `[~@xs] `` generates `sconcat` inside SexpBracket [R3 S10]

#### Auto-gensym [R3 S10]
- `qq_gensym_consistent_within_expansion` — `x#` used twice in one quasiquote produces the same generated name both times [R3 S10]
- `qq_gensym_different_across_expansions` — `x#` in separate quasiquote expansions produces different names [R3 S10]
- `qq_gensym_different_bases` — `x#` and `y#` in the same quasiquote produce different generated names [R3 S10]

#### Nested quasiquote [R3 S10]
- `qq_nested_depth_handling` — Nested quasiquote `` `(a `(b ~c)) `` increases depth; inner `~c` is structurally quoted at depth > 0 [R3 S10]

#### Module qualification [R3 S10]
- `qq_constructors_are_module_qualified` — All constructor refs in quasiquote output use `macros/` prefix, not bare names [R3 S10]

### Phase 3: `defmacro` Parsing + Body Synthesis (spec: 09-macros §9.2)

#### Single-clause parsing [R3 S10]
- `defmacro_parse_single_clause` — `(defmacro name [x] body)` parses as single clause with one fixed param [R3 S10]
- `defmacro_parse_single_clause_variadic` — `(defmacro name [x & rest] body)` parses with one fixed param and rest param [R3 S10]

#### Multi-clause parsing [R3 S10]
- `defmacro_parse_two_clauses` — `(defmacro name ([x] body1) ([x y] body2))` parses as two clauses [R3 S10]
- `defmacro_parse_three_clauses` — Three-clause defmacro parses correctly with distinct param counts [R3 S10]

#### Bracket destructuring parameter [R3 S10]
- `defmacro_parse_bracket_param` — `(defmacro name [[a b] body] ...)` parses bracket pattern with two fixed names [R3 S10]
- `defmacro_parse_bracket_rest` — `(defmacro name [[a & rest] body] ...)` parses bracket pattern with rest [R3 S10]

#### Rest parameter [R3 S10]
- `defmacro_parse_rest_param` — `& rest` in params yields `rest_param = Some("rest")` [R3 S10]
- `defmacro_parse_rest_must_be_last` — `[& rest x]` is a parse error (rest param not last) [R3 S10]

#### Docstring extraction [R3 S10]
- `defmacro_parse_docstring` — `(defmacro name "docs" [x] body)` extracts docstring [R3 S10]
- `defmacro_parse_no_docstring` — `(defmacro name [x] body)` yields `docstring = None` [R3 S10]

#### Private macro [R3 S10]
- `defmacro_parse_private` — `(defmacro- name [x] body)` sets `is_private = true` [R3 S10]

#### Detection predicates [R3 S10]
- `is_defmacro_recognizes_defmacro` — `is_defmacro()` returns true for `(defmacro ...)` [R3 S10]
- `is_defmacro_recognizes_defmacro_private` — `is_defmacro()` returns true for `(defmacro- ...)` [R3 S10]
- `is_defmacro_rejects_defn` — `is_defmacro()` returns false for `(defn ...)` [R3 S10]
- `is_begin_recognizes_begin` — `is_begin()` returns true for `(begin ...)` [R3 S10]
- `is_begin_rejects_other` — `is_begin()` returns false for `(let ...)` [R3 S10]
- `flatten_begin_extracts_forms` — `flatten_begin((begin a b c))` yields `[a, b, c]` [R3 S10]

#### Synthesized Defn [R3 S10]
- `synthesize_defn_has_slist_sexp_param` — Synthesized Defn takes one parameter of type `(SList Sexp)` [R3 S10]
- `synthesize_defn_returns_sexp` — Synthesized Defn return type annotation is `Sexp` [R3 S10]
- `synthesize_defn_body_is_match_chain` — Synthesized body contains nested match on SCons for arg destructuring [R3 S10]

### Phase 4: CraneliftExpander Implementation (spec: 09-macros §9.3)

#### Compile and expand simple macro [R3 S10]
- `expander_identity_macro` — Compile `(defmacro id [x] x)`, expand `(id 42)` yields `42` [R3 S10]
- `expander_constant_macro` — Compile `(defmacro always-one [] (SexpInt 1))`, expand `always-one` yields `1` [R3 S10]
- `expander_sexp_building_macro` — Macro that constructs `(SexpList ...)` produces correct expansion [R3 S10]

#### Multi-clause dispatch [R3 S10]
- `expander_multi_clause_arity_dispatch` — Two-clause macro dispatches by argument count [R3 S10]
- `expander_multi_clause_first_match_wins` — When multiple clauses could match, the first in definition order wins [R3 S10]
- `expander_multi_clause_no_match_error` — Calling a macro with no matching clause produces a compile-time error [R3 S10]

#### Clause matching [R3 S10]
- `clause_matches_fixed_arity` — Fixed-arity clause matches exact argument count [R3 S10]
- `clause_matches_variadic` — Variadic clause matches argument count >= fixed param count [R3 S10]
- `clause_matches_bracket_structural` — Bracket param clause matches `SexpBracket` argument with correct element count [R3 S10]
- `clause_rejects_bracket_mismatch` — Bracket param clause rejects non-bracket argument [R3 S10]

#### Expansion depth limit [R3 S10]
- `expander_depth_limit_error` — Self-expanding macro hits depth limit and produces compile-time error, not infinite loop [R3 S10]

#### is_macro predicate [R3 S10]
- `is_macro_true_for_registered` — `is_macro()` returns true for a compiled and registered macro [R3 S10]
- `is_macro_false_for_unknown` — `is_macro()` returns false for an unregistered name [R3 S10]

#### Recursive expansion [R3 S10]
- `expand_sexp_recursive` — `expand_sexp()` recursively expands nested macro calls to fixed point [R3 S10]
- `expand_sexp_no_macros_passthrough` — `expand_sexp()` with no macros returns sexp unchanged [R3 S10]

#### Span rewriting [R3 S10]
- `expander_span_rewrite` — Expanded sexp nodes carry the call-site span, not the macro body span [R3 S10]

#### Return type enforcement [R3 S10]
- `expander_bad_return_type_error` — `(defmacro bad [] 42)` produces compile error: body type Int, expected Sexp [R3 S10]

## Phase 5-7 Pipeline, Prelude & REPL Tests (Sprint 11)

Test cases derived from `design/frontend/macro-plan.md` Phases 5-7, `design/arch/macro-pipeline.md` §7 (bootstrapping), `repl/spec.md` §3.3-3.4 + §11, and `sprints/SPRINT.md` Sprint 11 scope.

### Phase 5: Pipeline Integration (spec: 09-macros §9.12, macro-pipeline.md §7)

#### CraneliftExpander wiring [R3 S11]
- `pipeline_batch_uses_cranelift_expander` — Batch `compile_and_run()` uses `CraneliftExpander` (not `NoOpExpander`); a defmacro + usage in the same batch file compiles and executes correctly [R3 S11]
- `pipeline_repl_uses_cranelift_expander` — REPL `eval()` uses `CraneliftExpander`; defmacro at REPL followed by usage in next eval produces correct result [R3 S11]
- `repl_session_owns_expander` — `ReplSession` stores a `CraneliftExpander` field that persists across eval calls; macros defined in one eval are available in subsequent evals [R3 S11]

#### Two-pass prelude loading (spec: 09-macros §9.12) [R3 S11]
- `prelude_pass1_registers_types` — After prelude loading, all prelude-defined types (e.g., `List`, `Option`) are resolvable as type constructors [R3 S11]
- `prelude_pass2_compiles_macros` — After prelude loading, all prelude-defined macros (e.g., `list`, `cond`, `->`) are registered in `CraneliftExpander.is_macro()` [R3 S11]
- `prelude_macros_available_at_repl_startup` — A fresh REPL session can immediately use `(list 1 2 3)` without explicit import or definition [R3 S11]
- `prelude_macro_uses_earlier_macro` — Prelude macros that depend on earlier prelude macros (e.g., `list` uses `slist`) work correctly after two-pass loading [R3 S11]
- `prelude_macro_uses_type_from_pass1` — A prelude macro body that references a type constructor registered in Pass 1 compiles correctly [R3 S11]

#### defmacro interception at Sexp level [R3 S11]
- `batch_defmacro_intercepted_before_ast` — In batch mode, `(defmacro ...)` is intercepted at the Sexp level before reaching the AST builder; the macro is compiled and registered in `MacroEnv` [R3 S11]
- `repl_defmacro_intercepted_before_ast` — In REPL mode, `(defmacro ...)` is intercepted at the Sexp level; subsequent input sees the macro [R3 S11]
- `batch_sequential_defmacro_then_usage` — A batch file with `(defmacro foo ...)` followed by `(foo ...)` compiles and runs correctly because forms are processed sequentially [R3 S11]

#### begin splicing [R3 S11]
- `begin_splicing_batch` — A macro that expands to `(begin form1 form2)` in batch mode: both forms are processed sequentially [R3 S11]
- `begin_splicing_repl` — A macro that expands to `(begin form1 form2)` in REPL mode: both forms are processed; the last form's result is displayed [R3 S11]
- `begin_splicing_defmacro_in_begin` — A `(begin ...)` result containing a `(defmacro ...)` sub-form: the inner defmacro is compiled and registered, subsequent sub-forms can use it [R3 S11]

#### defmacro-in-results [R3 S11]
- `defmacro_in_results_batch` — A macro expansion that produces `(begin (defn ...) (defmacro ...))` (e.g., `def` macro): both the defn and the nested defmacro are compiled and registered [R3 S11]
- `defmacro_in_results_repl` — Same as above but at the REPL; subsequent REPL input can use the nested macro [R3 S11]
- `def_macro_produces_defmacro_in_begin` — The `def` prelude macro expands to a `begin` containing both a `defn` and a `defmacro`; both are functional after expansion [R3 S11]

#### REPL defmacro display (spec: repl/spec.md §11.3) [R3 S11]
- `repl_defmacro_display_single_clause` — Defining a single-clause macro at the REPL displays `name :: macro` [R3 S11]
- `repl_defmacro_display_multi_clause` — Defining a multi-clause macro at the REPL displays `name :: macro (N clauses)` [R3 S11]

#### Error recovery [R3 S11]
- `repl_failed_macro_compilation_no_corrupt` — A `defmacro` with a type error in its body produces an error message but does not corrupt the session; subsequent valid expressions still work [R3 S11]
- `repl_failed_macro_expansion_no_corrupt` — A macro call that fails during expansion (e.g., arity mismatch) produces an error but does not corrupt the expander or typechecker state [R3 S11]

#### Ring 3 gate errors removed [R3 S11]
- `gate_quote_no_longer_errors` — `(quote foo)` no longer produces a Ring 3 gate error in the AST builder [R3 S11]
- `gate_quasiquote_no_longer_errors` — `(quasiquote ...)` no longer produces a Ring 3 gate error [R3 S11]
- `gate_unquote_no_longer_errors` — `(unquote ...)` inside a quasiquote no longer produces a Ring 3 gate error [R3 S11]
- `gate_unquote_splicing_no_longer_errors` — `(unquote-splicing ...)` inside a quasiquote no longer produces a Ring 3 gate error [R3 S11]

### Phase 6: SList Helpers + Prelude Macros (spec: 09-macros §9.7, §9.10, 11-stdlib)

#### SList helpers (stdlib/core/syntax.cl) [R3 S11]
- `slist_sfold_left_fold` — `(sfold f init slist)` performs left fold over an SList; `(sfold + 0 (slist 1 2 3))` yields `6` [R3 S11]
- `slist_sreverse` — `(sreverse (slist 1 2 3))` produces an SList with elements in reverse order [R3 S11]
- `slist_sconcat` — `(sconcat (slist 1 2) (slist 3 4))` produces an SList `(slist 1 2 3 4)` [R3 S11]
- `slist_sempty_nil` — `(sempty? macros/SNil)` returns `true` [R3 S11]
- `slist_sempty_cons` — `(sempty? (macros/SCons x macros/SNil))` returns `false` [R3 S11]
- `slist_macro_builds_chain` — `(slist 1 2 3)` builds an SCons chain equivalent to `(SCons 1 (SCons 2 (SCons 3 SNil)))` [R3 S11]

#### Prelude macro: list [R3 S11]
- `prelude_list_empty` — `(list)` produces `Nil` (empty list) [R3 S11]
- `prelude_list_single` — `(list 1)` produces `(Cons 1 Nil)` [R3 S11]
- `prelude_list_multi` — `(list 1 2 3)` produces a three-element list [R3 S11]
- `prelude_list_nested` — `(list (list 1 2) (list 3 4))` produces nested lists [R3 S11]

#### Prelude macro: do [R3 S11]
- `prelude_do_single` — `(do expr)` evaluates to `expr` [R3 S11]
- `prelude_do_multi` — `(do expr1 expr2 expr3)` evaluates all expressions, returns last [R3 S11]

#### Prelude macro: vec [R3 S11]
- `prelude_vec_elements` — `(vec 1 2 3)` produces a Vec with three elements [R3 S11]
- `prelude_vec_empty` — `(vec)` produces an empty Vec [R3 S11]

#### Prelude macro: cond [R3 S11]
- `prelude_cond_first_match` — `(cond true "yes" "no")` returns `"yes"` [R3 S11]
- `prelude_cond_second_match` — `(cond false "a" true "b" "c")` returns `"b"` [R3 S11]
- `prelude_cond_default` — `(cond false "a" false "b" "default")` returns `"default"` [R3 S11]
- `prelude_cond_with_comparison` — `(cond (> x 0) "pos" (= x 0) "zero" "neg")` works with expressions [R3 S11]

#### Prelude macro: case [R3 S11]
- `prelude_case_first_match` — `(case x Color.Red "red" Color.Green "green" "other")` matches first branch [R3 S11]
- `prelude_case_second_match` — case matches second branch when first fails [R3 S11]
- `prelude_case_default` — case falls through to default [R3 S11]

#### Prelude macro: -> (thread-first) [R3 S11]
- `prelude_thread_first_single` — `(-> x f)` expands to `(f x)` [R3 S11]
- `prelude_thread_first_multi` — `(-> x f g h)` threads through multiple forms [R3 S11]
- `prelude_thread_first_list_form` — `(-> x (f a) (g b))` threads as first arg in list forms [R3 S11]
- `prelude_thread_first_bare_symbol` — `(-> x f)` where `f` is a bare symbol treats it as `(f x)` [R3 S11]

#### Prelude macro: ->> (thread-last) [R3 S11]
- `prelude_thread_last_single` — `(->> x f)` expands to `(f x)` [R3 S11]
- `prelude_thread_last_multi` — `(->> x f g h)` threads through multiple forms [R3 S11]
- `prelude_thread_last_list_form` — `(->> x (f a) (g b))` threads as last arg in list forms [R3 S11]

#### Prelude macro: str [R3 S11]
- `prelude_str_empty` — `(str)` produces `""` [R3 S11]
- `prelude_str_single` — `(str "hello")` produces `"hello"` [R3 S11]
- `prelude_str_multi` — `(str "hello" " " "world")` concatenates strings [R3 S11]

#### Prelude macro: when [R3 S11]
- `prelude_when_true` — `(when true expr)` evaluates and returns `expr` [R3 S11]
- `prelude_when_false` — `(when false expr)` returns `None` (or unit equivalent) [R3 S11]

#### Prelude macro: const / const- [R3 S11]
- `prelude_const_int` — `(const PI 3)` defines a macro that expands to `3` [R3 S11]
- `prelude_const_float` — `(const TAU 6.28)` defines a float constant [R3 S11]
- `prelude_const_string` — `(const GREETING "hello")` defines a string constant [R3 S11]
- `prelude_const_private` — `(const- internal 42)` defines a private constant (not exported) [R3 S11]
- `prelude_const_bare_expansion` — After `(const X 42)`, bare `X` expands to `42` [R3 S11]

#### Prelude macro: def / def- [R3 S11]
- `prelude_def_basic` — `(def foo 42)` defines a zero-arg function and a bare-symbol macro; `(foo)` and bare `foo` both yield `42` [R3 S11]
- `prelude_def_expression` — `(def bar (+ 1 2))` captures expression result; `bar` evaluates to `3` [R3 S11]
- `prelude_def_got_call` — `(def baz (some-fn 1))` — the function is called once at definition time and the result is cached via GOT [R3 S11]
- `prelude_def_private` — `(def- internal 42)` defines a private def (not exported) [R3 S11]

### Phase 7: REPL Polish + New Commands (spec: repl/spec.md §3.3-3.4, §11)

#### /expand command (spec: repl/spec.md §11.1) [R3 S11]
- `repl_expand_single_macro` — `/expand (macro-name arg)` shows the expanded form without evaluating [R3 S11]
- `repl_expand_nested_macros` — `/expand` with nested macro calls shows fully expanded form (recursive to fixed point) [R3 S11]
- `repl_expand_no_macro` — `/expand (+ 1 2)` on a non-macro form displays the input unchanged [R3 S11]
- `repl_expand_error_no_corrupt` — `/expand` on a form with expansion error (e.g., arity mismatch) displays error without corrupting session [R3 S11]
- `repl_expand_alias` — `/e (macro-name arg)` works as alias for `/expand` [R3 S11]

#### /imports command (spec: repl/spec.md §3.4) [R3 S11]
- `repl_imports_shows_grouped` — `/imports` shows all imports grouped by source module with type signatures [R3 S11]
- `repl_imports_alphabetical_names` — Names within each source module group are sorted alphabetically [R3 S11]
- `repl_imports_alphabetical_modules` — Source module groups are sorted alphabetically [R3 S11]
- `repl_imports_shows_individual_names_from_glob` — After `(import [mod [*]])`, `/imports` shows the individual names that were imported, not just `*` [R3 S11]
- `repl_imports_immediate_source` — For re-exported names, `/imports` shows the immediate source module (the module in the import form), not the ultimate origin [R3 S11]
- `repl_imports_filter_by_module` — `/imports prelude` filters to show only names imported from `prelude` [R3 S11]
- `repl_imports_implicit_prelude_visible` — The implicit `(import [prelude [*]])` IS visible in `/imports` output [R3 S11]
- `repl_imports_no_imports_empty` — In a fresh session with no imports and no prelude, `/imports` shows empty output (silent re-prompt, not error) [R3 S11]
- `repl_imports_nonexistent_module` — `/imports nonexistent` shows empty output (silent re-prompt, not error) [R3 S11]

#### /list Macros category (spec: repl/spec.md §11.2.1, §3.3) [R3 S11]
- `repl_list_macros_category_present` — After defining a macro, `/list` includes a "Macros" category listing the macro name [R3 S11]
- `repl_list_macros_multiple` — Multiple defined macros all appear under the Macros category [R3 S11]
- `repl_list_macros_prelude` — Prelude macros (e.g., `list`, `cond`) appear under Macros category after prelude loading [R3 S11]

#### /list Imports category (spec: repl/spec.md §3.3) [R3 S11]
- `repl_list_imports_summary` — After importing, the Imports category shows a count of imported names per source module [R3 S11]
- `repl_list_imports_small_inline` — For small imports (<=5 names), the names are listed inline after the count [R3 S11]
- `repl_list_imports_large_count_only` — For large imports (>5 names), only the count is shown [R3 S11]

#### Macro introspection (spec: repl/spec.md §11.2.2-11.2.4, §11.4) [R3 S11]
- `repl_info_macro_single_clause` — `/info name` for a single-clause macro shows `name :: macro` [R3 S11]
- `repl_info_macro_multi_clause` — `/info name` for a multi-clause macro shows `name :: macro (N clauses)` and clause count [R3 S11]
- `repl_info_macro_docstring` — `/info name` for a macro with a docstring shows the docstring [R3 S11]
- `repl_sig_macro_variadic` — `/sig name` for a variadic macro shows parameter signature with `& rest` [R3 S11]
- `repl_sig_macro_bracket` — `/sig name` for a bracket-destructuring macro shows bracket notation in signature [R3 S11]
- `repl_sig_macro_multi_clause` — `/sig name` for a multi-clause macro shows each clause's parameter list [R3 S11]
- `repl_doc_macro_present` — `/doc name` for a macro with docstring shows the docstring [R3 S11]
- `repl_doc_macro_absent` — `/doc name` for a macro without docstring shows "no docstring" message [R3 S11]
- `repl_bare_macro_lookup` — Entering a macro name bare (non-zero-arg) displays clause signatures per self-documentation contract [R3 S11]

#### List value display (spec: repl/spec.md §1.5) [R3 S11]
- `repl_list_value_display` — `(list 1 2 3)` displays as `:... (list 1 2 3)` using the `(list ...)` format [R3 S11]
- `repl_list_value_display_empty` — `List.Nil` displays as `List.Nil` (nullary constructor notation) [R3 S11]
- `repl_list_value_display_nested` — Nested lists display recursively in `(list ...)` format [R3 S11]

#### Overloaded fn display (spec: repl/spec.md §1.3) [R3 S11]
- `repl_overloaded_fn_shows_all_variants` — Defining an overloaded function shows all variant signatures [R3 S11]

### Sprint 10 Deferred Items (spec: 09-macros)

#### Edge-case test gaps [R3 S11]
- `expander_depth_limit_error_message` — Self-expanding macro hits depth limit; error message names the macro and the iteration count [R3 S11]
- `marshal_rc_inc_direct` — Direct test of `rc_inc` on marshalled Sexp values (verify no double-free or leak) [R3 S11]
- `defmacro_malformed_missing_name` — `(defmacro)` with no name produces a clear parse error [R3 S11]
- `defmacro_malformed_missing_params` — `(defmacro foo body)` with no param bracket produces a clear parse error [R3 S11]
- `defmacro_malformed_bad_return_type` — `(defmacro bad [] 42)` produces compile error: body type Int, expected Sexp [R3 S11]

### Negative Test Audit: Rings 0-2 Existing Features (Sprint 11, Wave 2)

These tests run against the CURRENT codebase BEFORE Ring 3 changes land. They verify what MUST NOT happen for existing REPL features, surfacing hidden defects early.

#### /list scope boundaries (spec: repl/spec.md §3.3 negative requirements) [R3 S11]
- `list_neg_no_primitives_in_functions` — `/list` Functions category MUST NOT contain primitives (`add-i64`, `mul-i64`, `eq-i64`, etc.) when current module is `user` [R3 S11]
- `list_neg_no_imported_names_in_functions` — `/list` Functions category MUST NOT contain imported names (trait methods like `+`, `show`) — they belong in Imports [R3 S11]
- `list_neg_no_primitives_types_in_types` — `/list` Types category MUST NOT contain types from `primitives` module (`Int`, `Bool`, `Float`, `String`) [R3 S11]
- `list_neg_fresh_session_special_forms_only` — Fresh `user` session with no definitions: `/list` MUST show ONLY Special forms (no Functions, no Types, no Traits) [R3 S11]
- `list_neg_defn_adds_functions_not_primitives` — After `(defn foo [x] x)`: Functions category appears with `foo`, but primitives still absent from Functions [R3 S11]
- `list_neg_constructors_not_in_functions` — After `(deftype Color Red Green Blue)`: constructors `Red`, `Green`, `Blue` MUST NOT appear in Functions category (they belong to their type) [R3 S11]
- `list_neg_no_item_in_two_categories` — No item appears in two different `/list` categories simultaneously [R3 S11]

#### Expression/definition display negatives (spec: repl/spec.md §1.2-1.3) [R3 S11]
- `display_neg_defn_not_closure` — `(defn foo [x] x)` MUST NOT display `<closure>` — must show qualified name `user/foo` [R3 S11]
- `display_neg_type_always_qualified` — Named function result MUST NOT show bare unqualified type (`Int` alone); must show `primitives/Int` [R3 S11]
- `display_neg_type_vars_normalized` — Type variables MUST NOT show internal names (`t0`, `t1`, `_t42`) — must be normalized to `a`, `b`, `c` [R3 S11]
- `display_neg_deftype_not_function` — `(deftype Color Red Green Blue)` MUST NOT show function-like type — must show `:user/Color` [R3 S11]

#### Error boundary negatives (spec: repl/spec.md §5.2) [R3 S11]
- `error_neg_type_error_no_corrupt_next` — After a type error, next valid expression MUST NOT be affected by failed type state [R3 S11]
- `error_neg_parse_error_preserves_definitions` — After a parse error, previously defined functions MUST still be callable [R3 S11]
- `error_neg_failed_defn_no_partial_binding` — Failed `defn` (e.g., type error in body) MUST NOT leave a partial binding in scope [R3 S11]

#### Module resolution negatives (spec: repl/spec.md §4.1) [R3 S11]
- `module_neg_unimported_primitive_unbound` — Entering a name that exists in `primitives` but not `user` (e.g., `add-i64` without import) MUST produce "unbound" error, not silently resolve [R3 S11]

### Negative Tests: Ring 3 New Features (Sprint 11, Wave 4)

These verify what MUST NOT happen for Ring 3-specific features.

#### /imports empty and boundary cases [R3 S11]
- `imports_neg_no_imports_not_error` — `/imports` with no imports produces empty output (silent re-prompt), NOT an error message [R3 S11]
- `imports_neg_nonexistent_module_not_error` — `/imports nonexistent` produces empty output, NOT an error message [R3 S11]

#### Macro category boundaries [R3 S11]
- `list_neg_non_macros_absent_from_macros` — `/list` Macros category MUST NOT contain functions, types, or other non-macro definitions [R3 S11]
- `list_neg_macros_absent_from_functions` — `/list` Functions category MUST NOT contain macro names [R3 S11]
- `macro_neg_zero_arg_expands_not_introspects` — A zero-argument macro entered bare MUST expand (not display introspection); introspection is for non-zero-arg macros [R3 S11]

#### /expand boundary cases [R3 S11]
- `expand_neg_non_macro_unchanged` — `/expand (+ 1 2)` on a non-macro form MUST display the input unchanged, NOT an error [R3 S11]
- `expand_neg_error_no_corrupt` — `/expand` on a malformed macro call MUST display an error WITHOUT corrupting session state [R3 S11]

#### Malformed macro errors [R3 S11]
- `macro_neg_malformed_no_crash` — A malformed macro call (wrong arity, wrong arg types) MUST produce a clear error message, NOT a crash or panic [R3 S11]
- `macro_neg_expansion_limit_clear_error` — A self-recursive macro that exceeds the expansion depth limit MUST produce a clear error naming the macro, NOT an infinite loop [R3 S11]
- `macro_neg_bad_return_type_compile_error` — A macro body that returns `Int` instead of `Sexp` MUST produce a compile-time type error [R3 S11]

## New Tests

- Macro expansion depth limit (verify error, not infinite loop)
- Macro error reporting (error span points to call site, not macro body)
- Prelude completeness (every prelude export is reachable via import)
- `stdlib/core/*.cl` modules all compile without errors
- Macro + RC interaction (macro-generated code with heap types has balanced RC)

## Acceptance Gate

- `stdlib/prelude.cl` compiles fully
- All prelude macros expand correctly
- Standard library functions pass unit tests
- All Ring 0–2 tests still pass (regression)
- `/review` approves Ring 3
