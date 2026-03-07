# Ring 3 Test Plan: Meta

<!-- FIXME(/qa): Decision 17 — when compiler-seeded traits (Num, Eq, Ord, Display) are
     removed from builtins.rs, all existing integration tests that use operators (+, -, *,
     /, =, <, >, <=, >=, show) will fail. Each test must either (a) define the necessary
     traits/impls inline, or (b) use named primitives (add-i64 etc.) directly. A shared
     test helper that emits the trait boilerplate would reduce duplication. Ring 2 tests
     that specifically test trait dispatch should define traits inline — that makes the
     test self-contained and explicit. See design/arch/CLAUDE.md Decision 17. -->

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

## New Tests

- Macro expansion depth limit (verify error, not infinite loop)
- Macro error reporting (error span points to call site, not macro body)
- Prelude completeness (every prelude export is reachable via import)
- `lib/core/*.cl` modules all compile without errors
- Macro + RC interaction (macro-generated code with heap types has balanced RC)

## Acceptance Gate

- `lib/prelude.cl` compiles fully
- All prelude macros expand correctly
- Standard library functions pass unit tests
- All Ring 0–2 tests still pass (regression)
- `/review` approves Ring 3
