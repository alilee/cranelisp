# Ring 3 Test Plan: Meta

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
