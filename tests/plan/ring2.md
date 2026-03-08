# Ring 2 Test Plan: Abstraction

**Features**: Traits, method resolution, constrained polymorphism, monomorphisation, multi-sig dispatch, auto-curry, modules, imports, exports, visibility. Name resolution and dispatch established.

**Test count target**: ~160 additional tests (~370 cumulative).

## Tests to Port

### Traits — builtin show (spec: 07-traits)
- `builtin_show_int`, `builtin_show_bool`, `builtin_show_string`
- `repl_builtin_show_int`, `repl_builtin_show_bool`

### Traits — user-defined (spec: 07-traits)
- `user_defined_trait_impl`, `user_defined_trait_with_show`
- `repl_user_defined_trait`, `repl_user_trait_with_show`

### Trait introspection (spec: 07-traits, 12-runtime)
<!-- FIXME(/qa): None of the trait introspection tests below have been written. Typing a bare trait name (e.g. `Num`, `Display`) at the REPL produces `undefined variable` instead of listing method signatures. Spec: repl/spec.md §4.1 (bare trait name should produce method signatures). Implementing skill: /int (REPL eval path). Found by /repl in ring2b.demo Sprint 12. -->
- `repl_bare_builtin_trait_method_type`, `repl_bare_user_trait_method_type`
- `repl_non_trait_var_returns_none`
- `repl_bare_builtin_trait_display`, `repl_bare_user_trait_display`
- `repl_bare_trait_name_not_function`, `repl_trait_error_recovers`

### Default methods (spec: 07-traits)
- `default_method_used_when_not_overridden`, `default_method_overridden`
- `default_method_calls_other_trait_method`
- `default_method_less_equal_boundary`, `default_method_greater_equal`
- `repl_default_method_basic`, `repl_default_method_override`
- `default_method_on_adt`, `default_method_validate_impl_missing_required`

### ADT trait impls (spec: 03-types, 07-traits)
- `adt_display_enum`, `adt_display_product`
- `adt_eq_enum`, `adt_eq_enum_not_equal`
- `repl_adt_display_enum`, `repl_adt_eq_enum`
- `adt_display_option_int_batch`, `adt_display_option_int_none_batch`
- `repl_adt_display_option_int`
- `adt_display_option_polymorphic_batch`, `repl_adt_display_option_polymorphic`
- `parse_impl_target_bare`, `parse_impl_target_concrete_adt`, `parse_impl_target_constrained_adt`

### Multi-sig dispatch (spec: 05-definitions)
- `multi_sig_different_arities`, `multi_sig_type_based_dispatch`, `multi_sig_duplicate_signature_error`
- `repl_multi_sig_different_arities`

### Auto-curry (spec: 04-expressions)
- `auto_curry_simple`, `auto_curry_higher_order`, `auto_curry_multi_sig`
- `repl_auto_curry`, `repl_multi_sig_auto_curry`

### Defn type finalization (spec: 03-types, 07-traits)
- `repl_defn_using_trait_stores_concrete_type`, `repl_defn_using_trait_rejects_wrong_type`
- `repl_defn_using_trait_accepts_correct_type`, `repl_defn_truly_polymorphic_stays_polymorphic`

### Constrained polymorphism (spec: 03-types, 07-traits)
- `constrained_add_int`, `constrained_add_float`, `constrained_add_both_types`
- `constrained_never_called_ok`
- `repl_constrained_fn_int`, `repl_constrained_fn_float`, `repl_constrained_fn_both_types`
- `repl_constrained_fn_bare_name_describes`, `repl_constrained_fn_as_value_errors`
- `repl_overloaded_fn_bare_name_describes`

### Functor HKT (spec: 07-traits)
- `functor_fmap_option_some`, `functor_fmap_option_none`
- `functor_fmap_list`, `functor_fmap_list_all_elements`, `functor_fmap_list_empty`
- `functor_fmap_with_lambda`, `functor_fmap_composition`
- `functor_fmap_seq_basic`, `functor_fmap_seq_empty`, `functor_fmap_seq_with_range`
- `functor_hkt_arity_error`

### Type annotations (spec: 03-types)
- `annotation_expr_int`, `annotation_constrains_none_to_option_int`
- `annotation_param_concrete`, `annotation_param_trait_constraint`, `annotation_param_trait_both_types`
- `repl_annotation_expr`, `repl_annotation_option_int`
- `repl_annotation_param_defn`, `repl_annotation_trait_constraint`
- `repl_annotation_trait_constraint_float`, `repl_annotated_lambda`

### Modules (spec: 08-modules)
- `single_file_via_run_project`, `module_missing_file_error`, `module_cycle_detection`
- `module_qualified_name_resolution`, `module_unknown_qualified_name_error`
- `example_imports`

### Imports (spec: 08-modules)
- `import_specific_names`, `import_glob`
- `import_nonexistent_name_errors`, `import_undeclared_module_errors`
- `qualified_access_still_works_without_import`, `bare_name_from_non_imported_module_not_accessible`

### Visibility (spec: 08-modules)
- `private_defn_not_accessible_via_qualified`, `private_defn_not_importable`
- `public_defn_accessible_via_qualified`
- `private_deftype_constructors_not_importable`, `glob_import_skips_private`

### Exports (spec: 08-modules)
- `export_re_exports_names`, `export_cannot_reexport_private`

### Ambiguity (spec: 08-modules)
- `ambiguous_import_same_name_different_sources`, `definition_conflicts_with_import`
- `import_shadows_prelude_allowed`
- `init_builtins_registers_qualified_only`, `init_builtins_no_platform_module`
- `get_module_public_names_primitives`, `get_module_public_names_platform_empty_without_dll`
- `repl_full_session_primitives_not_in_user_scope`, `repl_full_session_qualified_primitive_accessible`
- `repl_full_session_print_not_visible_without_platform`
- `repl_full_session_qualified_name_primitives`, `repl_full_session_fold_helpers_not_visible`
- `repl_full_session_list_no_inline_primitives`, `repl_full_session_overloaded_fn_qualified`
- `repl_full_session_get_module_public_names_excludes_private`
- `ambiguous_trait_method_bare_name_errors`, `ambiguous_import_qualified_bypass`
- `repl_ambiguous_trait_method_describe`

### Symbol display (spec: 12-runtime)
- `repl_user_fn_bare_name_describes`, `repl_prelude_fn_bare_name_describes`

### Inline modules (spec: 08-modules)
- `inline_module_extraction`, `inline_module_with_super_import`
- `super_import_in_top_level_module_errors`
- `repl_mod_switches_to_inline_submodule`

## New Tests

- Cross-module trait dispatch with heap-typed arguments (RC correctness)
- Cross-module constrained polymorphism (specialization compiled into defining module)
- Module reload invalidation (basic, ahead of Ring 4 hot-reload)
- Trait + ADT interaction with RC (trait method receives ADT, returns ADT)
- Known-issue tests rewritten for correct behavior:
  - `adt_accessor_shadowing` — should use module-scoped accessors
  - `qualified_name_resolution` — should resolve correctly

## Design-Doc-Derived Tests

Tests identified by reviewing the three Ring 2 design documents (`design/backend/ring2-rc.md`, `design/typecheck/traits.md`, `design/frontend/modules.md`) against existing coverage. Organized by design doc, with gap analysis.

---

### From `design/backend/ring2-rc.md` — RC, Calling Conventions, Drop Glue

#### Already covered (no new tests needed)

- RC starts at 1 (Invariant 6.1.2): `rc_string_alloc_and_drop`, `rc_adt_product_alloc`, `rc_closure_env_alloc`, `rc_vec_alloc_drop`
- RC never negative (Invariant 6.1.1): tested implicitly via `debug_assert!` in all RC tests
- NeverHeap types skip RC: `rc_adt_enum_no_alloc`, `rc_adt_sum_none_no_alloc`
- Mixed ADT guarded dec: `rc_mixed_adt_none_drop`, `rc_mixed_adt_some_drop` and balanced variants
- Scope cleanup dec's bindings: `rc_string_in_let_scope`, `rc_adt_in_let_scope`, `rc_closure_in_let_scope`
- Consuming convention for user functions: `rc_string_passed_to_function`, `rc_adt_returned_from_function`
- Closure drop glue: `rc_closure_captures_string`, `rc_closure_captures_adt`, `rc_closure_captures_string_balanced`
- Vec drop glue: `rc_vec_of_strings`, `rc_vec_of_options`
- Vec COW: `rc_vec_set_copy`, `rc_vec_push_copy`
- Match field extraction inc: `rc_adt_in_match_arms`, `rc_adt_containing_string_in_match`

#### New tests — RC calling convention gaps [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `rc_borrowing_conv_string_temporary` | §3.2 Borrowing Convention | String temporary passed to extern (`str-eq`) is dec'd by caller after call; verify no leak |
| `rc_borrowing_conv_var_not_dec` | §3.2 Borrowing Convention | String variable passed to extern is NOT dec'd by caller (scope owns it); verify no double-free |
| `rc_consuming_conv_var_inc_before_call` | §3.1 Consuming Convention | Variable arg to user fn gets inc'd before call so caller's binding survives callee's dec |
| `rc_consuming_conv_temporary_no_inc` | §3.1 Consuming Convention | Temporary arg to user fn starts at rc=1; callee's dec frees it; no caller inc needed |
| `rc_data_ctor_conv_no_inc_dec` | §3.3 Data Constructor Convention | Variable stored into ADT constructor has no inc/dec at call site; drop glue handles it |
| `rc_data_ctor_conv_temporary_field` | §3.3 Data Constructor Convention | Temporary expression as ADT field — rc=1 at construction, drop glue dec's it |

#### New tests — protect_return_value gaps [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `rc_protect_return_if_alias` | §5.3 protect_return_value | `(let [s "hello"] (if cond s "world"))` — return value aliases scope binding; must inc before scope cleanup |
| `rc_protect_return_match_alias` | §5.3 protect_return_value | `(let [s "hello"] (match x [_ s]))` — match arm returns scope-aliased value; must inc |
| `rc_protect_return_fresh_alloc_no_inc` | §5.3 protect_return_value | `(let [s "hello"] "world")` — fresh StringLit cannot alias; no inc needed; verify balanced |
| `rc_protect_return_lambda_no_inc` | §5.3 protect_return_value | `(let [s "hello"] (fn [x] x))` — fresh lambda cannot alias; no inc needed |

#### New tests — temporary closure callee [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `rc_temporary_closure_callee_dec` | §3.5 Temporary Closure Callee | `((make-adder 5) 3)` — temporary closure at rc=1 is dec'd after call; result protected |
| `rc_temporary_closure_callee_result_alias` | §3.5 Temporary Closure Callee | Closure returns a captured value — result inc'd before closure dec to prevent premature free |

#### New tests — scope cleanup edge cases [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `rc_scope_skip_var_direct_return` | §5.2 return_var_in_scope | `(let [s "hello"] s)` — direct Var return skips dec of `s`; verify balanced |
| `rc_scope_skip_var_non_var_body` | §5.2 return_var_in_scope | `(let [s "hello"] (if true s "world"))` — body is `if`, skip_var is None; protect_return_value handles it |
| `rc_match_arm_field_binding_cleanup` | §5.4 Match Interaction | Constructor pattern extracts heap field; arm body does NOT return it; scope cleanup dec's extracted field |
| `rc_match_scrutinee_temporary_dec` | §5.4 Match Interaction | Scrutinee is a temporary expression (function call returning ADT); dec'd after all arms merge |

#### New tests — captured variable last-use invariant [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `rc_captured_var_never_last_use` | §5.5 Captured Variables | Variable closed over by lambda is NOT eligible for last-use transfer even at final use site; closure env holds its own inc'd reference |

#### New tests — TCO + RC interaction [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `rc_tco_heap_param_leak` | §8.2 TCO and RC | Self-recursive tail call with heap-typed param — document whether it leaks (known gap per design doc) or whether cleanup is implemented |

#### New tests — drop glue correctness [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `rc_adt_inline_drop_glue_multi_ctor` | §4.2 ADT Inline Drop Glue | ADT with multiple data constructors (each with heap fields) — tag-dispatch drop glue dec's correct fields per constructor |
| `rc_closure_drop_glue_ptr_zero` | §4.1 Closure Drop Glue | Closure with no heap captures has drop_glue_ptr = 0; dec skips glue call; verify no crash |
| `rc_closure_drop_glue_ptr_nonzero` | §4.1 Closure Drop Glue | Closure with heap captures has nonzero drop_glue_ptr; dec calls glue which dec's each captured heap value |
| `rc_vec_elem_dec_fn_adt` | §4.3 Vec Drop Glue | Vec of ADT with heap fields — elem_dec_fn calls ADT drop glue per element on Vec drop |

---

### From `design/typecheck/traits.md` — Traits, Constrained Poly, Monomorphisation

#### Already covered (no new tests needed)

- Core trait operators (+, -, *, /, =, <, show): 60+ tests in ring2.rs covering Int/Float/Bool/String
<!-- FIXME(/qa): `default_method_neq_int` test listed below but never written. `!=` cannot even parse because `!` is not in the sexp parser's `operator_char` set (only `+ - * / = < >`). The test must first verify that `!=` parses as an operator symbol, then verify its default-method semantics. Spec: spec/07-traits.md line 206 (defines `!=` as Eq default method). Implementing skill: /frontend (sexp parser operator_char pattern). Found by /repl in ring2b.demo Sprint 12. -->
- Default methods (!=, >, <=, >=): `default_method_gt_int`, `default_method_le_int`, `default_method_ge_int`, `default_method_neq_int` etc.
- User-defined traits: `user_trait_simple`, `user_trait_adt`, `user_trait_multiple_impls`
- Constrained polymorphism basic: `constrained_add_int`, `constrained_add_float`, `constrained_add_both_types`, `constrained_never_called_ok`
- REPL constrained fn: `repl_constrained_fn_int`, `repl_constrained_fn_float`
- Type annotation constraints: `annotation_concrete_type_int`, `annotation_wrong_type_error`, `annotation_mismatch_call_error`
- Trait method across modules: `trait_method_accessible_across_modules`
- Trait+ADT interaction: `trait_operators_in_adt_function`, `trait_arithmetic_with_adt_field`, `trait_eq_in_match_branch`
- Error: type mismatch in operators: `error_type_mismatch_plus`, `error_plus_bool`, `error_lt_string`

#### New tests — trait registry invariants [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `trait_duplicate_method_name_error` | §1 Invariant: method name uniqueness | Two traits declaring the same method name should produce an error; `method_to_trait` would be corrupted otherwise |
| `trait_duplicate_trait_name_error` | §2 Duplicate check | `(deftrait (Foo a) ...) (deftrait (Foo a) ...)` — re-declaring same trait name should error |
| `trait_impl_missing_required_method_error` | §3 Required method check, Invariant 10.2 | `(impl Num MyType ...)` missing a required method should error |
| `trait_impl_extra_method_ignored_or_error` | §3 Registration Pipeline | `(impl Num Int (defn extra-fn ...))` — providing a method not in the trait |

#### New tests — constraint propagation invariants [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `constraint_resolves_through_substitution` | §6 Constraint Propagation, Invariant 10.7 | Constraint on `Var(X)` where `subst[X] = Var(Y)` attaches to `Y` in the scheme; verify via generalized scheme inspection |
| `constraint_in_scheme_references_scheme_var` | §6, Invariant 10.5 | After generalization, every constraint key must be in the scheme's `vars` list |
| `active_constraints_not_cleared_between_forms` | §6, Invariant 10.6 | Two top-level forms in same batch — constraints from first form available during generalization of second |

#### New tests — monomorphisation invariants [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `mono_constrained_fn_not_compiled_directly` | §7 Invariants, 10.8 | Backend skips `Defn` whose name is in `constrained_fn_names`; only MonoDefn specializations compiled |
| `mono_deduplication` | §7 Invariants, 10.10 | Two call sites with same concrete types produce one MonoDefn, both dispatch to same mangled name |
| `mono_per_mono_isolation` | §7 Invariants, 10.9 | Each MonoDefn uses its own `resolutions` and `expr_types`, not the program-wide maps |
| `mono_self_recursive_constrained` | §7 monomorphise_call step 6 | Constrained function that calls itself recursively — inner call generates SigDispatch to same specialization |
| `mono_constraint_satisfaction_error` | §7 monomorphise_call step 4 | Call site passes type without required trait impl — should produce clear error |

#### New tests — method resolution invariants [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `resolution_deferred_then_resolved` | §8 Deferred Resolution, Invariant 10.12 | Trait call with unresolved arg type during inference gets resolved after substitution is complete |
| `resolution_span_keyed` | §8, Invariant 10.11 | Each Apply span maps to exactly one ResolvedCall; no span collision between different call sites |
| `resolution_primitive_for_trait_method_inline` | §8 primitive_for_trait_method | `(+ 1 2)` resolves to TraitMethod, backend maps to inline IR via primitive_for_trait_method; not a function call |
| `resolution_user_impl_direct_call` | §8 primitive_for_trait_method None path | User trait method with user impl — primitive_for_trait_method returns None; backend compiles direct call to mangled name |

#### New tests — bootstrap invariants [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `bootstrap_clear_transient_state` | §5, Invariant 10.13 | After core trait registration, `expr_types` and `method_resolutions` contain no SYNTHETIC span entries |
| `bootstrap_pipeline_uniformity` | §5, Invariant 10.14 | Core traits use same `register_trait_decl`/`register_trait_impl` pipeline as user traits; verify via user trait that exercises same code paths |

#### New tests — multi-sig edge cases [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `multi_sig_repl_not_supported_error` | §9 REPL Status | `DefnMulti` in REPL should produce a clear error, not crash |
| `multi_sig_constrained_poly_unsupported` | §9 Interaction note | Multi-sig variant that calls trait methods is not auto-detected as constrained; document behavior |

#### New tests — default method edge cases [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `default_method_override_provided` | §4 Override | Impl provides a method that has a default — provided implementation used instead of default |
| `default_method_on_user_adt` | §4 Generation | Default methods generated for user-defined ADT impl (not just primitive types) |

---

### From `design/frontend/modules.md` — Module System, Cross-Module Resolution

#### Already covered (no new tests needed)

- Single file compilation: `single_file_via_run_project`
- Missing module file: `module_missing_file_error`
- Cycle detection (toposort): `module_cycle_detection`
- Qualified name resolution: `module_qualified_name_resolution`, `qualified_reference_to_module`
- Import specific names: `import_specific_names`
- Glob import: `import_glob`
- Import nonexistent name: `import_nonexistent_name_errors`
- Visibility private defn: `visibility_private_defn_not_importable`
- Visibility public defn: `visibility_public_defn_importable`
- Visibility private deftype: `visibility_private_deftype_not_importable`
- Trait method across modules: `trait_method_accessible_across_modules`
- Local shadows module: `name_resolution_local_shadows_module`
- Module declarations before compilation: `module_phase_declarations_order_independent`
- Synthetic primitives module: `synthetic_primitives_module_available`

#### New tests — import chain depth limit [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `import_chain_depth_limit_exceeded` | §4.2, Invariant 9.2 | Re-export chain exceeding `IMPORT_CHAIN_DEPTH_LIMIT = 10` returns None (name not found); verify graceful failure, not infinite loop |
| `import_chain_normal_reexport` | §4.2 | Re-export chain of depth 2-3 resolves correctly; verify Reexport follows Import chain to terminal Def |

#### New tests — ambiguity detection [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `ambiguous_import_produces_error` | §3.2, Invariant 9.3 | Two modules export different `helper` fns; importing both via glob produces Ambiguous entry; using bare name errors |
| `ambiguous_same_source_not_ambiguous` | §3.2 | Same name arriving through two re-export paths from same original definition is NOT ambiguous (spec §8.6.4) |
| `ambiguous_qualified_bypass` | §4.3 | Ambiguous bare name errors, but qualified `mod/name` access works |

#### New tests — qualified name resolution edge cases [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `qualified_child_of_current_module` | §4.3 | `util/helper` from module `main` resolves to `main.util` first (child-of-current-module priority) |
| `qualified_absolute_path_fallback` | §4.3 | When child path fails, absolute path `util` is tried; verify correct fallback |
| `qualified_private_from_outside_subtree_error` | §4.3, §3.4 | Qualified reference to private name from outside the subtree produces TypeError |
| `qualified_private_from_child_module_ok` | §4.3, §3.4 | Child module can access parent's private names (subtree check: `is_in_subtree`) |

#### New tests — module alias [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `import_with_alias` | §3.1 | `(import [(core.string str) []])` registers `str` as alias; `str/concat` resolves correctly |
| `alias_in_qualified_name` | §4.3 | First path component resolved through `module_aliases`; verify alias lookup in `resolve_qualified` |

#### New tests — member glob import [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `import_member_glob_constructors` | §3.1, §3.2 | `[Display.*]` imports all constructors or methods matching the parent name |
| `import_member_glob_trait_methods` | §3.1 | MemberGlob on trait name imports that trait's methods |

#### New tests — export/reexport [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `export_creates_reexport_entries` | §3.3 | Export specs create `Reexport` entries (not `Import`); verify semantically distinct |
| `export_glob_skips_private` | §3.4 | `(export [submod [*]])` skips private names from submodule |
| `reexport_chain_follows_to_def` | §4.2 | Reexport -> Import -> Def chain followed correctly; terminal Def produces scheme |

#### New tests — set_current_module bootstrap [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `new_module_seeded_with_builtins` | §5.5 | `set_current_module("math")` creates table with all primitives, special forms, constructors copied as Import from "user" |
| `current_module_always_exists` | Invariant 9.4 | After `set_current_module`, `current_symbol_table()` never panics |

#### New tests — topological compilation [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `toposort_leaves_first` | §5.2 | Leaf modules (no dependencies) compile before dependents; verify order |
| `toposort_diamond_dependency` | §5.2 | Diamond dependency pattern (A->B, A->C, B->D, C->D) — D compiled first, A last |

#### New tests — cross-module function resolution [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `cross_module_func_sigs_accumulated` | §5.3 | Each compiled module's function signatures accumulated in `all_func_sigs`; downstream module can call upstream functions |
| `cross_module_qualified_alias_registered` | §5.3 | Submodule function `helper` in module `main.util` registered as `util/helper` alias for parent `main` |

#### New tests — REPL module integration [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `repl_mod_switch_creates_new_table` | §7.2 | `/mod math` creates new symbol table if one doesn't exist |
| `repl_mod_switch_preserves_builtins` | §7.2 | After `/mod math`, operators and builtins still work |
| `repl_import_requires_loaded_module` | §7.3 | REPL `(import [missing [*]])` — module not loaded produces error |
| `repl_snapshot_restore_on_error` | §7.5 | Failed REPL input does not corrupt type environment; subsequent input works |
| `repl_snapshot_restore_type_var_counter` | §7.5 | After error, `next_type_id` rolled back; fresh type vars do not leak |

#### New tests — module declarations before macro expansion [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `mod_import_export_not_subject_to_expansion` | Invariant 9.6 | `mod`, `import`, `export` extracted from raw sexps before AST builder; not subject to macro expansion |

#### New tests — cross-module GOT (interactive mode) [R2 S9]

| Test name | Design doc reference | Description |
|---|---|---|
| `repl_cross_module_got_local_first` | §5.4 | `resolve_got_entry` checks local GOT first, then cross-module GOT |
| `repl_cross_module_got_call` | §5.4 | Function compiled in one module's GOT callable from another module via cross-module GOT |

---

### Cross-Subsystem Interaction Tests [R2 S9]

Tests covering boundaries where two subsystems interact.

| Test name | Subsystems | Description |
|---|---|---|
| `rc_trait_method_heap_arg_consuming` | RC + Traits | Trait method on user impl receiving heap-typed arg (String/ADT) — consuming convention applies; balanced RC |
| `rc_trait_method_primitive_borrowing` | RC + Traits | Trait method resolving to primitive (e.g., `str-eq`) — borrowing convention applies; temporary String dec'd by caller |
| `rc_constrained_mono_heap_args` | RC + Monomorphisation | Monomorphised specialization of constrained fn with heap-typed args — calling convention correct per specialization |
| `rc_cross_module_fn_call_heap` | RC + Modules | User function in module A calls user function in module B with String arg — consuming convention across module boundary |
| `rc_cross_module_adt_drop_glue` | RC + Modules | ADT defined in module A, constructed in module B — drop glue correctly dec's fields even though type info is cross-module |
| `trait_resolution_flows_to_primitive` | Traits + Backend | `ResolvedCall::TraitMethod` for `(+ 1 2)` — backend's `primitive_for_trait_method` maps to `add-i64` inline IR |
| `trait_resolution_user_impl_to_codegen` | Traits + Backend | `ResolvedCall::TraitMethod` for user impl — `primitive_for_trait_method` returns None; backend emits direct call to mangled name |
| `module_import_trait_methods_resolve` | Modules + Traits | Trait declared in module A, impl in module B, call in module C — method resolution follows import chain correctly |
| `module_constrained_fn_cross_module` | Modules + Monomorphisation | Constrained fn defined in module A, called with concrete types in module B — monomorphisation produces specialization |
| `mono_sig_dispatch_cross_module` | Monomorphisation + Modules | SigDispatch resolution for cross-module constrained fn call points to correct mangled name |

---

## REPL Display Non-Conformances

(No new items identified from design doc review.)

## Acceptance Gate

- All module import/export tests pass
- Trait dispatch is deterministic (no hash-order sensitivity)
- Cross-module constrained-poly specializations compile correctly
- All Ring 0-1 tests still pass (regression)
- `/review` approves Ring 2
- RC calling convention tests verify no leaks or double-frees at all three convention boundaries (consuming, borrowing, data constructor)
- Import chain depth limit enforced (no infinite loops)
- Ambiguity detection produces clear errors with qualified alternatives
