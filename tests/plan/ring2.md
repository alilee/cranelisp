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

## REPL Display Non-Conformances

<!-- FIXME(/qa): R2.1 — deftrait display shows `:Bool false` instead of `:user/Sizeable`.
     Spec §1.3 requires trait declaration to display the trait name. The deftrait form appears
     to evaluate to a boolean rather than producing a trait-name display. This is a codegen or
     REPL response-formatting bug, not just a display issue. Source: /repl sprint 6 audit. Severity: important. -->

<!-- FIXME(/qa): R2.2 — Constrained function type display omits trait constraints.
     `(defn double [x] (+ x x))` shows `:(Fn [a] a)` but spec §1.4 requires
     `:(Fn [:core.numerics/Num a] a)`. Constraints from Scheme.constraints are not rendered
     in the type display. Same issue for clamp/Ord. Source: /repl sprint 6 audit. Severity: important. -->

<!-- FIXME(/qa): R2.3 — impl display not verified.
     Spec §1.3 requires `impl user/Sizeable for user/Circle` format. No demo exercises impl
     display. Need E2E test coverage. Source: /repl sprint 6 audit. Severity: suggestion. -->

## Acceptance Gate

- All module import/export tests pass
- Trait dispatch is deterministic (no hash-order sensitivity)
- Cross-module constrained-poly specializations compile correctly
- All Ring 0–1 tests still pass (regression)
- `/review` approves Ring 2
