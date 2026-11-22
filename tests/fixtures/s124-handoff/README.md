# S124 test handoff at `506ee06e`

- **Owner:** `test`. **Reader:** `qa`, re-judging the coverage bands and the
  delivered cells; `sprint`, sequencing that handoff.
- **Authority:** [evidence delta §14.3](../../plan/s124-evidence-delta.md#143-allocated-to-test)
  and its named filings. This is test-side traceability, not a coverage-band
  restoration, new requirement, product attribution, or release judgment.
- **Source:** clean `main` at `506ee06e`; no compiler, specification, design or
  sprint file changed. Executed test source is committed through `c0c6f4e7`.
- **Retention:** keep this dated handoff until QA has incorporated or explicitly
  dispositioned every row. It is not a second current assurance plan.

## Focused execution

```sh
cargo nextest run --no-fail-fast \
  --test repl_introspection --test spec_07_traits \
  --test spec_09_macros --test spec_10_io \
  -E 'binary(repl_introspection) | binary(spec_07_traits) | binary(spec_09_macros) | binary(spec_10_io)'
```

Final run: **882 executed, 807 PASS, 75 RED, 0 skipped**, 35.167 seconds
post-build (nextest run `1bbb678b-e4e7-4a39-9896-b5a058d5aa6c`).
Each row below reports a test result, not a number of product
root causes. Earlier ranked runs preceded the next batch; no full-suite run
was taken. No test was ignored.

| Binary | PASS | RED | Total |
|---|---:|---:|---:|
| repl_introspection | 206 | 17 | 223 |
| spec_07_traits | 253 | 31 | 284 |
| spec_09_macros | 114 | 6 | 120 |
| spec_10_io | 234 | 21 | 255 |

The allocated cells, including unchanged controls, are mapped below. The other REDs are the
existing `/type`, imported-impl/non-first-self dispatch, applied-Vec,
macro-sibling, prelude-bind and owned-print defect guards. No product fix was
attempted. Build output carries the existing `nix v0.28.0` future-incompatibility
notice.

## Allocated cells and their falsifiers

`GREEN` means the named assertions passed in the completion run. `RED` means
they failed at the named behavioral assertion, not fixture parsing, invocation
usage or a missing platform. For the public-lift cells, the missing `pure`
member **is the allocated product assertion**, not setup for a different
clause. The safety fences observe child exit status without dereferencing
product internals. Signal children return to the harness in milliseconds.

The cell names below are in the linked test binary. Historical names containing
`not_signaled`, `control` or `uses_impl_or_refuses` remain so existing backlinks
continue to resolve; their assertions follow the final ruling, as this map
states.

### Rank 1: T-TYPE-EXPR

[Test source](../../repl_introspection.rs).

| Cell | Leg | Assertion / rejected wrong implementation | Observed |
|---|---|---|---|
| `s124_type_expr_fresh_some_remains_evaluable` | REPL; T-TYPE-EXPR builtin | Exit 0; Some 1 value; final Int 10. Rejects: Query installs uncompiled constructor instance. | RED: signal 11 after the type answer |
| `s124_type_expr_fresh_box_remains_evaluable` | REPL; T-TYPE-EXPR user type | Exit 0; Box.Mk 1 value; final Int 10. Rejects: Fix handles only seeded constructors. | RED: signal 11 after the type answer |
| `s124_type_expr_evaluated_constructor_control` | REPL; both evaluated-first controls | Two value displays per type; exit 0; final 10. Rejects: Constructor generally cannot execute, independently of query ordering. | GREEN: both types display twice and continue |

### Rank 2: T-IO-OPAQUE and narrowed IO cells

[Test source](../../spec_10_io.rs).

| Cell | Leg | Assertion / rejected wrong implementation | Observed |
|---|---|---|---|
| `s124_effect_field_forced_not_signaled_run` | run; Effect forced | Compile diagnostic; nonsignal exit; no runtime panic or usage error. Rejects: Constructible/matchable IO, or a no-signal-only guard. | RED: signal 11 |
| `s124_effect_field_forced_not_signaled_link` | linked executable; Effect forced | Compile diagnostic; nonsignal exit; no runtime panic or usage error. Rejects: Constructible/matchable IO, or a no-signal-only guard. | RED: signal 11 after successful link |
| `s124_effect_field_unforced_not_signaled_run` | run; unforced Effect released | Compile diagnostic; nonsignal exit; no runtime panic or usage error. Rejects: Constructible/matchable IO, or a no-signal-only guard. | RED: signal 11 |
| `s124_effect_field_forced_not_signaled_repl` | REPL; Effect forced | Compile diagnostic; nonsignal exit; no runtime panic or usage error. Rejects: Constructible/matchable IO, or a no-signal-only guard. | RED: signal 11 |
| `s124_effect_field_match_not_signaled_repl` | REPL; test-capture read-line field match | Compile diagnostic; nonsignal exit; no runtime panic or usage error. Rejects: Constructible/matchable IO, or a no-signal-only guard. | RED: signal 7 |
| `s124_io_opaque_pure_constructor_refused_run` | run; Pure constructor | Compile diagnostic; nonsignal exit; no runtime panic or usage error. Rejects: Constructible/matchable IO, or a no-signal-only guard. | RED: accepted; exit 5 |
| `s124_io_match_not_runtime_match_failed_run` | run; constructor-only match on a bind IO value | Compile diagnostic; nonsignal exit; no runtime panic or usage error. Rejects: Constructible/matchable IO, or a no-signal-only guard. | RED: accepted; runtime panic: match failed, exit 1 |
| `s124_io_match_wildcard_control_run` | run; constructor plus wildcard match on a bind IO value | Compile diagnostic; nonsignal exit; no runtime panic or usage error. Rejects: Constructible/matchable IO, or a no-signal-only guard. | RED: accepted; exit 0 |
| `s124_io_match_pure_only_refused_control_run` | run; single Pure-arm match | Compile diagnostic; nonsignal exit; no runtime panic or usage error. Rejects: Constructible/matchable IO, or a no-signal-only guard. | GREEN: refused as non-exhaustive |
| `s124_effect_field_pure_control_run` | run; public pure | 42 as process result (or REPL payload). Rejects: Public lift absent or does not yield its input. | RED: missing primitives/pure member |
| `s124_effect_field_pure_control_link` | link request; public pure | 42 as process result (or REPL payload). Rejects: Public lift absent or does not yield its input. | RED: missing primitives/pure member |
| `s124_effect_field_pure_control_repl` | REPL; public pure | 42 as process result (or REPL payload). Rejects: Public lift absent or does not yield its input. | RED: missing primitives/pure member |
| `s124_io_opaque_pure_info` | REPL /info | (Fn [a] (primitives/IO a)). Rejects: Absent/wrong public lift scheme. | RED: unknown symbol primitives/pure |
| `s124_bind_spelling_outcomes_agree_run` | run; bare/imported, qualified, dotted, value | All four independently have a compile diagnostic and nonsignal status. Rejects: Gate applies only to bare Bind. | RED: bare refused; qualified/dotted/value each accepted, exit 0; collected before assertion |
| `s124_bind_spelling_builtin_control_run` | run; public bind with pure inputs | Exit 42. Rejects: Surface refusal disables public composition or lift is absent. | RED: missing primitives/pure member |
| `s124_io_opaque_refusal_checker_controls` | synthetic checker control | Accept batch/REPL diagnostic; reject signal/value/runtime panic/usage pairs. Rejects: Guard credits panic text or an invocation failure as compile refusal. | GREEN: both accepting and rejecting synthetic legs pass |

### Rank 3: T-TRAIT-SPELLING

[Test source](../../spec_07_traits.rs).

| Cell | Leg | Assertion / rejected wrong implementation | Observed |
|---|---|---|---|
| `s124_trait_spelling_num_direct_uses_impl_or_refuses` | run; T-TRAIT-SPELLING | Exit 2; refusal no longer admitted. Rejects: Spelling-keyed primitive instead of the declared body. | RED: exit 8 |
| `s124_trait_spelling_num_value_uses_impl_or_refuses` | run; T-TRAIT-SPELLING | Exit 2; refusal no longer admitted. Rejects: Correction handles only direct method calls. | RED: exit 8 |
| `s124_trait_spelling_num_constrained_uses_impl_or_refuses` | run; T-TRAIT-SPELLING | Exit 0; refusal no longer admitted. Rejects: Correction leaves constrained dispatch spelling-keyed. | RED: exit 10 |
| `s124_trait_spelling_eq_uses_impl_or_refuses` | run; T-TRAIT-SPELLING | Exit 7; refusal no longer admitted. Rejects: Correction handles Num alone. | RED: exit 9 |
| `s124_trait_spelling_ord_uses_impl_or_refuses` | run; T-TRAIT-SPELLING | Exit 7; refusal no longer admitted. Rejects: Correction handles Num/Eq alone. | RED: exit 9 |
| `s124_trait_spelling_display_uses_impl_or_refuses` | run; T-TRAIT-SPELLING | Exit 2; refusal no longer admitted. Rejects: Display implementation silently replaced by primitive. | RED: exit 5 |
| `s124_trait_spelling_renamed_num_control` | run; unchanged renamed control | Exit 2. Rejects: Fixture cannot run an equivalent user impl at all. | GREEN: exit 2 |
| `s124_trait_spelling_renamed_eq_control` | run; unchanged renamed control | Exit 7. Rejects: Fixture cannot run an equivalent user impl at all. | GREEN: exit 7 |
| `s124_trait_spelling_renamed_display_control` | run; unchanged renamed control | Exit 2. Rejects: Fixture cannot run an equivalent user impl at all. | GREEN: exit 2 |

### Rank 4: T-VEC-FUNCTOR

[Test source](../../spec_07_traits.rs).

| Cell | Leg | Assertion / rejected wrong implementation | Observed |
|---|---|---|---|
| `s124_vec_functor_maps_builtin_vec` | run; T-VEC-FUNCTOR | Third mapped element yields exit 4. Rejects: Vec arity read as zero, or only conventional impl corrected. | RED: Vec has 0 type parameters; trait Functor expects arity 1 |
| `s124_vec_functor_option_control` | run; same trait on Option | Exit 4. Rejects: The higher-kinded trait fixture itself is malformed. | GREEN: exit 4 |
| `s124_vec_functor_helper_control` | run; Vec helper directly | Exit 4. Rejects: Recursive vector helper, indexing or callback fixture broken. | GREEN: exit 4 |

### Rank 5: T-MARKERS

[Test source](../../repl_introspection.rs).

| Cell | Leg | Assertion / rejected wrong implementation | Observed |
|---|---|---|---|
| `s124_markers_closure_display` | REPL; T-MARKERS closure | Typed function value ends in #closure. Rejects: Anonymous function retains retired display marker. | RED: <closure> |
| `s124_markers_nested_io_display` | REPL; T-MARKERS nested IO | Vector value contains [#io]. Rejects: Nested IO falls through to tag formatter. | RED: [<unknown-tag:4>] |
| `s124_markers_input_refused_session_continues` | REPL; one session per token | Parse refusal for #io and #closure; exit 0; next turn 10. Rejects: Markers become accepted source or refusal kills the session. | GREEN: both refused; both next turns print 10 |

### Rank 6: T-SCONCAT-PUBLIC

[Test source](../../spec_09_macros.rs).

| Cell | Leg | Assertion / rejected wrong implementation | Observed |
|---|---|---|---|
| `s124_sconcat_public_no_import_run` | run; T-SCONCAT-PUBLIC | Two one-element SLists concatenate to length 2; exit 2. Rejects: Public sconcat requires library/prelude/import or drops a list. | GREEN: exit 2 |
| `s124_sconcat_public_no_import_link` | linked executable; T-SCONCAT-PUBLIC | Two one-element SLists concatenate to length 2; exit 2. Rejects: Public sconcat requires library/prelude/import or drops a list. | GREEN: exit 2 |
| `s124_sconcat_public_info` | REPL /info; no imports | Two (macros/SList macros/Sexp) args and same result. Rejects: Helper is private or has the wrong public scheme. | GREEN: exact qualified scheme found |

### Rank 7: T-DEFAULT-UNDEFINED

[Test source](../../spec_07_traits.rs).

| Cell | Leg | Assertion / rejected wrong implementation | Observed |
|---|---|---|---|
| `s124_default_undefined_declaration_accepted` | REPL; T-DEFAULT-UNDEFINED declaration | No error, next expression 10. Rejects: Default body eagerly checked at declaration. | GREEN: accepted; next turn 10 |
| `s124_default_undefined_inherited_reports_name` | run; inheriting impl | Exit 1 with error and nosuch. Rejects: Undefined inherited body ignored or reported without its name. | GREEN: diagnostic names nosuch |
| `s124_default_undefined_override_dispatches` | run; overriding impl | Exit 7 from dflt Mk. Rejects: Overriding impl still instantiates the unused default template. | GREEN: exit 7 |

### Fixture changes and limits

- IO subjects use `sleep 0` to build public IO operands and return IO from
  `main` without needing the absent `pure`. Thus acceptance of construction
  or matching stays observable, instead of passing because an unrelated
  `pure` lookup failed. The constructor-only and wildcard subjects match a
  builtin-bind node. The unforced Effect subject returns `sleep 0` after the
  unused node. The obsolete match-with-Pure value control is replaced by the
  public-lift and opacity subjects.
- The single-Pure-arm match remains GREEN on a non-exhaustive diagnostic;
  that satisfies refusal but does not independently prove opacity.
- Bare Bind refusal is GREEN inside the four-spelling cell; its other three
  legs are RED. The aggregate captures all four children before asserting.
- No allocated cell was unconstructible. No replacement compiler API or
  custom process harness was needed. Every new product cell is free-standing;
  the backlink walk below reads existing library-conformance witnesses but
  does not add a library dependency.
- The short Bind allocation remains a module-only residual (ACT-1105); the
  unrecorded trace root (ACT-1110) has no allocated cell. The new tests do not
  claim to observe either. Green guards were not mutation-tested; their
  recorded evidence is their executing assertions and controls, not a claim
  that every plausible fault has been planted.

## Rank 8: backlink clause map

This is a **source walk**, not 108 fresh test executions or QA's final
adequacy decision. Each former citation and relevant test fixture/assertion
was compared with the requirement as written at `506ee06e`. Additional
candidates come from `// spec:` backlinks; a matching anchor alone is not
credited as evidence. A retained assertion is named with its falsifier;
missing clauses and invalid fixture assumptions stay explicit.

`spec_coverage_reconcile.py` reports 115 cleared **rows** at this checkpoint.
Seven predate the 2026-11-22 rewrite (`2fe6d28f^`): §3.10, trace §4.12,
§4.12.3 heading and extern bullet, diagnostic §5.5, and two persistence §15.4
rows. Excluding those leaves the requested **108 rows**. Three binder rows
(25, 27, 29) each contain two bracket markers: the 108-row set therefore
contains 111 markers, all addressed here. The source line in this table is a
checkpoint coordinate, not a promise that future edits preserve line numbers.

The former cells column reproduces identifiers for navigation, **not** a
coverage claim. An em dash means the cleared row had no named test citation;
its judgment names any useful candidates found. Source paths are relative to
the repository root. No `[Tested]` annotation is changed by this map.

| Row | Source at checkpoint | Former cells | Assertion, falsifier and remaining clauses |
|---:|---|---|---|
| 1 | [repl/spec/01-display-format.md:83](../../../repl/spec/01-display-format.md) | — | **Partial.** Scalar envelope cells retain their typed-value assertions; section rollup cannot be restored over the closure marker RED or unevidenced elision uniformity (row 90). |
| 2 | [repl/spec/01-display-format.md:102](../../../repl/spec/01-display-format.md) | `tests/repl_introspection::display_int_result` | **Mismatch / RED replacement.** display_int_result evaluates integer addition only; it cannot observe an anonymous function. s124_markers_closure_display now rejects the retired marker, RED on <closure>; its concrete Int signature does not cover the illustrated polymorphic signature. |
| 3 | [repl/spec/01-display-format.md:103](../../../repl/spec/01-display-format.md) | `tests/repl_introspection::named_function_value_displays_fq_name_not_closure`; `tests/repl_introspection::fq_bare_display_parity_with_imported_introspection` | **Retains with limit.** Named-reference cells require primitives/vec-len or mathx/gcount and reject codegen / <closure>. Their imports are explicit or empty. They do not reject the newly forbidden #closure token; add that negative during the marker migration. |
| 4 | [repl/spec/01-display-format.md:112](../../../repl/spec/01-display-format.md) | `tests/spec_10_io::repl_pure_int_result_prints_io_notice_then_payload`; `tests/spec_10_io::repl_pure_string_result_prints_io_notice_then_payload`; `tests/spec_10_io::repl_bind_pure_lambda_result_prints_io_notice_then_payload_without_double_free`; `tests/spec_10_io::repl_io_notice_precedes_effect_output_neg_not_on_pure_defn_or_lookup_turns`; `tests/output_equivalence::output_equiv_single_print` | **Fixture migration.** Notice/payload ordering and the absent-notice negative still discriminate execution/display order. Three cells construct Pure; migrate those fixtures to pure with ACT-1108. Platform-print notice and batch output equivalence do not depend on that constructor. No new pure coverage from their current green. |
| 5 | [repl/spec/01-display-format.md:136](../../../repl/spec/01-display-format.md) | — | **Partial.** Use the per-kind defn/deftype/deftrait/impl cells in repl_introspection, rather than the zero-arg-defn witness for every kind. defn_display_neg_not_closure checks the retired token only. Canonical-home twins in ps_d1_impl_confirmation_home assert foreign type/trait homes, but currently load the workspace library; they do not prove prelude independence. |
| 6 | [repl/spec/01-display-format.md:216](../../../repl/spec/01-display-format.md) | `tests/repl_introspection::named_function_value_displays_fq_name_not_closure`; `tests/repl_introspection::fq_bare_display_parity_with_imported_introspection` | **Retains with limit.** Same named-reference assertions as row 3. Explicitly imported gcount and qualified vec-len observe canonical names; no proof yet against replacement with #closure. |
| 7 | [repl/spec/01-display-format.md:219](../../../repl/spec/01-display-format.md) | `tests/repl_introspection::display_user_list_value_shows_elements_and_nil`; `tests/display_exact::display_exact_user_list_recursive_form_whole_line` | **Retains.** Both cells define List inline. Exact recursive value/whole-line assertions reject raw pointers, type tokens interleaved with values, or a special built-in-list requirement. PrimitivesOnly supplies scalar names explicitly, not stdlib. |
| 8 | [repl/spec/01-display-format.md:221](../../../repl/spec/01-display-format.md) | `tests/repl_introspection::display_infinite_seq_value_does_not_hang` | **Partial / stale expectation.** Inline Seq and bounded child observe an unforced infinite tail and head 7. The literal <closure> assertion contradicts the new #closure clause; retain termination evidence only until marker migration. No library dependency. |
| 9 | [repl/spec/01-display-format.md:239](../../../repl/spec/01-display-format.md) | `tests/repl_introspection::named_function_value_displays_fq_name_not_closure`; `tests/repl_introspection::fq_bare_display_parity_with_imported_introspection` | **Partial.** The two cited cells observe named-reference and imported/FQ envelopes, not every value reached through computation. Their retired-token negative needs migration; T-MARKERS adds an anonymous-value RED, not a universal envelope proof. |
| 10 | [repl/spec/03-slash-commands.md:337](../../../repl/spec/03-slash-commands.md) | — | **Partial rollup.** The existing target-resolution cells still observe switching/refusal. Rows 11–16 hold environment parity only for the selected test preludes, not arbitrary or empty prelude contents; dotted/lib-directory target limits already recorded in the row remain. |
| 11 | [repl/spec/03-slash-commands.md:364](../../../repl/spec/03-slash-commands.md) | — | **Partial.** devloop_fresh_prelude_using_mod_turn_compiles supplies TestStandard and requires result 7 with no undefined-variable error. It shows provided + remains available, not that no operator is required with an empty prelude. A prelude absence discriminator is absent from these cells. |
| 12 | [repl/spec/03-slash-commands.md:366](../../../repl/spec/03-slash-commands.md) | — | **Partial / fixture mismatch.** devloop_fresh_mod_turn_bare_type_alias_resolves supplies Int through PrimitivesOnly, while m.cl imports nothing. Its 7/no-unknown-type assertions show a prelude alias, not the newly stated own-file import clause. Needs a module-local-import fixture. |
| 13 | [repl/spec/03-slash-commands.md:372](../../../repl/spec/03-slash-commands.md) | — | **Partial.** devloop_cache_restored_prelude_using_mod_turn_compiles preserves the directory and requires result 7 after restart. It rejects loss of + in a restored namespace; it does not assert a cache-hit diagnostic, so also passes if every module is recompiled. |
| 14 | [repl/spec/03-slash-commands.md:376](../../../repl/spec/03-slash-commands.md) | `tests/repl_mod_devloop::devloop_fresh_prelude_using_mod_turn_compiles` | **Retains.** TestStandard is a deliberately supplied prelude. Result 7 plus no undefined-variable diagnostic rejects a fresh /mod environment losing that provided +. The example does not make + mandatory language content. |
| 15 | [repl/spec/03-slash-commands.md:377](../../../repl/spec/03-slash-commands.md) | `tests/repl_mod_devloop::devloop_cache_restored_prelude_using_mod_turn_compiles` | **Retains with cache limit.** The same TestStandard setup and saved directory exercise the restart axis; result 7 rejects loss of the prelude name. No assertion forces the restore mechanism rather than recompilation (row 13). |
| 16 | [repl/spec/03-slash-commands.md:378](../../../repl/spec/03-slash-commands.md) | `tests/repl_mod_devloop::devloop_fresh_mod_turn_bare_type_alias_resolves` | **Mismatch.** The named cell has no Int import in m.cl; the alias comes from its PrimitivesOnly prelude. It does not prove an import written in the file body survives /mod. Do not restore this row from that cell. |
| 17 | [repl/spec/10-terminal-styling.md:26](../../../repl/spec/10-terminal-styling.md) | — | **Partial.** display_exact::source_comment_colour_off_carries_no_sgr_neg and its whole-block twin reject SGR in plain output; callable_and_accessor_coexistence_colour_off_carries_no_sgr_neg covers a second surface. They do not establish the whole R1–R15 role table or the new marker bytes under colour-on. No exact §10.4 backlink. |
| 18 | [repl/spec/10-terminal-styling.md:68](../../../repl/spec/10-terminal-styling.md) | — | **Illustration.** Worked styling example is subordinate to §10.3. No direct test backlink; scalar/no-SGR cells do not validate every illustrated role or the new #closure text. Do not grade the illustration as fully tested. |
| 19 | [repl/spec/11-macro-introspection.md:13](../../../repl/spec/11-macro-introspection.md) | `tests/repl_introspection::expand_user_defmacro` | **Partial.** expand_user_defmacro only looks for add-i64 anywhere in stdout. It neither isolates the /expand response nor checks fixed point, unchanged non-macro form, no evaluation, valid Sexp or state after an expansion error. Its macro is defined inline; no stdlib dependency. |
| 20 | [spec/03-types.md:39](../../../spec/03-types.md) | `crates/cranelisp-typecheck/src/adt/tests.rs::test_resolution_validates_registered_arity` | **Partial / module seam.** `crates/cranelisp-typecheck/src/adt/tests.rs::test_resolution_validates_registered_arity` registers local Option/Color and checks accepted/rejected type arities. It does not observe a seeded primitives/Option, distinct same-spelled local identity, constructor shape or no-prelude qualified use; those new clauses need other evidence. |
| 21 | [spec/03-types.md:216](../../../spec/03-types.md) | — | **Retains with fixture limit.** spec_03_types::returned_rank1_polymorphic_fn_accepted asserts equal written/unwritten schemes; single_poly_instance_used_at_two_types_value_restriction_neg and rank2_argument_applied_at_two_types_neg reject misuse. The result-only-var cells distinguish ambiguity at use from rejection at definition. Test preludes are explicit; batch fixtures still use Pure, so the new pure examples are not covered. |
| 22 | [spec/04-expressions.md:344](../../../spec/04-expressions.md) | `tests/spec_04_expressions::auto_curry_two_param_partial_apply`; `tests/spec_04_expressions::auto_curry_passed_to_higher_order_fn`; `tests/shadowing_scope_lookup::local_closure_auto_curry_non_trait_control_resolves_to_local` | **Partial / stale names.** Existing auto_curry_two_param_partial_apply and auto_curry_three_param_partial_apply require 3/60; auto_curry_passed_to_higher_order_fn requires 15; local_closure_auto_curry_non_trait_control_resolves_to_local requires 0. Negative functions are now auto_curry_too_many_args_error_neg / auto_curry_wrong_type_error_neg, not the old bare names. Constrained examples use TestStandard-defined traits. Result behavior survives the rewrite, but #closure examples and the whole multi-signature restriction are not proven by these former citations. |
| 23 | [spec/04-expressions.md:683](../../../spec/04-expressions.md) | — | **Partial rollup.** No direct §4.11 backlink. Chained application and branch/match cases observe individual results; a pure arithmetic result alone cannot prove all sequencing/deferral clauses. Reconcile by child/form, not the old section-level Tested tag. |
| 24 | [spec/04-expressions.md:708](../../../spec/04-expressions.md) | — | **Partial.** No direct §4.11 backlink to this paragraph. Bind-chain print sequencing (spec_platforms) rejects reversed effects; lenient result parity (spec_12_runtime) allows concurrency. Neither proves physical left-to-right pure evaluation, which is intentionally unobservable. Old Pure fixtures still need migration. |
| 25 | [spec/05-definitions.md:44](../../../spec/05-definitions.md) | — | **Partial / two bands.** stdlib_conformance::stdlib_def_qualified_head_rejected_binder_neg and stdlib_const_qualified_head_rejected_binder_neg assert qualified-head refusal and no silent binding. They load the actual library and do not assert the span at the written macro head or the dotted spelling. Keep binder evidence separate from the unproven written-span band; these are library-route witnesses, not mandatory core macro names. |
| 26 | [spec/05-definitions.md:677](../../../spec/05-definitions.md) | `tests/spec_11_stdlib::macro_const_int`; `tests/spec_11_stdlib::macro_const_string`; `tests/exemplar::batch_const_macro_in_main` | **Library-only / mismatch.** macro_const_int/string are workspace-library conformance and retain their 42/hi assertions for that library only. exemplar::batch_const_macro_in_main defines its own macro size; it does not exercise const at all. No language obligation that const exists; expansion/binder rules need native-form evidence. |
| 27 | [spec/05-definitions.md:700](../../../spec/05-definitions.md) | — | **Partial / two bands.** stdlib_const_qualified_head_rejected_binder_neg observes an error and absence of user/fmt/PI via the library macro. It does not assert dotted-head refusal or the written-head location; no restored claim for either missing clause. Core language does not require this macro. |
| 28 | [spec/05-definitions.md:704](../../../spec/05-definitions.md) | `tests/spec_11_stdlib::macro_def_basic`; `tests/spec_11_stdlib::macro_def_expression` | **Library-only.** macro_def_basic/expression load the workspace library and require 42/3. They still test that library's macro; they do not make def core or establish evaluation-once, visibility or every native expansion rule. |
| 29 | [spec/05-definitions.md:726](../../../spec/05-definitions.md) | — | **Partial / two bands.** stdlib_def_qualified_head_rejected_binder_neg and stdlib_def_bare_head_accepts_twin distinguish qualified refusal from a valid bare binding. Neither asserts a dotted spelling or source-span provenance. Both intentionally depend on the actual library; do not infer an obligatory macro. |
| 30 | [spec/05-definitions.md:806](../../../spec/05-definitions.md) | `tests/spec_05_definitions::private_defn_callable_in_module` | **Partial.** private_defn_callable_in_module requires result 42 for a private helper used locally. It does not reject imports from outside the subtree or exercise all private definition variants. The rewrite labels const/def as illustrative; no coverage for those follows from a defn-only test. |
| 31 | [spec/05-definitions.md:991](../../../spec/05-definitions.md) | — | **Rollup / no direct witness.** No §5.14 test backlink found. Native form tests and library-conformance macro tests must be judged separately; the summary alone is not one independently observed behavior. Do not restore a universal Tested rollup. |
| 32 | [spec/07-traits.md:854](../../../spec/07-traits.md) | `tests/spec_07_traits::user_trait_simple` | **Retains with spelling limit.** user_trait_simple defines Inc and its Int impl inline and requires 15. This proves user trait dispatch without stdlib, but not every spelling: the six T-TRAIT-SPELLING REDs show the same mechanism does not hold for Num/Eq/Ord/Display. |
| 33 | [spec/07-traits.md:989](../../../spec/07-traits.md) | — | **Rollup.** The heading has no prose or direct backlink; its child restrictions retain their own evidence. Do not assign a test to an empty heading or promote it above its least-covered child. |
| 34 | [spec/07-traits.md:1017](../../../spec/07-traits.md) | — | **Library illustration.** No §7.13 test backlink. derive and its helpers are user/library macros, not required language forms. Missing derive-conformance evidence is not a compiler defect; generic macro expansion and trait impl obligations live elsewhere. |
| 35 | [spec/09-macros.md:423](../../../spec/09-macros.md) | `tests/spec_09_macros::macro_emitted_definition_batch_lists_all_definitions_in_order`; `tests/spec_09_macros::macro_expanded_begin_deftype_then_impl_registers_in_source_order`; `tests/spec_09_macros::macro_expanded_begin_impl_neg_before_deftype_is_rejected` | **Retains / partial total.** Three cited inline-macro cells require alpha-before-omega, successful type-before-impl dispatch (41), and an error/no-dispatch for reversed order. They reject reordered/spurious registration without a library dependency. They do not by themselves observe every nested/batch begin rejection or the generated-defmacro publication checkpoint. |
| 36 | [spec/09-macros.md:627](../../../spec/09-macros.md) | `tests/spec_11_stdlib::macro_when_true`; `tests/spec_11_stdlib::macro_cond_first_match`; `tests/spec_11_stdlib::macro_thread_first_single`; `tests/spec_11_stdlib::macro_vec_elements` | **Library-only.** The four spec_11_stdlib cells use the workspace library. Their when/cond/thread/vec values still observe that library's macros, not required names, layouts or expansions. Bare names are supplied deliberately by that prelude; do not restore normative macro-name coverage. |
| 37 | [spec/09-macros.md:942](../../../spec/09-macros.md) | — | **Library-only / partial.** macro_when_true, macro_when_false_none and macro_when_option_body_nests_the_wrap distinguish Some/None and unconditional nesting for actual library when. No unless negative/positive evidence follows from those cells; this subsection is illustrative, not a core obligation. |
| 38 | [spec/10-io.md:15](../../../spec/10-io.md) | `tests/spec_10_io::io_propagates_into_inferred_return_type` | **Partial / fixture migration.** io_propagates_into_inferred_return_type checks the inferred IO signature of a Pure-producing function. It does not call a platform operation or a wrapper of that operation. Keep that narrow inference observation only; migrate Pure before claiming the new public pure surface. |
| 39 | [spec/10-io.md:59](../../../spec/10-io.md) | `tests/spec_10_io::pure_bool_unwraps_inline` | **Mismatch / RED public lift.** pure_bool_unwraps_inline applies Pure, not pure. It cannot cover the rewritten ordinary-function interface, Bool/String/None lift examples or first-class/partial application. T-IO-OPAQUE public-lift cells are RED on the missing name; Bool/etc remain unallocated. |
| 40 | [spec/10-io.md:70](../../../spec/10-io.md) | `tests/spec_10_io::bind_triple_chain` | **Partial / fixture migration.** bind_triple_chain requires 6 from nested primitive binds using an explicit PrimitivesOnly prelude. It observes composition, not non-execution at construction or the entire scheme; its Pure terminators must migrate. A library bind spelling is not assumed by this fixture. |
| 41 | [spec/10-io.md:78](../../../spec/10-io.md) | `tests/spec_10_io::bind_pure_to_pure_plus_one` | **Partial / fixture migration.** bind_pure_to_pure_plus_one requires 43, rejecting a dropped/wrong continuation value. It cannot prove that constructing the bind performs no effect (there is no observable effect). It uses Pure, so public pure remains uncovered. |
| 42 | [spec/10-io.md:98](../../../spec/10-io.md) | `tests/spec_11_stdlib::macro_do_returns_last` | **Library-only.** macro_do_returns_last asserts 3 using the actual workspace macro. It neither makes do mandatory nor proves the compiler recognizes only expanded core bind. This remains library conformance only; Pure fixture migration is carried. |
| 43 | [spec/10-io.md:110](../../../spec/10-io.md) | `tests/spec_platforms::bind_chain_print_sequence_with_pure_terminator_emits_all` | **Partial / native witness.** spec_platforms::bind_chain_print_sequence_with_pure_terminator_emits_all asserts exact one/two stdout and exit 42 with explicit bind imports, without do or bind! or stdlib. It tests the expanded core behavior, not an actual macro's expansion; replace its terminal Pure during the migration. |
| 44 | [spec/10-io.md:128](../../../spec/10-io.md) | — | **Library illustration / no direct witness.** No exact §10.4.2 backlink. The library do cells test selected values, not a universal core form or all IO-only refusal cases. Core sequencing requirements belong to bind and native typing. |
| 45 | [spec/10-io.md:143](../../../spec/10-io.md) | — | **Library illustration / no direct witness.** No exact §10.4.3 backlink. The printed greeting/show examples are not executed by an exact sample test here; the compiler does not owe these library names. |
| 46 | [spec/10-io.md:157](../../../spec/10-io.md) | `tests/spec_11_stdlib::macro_bind_bang_single_binding` | **Library-only.** macro_bind_bang_single_binding requires 42 using workspace bind!. Retains that library observation; no assertion proves an exact expansion or a mandatory bind! form. The native bind acceptance cells are separate. |
| 47 | [spec/10-io.md:172](../../../spec/10-io.md) | — | **Library illustration / no direct witness.** No exact §10.5.1 backlink. No test of the expansion strings follows from a successful library bind! result. New pure in the illustrated expansion is absent in the compiler. |
| 48 | [spec/10-io.md:199](../../../spec/10-io.md) | `tests/spec_11_stdlib::macro_bind_bang_sequential_reference` | **Library-only / partial.** macro_bind_bang_sequential_reference requires 10 when y uses x through actual library sugar. It rejects losing earlier-binding scope, but does not cover all IO-type refusal or evaluation-order clauses; current fixture still uses Pure. |
| 49 | [spec/10-io.md:205](../../../spec/10-io.md) | — | **Library illustration / no direct witness.** No exact §10.5.3 backlink. The distinction between discarded and named results is illustrative sugar over bind; library do/bind! cells cannot establish a required syntax. |
| 50 | [spec/10-io.md:306](../../../spec/10-io.md) | `tests/spec_10_io::io_values_deferred` | **Insufficient former witness.** io_values_deferred defines deferred and immediately calls it, asserting 99. It has no observable side effect and cannot distinguish eager execution from deferral. The rollup's still-pending isolation/comparison children must remain visible. |
| 51 | [spec/10-io.md:314](../../../spec/10-io.md) | `crates/cranelisp-intrinsics/src/io/tests.rs::test_run_io_pure` | **Partial / module seam and migration.** `crates/cranelisp-intrinsics/src/io/tests.rs::test_run_io_pure` constructs an internal node, forces it once and requires 42. It does not observe public pure, effect deferral, bind composition or node reuse. The named reuse cells cover sequential Pure/Effect only and still use constructor fixtures; Launch/EffectPoll/concurrent reuse remain unmeasured as recorded. |
| 52 | [spec/10-io.md:331](../../../spec/10-io.md) | `tests/spec_10_io::run_mode_deep_bind_chain_named_continuation` | **Partial / weak depth.** run_mode_deep_bind_chain_named_continuation requires 8 from nine binds, rejecting a dropped/reordered continuation. Nine frames would also pass a recursive implementation; it does not prove O(1) depth. Current Pure terminals need migration; the deeper intrinsics module witness is separate, not solution-level proof. |
| 53 | [spec/10-io.md:337](../../../spec/10-io.md) | — | **No direct witness.** No §10.8.3 backlink. The specified choose/print two-input discriminator is not in the former covering set; io_values_deferred does not discriminate it (row 50). Return to QA as an effect-isolation gap. |
| 54 | [spec/10-io.md:348](../../../spec/10-io.md) | — | **Mixed summary.** No §10.8.4 backlink. The new user-inspection clause is observed RED by T-IO-OPAQUE; stack/ordering/deferral need their own witnesses. The Haskell column is explanatory comparison, not executable compiler behavior. |
| 55 | [spec/10-io.md:387](../../../spec/10-io.md) | `tests/link::link_repeated_platform_adt_marshal_does_not_corrupt_heap` | **Retains narrow ABI witness.** link_repeated_platform_adt_marshal_does_not_corrupt_heap uses an inline Rectangle, explicit primitives and 200 linked platform calls; exit 0 rejects accumulated heap corruption. It does not establish every ABI layout/signature rule. Its terminal Pure requires migration, not a stdlib dependency. |
| 56 | [spec/10-io.md:405](../../../spec/10-io.md) | — | **No direct witness / module allocation.** No exact §10.10.3 solution backlink. The allocator callback's identity/layout is a module/ABI condition; a surviving marshal loop alone cannot distinguish every wrong allocator callback. Route to QA/dev rather than manufacture a middle-tier test. |
| 57 | [spec/10-io.md:417](../../../spec/10-io.md) | `tests/spec_10_io::resource_serial_same_token_serializes` | **Partial / wrong former summary witness.** resource_serial_same_token_serializes measures exclusion, not the newly stated independence analysis on core binds. auto_io_independent_diff_token_parallelizes_e2e and its dependent/Sequential controls are nearer candidates; timing alone does not prove a composed node when sequential runtime execution is allowed. |
| 58 | [spec/10-io.md:428](../../../spec/10-io.md) | `tests/spec_10_io::auto_io_independent_diff_token_parallelizes_e2e` | **Partial / over-strong timing.** auto_io_independent_diff_token_parallelizes_e2e requires sub-midpoint overlap for explicit primitive bind chains in run/link; dependent and Sequential controls require serialization. They distinguish scheduling outcomes, but mandatory observed overlap is stronger than the rewritten runtime MAY (sequential execution allowed). QA must separate compiler composition evidence from runtime performance. |
| 59 | [spec/10-io.md:435](../../../spec/10-io.md) | — | **Partial / same issue.** Same core-bind fixtures as row 58. Their timing cannot prove composition independently of runtime execution strategy; no unchanged blanket Tested judgment is warranted for the MAY clause. This is a QA classification handoff, not a newly classified product defect. |
| 60 | [spec/10-io.md:464](../../../spec/10-io.md) | `tests/spec_10_io::resource_serial_same_token_serializes` | **Partial.** resource_serial_same_token_serializes asserts a lower elapsed bound in run/link. It rejects overlap on one token but cannot reject serial effects executed in reversed source order. concurrency_capacity::same_token_capacity_1_blocking_serial_and_source_ordered and the poll twin add exact stdout order; all are explicit bind fixtures, with carried Pure migration. |
| 61 | [spec/10-io.md:476](../../../spec/10-io.md) | — | **Partial / timing classification.** Capacity cells cover distinct/shared pools, N+1 parking and capacity-1 source order on blocking and poll carriers. They use explicit imports and core binds. Lower timing bounds observe admission ceilings; upper overlap bounds demand more than the paragraph's permitted sequential execution, so QA must retain those as implementation-performance evidence only. |
| 62 | [spec/10-io.md:486](../../../spec/10-io.md) | — | **Retains ceiling; partial whole row.** same_token_capacity_n_blocking_admits_n_concurrent_nplus1_parks and its poll twin assert lower bounds rejecting all N+1 effects overlapping; their upper bounds demand saturation/overlap, not required by this MAY. No direct observation of each begin instant; wall clock is the declared discriminator. Pure terminals await migration. |
| 63 | [spec/10-io.md:519](../../../spec/10-io.md) | — | **Partial / mechanism-neutrality.** concurrency_cancellation::blocking_par_without_select_waits_for_both_workers_control observes join behavior for the current mechanism. It cannot require rayon/reactor selection. The normative value/order/permit clauses need their dedicated cells; mandatory overlap checks cannot grade the allowed sequential alternative. |
| 64 | [spec/10-io.md:570](../../../spec/10-io.md) | — | **Partial rollup.** launch_and_continue_runs_concurrently_launcher_does_not_await observes an unused-result/disjoint-token bind loop; degree_n_bounds_inflight_launched_effects_nplus1_parks observes throttling. They do not cover all eligibility/cancellation ownership clauses (ACT-0977). Both use Pure terminals awaiting migration; no do spelling is needed. |
| 65 | [spec/10-io.md:585](../../../spec/10-io.md) | — | **Retains current detached witness.** launch_and_continue_runs_concurrently_launcher_does_not_await asserts a positive duration floor (effects ran) and an upper overlap bound (launcher did not await five effects). Its source is a primitive bind loop; result-unused eligibility is explicit. It observes the detached path, not a language requirement to detach every eligible call. |
| 66 | [spec/10-io.md:586](../../../spec/10-io.md) | — | **Partial / constructive eligibility.** The same fanout loop has an unused continuation parameter and returns 0; its value does not use the effect result. This shows a legal discarded-result shape, not an independent dynamic test that no launched result can ever be observed. The rule is conditional on unused-result eligibility. |
| 67 | [spec/10-io.md:587](../../../spec/10-io.md) | `tests/concurrency_fanout::detached_faulting_effect_exits_the_process`; `tests/concurrency_fanout::launch_and_continue_runs_concurrently_launcher_does_not_await` | **Retains panic clause.** detached_faulting_effect_exits_the_process asserts a nonsignal nonzero exit and exactly the permitted panic report; the nonfaulting fanout control requires completion. This rejects recovery/continued launch execution. Explicit primitives, with Pure terminal migration still carried. |
| 68 | [spec/10-io.md:588](../../../spec/10-io.md) | — | **Retains with fixture limit.** degree_n_bounds_inflight_launched_effects_nplus1_parks uses distinct tokens and degree=2, so the lower timing bound rejects unbounded launch admission. Its upper bound also demands overlap of the current implementation. No library sugar; terminal Pure migration remains. |
| 69 | [spec/10-io.md:594](../../../spec/10-io.md) | — | **Partial / surface split.** select and sleep cells exercise language operations; race/timeout cells currently import primitives/race or implement a helper themselves. The new classification requires library derivation, so existing primitive-race greens cannot establish the public library contract. Empty-select and winner/cancellation clauses are separable below. |
| 70 | [spec/10-io.md:619](../../../spec/10-io.md) | — | **Retains value; cancellation partial.** concurrency_cancellation::select_returns_first_completed_value requires FAST as exit status with the fast branch in the middle; wrong source-first/last/index results differ. select_only_winner_value_returned_losers_side_effects_absent_neg adds losing-output absence. No library or Pure construction is needed for those direct select fixtures. |
| 71 | [spec/10-io.md:620](../../../spec/10-io.md) | — | **Retains separated winner.** The same middle-fast select fixture requires FAST and completion before SLOW. It rejects source-order-first selection when the later branch completes first. It does not choose a winner for simultaneously-ready ties, which the spec deliberately leaves unspecified. |
| 72 | [spec/10-io.md:621](../../../spec/10-io.md) | — | **Retains value/index discriminator; example unbuilt.** select_returns_first_completed_value returns FAST milliseconds, distinct from middle index 1. That rejects index-returning implementations. The new tagged-value example using public pure has no covering cell here; do not infer its availability from the result-only witness. |
| 73 | [spec/10-io.md:622](../../../spec/10-io.md) | `tests/concurrency_cancellation::race_loser_completion_side_effect_absent_neg`; `tests/concurrency_cancellation::select_only_winner_value_returned_losers_side_effects_absent_neg`; `tests/concurrency_cancellation::race_loser_releases_resource_permit` | **Partial / core versus library.** select_only_winner_value_returned_losers_side_effects_absent_neg rejects running all select branches to completion. The two race cells exercise primitives/race, now withdrawn from required core surface, so migrate them to select or a local/library derivation before core claims. The cancellation-context contrast remains ACT-0977; losing-output absence alone does not prove all resource releases. |
| 74 | [spec/10-io.md:623](../../../spec/10-io.md) | — | **Library illustration.** timeout_io_completes_before_deadline_returns_result and timeout_io_exceeds_deadline_fires_and_cancels_io_neg use a test-local timeout derivation, not required core syntax. They observe Some/None and losing completion absence for that derivation only; it still uses primitive race and Pure. No new public-library claim is established. |
| 75 | [spec/10-io.md:625](../../../spec/10-io.md) | `tests/concurrency_sleep::sleep_parks_for_duration_then_resumes_and_continues`; `tests/concurrency_sleep::sleep_links_and_runs_through_link_mode` | **Partial.** sleep_parks_for_duration_then_resumes_and_continues asserts a duration floor and exit 7 after the timer; linked twin asserts exit 7 only. Neither reads the sleep payload (continuation ignores it), so the specified result 0 is not proven. A duration lower bound alone would also accept seconds instead of milliseconds; do not claim the unit's negative direction from it. Pure continuation migration remains. |
| 76 | [spec/10-io.md:628](../../../spec/10-io.md) | `tests/concurrency_v9_select::empty_select_heap_typed_fatal_runtime_error`; `tests/concurrency_v9_select::empty_select_heap_typed_not_unit_zero_neg`; `tests/concurrency_v9_select::empty_select_does_not_hang`; `tests/concurrency_v9_select::empty_select_repl_run_parity_no_unsound_null` | **Retains with mode limit.** The four empty-select cells require the message, nonsignal nonzero exit, no fabricated value, bounded completion, and run/REPL termination parity. They use direct select with explicit or qualified primitives. The carried set does not establish the linked leg from these citations alone. |
| 77 | [spec/11-stdlib.md:19](../../../spec/11-stdlib.md) | `tests/spec_04_expressions::trace_returns_trace_type`; `tests/spec_10_io::pure_int_unwraps_inline`; `tests/trace::trace_adt_names_are_importable_from_primitives`; `tests/trace::trace_adt_names_not_auto_imported_neg`; `tests/trace::trace_adt_names_reachable_via_qualified_path_without_import` | **Partial inventory.** trace_returns_trace_type and the Trace import/FQ cells retain selected seeded-Trace observations. The bare-name negative is weak (contains TraceCall suffices), not a decisive unresolved-name assertion. Pure constructor execution cannot prove opaque IO; T-IO-OPAQUE is RED. Newly listed seeded Option/Result/Pair are not inventoried by this former set. Non-normative reference table does not create a second spec authority. |
| 78 | [spec/12-runtime.md:138](../../../spec/12-runtime.md) | — | **Rollup / partial.** Judge strictness, lazy ADTs, lenient scheduling and explicit control separately (rows 79–84). A Tested rollup cannot stand while descendants carry marker/pure migration and unmeasured clauses; no one direct section test. |
| 79 | [spec/12-runtime.md:140](../../../spec/12-runtime.md) | `tests/spec_04_expressions::application_chained` | **Partial / insufficient former witness.** application_chained requires 3 from nested pure inc calls. It does not distinguish eager versus lazy argument evaluation, let order, one-branch-only evaluation or first matching arm. No library dependency, but no complete strictness claim from this cell. |
| 80 | [spec/12-runtime.md:149](../../../spec/12-runtime.md) | — | **Partial.** No exact §12.4.1 paragraph backlink. Bind/print ordering observes effect order, not unobservable scheduling among independent pure operands; lenient value-parity cells are relevant candidates. Neither justifies grading physical evaluation order by result alone. |
| 81 | [spec/12-runtime.md:151](../../../spec/12-runtime.md) | `tests/spec_12_runtime::lazy_stream_take_from_infinite_terminates_with_demanded_element`; `tests/spec_12_runtime::lazy_stream_construction_does_not_force_tail` | **Retains core lazy-ADT behavior.** Both cells declare Stream inline, with explicit primitives, and require 42/37 while constructing an infinite thunked tail. Eagerly forcing the tail times out. This matches user-controlled laziness and requires no built-in Seq; Pure main terminals await migration. |
| 82 | [spec/12-runtime.md:155](../../../spec/12-runtime.md) | `tests/spec_12_runtime::lenient_no_lenient_env_var_preserves_correctness`; `tests/spec_12_runtime::apply_arg_single_expensive_preserves_result_parity`; `tests/spec_12_runtime::apply_arg_panic_exits_run`; `tests/spec_12_runtime::apply_arg_dual_panic_exits_with_one_report`; `tests/concurrency_spark::dependent_spark_dependency_panic_exits_run`; `tests/spec_12_runtime::lenient_binding_panic_not_swallowed_neg`; `tests/trace::trace_records_every_call_of_spark_admitted_callee`; `tests/trace::s124_1038_untraced_sparks_control`; `tests/spec_12_runtime::apply_arg_non_panicking_twins_spawn`; `tests/concurrency_spark::dependent_spark_non_panicking_twin_spawns` | **Retains clauses with gaps.** Panic-exit predicates reject recovery, continuation, signals and duplicate reports; dual-panic accepts either message. Nonpanicking twins assert actual spawns. Trace frame-count plus trace_declines and untraced-spawns distinguish the strict trace exception. Result parity cells alone do not grade heuristic policy. Existing Pure fixtures still need migration; no blanket all-clauses restoration. |
| 83 | [spec/12-runtime.md:157](../../../spec/12-runtime.md) | — | **Partial / changed permission.** Lenient ON/OFF result cells reject result corruption; trace decline/spawn controls observe the exception. Fixed overlap/spawn demand must be judged against the paragraph's allowed sequential implementation, not promoted to universal acceptance. No new language requirement is inferred here. |
| 84 | [spec/12-runtime.md:159](../../../spec/12-runtime.md) | — | **Partial.** apply_arg_single_expensive_preserves_result_parity requires the same result with ON/OFF, but explicitly delegates no-spark emission to another tier. It cannot prove the cost/at-least-two heuristic never spawns. Cheap/mixed let result cells have the same limitation; source-only mapping, no new module claim. |
| 85 | [spec/12-runtime.md:194](../../../spec/12-runtime.md) | `tests/spec_12_runtime::tco_deep_countdown`; `tests/spec_12_runtime::tco_match_tail_position`; `tests/spec_12_runtime::tco_accumulator`; `tests/spec_12_runtime::tco_let_body_tail_position`; `tests/spec_12_runtime::tco_non_tail_recursion_unchanged` | **Retains selected tails / partial total.** Million-depth countdown and 100k match/let tests reject stack growth at those tail sites. Accumulator and non-tail cells only assert values (5050/55), not frame behavior. They do not prove every tail position or macro-expanded tail; Pure/library macro migration is separate. |
| 86 | [spec/12-runtime.md:210](../../../spec/12-runtime.md) | — | **No dedicated depth discriminator.** Fanout's five-launch and four-launch degree loops are too shallow to falsify linear stack growth; ordinary million-depth pure TCO cannot prove launch/trampoline interaction. No exact launch-depth cell located in this backlink walk. Return this clause to QA without equating shallow success to constant space. |
| 87 | [spec/12-runtime.md:307](../../../spec/12-runtime.md) | `tests/platform_errors::platform_dispatch_fault_exits_repl`; `tests/platform_errors::dispatch_fault_during_io_surfaces_run`; `tests/platform_errors::platform_dispatch_error_exits_link`; `tests/platform_errors::platform_dispatch_non_faulting_controls_finish`; `tests/spec_10_io::auto_io_par_branch_panic_exits_neg` | **Retains report clauses / platform-value gap.** platform_errors cells assert one unprefixed FQ-named stderr line, nonzero nonsignal exit and no resumed REPL; nonfaulting twins finish. auto_io_par_branch_panic_exits_neg checks a parallel panic. These reject recovery and wrong report shape; they do not observe expected platform failures returning Option/Result values. The --test leg remains module-only as recorded. |
| 88 | [spec/12-runtime.md:333](../../../spec/12-runtime.md) | — | **No direct witness.** No §12.7.7 backlink. Ordinary Option/Result matching does not prove the absence of panic/error/throw/raise core entries. The example's explicit primitive imports remove a prelude assumption, but do not create executable evidence for the entire negative inventory. |
| 89 | [spec/12-runtime.md:365](../../../spec/12-runtime.md) | `tests/repl_introspection::display_int_result` | **Insufficient former witness.** display_int_result only observes scalar REPL output. It cannot prove trace/REPL formatting equality, independence from a user Display impl, ADT formatting or marker rules. T-MARKERS supplies two narrow REDs, not canonical-format uniformity. |
| 90 | [spec/12-runtime.md:400](../../../spec/12-runtime.md) | `tests/repl_introspection::display_int_result` | **Mismatch.** display_int_result displays 3; it never reaches vector/string/depth thresholds or compares trace output. No uniform elision or unchanged underlying-value assertion follows. Return the SHOULD clauses to QA as unevidenced by this cited cell. |
| 91 | [spec/appendix-a-builtins.md:16](../../../spec/appendix-a-builtins.md) | `tests/spec_04_expressions::vec_literal_int`; `tests/spec_10_io::pure_int_unwraps_inline`; `tests/spec_09_macros::defmacro_identity_expands` | **Partial reference inventory.** vec_literal_int observes a Vec type prefix; defmacro_identity_expands only proves an identity macro result, not every Sexp/SList constructor; pure_int_unwraps_inline uses the retired constructor. These cannot justify the expanded seeded-type inventory or opaque IO. Treat the non-normative reference separately from normative source sections. |
| 92 | [spec/appendix-a-builtins.md:23](../../../spec/appendix-a-builtins.md) | — | **RED opaque IO.** No former cell (S9). T-IO-OPAQUE now observes public lift absence and accepted constructors/matches; it provides RED evidence of the rewritten opaque contract. The bare-Bind and pure-only-match refusals are narrow greens, not total opacity. |
| 93 | [spec/appendix-b-examples.md:15](../../../spec/appendix-b-examples.md) | — | **No backlink / library example.** Hello-world explicitly imports the reference prelude and show. No direct B.1 cell; generic print tests do not execute this exact program. Reference example, not a mandatory compiler-provided show function. |
| 94 | [spec/appendix-b-examples.md:29](../../../spec/appendix-b-examples.md) | — | **No backlink / library example.** Factorial explicitly imports arithmetic/show from the reference prelude. No direct B.2 cell; unrelated recursion tests cannot establish this exact sample's output under its imports. |
| 95 | [spec/appendix-b-examples.md:48](../../../spec/appendix-b-examples.md) | — | **No backlink / library example.** Inline ADTs and Display impls depend on explicitly imported library Display/do/show. No direct B.3 witness for the combined output; trait and ADT unit results elsewhere are narrower. |
| 96 | [spec/appendix-b-examples.md:121](../../../spec/appendix-b-examples.md) | — | **No backlink / fixture blocked.** The sample uses library bind! and new public pure. No direct B.4 cell; pure is absent (ACT-1108), so the rewritten sample cannot currently be accepted by a conforming-output guard without that product work. |
| 97 | [spec/appendix-b-examples.md:148](../../../spec/appendix-b-examples.md) | — | **No backlink / library example.** The Seq collection functions come from the explicit reference prelude. No direct B.5 witness; inline Stream tests prove the core thunk mechanism, not these library transformations or this full transcript. |
| 98 | [spec/appendix-b-examples.md:188](../../../spec/appendix-b-examples.md) | — | **No backlink / library example.** The example explicitly imports macros data and core.syntax/slist. No direct B.6 witness for 42/Some99/30 together; no implicit requirement for slist or when is inferred from generic macro tests. |
| 99 | [spec/appendix-b-examples.md:216](../../../spec/appendix-b-examples.md) | — | **No backlink / library example.** Higher-order code uses explicit prelude arithmetic and do/show. No direct B.7 witness; individual closure/curry tests do not execute its combined sample or establish a mandatory library layout. |
| 100 | [spec/appendix-b-examples.md:243](../../../spec/appendix-b-examples.md) | — | **No backlink / library example.** Threading macros and collection helpers are explicit reference imports. No direct B.8 cell; spec_11_stdlib threading cells are library-specific and do not validate this exact pipeline. |
| 101 | [spec/appendix-b-examples.md:265](../../../spec/appendix-b-examples.md) | — | **No backlink / library example.** The sample's map over Vec/List/Seq relies on the reference library. No direct B.9 cell; native multi-signature tests do not prove its container helpers or output. |
| 102 | [spec/appendix-b-examples.md:295](../../../spec/appendix-b-examples.md) | — | **No backlink / library example.** Num/show are supplied by the reference prelude. No direct B.10 cell; constrained core tests observe selected dispatch results, not this combined reference output or every trait spelling (ACT-1103). |
| 103 | [spec/appendix-b-examples.md:325](../../../spec/appendix-b-examples.md) | — | **No backlink / library example.** Three prints are sequenced by explicitly imported library do. No direct B.11 cell; exact native-bind print tests are candidates for the expansion mechanism only, not execution of the authored macro sample. |
| 104 | [spec/appendix-b-examples.md:347](../../../spec/appendix-b-examples.md) | — | **No backlink / fixture blocked.** The conditional uses new pure for its non-effect branch. No direct B.12 witness; Pure-based branch-unification cells cannot prove the rewritten interface, absent under ACT-1108. |
| 105 | [spec/appendix-b-examples.md:373](../../../spec/appendix-b-examples.md) | — | **No backlink / fixture blocked.** The combined do/bind!/read-line sample imports the reference library and ends with new pure. No direct B.13 cell or exact stdin/transcript witness; public pure absence is a product blocker, not a test setup completion. |
| 106 | [spec/appendix-c-nfr.md:132](../../../spec/appendix-c-nfr.md) | — | **Partial / architectural clauses.** Core-bind scheduling timing witnesses and select cancellation/output witnesses map to the behavioral parts of §10.12. The same-token order cells distinguish exclusion from order. No one cell proves emitted-node insertion or all detached cancellation contexts; ACT-0977 remains. Underlying infrastructure guarantees need module/arch evidence, not a new internal-session integration tier. |
| 107 | [spec/appendix-c-nfr.md:182](../../../spec/appendix-c-nfr.md) | — | **Architectural / no solution cell.** No C.4.4 backlink. Registerable opaque Chan, reusable pool and dispatch extensibility are future architecture constraints; current IO tests cannot prove that new channels need no core-dispatch change. Route to arch/QA, not a fabricated language test. |
| 108 | [spec/index.md:33](../../../spec/index.md) | — | **Editorial / no runtime cell.** Notation defines EBNF, requirement levels and explicit example scope, not one runtime behavior. No direct notation backlink. Tests with chosen preludes show only their fixtures; they cannot establish that no prelude is assumed throughout the prose. QA/spec must judge this editorial summary separately. |

## Structural checks

- `git diff --check`: PASS.
- `spec_link_check.py`: 3,858 citations scanned, 3,845 checked, 13 free-form
  notes skipped, zero mis-cited or malformed.
- `spec_coverage_reconcile.py`: zero dead citations and zero missing function
  names; RED because 115 cleared rows still await QA judgment, including this
  handoff's 108 rows. That is not a product-test result.
- Shared document checker: RED, 576 unsuppressed findings. One is this new
  record's missing machine declaration; the other 575 concern other document
  locations, including unchanged guidance in the tests memory. No new broken
  source path or ambiguous shorthand remains in this record.

## Handoff

**Coordinator metadata dependency:** the root project declaration is owned by
`sprint`, outside this dispatch's edit authority. The record is linked from
`tests/AGENTS.md`, but the document checker also requires its registration in
`standing-documents.toml`. The coordinator can add this exact entry:

```toml
[[document]]
path = "tests/fixtures/s124-handoff/README.md"
kind = "standing"
owner = "test"
purpose = "Dated S124 test-side clause map and focused execution evidence for QA re-judgment."
established_by = "tests/AGENTS.md"
```

This registration is an unresolved synchronous handoff, not an accepted
checker baseline or a request to repair unrelated document findings.


Invoke `qa` next to judge the delivered clause map, restore or explicitly carry
each cleared band, and allocate any remaining missing clauses. The source walk
identifies fixture and coverage limits; it does not authorize new product work.
The coordinator retains responsibility for phase progression and the user's
carried compiler migrations.

Commits before this traceability record:
`2929d74f` (rank 1), `0cfe3a00` (rank 2), `ca8f88b9` (rank 3),
`8bd6b51c` (rank 4), `d4e12848` (rank 5), `929975de` (rank 6),
`ace94858` (rank 7), `c0c6f4e7` (final checker/backlink and local formatting).
