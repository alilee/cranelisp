# Sprint 117 QA plan — conformance, recovery, and production ownership witnesses

> **Retained dated record (S122 consolidation).** Three parts remain, with their
> original numbering: §3, because [ACT-0958](../../sprints/actions/ACT-0958-rearm-failed-turn-recovery-coverage.md)
> cites §3.3; §6, because the [risk register](risks.md) cites the S115 backfill;
> and §5, an S117 allocation of module matrices to `dev` whose delivery this
> consolidation did not verify — compare it with the current module tests before
> treating any row as owed or as done. Nothing here is current status. The exit
> verdict, R-2/0859 witness record, gate reconciliations and forward-flow notes
> are recoverable with `git show 48d6e713:tests/plan/s117-test-plan.md`; the 0859
> disposition is current in [PLAN](PLAN.md#active-allocation-and-unresolved-evidence),
> and filings 0800 and 0863 carry their own subjects.
## 3. Sprint-wide failing-first e2e set

Every test below is authored by `/testing`, remains failing-not-ignored until
fixed, carries its spec citation, and carries one `// defect:` line.

### 3.1 Trait reference versus declaration binder

| ID | Proposed test | Required assertion |
|---|---|---|
| QT-1 | `qualified_impl_trait_reference_resolves_canonical_home_and_dispatches` | Define/import a foreign trait method, do not import the trait name, implement using `mod/Trait`, and dispatch successfully. Echo names the trait's true home. Exercise REPL and a file twin through Run/Link. |
| QT-2 | `qualified_impl_trait_reference_neg_does_not_mint_written_qualifier_into_method_name` | No missing-entry/codegen error may mention a writer-home trait key; `/info <Trait>` and dispatch agree on the one canonical pair. |
| QT-3 | existing `deftrait_qualified_{bare,parenthesized}_head_rejected_binder_neg` | Preserve as controls. A fix for QT-1 must not accept qualified declaration heads. No new test is needed unless `/testing` finds a missing macro-expanded binder variant. |

QT-1/QT-2 are failing-first ready against the scribed `trait_ref` rule.
QT-3 preserves the distinct `trait_binder` rule.

The ruling correctly invalidated, and `/qa` leaves unrestored pending evidence,
the S117 bands at:

- grammar §2.2.3 and §2.2.4;
- definitions §5.4, §5.4.4, and §5.11.1's method-import edge;
- traits §7.3 (including its resolvable-reference paragraph), §7.3.4,
  §7.3.5 Case 3, and §7.11.2's method-import edge.

QT-1/QT-2 supply the new conventional-reference evidence, but the broader HKT
and method-import bands require their cited matrices to be re-evaluated after
the fix. No band is restored during Phase 3.

### 3.2 Macro publication and staging

| ID | Proposed test | Required assertion |
|---|---|---|
| DF-1 | `def_definition_echo_names_user_binding_not_internal_thunk` | `(def n 42)` confirms `user/n` with value type `Int`; no `n-def` appears. |
| DF-2 | `def_info_and_sig_describe_bound_value_not_macro` | `/info n`, `/sig n`, and bare `n` agree; neither introspection route says `defmacro` or `Sexp`. |
| DF-3 | name reserved after `/stdlib` design | `/stdlib` decides whether its zero-arg macro API offers a callable function-valued binding, another explicit operation, or a deliberate rejection. After that choice, `/qa` specifies the behavioral test and `/repl` ensures presentation/diagnostics describe the stdlib API truthfully rather than pretending `def` is a core special form. |
| MB-1 | `macro_expanded_begin_deftype_then_impl_registers_in_source_order` | A macro returning `(begin (deftype T …) (impl Trait T …))` dispatches in the same turn. Use a minimal hand-authored macro, not workspace stdlib. |
| MB-2 | `macro_expanded_begin_impl_neg_before_deftype_is_rejected` | Reversed source order does not gain forward visibility accidentally. |
| MB-3 | `expanded_and_literal_begin_registration_are_twins` | REPL literal-begin control and macro-expanded form have identical registration result; Run/Link file forms use a macro output (top-level literal `begin` is forbidden in batch). |
| MB-4 | `expanded_begin_trait_family_registration_is_uniform` | Small trait matrix `{user conventional trait with required method, trait with default sibling}` × `{same expansion, pre-defined type}`. Do not use stdlib `Display`/`Eq` implementations as separate mechanism proxies. |

0800 and 0816 remain separate families. They may collapse only after a
reduction demonstrates the same failed registrar or transaction invariant.

### 3.3 Failed-turn transaction and diagnostics

| ID | Proposed test | Required assertion |
|---|---|---|
| TX-1 | `failed_codegen_turn_does_not_poison_following_literal` | In one REPL subprocess, trigger a genuine codegen failure, then evaluate `42`; the later turn returns `:primitives/Int 42` and does not repeat the prior error/span. |
| TX-2 | `failed_codegen_turn_does_not_poison_following_definition_and_call` | After the failure, define and call an unrelated function successfully; this proves registration, typecheck, batch derivation, GOT publication, and evaluation all recover. |
| TX-3 | `failed_codegen_turn_does_not_publish_partial_definition` | The symbol whose compile failed is not callable as stale/partial code and does not contaminate `/info`; a clean redefinition of that same symbol can subsequently compile and run. |
| TX-4 | `failed_codegen_diagnostic_names_actual_failing_unit_not_operator_slash` | The first diagnostic names the actual failing definition or source/module context; it must not say `codegen failed for /` unless `/` is the unit being compiled. |

These are REPL-only because they test sequential turns, but they must use
`CompilerSession`'s v4 path via the public binary. No internal session helper
or REPL-only compiler path is admissible. The trigger may initially use 0488,
but the assertion must be trigger-independent so it survives that defect's
eventual fix.

### 3.4 Display and introspection

| ID | Proposed test | Required assertion |
|---|---|---|
| TD-1 | `constraint_trait_name_displays_canonical_home_neg_no_bare_trait` | Prelude trait (`num.num/Num`) and same-named user/imported trait controls show FQ constraint names; stripping qualified tokens leaves no bare trait in constraint position. |
| TD-2 | `constraint_display_is_identical_across_definition_sig_and_bare_lookup` | Definition echo, `/sig`, and bare lookup use one canonical type renderer. |
| IN-1 | `info_type_lists_each_implemented_trait_once` | `/info Box` lists `Display` after one impl and still exactly once after a re-impl. |
| IN-2 | `info_trait_and_type_impl_views_are_inverse_twins` | The same pair appears once from `/info Trait` and once from `/info Type`; unrelated traits/types are absent. |
| IN-3 | `info_type_impls_include_local_and_imported_traits_in_canonical_order` | Preserve §4.1's local-first/imported ordering and unqualified related-symbol names. |

TD-1 replaces the false constrained-variable coverage claim currently attached
to `display_neg_type_always_qualified`; that old test remains valid for
primitive/function concrete type qualification.

## 5. Required future `/dev` unit matrices

- **`/dev(typecheck)`**: trait reference resolution
  `{bare imported, FQ same trait, FQ same-spelled foreign trait, nonexistent
  module}` × `{method mint, default synthesis, re-impl forced enrollment}`.
  Declaration-binder parsing is a separate frontend negative matrix.
- **`/dev(frontend/int)`**: macro-expanded top-level sequence
  `{deftype, deftrait, defn, defmacro}` × `{followed by dependent impl/call,
  reversed negative}` through the shared Pass-2/3 registrar. No macro-only
  registration path.
- **`/dev(src)`**: v4 transaction state
  `{typecheck fail, codegen fail, publish fail}` ×
  `{batch membership, symbol publication, GOT/introspection publication,
  next-turn retry}`. Failure rolls back only the failed turn; prior committed
  definitions survive. Failing-unit attribution uses the batch symbol, never
  an incidental expression head.
- **`/dev(src)`**: `/info` inverse-index enumeration
  `{local/imported trait}` × `{first impl, re-impl, rejected re-impl}` with
  exact pair deduplication and ordering.
- **`/dev(types/int)`**: type-render variants
  `{primitive, ADT, Fn, bare var, constrained var}` ×
  `{definition echo, bare lookup, /sig, /info}` × `{local, imported,
  same-spelled foreign}`; every named type/trait renders its canonical home.
- **`/dev(primitives+typecheck+backend)`**: the R-2 class ×
  source-shape × result-use matrices in §4. MayAlias uses the verified
  producer-side `Fresh`/non-`Fresh` merged-return seam. Typecheck transfer
  units distinguish `ProjectionOf` from `Fresh` and `AliasOf` argument origin,
  and `MayAliasOf` conditional COW-link/escape provenance from unconditional
  aliasing where production RC legitimately collapses. Mutation records use
  declaration-only changes and retain direct inline CLIF as body guards.
  Projection's missing declaration-sensitive production artifact remains
  tracked by FIXME 0859 rather than being inferred from emission-inert shapes.

## 6. Historical S115 coverage audit (0804)

The audit confirms that the S115 normative edits listed by 0804 were not
systematically invalidated. Current `[S115]` tags are delivery markers, not
coverage evidence, and several broad `[Tested]` headings predate the changed
meaning.

QA reconciliation completed 2026-07-25:

1. **Restored — trait occurrence and one-tail/default semantics.** §7.1.1 is
   now `[Tested+Neg]` against the non-nullary `Convertible` rejection, nullary
   no-occurrence rejection, self-return control, and bare-parameter control.
   §7.1.5 is `[Tested+Neg]` against inferred and annotated one-tail defaults,
   deleted legacy spelling, and replacement-default dispatch. The broad §7.1
   heading remains `[Uncovered S115 — was Tested]`: the type/value-collision
   “type wins” case and all per-impl constraint variants do not have a focused
   covering matrix.
2. **Left uncovered — method-level-only and marker boundaries.** §7.3.6's
   conventional-trait method-level-variable ruling and §7.1.1's zero-method
   marker-trait rejection have no focused behavioral evidence. Each now uses
   `[Uncovered S115 — was no prior coverage]`.
3. **Partially restored — dotted binders.** The executed dotted-binder matrix
   supports §4.3 let binders and §6.2.4 variable patterns. The broad §5 heading
   remains `[Uncovered S115 — was Tested]` because the 18-row table includes
   unverified macro-expanded and alias/platform rows. §4.5.2 remains
   `[Uncovered S115 — was tests/spec_03_types::annotated_params_int]`: that
   former test covers annotation semantics, not dotted `fn` parameter
   rejection. Newer S117 trait/impl markers were not changed.
4. **Restored — impl hot reload.** §5.4.5 is `[Tested+Neg]` against the four
   permanent `impl_redefinition_dispatch` cells: repeated replacement,
   override/default cycles, omitted-method fallback, and rejected replacement
   preserving the prior impl.
5. **Restored — constructor definition and pattern forms.** §2.2.2,
   §5.2/§5.2.1/§5.2.2/§5.2.5/§5.2.7, and §6.2.1/§6.2.2 now cite the executed
   positive/negative S116 constructor matrix. §4.2.1 remains
   `[Uncovered S115 — was
   tests/spec_04_expressions::data_constructor_undefined_error_names_constructor_strict]`
   because the former test does not cover the changed value-position `(Ctor)`
   non-application ruling.
6. **Partially restored — read-time annotation fold.** §1.8, §2.3.8, §3.9,
   §9.2, and §9.4 now cite the executed reader, macro-argument, and
   quote/quasiquote structural matrices. §1.4.5 remains
   `[Uncovered S115 — was ...]`: the focused cold/warm cache carrier test is
   still a known failing-not-ignored defect (`selected baseline macro
   dependency ... is not executable`). §9.1 remains uncovered because module
   existence does not prove the exact `SexpAnnotated` marshalling halves.

Evidence run: 67/67 across the annotation-macro, dotted-binder, trait-tail,
constructor-form, and impl-redefinition binaries; 8/8 focused frontend
reader/quasiquote units; and 8/9 across nondispatchable-trait plus structural
annotation binaries, with the sole RED the known cache-carrier defect above.
No newer `[Uncovered S117 — was ...]` provenance was overwritten.
