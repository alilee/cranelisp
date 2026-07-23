# Sprint 116 baseline reconciliation

Date: 2026-07-23  
Authority: `/qa`  
Sprint-start commit: `aefe7e11`  
Current checkpoint: `e10ee657`

## Method

The sprint-start commit was exported with `git archive` into an isolated `/tmp`
directory. It was not checked out into the shared worktree. Both the export and
current HEAD were run serially with:

```text
cargo nextest run --no-fail-fast
```

Failure names were extracted from the complete nextest logs, sorted, and
compared as sets. This reconstruction is environment-specific: it answers
which named tests changed polarity under the current host, not whether the
S115 close report was accurate on its original host.

## Observations

| Run | Tests | Passed | Failed | Skipped |
|---|---:|---:|---:|---:|
| `aefe7e11`, first reconstruction | 5412 | 5272 | 140 | 1 |
| `aefe7e11`, captured comparison run | 5412 | 5274 | 138 | 1 |
| `f606ce4c`, first full run | 5460 | 5220 | 240 | 1 |
| `f606ce4c`, captured comparison run | 5460 | 5218 | 242 | 1 |

The two-run spread proves that raw totals contain a small flapping component.
The historical result also does not reproduce the S115 close count of 29 REDs:
platform tests cascade from unresolved `runtime/panic` in generated dynamic
libraries, and the same three reactor unit tests hit their 30-second one-shot
backstop at both commits. These environment-dependent failures must be tracked
separately from deterministic compiler regressions.

The captured name-set comparison is:

- 119 failures present at HEAD but absent at the sprint-start commit;
- 15 failures present at the sprint-start commit but absent at HEAD;
- 123 failures common to both captured runs.

The 15 fixed tests are exactly the intended constructor-form and trait-tail
negative gates: eight constructor-form rulings, four duplicate-name rejects,
and three deleted/extra trait-method spelling rejects.

## HEAD-only clusters

The 119 HEAD-only failures are not independent defects. Their concentration is
strong evidence for a small number of shared regressions:

| Cluster | HEAD-only names | Initial attribution |
|---|---:|---|
| `spec_09_macros` | 29 | `src/` macro definition/compile/expansion path |
| S99 fixtures | 13 | likely downstream of macro/prelude availability; confirm after macro repair |
| `spec_07_traits` | 9 | frontend/typecheck one-tail classification and reader-fold interaction |
| S76 macro availability | 8 | same macro compilation/availability seam |
| REPL introspection | 7 | mostly downstream macro/type registration state |
| `spec_05_definitions` | 5 | macro definition plus one constructor regression |
| macro interior-alias guards | 5 | in-scope safety REDs; distinguish mechanism from macro-unavailable cascade |
| local macro shadowing | 4 | `src/expander.rs` binder scope regression |
| remaining named groups | 39 | classify only after the two dominant roots are repaired |

Three root-crate unit failures directly expose migration gaps and should be the
first controls for the macro/annotation cluster:

- `expander::tests::defn_param_shadows_zero_arg_macro`;
- `session_v4::lifecycle::degraded_startup_tests::defined_symbol_of_form_defining_heads_yield_symbol`;
- `worker::tests::leading_annotation_len_counts_annotation_sexps`.

The backend unit failure
`constructor_as_value_falls_through_to_fn_as_value` is isolated from those
clusters and remains separately attributable to backend.

## QA gate

Do not resume unrelated Sprint 116 implementation until the deterministic
HEAD-only set has been reduced at the two dominant seams. Work serially:

1. `/dev(src)` repairs macro/annotation expansion and availability, using the
   three root unit failures as controls; focused unit/e2e run, then full suite.
2. `/review(src)` checks the repair against the int design and confirms no
   parallel macro path.
3. `/dev(frontend)` then `/dev(typecheck)` address only trait-tail failures that
   remain after step 1, each with focused controls and review.
4. `/dev(backend)` handles the isolated constructor-as-value unit regression.
5. `/qa` repeats this name-set comparison and reclassifies the residual before
   the original Track A/Track C waves resume.

The acceptance condition for this recovery wave is name-level parity with the
sprint-start deterministic set, except for explicitly planned S116 REDs that
have flipped green. A lower scalar failure count alone is insufficient.

## Post-repair reconciliation

The full workspace run at `e10ee657` executed 5,460 tests: 5,300 passed, 160
failed, and one was skipped. Name-set comparison against the captured
sprint-start run gives:

- 40 failures present now but absent from the captured sprint-start run;
- 18 failures present in the captured sprint-start run but absent now;
- 82 of the 242 failures at `f606ce4c` have been removed.

The scalar difference is therefore +22, but the 40 current-only names are the
correct review set: the 18 opposite-polarity names show why subtracting totals
would conceal test identity and environmental flapping.

### QA-approved fixture migrations

The following current-only failures stop at syntax that was valid before the
settled S115/S116 rulings. They do not reach the behavior their assertions are
intended to test. QA approves only the listed source-fixture substitutions; the
test names, assertions, expected values, polarity, and `// spec:` behavioral
traces MUST remain unchanged.

| Test(s) | Fixture-only substitution | Normative basis | Preserved oracle |
|---|---|---|---|
| `spec_05_definitions::deftype_sum_bracketed_field_still_constructs` | Give the `R` arm a field binder distinct from the `L` arm's `n` | `spec/05-definitions.md` §5.2.2: field binders are pairwise unique within one type | `L` remains a unary constructor and `(L 5)` remains `Rotation.L 5` |
| `spec_12_runtime::{lazy_stream_construction_does_not_force_tail,lazy_stream_take_from_infinite_terminates_with_demanded_element}` | Spell the nullary constructor and its patterns as bare `SNil`, not `(SNil)` | `spec/05-definitions.md` §5.2.2 and `spec/06-pattern-matching.md` §6.2.1–2: no position parenthesizes a nullary constructor | Construction remains non-strict; demanded exits remain 37 and 42 |
| `spec_07_traits::{default_method_used_when_not_overridden,default_method_overridden_by_impl,default_method_used_on_adt_impl,default_method_with_primitive_only_body,default_method_body_resolves_in_trait_defining_module}` | Remove the deleted return-type slot before each default body | `spec/07-traits.md` §7.1 and §7.1.5: exactly one trailing element; a non-type expression is the inferred default body | Default synthesis, override, ADT dispatch, primitive body, and defining-module resolution assertions remain unchanged |

These migrations are not compiler fixes and MUST NOT be reported as evidence
that the behaviors themselves were repaired. If a migrated test remains RED,
its resulting diagnostic is the attributable implementation defect.

The remaining current-only names are not approved for test edits by this
entry. In particular, the S116 trait-tail tests already use the normative
spelling and expose a real default-synthesis/conformance defect; their tests
must not be weakened.

### QA-approved residual syntax migrations

After the default-method implementation checkpoint (`0aad5bca`), the complete
workspace gate executed 5,461 tests: 5,311 passed, 150 failed, and one was
skipped. The current-only set fell from 40 to 32 names; 20 captured-baseline
REDs are now absent. The following second fixture batch is approved before any
test source changes:

| Test/fixture set | Fixture or diagnostic substitution | Normative basis | Preserved oracle |
|---|---|---|---|
| S99 `f1_machinery.cl` through `f4_sudoku.cl`; S105 `F3_SHARED_READ`; runtime `conj_wrapper_multivariant_cell_vec_built_correctly_run` | Give `Given`, `Solved`, and `Candidates` distinct field binders within `Cell` | `spec/05-definitions.md` §5.2.2: field binders are pairwise unique within one type | All reads remain positional pattern destructures; parallel/serial, RC-stat, and exit assertions are unchanged |
| S99 F8 fixtures and S105 `F8_SERIAL`/`F8_PARALLEL` | Give `B` field binders names distinct from `A` within `P` | `spec/05-definitions.md` §5.2.2 | Constructor values and positional pattern bindings are unchanged |
| `spec_07_traits::impl_missing_required_method_neg`; both `impl_redefinition_dispatch` tests | Remove the deleted return-type slot preceding each default body | `spec/07-traits.md` §7.1 and §7.1.5 | Missing-required rejection and re-impl dispatch values remain unchanged |
| `bd_a_annotation_ascription::{trait_default_method_body_ascription_accepted,trait_default_method_body_bare_twin}` | Write the annotated one-tail body as `:Int x`; write its bare twin as `x` | `spec/07-traits.md` §7.1 and `spec/01-lexical.md` §1.4.5 | Acceptance/exit assertions remain unchanged; the pair again differs only by annotation |
| `spec_07_traits::{deftrait_bare_return_convar_never_applied_rejected_neg,never_applied_head_declaration_reject_is_mode_uniform_neg}` | Replace the illegal trailing annotation introducer `:a` with bare return type `a` | `spec/07-traits.md` §7.1.1: required return types are bare, while §7.2.1 rejects the never-applied constructor variable | The declaration-time never-applied rejection and its mode parity remain the asserted behavior |
| `spec_07_traits::deftrait_method_nameless_annotation_param_rejected_neg` | Expect the reader's located `annotation missing expression` diagnostic for `[:a]` | `spec/01-lexical.md` §1.4.5: an annotation introducer must bind the following form before the closing delimiter | Still a negative test: the malformed declaration must reject and must not register the trait |

The HKT unknown-uppercase-tail tests are deliberately excluded. Under
`spec/07-traits.md` §7.1's resolution-based discriminator, an unknown name does
not resolve as a type and therefore reads as a default body; HKT defaults are
separately forbidden. Their desired `unknown type` diagnostic is a normative
question, not an approved fixture migration.

### Post-migration name reconciliation

At checkpoint `11bd5153`, the complete workspace gate executed 5,461 tests:
5,335 passed, 126 failed, and one was skipped. Against the captured
sprint-start run, eight failures are current-only and 20 captured-baseline
failures are now absent. The following current-only fixtures stop before the
behavior under test at syntax settled by the user; QA approves only these
substitutions:

| Test(s) | Fixture-only substitution | Normative basis | Preserved oracle |
|---|---|---|---|
| `repl_introspection::{nullary_constructor_bare_lookup_shows_deftype_and_qualified_home,ls1_bare_lookup_of_type_invariant_to_session_history,ls1_bare_type_display_invariant_to_session_history}` | Spell the nullary constructor declarations as bare `Red`, `Green`, `Dark`, and `Light` | `spec/05-definitions.md` §5.2.2: bare names are the only content-free nullary-constructor spelling | Qualified constructor display and session-history-invariant type lookup assertions remain unchanged |
| `ownership_reuse::r5_soundness_couple_unflattened_two_ctor_not_copy_moded` | Give the `Solved` arm a field binder distinct from `Given`'s `value` | `spec/05-definitions.md` §5.2.2: field binders are pairwise unique within one type | Both constructors remain unary; positional matching, sustained value result, and heap-balance assertions remain unchanged |

The other four current-only failures are not approved for test edits:

- the two HKT unknown-name tests still require a normative ruling;
- `clif_golden_lane_no_drift` requires emission-drift attribution before any
  golden recapture;
- `exemplar::t_s2_1_eliminate_contract_on_given_returns_none` is downstream of
  workspace-stdlib compilation on this host and does not justify changing its
  assertion.

### Golden-corpus syntax reconciliation

`clif_golden_lane_no_drift` initially stopped after entry 06 because corpus
entry `07_trait_dispatch.cl` did not emit any frames: its required trait method
still used the deleted annotation-introducer spelling `(size [a] :Int)`.
QA approves changing only that tail to bare `Int`, as required by
`spec/07-traits.md` §7.1.1. The trait remains required, both implementations and
the exit-8 behavioral witness remain unchanged, and no golden is recaptured by
this fixture migration. Any resulting CLIF difference remains attributable
emission evidence and must be reviewed separately.

Entry `08_adt_in_vec_projection.cl` then exposed the same settled duplicate
field-binder migration: `Given` and `Solved` both declared `value`. QA approves
renaming only the `Solved` binder to `solved-value` under
`spec/05-definitions.md` §5.2.2. Constructor arity, positional matches, the
projection loop, and its exit witness remain unchanged.

After those migrations and the separately attributed canonical-glue FuncId
rebaseline (`4c198e43`), the complete workspace gate executed 5,461 tests:
5,339 passed, 122 failed, and one was skipped in 69.6 seconds. The golden-lane
test and all four post-migration current-only fixture tests are green. The
remaining one-count difference from the deterministic arithmetic is consistent
with the environment-dependent/flapping component already demonstrated by the
paired baseline runs; sprint closure still requires a saved name-set comparison
and repeated certification runs, not this scalar alone.

### Host-export and stdlib-cascade attribution

The macro/stdlib cascade reduced to the synthetic `macros/sconcat`
`PrimitiveExtern`: Linux host binaries contained the function in `.symtab` but
not `.dynsym`, so fresh-JIT `dlsym(RTLD_DEFAULT, "sconcat")` failed. Repository-
owned Linux `--export-dynamic` wiring flips the existing
`worker::tests::dlsym_host_symbol_resolves_exported_primitive` guard and clears
the macro-splice and stdlib publication cascade without changing library or
test semantics.

After that fix, `spec_11_stdlib::macro_vec_empty_pinned_ok` alone stopped at an
unknown bare `Vec` type. QA approves adding `Vec` to its existing explicit
`primitives` import: `spec/03-types.md` §3.1 and `spec/08-modules.md` §8.8.1
require a bare type to be explicitly imported or prelude-exported, and the
curated workspace prelude deliberately exports only `Int`, `Bool`, `Float`,
and `String`. The annotated empty-vector expression, expected length zero, and
positive pinning oracle remain unchanged.

### Exemplar field-binder reconciliation

Once the workspace stdlib cascade cleared, the exemplar and its independent
`exemplar::t_s2_1_eliminate_contract_on_given_returns_none` fixture both
stopped at `Cell` declarations that reused one field binder across `Given` and
`Solved`. QA approves distinct `given-*` and `solved-*` binder names under
`spec/05-definitions.md` §5.2.2. Constructor arities and all positional match
bindings are unchanged; the fixture still asserts only that eliminating a
fixed cell's own digit returns `None` via exit 0.

## Next skills

- `/dev(src)` — macro/annotation expansion and availability cluster.
- `/review(src)` — design-conformance review after that repair.
- `/qa` — repeat the named reconciliation after the full-suite checkpoint.
