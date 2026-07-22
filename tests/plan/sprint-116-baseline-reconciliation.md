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

## Next skills

- `/dev(src)` — macro/annotation expansion and availability cluster.
- `/review(src)` — design-conformance review after that repair.
- `/qa` — repeat the named reconciliation after the full-suite checkpoint.
