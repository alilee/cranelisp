# Sprint 116 baseline reconciliation

Date: 2026-07-23  
Authority: `/qa`  
Sprint-start commit: `aefe7e11`  
Current checkpoint: `f606ce4c`

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

## Next skills

- `/dev(src)` — macro/annotation expansion and availability cluster.
- `/review(src)` — design-conformance review after that repair.
- `/qa` — repeat the named reconciliation after the full-suite checkpoint.
