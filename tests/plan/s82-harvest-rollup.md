# S82 Harvest Measurement Gate — Roll-up

The confidence-to-delete centerpiece. Per-file dedup map across the 20
`tests/legacy/*.rs` files (1,323 `#[test]` fns), mapping every test to
COVERED / GAP / OBSOLETE per the §2.1 hard rule: **no legacy assertion
is dropped without a written disposition.**

Authored: `/qa` (S82 Wave 0, read-only audit; 2026-06-14). Methodology:
`tests/plan/sprint82-test-plan.md` §2. The 5 files with prior S64
per-test reaudits (`e2e`, `ring0`, `ring1`, `ring2`, `sketch_port`)
EXTEND those audits — their S64 disposition codes map to the S82
three-way as: COVERED→COVERED, DUPLICATE-IN-LEGACY→COVERED (canonical
instance covers it), GAP-COVER→GAP, GAP-HARVEST→GAP, REGRESSION-GUARD→GAP
(preserve). The 15 never-audited files were audited fresh this wave via
read-only `Explore` fan-out.

> **Granularity note.** The README "Tests" column counts assertions
> (e.g. e2e=309); the actual `#[test]` fn count is 1,323 total
> (e2e=148). This roll-up disposes at `#[test]` fn granularity, which
> is the unit the harvest ports. Multi-assert tests whose active
> coverage is partial were split to GAP per risk-class 5 (already done
> in the S64 reaudits; checked in the fresh audits).

## Roll-up table

| FIXME | File | Tests | C (covered) | G (gap) | O (obsolete) | reg-guard (⊂G) | Owning crate(s) for GAP harvest |
|---|---|---:|---:|---:|---:|---:|---|
| 0134 | `e2e.rs` | 148 | 82 | 66 | 0 | 12 | typecheck + backend + src/ (int slice e2e-covered) |
| 0134 | `ring0.rs` | 108 | 99 | 9 | 0 | 4 | typecheck (+ backend, src/) |
| 0134 | `ring1.rs` | 190 | 139 | 51 | 0 | 0 | typecheck (+ backend) |
| 0134 | `ring2.rs` | 199 | 164 | 35 | 0 | 7 | typecheck (+ backend) |
| 0136 | `sketch_port.rs` | 148 | 114 | 34 | 0 | 17 | /qa-internal (per-crate units; preserve 11-failure lineage) |
| 0124 | `repl_experience.rs` | 190 | 100 | 85 | 5 | 2 | src/ (with typecheck, backend) |
| 0124 | `repl_negative_old.rs` | 31 | 11 | 18 | 2 | 0 | src/ + backend (display) + typecheck (module/inference) |
| 0125 | `ring3_repl.rs` | 41 | 40 | 1 | 0 | 1 | typecheck (macro_expand) |
| 0127 | `io.rs` | 76 | 38 | 38 | 0 | 2 | platform + typecheck + backend + stdlib + spec_04 (curry) |
| 0127 | `io_minimal.rs` | 5 | 5 | 0 | 0 | 0 | — (all subsumed by spec_10_io) |
| 0130 | `ring4_trace_taxonomy.rs` | 31 | 27 | 4 | 0 | 0 | typecheck (co: **intrinsics**) |
| 0133 | `v4_jit_reclaim.rs` | 6 | 0 | 6 | 0 | 6 | backend (Arc/Jit reclaim) |
| 0135 | `lenient.rs` | 16 | 11 | 5 | 0 | 0 | backend (co: **primitives**) + platform (IO-schedule) |
| 0143 | `examples.rs` | 15 | 15 | 0 | 0 | 0 | — (subsumed by tests/examples.rs umbrella) |
| 0143 | `examples_run.rs` | 1 | 1 | 0 | 0 | 0 | — (subsumed by tests/examples.rs) |
| 0143 | `exemplar.rs` | 3 | 3 | 0 | 0 | 0 | — (subsumed by tests/exemplar.rs) |
| 0143 | `exemplar_solver_correctness.rs` | 2 | 2 | 0 | 0 | 2 | — (subsumed by tests/exemplar.rs + regression.rs) |
| 0144 | `sprint23.rs` | 61 | 57 | 4 | 0 | 3 | src/ (build_confidence batch + cache manifest) |
| 0148 | `wave6_demo_repros.rs` | 5 | 5 | 0 | 0 | 1 | — (subsumed; Defect 6 guard FAILING-NOT-IGNORED in regression.rs) |
| 0149 | `v4_pipeline.rs` | 47 | 47 | 0 | 0 | 0 | — (all subsumed by spec_* + cache + platforms) |
| | **TOTALS** | **1323** | **960** | **356** | **7** | **57** | |

C + G + O = 960 + 356 + 7 = 1323 ✓

## Headline

- **Total legacy tests:** 1,323 `#[test]` fns across 20 files.
- **Genuine GAP to harvest:** **356** (of which 57 REGRESSION-GUARD, must
  be preserved failing-or-passing per lineage).
- **COVERED + OBSOLETE = delete-on-confirm:** **967** (960 covered + 7
  obsolete) — re-confirmed against named active tests, no harvest needed.

This turns "re-port 1,323 tests" into "harvest 356 measured gaps,
confirm 959 covered, drop 8 obsolete." The harvest is ~27% of the
corpus, not 100%.

## GAP concentration (where the 356 live)

| Cluster | ~Count | Owner | Notes |
|---|---:|---|---|
| e2e slash-command argument-handling + display-format | ~66 | src/, backend, typecheck | `/info`/`/list <prefix>`/`/mod`/positives; biggest single cluster |
| repl_experience Ring-1/Ring-2A display + operators | ~85 | src/ (display), backend, typecheck | string/ADT/closure display, trait-operator dispatch display |
| ring1 composition shapes (strings×ADT×closure×Vec) + neg-coverage | ~51 | typecheck, backend | spec MUST clauses (§3.8, §6.5.x, §4.4) not e2e-verified |
| io platform-effect + RC-discard + IO type-error | ~38 | platform, backend, typecheck, stdlib | print/read-line, then-combinator RC, bind type-errors, do/bind! desugar |
| ring2 trait/constrained-poly + 5 ex-HARVEST reclassified | ~35 | typecheck, backend | HKT, occurs-check, neg trait-impl |
| sketch_port sigsegv-isolation + RC + default-method guards | ~34 | per-crate (qa-internal) | 17 reg-guards incl 11-failure lineage |
| repl_negative_old display/list/module negatives | ~18 | backend(display), typecheck, src/ | classification + qualified-display + scoping negatives |
| v4_jit_reclaim Decision-31 reclaim | 6 | backend | all reg-guard; Arc/counter assertions (Rust-internal) |
| lenient IO-scheduling (Par/ResourceSerial) | 5 | backend + platform | needs test-capture DLL classification |
| ring4_trace type-shape | 4 | typecheck (co: intrinsics) | (SList String) / (SList Trace) field type assertions |
| sprint23 batch-main + cache-manifest | 4 | src/ (build_confidence, cache) | --run main exit-code coverage gap |
| ring0 parse-error/redefn-GOT/nested-if | 9 | typecheck, src/ | 4 reg-guard |
| ring3 forward-ref-not-expanded | 1 | typecheck (macro_expand) | reg-guard |

## Flags carried into the harvest (Phase 5)

1. **`0134` partition — CONFIRMED, no mis-assignment.** typecheck =
   AST/type-shape + inference + `assert_type_error`→`tc.check()`;
   backend = `assert_rc_balanced` + closure-capture + Vec-COW codegen;
   int = `compile_both()` batch/REPL parity = e2e-covered →
   **int slice mostly delete** (no int unit harvest warranted; the int
   `target:` is retained only as coordination anchor). e2e+ring1+ring2
   GAPs are predominantly typecheck/backend; the int-parity shapes in
   `e2e.rs` and `v4_pipeline.rs` are already covered by the canonical
   e2e `run_through_all_modes` discipline (v4_pipeline = 0 GAP confirms
   this).

2. **Co-owner relabel (post-D43):** `cranelisp-runtime` no longer
   exists. `0130` (ring4_trace_taxonomy) co-owner = **`cranelisp-intrinsics`**
   (trace bodies / `DisplayDescriptor`), NOT "/runtime". `0135` (lenient)
   co-owner = **`cranelisp-primitives`**, NOT "/runtime". The README rows
   say "/runtime" — moot at delete-time (row removed with file) but the
   GAP targets above name the correct crate.

3. **`0136` sketch_port — 11-known-failure lineage preserved.** The
   sketch_port slice carries 17 REGRESSION-GUARDs (the `sigsegv_isolation_*`
   cluster = 5 distinct shapes, the RC cluster, the default-method
   triple, etc.). These exercise real compiler corner cases. Any GAP
   among the 11 historical pre-existing failures harvests as a
   **failing-not-ignored unit in the owning crate** (per
   `memory/feedback_failing_not_ignored.md`) — NOT dropped as OBSOLETE
   just because it fails. This is called out explicitly in
   `s82-harvest-sketch_port.md`.

4. **OBSOLETE total is small (7) and well-evidenced.** 5 in
   `repl_experience.rs` (perf microbenchmarks — `*_is_fast`,
   `first_five_minutes_workflow` — measure speed not semantics, not
   spec-required); 2 in `repl_negative_old.rs` (1 D17-superseded
   trait-method-registration negative + 1 perf/sanity-shape fold). No
   legacy assertion is dropped without this written reason.

## Per-file disposition docs

One doc per file under `tests/plan/`:
`s82-harvest-{file}.md`. The 5 prior-reaudited files cite + extend
their `wave-5.6-{file}-reaudit.md`. Exit checklist per file (per §2.3):
(a) every test dispositioned [DONE this wave]; (b) all GAP harvested +
green in owning crate [Wave 2]; (c) file deleted [Wave 2]; (d) README
row removed [Wave 2]; (e) FIXME closed [Wave 2].

This wave (Wave 0) delivers (a) only — the measurement gate. Wave 2
executes (b)-(e).
