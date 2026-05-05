# Wave 6 batch 5 — sprint61_bare_primitive + wave6_demo_repros audit

Per-test audit of two small legacy files:

- `tests/sprint61_bare_primitive.rs` (267 LOC, 5 tests) — Sprint 61
  Slice 1 bare-primitive value-path regression guard
- `tests/wave6_demo_repros.rs` (495 LOC, 5 tests) — Sprint 58 Wave 6
  demo-surfaced defects (Defects 1, 2, 3, 4+5, 6)

Total: **10 tests** across **2 files**.

Author: `/qa` (audit + carry-forward dispatch, 2026-05-05). Methodology
identical to Wave 6 batches 1–4: per-test review against the existing
e2e carry-forward universe with disposition codes (COVERED /
DUPLICATE-IN-LEGACY / GAP-COVER / REGRESSION-GUARD / GAP-HARVEST),
spec-anchored dedup, regression-named tests treated as presumptively
discriminating per Wave 5.5/5.6 protocol.

## Cluster character

The two files are unrelated by topic but co-batched per the Wave 6
schedule:

- `sprint61_bare_primitive.rs` — Sprint 61 Slice 1 work-product file
  guarding the bare-primitive value-path fix in
  `src/session_v4.rs::resolve_entry_for_display` +
  `check_bare_symbol_introspection`. The file is a five-test
  exhaustive partition of the discrimination axis: (T-S1-1) display
  format on bare reference; (T-S1-2) three-path (bare-value /
  introspection / call) convergence; (T-S1-3) ≥5-primitive
  generalisation; (T-S1-4) negative — unknown bare symbol must error;
  (T-S1-5) two-hop re-export chain landing on terminal Def. All five
  PASS today.

- `wave6_demo_repros.rs` — Sprint 58 Wave 6 user-proxy demo defect
  reductions, one test per Defect (4+5 collapse to one test). The
  five tests are anchored to specific historical defects by name:
  Defect 1 (REPL dep-load race), Defect 2 (stdlib seq.lazy missing
  imports), Defect 3 (docstring separator divergence), Defect 4+5
  (`/run-tests` batched crash on real exemplar html.cl), Defect 6
  (exemplar solver stack-overflow on full 81-cell puzzle). 4/5 PASS
  today; the **Defect 6** test (`exemplar_solver_does_not_stack_overflow_on_small_puzzle`)
  remains FAIL — it exercises `--run exemplar/solver.cl` on the
  real solver entry (which prints the puzzle, drives `solve`, prints
  the result), and the JIT'd recursion overflows the stack. This
  matches the open ledger entry per `tests/plan/ledger.md` lines
  120–131 and `memory/feedback_failing_not_ignored.md`.

Both files predate the Sprint 63 M7 inline-FIXME → numbered-FIXME
methodology pivot, so inline FIXMEs are preserved verbatim and
migrate at harvest review per the Wave 6 b2/b3/b4 precedent.

## Current pass/fail status against the binary at audit time

(2026-05-05, `cargo nextest run --test sprint61_bare_primitive --test wave6_demo_repros`):

- `sprint61_bare_primitive.rs`: **5/5 PASS**
- `wave6_demo_repros.rs`: **4/5 PASS**, 1 FAIL — only
  `exemplar_solver_does_not_stack_overflow_on_small_puzzle` fails
  (subprocess overflows stack and aborts with `fatal runtime error:
  stack overflow, aborting` after printing the input grid). Matches
  the existing Defect 6 ledger entry. The four PASS tests are:
  - `repl_dep_load_no_race_with_persistent_workers` (Defect 1 —
    underlying race resolved post-Sprint 58 W6)
  - `stdlib_seq_lazy_imports_resolve_nil_cons` (Defect 2 — `/stdlib`
    fix landed)
  - `display_defn_with_docstring_uses_dash_separator` (Defect 3 —
    `/int` separator format fix landed)
  - `run_tests_batched_invocation_no_crash` (Defect 4+5 — combined
    fix landed; current binary completes the batched run without
    crash, finds tests, reports pass/fail)

## Methodology recap

Per Wave 5.6 brief (in force from Waves 5.5/5.6):

1. No exact 1:1 duplicates after `[Tested ...]` carry-forward exists.
2. Multi-angle on same spec property → PRESERVE.
3. Regression-named tests are presumptively discriminating — default
   to GAP-COVER (REGRESSION-GUARD) unless EXACT 1:1 duplicate is
   provable.
4. Spec-anchoring is the dedup criterion, not source-shape match.

## Summary

| Disposition | Count |
|---|---:|
| COVERED | 0 |
| DUPLICATE-IN-LEGACY | 0 |
| GAP-COVER | 10 (of which REGRESSION-GUARD: 10) |
| GAP-HARVEST | 0 |
| **Total** | **10** |

Same structural finding as Wave 6 batches 2/3/4: regression-named
work-product files exhaustively partition the carry-forward surface.
The dedup risk is zero by construction — every test is a deliberate
reduction rung against a specific historic defect surface or a
deliberate spec-conformance rung against a specific Slice 1 promise.

## Per-test classifications

### File 1: tests/sprint61_bare_primitive.rs (5 tests)

The file's docstring (lines 1–22) names the cluster character: Slice 1
of Sprint 61 fix verification, written POST-fix as the regression
guard. Spec anchors: `repl/spec.md §1.1` (display format),
`spec/08-modules.md §8.9` (re-export provenance), and the design doc
`design/int/bare-primitive-value-path.md` (Slice 1 design + fix
rationale).

There is one existing carry-forward in the new e2e suite that overlaps
the topic: `tests/repl_introspection.rs::bare_primitive_type_int_displays_type_info`
(lines 712–731). It covers bare-`Int` (a primitive **type**), not
bare-`add-i64` (a primitive **fn**). Different resolution path, so no
overlap with any of the five Slice 1 tests.

The five tests partition the discrimination axis exhaustively:

| # | Test name | LOC | Spec property | Angle | Disposition | Status |
|---:|---|---|---|---|---|---|
| 1 | `bare_primitive_add_i64_at_prompt_displays_type_and_fqn` | 50–78 | repl/spec.md §1.1 — universal `:Type name ; classification - doc` format | bare `add-i64` displays primitives-qualified name + Fn type prefix + `; primitive` classification + `; primitive - <doc>` separator | GAP-COVER (REGRESSION-GUARD) — display-format conformance for bare primitive fn | PASS |
| 2 | `bare_primitive_parallel_paths_converge_on_same_attribution` | 87–125 | bare-primitive-value-path.md §2 (three paths) + §5 (expected output) — anti-divergence guard | three paths (`/sig add-i64`, bare `add-i64`, `(add-i64 2 3)`) all attribute to `primitives/add-i64`; call evaluates to 5 | GAP-COVER (REGRESSION-GUARD) — three-path convergence guard | PASS |
| 3 | `bare_primitive_surface_resolves_identically_across_five_plus_symbols` | 137–160 | spec/08-modules.md §8.9 — re-export provenance generalises to all primitives | parameterise over add-i64, eq-i64, mul-i64, sub-i64, not, str-concat — all resolve to `primitives/<name>`, no "undefined variable", classification `; primitive` | GAP-COVER (REGRESSION-GUARD) — generalisation across primitive surface | PASS |
| 4 | `bare_primitive_unknown_name_produces_undefined_error_neg` | 171–210 | repl/spec.md §1.1 negative complement — unknown name MUST NOT silently dispatch | unknown name "unknown-primitive-name-zzzz" produces an undefined/not-found error; no silent dispatch to similarly-named primitives | GAP-COVER (REGRESSION-GUARD) — negative guard against over-broad fix | PASS |
| 5 | `bare_primitive_two_hop_reexport_chain_lands_on_terminal_def` | 225–267 | bare-primitive-value-path.md §"Post-implementation note" + spec/08-modules.md §8.9 — re-export chain transitivity | with the workspace stdlib loaded, two-hop chain `user → prelude → primitives` lands on `primitives/add-i64` (not `user/add-i64` or `prelude/add-i64`) | GAP-COVER (REGRESSION-GUARD) — transitive-resolution guard | PASS |

**Carry target:** All 5 tests carry to `tests/repl_introspection.rs`
as siblings of the existing `bare_primitive_type_int_displays_type_info`
test. The introspection file already covers the bare-symbol display
surface; the bare-primitive-fn discrimination joins that cluster
(types vs fns are different resolution paths through the symbol
table). The PLAN.md row's nominal target (`spec_appendix_a_builtins.rs`)
is a poor fit — that file is for the per-builtin behaviour catalogue,
not display-format conformance.

**Spec-link linter findings (pre-port):** the legacy file has 1
MIS-CITED (line 223 cites `§8.9` in
`design/int/bare-primitive-value-path.md` — that anchor doesn't exist
there; the cite was meant to be `spec/08-modules.md §8.9` per the
sentence body) and 1 MALFORMED (line 131 cites bare
`bare-primitive-value-path.md` without the `design/int/` prefix). Both
will be fixed in the carry-forward annotations: the canonical anchor
is `repl/spec.md §1.1` (display format) + `spec/08-modules.md §8.9`
(provenance) + `design/int/bare-primitive-value-path.md §5` (expected
output) / §"Post-implementation note" (transitivity).

### File 2: tests/wave6_demo_repros.rs (5 tests)

The file's docstring (lines 1–29) names the cluster character: Sprint
58 Wave 6 demo-surfaced defects, one test per defect, each carrying a
`// spec:` annotation naming the spec section the defect violates
plus an inline `FIXME(/owning-skill)` pointer. Pre-Sprint-63
inline FIXMEs migrate at harvest per Sprint 63 M7 protocol.

| # | Test name | LOC | Spec property | Angle | Disposition | Status |
|---:|---|---|---|---|---|---|
| 1 | `repl_dep_load_no_race_with_persistent_workers` | 166–201 | implicit Principle 11 — REPL/`--run` parity (root CLAUDE.md "Defects" §1) | REPL with `--priority-workers 4` + REPL-import of `collections.list` MUST NOT emit "no parsed sexps for module" race symptom | GAP-COVER (REGRESSION-GUARD) — Defect 1 race regression guard | PASS |
| 2 | `stdlib_seq_lazy_imports_resolve_nil_cons` | 225–263 | spec/08-modules.md §8.3.6 — null-import-suppresses-prelude-glob: any module that uses `(import [prelude []])` MUST resolve every name through explicit imports | batch-compile entry that imports `seq.lazy [iterate take]` MUST NOT fail with "undefined variable: Nil/Cons/Some/None" | GAP-COVER (REGRESSION-GUARD) — Defect 2 stdlib-import regression guard | PASS |
| 3 | `display_defn_with_docstring_uses_dash_separator` | 286–307 | repl/spec.md §1.1 — universal output format mandates DASH separator between classification and docstring | `(defn double "Multiply by 2" [:Int x] ...)` → bare `double` displays `; defn - Multiply by 2`, NOT `; defn ; Multiply by 2` | GAP-COVER (REGRESSION-GUARD) — Defect 3 display-format regression guard | PASS |
| 4 | `run_tests_batched_invocation_no_crash` | 339–417 | repl/spec.md §16.3 — `/run-tests <module>` MUST execute discovered tests + report pass/fail without crashing | exercise `/run-tests html` on the real exemplar — assert no signal crash, no race symptom, no load failure, AND assert the test actually ran | GAP-COVER (REGRESSION-GUARD) — Defect 4+5 batched-run regression guard. Stronger than `regression.rs::d45_real_exemplar_html_run_tests_no_crash` (which only checks signal-crash); this version asserts positive completion (`test-wrap-tag` + `ok`/`FAILED:` substring) | PASS |
| 5 | `exemplar_solver_does_not_stack_overflow_on_small_puzzle` | 448–495 | implicit (exemplar validation) — solving an 81-cell puzzle via `--run exemplar/solver.cl` (the real solver entry) must return a SolveResult, not segfault/abort | `--run exemplar/solver.cl` on the canonical 17-clue puzzle MUST NOT exit with signal-crash or stack-overflow abort | GAP-COVER (REGRESSION-GUARD) — Defect 6 real-solver-entry regression guard. Distinct angle from `regression.rs::d6_exemplar_solve_minimal_puzzle_no_io_does_not_segv` (which is a synthetic single-form repro using the exemplar source as a library — no IO, no print). This test exercises the **real solver entry** (`exemplar/solver.cl::main`) including the IO trampolines that the synthetic repro elides. | **FAIL** — open Defect 6 stack-overflow ledger entry |

**Carry target:** Defects 1, 2 carry to `tests/repl_persist_race.rs`
or `tests/spec_08_modules.rs` (Defect 2's anchor is §8.3.6
null-import). Defects 3, 4+5 carry to `tests/repl_introspection.rs`
(Defect 3 — display format) and `tests/regression.rs` (Defect 4+5 —
sibling of d45 cluster). Defect 6 carries to `tests/regression.rs`
(sibling of `d6_exemplar_*` cluster) as failing-not-ignored, joining
the four existing FAILING d6_exemplar carry-forwards from Wave 6 b3.

After analysis the carry-forward landing is:

- Defect 1 (`repl_dep_load_no_race_with_persistent_workers`) →
  `tests/repl_persist_race.rs` (file is dedicated to REPL+priority-
  worker race regressions; this is the natural home).
- Defect 2 (`stdlib_seq_lazy_imports_resolve_nil_cons`) →
  `tests/spec_08_modules.rs` (anchor is §8.3.6, the null-import
  semantics).
- Defect 3 (`display_defn_with_docstring_uses_dash_separator`) →
  `tests/repl_introspection.rs` (anchor is §1.1, sibling of the
  existing `defn_reports_function_type` and `bare_primitive_type_int_*`
  display-format tests).
- Defect 4+5 (`run_tests_batched_invocation_no_crash`) →
  `tests/regression.rs` (as `wave6_run_tests_batched_html_completes_without_crash`,
  sibling of d45 cluster — adds the positive-assertion angle).
- Defect 6 (`exemplar_solver_does_not_stack_overflow_on_small_puzzle`)
  → `tests/regression.rs` (as `wave6_exemplar_solver_full_run_does_not_stack_overflow`,
  sibling of d6_exemplar cluster — failing-not-ignored).

## Tests flagged for /sprint judgment

### A. Defect 6 carry-forward — failing-not-ignored

Test 5 of `wave6_demo_repros.rs` is the sole failing carry-forward.
It joins the four existing failing-not-ignored tests in
`regression.rs §F` (`d6_exemplar_*` cluster, Wave 6 batch 3 carries).
The angle is distinct: `wave6_demo_repros::exemplar_solver_*` exercises
the real solver entry (`--run exemplar/solver.cl` from the IO-driven
`main`), whereas the four d6_exemplar tests exercise synthetic single-
form repros that use the exemplar source as a library (no IO).
Discriminating the **IO-trampoline path** from the **pure-core
recursion** is the unique value of this carry-forward. Per
`memory/feedback_failing_not_ignored.md` it lands un-ignored.

The owning skill is `/backend` (deep recursion stack-overflow on
81-cell Vec-copying ADT traversal). Existing FIXME 0145 (Wave 6 b3
sprint59 repros) is the right harvest target — same defect, same
owner, same cluster — but rather than amend FIXME 0145, this batch
files its own FIXME 0147 referencing 0145 as the parent harvest
scope.

### B. Owning-skill alignment for the harvest FIXME

The 5 sprint61_bare_primitive tests target `/int` (REPL session_v4
`resolve_entry_for_display` + `check_bare_symbol_introspection` —
the Slice 1 fix area). The 5 wave6_demo_repros tests target a fan-
out of skills (Defect 1 → /int session_v4 dep-load wiring; Defect 2
→ /stdlib fixed; Defect 3 → /int display format; Defect 4+5 →
/backend or /int run-tests dispatch; Defect 6 → /backend solver
recursion).

Per Wave 6 b2/b3/b4 precedent (one harvest FIXME per quarantine batch
when owners predominantly align), this batch files **two harvest
FIXMEs** because the owning-skill alignment is genuinely different:

- FIXME 0147 — `harvest: tests/legacy/sprint61_bare_primitive.rs into
  /int #[cfg(test)] unit tests` — target `/int`, scope the bare-
  primitive value-path Slice 1 surface area.
- FIXME 0148 — `harvest: tests/legacy/wave6_demo_repros.rs into
  /int + /backend + /stdlib unit tests` — target `/int` (primary,
  three of five tests), with co-owners called out for the /backend
  Defect 6 scope (cross-references existing FIXME 0145) and /stdlib
  for Defect 2 (already resolved; the legacy test is a
  resolved-by-passing carry-forward).

Alternative considered + rejected: ONE consolidated FIXME 0147
covering both files. Rejected because the bare-primitive-value-path
work product is a clean surface bounded by a single Slice 1 fix in
session_v4.rs (mappable directly to one unit-test crate region),
whereas the demo-repro file is a fan-out of five unrelated defects
with five distinct unit-tier harvest targets. Splitting yields
clearer harvest boundaries.

### C. Inline FIXMEs in legacy files

**sprint61_bare_primitive.rs** — zero pre-Sprint-63 inline `FIXME(...)`
markers. The file's docstring + per-test docstrings reference design
docs by anchor; no migration step required.

**wave6_demo_repros.rs** — **5 inline `FIXME(/owning-skill)` markers**
(one per defect, in the per-defect section banner):
- line 158–161: `FIXME(/int)` — Defect 1 dep-load race fix in
  `compile_dep_inline`. Carry-forward passes today; resolved-by-
  passing.
- line 219–222: `FIXME(/stdlib)` — Defect 2 add explicit imports to
  `stdlib/seq/lazy.cl`. Carry-forward passes today; resolved-by-
  passing.
- line 279–281: `FIXME(/int)` — Defect 3 `append_docstring_comment`
  format. Carry-forward passes today; resolved-by-passing.
- line 329–332: `FIXME(/backend) or FIXME(/int)` — Defect 4+5 RC /
  last-use issue across consecutive run-test invocations. Carry-
  forward passes today; resolved-by-passing.
- line 437–443: `FIXME(/backend)` + `FIXME(/port)` — Defect 6
  solver stack-overflow + re-enable disabled solver tests once
  fixed. Carry-forward FAILS today; **OPEN** defect; FIXME 0148
  documents the parent /backend scope (cross-ref FIXME 0145).

Per Wave 6 b2/b3/b4 protocol, all five inline FIXMEs are preserved
verbatim in the quarantined source (read-only) and migrate to
numbered `design/arch/fixmes/NNNN-*.md` per Sprint 63 M7 protocol at
harvest review. Four of the five are "resolved by passing carry-
forward" (Defects 1, 2, 3, 4+5). One (Defect 6) is open and folds
into the existing /backend solver scope (FIXME 0145 + new 0148).

### D. Spec-link linter findings

Pre-port linter run found 4 issues:

- `sprint61_bare_primitive.rs:223` MIS-CITED — `§8.9` not in
  `design/int/bare-primitive-value-path.md`. Resolution: the cite is
  malformed; intended cite is `spec/08-modules.md §8.9`. Carry-
  forward will use the canonical pair `repl/spec.md §1.1 +
  spec/08-modules.md §8.9 + design/int/bare-primitive-value-path.md
  §"Post-implementation note"`.
- `sprint61_bare_primitive.rs:131` MALFORMED — bare
  `bare-primitive-value-path.md` without the `design/int/` prefix.
  Resolution: carry-forward uses the full path
  `design/int/bare-primitive-value-path.md §7`.
- `wave6_demo_repros.rs:163` MIS-CITED — `§Self-documenting REPL` not
  found in `CLAUDE.md`. Resolution: the cite was a stretch — Defect 1
  is a `--run`/REPL parity defect, not a `repl/spec.md` clause.
  Carry-forward uses the closest concrete anchor: `repl/spec.md
  §0.2` ("Run Mode") + the new test name discriminates the implicit
  Principle 11 nature.
- `wave6_demo_repros.rs:445` MALFORMED — `implicit (exemplar
  validation)`. Resolution: carry-forward uses
  `spec/12-runtime.md §12.5` (RC behaviour at depth) — same anchor
  as the existing `d6_exemplar_*` cluster.

All four are addressed in the carry-forward annotations; the legacy
files remain as-quarantined (read-only post-quarantine).

## Recommendations

1. **Carry forward all 10 tests.** Zero DUPLICATE-IN-LEGACY, zero
   COVERED, zero GAP-HARVEST. Every test is a discrete reduction
   rung anchoring a specific historic defect surface or a specific
   Slice 1 promise — same structural finding as Wave 6 b1–b4.

2. **Five carry-forward targets**: extend `tests/repl_introspection.rs`
   (+5 bare-primitive + 1 docstring-separator = +6 tests),
   `tests/repl_persist_race.rs` (+1 dep-load race),
   `tests/spec_08_modules.rs` (+1 stdlib seq.lazy null-import
   regression), `tests/regression.rs` (+2: run-tests batched + solver
   stack-overflow). No new files.

3. **Two harvest FIXMEs**:
   - **0147** target `/int` — sprint61_bare_primitive.rs into
     `crates/cranelisp-` (TBD: probably `src/session_v4.rs`
     `#[cfg(test)]` cluster, since the Slice 1 fix is in src/) unit
     tests.
   - **0148** target `/int` — wave6_demo_repros.rs harvest fan-out;
     names co-owners /backend + /stdlib + /port; cross-references
     FIXME 0145 for the Defect 6 scope.

4. **One failing-not-ignored carry-forward** for Defect 6
   (`wave6_exemplar_solver_full_run_does_not_stack_overflow` in
   `regression.rs`). Owning skill `/backend`. Joins four existing
   failing-not-ignored Defect 6 carries from Wave 6 b3.

5. **Preserve inline FIXMEs** verbatim in the quarantine source
   (read-only post-quarantine). FIXME 0148 names the resolved-by-
   passing dispositions for Defects 1, 2, 3, 4+5; FIXME 0145+0148
   together cover the Defect 6 open scope.

## Methodology takeaway

Wave 6 batch 5 is the **fifth 100% GAP-COVER REGRESSION-GUARD batch
in a row** in S64 W6:

| Batch | Tests | GAP-COVER | DUPLICATE | COVERED | Yield % |
|---|---:|---:|---:|---:|---:|
| b1 | 21 | 21 | 0 | 0 | 100% |
| b2 | 61 | 59 | 2 | 0 | 97% |
| b3 | 36 | 36 | 0 | 0 | 100% |
| b4 | 25 | 25 | 0 | 0 | 100% |
| b5 | 10 | 10 | 0 | 0 | 100% |

The pattern is locked: regression-named work-product files
exhaustively partition the carry-forward surface — they are
presumptively discriminating and the per-test review converges
quickly (audit's per-test classification is mechanical once the
cluster character is established). Wave 6 closes with five batches
totalling 153 carry-forwards across 11 quarantined files, zero
DUPLICATE-IN-LEGACY findings outside b2 (97% yield in b2 alone).
