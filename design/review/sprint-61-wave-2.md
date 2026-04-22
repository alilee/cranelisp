# Sprint 61 Wave 2 — /review Report

**Reviewer**: /review
**Date**: 2026-04-22
**Verdict**: **PASS WITH FINDINGS**
**Scope**: Slice 1 (bare-primitive value path, `/int`) + Slice 2 (exemplar
`test-unsolvable` — Layer 1 `/port` fix in `exemplar/solver.cl` + Layer 3
`/backend` fix in `crates/cranelisp-backend/src/compiler/mod.rs::is_last_use`).
Plus /qa integration tests (5 + 2) and design-doc updates
(`design/backend/ring2-rc.md §5.5`, `design/int/bare-primitive-value-path.md`
post-impl note), `tests/plan/baseline.md`, `tests/plan/ring4.md`.

## Summary

- Blockers: 0
- Importants: 2
- Suggestions: 4

Wave 2 meets its acceptance gate: Slice 1 5/5 green + Slice 2 2/2 green (the
two tests ledgered at Wave authoring as FAILING now PASS post-fix),
`borrowed_vars` gate lands symmetrically with the existing `captured_vars`
gate at a single site (`is_last_use`), no boundary-type changes, no new
`unwrap()` in pipeline code, no `#[ignore]` in the new tests, both new test
files declared in `tests/plan/ring4.md` with traceability rows.

Two Important findings concern (a) a pre-existing integration-test
convention violation carried into `tests/sprint61_bare_primitive.rs`
(inline `project_root()` / `test_dir` helper duplication — see below) and
(b) a design-doc drift between the Slice 2 closure narrative and the
Sketch-comparison mandate. Suggestions are polish items.

## Blockers (B)

None.

## Importants (I)

1. **`tests/sprint61_bare_primitive.rs:38–92` — duplicated E2E harness
   helpers.**
   The new file redeclares a `TEST_COUNTER`, `project_root()`,
   `binary_path()`, `test_dir(label)`, and `run_repl_with_stdlib(input,
   label)` inline — structurally identical to the patterns already
   established in `tests/e2e.rs` and in `tests/CLAUDE.md §"Test Helpers"`
   (`run_repl_with_test_prelude`). The general review checklist
   §6 "Duplication — No copy-pasted blocks" and the project's stated
   helper home (`tests/helpers/mod.rs`, present at
   `#[path = "helpers/mod.rs"] mod helpers;` at the top of this file)
   both point the other way. The inline helper is also a mild
   specification break: `tests/CLAUDE.md` says the harness with the
   real stdlib is `run_repl_with_stdlib` (not present in that file — the
   closest canonical helper is `run_repl_with_test_prelude` which points
   at `tests/fixtures/` rather than `stdlib/`). Slice 1 needed a
   real-stdlib invocation for T-S1-4 and T-S1-5; that is legitimate, but
   the harness ought to be added to `tests/helpers/mod.rs` as the
   canonical third option (e.g., `run_repl_with_stdlib(input, label)`)
   rather than inlined.

   **Recommendation**: promote the three inline helpers to
   `tests/helpers/mod.rs` under the existing naming pattern. Fold into
   Slice 5 (/qa Wave 5) — methodology/cleanup is the correct bucket.
   Not a blocker because the tests work and are traceable; but it
   re-opens the duplication pattern the general checklist calls out.

   **Owning skill**: `/qa`.

   **Classification rationale**: Important, not Blocker — the
   duplication does not hide a defect, does not affect acceptance, and
   nextest runs each test in its own process so there is no
   cross-contamination risk. But the pattern is exactly the kind the
   general checklist §6 flags ("If two code blocks are structurally
   identical … extract a shared helper"). Future test files that need
   stdlib-loaded subprocess REPLs will copy this one and the drift
   begins.

2. **`design/int/bare-primitive-value-path.md §10 Sketch comparison —
   post-implementation addition is not equally rigorous for
   `design/backend/ring2-rc.md §5.5` rewrite.**
   The Slice 1 design doc has a §10 Sketch comparison section per
   the project-wide mandate in `design/review/CLAUDE.md §"Review
   Workflow"` step 1. The Slice 2 Layer 3 backend fix is documented
   only in `ring2-rc.md §5.5`'s prose expansion (3 rules + regression
   history); no Sketch-comparison block was added or updated for the
   new `borrowed_vars` rule. The ring2-rc.md file as a whole carries an
   older Sketch-comparison section at its top (not visible in this
   review's diff scope), but the specific /arch-visible change here —
   recognising that captured_vars + borrowed_vars are structural twins
   and that last-use-analysis MUST gate on both — is a non-trivial
   design observation that merits a short "Sketch had no last-use
   analysis; the fix formalises a rule the sketch did not need" note.

   **Recommendation**: /backend adds a one-paragraph addendum to
   `ring2-rc.md §5.5` noting the sketch's treatment (sketch's Vec COW
   predates the reimplementation's explicit borrowed_vars tracking;
   sketch handled the same case via ad-hoc inc/dec scattering rather
   than a gated ownership-transfer predicate). Alternatively, a short
   note in the §5.5 regression-history paragraph pointing at
   `sketch/docs/data-structures.md` for the same problem. One sentence.

   **Owning skill**: `/backend`.

   **Classification rationale**: Important because /review is the
   gate that checks the sketch-comparison mandate and we must flag
   misses. Not a Blocker because the code fix itself is correct and
   the rule is explicit in prose — the sketch comparison is
   documentation-archaeological hygiene, not a correctness question.
   Deferable into the same Slice 5 doc-hygiene pass that already
   tracks S1 of the Wave 1 report.

## Suggestions (S)

1. **`crates/cranelisp-backend/src/compiler/mod.rs:1204–1217` — the fix
   site's comment is exemplary; use the same density elsewhere.**
   The 14-line gate carries a 10-line doc-comment citing `ring2-rc.md
   §3.1` + §5.5, naming the regression (`repro-slice2.cl`), and
   explaining the aliasing / double-free mechanism. This is the right
   shape for any future RC gate and exceeds the quality of the
   neighbouring `captured_vars` comment (lines 1200–1203, two lines).
   Suggestion: backfill the `captured_vars` comment with the same
   structural-twin observation on a future RC tidy pass. Non-blocking.

2. **`exemplar/solver.cl:371–405` — closure narrative is excellent;
   migration carry is explicit and correctly tracked as Slice 5 I.**
   /port's 35-line closure block is a model of the "explain the fix
   and the journey, not just the symptom" voice. It links the three
   layers back to hypothesis lifecycle, references the specific test
   paths, and surfaces the Slice 5 migration debt. No change needed.
   Suggestion: this narrative shape could be promoted to a convention
   in `exemplar/CLAUDE.md` as "how to write a post-closure block after
   a multi-layer Branch-b handoff" for future /port work. Non-blocking.

3. **`src/session_v4.rs:3501–3554` — `MAX_DEPTH = 32` magic constant
   could be a named module-level `const`.**
   General checklist §3 "Named constants for magic numbers" — `32` is
   a compile-time depth limit matching the typechecker's
   `IMPORT_CHAIN_DEPTH_LIMIT`. The inline `const MAX_DEPTH: usize = 32`
   is inside the function body with a rationale comment two lines above
   — compliant with the letter of the rule, but hoisting it to a
   module-level `const IMPORT_CHAIN_DISPLAY_DEPTH: usize = 32` (or
   re-exporting the typechecker's existing limit constant) would make
   the "matches the typechecker's limit" invariant a source-of-truth
   link rather than a prose claim. Non-blocking; the current shape is
   the local-consistency idiom the rest of the file uses.

4. **`tests/sprint61_bare_primitive.rs:32–35` — pre-existing comment
   mentions "6/0 pass" but there are 5 tests (+ one dropped T-S1-6).**
   Minor doc nit. Line 17 says "(T-S1-3 is parametrised over 5
   primitives so the assertion count is slightly higher than the row
   count)", which is accurate, but the preamble framing "6/0 pass"
   reads as 6 test functions when there are 5. One-word fix.
   Non-blocking.

## Design-adherence audit

### Slice 1 (`/int`)

- **`design/int/bare-primitive-value-path.md §Post-implementation note`**:
  accurately documents Candidate 2 outcome with the "mechanical twist"
  clarification (one-hop resolver, not fall-through). ✓
- **§10 Sketch comparison**: present (sketch had a single-threaded
  eval path with no three-path split; the split is v4-specific and
  the divergence is incidental to the restructure). ✓
- **Fix landing**: `resolve_entry_for_display` now a bounded-depth
  loop (32 iterations, matching `IMPORT_CHAIN_DEPTH_LIMIT` intent);
  `check_bare_symbol_introspection` threads `resolved_module` into the
  returned `FQSymbol.module` across all 5 `ModuleEntry` arms (Macro,
  Def, TypeDef, TraitDecl, Constructor) consistently. ✓
- **Single-site alignment principle honoured**: no
  `SymbolInfo`/`ModuleEntry`/`FQSymbol` shape changes. ✓
- **Out-of-scope `/sig` divergence** (`/sig add-i64` still prints
  `... imported from prelude/add-i64` via `format_entry_sig`'s
  `ModuleEntry::Import` arm): correctly noted in design-doc §"Out of
  scope" as a Sprint 62 polish candidate. Acceptable carry. ✓

### Slice 2 Layer 3 (`/backend`)

- **`design/backend/ring2-rc.md §5.5` expansion**: two rules → three
  rules (captured + borrowed + last-use), with last-use now explicitly
  gated on both captured_vars AND borrowed_vars. Regression history
  paragraph names `exemplar/repro-slice2.cl`, cites the Layer 2
  Sudoku-backtracking bundling-by-construction, and cross-references
  the fix-site path. Implementation-location table gains a new row for
  `is_last_use`. ✓
- **Symmetry check**: `borrowed_vars` rule text mirrors the
  `captured_vars` rule text structurally ("do NOT own the value"
  → "The closure env holds its own inc'd reference"). Both name the
  mechanism by which ownership is already held elsewhere; both
  declare last-use transfer ineligible. ✓
- **Code site**: the gate at `compiler/mod.rs:1204–1217` is a
  structural twin of the `captured_vars` gate at
  `compiler/mod.rs:1200–1203`. Both return `false` before the
  `last_uses` lookup. Both operate at function-level scope. The
  comment at 1204–1214 cites `ring2-rc.md §3.1` + §5.5 and names the
  regression. ✓
- **RC-trace surface unchanged**: the gate adds a `HashSet::contains`
  guard ahead of the existing `last_uses` lookup. Off-path cost: one
  branch + one hash lookup per `is_last_use` call; on-path cost: early
  return avoiding the subsequent `HashMap::get`. Net-zero for the hot
  path. No new allocation on the Cranelisp heap, no new RC events. ✓

### Slice 2 Layer 1 (`/port`)

- **`exemplar/solver.cl:39–40`**: Given/Solved arms return `None` on
  `v == d`, matching the one-line Layer 1 fix the FIXME block
  predicted. ✓
- **`exemplar/solver.cl:371–405`**: FIXME block rewritten from
  51 lines (pre-fix hypothesis enumeration) to 35 lines (closure
  narrative citing tests + Layer classifications + migration carry).
  Voice is /port's (hypothesis-lifecycle-first, closure-last); no
  residual /backend-voice code-site references. ✓
- **Scope compliance**: working-tree `exemplar/solver.cl` hashes to
  `b4600e6`; stash@{0} `exemplar/solver.cl` hashes to `4a8833d`. The
  two diverge, confirming /port reapplied Layer 1 in their own words
  after /sprint reverted /backend's out-of-scope edits. ✓

## Scope-violation audit

Task brief claims `stash@{0}` contains /backend's out-of-scope edits
reverted by /sprint; /port reapplied Layer 1 properly. Verification:

- **`git stash list`**: `stash@{0}` carries the label "sprint61
  wave2: /backend out-of-scope exemplar/solver.cl edits (Layer 1 fix +
  FIXME rewrite); /port will reapply in follow-on". ✓
- **`git stash show stash@{0} --stat`**: the stash spans all seven
  Wave-2 files, not just `exemplar/solver.cl` — this is because the
  stash-pop cycle /sprint used preserved the backend crate's code fix
  + design-doc update + ring2-rc.md change, *plus* /backend's
  out-of-scope solver.cl edits. When `/sprint` popped, the intended
  path was "keep the backend-voice in-scope edits (compiler/mod.rs,
  ring2-rc.md), drop the out-of-scope exemplar/solver.cl edit, and let
  /port reapply in their own voice". ✓
- **Stash solver.cl vs working-tree solver.cl**: the Layer 1 fix at
  lines 39–40 is identical in both (as expected — the semantic
  content of "return None on v==d" is load-bearing and small). The
  FIXME block (lines 371–405 in working tree) is 35 lines in /port's
  voice; the stash version is ~55 lines in /backend's voice
  (technical RC-mechanism framing rather than hypothesis-lifecycle
  framing). The working-tree block names /port's SPRINT.md §Skill
  Plans hypothesis enumeration and opens with "Investigation: /port
  worked the 4-candidate hypothesis list from SPRINT.md
  cheapest-first"; the stash version opens with "LAYER 1
  (algorithmic):". The working-tree voice is /port's. ✓
- **No code drift**: all three Layer 1 behaviour assertions are
  semantically identical; the prose framing is different. /port's
  reapply did not inadvertently revert the Layer 1 semantic. ✓

**Conclusion**: scope violation is cleanly handled. /port's reapplied
Layer 1 fix has the correct semantic, and the FIXME block is in
/port's voice. No residual /backend-authored text in the working-tree
`exemplar/solver.cl`.

## Test coverage audit

### Slice 1 tests (`tests/sprint61_bare_primitive.rs`, 5 tests, ~325 LOC)

- **No `#[ignore]`**: `rg '#\[ignore\]' tests/sprint61_bare_primitive.rs`
  — 0 matches. ✓
- **All 5/5 passing** at SHA `b140ec5` per SPRINT.md line 497 readout.
  Authored POST-fix; stand as regression guards. ✓
- **Spec traceability**: every test carries a `// spec:` comment
  pointing at `repl/spec.md §1.1` + `spec/08-modules.md §8.9` +
  `design/int/bare-primitive-value-path.md`. ✓
- **Negative coverage bundled**: T-S1-4 guards against over-broad fix
  (unknown bare symbol must NOT silently dispatch); T-S1-5 bundles
  qualified-type negative assertion. ✓
- **Test-plan row present**: `tests/plan/ring4.md §Slice 1 authored
  test-name map` enumerates T-S1-1 through T-S1-5 with PASS status
  and T-S1-6 omission rationale. ✓

### Slice 2 tests (`tests/exemplar_solver_correctness.rs`, 2 tests, ~198 LOC)

- **No `#[ignore]`**: 0 matches. ✓
- **Authored FAILING per branch-(b) protocol**, now passing 2/2
  post-fix. Ledgered at
  `tests/plan/baseline.md §"Resolved this sprint"` with the three-line
  rationale trail per §Close-time Verification Protocol item 3. ✓
- **Spec traceability**: both tests carry `// spec:` comments citing
  `exemplar/solver.cl:370+ FIXME block`,
  `memory/feedback_cross_skill_minimal_repro.md`, and
  `memory/feedback_repros_join_suite.md`. ✓
- **FIXME handoffs visible**: T-S2-1 carries `FIXME(/port)` (pending
  migration action); T-S2-2 carries `FIXME(/backend)` (pre-fix;
  correctly left in code as a marker but the fix has landed — see
  suggestion below). ✓
- **Test-plan rows present**: `tests/plan/ring4.md §Slice 2 branch-b
  outcome` table enumerates T-S2-1 and T-S2-2 with ownership, flip
  triggers, and Wave-2 outcome. ✓

### Test fixture (`exemplar/test-eliminate-contract.cl`, 56 LOC) + repro (`exemplar/repro-slice2.cl`, 83 LOC)

- **Slice 5 I migration debt explicitly tracked**: SPRINT.md §Slice 5
  carries item `I` ("Repro-handoff migration") naming both files,
  with the relocation target (`tests/fixtures/*.cl` or inlined as
  string literals) and the FIXME-update instruction for
  `exemplar/solver.cl:370+`. ✓
- **Current location rationale documented**: per the task brief and
  `memory/feedback_repro_handoff.md` (user directive 2026-04-22), the
  current `exemplar/` location is a Wave-2 expedient; migration lands
  in Slice 5 Wave 5. Not a Wave 2 finding. ✓

### Suggestion on T-S2-2's stale FIXME

- `tests/exemplar_solver_correctness.rs:150 FIXME(/backend)` predates
  the fix. Now that `is_last_use` is gated, the FIXME should be removed
  or converted to a note "Fix landed at `compiler/mod.rs::is_last_use`,
  Sprint 61 Wave 2, commit <pending>". Sub-Important; fold into Slice 5
  G/I cleanup.

## Cross-skill handoff audit

Per `memory/feedback_cross_skill_minimal_repro.md` (user directive Sprint
59 Wave 1) + `memory/feedback_repros_join_suite.md` (permanent repro
preservation):

1. **/port → /qa handoff** (branch-b trigger):
   - Minimal repro shipped: `exemplar/repro-slice2.cl` (< 30 LOC
     excluding license/comments; comment-inclusive ~83 LOC).
     Non-Sudoku, deterministic. ✓
   - Handoff brief in SPRINT.md §Skill Plans Wave 2 → /port: three
     layers named, hypothesis space documented, Layer 3 repro path
     named, sibling-bug caveat flagged ("Layer 3 trigger shape is
     distinct from Layer 2 solver call sites"). ✓
   - /qa narrowed to two cargo tests + one exemplar fixture. T-S2-1
     covers Layer 1 contract via `exemplar/test-eliminate-contract.cl`
     (exit-code protocol). T-S2-2 wraps `exemplar/repro-slice2.cl`
     with stdout assertions. ✓

2. **/qa → /backend handoff**:
   - /qa's two tests were committed FAILING at SHA `b140ec5` per
     ledger. ✓
   - /backend investigated using `CRANELISP_CODEGEN_TRACE=1` (per
     SPRINT.md §Skill Plans Wave 2 → /backend prescription) and
     `/clif try-digits`. Root cause identified as `is_last_use`
     missing `borrowed_vars` gate — a 14-line fix at a single site. ✓
   - Layer 2 resolution noted as "bundled by construction" (same RC
     path, different caller shape) with narrative reasoning in
     SPRINT.md Wave 2 → /backend row. This is acceptable framing but
     slightly informal — a separate Layer 2 regression test under the
     recursive-backtracking shape would be strictly stronger. Not a
     finding this wave because T-S2-1 (Layer 1 contract) implicitly
     exercises the Layer 2 code path on a valid puzzle (the solver
     main invocation in `test-eliminate-contract.cl` touches the
     `try-digits`/`solve` paths; if those regressed, T-S2-1 would
     fail). But a dedicated Layer 2 test would make the regression
     guard explicit. Candidate for Slice 5 J.

3. **Cross-skill protocol per `memory/feedback_cross_skill_minimal_repro.md`**:
   followed. /port did not hand off with only a surface error signature;
   they handed off with an isolated < 30 LOC repro naming the precise
   compiler-layer hypothesis. /backend did not broaden the fix beyond
   the repro-attested site; the one-line gate at `is_last_use` is
   minimal and symmetric with the existing `captured_vars` pattern. ✓

## Review dimensions — all 13 checked

| # | Dimension | Status |
|---|---|---|
| 1 | Design adherence | ✓ (strong, both skills) |
| 2 | Boundary hygiene (Principle 3) | ✓ — no boundary-type changes |
| 3 | Allocator discipline | N/A — fix sites not in trace paths; RC gate adds no new trace emission |
| 4 | Error handling (no unwrap/panic in pipeline) | ✓ — `unwrap`s in new code confined to `#[cfg(test)]`; `Option::expect` only in test harness |
| 5 | Naming (typed identifiers, named constants) | ✓ with S3 caveat (`MAX_DEPTH` could be module-level const) |
| 6 | Function size (max 100 LOC) | ✓ — largest new/modified fn is `resolve_entry_for_display` at 27 LOC; `is_last_use` at 24 LOC |
| 7 | Clippy cleanliness | ✓ — pre-existing issues in `display.rs` / `repl_negative.rs` / `sketch_port.rs` / `vec.rs` / `float.rs` explicitly out of scope per task brief; new code introduces no new lints (visual inspection) |
| 8 | Test hygiene (no `#[ignore]`, no flaky) | ✓ — 0 `#[ignore]` in both new files; `rg 'flaky\|pre-existing\|timing-sensitive' tests/plan/baseline.md` surfaces only the meta-prose forbidding those dispositions |
| 9 | Unit vs integration separation | ✓ — `/int` co-authored 3 unit tests inside `src/session_v4.rs::bare_primitive_value_path_tests`; `/qa` authored 7 integration tests in `tests/` |
| 10 | RC-regression surface | ✓ — fix is a gate that returns earlier; no new RC inc/dec emission |
| 11 | Serial-slice discipline | ✓ — Slice 1 and Slice 2 executed in parallel BUT scoped to different files (`src/session_v4.rs` vs `exemplar/solver.cl` + `compiler/mod.rs`); SPRINT.md §1 explicitly allows this exception |
| 12 | Scope-violation cleanup | ✓ — /backend's out-of-scope `exemplar/solver.cl` edits reverted into `stash@{0}`; /port reapplied Layer 1 in their own voice; no residual /backend voice in working-tree solver.cl |
| 13 | Slice 5 I migration tracked | ✓ — SPRINT.md §Slice 5 carries item I naming `exemplar/repro-slice2.cl` + `exemplar/test-eliminate-contract.cl` with migration target |

## Recommendations to /sprint

1. **Accept the Wave 2 submission as PASS WITH FINDINGS**. Both
   Important findings (I-1 harness duplication, I-2 sketch-comparison
   on §5.5) are sprint-local cleanup candidates, not acceptance
   blockers.

2. **Fold I-1 into Slice 5 /qa sweep** (alongside the existing E-1
   TempDir-per-test rule and G test rename). Creating
   `run_repl_with_stdlib(input, label)` in `tests/helpers/mod.rs` is
   ~15 LOC and unblocks any future stdlib-loaded subprocess test.

3. **Fold I-2 into Slice 5 doc-hygiene pass** (alongside the Wave 1
   S5 field-naming inconsistency `timestamp_ns` vs `timestamp`). One
   paragraph in `ring2-rc.md §5.5` addendum.

4. **Slice 5 I migration is explicit in SPRINT.md** — no change
   needed, just confirm /sprint will not close Wave 5 until the
   migration lands and FIXME block at `exemplar/solver.cl:402–405` is
   updated.

5. **T-S2-2's stale `FIXME(/backend)` at test file line 150** — trivial
   but correct to remove on the Wave 2 commit or fold into Slice 5.
   A stale FIXME on a passing test misleads future readers into
   thinking the fix is pending.

6. **Commit gate** — nothing blocks the Wave 2 commit. /backend's
   crate tests pass 174/174, Slice 1 passes 5/5, Slice 2 passes 2/2,
   workspace is clean (modulo declared out-of-scope clippy baseline).

Wave 2 closes the two deterministic defects (Slice 1 + Slice 2) cleanly
with isolation → fix → verify → commit per the sprint's serial-slice
discipline. The cross-skill repro-narrowing protocol was followed to
the letter; both compiler-skill fixes are minimal and structurally
symmetric with existing patterns. Ship Wave 2.

End of review.
