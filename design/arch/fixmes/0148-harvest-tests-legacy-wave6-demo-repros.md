---
number: 0148
target: /int
filed_by: /qa
filed_at: 2026-05-05
sprint_filed: 64
refers_to: tests/legacy/wave6_demo_repros.rs, tests/repl_persist_race.rs, tests/spec_08_modules.rs, tests/repl_introspection.rs, tests/regression.rs, tests/plan/wave-6-batch-5-audit.md, design/arch/fixmes/0145-harvest-tests-legacy-sprint59-repros.md
status: open
int_reviewed_by: /dev int (S81 W-E)
---

## S81 W-E /dev int review — int-owned portion DISPOSED; carries for /backend + /stdlib + deletion

The two int-owned defects in this file's carry-forward are accounted for:

- **Defect 1 (dep-load race in `compile_dep_inline`)** — the named function
  (`session_v4::compile_dep_inline`) was DELETED in Sprint 59 Workstream A §7;
  the dep-load ordering it guarded is now covered by the S78 in-call-stack
  retry-from-top model and the e2e FQ-autoload / dep-chain + H5-replay suites
  (`tests/repl_persist_race.rs`). No int unit harvest is possible (surface gone)
  or needed (behaviour relocated + e2e-guarded).
- **Defect 3 (`append_docstring_comment` dash separator)** — fully covered at the
  int Rust-API layer by `src/session_v4.rs` `#[cfg(test)] mod format_entry_sig_tests`
  (`format_entry_sig_defn_includes_docstring_after_dash`,
  `format_entry_sig_defn_without_docstring_omits_dash`,
  `format_entry_sig_defn_docstring_uses_first_line_only`). No new int test needed.

**Carries (NOT int):** Defects 4+5 (RC/last-use in the IO-trampoline run-tests
path) → /backend; Defect 6 (solver stack-overflow) → /backend (folds into FIXME
0145, still OPEN); Defect 2 (seq.lazy null-import) → /stdlib (resolved-by-passing-
carry-forward). This FIXME stays open carrying those.

**Eventual deletion (/qa):** once Defect 6 lands, `tests/legacy/wave6_demo_repros.rs`
may be deleted + its README row removed. Not actionable from the int wave.

---

# Harvest tests/legacy/wave6_demo_repros.rs into /int + /backend + /stdlib unit tests

## Issue

Sprint 64 Wave 6 batch 5 quarantined Sprint 58 Wave 6's demo-surfaced
defect repro file:

- `tests/wave6_demo_repros.rs` (495 LOC, 5 tests, one per defect:
  Defect 1 dep-load race, Defect 2 stdlib seq.lazy null-import,
  Defect 3 docstring separator, Defect 4+5 /run-tests batched crash,
  Defect 6 exemplar solver stack-overflow)

All 5 tests carry forward as REGRESSION-GUARDs across **four existing
e2e files** (no new files):

- `tests/repl_persist_race.rs` (extended +1):
  `repl_dep_load_no_race_with_persistent_workers` — Defect 1 race
  guard. Owning skill: /int (session_v4 `compile_dep_inline` ordering
  invariant).
- `tests/spec_08_modules.rs` (extended +1):
  `null_import_module_resolves_all_names_via_explicit_imports` —
  Defect 2 null-import guard. Owning skill: /stdlib (per-module
  import discipline; **resolved-by-passing-carry-forward**).
- `tests/repl_introspection.rs` (extended +1):
  `display_defn_with_docstring_uses_dash_separator` — Defect 3
  display-format guard. Owning skill: /int (`append_docstring_comment`
  format string; **resolved-by-passing-carry-forward**).
- `tests/regression.rs` (extended +2):
  - `wave6_run_tests_batched_html_completes_without_crash` —
    Defects 4+5 batched-crash guard with positive-completion angle.
    Owning skill: /backend (RC / last-use across consecutive
    `run_test_by_name` calls) or /int (`/run-tests` dispatch loop).
    **Stronger than** `regression.rs::d45_real_exemplar_html_run_tests_no_crash`
    (which only checks signal-crash); this version asserts positive
    completion (`test-wrap-tag` + `ok`/`FAILED:` substring).
  - `wave6_exemplar_solver_full_run_does_not_stack_overflow` —
    Defect 6 stack-overflow guard, exercising the **real solver
    entry** (`--run exemplar/solver.cl::main` including IO
    trampolines). **FAILING-NOT-IGNORED** per
    `memory/feedback_failing_not_ignored.md`. Owning skill: /backend
    (deep recursion / Vec COW / stack frame size). Joins the four
    existing failing-not-ignored `d6_exemplar_*` guards in
    `regression.rs §F`.

Total carry-forward: **5 tests across 4 files**. On the binary at
audit time (2026-05-05): **4/5 PASS, 1 FAIL** — the failing test is
`wave6_exemplar_solver_full_run_does_not_stack_overflow` (open
Defect 6 stack-overflow ledger entry, matching the existing
`d6_exemplar_*` cluster behaviour).

## Owner alignment

The five tests fan out across four owning-skills:

- Defect 1 → /int (session_v4 dep-load wiring) — race resolved
- Defect 2 → /stdlib (seq.lazy explicit imports) — fix landed
- Defect 3 → /int (append_docstring_comment format) — fix landed
- Defect 4+5 → /backend (RC/last-use) or /int (run-tests dispatch) —
  combined fix landed
- Defect 6 → /backend (solver recursion) — **OPEN** (cross-references
  parent FIXME 0145)

Per Wave 6 b2/b3/b4 precedent, this FIXME consolidates the entire
file's carry-forward under primary owner `/int` (3/5 tests) with
co-owner `/backend` (Defects 4+5 + 6, the open one) and co-owner
`/stdlib` (Defect 2, already resolved). Cross-reference: existing
**FIXME 0145** (`harvest-tests-legacy-sprint59-repros`) is the parent
harvest scope for Defect 6 — both this FIXME and 0145 cover the same
solver recursion defect cluster. /port has a downstream task (re-
enable disabled solver tests in `exemplar/solver.cl`) once Defect 6
is fixed.

## Inline FIXMEs preserved in legacy/wave6_demo_repros.rs

The legacy file preserves **5 inline `FIXME(/owning-skill)` markers**,
one per defect section banner. Per Wave 6 b2/b3/b4 protocol, they are
preserved verbatim in the quarantined source (read-only post-
quarantine):

- lines 158–161: `FIXME(/int)` — Defect 1 dep-load race fix in
  `compile_dep_inline`. Hypothesis confirmed; fix landed; carry-
  forward passes today. **Resolved-by-passing-carry-forward.**
- lines 219–222: `FIXME(/stdlib)` — Defect 2 add explicit imports to
  `stdlib/seq/lazy.cl`. Fix landed; carry-forward passes today.
  **Resolved-by-passing-carry-forward.**
- lines 279–281: `FIXME(/int)` — Defect 3 `append_docstring_comment`
  format string. Fix landed; carry-forward passes today.
  **Resolved-by-passing-carry-forward.**
- lines 329–332: `FIXME(/backend) or FIXME(/int)` — Defect 4+5 RC /
  last-use issue across consecutive `run_test_by_name` invocations.
  Combined fix landed; carry-forward passes today.
  **Resolved-by-passing-carry-forward.**
- lines 437–443: `FIXME(/backend)` + `FIXME(/port)` — Defect 6 solver
  stack-overflow + re-enable disabled solver tests. **OPEN** defect;
  joins the parent /backend solver-recursion scope under FIXME 0145
  (sibling cluster `d6_exemplar_*` already failing-not-ignored).

When confirmed-resolved at harvest review, each FIXME is deleted from
the legacy file. When all five are confirmed (Defect 6 last), the
legacy file may be deleted in full.

## Spec-link linter findings (pre-port)

Two issues addressed during carry-forward authoring:

- `wave6_demo_repros.rs:163` MIS-CITED — `§Self-documenting REPL` not
  in `CLAUDE.md`. Carry-forward in `repl_persist_race.rs` uses the
  closest concrete anchor: `repl/spec.md §0.2` (Run Mode parity) +
  the implicit-Principle-11 framing.
- `wave6_demo_repros.rs:445` MALFORMED — `implicit (exemplar
  validation)`. Carry-forward in `regression.rs` uses
  `spec/12-runtime.md §12.5` — same anchor as the existing
  `d6_exemplar_*` cluster.

## Proposed resolution

The owning skills review the quarantined file's carry-forward
mapping:

1. **`/int`** verifies that the four `/int`-owned carry-forwards
   (Defects 1, 3 + Defects 4+5 if /int wins the run-tests dispatch
   ownership) have unit-tier counterparts in
   `src/session_v4.rs`/`src/repl.rs` `#[cfg(test)]` modules covering
   the same invariants. Specifically:
   - `compile_dep_inline` ordering: dep_sexps published BEFORE
     scheduler.register_module
   - `append_docstring_comment` format: dash separator between
     classification and docstring
   - `/run-tests` dispatch loop integrity across consecutive
     `run_test_by_name` calls

2. **`/backend`** verifies the Defects 4+5 + Defect 6 carry-forwards
   against current codegen:
   - For Defects 4+5, the surface is RC / last-use accounting in the
     IO-trampoline path used by `run_test_by_name`. Confirm the unit-
     tier counterparts in `crates/cranelisp-backend/src/compiler/builtins.rs`
     + `cranelisp-runtime/src/io_trampoline.rs` cover the
     consecutive-invocation invariant.
   - For Defect 6 (open), this FIXME folds into the existing
     **FIXME 0145** scope. The five existing failing-not-ignored
     `d6_exemplar_*` guards in `regression.rs §F` plus the new
     `wave6_exemplar_solver_full_run_does_not_stack_overflow`
     (six total) define the failure surface. Resolution criteria:
     deep recursion through Vec-copying ADT traversal must terminate
     under default Rust thread stack size (8 MiB) for the canonical
     17-clue puzzle. When fixed, all six carry-forwards become
     passing regression guards and `/port` can re-enable the three
     disabled solver tests in `exemplar/solver.cl`.

3. **`/stdlib`** verifies that `stdlib/seq/lazy.cl` retains the
   explicit imports for `Nil/Cons/Some/None`. The carry-forward
   passes today; this is a regression-guard against future stdlib
   refactors that might re-introduce a bare prelude reference.

4. When all surface is harvested or proven stale (likely after
   Defect 6 resolution), delete
   `tests/legacy/wave6_demo_repros.rs`. Git history preserves
   provenance.

## Operational implication / Context

This batch closes Sprint 64 Wave 6 with the **fifth 100%-GAP-COVER
batch in a row**:

| Batch | Tests | GAP-COVER | DUPLICATE | COVERED | Yield % |
|---|---:|---:|---:|---:|---:|
| b1 | 21 | 21 | 0 | 0 | 100% |
| b2 | 61 | 59 | 2 | 0 | 97% |
| b3 | 36 | 36 | 0 | 0 | 100% |
| b4 | 25 | 25 | 0 | 0 | 100% |
| b5 | 10 | 10 | 0 | 0 | 100% |
| **Wave 6 total** | **153** | **151** | **2** | **0** | **99%** |

Wave 6 closes with 153 carry-forwards across 11 quarantined files,
zero DUPLICATE-IN-LEGACY findings outside b2 (97% yield in b2 alone).
The pattern: regression-named work-product files exhaustively
partition the carry-forward surface — they are presumptively
discriminating and the per-test review converges quickly. Audit's
per-test classification is mechanical once the cluster character is
established.

The most consequential downstream finding from this batch: the
**Defect 6 real-solver-entry carry-forward**
(`wave6_exemplar_solver_full_run_does_not_stack_overflow`) is a
distinct angle from the four existing `d6_exemplar_*` synthetic
single-form repros — it exercises the IO-trampoline path that the
synthetic repros elide. Differential observation: when /backend
resolves the recursion-depth issue, if the synthetic four pass but
the real-solver-entry one still fails, the remaining defect is in
the IO-trampoline interaction (or in the IO-driver thread-stack
sizing).

## Cross-references

- Audit document: `tests/plan/wave-6-batch-5-audit.md`
- Carry-forward sources:
  - `tests/repl_persist_race.rs::repl_dep_load_no_race_with_persistent_workers`
  - `tests/spec_08_modules.rs::null_import_module_resolves_all_names_via_explicit_imports`
  - `tests/repl_introspection.rs::display_defn_with_docstring_uses_dash_separator`
  - `tests/regression.rs::wave6_run_tests_batched_html_completes_without_crash`
  - `tests/regression.rs::wave6_exemplar_solver_full_run_does_not_stack_overflow`
- Sibling carry-forwards from earlier batches:
  - `tests/regression.rs::d45_*` (Wave 6 b3 carries — d45 cluster)
  - `tests/regression.rs::d6_exemplar_*` (Wave 6 b3 carries — Defect 6
    synthetic single-form repros, four failing-not-ignored)
  - `tests/repl_persist_race.rs::heisenbug_race_reduced_concurrent_import_pairs`
    (Wave 6 b2 carry — same race surface family)
- Sister FIXME: 0147 (Wave 6 b5 sprint61_bare_primitive)
- Parent FIXME for Defect 6: 0145 (Wave 6 b3 sprint59 repros)
- Related FIXMEs:
  - 0142 (`int-repl-unclosed-paren-on-eof-silent`) — distinct REPL-eval
    defect; unrelated
  - 0146 (Wave 6 b4 sprint60-trio) — sibling /backend harvest scope
- Source code areas:
  - `src/session_v4.rs::compile_dep_inline` (Defect 1 fix area)
  - `src/session_v4.rs::append_docstring_comment` (Defect 3 fix area)
  - `src/repl.rs::run_test_by_name` (Defects 4+5 dispatch loop)
  - `crates/cranelisp-backend/src/compiler/builtins.rs::compile_vec_op`
    (Defect 6 Vec COW / drop-glue)
  - `cranelisp-runtime/src/io_trampoline.rs` (Defects 4+5 IO path;
    Defect 6 IO-driver stack)
- Design-doc anchors:
  - `repl/spec.md §1.1` (Defect 3 — display format)
  - `repl/spec.md §16.3` (Defects 4+5 — /run-tests semantics)
  - `repl/spec.md §0.2` (Defect 1 — Run Mode parity)
  - `spec/08-modules.md §8.3.6` (Defect 2 — null-import semantics)
  - `spec/12-runtime.md §12.5` (Defect 6 — RC behaviour at depth)
  - `exemplar/CLAUDE.md` "Known Issues" (Defect 6 ledger)
  - `tests/plan/ledger.md` lines 120–131 (Defect 6 ledger entry)
