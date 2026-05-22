# Sprint 69 — /qa Phase 3 Test Plan

**Status**: Phase 3 Design — authored 2026-05-18. Draft for Phase 5 execution.
**Author**: /qa (narrow Sprint 69 deployment)
**Scope**: Drives /qa Phase 5 (failing-tests-first sprint-wide) for Sprint 69.

This document plans the /qa-owned work for Sprint 69 (Category B test
refinements, Category D filter, Category E baseline regeneration, plus
source-side-row test sketches and the audit-driven additions
placeholder for the Wave-1 → Wave-2 gate fill-in). It is subordinate
to `tests/plan/baseline.md`; rows folded back into baseline once
Phase 5 lands them.

---

## 1 — Failing-test inventory

`cargo nextest run --no-fail-fast` against the full workspace exceeded
the 30s sprint-cap (581s before SIGINT at 599/1078 tests; 559 passed,
40 failed, 6 skipped). The slow time was dominated by:

- `public_api_relocations.rs::public_api_check_runs_against_all_seven_crates` — SLOW > 240s (subprocess-runs `cargo +nightly public-api` × 7 crates; each spawns `rustdoc --output-format json` which is slow on first run).
- `link::*` (7 tests, ~131s each) and `got_trace::*` (3 tests, ~131s each) — each carries an internal 30s subprocess timeout that fires under load contention.
- `repl_persist::*` cluster (~50s per test) — multi-session restart fixtures.

Narrowed re-run targeting just the three S69 conformance tests
(`facade_compliance`, `facade_pif_rows`, `public_api_relocations`)
completed in 12.5s: 14 tests, 8 passed, 6 failed. Per
`memory/feedback_time_test_runs.md`: record this baseline so future
S69 phases do **not** invoke workspace-wide nextest; narrow to the
relevant binaries first.

### Classification

#### (a) Closed by Sprint 69 source-side work (rows 7, 21, rev3, audit findings)

| Failing test | Sprint 69 row / source-side work |
|---|---|
| `facade_pif_rows::row_07_operators_module_retired_from_backend` | Row 7 (`/dev backend`) — but **needs reframing** per /design backend audit, see §5 |
| `facade_pif_rows::row_21_typecheck_env_narrowed_to_facade_two_methods` | Row 21 (atomic `/dev typecheck + int`) |

**Note: rev3 currently PASSES** (0.96s) — the `/info add-i64` runs
through cleanly in the narrowed test. The 30s timeout described in
SPRINT.md §"Category A" + the int audit's rev3 hypothesis is **not
reproducing** in the current workspace state. /qa SHOULD verify this
in Wave 2 before assuming the rev3 row is closeable as-is; if
PASS-on-narrow but FAIL-on-workspace, that itself is a finding.

#### (b) Closed by Sprint 69 test-side work (Category B + D + row_27 restructure)

| Failing test | Category B / D resolution |
|---|---|
| `facade_pif_rows::row_01_code_enum_named_in_backend_pub_api` | Category B — accept `#[non_exhaustive]` prefix |
| `facade_pif_rows::row_05_linker_error_enum_named_in_backend_pub_api` | Category B — same |
| `facade_pif_rows::rows_02_03_compilation_error_enum_named_in_backend_pub_api` | Category B — same |
| `facade_pif_rows::rows_03_04_linker_and_object_artefact_named_in_backend_pub_api` | Category B — same (for `pub struct`) |
| `facade_pif_rows::row_27_primitives_string_vec_physically_owned_by_primitives_not_reexported` | Category B — structural rewrite per /arch Q1 (D0048 mismatch) |
| `facade_compliance::facade_compliance_orphans_match_expected_sprint_67_baseline` | Category D1 — extend filter to drop ALIGN / Output / Owned |
| `facade_pif_rows::shared_state_field_count_matches_facade_after_pif` | Reported in the narrowed re-run but **not in S69 scope per SPRINT.md** — pre-existing S67 PIF residue (FIXME 0176 broader scope). **Flag for /sprint**: surface that this test fails today even though SPRINT.md only lists 6 facade-pif failures; either accept it as a known pre-existing failure or scope-add it. |

#### (c) Pre-existing carry — out of scope per SPRINT.md

| Failing test cluster | Pre-existing carry / FIXME |
|---|---|
| `build_confidence::mode_equiv_pattern_match_nested` | Pre-existing — pattern-match-nested-mode parity carry |
| `build_confidence::perf_simple_eval_latency_under_2000ms` | Pre-existing perf budget gap (3.3s actual vs 2.0s ceiling) — orthogonal |
| `cache::cache_multi_module_transitive_imports` | Pre-existing cache carry |
| `link::link_*` (7 tests) | Pre-existing `--link` mode carries; timing-sensitive 30s subprocess waits — likely FIXME 0145 / 0148 territory |
| `got_trace::got_trace_*` (3 tests) | Pre-existing GOT-observer carries; tied to FIXME 0099 (GotObserver implementation) — out of S69 scope |
| `repl_persist::persist_bug1_constrained_polymorphic_fn_callable_after_restart` | Pre-existing constrained-poly persistence carry |
| `repl_persist::persist_bug_macro_usage_in_defn_survives_session_restart` | Pre-existing macro-persistence carry (FIXME 0181 cross-module macro 3-module stack-overflow territory) |

#### (d) Other / flag for /sprint

| Issue | Detail |
|---|---|
| Workspace-wide nextest exceeds 30s cap | The S69 mechanical-conformance tests + the existing pre-existing-carry cluster + the slow `public-api` subprocess test multiplied by `--no-fail-fast` create a 581s total. /qa Phase 5 SHOULD run targeted subsets per `feedback_test_confidence.md`. **Flag for /sprint**: workspace nextest is **not** a viable single-shot gate for S69; per-binary nextest runs are. |
| `shared_state_field_count_matches_facade_after_pif` failure | SPRINT.md only names 6 PIF failures; the narrowed re-run shows 7 (including this one). May indicate pre-existing carry not enumerated, or test failing for a different reason than design intent. Flag for /sprint. |
| `public_api_relocations` test runtime (240s+) | The full 7-crate `cargo +nightly public-api --diff` chain dominates total runtime. Consider per-crate split or `#[ignore]` + targeted run only on edge changes. Out of S69 scope but a /sprint observation. |

---

## 2 — Category B — PIF assertion refinements

Per /arch Q1 + SPRINT.md §"Category B". File: `tests/facade_pif_rows.rs`.

### B.1 — Enum prefix relaxation (rows 1, 2/3, 5)

The three enum-name tests assert `line.starts_with("pub enum ")`,
which mis-matches against `cargo public-api`'s
`#[non_exhaustive] pub enum …` line shape. Verified in baseline:
backend's `Code`, `CompilationError`, `LinkerError` all carry
`#[non_exhaustive]` per Principle 14.

| Row | File:line of current assertion | Proposed change |
|---|---|---|
| row_01 (`Code`) | `tests/facade_pif_rows.rs:59-63` | Replace `line.starts_with("pub enum ")` with `(line.starts_with("pub enum ") || line.starts_with("#[non_exhaustive] pub enum "))` — preserve the substantive `pub enum` + crate + leaf-name assertion. |
| rows_02_03 (`CompilationError`) | `tests/facade_pif_rows.rs:84-88` | Same |
| row_05 (`LinkerError`) | `tests/facade_pif_rows.rs:101-105` | Same |

**Idiom**: extract a helper `fn is_pub_enum_decl(line: &str, leaf: &str, crate_prefix: &str) -> bool` and use it across all three rows + future tests. Keeps the relaxation DRY.

### B.2 — Struct prefix relaxation (rows 3/4)

| Row | File:line | Proposed change |
|---|---|---|
| rows_03_04 (`LinkerArtefact` + `ObjectArtefact`) | `tests/facade_pif_rows.rs:120-129` | Replace `line.starts_with("pub struct ")` with `(line.starts_with("pub struct ") || line.starts_with("#[non_exhaustive] pub struct "))`. Per /design backend audit §"Shape drift" both structs carry `#[non_exhaustive]`. |

**Idiom**: parallel helper `fn is_pub_struct_decl(line: &str, leaf: &str, crate_prefix: &str) -> bool`.

### B.3 — Row 27 structural rewrite (per /arch Q1 + Decision 0048)

The current `row_27_primitives_string_vec_physically_owned_by_primitives_not_reexported` test (lines 267-315) asserts `str_helpers_in_primitives > 0` by grepping `pub` against names like `str_concat`/`vec_len`. Per Decision 0048 those fns are `pub(crate) extern "C"` with `#[unsafe(export_name = "…")]`, and so do **not** appear in primitives' `public-api.txt`. The current test is structurally incompatible with the design target.

**Proposed replacement** (file:line: `tests/facade_pif_rows.rs:267-315`):

```rust
// Replace the body with two independent assertions:
// (a) zero `cranelisp_intrinsics::{string,vec}::*` items in intrinsics pub-api
//     — already true per /arch Q1 verification + intrinsics audit
// (b) primitives-side presence via:
//     (b1) `crates/cranelisp-primitives/public-api.txt` contains
//          `pub static PRIMITIVES_TABLE` (already covered by row_26 but
//          treat as a precondition here for self-containedness), AND
//     (b2) filesystem existence of `crates/cranelisp-primitives/src/string.rs`
//          AND `crates/cranelisp-primitives/src/vec.rs`.
// NOT via `pub` extern-fn enumeration — that contradicts Decision 0048.
```

Spec citation: `design/arch/facades/primitives.md §"Public surface"` + Decision 0048 §"Structural invariant".

`// spec: design/arch/facades/primitives.md §"Public surface"` retained; `// FIXME(...)` comment updated to point at completion (no /dev work required — restructure is /qa-only). Test name renamed to `row_27_primitives_string_vec_owned_per_d0048` for clarity, OR the existing name preserved for diff-friendliness — /qa picks at Wave 2.

### B.4 — Helper extraction (recommended)

Bundle B.1, B.2, B.3 in one Wave 2 /qa commit. The helpers extracted in B.1+B.2 (`is_pub_enum_decl`, `is_pub_struct_decl`) become reusable for future PIF row tests; the row_27 rewrite is independent but lands in the same commit.

**Estimated diff size**: ~30 LOC additions in `tests/facade_pif_rows.rs`; net change might be a slight decrease since row_27's body shrinks materially.

---

## 3 — Category D — orphan-filter refinement (D1, user-arbitrated)

File: `tests/facade_compliance.rs`, fn `extract_names()` (current at lines 89-208).

Target lines: same baseline that produces the 3-orphan failure (`ALIGN`, `Output`, `Owned`). Per SPRINT.md §"Category D":

> "extend the filter in `tests/facade_compliance.rs::extract_names()` to drop lines matching `pub const … ::ALIGN`, `pub type … ::Output = T`, `pub type … ::Owned = T`. ~5 LOC test change."

### D.1 — Filter additions

In the existing skip-block (current lines 113-133, the `if l.starts_with("impl core::") || …` block) add a third sub-block analogous to the auto-derived-impl block + the `pub type … ::Target = …` line at line 157:

```rust
// New filter — to be inserted after the existing
// `pub fn ::clone(` filter (current line 137) or as a
// sibling to the `::Target = ` filter (current line 157):

// `pub const cranelisp_…::Foo::ALIGN: usize` — every type marked
// `cranelift_module::ALIGN`-aware emits this. Auto-generated.
if l.starts_with("pub const ") && l.contains("::ALIGN") {
    return out;
}
// `pub type cranelisp_…::Foo::Output = T` — From<T> blanket impl projection.
// `pub type cranelisp_…::Foo::Owned = T` — Borrow<T> blanket impl projection.
if l.starts_with("pub type ")
    && (l.contains("::Output = T") || l.contains("::Owned = T"))
{
    return out;
}
```

### D.2 — Expected post-filter state

After D.1 lands, `facade_compliance_orphans_match_expected_sprint_67_baseline`'s
backend orphan count drops from 3 → 0. Other crates already at 0 per the
current run output. Total orphans become 0; the test flips green.

### D.3 — Spec link

Add a brief comment block above the new filter pointing at SPRINT.md
§"Category D" + the intrinsics audit §"Unannounced surface" point 3
(same class of finding for `HeapString` / `IoEvent` / `IoEventTag`
auto-trait projections — D1 filter is the global fix).

---

## 4 — Category E — baseline regeneration

Per S68 Finding 5 + the user-direction "regenerate all 8 baselines at the top of the sprint and note any pre-existing drift, so subsequent /dev work isn't surprised by drift from other crates" (SPRINT.md §"Notes"):

### E.1 — Command sequence (order-independent; 8 crates)

```bash
# Pre-requisite: rustup nightly + cargo-public-api installed
cargo +nightly public-api --simplified --manifest-path crates/cranelisp-types/Cargo.toml > crates/cranelisp-types/public-api.txt
cargo +nightly public-api --simplified --manifest-path crates/cranelisp-frontend/Cargo.toml > crates/cranelisp-frontend/public-api.txt
cargo +nightly public-api --simplified --manifest-path crates/cranelisp-typecheck/Cargo.toml > crates/cranelisp-typecheck/public-api.txt
cargo +nightly public-api --simplified --manifest-path crates/cranelisp-backend/Cargo.toml > crates/cranelisp-backend/public-api.txt
cargo +nightly public-api --simplified --manifest-path crates/cranelisp-primitives/Cargo.toml > crates/cranelisp-primitives/public-api.txt
cargo +nightly public-api --simplified --manifest-path crates/cranelisp-intrinsics/Cargo.toml > crates/cranelisp-intrinsics/public-api.txt
cargo +nightly public-api --simplified --manifest-path crates/cranelisp-platform/Cargo.toml > crates/cranelisp-platform/public-api.txt
cargo +nightly public-api --simplified --manifest-path crates/cranelisp-exe-bundle/Cargo.toml > crates/cranelisp-exe-bundle/public-api.txt
```

(8 baselines. Order is irrelevant; can be parallelised via shell `&` + `wait`. Each takes ~10-30s depending on cache state.)

### E.2 — When this runs

Per S68 Finding 5: **at sprint open** (the very first action of Phase 5, before any /dev work fires). Co-land with each /dev commit per the Baseline-Diff Discipline in `design/arch/CLAUDE.md §"Baseline-diff discipline"`. The Wave 2 regen is the workspace-wide reset; subsequent /dev work regenerates only the crate it touches.

### E.3 — Pre-existing drift expectation

SPRINT.md notes "Backend baseline drift (1048 line diff — auto-trait projections and pre-existing relocations)" — verify post-regen that the diff settles. /design backend audit §"Deferred" confirms the 1048-line diff is auto-trait-projection noise + the four shape-drift items, all expected.

### E.4 — Ownership

Per `tests/CLAUDE.md §"Public-API enforcement"`: `/dev` (per crate) regenerates as part of the implementing change-set. The Wave 2 sprint-open regen is /qa's mechanical orchestration (no facade or source semantics decided by /qa — just the file refresh). /design verifies each diff matches the audit memo; /review confirms diff alongside facade diff at PR time.

---

## 5 — Source-side row test sketches

For each of rows 7, 21, rev3: what assertion will validate the fix.

### Row 7 — `primitives_inline.rs` reframing (per /design backend audit)

**Audit re-frames the row**: SPRINT.md says "delete the file"; the audit (§"Row 7 readiness") says **no file deletion required**. The remaining inhabitants (`is_known_builtin`, `try_emit_inline_primitive`) are the legitimate name-keyed-shortcut optimisation the facade authorises; the only file-level deletion that was needed (`primitive_for_trait_method`) already happened in S67 W4. The Wave 3 work is **audit + facade narrative close**:

1. Verify every name `is_known_builtin` returns true for has a corresponding `ModuleEntry::Def` in `PRIMITIVES_TABLE`.
2. Verify the inline emission is byte-equivalent to (or strictly faster than) the GOT-indirect path.
3. Update `facades/backend.md` §"`primitives_inline.rs` retirement narrative" to mark D43 close-out as **done**.

**Test sketch — replace current `row_07_operators_module_retired_from_backend`**:

The current test asserts `!path_primitives_inline` (i.e., the file must not exist). Per the audit this is the wrong target. Replace with two assertions:

(a) `crates/cranelisp-backend/src/primitives_inline.rs` may exist, but
the test asserts that `pub fn primitive_for_trait_method` is absent
(grep returns no hits) — already verified in the audit (S67 W4
deletion confirmed). Spec citation: `facades/backend.md §"Forbidden patterns"`.

(b) For every name in `is_known_builtin`'s match arms (extracted via
a build script or via `cargo expand`), assert a corresponding entry
exists in `PRIMITIVES_TABLE` via a `cargo nextest`-runnable test that
includes a tiny build artefact listing the `is_known_builtin`
names. This is a **structural conformance test** that survives
future is_known_builtin additions: any added name without a
`PRIMITIVES_TABLE` entry fails.

**Alternative**: simpler one-off test — assert `crates/cranelisp-backend/src/operators.rs` is absent (currently true) AND `crates/cranelisp-backend/src/primitives_inline.rs` exists but is < 400 LOC (sanity check that scope hasn't ballooned). Mark `// FIXME(/dev backend)` to track the audit conformance work as a per-Wave-3 line item rather than a test gate.

**Recommendation**: pick the alternative for Sprint 69 (simpler, tracks the audit's actual deliverable — narrative close not deletion). Renames the test to `row_07_primitives_inline_residue_within_bounds`.

### Row 21 — `TypeCheckEnv` narrowing (5 methods, not 12)

Per /design typecheck audit: 7 methods are currently pub; 2 are the target; **5 to narrow** (not 12 — FIXME 0187 has Phase A 7/12 already complete). The 5: `ensure_module_exists`, `register_imports`, `register_exports`, `snapshot`, `restore`.

**Current test** (`tests/facade_pif_rows.rs:216-238`) asserts `methods.len() <= 4`. With 7 currently pub, fails today. Post-Wave-3 narrowing, methods.len() drops to 2 (the facade target). The `<= 4` slack is fine.

**Test sketch — no test edit required for the happy path**. The current assertion is correct in shape; it flips green when /dev (typecheck + int atomic brief) lands. **However**, /qa SHOULD strengthen the test for the final state:

- Add a stricter sub-assertion: `methods.len() == 2` (exact match to facade target) with the 5 specific narrowing victims listed in the panic message. This makes the test a regression guard against future `pub`-leakage on `TypeCheckEnv`.
- OR add a negative-coverage sibling test `row_21_neg_no_snapshot_restore_register_in_typecheck_pub_api` that explicitly asserts NONE of `snapshot`, `restore`, `register_imports`, `register_exports`, `ensure_module_exists` appear in `pub fn ::TypeCheckEnv` lines.

**Recommendation**: ship row_21 as-is for sprint close (flips green on Wave 3 atomic brief); add the negative-coverage sibling in a follow-up Wave 2 /qa commit. Spec citation `facades/typecheck.md §"Cluster check scaffolding"`.

### rev3 — `describe_symbol` routing (per /design int audit)

Per /design int audit §"rev3 hypothesis": the 30s timeout's likely cause is `wait_for_inmem` against a `Code::Primitive` symbol (no `notify_inmem_codegen_complete` ever fires for the always-ready marker variant). Two candidate fixes: (a) short-circuit `wait_for_inmem(fq)` against primitives-module symbols (primary), (b) `describe_symbol` fallback to `ModuleFullPath::primitives()` not just root `""` (cleanup).

**Current test** (`tests/facade_pif_rows.rs:592-617`) runs `/info add-i64` against `PreludeVariant::PrimitivesOnly` and asserts the output contains `primitive` or `primitives/add-i64` or `add-i64`. **This test PASSES on the current narrowed nextest run (0.96s) — not 30s**. The 30s ceiling described in SPRINT.md is **not reproducing** today.

This is an important finding: either (a) the rev3 hypothesis has been resolved upstream since SPRINT.md was authored (e.g., during /design audit-driven session), or (b) the failure is workspace-context-dependent (e.g., only fires when prelude is fully loaded, or only in particular module-cache states).

**Test sketch**:

(a) **Keep the current assertion** but **add a deeper one** that exercises the bare-eval path (the int audit's "secondary" candidate failure mode): `/info` then `add-i64` as a bare reference (no `/info` prefix) — the latter goes through the eval / codegen / `wait_for_inmem` path that the audit's primary hypothesis points at. If the bare-reference test reproduces the 30s timeout, /qa has the durable repro.

(b) Per `feedback_repros_join_suite.md`: if reduction lands but the bug doesn't, the partial-reduction test ships anyway. Currently both signals pass — /qa should note this in the Wave 2 commit and leave the strengthened test in place as a regression guard.

(c) Add a 5-second cargo-nextest-side timeout via the test itself
(`std::time::Instant::now()` start + assert duration < 5s) — this is the
cleanest e2e signal for "the 30s wait_for_inmem path is not hit".

Spec citation `facades/int.md §"Composed introspection flows"` retained; new `// spec:` for the bare-reference test should also cite `decisions/0048-primitives-static-symboltable-and-got-in-crate.md §"Structural invariant"`.

**Recommendation**: pre-Phase-5 sanity check — re-run rev3 with workspace prelude + after the Category E baseline regen. If it still passes, the durable signal is the timing-bound assertion (c). If it fails post-regen, the primary fix (audit's wait_for_inmem short-circuit) lands in Wave 3 /dev (int).

---

## 6 — Audit-driven test additions placeholder (Wave 1 → Wave 2 gate)

The 8 close-reading audits (committed 2026-05-18) surface drift that the
3 mechanical tests cannot catch. /sprint's user-checkpoint gate at end
of Wave 1 will surface scope additions; /qa fills this section in
during the gate.

### 6.1 — Pre-fill from already-read audits

The audits I have read (backend, typecheck, int, types) suggest the following candidate tests. Final selection happens at the gate.

#### From backend audit
- §"Coverage holes" item 2: `CodeFinalizer` trait method signatures (`finalize_for_code_read`, `try_get_finalized_function`, `define_module_got_data`). Currently the substring grep catches the names but not the shape. **Candidate**: a per-method shape assertion against the baseline. Out of S69 scope per audit's "Wave 2 facade-doc work" disposition.
- §"Shape drift" `Code` variant `{ jit, ptr }` vs facade target `Arc<Jit>`: facade-doc lag, not test. No test addition.

#### From typecheck audit
- §"Watch items (b) P17-1": `checker.rs:1991`'s `all_type_defs_map` iteration — pending caller audit. If found to be `check_forms`-internal, that's a Principle 17 violation. **Candidate negative test**: assert `all_type_defs_map` callers are session-layer only. Defer to Wave 3 /dev (typecheck) per audit recommendation.
- Audit confirms 7 (not 12) methods pub; `row_21` test threshold is correct.

#### From int audit
- §"Coverage holes" C2: `Code::Primitive` null-handling in int's `c.ptr() as i64` consumers. **Candidate**: a `--run` mode test that exercises every match site with a primitive-only program. Out of S69 unless rev3 surfaces a sweep.
- §"Coverage holes" C1: slash-command set enumeration (22 commands). Audit defers to /qa's behavioural e2e suite. No new test needed in S69.

#### From types audit
- §"Coverage holes" C-HOLE-1, C-HOLE-2: crate-root re-export set + field-type compliance. Audit defers to FIXME 0223 (S70+). No new test in S69.
- §"Verdict — SUBSTANTIAL DRIFT": the surface is right, the details have moved. /qa flags this for /sprint: the **types audit is the heavyweight** — facade-doc Wave 2 work is bulk (22 named facade-doc updates per the audit's §"Wave 2 facade-doc work"). The 9 deferred FIXMEs (0216–0224) explicitly named for S70+ confirm the bulk does NOT land in S69.

#### From the 4 audits not deep-read here (primitives, intrinsics, frontend, platform)
- Per quick scan all 4 have verdict SMALL DRIFT (or NO DRIFT for frontend). All work is Wave 2 facade-doc, none surface new /qa test work.
- Intrinsics audit §"Unannounced surface" item 3 explicitly flags `HeapString`/`IoEvent`/`IoEventTag` auto-trait projections as "covered by /qa's Category D1 filter extension" — the D1 filter additions I plan in §3 above cover this finding automatically.

### 6.2 — Gate questions for /sprint

At the Wave 1 → Wave 2 gate, the user-arbitrated decision points are:

1. Does the rev3 PASS-on-narrow finding (§5 row 3) constitute closure for the rev3 row, or does Wave 3 still need a /dev (int) fix? **Recommendation**: schedule the audit's `wait_for_inmem` short-circuit as a Wave 3 /dev (int) carry even if rev3 currently passes — the underlying lifecycle bug per the int audit is real and would surface differently in future.
2. Does `shared_state_field_count_matches_facade_after_pif` (now failing, not in SPRINT.md's enumerated 6 failures) get added to S69 scope, or accepted as a pre-existing carry?
3. Does the row 7 reframing (audit's "no deletion") get the test renamed + assertion changed (§5 row 1, my recommendation), or is the current assertion kept failing as a forcing function on the facade narrative update?

---

## 7 — Test plan summary table

| Section | File(s) touched | Owner | Wave |
|---|---|---|---|
| §2 B.1+B.2+B.3 — PIF assertion refinements | `tests/facade_pif_rows.rs:59-63, 84-88, 101-105, 120-129, 267-315` | /qa | 2 |
| §3 D.1 — Filter additions | `tests/facade_compliance.rs:89-208` (extend `extract_names`) | /qa | 2 |
| §4 E.1 — Baseline regen × 8 | `crates/cranelisp-*/public-api.txt` (8 files) | /qa orchestrates; /dev co-lands subsequent edits | 2 (sprint open) |
| §5 Row 7 — test reframe + facade work | `tests/facade_pif_rows.rs:168-207` (reframe) + `facades/backend.md §"primitives_inline.rs retirement"` (/design backend) | /qa + /design backend | 2 |
| §5 Row 21 — strengthen | `tests/facade_pif_rows.rs:216-238` (tighten + add neg sibling) | /qa | 2 (post-Wave-3) |
| §5 rev3 — strengthen + timing-bound | `tests/facade_pif_rows.rs:592-617` (extend + timing) | /qa | 2 |
| §6 Audit-driven additions | TBD at gate | /qa | 2 (fills at gate) |

---

## 8 — Cross-references

- `sprints/SPRINT.md` — Sprint 69 master plan (Phase 3)
- `design/arch/facades/{crate}-audit-s69.md` — the 8 audit memos
- `design/arch/CLAUDE.md §"Baseline-diff discipline"` — co-land facade + baseline
- `tests/CLAUDE.md §"Public-API enforcement"` — triad ownership
- `tests/plan/baseline.md` — normative baseline; this plan folds back into it post-Phase-5
- `memory/feedback_failing_not_ignored.md` — the failing-not-ignored discipline
- `memory/feedback_time_test_runs.md` — workspace nextest cost data
- `memory/feedback_repros_join_suite.md` — partial reductions ship even when fix doesn't

---

**End of Sprint 69 /qa Phase 3 Test Plan**
