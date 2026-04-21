# Sprint 60 Wave 1 — /review Report

**Reviewer**: /review
**Verdict**: **PASS**
**Scope**: All Wave 1 deliverables per `sprints/SPRINT.md` §Wave 1 — Workstreams B, C, E-1/E-2/E-3, F (rescoped), G, W cleanup, plus /qa integration tests and H annotation promotions.

## Summary

- **Blockers**: 0
- **Importants**: 1 (I-1: tests/sprint60/ .gitignore omission — cosmetic, matches the Sprint-59 pattern)
- **Suggestions**: 4

The three Sprint-59 /review Importants (I-1/I-2/I-3) are all genuinely resolved. /arch Condition 3 compliance is explicitly documented inline at the targeted location. Wave 1 meets its expected test flip: baseline is **1803 passed / 12 failed** (vs. expected ~1792/14), all 12 failures are the A-carry cluster scheduled for Wave 2.

## Blockers (B)

None.

## Important (I)

1. **`tests/sprint60/` scratch artefact directory lacks a `.gitignore` entry.** `tests/sprint60_observability.rs` writes to `tests/sprint60/.runs/` at line 31–35 (same pattern `tests/sprint59/` used). The `tests/sprint59/.runs/` entry was added post-close in commit `3b2df72` ("sprint 59 post-close: untrack tests/sprint59/.runs/ scratch artefacts"). Sprint 60 repeats the pattern but not the ignore. **Recommend fix in-sprint**: add `tests/sprint60/.runs/` to `.gitignore` before close to avoid the post-close re-untrack commit. Owning skill: `/qa`. One-line addition.

## Suggestions (S)

1. **`register_transitive_cached_imports` migration — `let _ = dep_sexps` dead binding**. `src/worker.rs:1677` binds the shim's return value only to discard it, because the shim has already published into `shared.module_sexps`. The `let _ =` with explanatory comment is clear but the pattern `if let Err(_) = ... { continue }` → then unused `Ok(s)` on the previous line could be simplified with `if register_dep(...).is_err() { continue }` once the caller doesn't use `dep_sexps`. Minor readability nit; defer.

2. **`register_dep_for_eval` test (`register_dep_shim_publishes_before_caller_registers`) does NOT actually call `register_dep_for_eval`** — the comment at `src/session_v4.rs:4348-4352` acknowledges the test "directly exercise[s] the shim's publish+register steps manually in the same order they occur in the function body." This is NOT a guard on the function's behaviour — the function could regress to `publish AFTER register` and this test would still pass because it inlines the ordering. The `debug_assert!` at line 1328 is the real runtime guard; the E-2 deterministic test (`register_dep_for_eval_uses_delays_other_true`) covers the pool invariant. **Suggestion**: rename this test from `register_dep_shim_publishes_before_caller_registers` to `register_dep_for_eval_publish_then_register_is_observable_to_downstream` (or similar) to accurately describe what it tests — the invariant property, not the function's implementation. Without this rename a future reader expects the test to break if the function is accidentally reordered, and will be surprised it does not. Owning skill: `/int`. Documentation-level fix; defer.

3. **`write_clif_dump` writes directly to stderr with an ignored `Result`**. `crates/cranelisp-backend/src/lib.rs:540-546` — the `let _ =` on the `write_clif_dump` call and the rationale comment ("stderr failure is not worth poisoning a codegen result over") are correct, but the `write!`/`writeln!` calls inside the helper return `io::Result` that is threaded through `?` and then silently discarded at the call site. The helper itself is correctly written. This is a style note only — the discard is justified. No action.

4. **`stdlib/CLAUDE.md` table row formatting**. The new "Primitives (30, re-exported from `primitives` for `--run` parity...)" row is a single long paragraph under the existing "Macros" row in the "Available after prelude load" list. For consistency with the preceding bullet structure (Traits/Types/Functions/Macros each on its own line), the primitives row fits but the inline parenthetical with a design-doc ref bloats the line. Consider a second paragraph or a footnote. Defer.

## Sprint-59 Important resolution audit

**I-1 (`register_transitive_cached_imports` migration to shim)** — **RESOLVED.** `src/worker.rs:1653-1681` routes the cache-miss branch through `register_dep`. Source-hash recording + file_to_module update now happen inside the shim (previously inlined), preserving publish-before-register. `grep scheduler.register_module src/` confirms 5 worker-side sites (1268, 1684, 1755, 1838, 2326) all pass `true`, and the only `false` sites are entry-module registration points (scheduler.rs:1726, session_v4.rs:1204, 1273) which are structurally distinct. No 6th per-dep prologue site survives.

**I-2 (`delays_other` divergence)** — **RESOLVED.** `src/session_v4.rs:1335` flips `false` → `true`. Rationale is documented inline at lines 1313–1326 (and formally in `design/int/dual-path-persistence-collapse.md §8.2`). `debug_assert!` at line 1328 guards the publish-before-register invariant. The FIXME(/int) comment on this line is fully removed.

**I-3 (unit guard restoration)** — **RESOLVED.** Two new tests land in `src/session_v4.rs::persistent_worker_tests`:
- `register_dep_shim_publishes_before_caller_registers` (lines 4355–4405) — structural publish+register invariant, widened to `is_some()` after flakiness (see Suggestion 2 about naming).
- `register_dep_for_eval_uses_delays_other_true` (lines 4415–4445) — **deterministic** E-2 pool-placement invariant using standalone `CompileScheduler`. This is the sufficient coverage for the pool invariant: it uses no worker threads, uses the raw `scheduler.register_module(_, true)` call (mirroring line 1335), and asserts `ModulePool::TypecheckFirst` — plus a negative assertion that `false` produces `TypecheckNext`. The widening of the first test to `is_some()` is therefore CORRECT: the pool invariant is deterministically guarded by the second test, and the first test covers the publish+register ordering without racing worker threads.

Additionally, `debug_assert!`s inside both `register_dep` (worker.rs:1372–1384) and `register_dep_for_eval` (session_v4.rs:1328–1334) catch reordering accidents in dev/test runs, fulfilling the structural guard role the deleted unit test previously held.

## /arch Condition 3 compliance on Workstream C

**CONFIRMED.** Two inline documentation sites clarify "additional, not substitute":

1. `crates/cranelisp-backend/src/cache/mod.rs:56-74` — docstring on `pub const BUILD_ID: &str`: "**This is an ADDITIONAL cache-invalidation trigger, not a substitute for the manual `CACHE_SCHEMA_VERSION` bump that Decision 34 requires…** Both triggers coexist…"
2. `crates/cranelisp-backend/build.rs:1-14` — header comment on build.rs: "This is an **additional** invalidation trigger; the Decision 34 manual-bump discipline on serialised-shape changes is unchanged."

Additionally, the test `schema_mismatch_shadows_build_id_mismatch` (`cache/serialize.rs:725-742`) encodes the check-order discipline — schema check fires first, build-id check second — making the "both coexist, schema strictly subsumes" relationship mechanically enforceable. Condition 3 is satisfied beyond the minimum (commit message + comment); the test itself enshrines the semantic.

## Decision 24 / RC convention and Decision 31 / carry-forward checks

- **Decision 24 (RC consuming convention)**: No new CLIF emission or extern-boundary code in Wave 1. Workstream B dumps CLIF *after* codegen (read-only observability); Workstream C operates in `.meta.json` serialisation (no runtime boundary). No finding.
- **Decision 31 (carry-forward invariant at `program.rs:2184-2232`)**: E-1/E-2 operate upstream of the upsert site; they change publish-then-register ordering and pool assignment, not GOT/`Code` population. Carry-forward semantics are untouched. Verified by inspection. No finding.

## Structural debts check

- **Long functions**: `register_transitive_cached_imports` (pre-migration ~80 LOC of prologue inline, post-migration ~40 LOC of orchestration) SHRANK — a win. `format_entry_sig` (unchanged in size, one line changed). No new god functions.
- **Parameter counts**: `register_dep` 4 params + error closure — unchanged from Sprint 59. No growth.
- **Duplicate logic**: Workstream E-1 specifically eliminates duplication (5th→6th site consolidation). Workstream B extracts `clif_dump_matches` + `write_clif_dump` as small, testable helpers — not expanded inline.
- **String-based dispatch**: CLIF-dump filter parses `"module::symbol"` as a string, but this is a user-facing env var surface with a published grammar documented in both the lib.rs header and the unit tests. Acceptable for CLI/env-var surfaces (mirrored by `CRANELISP_RC_TRACE` etc.).
- **God-object re-emergence**: None. All changes are localised to one module each.

## Unsafe code audit

No new `unsafe` blocks in Wave 1. Existing `unsafe` is untouched.

## Test results

**Current baseline**: 1803 passed / 12 failed / 0 ignored (vs. expected ~1792/14). Failures are entirely the A-carry cluster:
- 7 × `sprint59_defects456_repro::d45_*`
- 3 × `sprint59_defects456_repro::d6_*`
- 2 × `wave6_demo_repros` (run_tests_batched, exemplar_solver_stack_overflow)

Wave 1 has flipped ~3 extra tests green beyond the baseline expectation. No Wave-1-caused regressions. No `#[ignore]` introduced.

## Test quality check on new test files

- `tests/sprint60_observability.rs` (182 LOC, 4 tests) — subprocess-level env-var plumbing check. Uses `binary_path()` + stdin-piped source. Appropriate layer (E2E per `tests/CLAUDE.md` Layer 4). Good.
- `tests/sprint60_cache_build_marker.rs` (261 LOC, 3 tests) — cache round-trip + stale-build-id + missing-field-routes-stale. Good coverage.
- `tests/examples_run.rs` (186 LOC) — rewritten post-rescope for spec-correct assertion of `examples/Cranelisp.toml + examples/lib/prelude.cl` via `cargo run -- --run`. Correctly enforces Stdlib-separation principle.
- Unit tests: 6 CLIF-dump + 6 cache build-id + 3 format_entry_sig = **15 new unit tests** alongside the integration cohort. Owning-skill unit coverage adheres to `memory/feedback_unit_tests_with_dev.md`.

## H annotation promotions

§12.5 (§TCO) and §C.3.3 (§TCO NFR appendix) both upgrade `[Tested ...]` → `[Tested+Neg tests/ring0.rs::tco_deep_countdown]`. Two of the ≥3 candidates promoted this wave; remaining promotions land in Wave 3.

## Discipline audit

- **Minimal-repro-before-handoff**: N/A for Wave 1 (no new defect handoff — A-carries are pre-existing).
- **Repros-join-suite**: No new `#[ignore]` introduced. All Wave-1 failing-or-passing tests visibly pass/fail.
- **Keep-small**: Unit tests are tight (6 CLIF dump tests are single-assertion each; 3 format_entry_sig tests pin one spec clause each). Good.
- **Agents clean their own crate**: Implicit — the cleanup pass (Workstream W) eliminated pre-existing warnings.

## Sketch comparison

Not applicable — Wave 1 is narrow cleanup + observability infrastructure + invariant reconciliation. No new architectural surface. (Workstream A in Wave 2 will require a sketch comparison per `design/backend/jit-object-convergence.md §7`.)

## Wave 2 readiness

**Wave 2 MAY proceed.** 0 Blockers; single Important (I-1 .gitignore) is cosmetic and can be folded into `/qa` cleanup during the Wave 2 flow or at close. All Sprint-59 Importants (I-1/I-2/I-3) are genuinely resolved with structural rather than lexical fixes. The CLIF-dump infrastructure required by Wave 2's H3 audit is landed, tested end-to-end, and filter-grammar-documented. Workstream A can begin per the audit-first phasing (§6.1 fix → H3 audit → drop-glue GOT → §4.3 carry-forward).
