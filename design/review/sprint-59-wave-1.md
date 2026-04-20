# Sprint 59 Wave 1 — /review Report

**Reviewer**: /review
**Verdict**: PASS with Importants

## Blockers (B)

None.

## Important (I)

1. **`register_dep_for_eval` passes `delays_other = false` to `register_module`** — `src/session_v4.rs:1301`. Every worker-side form handler (`handle_import`, `handle_export`, `handle_mod`, `inject_prelude_if_needed`) uses `true` (TypecheckFirst pool). The call is defensive / idempotent because the form handler has already registered with `true` before returning `Blocked`, so this arm short-circuits at the `modules.contains_key` guard. But the docstring explicitly covers the case where this function is reached *without* a prior form-handler registration (tests, alternative eval paths). Along that path the dep lands in `TypecheckNext`, not `TypecheckFirst`, silently diverging from the Decision-37 canonical flow. **Recommend fix in-sprint**: pass `true` and rely on the idempotency guard for correctness. Low risk, one-line change.

2. **Transitive-dep registration in `recurse_into_transitive_deps` not routed through `register_dep`** — `src/worker.rs:1640-1674`. This site manually inlines the same prologue (read source, hash, stash source text, file_to_module, publish sexps) that the new `register_dep` shim encapsulates, and then calls `scheduler.register_module`. The collapse migration plan §6 enumerated 5 surfaces — this is a 6th (predicted as a risk in §9 Risk 1). Behaviour is correct today (publish precedes register), but leaves one code path outside the shim's static invariant that "every dep registration routes through publish-first". **Recommend fix in-sprint**: refactor through `register_dep` for consistency and to prevent future drift. Small mechanical change.

3. **Unit guard `compile_dep_inline_publishes_sexps_before_register` deleted without replacement** — `src/session_v4.rs` test module. The test-removal comment argues the invariant is now "structurally preserved" because every dep registration routes through `register_dep` or `register_dep_for_eval`. That is true *if* Finding 2 is addressed; today, the transitive-dep site at `worker.rs:1640` does NOT route through the shim. The static invariant can only be stated once every dep registration is structurally routed. **Recommend fix in-sprint jointly with Finding 2**: once all 6 sites are routed through the shim, the structural argument is sound and the test removal is justified. Until then, either keep the old test or add a cheap structural guard (e.g., a `debug_assert!` in `ensure_got_slot`'s counterpart at the scheduler boundary, or a `grep`-style test that no call site calls `scheduler.register_module` without first calling the shim).

## Suggestions (S)

1. `register_dep_for_eval` defensively re-publishes dep_sexps and re-registers the dep even though the form-handler has already done so. The code is clearly written and the comment justifies it, but the comment's "e.g., tests, alternative eval paths" list is speculative. **Suggestion**: add a `debug_assert!` verifying `shared.module_sexps.contains_key(dep_module)` on entry in release-debug builds only — if the form-handler path is the only real caller, the assert will never fire and documents the invariant; if another call site emerges, the assert catches it.

2. Style nit on the new cache-hit `register_imports` call at `src/worker.rs:2296`: `register_imports(&mut ctx.check_state,&[prelude_spec])` is missing a space after the comma. Pre-existing style in the surrounding lines is the same — this would be a larger reformat pass if addressed. Defer.

3. `tests/sprint59_defects456_repro.rs` is 1771 lines / 34 tests. Legitimate given the reduction discipline (each test pins one axis of the D4/5 matrix), but warrants splitting when the file grows further. Defer.

## Per-workstream notes

**Workstream A (dual-path collapse)**: Matches `design/int/dual-path-persistence-collapse.md` §7 Steps 1–6. `register_dep` shim lands in the form handlers (4 sites); `register_dep_for_eval` replaces `compile_dep_inline`; the deleted `compile_dep_inline` comment clearly signposts the replacement path. `wait_module_inmem_complete_blocking` is the right primitive (scoped wait rather than whole-world) and is correctly documented with its deadlock rationale. Step 7 (heisenbug 50-loop repro) reported green by /int — not re-run here. Condition 1b (prelude-load-via-register_module) property holds: prelude entry into the system is unchanged. Condition 1c (carry-forward upsert at `program.rs:2184-2232`) is untouched — collapse is upstream of the upsert site.

**Defect 3 (docstring dash)**: 1-line format-string change — trivial and correct.

**Defect 8 (test-form scan gap)**: `any_expr_in_program` helper is the right factoring; now walks `TopLevel::Expr`, `TopLevel::Defn` variant bodies, and `TopLevel::TraitImpl` method variant bodies. The transitive-through-compiled-defns fix via `any_compiled_defn_uses_test_forms` is well-scoped to the `needs_test_state` gate and doesn't leak into unrelated paths. Correct.

**C-i (`into_owned_consuming`)**: Clean Decision-24 Form-B implementation. Default trait method bypasses `CLOwned::new`'s inc cleanly with `CLOwned { inner: self }`. Three new tests pin the RC semantics and contrast `own()` vs `into_owned_consuming()`. Stale FIXME at `io.rs:28` correctly removed. `ring2-rc.md` audit table updated with explicit `print_string` / `capture_print` rows.

**C-ii (`ensure_got_slot` local-symbol fix)**: Correct signature change — caller-resolved `symbol_addr` is passed in, internal lookup removed. Regression test `ensure_got_slot_accepts_preresolved_local_symbol_address` pins the bug shape (symbol NOT in `defined_symbols` / `symbols`). Sprint 58 Decision-23 regression-guard window preserved.

**Cache-hit prelude parity**: 4-line fix at `inject_prelude_if_needed` cache-hit arm. Mirrors the else-arm's `register_imports(prelude_spec)` call exactly. Flips `sprint23::cache_repl_loads_on_startup` green.

**`protect_return_value` RC-underflow fix**: Narrows `has_heap_bindings` predicate to exclude `borrowed_vars` and `consumed_vars` — which `pop_scope_with_cleanup` already skips. The symmetry argument in the comment is correct: a protective inc without a matching scope-cleanup dec leaves an inflated RC. Fix is at the right level.

## Invariant audit: JIT vs object codegen paths

`protect_return_value` is in `crates/cranelisp-backend/src/compiler/mod.rs` — shared codegen core. It applies uniformly whether the module is JIT-finalised or serialised to `.o` and later loaded by `Linker`. **The fix itself does not create divergence** — it applies to both paths by construction. However, the SPRINT.md Outcome section names the empirical divergence (same source: REPL-entered green 5/5, imported-from-module fails 75%) as an unresolved architectural red flag. The `protect_return_value` fix is consistent with the hypothesis that the remaining 75% failure arises *downstream* of codegen — in object-file serialisation, relocation, or GOT fixup — rather than in codegen itself. **Flag**: the FIXME on SPRINT.md naming this as S60 /arch work is correctly scoped. No Wave 1 code newly contributes to the divergence.

## Discipline audit

Minimal-repro-before-handoff: Followed. `tests/sprint59_cache_repro.rs` (cache-hit prelude) and `tests/sprint59_defects456_repro.rs` (D4/5 reduction to 25-LOC html + 14-LOC grid) were both committed as narrow repros before handoff. `design/backend/cache-repl-loads-triage.md` documents the classification and repro before any fix.

Repros-join-suite: Followed. 34 D4/5 reduction tests, 9 cache-repro variants, and Workstream D neg tests all un-ignored, visibly failing or passing as narrowed. No `#[ignore]` introduced.

Keep-small: Followed. D4/5 reductions range from 1-line test bodies up to the real-html-plus-trimmed-grid pair. The 14-line trimmed grid.cl fixture specifically exemplifies the discipline.

`/backend`'s `protect_return_value` fix: A dedicated minimal repro is not visibly present in Wave 1. The fix itself is 4 lines and clearly justified by the comment, but the narrow test shape pinning the exact scope-cleanup/borrowed/consumed interaction — as opposed to subsuming demo-level tests — is not in the diff. **Minor discipline note**: a targeted backend unit test would strengthen the regression guard. Not a blocker since the fix is small and the surrounding test surface exercises the path.

No 2x-deferral escalations in Wave 1. The S60 FIXMEs (CLIF-dump infra, exe-mtime-in-objects, JIT/object divergence) are first-time carries, not repeat deferrals.
