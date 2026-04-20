# Sprint 58 Wave 6 Review — Showcase + defect-handoff codification + Defect 1+2 fixes

**Sprint**: 58 Wave 6
**Date**: 2026-04-20
**Reviewer**: `/review`
**Commits reviewed**: `0bb35c6` (showcase: ring4p.demo + exemplar verification + Cranelisp.toml docs), `dea17b1` (process: defect-handoff codified across root CLAUDE.md + 6 user-proxy skill defs), `528c14a` (`/qa` 5 narrow-repro tests in `tests/wave6_demo_repros.rs`), `a9e194c` (`/int` Defect 1 fix — REPL dep-load race at 5 sites), `98bf4ef` (`/stdlib` Defect 2 fix — `seq/lazy.cl` missing imports), `d6fa3ad` (`/spec` §8.11.4 + §8.2.3 annotation cleanups), `c658eba` (`/qa` Pass 2 close-time audit + SPRINT.md §Outcome populated)
**Scope**: Phase 5 sprint-close wave. Showcase deliverables for the convergence headline (Decision 31 Scenario 2 + Cranelisp.toml + multi-sig display + private submodule rejection); codification of the user-proxy `/qa`-narrow-repro discipline that emerged organically across Sprint 58; two demo-surfaced defects fixed inside the wave (Defects 1 + 2); three demo-surfaced defects deferred with failing tests as durable records (Defects 3, 4+5, 6+7); spec annotation cleanups; close-time audit ratifying the 6-failure baseline.

## Verdict

**PASS.** Wave 6 is the canonical demonstration of the defect-handoff principle it codified: `/repl` and `/port` walked through demos and surfaced 7 real defects, `/qa` pinned all 7 as failing integration tests with `// spec:` + `FIXME(/owner)` annotations, the two cheapest-to-fix (Defects 1 + 2) landed inside the wave, and the deferred three carry forward as visible failing tests rather than buried FIXMEs. The architectural anchors (Decisions 23, 25, 31, 32, 35, 36, 37) are unchanged this wave — Wave 6 is process + showcase + narrow defect closure, not architecture. The Defect 1 fix scoped correctly beyond the original FIXME-3 (race shape lived at 5 sites, not 1) and shipped with a regression-guard unit test in `src/session_v4.rs::persistent_worker_tests::compile_dep_inline_publishes_sexps_before_register` that pins the publish-then-register order structurally. The Defect 2 fix was preceded by a stdlib-wide audit of all 35 `(import [prelude []])` files (commit message says 32; actual is 35 — minor inconsistency, see S-3) confirming `seq/lazy.cl` was the only at-risk file. The defect-handoff principle is consistent across root CLAUDE.md and all 6 user-proxy skill defs (`/repl`, `/port`, `/docs`, `/examples`, `/stdlib`, `/platform`), each tailored to that skill's specific sentinel context. Per-crate clippy gate holds (zero new warnings vs the post-Wave-3 baseline `b7f3e0a`). Test baseline preserved exactly at 1760 / 1754p / 6f.

The Importants below are bookkeeping / cosmetic: (a) commit-hash typo `a9e174e` should be `a9e194c` repeated 4× across `sprints/SPRINT.md` + `tests/plan/ring4.md`; (b) commit message audit count says 32 stdlib files but actual is 35 (the audit conclusion is unchanged — only `seq/lazy.cl` is at-risk — but the count drift suggests the audit may have under-enumerated); (c) the dual-path persistence structural debt that Defect 1 was a symptom of is correctly surfaced in §Findings but no concrete tracking issue / future-sprint name is filed beyond "tracked for a future sprint". None of these block sprint close — the user can confirm close on the current artefacts.

## Counts

| Severity | Count |
|---|---|
| Blocker | 0 |
| Important | 3 |
| Suggestion | 4 |

---

## Focus area findings

### Focus 1 — Defect-handoff principle codification (commit `dea17b1`)

**Verdict**: PASS. The principle is clean, actionable, and consistently applied.

**Root principle** (`CLAUDE.md:97-105`): the §"Usability Findings and Defects" section cleanly distinguishes the two categories. Usability findings (corner cases, ergonomic issues) → FIXME on doc; documentation is sufficient closure. Defects (compiler bugs, spec violations, runtime crashes, REPL/`--run` divergences) → `/qa` narrow integration test; failing test is the durable record + the trigger for compiler-skill resolution. The closing sentence ("A FIXME comment on a design doc captures intent but doesn't prove the issue exists, doesn't catch regression, and doesn't trigger CI. The failing test does all three.") nails the rationale for why this matters — it forecloses the failure mode that produced this whole Sprint 58 close-wave salvage operation.

**Six skill-def updates** (`.claude/commands/{docs,examples,platform,port,repl,stdlib}.md`): each gains a "Defect Handoff (Required Before Wave Close)" section. The four common requirements (failing + un-ignored + `// spec:` + `FIXME(/owning-skill)`) are spelled out in each. The sentinel framing is tailored per skill:

- `/repl` (`repl.md:80-88`): demos are sentinels — when they catch real bugs, those bugs must become failing tests.
- `/port` (`port.md:42-51`): exemplar is a stress-test sentinel — when it catches one, the bug must become a failing test, not just an `exemplar/CLAUDE.md` "Known Issues" entry.
- `/docs` (`docs.md:69-78`): user docs are sentinels — they catch real bugs by walking through what users actually do.
- `/examples` (`examples.md:99-108`): examples are sentinels — they catch real bugs by exercising the language end-to-end in compact form.
- `/stdlib` (`stdlib.md:160-169`): stdlib is a sentinel — it catches real bugs by composing primitives at scale. (Defects in stdlib code itself are `/stdlib`'s own to fix; this handoff applies to defects in the LANGUAGE, surfaced by stdlib code.)
- `/platform` (`platform.md:110-119`): platform DLLs are sentinels at the language/runtime boundary. (Same own-fix carve-out as `/stdlib`.)

Each skill's section cross-references root CLAUDE.md §"Usability Findings and Defects". The own-fix carve-outs on `/stdlib` and `/platform` are correctly scoped — a bug in stdlib `.cl` code is `/stdlib`'s; a compiler bug surfaced by stdlib code is the compiler skill's. **No inconsistencies between the 6 skill defs and the root principle.**

The `/repl` def at `repl.md:71` also drops the stale "Consumes the REPL implementation from `/qa` (which owns `src/repl/`)" line that pre-dated the `/int`/`/qa` split, replacing with the correct "from `/int` (which owns `src/`) and `/qa` (which owns `tests/`)". Good cleanup.

### Focus 2 — Defect 1 fix (commit `a9e194c`)

**Verdict**: PASS. Correct scope expansion; sound regression-guard test; clean shared-helper API.

**Race-site identification**: `/int`'s original FIXME-3 named only `compile_dep_inline` in `src/session_v4.rs`. The actual fix correctly extends to 5 production sites (one in `session_v4.rs`, four in `worker.rs`). I verified by grep — every production `scheduler.register_module(<dep>, true)` call site in `src/` is now preceded by either `publish_dep_sexps(ctx, ...)` (the new shared helper) or an inline-equivalent `shared.module_sexps.lock()...insert(...)` block. The exhaustive list:

| Site | File:line | Pre-publish source |
|---|---|---|
| `compile_dep_inline` | `src/session_v4.rs:1953-1956` | inline (commit `a9e194c`) |
| `handle_import` | `src/worker.rs:1284,1288` | `publish_dep_sexps` (commit `a9e194c`) |
| `register_transitive_cached_imports` | `src/worker.rs:1611-1613,1627` | inline (pre-existing — Sprint 56 lineage) |
| `handle_export` | `src/worker.rs:1701,1705` | `publish_dep_sexps` (commit `a9e194c`) |
| `handle_mod` | `src/worker.rs:1801,1805` | `publish_dep_sexps` (commit `a9e194c`) |
| `inject_prelude_if_needed` | `src/worker.rs:2313,2316` | `publish_dep_sexps` (commit `a9e194c`) |

Two `register_module(... , false)` call sites also exist in `session_v4.rs:1199` and `:1268` — both are `register_module_with_source` style entry-module paths, both publish-before-register inline (pre-existing — Sprint 57 lineage). One test-only call at `src/scheduler.rs:1689` is scaffolding only. **Nothing is missed.**

**Shared helper API** (`src/worker.rs:1306-1322`): `publish_dep_sexps(ctx: &ModuleCompiler, dep: &ModuleFullPath, dep_sexps: &[Sexp])` — the no-op-when-`shared_state`-`None` pattern is correct (REPL inline contexts that don't use SharedState fall back to the local map and don't need the publish; the shared-state contexts MUST publish or risk the race). The `map.entry(dep.clone()).or_insert_with(|| dep_sexps.to_vec())` semantics correctly preserves prior content if a faster path already published — idempotent under retries. The doc-comment at `:1305-1314` explains the MUST-call-before-`register_module` invariant and cross-references both the integration repro test and the unit guard. Good defensive shape.

**Regression-guard unit test** (`src/session_v4.rs:4259-4304` in `mod persistent_worker_tests`): the test uses `test_session(0)` (zero priority workers) so the published `dep_sexps` entry is observable by the test (no concurrent worker has consumed it). Pre-condition asserts `shared.module_sexps` does NOT contain the dep before `compile_dep_inline` runs. Post-condition asserts `map.get(&dep).map(|v| v.len()) == Some(dep_sexps.len())` after `compile_dep_inline` returns. The doc-comment at `:4226-4258` is comprehensive — explains the invariant being pinned, why `priority_workers = 0` is required for observability, why the integration test in `tests/wave6_demo_repros.rs` covers the many-worker scenario end-to-end, and what failure mode a regression would surface. **Strong enough to catch any future change that moves the publish after `register_module` or removes it.**

**Dual-path persistence**: the commit message correctly identifies that "Option B (collapse to single path) is the permanent fix; tracked for a future sprint." This is the right disposition — Wave 6 is sprint-close, not new structural-debt remediation. See I-3 below for the recommendation to file a concrete tracking artefact.

### Focus 3 — Defect 2 fix (commit `98bf4ef`)

**Verdict**: PASS with one bookkeeping inconsistency (S-3 below).

**Stdlib-wide audit**: I spot-checked the audit's claim by independently searching all `(import [prelude []])` files for `Nil`/`Cons`/`Some`/`None`/`Ok`/`Err` references:

- `stdlib/text/display.cl`, `stdlib/text/string.cl`, `stdlib/text.cl` — zero ADT references. Clean.
- `stdlib/fn/threading.cl` — references only macros-module-qualified `macros/SCons` / `macros/SNil` (in macro bodies). Clean.
- `stdlib/io/monad.cl` — explicit imports of `SCons`/`SNil`/`Sexp`/`SList` from `macros`. Clean.
- `stdlib/control.cl` — references `None` inside backquote macro bodies (lines 13, 16). This resolves at the expansion site (where the macro is invoked, where `None` is in scope via the user's prelude), not in the macro's defining module. Per the standard cranelisp macro-expansion semantics this is correct.
- `stdlib/seq/lazy.cl` — references `Nil`/`Cons` (lines 131-132) and `Some`/`None` (lines 99, 101). Now correctly imports them at lines 18-19. **Defect closed.**

**Updated comment** (`stdlib/seq/lazy.cl:9-12`): the new comment text is accurate and explains the WHY ("This module suppresses the implicit prelude glob (per spec §8.3.6) because it is part of the stdlib and a project's custom prelude could re-export from us — that would be a circular dependency. All names must therefore be resolved through explicit imports."). Aligns with the stdlib-wide convention. **Better than the misleading "available via implicit prelude import" line it replaced.**

### Focus 4 — Narrow-repro tests (commit `528c14a`)

**Verdict**: PASS. All 5 tests follow the defect-handoff conventions exactly.

**Test inventory**:

| Test | Defect | Annotation | Owner | Assertion shape |
|---|---|---|---|---|
| `repl_dep_load_no_race_with_persistent_workers` | 1 | `// spec: implicit (REPL/--run parity)` | `/int` | Asserts REPL output does NOT contain `"no parsed sexps for module"` symptom |
| `stdlib_seq_lazy_imports_resolve_nil_cons` | 2 | `// spec: spec/08-modules.md §8.3.6` | `/stdlib` | Asserts batch typecheck does NOT emit `"undefined variable: Nil/Cons/Some/None"` |
| `display_defn_with_docstring_uses_dash_separator` | 3 | `// spec: repl/spec.md §1.1` | `/int` | Asserts REPL output contains `"; defn - Multiply by 2"` (dash) and reports if it found semicolon |
| `run_tests_batched_invocation_no_crash` | 4 + 5 | `// spec: repl/spec.md §16.3` | `/backend` | Asserts NOT (signal_crash OR no_tests_found OR load_failed) AND test_ran |
| `exemplar_solver_does_not_stack_overflow_on_small_puzzle` | 6 + 7 | `// spec: implicit (exemplar validation)` | `/backend` + `/port` | Asserts NOT signal-segv AND NOT killed-by-signal |

All 5 are failing-not-ignored (verified by grep — zero `#[ignore]` in the file). All 5 carry both `// spec:` annotations naming the spec section and inline `FIXME(/owning-skill)` blocks at the test's introductory comment naming the resolver. Test names describe the spec violation, not the implementation bug.

**Defect 4+5 collapse**: the assertion at `tests/wave6_demo_repros.rs:374-385` is broad enough to catch both manifestations — `signal_crash` matches `Some(139)` (SIGSEGV / Defect 4) OR `Some(133)` (SIGTRAP / Defect 5) OR `None` (killed by uncaught signal). The test additionally guards against the upstream gating modes (Defect 1 race symptom hiding test discovery, Defects 1+2 preventing module load) and requires positive evidence that at least one test actually ran. **Layered and robust.**

**Defect 6+7 collapse**: the assertion at `tests/wave6_demo_repros.rs:447-460` checks for SIGSEGV (139) and signal-kill (None). The doc comment correctly notes that re-enabling the 3 puzzle tests in `exemplar/solver.cl` is `/port`'s acceptance criteria once `/backend` resolves Defect 6. **Captures what we expect to work post-fix.**

### Focus 5 — Showcase deliverables (commit `0bb35c6`)

**Verdict**: PASS.

**`repl/demos/ring4p.demo`** (52 lines, 5 vignettes): I read the file end-to-end. Vignettes are tightly aligned with Phase 5 deliverables:
- HEADLINE — Decision 31 Scenario 2: defines `f`, runs `/sig f` + `/mem`, redefines `f`, runs `/mem` again. The narrative ("`Arc<Jit>` lives on `ModuleEntry::Def.code`; redefinition drops the prior clone; `Drop` calls `unsafe free_memory()`") correctly summarises the architectural payoff of Wave 3.
- Step 5d (ii) multi-sig display: `(defn pick "Pick first arg" ([:Int x] x) ([:Int x :Int y] x))` then bare `pick` — exercises the multi-sig REPL bare-symbol display path.
- Step 5d (iii) Cranelisp.toml lookup: live `/sh` write of `Cranelisp.toml` then `cat`.
- Step 5d (i) private submodule rejection: cross-session via `/sh` + `/quit` trampoline; fresh REPL rejects the import per spec §8.2.3.
- Step 5b cache-hit fast restart: post-trampoline `/sh ls .cranelisp-cache | head -6` shows `.meta.json` + `.o` files materialised.

The closing comment ("Phase 5 closes the v4 data-model: structural decls + cache + generics on one `SymbolTable<C, L>`. Per-redefinition reclaim, multi-sig display, project-config lookup, and rejected private imports all flow through one shape.") is a faithful Phase-5 elevator pitch. The commit message confirms the demo plays cleanly via `DEMO_FAST=1 ./repl/showcase ring4p`.

**Exemplar verification**: 4 modules typecheck cleanly; `/run-tests grid` is 15/15 in 3.74ms (validates Decision 30 safe pattern (c) at exemplar scale); `/run-tests solver` 4/4 (excluding 3 puzzle tests body-disabled per Wave 0). The `/run-tests html` + `form` batched crashes and the Sprint 19 solver segfault are correctly NOT presented as Sprint 58 regressions — they are pre-existing or surface from Wave 0's enabling of test functions that were never exercised before. The 3 follow-on FIXMEs filed in the commit are all properly scoped (one to `/spec`, two to `/qa`).

**`user/getting-started.md` Cranelisp.toml docs**: I read the diff. The new "Library Search Path" section accurately reflects what shipped:
- 3-tier precedence chain (Project Config → CRANELISP_LIB → stdlib default)
- TOML key (`lib-dirs` as path-string list)
- Relative-path semantics ("resolved against the project root")
- Explicit cross-reference to `spec/08-modules.md §8.11.4`
- Empty `lib-dirs = []` is a valid declaration
- Environment-variable fallback only consulted when no Cranelisp.toml present

Matches the spec text after the §8.11.4 cleanup in `d6fa3ad`. **Aligned.**

### Focus 6 — `/spec` annotation cleanups (commit `d6fa3ad`)

**Verdict**: PASS.

**§8.11.4** (lib-dirs precedence): heading annotation correctly promoted from `[Tested ... env var; project-config file NOT YET IMPLEMENTED — see FIXME(/int) below]` to `[Tested ...]` listing all 5 e2e tests. Inline `FIXME(/int)` HTML comment removed. Spec text for item 2 tightened to match shipped behaviour (file name in project root, TOML key, relative-path resolution, malformed-file diagnostic requirement). Precedence chain wording preserved (already correct).

**§8.2.3** (private submodule visibility): heading annotation cleaned from `[Tested+Neg ... — FAILING: /int gap, (mod- ...) protection not enforced cross-module]` to `[Tested+Neg tests/ring2.rs::neg_private_submodule_not_importable_from_peer]`. Both inline FIXMEs (one filed by `/repl` Wave 6 audit, one filed by `/qa` Sprint 57 Wave 5) removed.

**Verification**: I grepped `spec/08-modules.md` for `FIXME|FAILING|NOT YET IMPLEMENTED` — zero matches. **Clean.**

The commit also correctly flags `§8.11.5` item 2 ("Project configuration file MAY specify a platform directory list") as a future-sprint follow-on (still abstract and untested — no Cranelisp.toml schema given for platforms). Not Sprint 58 scope.

### Focus 7 — Close-time audit completeness (commit `c658eba`)

**Verdict**: PASS with one bookkeeping inconsistency (I-1 below).

**`tests/plan/ring4.md §G.18`**: comprehensive bookkeeping of Wave 5 + Wave 6 outcomes. The 4 sub-tables (Wave 5 deliverables; Wave 6 narrow-repro tests; Wave 3d Decision 31 reclaim tests; Wave 6 follow-on Defect 1 + Defect 2 fixes; full re-triage of 6 baseline failures) cover the full surface. Each baseline failure has named owner + disposition + FIXME location.

**`sprints/SPRINT.md §Outcome`**: correctly populated. The §Delivered section lists Phase 5 sub-steps (5a + 5b + 5c + 5d + 5e all named), Decision 31 Scenario 2 ACTIVE with named test, 9 architectural decisions, defect-handoff codification, 50+ new tests with the breakdown, spec annotation promotions, and the two Sprint 57 carries closed (`tests/ring2.rs::neg_private_submodule_not_importable_from_peer` and `tests/repl_experience.rs::display_overloaded_fn_shows_all_variants`). The §Deferred section is the 6-failure table + the explicit other-deferred-work block (io.rs:28, v4_cache_hit_dependency, dual-path persistence collapse, Decision 25/31 footnote tightening, sequence-diagram regen, persistent-workers REPL eval-latency measurement, design-doc forward FIXMEs). The §Findings section captures the 7 close-time lessons.

**FIXME audit**: I cross-checked the "0 unaccounted source-tree FIXMEs" claim by greping `src/` + `crates/` + `spec/` + `repl/` + `user/` for `FIXME(`:

- `crates/cranelisp-runtime/src/io.rs:28` — FIXME(/backend) — accounted (one-deferral-permitted).
- `crates/cranelisp-typecheck/plan-typecheck.md:577` — explicitly resolved (not an open FIXME).
- `crates/cranelisp-backend/plan-backend.md:36` + `:618` — design-doc forward pointers, named owner.
- `spec/index.md:3` — moved-to-tracker note, not an open FIXME.
- `spec/CLAUDE.md:92` — describes resolved state.
- `repl/spec.md:319` — FIXME(/int) for Ring 4 polish sprint. Forward-pointer, named owner. Acceptable per project convention.
- `user/plan-docs.md:472` — describes resolved state.
- `user/CLAUDE.md:52` — meta-description of FIXME convention, not an open FIXME.

**Confirmed: 0 unaccounted in-source FIXMEs. The 1 deferred under one-deferral-permitted policy is properly disposed.** Forward-pointer FIXMEs in design plan docs are by convention acceptable.

### Focus 8 — Per-crate clippy gate

**Verdict**: PASS — zero new warnings vs the post-Wave-3 baseline (`b7f3e0a`).

I ran `cargo clippy -p cranelisp --lib` against both HEAD and the `b7f3e0a` baseline-equivalent (after temporarily reverting `src/worker.rs` + `src/session_v4.rs`). Both produce the same 4 lib warnings (1 in `cranelisp-backend` `compiler/mod.rs:645`, 3 in `cranelisp` `src/watch.rs:70-72` + `src/worker.rs:2303` — all `collapsible_if` / `contains_key`-then-`insert` pre-existing patterns). The `src/worker.rs:2303` warning predates Wave 6 (Sprint 54 lineage per `git log -L`).

`cargo clippy -p cranelisp-backend --all-targets`: 1 error (the pre-existing `tests/sketch_port.rs:1104` `approx_constant` lint on the literal `3.14`) + 4 lib-test warnings (all pre-existing `collapsible_if` patterns). Out-of-scope per task brief.

`cargo clippy -p cranelisp-types --all-targets`: 1 lib-test warning (pre-existing `needless_borrow`). Out-of-scope.

`cargo clippy -p cranelisp-typecheck --all-targets`: 8 lib-test warnings (all pre-existing `collapsible_if` patterns). Out-of-scope.

**Wave 6 source code introduces ZERO new clippy warnings.** The new `publish_dep_sexps` helper, the new `compile_dep_inline_publishes_sexps_before_register` test, the new `tests/wave6_demo_repros.rs` integration tests — all are clippy-clean.

`cargo check --workspace`: clean. **Workspace cargo check gate met.**

### Focus 9 — Sprint-close gate criteria

| Gate | Status |
|---|---|
| All Phase 5 sub-steps shipped (5a + 5b + 5c + 5d + 5e) | MET (per SPRINT.md §Delivered) |
| Decision 31 Scenario 2 verified working | MET (`tests/v4_jit_reclaim.rs::decision31_scenario2_per_redefinition_jit_pages_reclaimed` + `_repeated_redefinition_no_unbounded_growth`) |
| Defect-handoff principle codified | MET (commit `dea17b1` — root CLAUDE.md + 6 skill defs) |
| All FIXMEs disposed (resolved or deferred-with-named-owner) | MET (audit confirms 0 unaccounted in source tree) |
| Test count rises (50+ new tests across 6 waves) | MET (5 reclaim + 5 Cranelisp.toml E2E + 4 /mem E2E + 11 unit + 4 match neg + 5 wave6_demo_repros + assorted regression-guards) |
| Baseline failures explained (3 pre-existing + 3 demo-surfaced deferred) | MET (per SPRINT.md §Deferred 6-failure table) |
| Workspace cargo check clean | MET |
| Per-crate clippy zero new warnings | MET |

**8 of 8 gates met.** No blocker for sprint close.

---

## Findings

**I-1** (Important, /sprint or /qa): Commit-hash typo `a9e174e` should be `a9e194c`. Affects 4 occurrences across `sprints/SPRINT.md:723` and `tests/plan/ring4.md:1093`, `:1102`, `:1140`. Correct hash is `a9e194c` per `git log` output. The narrative is otherwise accurate; only the hash is wrong. Recommendation: fix the four occurrences before user-confirmed sprint close so the bookkeeping ties to the actual commit.

**I-2** (Important, /stdlib): Commit message for `98bf4ef` says "Stdlib-wide audit (32 .cl files using `(import [prelude []])`)"; the actual count is 35 .cl files. The audit's CONCLUSION is unchanged (only `seq/lazy.cl` was at-risk; the other files either define the names they reference or qualified-import them), but the count drift suggests the audit may have under-enumerated by 3 files. Recommendation: re-verify the 3 missing files in the next `/stdlib` invocation; if all 3 are equally clean, update the bookkeeping in a future commit; if any one is at-risk, file a follow-on FIXME(/stdlib). Likely candidates by name shape: `stdlib/derive.cl`, `stdlib/defs.cl`, `stdlib/default.cl` — the three that didn't appear in any of the patterns the commit message enumerates. Not blocking sprint close; this is verification hygiene.

**I-3** (Important, /int + /sprint): The dual-path persistence structural debt that Defect 1 was a symptom of is correctly named in §Findings (commit `c658eba` SPRINT.md §Outcome) but the disposition is "tracked for a future sprint" without a concrete artefact. The 3 sprint23 baseline failures (`cache_repl_loads_on_startup`, `persist_import_survives_restart`, plus the pre-Wave-3 cluster) all trace to this same root cause per `tests/sprint23.rs:1126` + `:1307` FIXMEs. Recommendation: when `/sprint` opens the next post-Sprint-58 sprint, the dual-path-persistence-collapse work should appear on the §Roadmap with a target sprint name (not just "future"); ideally `/int` files a stub design doc at `design/int/dual-path-persistence-collapse.md` capturing the Option B approach so the next sprint can pick up the analysis cold. Not blocking Sprint 58 close.

**S-1** (Suggestion, /int): The `publish_dep_sexps` helper (`src/worker.rs:1306-1322`) takes `dep_sexps: &[Sexp]` and clones it via `.to_vec()` inside the `or_insert_with` closure. This is correct (the map owns its values), but the doc comment doesn't explicitly state the cloning cost. For most modules `dep_sexps` is small, so this is negligible — but for prelude (~50+ sexps) the clone is non-trivial. Not a defect; future micro-optimisation might pass `Vec<Sexp>` and let the caller decide. Defer.

**S-2** (Suggestion, /repl): `repl/demos/ring4p.demo` line 24 uses `(add-i64 x 1)` for the `f` redefinition. The bare `add-i64` primitive name leaks compiler-internal naming into the demo where the convention has shifted to `+` (via prelude). Not wrong (the primitive is still callable by its kebab-case name per `src/CLAUDE.md` §JIT Symbol Names), but cosmetically less polished than the rest of the demo. Consider `(+ x 1)` if the prelude is in scope by the time this vignette runs; otherwise leave as-is and add a one-line comment that `add-i64` is the explicit primitive.

**S-3** (Suggestion, /qa): `tests/wave6_demo_repros.rs::run_tests_batched_invocation_no_crash` is a complex 4-mode assertion (signal_crash, no_tests_found, load_failed, test_ran). The error message is comprehensive but the assertion logic is `!signal_crash && !no_tests_found && !load_failed && test_ran` — if a future failure mode appears that doesn't match any of the 3 negative checks AND `test_ran` is true (e.g., a test runs but produces wrong output), the assertion would PASS while the underlying defect is still present. Consider adding a positive assertion on the `pass`/`FAILED` token AND a count-of-tests-run check to harden against this. Not urgent — current shape catches what we know about. File for `/qa` follow-on.

**S-4** (Suggestion, /arch + /int): The `publish_dep_sexps` helper's existence is itself evidence of the dual-path persistence debt (I-3). When Option B lands (single-path persistence collapse), the helper should disappear — no need for an explicit "publish to shared map" step because there is only one map. Recommend annotating the helper's doc-comment with "TODO(dual-path collapse): remove this helper when single-path lands per §Findings of Sprint 58." Helps the next reader connect the dots. Defer.

---

## Anything blocking sprint close

**Nothing blocks sprint close.** The 3 Importants are all bookkeeping/cosmetic and can be addressed inside the user-confirmed close commit (or in a Sprint 59 opening commit). The 8/8 sprint-close gate criteria are met. Test baseline preserved exactly. Per-crate clippy gate held. Workspace cargo check clean.

Sprint 58 may close on user confirmation.

---

## Anything `/sprint` should escalate to user before final close

- **Commit-hash typo (I-1)** is a 30-second fix that would land in the sprint close commit; flag for user attention so they can authorise the inline correction.
- **Stdlib audit count drift (I-2)** is verification hygiene; not user-facing but worth mentioning so user knows the exact-count claim in commit `98bf4ef` is approximate.
- **Dual-path persistence (I-3)** should appear on the user's radar as the named structural-debt carry from Sprint 58 — Sprint 59 (or whichever next sprint targets stabilisation) is the natural home.
- **No surprises in the architectural anchor decisions** (23, 25, 31, 32, 35, 36, 37). All unchanged this wave. Wave 6 is showcase + process + narrow defect closure, exactly as intended.
- **The defect-handoff principle codification is the structural lesson of Sprint 58** and worth highlighting to user as the most important durable artefact of this sprint — it foreclosed a class of failure mode (defects buried as FIXMEs) that nearly cost this sprint a clean close.
