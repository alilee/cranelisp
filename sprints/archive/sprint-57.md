# Sprint 57: Pipeline v4 Convergence Phases 3 + 4

**Status**: READY-FOR-CLOSE — All 6 Waves COMPLETE. Pending user close confirmation. Wave 0 /review PASS+S6; Wave 2 /review PASS+I3/S7; Wave 3 /review PASS+S7; Wave 4 /review PASS+I2/S5 — both Importants **dissolved** via Decision 31 reconciliation (persistent-per-worker JIT premise retracted). Custom `Drop` on `Jit` wrapper shipped (Scenario 1 + session-teardown reclaim active). Wave-6 /int follow-ons resolved Decision 31 × eval-path interaction (inline-trampoline + consuming IO-tree release across all three eval sites). Full Scenario 2 (per-redefinition) reclaim requires `SymbolTable<C, L>` generics activation — scheduled for Sprint 58 Step 5c. Final test baseline: **1679/1696 passing, 17 failing** (15 pre-existing Phase-5-deferred + 2 explicit Wave-5 spec-exposure carries to Sprint 58).
**Ring**: 4 (Effects — full spec scope)
**Goal**: Collapse the remaining intermediate DashMaps into the symbol table. Code, platform function pointers, and persistent priority workers all live on / flow through `SymbolTable`. After this sprint, the §9 target data model is whole except for Phase 5 (structural declarations + cache serialization).

## Scope

Phases 3 and 4 of `design/arch/pipeline-v4-roadmap.md`. These two phases are declared independent in the roadmap and can be done in the same sprint because each lands through a different skill axis:

- **Phase 3 Step 3b (G6)** — Move compiled `Code` onto `ModuleEntry::Def`. Delete the `CodegenProduct` DashMap. Phase 3 Step 3a (GOT on `SymbolTable`, G7) was pulled forward into Sprint 56 and is already done.
- **Phase 4 Step 4a (G8)** — Platform function pointers on `ModuleEntry::Def` entries with `PrimitiveKind::PlatformEffect`. Delete `PlatformRegistry`. IO trampoline resolves platform functions by symbol-table lookup.
- **Phase 4 Step 4b (G9, G10, G11)** — Priority workers become session-persistent (spawned in `CompilerSession::new`, parked on condvar). `thread::scope` disappears from the worker lifecycle. `eval`, `reload_module`, and `register_module` all route through persistent workers. Persistent eval JIT emerges naturally from this change.

After this sprint, `CodegenProduct`, `PlatformRegistry`, and scoped-worker spawning are all deleted. Only Phase 5 (structural declarations on `SymbolTable` + cache serialization via `SymbolTable`) remains in the v4 data model programme.

**Unifying principle (Principle 11)**: One compilation pipeline, one store. After Phase 3, the symbol table IS the compilation state — AST, GOT, code, platform ptrs, scheme, callees all live on `ModuleEntry::Def`. Side DashMaps (`CodegenProduct`, `PlatformRegistry`) are a pre-v4 accretion; each additional DashMap is a coupling surface that makes cache restore, introspection, and worker coordination harder.

### Direct failure-fixing opportunities

The 14-failure baseline breaks down as:

| Category | Count | Expected fix |
|----------|-------|--------------|
| cache SIGSEGV / cross-module GOT | 9 | Phase 3 (G6 cleans up `CodegenProduct` lifetime) + Phase 5 (cache) |
| sprint23 cache/link | 3 | Phase 3 + Phase 5 |
| v4 cache-hit dep | 1 | Phase 3 |
| v4_platform | 5 | Phase 4 (G8) |
| `sketch_run_tests_pass_fn_called` (discover-tests / run-test builtins composition) | 1 | **THIS SPRINT — triage**. Not a missing feature; the builtins exist. Either fix the defect or fix the test. |

**Phase 3 + Phase 4 target**: clear the 5 v4_platform failures (Phase 4 G8), land as many of the 13 cache/cross-module failures as possible (Phase 3 G6 is expected to unblock at least the single-module cache paths; cross-module cache may need Phase 5). Worst case: Phase 3+4 land green on the 14-failure baseline and Phase 5 clears the remaining.

### Bundled pre-existing debt

The Sprint 56 close surfaced five non-Sprint-56 defects. Per the deferral principles, carrying defects is an anti-pattern; most of these are small enough to clear inside this sprint without displacing convergence work.

- **Super-import regression blocking `/port`** — `(mod test (import [super [*]]) …)` in exemplar modules fails because v4 module loader never rewrites `super` → parent path. Sketch had this at `sketch/src/module.rs:1429-1434`; spec mandates it at `spec/08-modules.md §8.3.7`. Fix in `crates/cranelisp-frontend/src/module_extract.rs` or at the scheduler's first import-spec consumption site.
- **`/mem` slash command missing** — `repl/spec.md:385` FIXME. `cranelisp_runtime::alloc_count()` / `dealloc_count()` are already public; command is a thin wrapper.
- **`CheckResult` slimming** — filed on `crates/cranelisp-types/src/check.rs:1`. Not a defect but blocks Phase 5 cache work. Slim `method_resolutions`, `mono_defns`, `default_method_defns`, `constrained_fn_names`, `expr_types` fields once we confirm no reader remains (Phase 1 claim).
- **`src/pipeline.rs:55` cosmetic** — `compile_and_execute_expr` still takes a `program: &Program` fallback parameter with no production caller. Delete it.
- **`sketch_run_tests_pass_fn_called` baseline failure triage** — this is a `discover-tests` / `run-test` *builtins* composition test, NOT a missing special form. The old `(run-tests init pass-fn fail-fn)` special form has been retired from the language (replaced by `discover-tests` + `run-test` builtins per spec/appendix-a-builtins.md + repl/spec.md §16.3). The test composes those builtins into a user-defined `my-run-tests` via `bind`. Triage whether the failure is (a) a defect in the builtins (fix in Sprint 57) or (b) a test-authoring issue (fix or delete the test). Either way, close it this sprint.
- **Stale `run-tests` references in crate plans + doc-comments** — cosmetic cleanup. `/frontend` ast_builder.rs §-header, `/typecheck` infer.rs doc-comment on `infer_annotate`, `/frontend` plan-frontend.md:142/414, `/backend` plan-backend.md:35/613, `/platform` plan-platform.md:74 + trace.rs:380, `/qa` tests/plan/ring4.md:3 + risks.md:4. FIXME(/skill) filed; owning skills update during Wave 5 parallel work.

### Prior-ring coverage gaps (/qa)

Fourteen `FIXME(/qa)` entries filed during Sprint 56 close sit on `spec/*.md` and `repl/spec.md`. Every entry is one of:
- **Coverage gap** — requirement tagged `[R2 S…]` or `[R3 S…]` where ring is complete but no integration test exercises the feature.
- **Traceability gap** — tests exist and pass; spec annotation still reads `[R{N} S{M}]` rather than `[Tested …]`.
- **Negative coverage gap** — MUST/MUST NOT requirement passes positive `[Tested …]` but has no `[Tested+Neg …]` counterpart.

Phase 3+4 implementation work is primarily data-model plumbing (DashMap deletions, pointer moves, worker lifecycle refactor) with relatively small /qa integration-test additions. The prior-ring coverage backlog is naturally parallelisable against these implementation waves and gives `/qa` useful Wave-1/2 work.

### /int Burden Assessment

**VERY HEAVY.** Three changes land in `/int` territory:

1. **Phase 3 G6** — `src/worker.rs` (write code to entry), `src/session_v4.rs` (delete `CodegenProduct` DashMap), all code-read sites (priority worker, REPL eval, introspection).
2. **Phase 4 G8** — `src/platform_registry.rs` (delete), `src/worker.rs` (platform form handling), IO trampoline (resolve platform fns by symbol table lookup).
3. **Phase 4 G9** — `src/session_v4.rs` complete worker lifecycle rework: workers spawned at session init, condvar-parked, `thread::scope` eliminated outside tests.

**Mitigation**: sequence the three steps so each lands green independently. Phase 3 G6 before Phase 4 G8 (simpler, no lifecycle change). Phase 4 G8 before Phase 4 G9 (platform removal is localised). Phase 4 G9 last — the riskiest change.

If `/int`'s Phase 1 design review surfaces a burden risk, fall back to either:
- **Descope option A**: ship Phase 3 G6 only; defer Phase 4 to Sprint 58.
- **Descope option B**: ship Phase 3 G6 + Phase 4 G8 only; defer G9 (persistent workers) to Sprint 58.

`/sprint` will escalate to the user if any sub-step blocks convergence for a full wave.

### Out of Scope

- **Phase 5 (structural declarations + cache serialization)** — next sprint.
- **Stdlib `run-tests` convenience fn** — if/when desired, builds on `discover-tests` + `run-test` builtins. `/stdlib` call on whether/when. Not a convergence item.
- **`FQTypeName` migration** — 182 call sites. Display works via `type_modules` lookup. Roadmap-deferred.
- **BL range fix (linker.rs)** — only manifests on very large codebases. Roadmap-deferred.
- **`SymbolTable<C, L>` generics** — API cleanliness only. `#[serde(skip)]` on code field is sufficient.

## FIXME Debt

FIXMEs found during Phase 1 scan (source + in-scope design/spec docs):

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `src/pipeline.rs:55` | /int | `compile_and_execute_expr` `&Program` fallback parameter unused | **this sprint** — delete as part of G6 cleanup |
| `crates/cranelisp-types/src/check.rs:1` | /typecheck | `CheckResult` slim-down (Phase 5 prereq) | **this sprint** — confirm no live readers; slim fields; file FIXME if Phase 5 needs more |
| `crates/cranelisp-runtime/src/io.rs:58` | /backend | `run_io_trampoline` intermediate Pure/Effect node leak | **this sprint** — real RC leak; fix inside Phase 4 IO trampoline rework |
| `design/arch/pipeline-v4-roadmap.md:47` (super-import FIXME) | /int | `super` import rewrite missing in v4 module loader | **this sprint** — unblocks `/port` exemplar |
| `repl/spec.md:385` | /repl + /int | `/mem` slash command not implemented | **this sprint** — thin wrapper around `cranelisp_runtime::alloc_count()` |
| `spec/appendix-a-builtins.md` (×3) | /qa | coverage + traceability gaps for `vec-map`, `vec-reduce`, builtin shadowing | **this sprint** — parallel /qa work |
| `crates/cranelisp-frontend/src/ast_builder.rs:989` | /frontend | stale "run-tests expression" section header; function below is `build_trace` | **this sprint** — cosmetic; correct header |
| `crates/cranelisp-typecheck/src/infer.rs:828` | /typecheck | stale doc-comment describing retired `(run-tests ...)` signature above `infer_annotate` | **this sprint** — cosmetic; rewrite doc |
| `crates/cranelisp-frontend/plan-frontend.md:141,414` | /frontend | stale `(run-tests …)` Ring 0 rejection rows — special form retired | **this sprint** — cosmetic; remove or annotate |
| `crates/cranelisp-backend/plan-backend.md:35,613` | /backend | stale `run-tests` in Ring 4 feature list + moot `compile_run_tests` deferral | **this sprint** — cosmetic; confirm no live `compile_run_tests` fn |
| `crates/cranelisp-runtime/plan-platform.md:74` + `src/trace.rs:380` | /platform | stale "run-tests timing" in `trace_first_child_nanos` descriptions | **this sprint** — cosmetic |
| `tests/plan/ring4.md:3` + `tests/plan/risks.md:4` | /qa | stale `run-tests` in feature/prototype-count lists | **this sprint** — cosmetic |
| `spec/index.md` (×1) | /qa | traceability gap | **this sprint** — parallel /qa work |
| `spec/12-runtime.md` (×1) | /qa | coverage gap | **this sprint** — parallel /qa work |
| `spec/08-modules.md` (×1) | /qa | traceability gap | **this sprint** — parallel /qa work |
| `spec/05-definitions.md` (×2) | /qa | traceability gap §5.4.2 / §5.4.3 (ADT impls) | **this sprint** — parallel /qa work |
| `spec/03-types.md` (×1) | /qa | traceability gap §3.7 (HKT) | **this sprint** — parallel /qa work |
| `repl/spec.md` (×6, excluding /mem) | /qa | coverage gaps §4.1 / §7.4 + traceability | **this sprint** — parallel /qa work |
| `tests/plan/ring4.md` | /qa | Ring 4 RC-balance assertion adoption survey | **this sprint** — parallel /qa work; results land in test plan |

Not-in-scope FIXMEs (deferred with rationale):

| File | Owning Skill | Issue | Rationale |
|------|-------------|-------|-----------|
| `stdlib/plan-stdlib.md` | /stdlib | prelude monolith remediation | Pre-existing stdlib refactor; no convergence dependency. Keep for stdlib-focused sprint. |
| `user/plan-docs.md` | /docs | docs survey items | No convergence dependency. |

## Architecture Review

**Reviewer**: `/arch`
**Verdict**: **APPROVED with conditions**

The Phase 3 + 4 scope is coherent, each step lands green independently, and the target data-model shape (G6 + G8 + G9) is the `pipeline-v4.md` §9 target — not an interim. Debt bundling is disciplined and proportionate (super-import, `/mem`, `pipeline.rs:55`, `CheckResult` slim-down, `sketch_run_tests_pass_fn_called` triage, stale `run-tests` cosmetics, 14 prior-ring `/qa` gaps). The conditions below are design-doc prerequisites for Wave 1 and a handful of shape decisions that must be pinned before any implementation wave opens. No blockers.

### Review findings

**1. Technical coherence — step sequencing (G6 → G8 → G9)** — **PASS.** Each step lands green independently. G6 is a targeted data-model move (delete `CodegenProduct`; field on entry) that can ship without touching workers' lifecycle. G8 is also data-model only (delete `PlatformRegistry`; field on entry) — its only lifecycle interaction is that platform-form handling in `src/worker.rs` now writes to `ModuleEntry::Def` instead of the registry, which Wave 2's G6 migration has already exercised. G9 (worker lifecycle rework) is correctly the riskiest, last wave. The sprint's descope contingency (ship G6; optionally G8; defer G9 to 58) preserves green-per-wave even under burden overload.

**2. No interim architecture (Principle 8) — `code: Option<Code>` on `ModuleEntry::Def`** — **PASS.** The §9.1 / §9.4 target IS `code: Option<C>` on the entry; `pipeline-v4-roadmap.md:198` explicitly defers the `SymbolTable<C: CodeStore, L: LinkerStore>` generics as an API-cleanliness item, not a shape change. `#[serde(skip)]` on a concrete `Code` is the sufficient form — Phase 5 cache serialisation re-derives code from `ast` on cache-hit load, so the field is runtime-only by design. Confirmed in new Decision 25 (`design/arch/CLAUDE.md`): Phase 3 G6 is the target shape, not a stepping stone; introducing generics now would touch 182+ call sites without behavioural payoff.

**3. `CheckResult` slim-down (Phase 1 claim audit)** — **PASS, slim-down belongs in Phase 2 scope of this sprint.** Verified by grep across `src/`, `crates/cranelisp-backend/`, `crates/cranelisp-typecheck/`:

- Production backend (`crates/cranelisp-backend/src/lib.rs:97` `compile_to_module` signature) takes NO `CheckResult`. All `CheckResult` references in `crates/cranelisp-backend/src/lib.rs` are inside `#[cfg(test)]` (lines 391, 395–403, 1184, 1350, 1417, 1482, 1548, 1634, 1706, 1771, 1825, 1939, 2010, 2083, 2154, 2222, 2268, 3047) — test scaffolding bridging hand-built `Defn`s through `enrich_defn_from_side_maps` (also `#[cfg(test)]`). No production backend reader remains.
- `src/` readers (`src/session_v4.rs`, `src/worker.rs`): read only `check_result.warnings` and `check_result.display`. Other fields (`method_resolutions`, `mono_defns`, `default_method_defns`, `constrained_fn_names`, `expr_types`) are written inside typecheck during finalisation, then **dropped on match** (`src/worker.rs:2754`, `:2970` use `check_result: _`). Path confirmed by `src/session_v4.rs:1410–1428`, `:2175–2176`, `:1578`, `:1597`, `:1624`, `:1634`.
- Conclusion: Phase 1's "no longer *boundary* data" claim holds for all 5 fields targeted by the slim-down. The field set `method_resolutions / mono_defns / default_method_defns / constrained_fn_names / expr_types` is now typecheck-internal live state (used inside typecheck itself during `finalize_check_result`) that is never read outside the crate; the struct on the boundary can shrink to `warnings: Vec<Warning> + display: Option<DisplayInfo>`.
- Action: the slim-down belongs in Sprint 57 Phase 2, coupled with Wave 2 G6 — doing it later means test scaffolding in `crates/cranelisp-backend/src/lib.rs` keeps the full `CheckResult` shape alive artificially. `/typecheck`'s Wave 1 design doc MUST either (a) land the slim-down pairing with G6 in Wave 2, or (b) file a detailed FIXME explaining which live reader blocks the slim (none is predicted). The backend's test scaffolding (lines 395–403, 417–502, 540–594, 604–639) is internal-to-crate and may retain a locally-defined `TestCheckResult` helper struct — that is not a boundary concern.

**4. Design doc readiness — Wave 1 gates Wave 2** — **PASS with enumerated prerequisites.** The following docs MUST land and be `/arch`-approved before Wave 2 opens:

  a. `design/backend/compile-to-module.md` §9 update — "code write path": after `compile_to_module` returns, the priority worker writes each compiled `Code` onto `ModuleEntry::Def.code`. Introspection artifacts continue to return separately per §9.6. **Owner**: `/backend`.
  b. `design/int/phase2-codegen-convergence.md` G6 extension — the `CodegenProduct` deletion migration table (priority worker, REPL eval, introspection, `/clif`, `/disasm`, `/source` all read-sites). **Owner**: `/int`.
  c. `design/int/persistent-workers.md` (NEW) — G9 lifecycle design: spawn-at-session-init, condvar park/wake, shutdown path, `register_module` / `eval` / `reload_module` submit paths, interaction with `thread::scope` (permitted only in tests). MUST include a Sketch comparison section (per `/arch` skill §Sketch Consultation). **Owner**: `/int`.
  d. `design/int/platform-registry-removal.md` (NEW) — G8 migration design: where the `scheduling_class` currently on `PlatformRegistry::PlatformFunction` moves (entry field vs `DefKind::Primitive { primitive_kind: PlatformEffect { scheduling_class } }`), how `bind_chain_analysis.rs:137 classify_expr` resolves `scheduling_class` from the symbol table (§5 of `/int`'s Wave 1 design doc). Shared with `/platform`. **Owner**: `/int` + `/platform`.
  e. `design/typecheck/ast-annotation.md` §9 update — `code` field write path note + `CheckResult` slim-down disposition (see condition 1 below). **Owner**: `/typecheck`.
  f. `design/backend/ring2-rc.md` IO trampoline RC-leak fix note — FIXME at `crates/cranelisp-runtime/src/io.rs:58` is a real leak, not a cosmetic. **Owner**: `/backend`.

All six docs are in-scope for Wave 1. Wave 2 is gated on `/arch` sign-off of (a) and (b); Wave 3 on (d) and (f); Wave 4 on (c). (e) gates Wave 2 only if the slim-down lands in-sprint (condition 1 below).

**5. Interface changes — `ModuleEntry::Def` shape** — **PASS; updated in `interfaces.md` as part of this review.**

  - `code: Option<Code>` — `#[serde(skip)]`. Written by priority worker after `compile_to_module` returns. Read by REPL eval, introspection, linker. `Code` type stays in the integration layer (`src/session_v4.rs:447` shape retained — `{ jit: Arc<Jit>, ptr: *const u8 }`). See Decision 25.
  - `platform_fn_ptr: Option<*const u8>` — `#[serde(skip)]`. `Some` only when `kind == DefKind::Primitive { primitive_kind: PlatformEffect, .. }`. Written during `(platform …)` form processing. See Decision 26.
  - `scheduling_class` placement: `/int`'s Wave 1 design MUST decide between (a) a new sibling field on `ModuleEntry::Def` or (b) extending `PrimitiveKind::PlatformEffect` to carry it. Either satisfies the "one store" invariant; (b) is tighter because it restricts the field to the categories that actually carry a scheduling class. `/arch`'s preference is (b) but defers to `/int`'s implementation call.
  - `interfaces.md` §"Module Entries" now shows the full target shape including `got_slot`, `trait_origin`, `ast`, `code`, `platform_fn_ptr`, and the `Box<DefKind>` already in-tree.

**6. Step ordering — can G8 and G9 swap?** — **PASS, order is correct.** G8 is a data-model move (DashMap → entry field). G9 is a lifecycle rework (scoped spawn → persistent workers on condvars). Dependencies:

  - G8 → G9: not blocking (G8 writes to entry, the worker lifecycle doesn't care where platform ptrs live).
  - G9 → G8: not blocking (persistent workers still need to handle `(platform …)` forms; whether the pointer lands on a registry or on an entry is orthogonal).
  - G6 → G8: G8 can land before G6, but then G8 must temporarily route platform-fn access through a hybrid path (registry still alive). That is more scaffolding than reading/writing the entry field directly — better to finish G6 first so `ModuleEntry::Def` already has `#[serde(skip)]` discipline in tree.

The sprint's G6 → G8 → G9 ordering minimises transient state. Swapping G8 and G9 would defer the "one store" property of the symbol table and add a condvar-lifecycle risk onto an unchanged platform path — no benefit. Order stands.

**7. /int burden — "VERY HEAVY" assessment** — **PASS with descope commitment pinned.** The three-change sequence is genuinely heavy: G6 touches every code-read site (priority worker, REPL eval, 6 slash commands), G8 touches platform-form handling + IO trampoline + `bind_chain_analysis.rs`, G9 reworks `CompilerSession::new` / `register_module` / `eval` / `reload_module`. The draft's descope options A (ship G6 only) and B (ship G6+G8 only) are the right fallbacks. Condition: `/sprint` MUST escalate to user at the end of Wave 1 if `/int`'s design-doc authoring time exceeds 4 hours — that is the leading indicator of overload. If Wave 2 G6 lands and Wave 3 G8 starts but regresses the 14-failure baseline, `/sprint` invokes Descope B regardless of schedule pressure. See condition 4 below.

**8. Inter-wave gates** — **PASS.** Wave 0 (super-import) unblocks `/port`. Wave 1 (design + `/arch` approval) gates all implementation. Waves 2/3/4 are sequential with `/review` after each. Wave 5 (prior-ring coverage) runs in parallel. Wave 6 (showcase + close) depends on 2/3/4. Gate criteria in each wave are concrete and testable. One refinement condition: Wave 2's "cargo clippy clean" gate must be applied per-skill (each implementation crate clean at its own cleanup pass, per memory/feedback_agents_clean_their_crate.md) — the SPRINT.md reads as a global clippy check which is correct for the close but not sufficient mid-wave. Condition 5.

**9. Spec/design consistency — stale references in `design/arch/`** — **PASS with self-corrections applied.** The draft cleans up 7 downstream-owned stale `run-tests` references via FIXME. `/arch` self-audit of `design/arch/` found three stale references and fixed them in-place during this review: `design/arch/roadmap.md:120` ("`run-tests` special form") → `discover-tests` / `run-test` builtins + `/run-tests` slash command; `design/arch/roadmap.md:125` (trace list) → `/run-tests`; `design/arch/roadmap.md:139` (acceptance list) → builtins + slash command. `pipeline-v4-roadmap.md` G9/G10/G11 gap table (lines 62–80) matches the Phase 4 Step 4b text — G9 is LOW-severity worker-lifecycle rework, G10/G11 fall out of G9. Confirmed accurate.

### Conditions for Approval

1. **`CheckResult` slim-down lands in Wave 2, paired with G6.** `/typecheck` Wave 1 design doc (`design/typecheck/ast-annotation.md` §9) MUST commit to slimming `CheckResult` to `{ warnings, display }` in Wave 2. Backend test scaffolding that constructs full `CheckResult` values moves to a crate-internal `TestCheckResult` helper (not a boundary-visible change). If a live reader of any of the 5 slim-target fields is discovered during design authoring, `/typecheck` files a FIXME with the concrete reader's file:line and the slim-down moves to Phase 5 with rationale; otherwise it ships this sprint.

2. **All six design docs in finding 4 land before Wave 2 opens.** Wave 1 gate criterion is concrete: (a) `design/backend/compile-to-module.md` §9 code-write path, (b) `design/int/phase2-codegen-convergence.md` G6 extension, (c) `design/int/persistent-workers.md` NEW (with Sketch comparison), (d) `design/int/platform-registry-removal.md` NEW, (e) `design/typecheck/ast-annotation.md` §9 update, (f) `design/backend/ring2-rc.md` IO-trampoline fix note. `/arch` reviews each for Sketch-comparison adequacy and pipeline-v4 coherence.

3. **`scheduling_class` placement decided in Wave 1, not discovered in Wave 3.** `/int` + `/platform` joint design (doc d above) MUST pick: field on `ModuleEntry::Def` vs. field inside `PrimitiveKind::PlatformEffect { scheduling_class }`. `/arch` preference: the latter (tighter scope), but defers. Decision recorded in the design doc + a one-line update to Decision 26 if the enum-variant path is chosen.

4. **Descope triggers pinned in `/sprint` close checklist.** Descope B (ship G6 + G8; defer G9) MUST auto-fire if: (i) `/int`'s Wave 1 design authoring exceeds 4 hours, or (ii) Wave 2 G6 regresses the 14-failure baseline, or (iii) Wave 3 G8 regresses the 14-failure baseline. `/sprint` escalates to user at each trigger, but the default is descope. This discipline protects against the quality-gate lesson from Sprint 25 ("getting things working by not doing them isn't getting things working") — the architect's job is to prevent partial-G9 from shipping, not to accept it under schedule pressure.

5. **Per-wave clippy clean is per-crate, not global.** The Wave 2/3/4 gate criterion "cargo clippy clean" means: every crate the wave touched is clippy-clean at wave close. Global `cargo clippy` at sprint close is still required (Wave 6).

6. **G8 IO-trampoline RC-leak fix is not cosmetic.** `crates/cranelisp-runtime/src/io.rs:58`'s intermediate Pure/Effect node leak is a real RC leak. `/backend` Wave 3 acceptance criterion MUST include `/qa`'s RC-balance integration test exercising the trampoline path — not just "platform tests pass". This is non-negotiable; a leaking trampoline under Ring 4's IO surface would pollute every Ring 4+ program.

### Architecture updates applied during this review

- `design/arch/CLAUDE.md` — added Decision 25 (`code: Option<Code>` on `ModuleEntry::Def` is the §9 target, not interim; generics deferred) and Decision 26 (`platform_fn_ptr: Option<*const u8>` on `ModuleEntry::Def`; `PlatformRegistry` deleted; `scheduling_class` placement open in Wave 1 design).
- `design/arch/interfaces.md` §"Module Entries" — `ModuleEntry::Def` expanded to show the full post-Phase-3+4 target shape: `scheme, visibility, docstring, param_names, kind: Box<DefKind>, callees, got_slot, trait_origin, ast, code (#[serde(skip)]), platform_fn_ptr (#[serde(skip)])`. The stale "Note on `ModuleEntry::Def.ast`" admonition updated to reflect the full shape now present in the variant definition.
- `design/arch/roadmap.md` — three stale `run-tests` references updated to the current builtins + slash command.

No FIXMEs filed against other skills during this review — the SPRINT.md draft already enumerates every cross-skill request this sprint needs (7 stale-reference FIXMEs filed during Phase 1, plus the 14 `/qa` coverage gaps).

### Phase 3a Design Review (step 9)

**Reviewer**: `/arch`
**Verdict**: **APPROVED with conditions** (carryover + 2 new conditions)

Four design docs authored in parallel by `/backend`, `/int`, `/typecheck`, `/platform`:
1. `design/backend/compile-to-module.md` §9.1 (G6 write path) + §9.2 (CodegenProduct elimination); `design/backend/ring2-rc.md` §3.5 (IO trampoline leak fix).
2. `design/int/phase2-codegen-convergence.md` §13 (G6 extension, 12 subsections); `design/int/platform-registry-removal.md` (NEW, 12 §); `design/int/persistent-workers.md` (NEW, 12 §, with Sketch-comparison acknowledging no sketch antecedent).
3. `design/typecheck/ast-annotation.md` §10 (G6 interaction + CheckResult slim-down audit).
4. `design/platform/platform-registry-removal.md` (NEW).

#### Review findings

**A. Architectural coherence (all four docs)** — **PASS.** No contradiction on what G6/G8/G9 mean, what changes, what gets deleted. The three-way convergence on `scheduling_class` placement is striking: `/arch`, `/platform`, and `/int` all independently selected Option B (variant-internal `PrimitiveKind::PlatformEffect { scheduling_class }`) from the same rationale (Principle 6 + Principle 7: ill-formed states become unrepresentable; dead-state on non-platform entries is eliminated). Decision 26 in `design/arch/CLAUDE.md` has been tightened to declare this **final** rather than open.

**B. Correct crate boundaries** — **PASS.** `/typecheck`'s CheckResult slim-down audit (§10.2) is methodical: grep across `src/`, `crates/cranelisp-backend/`, `crates/cranelisp-typecheck/` for each of the five fields. Every backend hit is inside `#[cfg(test)] mod tests`; every `src/` hit is on the accumulator (typecheck-internal), not on `CheckResult`. Zero LIVE BACKEND READERS across all five slim-target fields. The slim-down does not cross into `cranelisp-backend` except for an internal `TestCheckResult` helper under `#[cfg(test)]` that never leaks across the crate boundary. Proposal is sound.

**C. No dependency violations** — **PASS.** `cranelisp-types` stays acyclic. `cranelisp-typecheck` does not depend on `cranelisp-backend`. Per `/int` §13, the priority-worker writes to `ModuleEntry::Def.code` inside the backend's `compile_to_module`, so the write-site crosses the `src/` → `cranelisp-backend` boundary but the direction is correct (backend writes into a type owned by `cranelisp-types`). The `Code` type stays in the integration layer per Decision 25 — no new `cranelisp-backend` → `src/` reverse dependency.

**D. Consistent with existing decisions** — **PASS with two tightenings applied during review.** Decision 25 unchanged. Decision 26 tightened to pin Option B as final (three-way convergence rationale recorded). Three new decisions added to cover boundary-crossing items the design docs raised:
- **Decision 27** — G8 → G9 sequencing invariant (the `Mutex<PlatformRegistry>` is a borrow-checker obstacle for G9, so G8 must land first).
- **Decision 28** — per-worker (not per-session) JIT is the G10 target shape, not a stepping stone. Rotation policy is a future Wave 4+1 optimisation.
- **Decision 29** — `rc::dec_shallow_io` is a genuine `cranelisp-runtime` primitive (not throwaway): the shallow single-node dec is the Ring 4 dual of transitive consume and will recur for any runtime state-machine walker over an RC-tracked tree.

**E. Interactions between skills are sound** — **PASS.** Ownership boundary clear: typecheck writes `ast`; backend writes `code`; integration orchestrates. `/typecheck` §10.1 states the hard invariant ("`/typecheck` MUST NOT touch `code`; `/backend` MUST NOT touch `ast`") and backs it by enumerating every category of entry (§10.1 per-category table). `/backend` §9.1.3 specifies the write happens inside `compile_to_module` post-`finalize_definitions`, before return. `/int` §13.2 confirms only one writer path (`inline_jit_codegen_for_names`) and shows the read sites all collapse into one pattern (`symbol_tables[module].get(name).code`). The priority worker does NOT stage anything into a side map — confirmed by §13.3 read migration table (10 reader sites, all migrate to the symbol-table path; no parallel side-store survives).

**F. Principle 8 compliance** — **PASS.** The shallow `rc::dec_shallow_io` helper (Decision 29) is a genuine primitive, not throwaway — the "outer-alloc-only dec, fields already re-owned" pattern is a recurring Runtime concern. The per-worker JIT (Decision 28) is the target shape, not an interim between per-function (Sprint 56) and per-session: per-session is architecturally incorrect (`JITModule` is not `Sync`). Rotation-after-M-compiles is explicitly tagged as a Wave 4+1 optimisation (FIXME(/int) on `design/int/persistent-workers.md:206`), not required by G9. The `TestCheckResult` helper (`/typecheck` §10.2.5) is a localised test-bridge inside `#[cfg(test)] mod tests`, not a boundary type — no Principle 8 violation.

**G. Testability** — **PASS with one gap flagged for `/qa`.** All four docs state concrete test strategy:
- `/backend` §9.1.4 + §3.5.7 define RC-balance assertions for the IO trampoline fix (non-negotiable per Condition 6).
- `/int` §9 + §10.1 list per-wave unit tests and integration tests.
- `/platform` §6 triages the five `v4_platform` failures.
- **Gap**: `/platform` §6 flags that the 5 `v4_platform` test names in the 14-failure baseline are not yet pinned; `/platform` requests `/qa` record the exact five in `tests/plan/ring4.md` during Wave 1. `/arch` routes this to `/qa` as Wave-1 work (see FIXME disposition below).

#### Cross-ref reconciliation

After review, the three docs agree on G6 write-path ownership:

- `/backend` §9.1 owns the write contract (signature, lifecycle, failure semantics, cache-hit interaction, object-mode gate).
- `/int` §13.2 consumes that contract (one writer path; exhaustive reader migration in §13.3; 10 reader sites all migrate).
- `/typecheck` §10.1 states the ownership boundary (table: typecheck writes `ast`; backend writes `code`; no adapter).

The stub cross-ref in `/backend` §9.1.8 points to `/int` §13 and `/typecheck` §10 (concrete anchors now available). The stub cross-ref in `/typecheck` §10.4 (`// TODO cross-ref §9.x` to backend and `/int` G6) can now resolve to `/backend` §9.1 and `/int` §13 respectively. These are minor section-number reconciliations, not substantive changes; left as TODO markers — `/typecheck` updates in Wave 2 implementation when the anchors are first read.

The stub cross-ref in `/int` §13.11 (`TODO: exact section to be filled by /backend Wave 1 update; reference anchor reserved`) resolves to `/backend` §9.1. `/int` §13.12 TODOs:
- `TODO(/backend §9.x)` → resolves to `design/backend/compile-to-module.md` §9.1. Left as-is in `/int`'s doc; Wave 2 implementation reads the anchored section.
- `TODO(/typecheck §9)` — reconciled in this review: `/typecheck` §10.1 explicitly states typecheck does NOT write `code`; `/int`'s assumption is confirmed.

#### /int scope-risk signal

`/int` flagged (`design/int/persistent-workers.md` §10) that G9 is feasible only if Waves 2+3 land clean. The design-side scope signal is well-formed (Descope B trigger is concrete: >60% bandwidth on Waves 2+3 → auto-fire). `/arch` agrees the signal is sound and proposes an explicit Wave-3 checkpoint in SPRINT.md to make the gate operational:

> **Proposed addition to §Waves / Wave 3 Gate criterion**: After Wave 3 G8 lands green, `/sprint` measures cumulative `/int` wall-clock spent on Waves 2+3 and checks against the pre-sprint budget. If >60% of `/int` bandwidth is consumed by end of Wave 3, auto-fire Descope B (defer G9 to Sprint 58) and escalate to user. This is condition 4's trigger (iii) in observable form. `/sprint` does NOT need user confirmation to fire the descope — the trigger is automatic; escalation informs the user of the fire, does not ask permission.

This addition strengthens condition 4 by making the trigger auditable rather than a judgement call at wave close. Proposed as **Condition 7** below; user can accept or strike during final SPRINT.md review.

#### FIXME disposition

From `/int`'s `design/int/platform-registry-removal.md`:

| # | FIXME | Disposition |
|---|-------|-------------|
| 1 | `FIXME(/platform)` §3: confirm Option B alignment | **RESOLVED in this review.** `/platform`'s own design doc §3 independently selected Option B. Three-way convergence achieved. FIXME is superseded — `/int` may strike it during Wave 2 implementation. Decision 26 tightened accordingly. |
| 2 | `FIXME(/platform)` §4.2: confirm write-site inside `load_and_register_platform` | **ROUTED to Wave 1 pre-implementation.** `/platform` confirms (§4 of their doc) that `crates/cranelisp-platform/` is unchanged; `load_and_register_platform` lives in `src/platform.rs` (integration) and is `/int`-owned. `/platform` concurs in principle with the write-site placement. Left as FIXME for `/platform` to strike when they read the doc. |
| 3 | `FIXME(/platform)` §7: confirm no DLL/ABI references `PlatformRegistry` | **RESOLVED in this review.** `/platform` §4 explicitly confirms: "`declare_platform!` macro produces `PlatformFn` descriptors, not registry entries. No coupling." FIXME is superseded. |
| 4 | `FIXME(/platform)` §8: triage 5 v4_platform failures for cache-restore dependency | **ROUTED to `/qa` Wave 1.** `/platform` §6 triages but flags that `/qa` must pin exact test names. Routed to `/qa` as Wave-1 deliverable; SPRINT.md §Waves Wave 1 already lists `/qa` "Derive Phase 3+4 test cases from designs; update `tests/plan/ring4.md`" — extended to include this triage. |

From `/int`'s `design/int/persistent-workers.md`:

| # | FIXME | Disposition |
|---|-------|-------------|
| 5 | `FIXME(/int)` §4.5: Wave 4+1 JIT rotation policy | **ROUTED as post-sprint.** Decision 28 records per-worker JIT as the target and rotation as a future optimisation. Not a Sprint 57 blocker. FIXME stays in the doc as a forward-pointer. |
| 6 | `FIXME(/repl)` §8.3: measure REPL eval latency with 4 priority workers mid-compile | **ROUTED to `/repl` Wave 6.** `/repl` showcase task already exists (ring4o.demo); extended to include a latency measurement note. If >100ms median for trivial eval, `/repl` files a follow-up FIXME for a dedicated REPL-priority work level. Non-blocking for Sprint 57. |

From `/platform`'s inline "Next skills" requests:

| # | Request | Disposition |
|---|---------|-------------|
| 7 | `/arch` minor-update to Decision 26 re scheduling_class placement | **DONE in this review.** Decision 26 tightened; three-way convergence recorded. |
| 8 | `/int` `SymbolTable::resolve_chain` helper | **ROUTED to `/int` Wave 2.** `/int`'s `design/int/platform-registry-removal.md` §10 deletion list covers the read-site migration; the helper is a natural product. Left as Wave 2 implementation detail. |
| 9 | `/qa` pin the five-test identity | **ROUTED to `/qa` Wave 1.** Same route as FIXME #4 above. |
| 10 | `/backend` IO-trampoline leak fix | **COVERED by `/backend`'s own output.** `/backend` §3.5 is the response; Condition 6 gates Wave 3. |

From `/typecheck`'s ast-annotation.md §10 TODOs:

| # | TODO | Disposition |
|---|------|-------------|
| 11 | `// TODO cross-ref §9.x in design/backend/compile-to-module.md` | **RESOLVED** — anchor is `/backend` §9.1. `/typecheck` may update during Wave 2. Not a blocker. |
| 12 | `// TODO cross-ref /int's G6 §9.x extension` | **RESOLVED** — anchor is `/int` §13. Same as above. |

From `/backend`: no FIXMEs filed.

**Total dispositions**: 12. Resolved in this review: 4. Routed with concrete owner + wave: 8. No FIXME is left unrouted.

#### Additional conditions for Wave 2 to open

In addition to the six existing conditions, the Phase 3a review adds:

7. **Wave-3 checkpoint on `/int` bandwidth** (tracks condition 4 trigger (iii)). After Wave 3 G8 lands green, `/sprint` checks cumulative `/int` wall-clock on Waves 2+3 and auto-fires Descope B if >60% of budget is consumed. `/sprint` notifies user of the fire but does not require user confirmation. This makes condition 4 operationally testable rather than judgement-based.

8. **Design doc cross-refs resolved before Wave 2 close (not a gate to Wave 2 open)**. The three stub cross-refs in `/typecheck` §10.4 and `/int` §13.11/§13.12 have concrete anchors per the reconciliation above. `/typecheck` + `/int` update their cross-refs to cite `/backend` §9.1 and each other's §13 / §10 respectively during Wave 2 implementation; this is a Wave-2 exit check, not a Wave-2 open gate.

#### Verdict summary

All four design docs are **APPROVED with conditions**. The six pre-existing conditions (slim-down in Wave 2; all six design docs landed; scheduling_class placement decided; descope triggers pinned; per-crate clippy; IO-trampoline RC-leak fix non-negotiable) are carried forward. Two new conditions (Wave-3 checkpoint on `/int` bandwidth; cross-ref reconciliation in Wave 2 exit) are added by this review. `interfaces.md` §"Module Entries" + §"Definition Classification" updated to reflect Option B. `design/arch/CLAUDE.md` Decision 26 tightened; Decisions 27, 28, 29 added. `/sprint` may open Wave 2 when conditions 1, 2, 3, 5, 6 from the prior review round are met; conditions 4 and 7 are continuous monitoring across waves; condition 8 is a Wave-2 exit check.

## Skill Plans

Phase 3a complete: each design doc is landed; approaches below are concise pointers to the authoritative section + key decisions. Phase 3b per-skill authoring was compressed per user direction.

### /arch
**Task**: Review Phase 3+4 sprint scope. Update `design/arch/interfaces.md` for `ModuleEntry::Def` additions. Update `design/arch/CLAUDE.md` with any new key decisions (persistent workers convention; platform registration location). Record deferrals with rationale.
**Design doc**: `design/arch/pipeline-v4-roadmap.md` Phase 3 / Phase 4 sections; `design/arch/interfaces.md`; `design/arch/CLAUDE.md`
**Approach**: DONE in Phase 2 + Phase 3a step 9. Decisions 25–29 landed; `interfaces.md` §"Module Entries" shows full post-Phase-3+4 shape with `code: Option<Code>` + `platform_fn_ptr: Option<*const u8>` + `PrimitiveKind::PlatformEffect { scheduling_class }`. Two review rounds yielded 7 conditions for Wave 2 open. In Waves 2–4: monitor Wave-3 checkpoint (Condition 7); arbitrate super-rewrite location (Wave 0); review any follow-on design concerns surfaced by implementation.
**Acceptance**: `/arch`-approved sprint scope; `interfaces.md` coherent with Phase 3+4 target; at most one new key decision per convergence axis.

### /typecheck
**Task**: 
- Ensure `ModuleEntry::Def` extensions don't leak typecheck-internal state across the boundary. Confirm `CheckResult` slim-down safety (any field still read by backend post-Phase-1?). Add unit tests for mangled-entry / mono-entry `code` write paths (via `/typecheck` → symbol-table, read by backend).
- Clean up `infer.rs:828` stale doc-comment: the doc-comment block describes the retired `(run-tests init pass-fn fail-fn)` signature but the function below is `infer_annotate`. Remove or rewrite.
**Design doc**: `design/typecheck/ast-annotation.md` §10 (landed; G6 interaction + CheckResult slim-down plan)
**Approach**: 
- **G6 boundary**: per §10.1 ownership table — typecheck writes `ast`; backend writes `code`; both coexist on `ModuleEntry::Def`. Typecheck never touches `code`.
- **CheckResult slim**: Wave 2 pair with G6. Per §10.2 audit — all 5 target fields (`method_resolutions`, `mono_defns`, `default_method_defns`, `constrained_fn_names`, `expr_types`) have zero live backend readers; 20+ `#[cfg(test)]` hits relocate to an internal `TestCheckResult` helper. Post-slim shape: `{ warnings, display }`. Migration order per §10.3 is atomic in one Wave-2 commit batch.
- **Cosmetic**: rewrite `crates/cranelisp-typecheck/src/infer.rs:828` doc-comment (retired run-tests description above `infer_annotate`).
- **Unit tests**: alongside Wave 2 implementation in `crates/cranelisp-typecheck/` `#[cfg(test)] mod tests` — mangled-entry + mono-entry `ast` invariants; post-slim `CheckResult` shape round-trip.
**Acceptance**: `CheckResult` slimmed to typecheck-internal fields only (or FIXME retained with detailed rationale); unit tests for write-code-to-entry invariants pass; no new boundary data; `infer.rs:828` doc-comment corrected.

### /backend
**Task**: 
- **G6**: `compile_to_module` writes `code: Option<Code>` onto `ModuleEntry::Def` before returning. Introspection data (`artifacts`) continues to return separately per §9.6.
- **IO trampoline leak (FIXME)**: fix `run_io_trampoline` intermediate Pure/Effect node leak.
- Confirm `compile_to_module` reads platform fn ptrs from `ModuleEntry::Def` (G8).
- Confirm byte-identical CLIF across JIT and Object persists after G6/G8.
**Design doc**: `design/backend/compile-to-module.md` §9.1 (G6 write path) + §9.2 (CodegenProduct elimination); `design/backend/ring2-rc.md` §3.5 (IO trampoline leak) + §3.3 audit-table update
**Approach**: 
- **G6 write**: per §9.1 — `compile_to_module` writes `code: Option<Code>` onto `ModuleEntry::Def` post-`finalize_definitions`, pre-return. Object mode skips the write (no `get_finalized_function` on ObjectModule). Failure semantics best-effort atomic at `CompilationResult` level — no partial rollback inside. Signature unchanged: `(module_path, names, symbol_tables, module)`.
- **IO trampoline fix** (per §3.5): introduce `rc::dec_shallow_io` primitive (Decision 29) in `crates/cranelisp-runtime/src/drop.rs` (~10 lines). Shallow dec only — transitive `consume_io_tree` would double-dec fields already re-owned by the step result. `call_continuation` at `io.rs:147` also needs `consume_closure` post-call. RC-balance integration test paired with `/qa` (Condition 6).
- **G8 platform-fn read path**: per §9.1.7 cross-ref — `compile_to_module` reads `platform_fn_ptr` from symbol table via the same `symbol_lookup_fn` mechanism used for GOT (Decision 23).
- **Byte-identical CLIF across JIT and Object**: preserved (Decision 23 unchanged).
- **Cosmetic cleanup**: `crates/cranelisp-backend/plan-backend.md:35` + `:613` stale `run-tests` / `compile_run_tests` references.
- **Unit tests**: alongside Wave 2 implementation in `crates/cranelisp-backend/` — code-on-entry write invariant; object-mode skip; failure semantics. `decision29_*` RC-balance tests on the new `rc::dec_shallow_io` helper in `crates/cranelisp-runtime/`.
**Acceptance**: `compile_to_module` writes code to symbol table; all callers read from symbol table; IO trampoline RC balance verified by new `/qa` integration test + unit tests on the new `rc::dec_shallow_io` primitive.

### /int
**Task**: 
- **G6**: Delete `CodegenProduct` DashMap on `SharedState`. All code reads go through `symbol_tables[module].get(name).code`. Priority worker / REPL eval / introspection migrated.
- **G8**: Delete `PlatformRegistry`. Platform form handling in `src/worker.rs` writes platform fn ptr onto `ModuleEntry::Def`. IO trampoline uses symbol-table lookup.
- **G9**: Workers become session-persistent (spawned in `CompilerSession::new`, parked on `condvar`). `register_module` enqueues work on scheduler. `eval` / `reload_module` submit through scheduler.
- **Super-import fix**: rewrite `super` → parent path at first import-spec consumption site (scheduler or worker, per Phase 1 design choice).
- **Pipeline cleanup**: delete `compile_and_execute_expr`'s `&Program` fallback param.
- **`/mem` command**: thin wrapper around `cranelisp_runtime::alloc_count()` / `dealloc_count()`.
- Priority-worker unit tests covering: code-on-entry write path, platform-fn-on-entry write path, persistent-worker lifecycle (park, wake, cycle).
**Design doc**: `design/int/phase2-codegen-convergence.md` §13 (G6 extension); `design/int/platform-registry-removal.md` (NEW, G8); `design/int/persistent-workers.md` (NEW, G9+G10+G11)
**Approach**: 
- **G6** (per §13): delete `CodegenProduct` DashMap on `SharedState`. All 10 code-read sites migrate to `symbol_tables[module].get(name).code` (§13.3 migration table). Priority worker, REPL eval, introspection (`/clif`, `/disasm`, `/source`), cross-module GOT symbol_lookup_fn — one pattern. `finalize_module` REPL `__expr` special case deleted (`__expr` flows through `compile_to_module` like any name).
- **G8** (per `platform-registry-removal.md`): delete `src/platform_registry.rs` entirely. `(platform ...)` form handler in `src/worker.rs` writes `platform_fn_ptr` onto `ModuleEntry::Def` with `kind: PrimitiveKind::PlatformEffect { scheduling_class }` (Option B — Decision 26 final). IO trampoline reads via symbol-table lookup. `bind_chain_analysis.rs:137 classify_expr` resolves `scheduling_class` from the variant via destructure-and-read. Wave-2 helper: `SymbolTable::resolve_chain` for Import chain walking.
- **G9** (per `persistent-workers.md`): spawn N priority workers (bounded `[1, 8]`) in `CompilerSession::new`. Condvar park/wake/drain. Per-worker JIT (Decision 28 — `JITModule` is not `Sync`). `register_module` enqueues on scheduler; `eval` submits and blocks; `reload_module` re-registers through scheduler. Shutdown: scheduler signals, workers drain, session `Drop` joins. G8 before G9 is critical (Decision 27) — G8 deletes the `Mutex<PlatformRegistry>` swap that is a borrow-checker obstacle.
- **Super-import fix**: Wave 0. Arbitration by `/arch` between frontend capture-time rewrite vs. scheduler consumption-time rewrite. Either location is fine; picking one ends Principle 7 drift.
- **Pipeline cleanup**: delete `compile_and_execute_expr`'s `&Program` fallback param in Wave 2 alongside G6 read-site migration.
- **`/mem` command**: thin wrapper over `cranelisp_runtime::alloc_count()` / `dealloc_count()` / `bytes_current()`. Wave 6 or parallel with Wave 2 if bandwidth.
- **Unit tests**: priority-worker lifecycle (spawn, park, wake, drain, shutdown race); code-on-entry write; platform-fn-on-entry write; concurrent `register_module`; reload-during-compile.
- **Scope risk**: self-monitor Wave-2+3 wall-clock. If >60% of budget, auto-fire Descope B (defer G9 to Sprint 58) per Condition 7. Notify user; no approval required.
**Acceptance**: `CodegenProduct`, `PlatformRegistry`, `thread::scope` worker blocks deleted; persistent-worker lifecycle design-reviewed by `/arch`; 14-failure baseline preserved or improved; `cargo clippy` clean per-crate per wave.

### /platform
**Task**: Confirm platform function registration flows end-to-end through the new G8 path. IO platform + any Ring 4 platform DLLs continue to work. Triage the 5 `v4_platform` failures — Phase 4 is expected to fix them.
**Design doc**: `design/platform/platform-registry-removal.md` (NEW — parallel to `/int`'s doc, focused on crate boundary + ABI)
**Approach**: 
- **`crates/cranelisp-platform/` API unchanged** — `SchedulingClass`, `PlatformManifest`, `OwnedPlatformFnDescriptor`, `CLIO`/`CLString`/`CLOwned`, `declare_platform!`, `HostContext` all survive G8. Deletion confined to binary crate (`src/platform_registry.rs`).
- **`scheduling_class` placement**: Option B (variant-internal `PrimitiveKind::PlatformEffect { scheduling_class }`) — three-way convergence with `/arch` + `/int`. Decision 26 final.
- **v4_platform triage**: 5 tests expected to flip green — `v4_platform_form` (:560), `v4_platform_stdio_print` (:751), `v4_platform_io_trampoline` (:773), `v4_platform_import_and_use` (:797), `v4_platform_multiple_calls` (:835). `v4_platform_empty_registry` (:819) is structurally non-platform (not in failing set; must not regress).
- **Cosmetic cleanup**: `crates/cranelisp-runtime/plan-platform.md:74` + `crates/cranelisp-runtime/src/trace.rs:380` stale "run-tests timing" references.
- **Sketch comparison**: divergence justified — sketch's three-way scatter (JIT `dynamic_symbols` + TC `platform_scheduling` + `PlatformRegistry`) is the Principle 7 anti-pattern; G8 consolidates.
**Acceptance**: 5 `v4_platform` failures pass; `v4_platform_empty_registry` does not regress; no regression on IO platform tests; cosmetic FIXMEs cleared.

### /frontend
**Task**: 
- Super-import rewrite. Audit `crates/cranelisp-frontend/src/module_extract.rs` for the `(import [super [*]])` capture point. Two options — rewrite at capture time (frontend) or at scheduler consumption time (/int). `/arch` to arbitrate which is authoritative per Principle 3 (dependency flows toward stability: module identity is a frontend concern).
- Clean up stale `run-tests` references: `ast_builder.rs:990` (section-header comment is wrong — the function below is `build_trace`), `plan-frontend.md:142,414` (historical Ring 0 rejection notes — assess whether still meaningful given the special form is retired).
**Design doc**: one-page decision record in `design/frontend/super-import.md` to author alongside Wave 0 arbitration.
**Approach**: 
- **Wave 0 — super-import**: `/arch` arbitrates between (a) frontend rewrite at `crates/cranelisp-frontend/src/module_extract.rs` capture time — module identity is a frontend concern (Principle 3); or (b) scheduler consumption-time rewrite. Sketch reference: `sketch/src/module.rs:1429-1434`. Spec: `spec/08-modules.md §8.3.7` (MUST rewrite; MUST error at root).
- **Cosmetic cleanup** (Wave 5 parallel): `crates/cranelisp-frontend/src/ast_builder.rs:989` section header fix (`run-tests expression` → `trace expression`); `crates/cranelisp-frontend/plan-frontend.md:142` + `:414` remove retired special-form rejection rows.
- **Unit tests**: `cranelisp-frontend` `#[cfg(test)]` — super-rewrite positive case for `(mod test (import [super [*]]))`; negative case for `super` at root module.
**Acceptance**: exemplar `(mod test (import [super [*]]) …)` compiles and runs; spec §8.3.7 unambiguously fulfilled; negative case (`super` at root module) produces the spec-mandated error; stale `run-tests` comments removed or corrected.

### /qa
**Task**: 
- Work through the 14 FIXME(/qa) entries on `spec/*.md`, `repl/spec.md`, `tests/plan/ring4.md`. Each resolution is either: add a test and update the annotation to `[Tested …]` / `[Tested+Neg …]`; or delete a stale annotation and update the section.
- **Triage `sketch_run_tests_pass_fn_called`** (`tests/sketch_port.rs:1602`). The builtins `discover-tests` and `run-test` are in the language. The test composes them into a user-defined `my-run-tests`. Determine whether the failure is: (a) a defect in the builtins — file FIXME(/int) or FIXME(/backend) with the root cause; or (b) a test-authoring issue (wrong assertion, stale syntax) — fix or delete the test. Close the failure in-sprint either way.
- Update `tests/plan/ring4.md:3` and `tests/plan/risks.md:4` to reflect that `run-tests` is no longer a language feature — the list should name `discover-tests` / `run-test` builtins + `/run-tests` slash command instead.
- Integration tests (in `tests/`) for Phase 3+4 convergence: code-on-entry observable from REPL `/clif` introspection; platform fn resolved from symbol table; super-import positive + negative case.
- Ring 4 RC-balance assertion adoption survey (FIXME on `tests/plan/ring4.md`) — report scope in `tests/plan/ring4.md` addendum.
- Close-time coverage audit (step 22).
**Design doc**: `tests/plan/ring4.md` — Sprint 57 section landed (G.0–G.9 subsections with ~97 test cases, ~38 unit routed to owning skills + ~59 integration `/qa`-owned).
**Approach**: 
- **Wave 0 tests**: super-import positive + negative integration tests per `spec/08-modules.md §8.3.7`. Land un-ignored; fail before Wave 0 implementation, pass after.
- **Wave 2 tests (G6 + CheckResult slim)**: 11 integration tests — code-on-entry via `/clif` introspection; `CodegenProduct` deletion regression guard (grep); cache-hit first-call JIT populates `code`; cross-module GOT call; 1 `v4_cache_hit_dep` flip target; 3 multi-sig JIT regression guard.
- **Wave 3 tests (G8 + IO-RC fix)**: 13 integration tests, **including non-negotiable IO-trampoline RC-balance test via `assert_rc_balanced_with` (Condition 6)**. 5 v4_platform flip targets pinned by exact name; `v4_platform_empty_registry` regression guard.
- **Wave 4 tests (G9 persistent workers)**: 8 integration tests — concurrent `register_module`; reload-during-compile race; per-worker JIT isolation; `thread::scope` grep regression guard.
- **Wave 5 (prior-ring)**: resolve 14 `FIXME(/qa)` entries. Each → add test + promote annotation to `[Tested …]` / `[Tested+Neg …]`, OR fix stale annotation.
- **RC-balance adoption survey**: outcome in `tests/plan/ring4.md §G.8`.
- **Sprint-56 triage — `sketch_run_tests_pass_fn_called`**: routed to `/int` as implementation defect (TestRunnerState pointer plumbing reads `codegen_products`; Wave 2 G6 migration to symbol-table lookup likely fixes it as a free side effect). If still failing after Wave 2: secondary candidate is Wave 3 IO-trampoline RC fix. Do not edit/delete the test.
- **Close-time audit (step 22)**: spec-surface coverage — every requirement in scope has a passing test.
**Acceptance**: 14 FIXME(/qa) resolved; Phase 3+4 integration tests pass; close-time coverage audit reports zero prior-ring coverage gaps and zero new negative-coverage gaps in Ring 4.

### /review
**Task**: Review each implementation wave after build-green. Blockers (B) / Important (I) / Suggestions (S). Focus areas:
- Wave 1 (G6): `CodegenProduct` actually gone from source; no residual DashMap-of-code.
- Wave 2 (G8): `PlatformRegistry` gone; platform lookups go through symbol table.
- Wave 3 (G9): no `thread::scope` for workers outside tests; worker lifecycle matches `design/int/persistent-workers.md`.
- Cross-wave: `code: Option<Code>` serde-skip confirmed; `Code` type stays in the integration layer per `pipeline-v4-roadmap.md:198` note.
**Design doc**: `design/review/checklist.md` (update Phase 3+4 section at Wave 2 open)
**Approach**: 
- **Post-Wave-2 review**: `CodegenProduct` gone from source tree (grep-based); no residual DashMap-of-code; `compile_to_module` code-write happens post-`finalize_definitions` per `/backend §9.1.3`; `CheckResult` slim-down preserves `{ warnings, display }` shape; `TestCheckResult` helper is `#[cfg(test)]`-only and doesn't leak across crate boundary.
- **Post-Wave-3 review**: `PlatformRegistry` gone; all platform lookups go through symbol-table; `scheduling_class` placement matches Decision 26 (variant-internal); IO-trampoline RC balance verified; `rc::dec_shallow_io` helper matches Decision 29 shape.
- **Post-Wave-4 review**: no `thread::scope` for workers outside tests; worker lifecycle matches `design/int/persistent-workers.md`; per-worker JIT per Decision 28; shutdown-race handling sound.
- **Cross-wave**: `code: Option<Code>` `#[serde(skip)]` confirmed; `Code` type location consistent with Decision 25 (integration layer); Decisions 25–29 applied consistently; no Principle 8 violations (interim scaffolding).
- **Deferral escalation**: any Important finding deferred must update the deferral-count table; 2x-deferred requires user approval.
**Acceptance**: all Blockers resolved in-sprint; Importants resolved or explicitly deferred with rationale; deferral escalation applied correctly.

### /sprint
**Task**: Drive the phased schedule. Review each wave's green baseline. Escalate scope risk to user if `/int` reports burden overload. Enforce FIXME gate between waves. Confirm showcase adequacy.
**Acceptance**: sprint closes with green baseline, new demo, clean FIXME scan, clean coverage audit.

### /stdlib
**Task**: 
- Run stdlib integration tests against the Phase 3+4 build. No stdlib change expected — this is a pipeline-internal sprint.
- **Optional**: Assess whether a user-level `run-tests` convenience fn belongs in stdlib (e.g. `stdlib/testing.cl`), composed on top of the `discover-tests` + `run-test` builtins. See `tests/sketch_port.rs::sketch_run_tests_pass_fn_called` for the composition pattern. If yes, add it with appropriate tests. If no (the `/run-tests` slash command is sufficient), record the decision in `stdlib/plan-stdlib.md`.
- Provide a showcase demo excerpt if stdlib surface changes.
**Approach**: 
- **Wave 6 regression sweep**: run 54/54 stdlib integration tests against the Phase 3+4 build. No stdlib surface change expected — this is pipeline-internal.
- **`run-tests` convenience fn decision**: defer to Sprint 58 stdlib-focused work. Record the decision in `stdlib/plan-stdlib.md` with rationale: `/run-tests` slash command + `discover-tests`/`run-test` builtins meet current user needs; a stdlib wrapper is low-value churn in a pipeline-internal sprint. `sketch_run_tests_pass_fn_called` provides the user-composition reference pattern.
**Acceptance**: stdlib tests pass; explicit stdlib/plan-stdlib.md decision on the `run-tests` convenience fn recorded; no unexpected stdlib surface change.

### /examples
**Task**: Run `examples/*.cl` against the Phase 3+4 build. Report any regression. Refine example plan if a convergence step surfaces inference friction.
**Approach**: Wave 6 regression sweep — 15/15 examples expected. Capture any inference friction revealed by the convergence as FIXME(/int) or FIXME(/typecheck). No implementation work unless a regression surfaces.
**Acceptance**: all examples compile and run; no regression.

### /port
**Task**: 
- Run the exemplar Sudoku Solver against the Phase 3+4 build **after super-import fix lands**.
- Verify all exemplar modules compile (grid, solver, html, form).
- Provide the showcase demo excerpt (`repl/demos/…`) that showcases exemplar-as-Phase-3+4 consumer.
**Approach**: 
- **Block** until Wave 0 super-import fix lands — exemplar cannot run without it.
- **Wave 6**: run full exemplar Sudoku Solver end-to-end. Verify all four modules (grid, solver, html, form) compile and link. File FIXME(/int) or FIXME(/backend) if any module fails — those are Sprint 57 regressions. Contribute a vignette into `/repl`'s `ring4o.demo` showing exemplar solver progress.
**Acceptance**: exemplar runs end-to-end; demo plays cleanly; any exemplar-surface issue filed as FIXME on owning skill.

### /repl
**Task**: 
- Create `repl/demos/ring4o.demo` showcasing Phase 3+4 deliverables. Target vignettes:
  - Platform fn loaded + introspected via symbol table (`(print "hello")` + `/sig print`)
  - Cross-module code lookup through `/clif` or `/disasm`
  - `/mem` command reports live allocations
  - Persistent-worker visible via faster repeat compilation (if measurable)
- Verify all prior demos play cleanly (regression gate).
- Refine `repl/spec.md` for any Phase 3+4-surfaced REPL behaviour (e.g. `/mem` format).
**Design doc**: `repl/spec.md` (update `/mem` spec + if any Phase 3+4 output format drifts)
**Approach**: 
- **`/mem` command + spec**: specify `/mem` output format in `repl/spec.md §4.2` alongside other slash commands. Implementation by `/int` (thin wrapper over `cranelisp_runtime::alloc_count()` / `dealloc_count()` / `bytes_current()`). Resolve `repl/spec.md:385` FIXME.
- **`ring4o.demo`**: Wave 6 — 4 vignettes per draft. Include `/port`'s exemplar vignette. Optionally measure REPL eval latency under worker contention (per FIXME(/repl) on `design/int/persistent-workers.md §8.3`). If median >100ms for trivial eval, file follow-up FIXME for a dedicated REPL-priority work level.
- **Prior demos regression sweep**: run all existing `repl/demos/*.demo` and confirm clean output.
- **6 FIXME(/qa) on `repl/spec.md`**: parallel Wave 5 work with `/qa`; some are traceability updates, some are coverage requests (§4.1 / §7.4).
**Acceptance**: `ring4o.demo` plays cleanly; prior demos regression-free; `/mem` specified in `repl/spec.md`.

### /docs
**Task**: Audit `user/` for stale references. Pipeline-internal sprint → low burden. Refine `user/plan-docs.md` if a Phase 3+4 change surfaces doc friction.
**Approach**: Wave 6 — grep `user/` for stale references (retired special forms, removed APIs). Refine `user/plan-docs.md` only if Phase 3+4 surfaces user-visible friction — unlikely given the pipeline-internal nature. Report no-op if clean.
**Acceptance**: no stale user docs; plan refined if applicable.

### /spec
**Task**: Scan completed-ring `[R0..R3 Sx]` coverage gaps (close-time sweep). Coordinate with `/qa` on any new FIXME(/qa) filings. Confirm spec §8.3.7 is unambiguous post-super-import fix.
**Approach**: 
- **Wave 5 parallel**: run close-time prior-ring sweep alongside `/qa`'s 14-FIXME resolution work. File any newly discovered gaps as FIXME(/qa).
- **Wave 0 follow-up**: after super-import fix lands, verify `spec/08-modules.md §8.3.7` is unambiguous. File FIXME(/spec) on itself if rewrite needed. (The spec already mandates the rewrite; expected: no change needed.)
- **Read-only task, can slot any wave.**
**Acceptance**: close-time coverage sweep clean; no new prior-ring gaps filed unassigned.

## Waves

Wave 1 (design + `/arch` approval) completed during Phase 3a authoring + review. Implementation waves begin with Wave 0 (super-import fix, unblocks `/port`) and Wave 2 (G6) in parallel. Waves 3 + 4 are sequential. Wave 5 (prior-ring coverage) runs parallel to any wave. Wave 6 (showcase) gates sprint close.

### Wave 0 — Super-import fix (`/frontend` + `/int`)

Prerequisite for `/port` to run exemplar. Small, unblocks multiple downstream validations. No design-doc prerequisite beyond the one-page decision record.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Arbitrate super-rewrite location (frontend vs. scheduler) | completed | Option A (frontend capture-time) — `design/arch/super-import-arbitration.md`. |
| /frontend | Implement super-rewrite per arbitration | pending | Rewrite at capture in `crates/cranelisp-frontend/src/module_extract.rs`; invert `test_import_super`; add negative case. |
| /qa | Super-import positive + negative integration tests | pending | `spec/08-modules.md §8.3.7` is the contract. |
| /review | Review super-rewrite code | completed | PASS with Suggestions (0 B / 0 I / 6 S); see `design/review/sprint57-wave0-review.md`. |

**Gate criterion**: exemplar `(mod test (import [super [*]]) …)` resolves correctly; negative case (super at root) errors with spec-mandated message; test count ≥ 1602.

### Wave 1 — Design + `/arch` approval — **COMPLETE**

Phase 3 (Design) per `/sprint` skill definition. Completed during Phase 3a authoring (2026-04-18).

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Approve Phase 3+4 sprint scope | completed | APPROVED with conditions; 7 conditions recorded. |
| /backend | `design/backend/compile-to-module.md` §9 — code write path | completed | §9.1 (G6 write) + §9.2 (CodegenProduct elimination). |
| /backend | `design/backend/ring2-rc.md` §3.5 — IO trampoline RC fix | completed | Shallow `rc::dec_shallow_io` helper specified (Decision 29). |
| /int | `design/int/phase2-codegen-convergence.md` §13 — G6 extension | completed | 12 subsections; 10-reader migration table. |
| /int | `design/int/persistent-workers.md` — G9 lifecycle (NEW) | completed | Spawn/park/drain; per-worker JIT; `[1,8]` worker bound. |
| /int | `design/int/platform-registry-removal.md` — G8 migration (NEW) | completed | Shared with `/platform`. |
| /typecheck | `design/typecheck/ast-annotation.md` §10 | completed | G6 boundary + CheckResult slim-down audit (5 fields, 0 live readers). |
| /platform | `design/platform/platform-registry-removal.md` (NEW) | completed | crate boundary unchanged; Option B chosen. |
| /arch | Review designs; update `interfaces.md`; record new key decisions | completed | Decisions 25–29 landed; interfaces.md updated. |
| /qa | Derive Phase 3+4 test cases from designs; update `tests/plan/ring4.md` | completed | ~97 test cases mapped; 5 v4_platform pinned by name. |

**Gate criterion**: all design docs landed and `/arch`-approved; test plan updated; interfaces.md coherent. **MET.**

### Wave 2 — Phase 3 G6 (Code on SymbolTable)

Depends on Wave 1. Delivers G6.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | Add `code: Option<Code>` field to `ModuleEntry::Def`; `#[serde(skip)]` | pending | `Code` type stays in `cranelisp-types` as an opaque newtype or kept in integration per `/arch` call. |
| /backend | `compile_to_module` writes `code` onto `ModuleEntry::Def` before returning | pending | Introspection artifacts still returned separately per §9.6. |
| /int | Delete `CodegenProduct` DashMap; migrate all code-read sites to symbol-table lookup | pending | Priority worker, REPL eval, introspection, `/clif`, `/disasm`, `/source`. |
| /int | Delete `compile_and_execute_expr` `&Program` fallback (`src/pipeline.rs:55`) | pending | Cosmetic cleanup; no production caller. |
| /typecheck | Slim `CheckResult` if no live backend reader remains | pending | If any reader remains, file FIXME with detailed rationale. |
| /int | 4 priority-worker + introspection unit tests | pending | Written alongside the migration. |
| /backend | 2 `compile_to_module` unit tests for code-write invariants | pending | Written alongside the extension. |
| /qa | Phase 3 G6 integration tests (code-on-entry observable from REPL) | pending | Ignored-if-failing policy: spec-first, un-ignored. |
| /review | Review Wave 2 code | completed (2026-04-18) — see `design/review/sprint57-wave2-review.md` | Verdict: PASS with Importants. 0 Blockers, 3 Importants (I-1 MonoDefn dead carriers / /typecheck, I-2 stale compile-to-module.md §9.1 Code shape / /backend, I-3 stale phase2-codegen-convergence.md §1-§12 framing / /int), 7 Suggestions. Baseline preserved (14 fails). FIXMEs filed on owning design docs. Importants are design-doc cleanliness items; none block Wave 3. |

**Gate criterion**: `CodegenProduct` deleted; priority worker / REPL / introspection all read code from symbol table; 14-failure baseline preserved or improved; `cargo clippy` clean.

### Wave 3 — Phase 4 G8 (Platform on SymbolTable)

Depends on Wave 2.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Migrate platform form handling to write platform fn ptr onto `ModuleEntry::Def` | completed | `PrimitiveKind::PlatformEffect` entry carries the ptr (Decision 26 Option B). |
| /int | Delete `crates/cranelisp-platform/src/platform_registry.rs` (or equivalent location) | completed | `src/platform_registry.rs` deleted (-183 lines). `CompilerSession.platform_registry` + `.loaded_platforms` fields removed. `kept_dlls` retention pool added. |
| /platform | Update IO trampoline to resolve platform fns via symbol-table lookup | completed (moot — see `design/review/sprint57-wave3-review.md` §Focus 5) | `/int`'s Wave 1 design revealed the trampoline never read `PlatformRegistry`; thunks capture DLL fn pointers at codegen time. `/qa`'s 9 G8 integration tests cover end-to-end platform-fn registration. `cranelisp-platform` ABI surface unchanged; `SchedulingClass` re-exports via `pub use cranelisp_types::SchedulingClass`. |
| /backend | Fix `run_io_trampoline` intermediate Pure/Effect RC leak | completed | Decision 29 realised as `dec_shallow_io` primitive in `crates/cranelisp-runtime/src/drop.rs:432`. Approach 4 (ownership-aware `current_is_fresh` flag) preserves the 24 pre-existing `tests/io.rs` tests; extern boundary (`cranelisp_run_io`) is consuming via `consume_io_tree`, internal `run_io_trampoline` is non-consuming. 6 new unit tests including 100-step deep chain. |
| /int | 3 platform unit tests | completed | `platform_form_handler_writes_fn_ptr_to_entry`, `cross_module_platform_fn_resolution`, `priority_worker_stores_code_ptr_in_got_slot`, plus `bind_chain_analysis_reads_scheduling_class_from_entry`. |
| /qa | Phase 4 G8 integration tests + 5 v4_platform fix verification | completed | 9 integration tests in `tests/wave3_g8.rs`, all pass. 5 v4_platform flipped green (`v4_platform_form`, `_stdio_print`, `_io_trampoline`, `_import_and_use`, `_multiple_calls`). `v4_platform_empty_registry` regression guard passes. Condition-6 gate `g8_io_trampoline_rc_balanced` passes via Pure/bind chains. |
| /review | Review Wave 3 code | completed (2026-04-18) — see `design/review/sprint57-wave3-review.md` | Verdict: PASS with Suggestions. 0 Blockers, 0 Importants, 7 Suggestions. All 5 v4_platform flip green; 14-failure baseline preserved (composition -5 v4_platform / +5 elsewhere — exact 5 to be pinned by `/sprint`). Focus 5 confirmed `/platform` task moot. Focus 3 flagged string-literal RC residual as FIXME(/backend) at `crates/cranelisp-runtime/src/io.rs` — future sprint, not a Wave-3 gate. Focus 2 recommends one-line clarification on Decision 24 for future-reader clarity (Suggestion, not Important). |

**Gate criterion**: `PlatformRegistry` deleted; IO + platform tests pass; 5 v4_platform failures cleared; RC balance verified for IO trampoline.

**Wave-3 close checkpoint (Condition 7)**: `/sprint` measures cumulative `/int` wall-clock on Waves 2+3 against the pre-sprint budget. If >60% consumed, auto-fire Descope B (defer G9 to Sprint 58) and notify user. Trigger is automatic; notification informs, does not request approval.

### Wave 4 — Phase 4 G9 (Persistent Workers)

Depends on Wave 3. Highest-risk wave.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Spawn priority workers in `CompilerSession::new`; condvar-park | completed | `[1, 8]` worker clamp; parked on condvar; session Drop joins. |
| /int | Migrate `register_module` to enqueue on scheduler | completed | No `thread::scope` in registration; block on `wait_inmem_complete_blocking`. |
| /int | Migrate `eval` to submit through scheduler; persistent eval JIT | completed (reframed) | REPL eval retains inline-on-main-thread compile path per Decision 31 (fresh JIT per eval + custom `Drop` → `free_memory()`). The "persistent eval JIT" framing was retracted; the current shape IS the target. |
| /int | Migrate `reload_module` to re-register through scheduler | completed | G11 — `poll_and_reload` + `register_module_with_source` via scheduler. |
| /int | Delete `thread::scope` worker blocks outside tests | completed | Structurally verified by `/qa` regression guard (`wave4_g9_thread_scope_absent_outside_cfg_test`). |
| /int | 4 persistent-worker lifecycle unit tests | completed | `persistent_worker_park_and_wake`, `shutdown_under_load_no_panic`, `concurrent_register_module_two_modules_complete`, `reload_during_compile_race_completes`. All pass. |
| /qa | Phase 4 G9 integration tests | completed | 4 tests in `tests/wave4_g9.rs`, all pass. |
| /review | Review Wave 4 code | completed (2026-04-19) — see `design/review/sprint57-wave4-review.md` | Verdict: PASS with 0 B / 2 I / 5 S. Both Importants (I-1 REPL eval bypasses persistent pool, I-2 per-worker JIT not delivered) **dissolved** via Decision 31 reconciliation — Decision 28 retracted, per-batch JIT with custom `Drop` is the target, fresh JIT per eval is the target. |
| /backend | Wave-4 follow-on: custom `Drop` on `Jit` wrapper (Decision 31 reclaim) | completed | `crates/cranelisp-backend/src/jit.rs` only. `JITModule` wrapped in `Option`; `Drop` takes + calls `unsafe free_memory()`. 3 new unit tests pass. Safety invariant audited: every fn pointer derived from a Jit is backed by the session-wide `kept_jits` Arc pool (alive for session duration). Scenario 1 (REPL eval) + session-teardown reclaim fully active. Scenario 2 (per-redefinition) deferred to Sprint 58 Step 5c. |

**Gate criterion**: workers persistent; no `thread::scope` for workers outside tests; all cache + sprint23 cache/link failures either passing or clearly Phase 5-dependent; `cargo clippy` clean.

### Wave 5 — Prior-ring coverage gaps (`/qa` parallel work)

Can run in parallel with Waves 2, 3, 4. Gated by nothing (read-only against spec + tests).

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Resolve 14 FIXME(/qa) entries on `spec/*.md`, `repl/spec.md` | completed | 20+ FIXMEs resolved (14 Sprint 56 + 5 /spec Wave-5 + 1 RC-balance survey). 30 tests added (ring1.rs ×20 string primitives, ring2.rs ×4 lazy-seq + private-submodule, repl_experience.rs ×7, e2e.rs ×3). 17 spec sections promoted to `[Tested]` / `[Tested+Neg]`. |
| /qa | Ring 4 RC-balance assertion adoption survey | completed | `tests/plan/ring4.md §G.8` — ~50 sites adopted, ~30 SHOULD adopt, ~20 blocked on trampoline, rest don't need it. Adoption policy drafted. |
| /spec | Close-time prior-ring coverage sweep | completed | 5 new FIXMEs filed (repl §1.1/§11/§11.2 traceability; spec §8.2.3/§8.7.3 neg-coverage). Architectural concern: section headings systematically lag sub-section tests — recommend sprint-close-protocol bump. All resolved by /qa in the same wave. |

**Gate criterion**: 14 /qa FIXMEs resolved; coverage audit clean; no new prior-ring FIXMEs filed unassigned. **MET.**

**Wave 5 /int gaps surfaced and carried to Sprint 58** (per Option 1 disposition, user-approved):

| Test | Spec | Failure mode | Disposition |
|------|------|-------------|-------------|
| `tests/repl_experience.rs::display_overloaded_fn_shows_all_variants` | `repl/spec.md §1.3` + §4.1.1 MUST: one line per variant for multi-sig functions | REPL bare-symbol lookup returns only first signature | **Sprint 58** — `/int` plumbs multi-sig display through symbol-table introspection. FIXME(/int) inline in spec row. |
| `tests/ring2.rs::neg_private_submodule_not_importable_from_peer` | `spec/08-modules.md §8.2.3` MUST NOT: peer modules importing from `(mod- internal)` | Private-visibility enforcement not plumbed through import resolver | **Sprint 58** — `/int` adds visibility check to import resolution. FIXME(/int) at spec §8.2.3. |

Both tests are correctly left **failing, un-ignored** per `memory/feedback_failing_not_ignored.md` — they expose real spec violations, not test bugs. Sprint 57 does not commit to fixing these; they are pre-existing `/int` implementation gaps surfaced by Wave 5's spec-first test-writing.

**Additional FIXMEs filed during Wave 5** (routed to other skills):
- `FIXME(/int)` at `spec/08-modules.md:608` — Cranelisp.toml lookup (§8.11.4 item 2) not implemented.
- `FIXME(/spec)` at `spec/appendix-a-builtins.md:122` — `vec-map` / `vec-reduce` are stdlib fns, miscategorized as primitives.
- `FIXME(/spec)` at `repl/spec.md:715` — §4.1.7 classification word question ("primitive" vs "defn").
- `FIXME(/spec)` at `repl/spec.md:316` — aspirational List/Seq display format vs current ADT fallback.

### Wave 6 — Showcase (gates sprint close)

Depends on Waves 2, 3, 4.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /repl | Create `repl/demos/ring4o.demo` | completed | 66 lines, 6 vignettes (platform fn via symbol table, /clif+/disasm, /mem snapshot, /mem delta, zero-delta eval, persistent workers). Plays end-to-end clean. |
| /int | Implement `/mem` command | completed | `/mem` + `/m` alias, bare + `/mem <expr>` variants. 3 unit tests pass. `cargo check` + clippy clean. |
| /repl | Normalize `/mem` format in `repl/spec.md §3.7` | completed | Adopted /int's format verbatim with clarifications; test-coverage FIXME(/qa) for 4 §3.7 rows filed. |
| /port | Run exemplar Sudoku Solver end-to-end | completed | All 4 modules (grid, solver, html, form) compile cleanly under Sprint 57. Board prints via platform stdio + bind + print + str-concat. Solver segfaults trying to solve (pre-existing stack-overflow from Sprint 19, documented in `exemplar/CLAUDE.md`). Wave 0 super-import fix works at unit-test level; form-by-form scheduler deadlocks on parent-with-inline-`(mod test)` + `[super [*]]` per Decision 30 — exemplar test submodules disabled with FIXME(/int) pointing at Decision 30. Exemplar minor updates: explicit `(import [primitives [*]])`, `const` → `defn` for cross-module visibility, inline test submodules removed. |
| /stdlib | Stdlib integration tests | completed (via /qa full-suite) | Covered by `cargo nextest run` — stdlib integration tests pass. |
| /examples | `examples/*.cl` | completed (via /qa full-suite) | Covered by `cargo nextest run` — example integration tests pass. |
| /repl | Verify all prior demos play cleanly | completed | 24 demos replayed; 16 clean; ring4b/ring4j initially crashed on `(do (print x) (print y) …)` but both flipped green once /int's Wave-6 `unwrap_io_inline` fix landed (verified by /int's integration verification). Remaining "crashes" are test-source gaps in ring0/ring1/ring4k/external-file demos unrelated to Sprint 57. |
| /docs | `user/` stale reference audit | completed | 5 files scanned. No-op verdict: user/ is clean with respect to Sprint 57 changes. No retired-run-tests, Decision 28, or ABI-internal terminology leakage. |
| /qa | Do-chain test + full regression + coverage audit | completed | Initial run exposed 44-test regression (24 SIGBUS from Decision 31 custom Drop × eval-path interaction). Reduction pass → minimal repro → /int fix → test migration → /int RC-leak sibling fix. Final full suite: **1679/1696 passing, 17 failing (11s)**. 17 all accounted for: 15 pre-existing (corrected baseline per /qa; was documented as 14 due to sprint23 tally drift) + 2 Wave-5 spec-exposure carries. SIGBUS eliminated. Decision 31 Scenario 1 per-eval reclaim fully working. Condition 6 (IO trampoline RC balance) restored. Sibling RC leaks in batch mode (`CompilerSession::trampoline`) and defensive at `format_eval_result` also fixed. |
| /qa | Final spec-surface coverage audit | completed | Every Sprint 57 in-scope requirement has a passing test. Gaps flagged as FIXME(/qa) for Sprint 58: /mem §3.7 integration tests; Decision 31 Scenario 1 dedicated reclaim test. |

**Gate criterion (sprint close)**: all Phase 5b items in close checklist met; `ring4o.demo` plays cleanly; prior demos regression-free (modulo pre-Sprint-57 test-source gaps); **17 failing vs 15 pre-existing baseline** (2 explicit Sprint 58 carries from Wave 5 `/int` gaps); 0 ignored tests for in-scope features; SIGBUS fully eliminated; Decision 31 scenarios 1 + session-teardown active; Condition 6 preserved. **MET.**

### Wave 6 follow-on /int fixes (landed in-wave, not separate waves)

Two /int fixes landed during Wave 6 execution to address issues surfaced by `/qa`'s reduction protocol:

1. **Inline-trampoline in `compile_and_execute_expr`** (`src/pipeline.rs::unwrap_io_inline`). Eval now trampolines IO values before the per-eval `Jit` drops; returns fully-reduced `a` from `IO a`. Unifies eval and `batch_run` contracts. 2 unit tests in `src/pipeline.rs::tests`. Resolves the SIGBUS that `/qa`'s `minimal_3`/`minimal_4` isolated.

2. **Consuming RC cleanup after trampoline** (`unwrap_io_inline` + `CompilerSession::trampoline` + `format_eval_result`). Added `cranelisp_runtime::drop::consume_io_tree(raw_value)` after `run_io_trampoline` — per Decision 24's consuming convention. Sibling leaks in batch mode (`CompilerSession::trampoline`, called by `src/main.rs:77`) and defensively at `format_eval_result` were silently leaking IO trees pre-Sprint-57; now fixed. Unit test `unwrap_io_inline_rc_balanced_for_pure_node` locks down the contract.

These two fixes revealed that Decision 31's safety invariant was under-specified: heap closure `code_ptr`s in IO trees count as in-flight user code for the "still-system" condition. The in-scope fix (inline-trampoline) resolves the violation; Decision 31's canonical framing in `design/arch/CLAUDE.md` can be tightened post-close with a note: "the `Jit` safely drops at the end of `compile_and_execute_expr` only after the IO tree it constructed has been fully trampolined."

### Test-harness migration (IO eval contract)

`/qa` migrated ~75 test sites across `tests/io.rs`, `tests/io_minimal.rs`, `tests/wave3_g8.rs`, `tests/stdlib.rs`, `tests/ring4_trace.rs` from the old manual-trampoline pattern to the unified eval contract. The old pattern was latently unsound (double-executed IO, relied on Cranelift's leak-on-drop to avoid segfault); new contract matches `batch_run`'s already-correct shape. `minimal_3`/`minimal_4` renamed to `_trampolines_inline` and kept as regression guards.

### Cross-wave notes

- **Parallelism**: Wave 5 (prior-ring coverage) runs throughout. `/frontend` and `/spec` read-only tasks can slot anywhere.
- **`/review` is invoked after each code-producing wave** — not batched at the end.
- **Tests are written spec-first**: failing-against-spec tests are committed un-ignored; implementation passes must close them within the sprint.
- **Build must be green after each sub-step**. If a step breaks the build, fix before proceeding.
- **Descope contingency**: if Wave 4 (G9 persistent workers) shows burden overload during design review or Wave 1 approval, `/sprint` escalates to user to pull G9 out and defer to Sprint 58. Phase 3 + Phase 4 G8 still close cleanly on their own.

## Notes

- Baseline: 1602 passed / 14 failed / 0 skipped (Sprint 56 close).
- Prior FIXME count resolved this sprint: target 19+ (14 /qa coverage gaps + 4 in-scope FIXMEs + super-import FIXME).
- FIXME-after-close count target: 0 on source tree; acceptable to file Phase 5 tracking FIXMEs.
- Expected failure count at close: ≤9 (Phase 4 G8 clears 5 v4_platform; Phase 3 G6 expected to clear at least the single-module cache failures; cross-module cache failures legitimately Phase-5-dependent).
- Post-Wave-4 observed baseline: 1633 passed / 15 failed. `/qa` identified the extra failure (vs documented 14) as a documentation-tally drift in sprint23 count (4 actual vs 3 documented), not caused by Wave 4. Pre-existing failures only.

### Decision 31 disposition (Wave 4 follow-on)

Decision 31 (JIT memory lifecycle) was reconciled mid-sprint after /review surfaced factual errors about Cranelift 0.116's `Memory::drop` behaviour:

- **Reconciliation landed** (/arch pass): Decision 28 (persistent-per-worker JIT) **retracted**; Decision 31 established. Canonical framing: one `JITModule` per compile batch, `Arc<Jit>` tracks reachability, custom `Drop` calls `unsafe free_memory()`. Three scenarios (REPL eval / defn JIT / object) unified under one reclaim primitive.
- **Custom `Drop` shipped** (/backend): `crates/cranelisp-backend/src/jit.rs` — `JITModule` wrapped in `Option`; `Drop` consumes it via `take()` + `unsafe free_memory()`. Single-file change, safety invariant audited (no fn pointer escapes the Arc-tracked discipline; spec §10.10.1 forbids Fn platform args today; §12.4.3 + §10.12 structured concurrency preserves still-system at REPL prompt).
- **Scenario 1 (REPL eval) reclaim: ACTIVE.** Each `compile_and_execute_expr` creates a stack-local `Jit`, runs, drops → `free_memory()` fires per-eval.
- **Session teardown reclaim: ACTIVE.** `CompilerSession::Drop` → `kept_jits` drops → every batch JIT's `free_memory()` fires.
- **Scenario 2 (defn redefinition) reclaim: PARTIAL.** Currently fires only at session teardown (Arc<Jit> lives in `SharedState.kept_jits`, not on `ModuleEntry::Def.code`). Full realisation requires `Arc<Jit>` directly on the entry, which requires activating `SymbolTable<C: CodeStore, L: LinkerStore>` generics (pipeline-v4.md §9.1). This path was explicitly rejected by Decision 25 pre-reconciliation as "API cleanliness only, 182+ call sites, no behavioural payoff" — but Decision 31 supplies the missing behavioural payoff (per-redefinition reclaim).
- **Deferral**: Scenario 2 full reclaim → **Sprint 58 Step 5c** (new): activate `SymbolTable<C, L>` generics; move `Arc<Jit>` onto `ModuleEntry::Def.code`; dissolve or reshape `SharedState.kept_jits`. Bundled with Phase 5 Steps 5a (structural declarations) + 5b (cache serialization) — all three touch `SymbolTable`'s structure. /arch pass updating `pipeline-v4-roadmap.md` Phase 5 + Decision 25 (remove rejected-alt (b)) + Decision 31 (note Scenario 2 scheduling) in progress. ROADMAP.md Sprint 58 row updated to name Step 5c.
- **Forward commitment recorded**: when platform ABI gains `Fn a b` args, heap-closure-address + GOT-indirect host-callback rule preserves invariant. `spec/10-io.md §10.10.1` has the forward-committed row; Decision 31's "Callback support" sub-section has the architectural rules. No current platform uses this, so today the invariant holds trivially.
- **Review findings dissolution**: Wave 4 /review's I-1 (REPL eval bypasses persistent pool) + I-2 (per-worker JIT not delivered per Decision 28) both dissolve under Decision 31 — Decision 28 retracted, fresh-JIT-per-eval is the target, per-batch is the target. `/review` should update `design/review/sprint57-wave4-review.md` to note the dissolution on next invocation.

## Outcome

{Filled in when sprint closes.}

### Delivered

{...}

### Deferred

{...}

### Findings

{...}
