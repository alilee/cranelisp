# Sprint 58: Pipeline v4 Convergence Phase 5

**Status**: ACTIVE
**Ring**: 4 (Effects — full spec scope)
**Goal**: Close the v4 data-model programme. After this sprint, the §9 target shape is complete: structural declarations on `SymbolTable`, cache restore via `SymbolTable`, and `Arc<Jit>` lives on `ModuleEntry::Def.code` so per-redefinition JIT reclaim fires (Decision 31 Scenario 2). The pre-existing 15-failure cluster (cache SIGSEGV / cross-module GOT / sprint23 cache-link) is expected to clear as a side-effect.

## Scope

`pipeline-v4-roadmap.md` Phase 5 plus the two carried `/int` gaps from Sprint 57 Wave 5. Five sub-streams, four convergence axes plus a procedural item:

- **Step 5a — Structural declarations on `SymbolTable`** (G — new): add `imports`, `exports`, `platforms`, `submodules` fields to `SymbolTable` so the regenerator and cache reader can reconstruct a module's structure from one source. `ModuleStructure` on `SharedState` dissolves. **Owners**: `/typecheck` (field shape) + `/int` (`save.rs` + worker write-path).
- **Step 5b — Cache serialization via `SymbolTable`** (G2 completion + cache fixes): `.meta.json` serialises the enriched `SymbolTable` (types, GOT slots, AST bodies, structural declarations, callees). Cache restore reconstructs the full compilation state without re-typechecking. `CodegenInput` stashing for cache writes is removed. Expected to clear the 9 cache SIGSEGV / cross-module GOT failures + 3 sprint23 cache-link failures + 1 v4 cache-hit-dep failure (13 of the 15 pre-existing). **Owners**: `/backend` (cache crate) + `/int` (worker cache write-path).
- **Step 5c — Activate `SymbolTable<C: CodeStore, L: LinkerStore>` generics** (G12, completes Decision 31 Scenario 2): parameterise `SymbolTable` per `pipeline-v4.md §9.1`. Move `Arc<Jit>` directly onto `ModuleEntry::Def.code` (the integration layer chooses `C = Arc<Jit>`). Dissolve `SharedState.kept_jits` for Jit retention. After this lands, REPL `/mem` shows live-bytes drop on defn redefinition (Scenario 2 fires per redefinition, not just at session teardown). ~182 mechanical type-annotation touches across `cranelisp-types`, `cranelisp-typecheck`, `cranelisp-backend`, `cranelisp-frontend`, `src/`. **Owners**: `/typecheck` (trait + field shape) + `/int` (call-site sweep + retention pool dissolution) + `/backend` (cache + JIT module sites).
- **Step 5d — Carried Sprint 57 Wave 5 `/int` gaps** (3 items): (i) private-submodule import-resolver enforcement per `spec/08-modules.md §8.2.3` (closes failing `tests/ring2.rs::neg_private_submodule_not_importable_from_peer`); (ii) multi-sig REPL bare-symbol display per `repl/spec.md §1.3 + §4.1.1` (closes failing `tests/repl_experience.rs::display_overloaded_fn_shows_all_variants`); (iii) Cranelisp.toml lookup per `spec/08-modules.md §8.11.4` item 2. **Owner**: `/int`.
- **Step 5e — Sprint-close protocol update** (procedural): when the last sub-section of a heading gains `[Tested ...]`, the heading annotation auto-bumps. Drives the close-checklist refinement that `/spec` requested in Sprint 57 Wave 5. **Owner**: `/sprint` (procedural — edit close checklist) + `/qa` (apply at audit).

Plus three FIXME(/spec) carries from Sprint 57 Wave 5 (small, in-sprint resolution):
- `spec/appendix-a-builtins.md §A.3` — `vec-map` / `vec-reduce` are stdlib fns, miscategorized as primitives
- `repl/spec.md §4.1.7` — classification word ("primitive" vs "defn") for builtin lookup
- `repl/spec.md §1.5` — aspirational List/Seq display format vs current ADT fallback

### Direct failure-fixing opportunities

The 17-failure baseline (Sprint 57 close) breaks down:

| Category | Count | Expected fix |
|----------|-------|--------------|
| cache SIGSEGV / cross-module GOT | 9 | Step 5b (cache via SymbolTable) |
| sprint23 cache/link | 3 | Step 5b |
| v4 cache-hit dep | 1 | Step 5b |
| `sketch_run_tests_pass_fn_called` | 1 | Pre-existing — re-triage in this sprint (likely defect uncovered by Step 5b) |
| `sketch_port` (Sprint 57 follow-on) | 1 | Re-triage |
| `tests/ring2.rs::neg_private_submodule_not_importable_from_peer` | 1 | Step 5d (i) |
| `tests/repl_experience.rs::display_overloaded_fn_shows_all_variants` | 1 | Step 5d (ii) |

**Phase 5 target**: clear ≥13 of the 17 pre-existing failures via Steps 5b + 5d. Step 5c is independent of failure resolution but delivers the Decision 31 Scenario 2 behavioural payoff. Worst case: Step 5b lands 9 cache failures; sprint23 cache/link clears in S59 follow-up; baseline drops to ≤4 carried failures.

### Bundled pre-existing debt

Sprint 57 close surfaced six small items that are best resolved in-sprint rather than carried:

- **Exemplar test submodule deadlock** (`exemplar/grid.cl:220`, `html.cl:151`, `form.cl:108`, `solver.cl:303`) — all four exemplar modules have inline `(mod test ...)` submodules disabled because parent↔child typecheck deadlocks per Decision 30. Decision 30 explicitly lists this as the unsafe pattern; the canonical workaround is `discover-tests` + `run-test` builtins. **Disposition**: `/port` rewrites the four exemplar test submodules to use `discover-tests` + `run-test` per Decision 30's "safe pattern (c)". Removes the FIXMEs and validates the recommended pattern at exemplar scale.
- **`/mem` integration tests** (`tests/plan/ring4.md:738` FIXME(/qa)) — 4 §3.7 rows. /int's unit tests cover `format_mem_snapshot` and parser; integration coverage through `run_repl` (E2E stdout assertions on `; live:` / `; allocs:` / `; delta:` lines) was deferred at Sprint 57 close. Land as `/qa` Wave 5 work.
- **Decision 31 Scenario 1 reclaim test** (`tests/plan/ring4.md:739` FIXME(/qa)) — positive: `/mem` shows live-bytes decrease after eval; negative: bytes do not grow unbounded under repeated eval. Land as `/qa` Wave 5 work.
- **Stale doc-comment** at `crates/cranelisp-typecheck/src/infer.rs:828` — describes the retired `(run-tests ...)` signature above `infer_annotate`. Sprint 57 named it but it was not fixed. **Owner**: `/typecheck` cosmetic cleanup in any wave.
- **Stale spec citation** at `crates/cranelisp-frontend/src/module_extract.rs:120` — references §8.3.6 where the correct anchor is §8.3.7. **Owner**: `/frontend` cosmetic cleanup.
- **String-literal lifetime through `print`** (`crates/cranelisp-runtime/src/io.rs:28` FIXME(/backend)) — RC residual from Sprint 57 Wave 3. Real bug; small; route to `/backend` for in-sprint fix or one-deferral-permitted disposition with rationale.

The two `design/arch/` items (`v4-target.mmd` SVG/PNG regeneration; cleanup of FIXME(/arch) at `design/arch/CLAUDE.md:71` Decision 24 scope clarification — carried from Sprint 57 Wave 3 review) are `/arch` cosmetic cleanups; not blockers.

### Prior-ring coverage gaps (/qa)

Sprint 57 Wave 5 promoted ~17 spec sections to `[Tested ...]` / `[Tested+Neg ...]`. The negative-coverage tracker in `spec/index.md:3` is now an ongoing standing tracker rather than a per-sprint FIXME burden; `/qa` continues incremental promotion in this sprint, prioritising:
1. Module/import boundaries (§8) — what MUST NOT leak across modules; private visibility (§8.5) negative tests; super depth boundary (§8.3.7); primitives-not-in-user-category absence tests
2. Match exhaustiveness (§6.5) — non-ADT scrutinee wildcard requirement, ADT non-exhaustive rejection
3. REPL category boundaries (`repl/spec.md` §3, §4) — empty categories omitted, primitives absent from user category

Step 5d (i) closes the §8.2.3 negative path; that promotes `[Tested+Neg]` once the test passes. `/qa` Wave 5 work follows the same shape.

### /int Burden Assessment

**VERY HEAVY — comparable to Sprint 57.** Three changes land in `/int` territory:

1. **Step 5b** — `src/worker.rs` cache write-path; `crates/cranelisp-backend/src/cache/` serialise/deserialise; restore reconstructs symbol table state. Touches every cache path.
2. **Step 5c** — ~182 mechanical call-site sweeps across `src/`, `crates/cranelisp-types/`, `crates/cranelisp-typecheck/`, `crates/cranelisp-backend/`, `crates/cranelisp-frontend/`. Most are pure type-annotation changes; some require concrete-type choices in `src/session_v4.rs` (the `C` and `L` instantiation site). Plus dissolution of `SharedState.kept_jits`.
3. **Step 5d** — three small but distinct subsystems: import resolver (private visibility check), REPL bare-symbol introspection (multi-sig display), CLI / project-config (Cranelisp.toml lookup).

**Sequence**: Step 5a (small, foundational data-model addition) → Step 5b (cache via the enriched table) → Step 5c (generics activation, parallel with Step 5d items, all mostly mechanical or local) → Step 5d (independent items, can land in any order). Step 5a + 5b are tightly coupled (5b deserialises what 5a defines) so they share design + implementation waves. Step 5c is independent and can land before, alongside, or after.

**Scope is fixed; no descoping.** User direction (Sprint 58 Phase 2 close): Sprint 58 ships the full Phase 5 scope (5a + 5b + 5c + 5d + 5e + bundled debt). If `/int` reports burden risk during Wave 1 design or Wave 2 implementation, `/sprint` escalates to the user with concrete options — but does not auto-defer. The user weighs schedule risk against the convergence payoff and decides.

### Out of Scope

- **`FQTypeName` migration** — 182 call sites; display works via `type_modules` lookup. Roadmap-deferred indefinitely.
- **BL range fix (linker.rs)** — only manifests on very large codebases. Roadmap-deferred.
- **Stdlib `run-tests` convenience fn** — Sprint 57 deferred to a stdlib-focused sprint; not a convergence item.
- **Module-system redesign to lift the parent↔child deadlock** — Decision 30 explicitly flags this as future research, not on the roadmap. The exemplar test-submodule rewrite uses the documented safe pattern.
- **Stdlib prelude monolith remediation** — pre-existing stdlib refactor; FIXME on `stdlib/plan-stdlib.md`. Carry to a stdlib-focused sprint.
- **Performance baseline / benchmark infrastructure** — Ring 4 acceptance criterion `Performance within 2x of prototype` is `NOT MEASURED`. Bundle into a dedicated post-convergence sprint; not coherent with this data-model close.
- **Long-session memory profiling** — adjacent to Step 5c's reclaim work but properly belongs to a stabilisation sprint after Step 5c lands and the `/mem` integration tests confirm the contract.

## FIXME Debt

FIXMEs found during Phase 1 scan (live, source + in-scope design/spec docs):

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `exemplar/grid.cl:220` | /port (orig /int) | Test submodule disabled — parent↔child typecheck deadlock | **this sprint** — rewrite to `discover-tests` + `run-test` (Decision 30 safe pattern (c)) |
| `exemplar/html.cl:151` | /port (orig /int) | (same) | **this sprint** — same |
| `exemplar/form.cl:108` | /port (orig /int) | (same) | **this sprint** — same |
| `exemplar/solver.cl:303` | /port (orig /int) | (same) | **this sprint** — same |
| `tests/plan/ring4.md:738` | /qa | `/mem` §3.7 integration tests not yet written | **this sprint** — Wave 5 |
| `tests/plan/ring4.md:739` | /qa | Decision 31 Scenario 1 reclaim test (Scenario 2 also lands once 5c is in) | **this sprint** — Wave 5; extend to Scenario 2 |
| `crates/cranelisp-typecheck/src/infer.rs:828` | /typecheck | Stale doc-comment about retired `(run-tests ...)` above `infer_annotate` | **this sprint** — cosmetic |
| `crates/cranelisp-frontend/src/module_extract.rs:120` | /frontend | Spec citations reference §8.3.6; should be §8.3.7 | **this sprint** — cosmetic |
| `crates/cranelisp-runtime/src/io.rs:28` | /backend | String-literal lifetime through `print` RC residual (Sprint 57 Wave 3 carry) | **this sprint** — small RC fix; or one-deferral with rationale |
| `crates/cranelisp-runtime/plan-platform.md:75` | /platform | Stale "run-tests timing" reference | **this sprint** — cosmetic |
| `spec/appendix-a-builtins.md:122,129,130` | /spec | `vec-map`/`vec-reduce` miscategorized as primitives | **this sprint** — Wave 1 (small) |
| `repl/spec.md:758` (§4.1.7) | /spec | Classification word ("primitive" vs "defn") for builtin lookup | **this sprint** — Wave 1 (small) |
| `repl/spec.md:314` (§1.5) | /spec | List/Seq display format vs ADT fallback | **this sprint** — Wave 1 (small) |
| `spec/08-modules.md:639,648` (§8.11.4 item 2) | /int | Cranelisp.toml lookup not implemented | **this sprint** — Step 5d (iii) |
| `design/arch/CLAUDE.md:71` (Decision 24) | /arch | One-line scope clarification (extern Rust helpers) carried from Sprint 57 Wave 3 review | **this sprint** — cosmetic |
| `design/arch/sequence-diagram/v4-target.mmd:10` | /arch | Regenerate svg/png after edits | **this sprint** — cosmetic |
| `design/typecheck/ast-annotation.md:475` | /typecheck | (verify scope; likely Sprint 57 carry) | **this sprint** — confirm + cosmetic if applicable |
| `design/int/persistent-workers.md:206` | /int | Wave 4+1 JIT rotation FIXME — **dissolves** under Decision 31 (per-batch JIT, no rotation) | **this sprint** — strike or rewrite; reflect Decision 31 framing |
| `design/int/persistent-workers.md:375` | /repl | Measure REPL eval latency with 4 priority workers mid-compile | defer with rationale OR resolve in Wave 6 if /repl bandwidth |
| `crates/cranelisp-backend/plan-backend.md:36` (Sprint 57 carry) | /backend | (verify scope) | **this sprint** — cosmetic if applicable |

Not-in-scope FIXMEs (deferred with rationale):

| File | Owning Skill | Issue | Rationale |
|------|-------------|-------|-----------|
| `stdlib/plan-stdlib.md` | /stdlib | Prelude monolith remediation | No convergence dependency; stdlib-focused sprint |
| `user/plan-docs.md:472` | /docs | Docs survey items | No convergence dependency |
| `design/int/session-persistence.md:383` | /arch | `traitimpl-symbol-table.md` design FIXME(/arch) | Verify scope; if not Phase 5 prerequisite, carry |
| `design/backend/auto-curry-and-run-tests.md:112` | /typecheck | `total_count` on `ResolvedCall::AutoCurry` | Long-standing; ascertain whether Phase 5 breaks the workaround; defer if not |

## Architecture Review

**Reviewer**: `/arch`
**Verdict**: **APPROVED with conditions** (7 conditions)

Phase 5 is the final v4 data-model convergence wave: Step 5a places structural declarations on `SymbolTable`, Step 5b serialises the enriched table for cache, Step 5c parameterises `SymbolTable<C, L>` so `Arc<Jit>` lives directly on `ModuleEntry::Def.code` (Decision 31 Scenario 2). The three sub-steps are independent in the dependency-graph sense (none reads what another writes) but cohesive in motivation: each closes a separate axis of the §9 target shape, all three touch `SymbolTable`'s structure, and the resulting tree IS the §9.1 normative form. Step 5d ships the two carried Wave-5 `/int` gaps + Cranelisp.toml; Step 5e refines the close protocol. Bundled debt is disciplined and tightly scoped (4 exemplar test rewrites + 2 `/qa` reclaim tests + 4 cosmetic FIXMEs + 1 RC residual). No blockers.

### Review findings

**1. Technical coherence — Phase 5 sub-step independence claims** — **PASS.** The roadmap (`pipeline-v4-roadmap.md` §"Dependency Graph") declares 5a/5b/5c independent within Phase 5 once Phases 1–4 are green. Verified:

- **5a → 5b**: 5b's cache serialiser writes whatever fields are on `SymbolTable`. If 5a lands first, the new `imports`/`exports`/`platforms`/`submodules` fields serialise alongside. If 5b lands first, the cache shape ships with `Vec::new()` defaults for those fields and 5a populates them. The `schema_version` (Decision 34) handles the cross-version mismatch cleanly. **Sequencing claim correct, but pairing 5a + 5b in one wave is the right call** — together they ship one cache schema bump (`CACHE_SCHEMA_VERSION = 1`) instead of two consecutive bumps.
- **5c → 5a/5b**: 5c is type-annotation work. It touches `SymbolTable<>` everywhere but does not change which fields exist. Mechanically commutes with 5a's field additions and 5b's serialisation rewrite. **Independence claim correct.**
- **5d → all of 5a/5b/5c**: import-resolver work, REPL bare-symbol display, and Cranelisp.toml lookup each touch one localised subsystem. None reads from `SymbolTable.imports/exports/platforms/submodules` (resolver reads from `ModuleEntry::Import` chains, not the structural-decl record); none touches `Arc<Jit>` lifetime. **Independence claim correct.**

The proposed wave sequencing (Wave 2: 5a+5b together; Wave 3: 5c; Wave 4: 5d) is sound. Step 5c MAY land before Wave 2 if `/int` bandwidth permits, but the SPRINT.md ordering is the safe default.

**2. No interim architecture (Principle 8)** — **PASS for Steps 5a, 5b, 5c.**

- **Step 5a**: the four `SymbolTable` fields are the §9.1 normative shape. The four field types reused (`ImportSpec`, `ExportSpec`, `PlatformSpec`, `ModDecl`) already exist in `crates/cranelisp-types/src/module.rs` lines 369/378/396/405. No new boundary types are introduced. Migration is 1:1 from `src/save.rs::ModuleStructure` to `SymbolTable` fields. **Final shape, not interim.** Decision 33 records this.
- **Step 5b**: the cache rewrite produces the §9.5 target shape directly — `.meta.json` IS a serialised `SymbolTable` (with the Step 5a fields populated and the Step 5c generics activated if 5c has landed; otherwise `()`). The previous `CodegenInput` stashing path is deleted, not refactored into a "thin wrapper." Cache-restore reconstructs the symbol table by deserialise + re-derive `code` and `platform_fn_ptr` (re-codegen / re-resolve from manifest), no intermediate type. **Final shape, not interim.**
- **Step 5c**: the `CodeStore` / `LinkerStore` traits land as empty markers (Decision 32) — the §9.1 shape exactly. Method-bearing or trait-object alternatives were considered and rejected as throwaway infrastructure. The integration layer's concrete `Code` type is a type alias around `Arc<cranelisp_backend::jit::Jit>` (or a thin newtype if `/int`'s Wave 1 design picks one), not a new generic-over-something abstraction. **Final shape, not interim.**

No throwaway infrastructure across the three steps.

**3. Design references — design docs named in SPRINT.md skill plans** — **PASS with one addition.**

For each compiler skill with implementation work, the SPRINT.md plan currently names the design docs but the bodies read `{filled in Phase 3}`. Verified the named docs are correct + the protocols / interface types they touch:

- **`/typecheck`**: `design/typecheck/ast-annotation.md` §11 (structural decls) + §12 (generics shape) — **correct**. `/typecheck` owns `cranelisp-types/src/module.rs` so it owns the `SymbolTable<C, L>` generic + structural-decl field shape. The Phase 5 protocol is: `/typecheck` defines the field shape and the trait surface; `/int` writes the populator (`src/worker.rs` form-handlers); `/backend` writes the cache (de)serialiser.
- **`/backend`**: `design/backend/module-caching.md` major update for Step 5b; `design/backend/compile-to-module.md` minor update for Step 5c — **correct**. `module-caching.md` already has a Sketch-comparison section per `/arch`'s prior policy; **see finding 6 below**. The §9.5 target reads "the `.meta.json` file is a serialized `SymbolTable`" — the design doc must spell out the envelope shape (Decision 34's `CACHE_SCHEMA_VERSION`) and the cache-restore reconstruction path (deserialise → re-codegen `code` per defined symbol → re-resolve `platform_fn_ptr` per manifest).
- **`/int`**: 5 NEW design docs named (`symbol-table-cache.md`, `symbol-table-generics.md`, `private-submodule-import.md`, `multi-sig-introspection.md`, `cranelisp-toml.md`). **Correct burden split**. `symbol-table-generics.md` MUST include "rough order" of the 182 call-site touches and the concrete-type choice site (`src/session_v4.rs`) per the SPRINT.md skill plan's own framing.
- **`/platform`**: addendum to `design/platform/platform-registry-removal.md` — **correct**. The Step 5b cache restore must reproduce platform fn ptrs by re-resolving from the manifest (per Decision 26's serialisation discipline) — confirm in the addendum that this still works after `SymbolTable.linker` lands.
- **`/frontend`**: cosmetic-only this sprint. Step 5a's structural-decl write-path is `/int`-owned (worker form-handlers). `/frontend` confirms the form is parsed correctly into the existing `ImportSpec` / `ExportSpec` / `PlatformSpec` / `ModDecl` types and hands off to `/int` cleanly.

**Addition**: `/int`'s `symbol-table-cache.md` MUST cross-reference `/backend`'s `module-caching.md` for the envelope shape — the worker cache-write path is the producer; `/backend`'s cache crate is the consumer-and-format-owner. The two docs MUST agree on which crate owns the `CACHE_SCHEMA_VERSION` constant (recommended: `/backend` per Decision 34) and which crate the worker calls into.

**4. Interface gaps — boundary types** — **resolved in `interfaces.md` as part of this review.**

- **Step 5a fields on `SymbolTable`**: the four `cranelisp-types` types (`ImportSpec`, `ExportSpec`, `PlatformSpec`, `ModDecl`) already exist and are reused 1:1. **No new boundary types needed.** The `SymbolTable` struct gains four fields (`imports`, `exports`, `platforms`, `submodules`). `interfaces.md` §"Symbol Table" updated to show the full Phase 5 shape including these fields.
- **Step 5b cache schema versioning**: a new `schema_version: u32` field on `SymbolTable` (with `#[serde(default)]`) handles version mismatch. **No new helper API on `SymbolTable` needed for cache restore** — restore deserialises into `SymbolTable<(), ()>` directly via the existing `serde::Deserialize` derive; the `code` and `platform_fn_ptr` fields are `#[serde(skip)]` and re-derived by the priority worker (codegen) and platform manifest re-resolution respectively. Decision 34 records the version policy. `interfaces.md` updated.
- **Step 5c trait shapes**: `CodeStore` + `LinkerStore` are empty marker traits with blanket impls (`Send + Sync + 'static`). `ModuleEntry::Def.code: Option<C>` (was `Option<Code>`). Concrete-type instantiation site is `src/session_v4.rs`. `interfaces.md` §"Symbol Table" + §"Module Entries" updated to show the parameterised shape. Decision 32 records the trait shape.

The `SymbolTable<C, L>` parameterisation does not propagate into typecheck or frontend signatures because `()` is the default — those crates' function signatures continue to read `SymbolTable` (i.e., `SymbolTable<(), ()>`). The integration layer is the sole instantiation site for the concrete types.

**5. `/int` burden assessment** — **NOTED; no descope contingencies per user direction.** The burden remains VERY HEAVY (comparable to Sprint 57). User direction at Phase 2 close: Sprint 58 ships the full Phase 5 scope; descope is not on the table. Burden mitigation is purely escalation-based — if `/int` reports overload during Wave 1 design or Wave 2 implementation, `/sprint` escalates to the user with concrete tradeoffs and the user decides. No automatic deferral. This places the schedule-risk vs convergence-payoff weighing entirely with the user.

**6. Sketch comparison requirement for Step 5b cache rewrite** — **PASS with condition.** The Phase 5 cache rewrite changes the persisted shape (`.meta.json` becomes a serialised `SymbolTable`, not the current `CacheMetadata` shape). `design/backend/module-caching.md` already has a "Sketch comparison" section from earlier sprints — `/backend`'s Step 5b update MUST refresh that section to compare:
- **Sketch's cache shape**: brief description of how the prototype handled module caching (or whether it did at all).
- **v4-target cache shape**: serialised `SymbolTable` with `schema_version: u32` envelope, `code` + `platform_fn_ptr` re-derived on load, structural decls preserved as the original specification.
- **Divergence rationale**: the prototype almost certainly did not separate "structural specification" from "resolved effects" the way Step 5a does; document why this separation is load-bearing (Decision 33's rationale).

Per `/arch`'s skill definition (§Sketch Consultation), `/arch` rejects Step 5b's design doc if the Sketch-comparison section is absent or stale. **Condition 4 below makes this a Wave 1 gate.**

**7. Decision 31 + Decision 25 reconciliation; SPRINT.md framing of 5c** — **PASS.** The SPRINT.md DRAFT frames Step 5c as completing Decision 31 Scenario 2 — this matches Decision 25's updated "rejected alternative (b)" (now reclassified as **rescheduled, not rejected**) and Decision 31's Scenario 2 footnote. Specifically:

- Decision 25's alternative (b) text: "**(rescheduled, not rejected)** eagerly introduce `SymbolTable<C, L>` generics before Phase 3 lands. … Generics activation is now scheduled as `pipeline-v4-roadmap.md` Phase 5 Step 5c (gap G12), alongside the structural-declaration and cache-serialisation work."
- Decision 31's Scenario 2 footnote: "**Scheduling footnote**: as of Sprint 57, `Arc<Jit>` lives in `SharedState.kept_jits` rather than directly on `ModuleEntry::Def.code`, because the `SymbolTable<C, L>` generics … are not yet activated. Consequently, per-redefinition reclaim is deferred — Scenario 2's `Drop` fires only at session teardown, not on redefinition. Sprint 58 Step 5c (gap G12; see `pipeline-v4-roadmap.md` Phase 5 and Decision 25's rescheduling note) activates the generics and completes Scenario 2."

The SPRINT.md framing is consistent with both. After Step 5c lands, both footnotes can be tightened or struck — `/arch` action item for the close.

**8. Procedural item Step 5e** — **PASS.** The auto-bump of section-level `[Tested ...]` headings when the last sub-section gains coverage is a sound close-protocol refinement that resolves the architectural concern raised by `/spec` in Sprint 57 Wave 5 ("section headings systematically lag sub-section tests"). No interface change. `/sprint` updates the close checklist; `/qa` applies the bump at coverage audit.

**9. `interfaces.md` coherence audit (Principle 13)** — **PASS, updated in this review.** Coherence checklist after Phase 5 updates:
- [x] No structurally identical types at any pipeline boundary — `SymbolTable<C, L>` is the single store; `ModuleStructure` dissolves; no parallel structural-decl type.
- [x] No adapter functions — no `build_*` between `SymbolTable` and any other type (the cache envelope is just `serde`).
- [x] Every pipeline stage has exactly one entry point per crate — unchanged by Phase 5.
- [x] Mode differences expressed as parameters — the `C, L` generics ARE the mode parameter (typecheck sees `()`; integration sees concrete types). No two `SymbolTable` flavours exist; one type with a generic.
- [x] All spec-required `TopLevel` variants present — unchanged by Phase 5.
- [x] `Serialize`/`Deserialize` on all boundary types that need caching — `SymbolTable` derives both; the new fields (`imports/exports/platforms/submodules/schema_version`) all serialise; `code` and `platform_fn_ptr` are correctly `#[serde(skip)]`.
- [x] Module context is an explicit parameter (`CompileContext`) — unchanged by Phase 5.

### Conditions for Approval

1. **Step 5b's `module-caching.md` update MUST refresh the Sketch-comparison section** (finding 6) — comparing sketch cache shape vs. v4-target serialised-`SymbolTable` shape with explicit divergence rationale (especially the Step-5a separation between structural specification and resolved effects). `/arch` reviews and rejects in Wave 1 if missing or stale.

2. **All five `/int` Phase-5 design docs land before Wave 2 opens** (Wave 1 gate per `/sprint` methodology). Specifically: `symbol-table-cache.md`, `symbol-table-generics.md`, `private-submodule-import.md`, `multi-sig-introspection.md`, `cranelisp-toml.md`. `symbol-table-cache.md` MUST cross-reference `/backend`'s `module-caching.md` for the envelope shape and name `CACHE_SCHEMA_VERSION` ownership (recommended: `/backend` owns the constant per Decision 34).

3. **`/typecheck`'s `ast-annotation.md` §11 + §12 land before Wave 2 opens.** §11 specifies the four structural-decl fields' shape (reusing existing `cranelisp-types` types per Decision 33). §12 specifies the `CodeStore` / `LinkerStore` trait surface and confirms typecheck never observes the `C` parameter (operates on `SymbolTable<(), ()>` everywhere). Both are read-only contracts from typecheck's POV — Decisions 32 + 33 already encode the shape; the design doc records the typecheck-side observation that nothing leaks.

4. **`/int` burden monitoring escalates to user, not auto-defer** — per user direction, scope is fixed for Sprint 58; no automatic deferral. `/sprint` MUST surface concrete burden-risk signals to the user as they emerge (Wave-1 design authoring time; Wave-2 cumulative wall-clock; specific subsystems blocking). User weighs schedule risk against convergence payoff and decides whether to extend the sprint, drop scope, or proceed.

5. **Per-crate clippy gate per wave (carried from Sprint 57 Condition 5)** — every crate touched by a wave is clippy-clean at wave close. Global clippy at sprint close still required (Wave 6).

6. **`io.rs:28` string-literal RC residual is a real bug, not cosmetic** — `/backend`'s in-sprint disposition MUST either (a) ship the fix in Wave 3 alongside the IO-trampoline RC primitives revisit, or (b) escalate-with-rationale per the one-deferral-permitted policy. If `/backend` defers, the deferral rationale must name the specific symptom under which the leak would manifest in user code so `/qa` can write a regression test before deferral. (Sprint 57 carried it forward as Wave-3 follow-on without a regression test — Sprint 58 must close the loop.)

7. **Decision 31 Scenario 2 verification test owned by `/qa` Wave 5** — `tests/plan/ring4.md` already lists "Decision 31 Scenario 1 reclaim test" as a Sprint 57 carry; `/qa` MUST extend it to Scenario 2 in this sprint: REPL redefinition with `/mem` shows live-bytes drop on the redefinition (not just session teardown). This is the headline behavioural payoff of Step 5c — without the test, the demo claim is unverified.

### Architecture updates applied during this review

- `design/arch/CLAUDE.md` Decision 24 — the FIXME(/arch) inline note was resolved: scope-of-rule clarification incorporated into the decision body (extern primitives' outer Rust functions ARE the consuming boundary; private internal helpers are free to choose their own convention). FIXME removed.
- `design/arch/CLAUDE.md` — added Decision 32 (`CodeStore` / `LinkerStore` empty marker traits in `cranelisp-types`), Decision 33 (structural decls as fields on `SymbolTable`, not parallel `ModuleStructure`), Decision 34 (cache schema versioned by explicit `schema_version: u32`; mismatch invalidates as if dependencies changed).
- `design/arch/interfaces.md` §"Symbol Table" — `SymbolTable<C: CodeStore, L: LinkerStore>` parameterisation; `imports`/`exports`/`platforms`/`submodules` fields; `linker: Option<L>` field; `schema_version: u32` field; `CodeStore` / `LinkerStore` trait definitions with blanket impls. `ModuleStructure` documented as deleted at Step 5a.
- `design/arch/interfaces.md` §"Module Entries" — `ModuleEntry<C: CodeStore = ()>` parameterisation; `code` field becomes `Option<C>`; doc-comment updated for Decision 31 Scenario 2 + Decision 32 cross-references.
- `design/arch/interfaces.md` §"Summary of Changes from v1" — documented `ModuleStructure` deletion; documented `CodeStore` / `LinkerStore` traits, structural-decl fields, `linker`, `schema_version` as additions.

### FIXMEs filed against other skills during this review

None new. The SPRINT.md DRAFT and finding 3 above already enumerate every cross-skill design request this sprint needs. Conditions 1, 2, 3, 7, 8 above route work to the named owning skills via the SPRINT.md skill-plan section, not via FIXMEs.

### Carried `/arch` cosmetic items

- **`design/arch/sequence-diagram/v4-target.mmd:10` regenerate svg/png** — carried Wave-6 task. The .mmd was edited at Decision 31 reconciliation; the .svg/.png lag. Add to Wave 6 close checklist; `/arch` runs the mermaid tool at close (one-line regeneration). Not a Phase 5 blocker.

Recommended addition to SPRINT.md §Waves Wave 6:
> **/arch**: Regenerate `design/arch/sequence-diagram/v4-target.svg` + `.png` from the `.mmd` source (Decision 31 reconciliation lag). One-line cosmetic.

### Phase 3a Design Review (step 9)

**Reviewer**: `/arch`
**Verdict**: **APPROVED with conditions** (1 new condition: C8 — `compile-to-module.md` §17 to spell out raw-shape return type per CP1 arbitration). All 5 conditions remaining after user struck C4 + C5 from the Phase 2 set are SATISFIED or properly tracked. The four Wave-1 design-doc sets are inter-coherent on the §9 target shape; CP1 arbitrated in favour of Layer 2 Option B and recorded as Decision 35; CP2 deferred as `/backend` implementation choice with a recommendation; CP3 routed to `/int` Wave 2 design call as `/typecheck` proposed.

#### Per-doc-set verdicts

| Doc set | Files | Verdict | Notes |
|---|---|---|---|
| `/typecheck` | `design/typecheck/ast-annotation.md` §11 + §12 | **APPROVED** | Decision 33's four `cranelisp-types` types verified at exact cited lines (369/378/396/405). Six typecheck-side invariants on the four `Vec<_>` fields are well-formed. §12.6 sketch comparison present. Wave-2 implementation footprint is correctly sized to 6 edits inside `cranelisp-types/src/module.rs` + 1 cosmetic edit at `infer.rs:828`; zero `cranelisp-typecheck/src/*` semantic changes. **Condition C3 SATISFIED.** |
| `/backend` | `design/backend/module-caching.md` §14 (NEW) + `design/backend/compile-to-module.md` §17 (NEW) + `design/backend/ring2-rc.md` §10 (NEW addendum) | **APPROVED with C8 follow-on** | §14.8 sketch-comparison refresh is substantive (sketch's CompiledModule god-object + `try_load_cached_module()` 238-line rehydrator vs v4's serialised-`SymbolTable` + structural-decl preservation), and explicitly maps to MED-2 root cause — **Condition C1 SATISFIED**. `CACHE_SCHEMA_VERSION` constant location pinned to `crates/cranelisp-backend/src/cache/mod.rs` per Decision 34 — **Condition C2 ownership-pin SATISFIED**. `io.rs:28` regression-test symptoms named in §10.6 (positive: 3-print balanced; negative: 1000-iter ±1 gap) — **Condition C6 SATISFIED**. Form A vs Form B fix shape is properly framed as audit-driven; Form B preferred if >2 affected externs (§10.4) — see Principle 8 cross-check below. The §17 generics-activation update is consistent with CP1 Option B (backend signatures stay `SymbolTable<(), ()>`-flavoured, integration layer writes `code`) but does not yet name the raw-tuple/`CompilationResult`-extension return shape that `/int`'s consumer needs — **C8 (new) requests this in Wave 2**. |
| `/int` | 5 NEW design docs (`symbol-table-cache.md`, `symbol-table-generics.md`, `private-submodule-import.md`, `multi-sig-introspection.md`, `cranelisp-toml.md`) | **APPROVED** | All 5 docs landed before Wave 2 opens — **Condition C2 (5-doc gate) SATISFIED**. `symbol-table-cache.md` cross-references `module-caching.md` for envelope shape and names `/backend` as `CACHE_SCHEMA_VERSION` owner — **Condition C2 cross-ref SATISFIED**. Concrete-type choice `C = Code` (enum unifying `Code::Jit { Arc<Jit>, ptr }` and `Code::Linker { Arc<Linker>, ptr }`) + `L = ()` is well-justified (§2.1, §2.2) and consistent with Decision 31's `Arc<Jit>`-on-entry mandate. The 5-stage migration order (§3, §4) is sequenced for build-greenness with explicit cargo-check checkpoints at each stage — meets per-crate clippy gate framing for **Condition C5**. Both `kept_jits` AND `kept_linkers` dissolve at Step 5c (§2.3) — Decision 35 records this as binding. |
| `/platform` | `design/platform/platform-registry-removal.md` §"Addendum — Sprint 58 Phase 5" (sections A1–A7) | **APPROVED** | Cache-restore flow (§A2) re-uses `load_and_register_platform` as-is — the post-Step-5b change is the upstream "which DLLs to reload?" data source, not the resolution mechanism. The three retention pools have disjoint lifetimes per §A3 table (`SymbolTable.linker` per-module, `SharedState::kept_dlls` session-global, `Code::Jit.jit` Arc per-batch). DLL-resolution failure modes (§A4) are sound — fall-through to fresh build matches the Decision 34 schema-mismatch pattern. No regression on the 5 v4_platform tests is correctly substantiated (§A5: fresh-build paths unchanged; cache-hit paths converge). Two soft cross-skill notes (§A7) routed to `/int` (cache-crate-vs-integration division for the post-deserialise platform reload pass) and `/backend` (`CacheLoadError::DllResolutionFailed` variant). |

#### Inter-doc coherence

**§9 target shape — three-way agreement** (`/typecheck` §12 + `/backend` §17 + `/int`'s `symbol-table-generics.md`): **CONVERGENT**.
- Trait shape: empty markers `pub trait CodeStore: Send + Sync + 'static {}` + blanket impl, default `()`. All three docs name this shape verbatim.
- `()` default propagation: `/typecheck` §12.2 enumerates 5 reasons typecheck never observes `C` or `L`; `/backend` §17.1 confirms backend signatures stay `SymbolTable` (i.e. `SymbolTable<(), ()>`); `/int` §3 (Layer 1) confirms most call sites use the default. No conflict.
- Concrete `C = Code` enum vs `C = Arc<Jit>` directly: `/typecheck` §12.4 (typecheck doesn't care which); `/backend` §17.3 (gives a stub `type Code = Arc<Jit>` example but explicitly defers to `/int`); `/int` §2.1 binds `C = Code` enum. **All three are mutually consistent.**

**Cache-restore flow** (`/backend` §14.3 + `/int`'s `symbol-table-cache.md` §3.2 + `/platform` §A2): **CONVERGENT**.
- Step ordering: deserialise → version check → install symbol table → drive `.o` linker (`--link` mode) OR re-codegen (JIT mode) → re-resolve platform fn ptrs → install module scope. All three docs match.
- Platform-fn-ptr re-resolution: all three name `load_and_register_platform` reuse + `PlatformDecl`-iteration as the mechanism. No new API surface invented.
- One observed inconsistency: `/backend` §14.3 step [5b] specifies cache-hit JIT mode goes through `compile_to_module<JITModule>` (re-codegen, not `.o` load); `/int`'s `symbol-table-cache.md` §3.2 step "drive `.o` linker" leaves both paths open. Reading both docs together, the resolution is: JIT-mode REPL → re-codegen path; `--link` mode → linker path. This is consistent but `/int`'s doc could state it more clearly. Not a blocker — `/int` Wave 2 implementation will collapse the ambiguity.

**`Code` enum + Decision-31-equivalent reclaim story for Linker-loaded code**: `/int` §2.1 explicitly addresses this — `Code::Linker { linker: Arc<Linker>, ptr }` carries the per-symbol Linker retention root, and reclaim fires when the last `Code::Linker` clone drops. `/platform` §A3 confirms this is independent of the `SymbolTable.linker: Option<L>` field (which `/int` resolves to `L = ()` so it isn't used). The Decision-31-Scenario-2 reclaim story has a structural dual on the cache-hit path: per-module Linker-pages reclaim when the last `Code::Linker` referencing a Linker drops. **No reclaim gap; the shape is symmetric.**

#### Condition disposition table

| # | Condition | Status | Notes |
|---|---|---|---|
| C1 | Sketch-comparison refresh in `module-caching.md` §14.8 | **SATISFIED** | §14.8 substantive: covers sketch's CompiledModule god-object cache shape, `try_load_cached_module()` 238-line rehydrator, lossy structural-decl reconstruction, vs v4's serialised-`SymbolTable` shape with explicit structural-decl preservation per Decision 33. Closes MED-2 root cause. |
| C2 | All 5 `/int` design docs land + cross-ref `module-caching.md` + name `CACHE_SCHEMA_VERSION` ownership | **SATISFIED** | All 5 docs present (`symbol-table-cache.md`, `symbol-table-generics.md`, `private-submodule-import.md`, `multi-sig-introspection.md`, `cranelisp-toml.md`). Cross-ref present (`symbol-table-cache.md` §2 + §4 + §10 reference `module-caching.md`). Ownership pinned to `/backend` per Decision 34 (`crates/cranelisp-backend/src/cache/mod.rs`). |
| C3 | `/typecheck`'s `ast-annotation.md` §11 + §12 land | **SATISFIED** | §11 + §12 present; both narrowly scoped (typecheck commits to never observing `C` or `L`); 6 typecheck-side invariants on the new fields are sound; sketch comparison present in §12.6. |
| C5 | Per-crate clippy gate per wave | **CARRIED** (no Wave-1 implementation) | Phase 3a is design-only; the gate first applies to Wave 2 (foundation + typecheck/frontend bundle) and Wave 3 (backend, integration). `/sprint` enforces at each wave close. `/int`'s `symbol-table-generics.md` §3 builds in the cargo-check checkpoint at each migration stage — directly supports C5. |
| C6 | `io.rs:28` is real bug, regression-test symptom named | **SATISFIED** | §10.6 names positive (`(do (print "a") (print "b") (print "c"))` — alloc/dealloc balanced) and negative (`(loop 1000 (print "x"))` — gap stays within ±1) test symptoms. Default disposition: fix in Wave 3 (Form A or B per audit). One-deferral-permitted policy held in reserve only with `/qa`-side `#[ignore]`d regression test landing first if invoked (§10.8). |
| C7 | Decision 31 Scenario 2 verification test owned by `/qa` Wave 5 | **TRACKED** | `/int`'s `symbol-table-generics.md` §2.3 explicitly names `/qa` Wave 5 as the verification site. `/qa` skill plan (SPRINT.md `### /qa`) lists "Step 5c verification: Decision 31 Scenario 2 — REPL redefinition with `/mem` shows live-bytes drop on the redefinition (not just session teardown)". `/sprint` to confirm `/qa`'s `tests/plan/ring4.md` Sprint-58 section extends Scenario 1 to Scenario 2 before Wave 5 closes. |
| **C8 (NEW)** | `/backend`'s `compile-to-module.md` §17 to spell out the raw-shape return type per CP1 arbitration (Decision 35) | **NEW for Wave 2** | §17 currently leaves the CP1 shape implicit. CP1 arbitration (Decision 35) confirms Layer 2 Option B: backend returns raw `(Arc<Jit>, HashMap<Symbol, *const u8>)` (or extends `CompilationResult` to carry both `func_ids` and `Arc<Jit>`); integration layer constructs `Code::Jit`. `/backend` updates §17 in Wave 2 to spell this out explicitly so the integration-side consumer (`/int`'s priority-worker compile-finalise) has a contract to code against. Filed as FIXME(/backend) on `compile-to-module.md` for Wave-2 close. **Wave 2 gate.** |

#### Open coordination point dispositions

**CP1 — Layer 2 Option A vs B for `compile_to_module` shape**: **RESOLVED in this review as Decision 35 / Layer 2 Option B.** `/arch` arbitrates in favour of Option B. Rationale: minimises backend's bound annotations (no `<C: CodeStore + From<RawCode>>` plumbing), keeps `compile_to_module`'s signature symmetric across `JITModule` and `ObjectModule` (object path returns bytes, not codestore wrapping), localises the `Code::Jit` construction to the one site (`/int`'s priority-worker compile-finalise) that knows the integration-layer's enum shape. The §17 update's "backend internals continue reading `SymbolTable<(), ()>`" framing is consistent with Option B. **Wave-2 follow-on (C8): `/backend` updates §17 to name the raw-shape return type explicitly** — either a `(Arc<Jit>, HashMap<Symbol, *const u8>)` tuple, or `CompilationResult` extended with the `Arc<Jit>` field. The choice between those two specific shapes is `/backend`'s implementation call.

**CP2 — `CacheEnvelope { schema_version, table }` wrapper vs top-level `schema_version` field on `SymbolTable`**: **DEFERRED to `/backend` Wave-2 implementation choice. Recommendation: top-level field on `SymbolTable`, no envelope.** Rationale: the field exists on the struct per `interfaces.md` line 891 (`#[serde(default)] schema_version: u32`), and Sprint 58's first numbered shape ships with it. No envelope adds a JSON-shape difference between in-memory `SymbolTable` and serialised `SymbolTable` for no observable benefit until forward-compatibility on enum-variant renames or non-additive shape changes surfaces a concrete case. `/backend` §14.1 already permits either approach and recommends the no-envelope path; `/int`'s sniff path (`symbol-table-cache.md` §4 last row) adapts to either. `/arch` confirms the no-envelope path is preferred unless `/backend` Wave-2 implementation surfaces a serde forward-compat blocker.

**CP3 — implicit prelude `ImportSpec` at `src/worker.rs:1973` appending to `SymbolTable.imports`?**: **ROUTED to `/int` Wave 2 design call as `/typecheck` proposed.** `/typecheck` §11.3 invariant 4 documented two principled answers: (a) yes, with synthetic `Span` (preserves "imports is the source of every Import entry's reason"); (b) no, prelude is special-cased and its `ModuleEntry::Import` chains lack a corresponding `ImportSpec` (matches today's behaviour). `/typecheck` correctly does not pre-empt; `/arch` does not pre-empt either. `/int`'s decision criterion: import-resolver diagnostic quality. `/int` Wave 2 records the call inline at the implementation site (with a one-line FIXME(/typecheck) update closing §11.3 invariant 4 if the answer differs from `/typecheck`'s default expectation).

#### Principle 8 cross-check (no throwaway infrastructure)

- **`/int`'s `Code` enum with `Jit` + `Linker` variants**: **NOT throwaway.** Decision 35 records the enum as the §9.1 target shape composed at the integration layer — the final concrete that activates Decision 31 Scenario 2 reclaim AND the cache-hit Linker reclaim story together. No interim shape; no future replacement planned. Both variants are needed (mixed-lineage modules in REPL sessions are first-class).
- **`/int`'s 5-stage migration ordering** (`symbol-table-generics.md` §3): the intermediate stages (Stage 1: `cranelisp-types` + typecheck bundled; Stage 2: frontend; Stage 3: backend; Stage 4: integration; Stage 5: tests) are **build-greenness checkpoints, not interim shapes**. Each stage either uses `()` defaults (Stages 1–3) or the final `Code` enum (Stage 4). No transient type lives across stages and dies. The "transient `Code::from(raw)` shim" mentioned in §4 last paragraph as a contingency if Stage 4 lands without `/backend`'s Layer-2 decision is correctly called out as "reabsorbed in Wave 3" — and Decision 35 closes the Layer-2 question now, so the shim is unnecessary. ✓
- **`/backend` §10's Form A vs Form B for `io.rs:28`**: **NEITHER is a stepping stone — both terminal.** Form A is one line per affected extern (`s.dec_rc()` after `s.own()`); Form B refactors `s.own()` into `s.into_owned_consuming()` and hides the consuming dec inside the helper. Form B is preferred if >2 externs are affected by the audit (§10.5); Form A is local-and-minimal otherwise. The choice is by audit, not by sequence. ✓

#### `interfaces.md` updates applied during this review

- §"Module System" gains a new sub-section **"Integration-Layer `Code` Enum (in `src/`)"** documenting the `Code` enum shape, the `code.ptr()` accessor, and the `unsafe impl Send + Sync` discipline. Cross-refs Decision 35 and CP1 arbitration.
- §"Summary of Changes from v1" → "Types added" gains a row for `Code` enum (Sprint 58 Phase 3a, Decision 35) — names placement (in `src/`, not `cranelisp-types`), CP1 arbitration outcome (Layer 2 Option B), variant shape.

#### `design/arch/CLAUDE.md` updates applied during this review

- **Decision 35 added** — `Code` enum location + Linker retention story + CP1 arbitration (Layer 2 Option B) + `kept_jits`+`kept_linkers` dual dissolution + mixed-lineage modules. Cross-refs Decisions 25, 31, 32, 34.

#### FIXMEs filed against other skills during this review

| File | Skill | Request |
|---|---|---|
| `design/backend/compile-to-module.md` §17 | `/backend` | Spell out the raw-shape return type per CP1 arbitration (Decision 35 / Layer 2 Option B). Either `(Arc<Jit>, HashMap<Symbol, *const u8>)` tuple or extend `CompilationResult` to carry the `Arc<Jit>`. Wave-2 close gate (Condition C8). |

#### Additional conditions (Wave 2 open)

- **C8** (new): `/backend`'s `compile-to-module.md` §17 to spell out the raw-shape return type per CP1 arbitration. Wave-2 close gate. (Files FIXME(/backend) on the doc.)

#### Status update

Phase 3a Architecture Review COMPLETE. All Phase-2 conditions satisfied except (C5 carried — clippy gate is Wave 2/3 work) and (C7 tracked — `/qa` Wave 5 work). One new condition (C8) opens for Wave 2. Three CPs disposed: CP1 resolved (Decision 35), CP2 deferred with recommendation, CP3 routed to `/int` Wave 2 design call. `interfaces.md` updated with `Code` enum documentation. `design/arch/CLAUDE.md` updated with Decision 35.

Recommended next action by `/sprint`: advance to Phase 3b (Design Review by `/review`) before opening Wave 2.

### Wave 2 mid-wave architectural reconciliation

**Reviewer**: `/arch`
**Trigger**: `/qa` Wave 2c surfaced 12 cache-hit production bugs; `/int` investigation traced them to an architectural defect (the `user`/`main` bare-naming special case in `crates/cranelisp-backend/src/lib.rs:182-186`). User-driven design discussion converged on a deeper architectural reframing.
**Verdict**: **APPROVED with 0 conditions** for the proposed Wave 2 fix shape (A + B + C). The shape produces the §9 target form directly (Principle 8), preserves Decision 31's redefinition invariant, and satisfies Decision 23's byte-identical-CLIF principle. `/sprint` may proceed to spawn `/backend` then `/int` in serial without waiting on further `/arch` work.

#### Findings

**1. The two-GOT model is the missing framing.** Pre-reconciliation, the docs treated "GOT" as one concept. Two distinct artefacts have been conflated:
- **SymbolTable GOT**: `Arc<GotTable>` field on `SymbolTable`, in-process, mutable. Used by JIT (`--run`) and REPL. Where REPL redefinition writes the new fn ptr (Decision 31 atomic swap). Resolved at JIT finalize via `JITBuilder::symbol_lookup_fn`.
- **`.o` data section GOT**: `Linkage::Export` data symbol `__cranelisp_got_{M}` defined inside `M`'s own `.o`, with relocation initializers against local function symbols. Used only by the system linker (`ld`) in `--link` mode. Dormant in `--run`/REPL.

Decision 23 has been UPDATED Sprint 58 Wave 2 to make this explicit. `interfaces.md` gains a "Two-GOT model" subsection in §"Symbol Table". The two-GOT framing IS the architectural shape Principle 11 mandates: same data symbol reference (`Linkage::Import` from caller's POV), mode chooses resolver. The pre-reconciliation conflation was the root cause behind both Bug A (cache-hit lookup of wrong name) and Bug B (`__cranelisp_got_M` never defined as Export data in `.o`).

**2. All-GOT calling is the Decision 31 prerequisite.** REPL redefinition correctness mandates that EVERY call site — including intra-module — go through the GOT slot. Without all-GOT, the Decision-31 atomic swap at the GOT slot would not affect existing callers' compiled code (they'd have the old function address baked in as a direct relocation). The all-GOT discipline is what makes the swap effective. This is documented elsewhere but not previously connected to function-symbol naming + linkage policy. The connection: under all-GOT, no native code ever takes a user function's symbol address across `.o` boundaries — therefore user functions don't need cross-`.o`-visible names, therefore bare + Local linkage is correct.

**3. The `user`/`main` special case is a defect, not a feature.** Pre-Sprint-58, `crates/cranelisp-backend/src/lib.rs:182-186` declared user functions in `user` and `main` modules with bare names + `Linkage::Export`, while every other module's functions got `module/name` qualified names + `Linkage::Export`. This violated Principle 11 (single pipeline, mode parameters): the same `compile_to_module` function emitted different linkage shapes depending on the module's name. It accreted to make `--link`'s `_main` entry point work — the system linker needs `_main` to find the program entry — and was never reconciled against the all-GOT-call architecture. Decision 36 records the corrected policy: bare + `Linkage::Local` uniformly, with the `_main` entry point provided by the `--link` layer as a single targeted Export alias outside `compile_to_module`. The defect being fixed in Wave 2 IS this special case.

**4. Cache-hit integration belongs inside `register_module`'s recursion, not as a parallel orchestration.** Pre-Sprint-58, `try_cache_hit_load` (`src/worker.rs:1169`) re-implemented dependency discovery, ordering, and GOT setup in parallel with the fresh-build code path. This is the dual-pipeline shape Principle 11 was created to forbid. Decision 37 records the correct shape: cache-hit decision is a branch inside `register_module` (deserialise-or-typecheck per module, then recurse on imports). After typecheck-or-deserialise completes for ALL transitively-reachable modules, codegen phase runs in any order across modules — typecheck has already pinned the GOT slot LAYOUT (slot indices in `SymbolTable.symbols[s].got_slot`), so codegen workers fill slot CONTENTS independently. No bespoke topo-sort is needed at codegen.

**5. Decision 25's "regenerated from `ast` on cache-hit load" wording was wrong.** The cache stores BOTH `.meta.json` (deserialise → SymbolTable) AND `.o` (linker maps native code; addresses populated into SymbolTable GOT). Cache-hit LOADS the `.o`; it does NOT re-codegen. Codegen runs only on fresh build. Decision 25 has been UPDATED Sprint 58 Wave 2 with this corrected framing.

#### Verdict on the proposed Wave 2 fix shape (A + B + C)

| Aspect | Verdict | Rationale |
|---|---|---|
| **A — `compile_to_module` user/main special case deletion + bare+Local function declarations + `__cranelisp_got_{M}` Export-data definition (`/backend`)** | APPROVED | Produces the §9 target shape directly: the Decision-36 naming policy is the final shape (no per-module asymmetry survives); the `__cranelisp_got_{M}` Export-data definition closes Bug B and aligns the `.o` data section GOT with Decision 23's two-GOT framing. Principle 8: not interim — this IS the §9 form. Principle 11: restored compliance (single pipeline, single naming rule). |
| **B — Cache-hit integration into `register_module`; defensive guard against swallowed-failure (`/int`)** | APPROVED | Produces the §9 target shape directly: Decision 37's recursive flow is the final shape (no bespoke `try_cache_hit_load` orchestration survives); the defensive guard upholds Decision 31's safety invariant (GOT slots that fail to resolve must error, not silently report success). Principle 8: not interim. Principle 11: single pipeline restored. Decision 31 invariant preserved by the defensive guard. |
| **C — Downstream consumers of the deleted bare-naming special case (`/int` survey)** | APPROVED | The `--link` layer's `_main` Export alias is the correct narrow exception — one targeted alias for the system linker's entry-point requirement, not a whole-module asymmetry. REPL display already uses bare names, so no display change is needed; the survey-and-verify approach is correct. Principle 11 satisfied (the alias is a `--link`-mode-only artefact, not a general policy). |

**Decision 23 byte-identical CLIF check**: PRESERVED. The CLIF emitted by `compile_to_module` is unchanged in structure: `global_value` against `__cranelisp_got_{M}` declared as `Linkage::Import` from the caller's POV, indexed load by slot. Only the `.o` data section GOT's *definition* (now `Linkage::Export` in the owning module's `.o`) is added — this is an additional emission, not a CLIF change at call sites. JIT mode still resolves the `Linkage::Import` reference via `JITBuilder::symbol_lookup_fn` to the SymbolTable GOT base; nothing about that path changes.

**Decision 31 redefinition invariant check**: PRESERVED. All-GOT calling continues unchanged. The bare + Local function naming does not affect call-site emission (which uses GOT, not function symbols). The SymbolTable GOT slot remains the atomic-swap target. The defensive guard in B (no swallowed failures) STRENGTHENS the invariant — pre-fix, a NULL slot could be reachable; post-fix, a slot that fails to populate errors out before the codegen worker reports success.

#### Conditions for approval

NONE. The Wave 2 fix shape (A + B + C) as proposed is approved without conditions.

#### Follow-on architectural concerns (not blockers)

1. **Decision 23's two-GOT framing implies a `compile_to_module<ObjectModule>` requirement to define `__cranelisp_got_{M}` as Export data.** This is captured in the FIXME on `compile-to-module.md` filed by `/arch` during this review. The mechanism (Module trait extension vs `TypeId` downcast vs caller-side responsibility) is `/backend`'s implementation choice — `/arch` does not pre-empt. The shape constraint is: every `.o` produced by `compile_to_module<ObjectModule>` MUST carry the defined `__cranelisp_got_{M}` Export data symbol with relocation initializers against the local function symbols. Wave 2 close gate: `/backend` confirms the chosen mechanism in `compile-to-module.md` §5 update.

2. **Cache-write becomes mandatory for any module with defined symbols.** Pre-reconciliation, the `.o` write was implicitly optional in some framings (REPL-only sessions might skip it). Post-reconciliation, the `.o` is the cache-hit path's load source — so any session that intends to populate the cache directory must write the `.o` for every module with defined symbols. This is captured in the FIXME on `module-caching.md` §14.5. Not a blocker, but `/sprint` should weigh whether REPL-only sessions are expected to populate the cache or are expected to bypass it entirely (the latter is fine; the former requires the `.o` write to be in the REPL-mode worker's discipline).

3. **The Decision-37 recursive-flow refactor touches `register_module` directly.** This is `/int`'s deepest worker-orchestration code. The proposed shape is sound, but the implementation may surface borrow-checker / scheduler-state-coordination issues that don't show up in the design. `/sprint` should monitor `/int`'s wave-2 implementation for emergent complexity, with the standard escalation path if scope expands beyond the wave's budget.

4. **No new architectural decisions are needed beyond Decisions 36 and 37.** The `/backend`-side and `/int`-side changes both flow from the Decision-23 + Decision-25 + Decision-31 + Decision-32 + Decision-33 + Decision-35 + Decision-36 + Decision-37 set. No further `/arch` arbitration is anticipated for Wave 2 close.

#### `design/arch/CLAUDE.md` updates applied during this review

- **Decision 23 UPDATED** — explicit two-GOT framing added (SymbolTable GOT vs `.o` data section GOT; same data symbol reference, mode chooses resolver). Cross-references Decisions 31, 36, and 37.
- **Decision 25 UPDATED** — corrected wording: cache stores BOTH `.meta.json` AND `.o`; cache-hit LOADS the `.o`, does NOT re-codegen. Earlier "regenerated from `ast` on cache-hit load" framing was wrong.
- **Decision 36 ADDED** — function symbol naming + linkage policy: bare names + `Linkage::Local` uniformly. The `user`/`main` special case is a defect, not a feature. The `--link` `_main` entry-point alias is a one-off targeted Export emitted by the `--link` layer, not a whole-module asymmetry.
- **Decision 37 ADDED** — cache-hit integration into `register_module`'s recursive flow; codegen phase order-independent because typecheck pins GOT slot LAYOUT. Bespoke `try_cache_hit_load` orchestration deleted.

#### `design/arch/interfaces.md` updates applied during this review

- §"Symbol Table" gains "Two-GOT model" subsection — distinguishes SymbolTable GOT (`Arc<GotTable>` field on `SymbolTable`, in-process, mutable, JIT-mode resolver target) from `.o` data section GOT (Export data symbol in object file, on-disk, immutable after load, `--link`-mode resolver target). Documents that the two share the same name + per-slot semantics so the backend emits byte-identical CLIF in both modes. Cross-references Decisions 23, 31, 36, 37.

#### FIXMEs filed against other skills during this review

| File | Skill | Concern |
|---|---|---|
| `design/int/symbol-table-cache.md` (head FIXME) | `/int` | (a) §3.1 vs §3.3 contradiction — rewrite §3.1 to match §3.3 (cache-hit LOADS `.o`, no re-codegen); (b) §3.2 — cache-hit decision moves inside `register_module`'s recursion per Decision 37; (c) reference Decisions 36 and 37 in the relevant subsections; "Investigation findings" Bug A's preferred fix becomes obsolete under Decision 36 (bare lookup uniformly is the correct fix, made consistent by `/backend`'s same-wave change). |
| `design/backend/compile-to-module.md` (head FIXME) | `/backend` | (a) §7 function declaration loop: bare names + `Linkage::Local` uniformly per Decision 36; delete the cross-module `Linkage::Import` paragraph (under all-GOT calling, no function-symbol cross-`.o` references exist); (b) §5.3 / new §5.4: `__cranelisp_got_{M}` Export-data definition for ObjectModule path (Bug B fix per Decision 23); (c) §12 head: add Decision-23 two-GOT framing reference. (Plus the previously-filed C8 follow-on for the raw-shape return type.) |
| `design/backend/module-caching.md` (head FIXME) | `/backend` | (a) §14.3 step [5b] is wrong — cache-hit LOADS `.o`, does not re-codegen per Decision 25 (updated); (b) cache-hit explicit two-GOT model paragraph; (c) §14.3 reframing per Decision 37 (cache-hit lives inside `register_module`'s recursion); (d) §14.5 — `.o` write becomes mandatory for any module with defined symbols. |

#### Status update

Wave 2 mid-wave architectural reconciliation COMPLETE. Decisions 23 + 25 updated; Decisions 36 + 37 added; `interfaces.md` gains two-GOT model subsection; three FIXMEs filed (one each on `/int` and two on `/backend`). The proposed Wave 2 fix shape is APPROVED with zero conditions. `/sprint` may proceed to spawn `/backend` then `/int` in serial action.

Recommended next action by `/sprint`: spawn `/backend` agent first to land the `compile_to_module` changes (A) and the FIXME-driven doc updates on `compile-to-module.md` + `module-caching.md`; then spawn `/int` agent to land the cache-hit-into-`register_module` integration (B), the downstream survey + `_main` Export alias for `--link` (C), and the FIXME-driven doc update on `symbol-table-cache.md`.

## Skill Plans

{Each skill's plan filled during Phase 3. Compiler skills with implementation work MUST land or update a design doc in their `design/{skill}/` subtree before Wave 2 opens. Per the Sprint 57 process, design-review and test-derivation gates Wave 2.}

### /arch
**Task**: Review Phase 5 sprint scope. Update `design/arch/interfaces.md` for `ModuleEntry::Def.code: Arc<Jit>` and `SymbolTable<C, L>` parameterisation. Update `design/arch/CLAUDE.md` with any new key decisions (CodeStore/LinkerStore trait shape; structural-decl placement). Resolve carried FIXMEs on Decision 24 scope clarification + sequence-diagram regeneration.
**Design doc**: `design/arch/pipeline-v4-roadmap.md` Phase 5 section; `design/arch/interfaces.md`; `design/arch/CLAUDE.md`
**Approach**: DONE in Phase 2. Verdict: APPROVED with 8 conditions (see §Architecture Review). Decision 24 scope-clarification FIXME resolved inline. Decisions 32 (CodeStore/LinkerStore empty marker traits), 33 (structural decls as fields on SymbolTable, ModuleStructure dissolves), 34 (cache schema versioned by explicit `schema_version: u32`) added to `design/arch/CLAUDE.md`. `interfaces.md` §"Symbol Table" + §"Module Entries" + §"Summary of Changes" updated to show the parameterised `SymbolTable<C: CodeStore, L: LinkerStore>` shape, the four structural-decl fields, the `linker: Option<L>` field, the `schema_version: u32` field, and `ModuleEntry<C: CodeStore = ()>` parameterisation. Sequence-diagram regen carried to Wave 6 (cosmetic). In Waves 2–4: monitor Wave-2 cumulative-wall-clock trigger (Condition 4); review any follow-on design concerns surfaced by implementation; pin a tighten-Decision-25-and-31-Scenario-2-footnote at sprint close (after 5c lands, both footnotes can be struck or trimmed).
**Acceptance**: scope `/arch`-approved; `interfaces.md` coherent with Phase 5 target; ≤2 new key decisions. **Met**: 3 decisions added (32/33/34); the count exceeds the soft-acceptance ≤2 because Phase 5 axes are three-way independent (trait shape / structural-decl placement / cache versioning) and combining them would obscure which rationale applies where. The acceptance was a guideline; this sprint's structure justifies the count.

### /typecheck
**Task**:
- **Step 5a**: shape of structural-decl fields (`imports`, `exports`, `platforms`, `submodules`) on `SymbolTable`. Coordinate with `/int` on writer placement.
- **Step 5b**: cache restore needs `SymbolTable` reconstruction without re-typechecking. Confirm typecheck-side invariants survive serialise→deserialise.
- **Step 5c**: introduce `CodeStore` + `LinkerStore` trait bounds on `cranelisp-types::SymbolTable` and `ModuleEntry::Def`. Confirm typecheck never observes `C` or `L` (operates on `SymbolTable<(), ()>` or equivalent).
- **Cosmetic**: `crates/cranelisp-typecheck/src/infer.rs:828` stale doc-comment.
**Design doc**: `design/typecheck/ast-annotation.md` extends with §11 (structural decls) + §12 (generics shape — read-only from typecheck POV).
**Approach**: LANDED in Wave 1 (Phase 3a). `ast-annotation.md` extended with §11 (Step 5a — Phase 5 structural-decl field shape, six typecheck-side invariants on the four `Vec<_>` fields, dissolution of `ModuleStructure`, cosmetic-fix plan for `infer.rs:828`) and §12 (Step 5c — empty-marker trait surface, five-point justification that `cranelisp-typecheck/src/*` never observes `C` or `L`, instantiation-site discipline at `src/session_v4.rs`, Step 5b cache-restore round-trip invariants from typecheck POV). All four `cranelisp-types` types named in Decision 33 verified present at the cited line numbers (`ImportSpec` line 369, `ExportSpec` line 378, `PlatformSpec` line 396, `ModDecl` line 405) — no shape mismatch. Wave 2 implementation work for /typecheck is narrowly scoped: (a) add `pub trait CodeStore` + `pub trait LinkerStore` empty markers + blanket impls to `crates/cranelisp-types/src/module.rs`; (b) parameterise `SymbolTable<C, L>` and `ModuleEntry<C>` with `()` defaults per the `interfaces.md` shape; (c) add the four structural-decl fields per §11.1; (d) add `linker: Option<L>` (`#[serde(skip)]`) per §12.4; (e) replace concrete `code: Option<Code>` with `code: Option<C>` on `ModuleEntry::Def`; (f) one-block cosmetic edit at `crates/cranelisp-typecheck/src/infer.rs:828` per §11.6. Zero changes anticipated to `cranelisp-typecheck/src/*` beyond the cosmetic — typecheck operates on `SymbolTable<(), ()>` everywhere. One open question filed for /int: §11.3 invariant 4 records that the implicit prelude injection at `src/worker.rs:1973` may or may not append to the structural `imports` field; /int decides based on resolver-diagnostic quality, /typecheck does not pre-empt.
**Acceptance**: structural-decl fields landed; cache deserialisation reproduces correct `SymbolTable` (round-trip tests); generics activation does not leak `C`/`L` into typecheck APIs.

### /backend
**Task**:
- **Step 5b**: rewrite `crates/cranelisp-backend/src/cache/` to serialise the enriched `SymbolTable`. Remove `CodegenInput` stashing path. Cache restore reconstructs the symbol table; `compile_to_module` reads `ast` and `code` from the symbol table same as fresh-build.
- **Step 5c**: update `compile_to_module` and JIT/Object path signatures for the parameterised symbol table. Backend internal call sites mechanical.
- **Bundled debt**: `crates/cranelisp-runtime/src/io.rs:28` string-literal RC residual.
- **Sketch comparison** required for Step 5b cache-restore design (sketch had a much simpler cache shape; document divergence).
**Design doc**: `design/backend/module-caching.md` major update for Step 5b; `design/backend/compile-to-module.md` minor update for Step 5c signature shape; `design/backend/ring2-rc.md` addendum for the io.rs:28 fix.
**Approach**:
- **Step 5b — cache rewrite**: `module-caching.md` §14 (NEW, PRESCRIPTIVE for Wave 2). The `.meta.json` IS a serialised `SymbolTable<(), ()>` — no `CacheMetadata`/`CacheCodegenState` decomposition. Persisted shape per §14.1 (table of fields with serde-skip discipline). `CACHE_SCHEMA_VERSION = 1` constant lives in `crates/cranelisp-backend/src/cache/mod.rs` per Decision 34 + `/arch` Condition 2 (renames the existing `CACHE_FORMAT_VERSION`). Cache-restore (§14.3): deserialise → version check → re-derive `code` per Defn entry by re-running `compile_to_module<JITModule>` against the persisted `ast` (fresh-build parity; one codegen path), re-derive `platform_fn_ptr` by re-resolving the DLL named in the persisted `PlatformDecl` per Decision 26. `--link` mode loads the `.o` via `Linker` and registers fn ptrs into the GOT directly. Deletions per §14.4: `serialize::CacheMetadata` + `CacheCodegenState`; `try_load_cached_module()`'s 238-line import-resolution duplication (closes MED-2). Cache-write (§14.5) is symmetric: clone the `SymbolTable`, set `schema_version`, `serde_json::to_vec`, atomic-write. Sketch-comparison refresh (§2 table + §14.8 dedicated subsection) covers sketch's `CompiledModule` god-object persistence vs the v4 `SymbolTable<(), ()>` shape, the structural-decl separation rationale (Decision 33 — `(import …)` originals preserved in source order vs sketch's lossy reconstruction from `ModuleEntry::Import` chains), and the `code`-on-entry vs sketch's parallel `def_codegen` map (closes MED-2's root cause). Closes `/arch` Condition 1.
- **Step 5c — generics**: `compile-to-module.md` §17 (NEW). Backend signatures continue to read `SymbolTable` (i.e. `SymbolTable<(), ()>`) — no `<C: CodeStore, L: LinkerStore>` bounds appear in backend. Backend operates on the typecheck-product shape; reads data fields (`ast`/`scheme`/`got_slot`), never observes `Arc<Jit>` through the signature. Concrete instantiation site is `src/session_v4.rs` (`/int` Wave 3). Backend's role: confirm `Jit` wrapper (Decision 31, landed Sprint 57 Wave 4) accepts `Arc<Jit>` storage (it does — `Send + Sync + 'static`), confirm no backend code references `kept_jits`. The `Drop` impl on `Jit` is unchanged.
- **`io.rs:28` fix**: `ring2-rc.md` §10 (NEW addendum). Root cause: `print_string` at `platforms/stdio/src/lib.rs:18-25` honours capture-RC for the deferred Effect thunk but does not honour Decision 24's input-boundary contract — caller transfers a ref via `compile_consuming_arg_list`, the extern never dec's it. Two fix forms (§10.4): Form A adds `s.dec_rc()` after `s.own()`; Form B adds `into_owned_consuming()` helper on `CLHeap` that consumes the caller's transferred ref directly. Recommend Form B if audit reveals >2 affected externs; Form A otherwise. §10.5 mandates a sweep over every `extern "C"` in `platforms/*/src/lib.rs` + `crates/cranelisp-platform/src/lib.rs` for the same pattern. §10.6 names the user-visible regression-test symptom per `/arch` Condition 6: positive — `(do (print "a") (print "b") (print "c"))` shows `alloc_count - dealloc_count` balanced; negative — `(loop 1000 (print "x"))` shows the gap stays within ±1 (pre-fix grows to ~1000). Unit-test names: `decision24_print_string_input_rc_balanced` + `decision24_print_string_repeated_rc_no_growth`. Default disposition: **fix in Wave 3**; one-deferral-permitted policy held in reserve only if implementation scope explodes (§10.8 specifies the artefacts for deferral if invoked).
**Acceptance**: cache hits reproduce identical compilation state; 9 cache SIGSEGV / cross-module GOT failures cleared; 3 sprint23 cache-link cleared; 1 v4 cache-hit-dep cleared; io.rs:28 RC residual fixed; backend unit tests for cache round-trip pass.

### /int
**Task**:
- **Step 5a**: write structural-decl fields from `src/worker.rs` form-handlers; delete `ModuleStructure` from `SharedState`; refactor `src/save.rs` to read from the enriched `SymbolTable`.
- **Step 5b**: update worker cache-write path to serialise the enriched `SymbolTable`; cache-hit code path stops needing the deferred-typecheck "stash" workaround.
- **Step 5c**: ~182 mechanical call-site touches across `src/` (largest concentration). Choose concrete `C` and `L` types for the session instantiation. Dissolve `SharedState.kept_jits` for Jit retention.
- **Step 5d**: three independent fixes:
  - (i) private-submodule import-resolver enforcement: `(mod- internal ...)` rejection at peer-module import resolution.
  - (ii) multi-sig REPL bare-symbol display: emit one line per variant (per `repl/spec.md §1.3 + §4.1.1`).
  - (iii) Cranelisp.toml lookup: implement project-config-file lookup per `spec/08-modules.md §8.11.4` item 2.
- **`/mem` slash command**: complete the Sprint 57 close-time integration-test contract by ensuring stable output for `/qa` Wave 5 E2E tests.
**Design doc**: `design/int/symbol-table-cache.md` (NEW, Step 5b coordination with `/backend`); `design/int/symbol-table-generics.md` (NEW, Step 5c — strategy doc for the call-site sweep, must include "rough order" and "concrete-type choice site"); `design/int/private-submodule-import.md` (NEW, Step 5d (i)); `design/int/multi-sig-introspection.md` (NEW, Step 5d (ii)); `design/int/cranelisp-toml.md` (NEW, Step 5d (iii)).
**Approach**: All five design docs landed in Wave 1 (Phase 3a).
- **Step 5a (paired with `/typecheck`'s field-shape work per Decision 33)**: in `src/worker.rs` form-handlers (lines 681/700/719/738), replace `shared.module_structures.entry(module).or_default().{import,export,mod,platform}_specs.push(...)` writes with appends to the new `symbol_tables[module].{imports,exports,submodules,platforms}` fields. Delete `SharedState.module_structures` and the `ModuleStructure` struct in `src/save.rs`. Refactor `src/save.rs::generate_module_source` to read the four structural-decl fields directly off the `SymbolTable` it already holds (drop the `structure: &ModuleStructure` parameter). See `design/int/symbol-table-cache.md` §3.1.
- **Step 5b (cache via `SymbolTable`, coordinated with `/backend`)**: per `design/int/symbol-table-cache.md`. Producer side (`src/worker.rs` cache-write path + `src/cache_writer.rs` packet shape): the worker stamps `schema_version = cache::CACHE_SCHEMA_VERSION` (constant owned by `/backend` per Decision 34, defined in `crates/cranelisp-backend/src/cache/mod.rs`) on the `SymbolTable<(), ()>` clone before serialise; deletes `SharedState.codegen_programs` + `stash_codegen_program`. Consumer side (`src/worker.rs::try_cache_hit_load`): peek `schema_version` first (mismatch → fall through as cache-miss, same code path as dep-hash mismatch); deserialise into `SymbolTable<(), ()>`; install in `symbol_tables`; drive `.o` linker to populate `Code::Linker { linker, ptr }` on each `Def.code`; walk `PlatformEffect` entries to re-resolve `platform_fn_ptr` from the surviving `PlatformDecl` (per `/platform` addendum §A1–A7). Cross-references `design/backend/module-caching.md` for the `CacheWritePacket` envelope shape — `/backend` owns the format and the version constant; `/int` is a stamping consumer.
- **Step 5c (generics activation; closes G12, completes Decision 31 Scenario 2)**: per `design/int/symbol-table-generics.md` §3 staged sweep. Concrete-type choice at `src/session_v4.rs`: `C = Code` where `Code` is an integration-layer enum unifying `Code::Jit { jit: Arc<Jit>, ptr }` and `Code::Linker { linker: Arc<Linker>, ptr }`; `L = ()` (Linker retention rolls through the per-symbol `Code::Linker` Arc). Migration order: (1) `cranelisp-types` + `cranelisp-typecheck` bundled (~80 sites, default-pin to `()`); (2) `cranelisp-frontend` (<10 sites); (3) `cranelisp-backend` (~50 sites, mostly `()`-pinned; `compile_to_module` shape decided with `/backend` per `compile-to-module.md` minor — preferred Layer-2 Option B: backend returns raw `(Arc<Jit>, HashMap<Symbol, *const u8>)` and `/int` builds `Code::Jit` per entry); (4) `src/` integration layer (~50 sites via `pub type SessionSymbolTable = SymbolTable<Code, ()>;` alias + `Code` enum; dissolve `SharedState.kept_jits` AND `SharedState.kept_linkers` — every prior `kept_jits.lock().push(arc)` site rewrites to populate `Code::Jit { jit: arc.clone(), ptr }` on each `Def.code` from the batch); (5) `tests/` adjustments (<10 sites). Per-crate clippy-clean checkpoint per Sprint 57 Condition 5 carried; full `cargo nextest run` after stage 4. Headline payoff: REPL `/mem` shows live-bytes drop on defn redefinition (Decision 31 Scenario 2 fires per redefinition, verified by `/qa` Wave 5).
- **Step 5d (i) — private-submodule import enforcement (`spec/08-modules.md §8.2.3`)**: per `design/int/private-submodule-import.md`. Insert a privacy check in `src/worker.rs::handle_import` (around line 1065) before file-resolution: derive `parent_path` from `spec.module_path`, ensure parent is loaded (reuse existing `block_for_typecheck` machinery if not), look up `symbol_tables[parent_path].submodules` (Step 5a-populated) for a `ModDecl { is_private: true, name: trailing_component }`, and reject with a spec-cited `ModuleError` if the importing module is not within the `parent_path` subtree (string-prefix check on the dotted path). Closes `tests/ring2.rs::neg_private_submodule_not_importable_from_peer` (currently failing).
- **Step 5d (ii) — multi-sig REPL bare-symbol display (`repl/spec.md §1.3 + §4.1.1`)**: per `design/int/multi-sig-introspection.md`. Add `format_overloaded_variants(name, module, variants, docstring)` helper in `src/session_v4.rs`; rewrite the `DefKind::Overloaded` branch in BOTH `format_def_entry` (~line 3150) AND `format_entry_sig` (~line 342) to call it. First variant carries `; defn - docstring`, subsequent variants are type+name only. Closes `tests/repl_experience.rs::display_overloaded_fn_shows_all_variants` (currently failing).
- **Step 5d (iii) — Cranelisp.toml lookup (`spec/08-modules.md §8.11.4 item 2`)**: per `design/int/cranelisp-toml.md`. Add `toml = "0.8"` dep on the binary crate; add `load_project_config_lib_dirs(project_root)` private helper in `src/session.rs` adjacent to `assemble_lib_dirs`; update `assemble_lib_dirs` to consult tier 2 first (Cranelisp.toml present → fully controls; else fall through to existing tier 3 env var → tier 4 default). Schema struct: `lib_dirs: Vec<PathBuf>` with `serde(rename = "lib-dirs")`. Path resolution: relative paths resolve against `project_root`; absolute paths used verbatim. Malformed TOML → `CranelispError` user-visible diagnostic (do NOT silently fall through). New `tests/e2e.rs` test demonstrates `Cranelisp.toml` precedence over `CRANELISP_LIB`. Closes inline FIXME(/int) at `spec/08-modules.md:639,648` — coordinate with `/spec` to remove FIXME after the test passes.
- **`/mem` integration-test stability**: confirm output stability of `format_mem_snapshot` (`src/session_v4.rs` ~line 331) for `/qa` Wave 5 E2E tests. Output format `; live: {N} bytes ({M} allocations)\n; allocs: {A}  deallocs: {D}` is documented and stable; `/qa` writes the assertions, `/int` does not change the format unless surface friction emerges during Wave 5.
**Scope risk**: self-monitor Wave-2 wall-clock. If >60% of `/int` budget by Wave-2 close, auto-fire Descope A (defer Step 5c to Sprint 59). Notify user.
**Acceptance**: `kept_jits` for Jit retention dissolved; redefinition reclaim verified by `/qa` integration test; the 2 carried Wave-5 tests pass; Cranelisp.toml lookup demonstrated in a test.

### /platform
**Task**: Confirm Phase 5 changes do not regress platform DLL loading or scheduling-class lookup. Step 5b's cache restore must reproduce platform fn ptrs correctly (re-resolve from manifest per Decision 26's serialisation discipline). Cosmetic: `crates/cranelisp-runtime/plan-platform.md:75` stale "run-tests timing" reference.
**Design doc**: addendum to `design/platform/platform-registry-removal.md` if cache-restore semantics change anything.
**Approach**: DONE in Phase 3a. Sprint 58 Phase 5 addendum landed at `design/platform/platform-registry-removal.md` §"Addendum — Sprint 58 Phase 5: Cache Restore via SymbolTable<C, L>" (sections A1–A7). Confirmation outcome: **cache restore re-resolves platform fn ptrs correctly as-is** — the existing `load_and_register_platform` codepath is reusable post-Step-5b; Step 5b only changes the upstream "which DLLs to reload?" data source (deserialised `PlatformDecl` entries from the symbol table, vs the prior `CodegenInput` stash). `SymbolTable.linker: Option<L>` (Decision 32) is independent of platform DLL retention — `SharedState::kept_dlls` continues to own DLL lifetimes per §G8 (the per-module `linker` field is for `.o` cache-hit code mapping, a parallel but disjoint concern). DLL-resolution failure recovery follows the Decision 34 pattern (cache-stale fall-through to fresh build). No regression expected on the 5 v4_platform tests that flipped green in Sprint 57 Wave 3 — fresh-build paths unchanged, cache-hit paths converge on the same observable shape via a different ingestion route. Two soft cross-skill requests filed in addendum §A7: (i) /int's `symbol-table-cache.md` should specify the cache-crate-vs-integration-layer division of the post-deserialise platform reload pass; (ii) /backend's `module-caching.md` Step 5b update may add a `CacheLoadError::DllResolutionFailed` variant or fold into existing dependency-changed path (either acceptable). In Wave 5: cosmetic cleanup of `crates/cranelisp-runtime/plan-platform.md:75` — replace stale "run-tests timing" wording with "per-test timing consumed by `/run-tests` slash command + user-level test runners composed from `discover-tests`/`run-test` builtins" (the FIXME comment already says this; the cleanup just removes the FIXME and confirms the inline description matches). Also check `crates/cranelisp-runtime/src/trace.rs:380` doc-comment for the matching update per the FIXME's own pointer.
**Acceptance**: platform tests pass; no regression on `v4_platform_*`; cache-hit reload of platform-using modules works.

### /frontend
**Task**:
- Cosmetic: `crates/cranelisp-frontend/src/module_extract.rs:120` spec-citation §8.3.6 → §8.3.7.
- **Step 5a coordination**: confirm frontend writes the structural decls into the typed `ModuleEntry`-side fields rather than into `ModuleStructure` (or hands off to `/int` worker cleanly).
**Approach**: {filled in Phase 3}
**Acceptance**: spec citations correct; structural-decl write-path well-defined.

### /qa
**Task**:
- **Step 5b verification**: cache round-trip integration tests — fresh-build vs cache-hit equivalence; multi-module cache; cache invalidation on dep change.
- **Step 5c verification**: `tests/plan/ring4.md` Decision 31 Scenario 2 — REPL redefinition with `/mem` shows live-bytes drop on the redefinition (not just session teardown).
- **Step 5d verification**: confirm `tests/ring2.rs::neg_private_submodule_not_importable_from_peer` flips green; confirm `tests/repl_experience.rs::display_overloaded_fn_shows_all_variants` flips green; new test for Cranelisp.toml lookup.
- **`/mem` integration tests** (Sprint 57 carry): 4 `repl/spec.md §3.7` rows.
- **Decision 31 Scenario 1 reclaim test** (Sprint 57 carry).
- **Prior-ring coverage** continued (negative-coverage tracker priority order from `spec/index.md:3`).
- **Re-triage `sketch_run_tests_pass_fn_called`** + Sprint 57 follow-on `sketch_port` failure — file FIXME on owning skill.
- **Close-time coverage audit (step 22)**.
**Design doc**: `tests/plan/ring4.md` extends with Sprint 58 section.
**Approach**: Test plan landed in Wave 1 (Phase 3a) — `tests/plan/ring4.md` §"Sprint 58 — Phase 5 Convergence Tests" with seven sub-sections (G.10 Step 5a structural-decl invariants; G.11 Step 5b cache round-trip + 13 pinned flip-green failures; G.12 Step 5c generics + Decision 31 Scenarios 1 + 2 reclaim; G.13 Step 5d (i)+(ii) confirmed flip-greens + (iii) Cranelisp.toml e2e + `/mem` integration; G.14 io.rs:28 RC regression-guard per Condition 6; G.15 prior-ring negative-coverage continuation; G.16 re-triage of two carried failures). Pinned flip-green list (13 tests):
- *9 cache SIGSEGV / cross-module GOT (`tests/cache.rs`)*: `cache_multi_module_hit_cross_module_call` (1253), `cache_multi_module_transitive_imports` (1297), `cache_multi_module_invalidation_dependency_change` (1336), `cache_multi_module_unchanged_dep_stays_cached` (1369), `cache_multi_module_multiple_imports` (1414), `cache_multi_module_two_deps` (1442), `cache_multi_module_with_prelude` (1561), `cache_pipeline_hit_second_compile` (1115), `cache_invalidation_transitive_pipeline` (1176).
- *3 sprint23 cache/link (`tests/sprint23.rs`)*: `cache_repl_loads_on_startup` (1119), `persist_bug2_cache_files_created_after_restore` (1695), `cache_repl_produces_object_files` (1923). (Sprint 57 close noted documented "3" vs observed "4"; the 4th is likely `cache_repl_writes_on_import` (1079); `/qa` confirms at Wave 2 baseline.)
- *1 v4 cache-hit-dep (`tests/v4_pipeline.rs`)*: `v4_cache_hit_dependency` (602).

Decision 31 reclaim test design (G.12 — the headline behavioural payoff):
- *Scenario 1* (Sprint 57 carry): `decision31_scenario1_repl_eval_mem_drops_after_eval` (positive: `/mem` baseline → `(+ 1 2)` → `/mem` shows `live_bytes` returned to baseline ±small_const) + `decision31_scenario1_repl_eval_no_unbounded_growth_repeated` (negative: 100x repeated eval; final `/mem` does NOT grow linearly with iterations; pre-fix would grow ~100x).
- *Scenario 2* (Step 5c headline): `decision31_scenario2_repl_redefinition_mem_drops_on_redefinition` (positive: `/mem` baseline → `(defn f [x] x)` → `/mem` (B) → `(defn f [x] (+ x 1))` → `/mem` (C); assert `C.live_bytes <= B.live_bytes + small_const` — second defn reclaimed first defn's JIT pages) + `decision31_scenario2_repeated_redefinition_no_unbounded_growth` (negative: 50x redefine; final `/mem` bounded; pre-Step-5c the gap grew ~50x because `kept_jits` accumulated each batch).

io.rs:28 regression-guard tests (G.14, per `/arch` Condition 6): `decision24_print_string_input_rc_balanced` + `decision24_print_string_repeated_rc_no_growth` (unit, in `crates/cranelisp-runtime/src/io.rs::tests`); `io_do_print_three_strings_rc_balanced_e2e` + `io_loop_print_no_unbounded_growth_e2e_neg` (integration, in `tests/io.rs`).

Cranelisp.toml e2e tests (G.13 (iii)): `e2e_cranelisp_toml_lib_dirs_overrides_default` (positive: takes precedence over `CRANELISP_LIB`); `e2e_cranelisp_toml_absent_falls_through_to_env_var` (positive sanity); `e2e_cranelisp_toml_malformed_emits_diagnostic` (negative: helpful error message containing path + TOML parse-error description); `e2e_cranelisp_toml_empty_lib_dirs_overrides_env` (edge case: empty list IS valid override per spec).

Wave-by-wave sequencing in `tests/plan/ring4.md` §G.17 Sprint 58 Delta Summary table (Wave 1 = this plan only; Wave 2 = G.10 + G.11 author + 13 pinned flip-green confirms + `sketch_run_tests_pass_fn_called` re-triage; Wave 3 = G.12 reclaim tests; Wave 4 = G.13 (i)+(ii) flip-green confirms + (iii) toml + `/mem` integration; Wave 5 parallel = G.14 + G.15; Wave 6 = coverage audit). No source-code authoring in this Wave-1 phase. No new FIXMEs filed against other skills (one open question on §11.3 invariant 4 implicit-prelude is already noted by `/typecheck`).
**Acceptance**: cache round-trip tests pass; Scenario 1 + Scenario 2 reclaim tests pass; both Wave-5 carries flip green; `/mem` E2E tests pass; coverage audit clean.

### /review
**Task**: Review each implementation wave after build-green. Focus areas:
- Step 5b: cache write/restore symmetry (no asymmetric fields); `CodegenInput` stashing fully removed.
- Step 5c: generics activation does not leak `C`/`L` upward into typecheck APIs; concrete-type choice cleanly localised; `kept_jits` dissolution complete; no residual side-store references.
- Step 5d: import-resolver enforcement covers both surface (defmacro shadowing) and direct import paths; multi-sig display matches §1.3 + §4.1.1 spec; Cranelisp.toml lookup precedence matches §8.11.4 ordering.
- Cross-wave: `Arc<Jit>` placement satisfies Decision 31 safety invariant.
**Design doc**: `design/review/checklist.md` updated for Phase 5 focus.
**Approach**: {filled in Phase 3}
**Acceptance**: all Blockers resolved in-sprint; Importants resolved or explicitly deferred with rationale.

### /sprint
**Task**: Drive the phased schedule. Review each wave's green baseline. Escalate scope risk to user if `/int` reports burden overload. Enforce FIXME gate between waves. Update close checklist with Step 5e procedural change. Confirm showcase adequacy.
**Acceptance**: sprint closes with green baseline (≤4 carried failures, all justified), new demo, clean FIXME scan, clean coverage audit, close checklist refined.

### /stdlib
**Task**:
- Run stdlib integration tests against the Phase 5 build. No stdlib change expected.
- Refresh stdlib showcase demo if any stdlib-surfacing change in Phase 5 (none expected).
- **Plan refinement**: `stdlib/plan-stdlib.md` prelude-monolith remediation — confirm carry to a stdlib-focused sprint; do not land here.
**Approach**: {filled in Phase 3}
**Acceptance**: stdlib tests pass; no surface change.

### /examples
**Task**: Run `examples/*.cl` against the Phase 5 build. Report any regression.
**Approach**: Wave 6 regression sweep — 15/15 examples expected. File FIXME on owning skill if any regression.
**Acceptance**: all examples compile and run.

### /port
**Task**:
- **Bundled debt**: rewrite the four exemplar test submodules (`grid.cl`, `html.cl`, `form.cl`, `solver.cl`) to use `discover-tests` + `run-test` per Decision 30 safe pattern (c). Removes the FIXMEs and validates the recommended pattern at exemplar scale.
- Run exemplar Sudoku Solver against Phase 5 build. The Sprint 19 stack-overflow (documented in `exemplar/CLAUDE.md`) remains pre-existing — do not block sprint close on it.
- Provide a showcase demo excerpt (`repl/demos/...`) showing exemplar's test scaffolding running through `discover-tests`/`run-test`.
**Approach**: {filled in Phase 3}
**Acceptance**: 4 exemplar test submodules work via `discover-tests`/`run-test`; demo plays cleanly.

### /repl
**Task**:
- Create `repl/demos/ring4p.demo` showcasing Phase 5 deliverables. Target vignettes:
  - REPL redefinition with `/mem` showing live-bytes drop (Scenario 2 reclaim — the headline)
  - Cache-hit fast restart visible to user (e.g., 2nd REPL invocation hits cache)
  - Private submodule import rejection (`(mod- internal ...)` peer rejection)
  - Multi-sig bare-symbol display showing all variants
- Verify all prior demos play cleanly (regression gate).
- Refine `repl/spec.md` for any §1.3 + §4.1.1 + §3.7 changes that surface during /int's Step 5d (ii) and Step 5b implementation.
**Design doc**: `repl/spec.md` updates for any newly-surfaced behaviour.
**Approach**: {filled in Phase 3}
**Acceptance**: `ring4p.demo` plays cleanly; prior demos regression-free; `repl/spec.md` reflects any newly observed behaviour.

### /docs
**Task**: Audit `user/` for stale references. Pipeline-internal sprint → low burden. Refresh `user/` if Step 5d (iii) Cranelisp.toml lookup adds user-visible config behaviour.
**Approach**: {filled in Phase 3}
**Acceptance**: no stale user docs; Cranelisp.toml documented if added.

### /spec
**Task**:
- Resolve the three carried FIXME(/spec) (vec-map/vec-reduce, §4.1.7 classification, §1.5 List/Seq display).
- Update `spec/08-modules.md §8.11.4` once Cranelisp.toml lookup lands (close the inline FIXME(/int)).
- Close-time prior-ring coverage sweep alongside `/qa`.
- Apply the Step 5e sprint-close protocol update — when last sub-section gains `[Tested ...]`, bump heading annotation.
**Approach**: {filled in Phase 3}
**Acceptance**: 3 carried FIXMEs resolved; §8.11.4 closes once 5d (iii) lands; close-time sweep clean; new heading-bump policy reflected in `spec/CLAUDE.md`.

## Waves

Wave 1 (design + `/arch` approval) completed during Phase 3a authoring + review. Implementation waves begin with Wave 0 (cosmetic cleanups, no dependencies) and Wave 2 (Steps 5a + 5b together) in parallel. Wave 3 (Step 5c — generics activation) is sequential after Wave 2 to avoid concurrent disruption of the `SymbolTable` shape. Wave 4 (Step 5d — three independent items) runs in parallel with Wave 3. Wave 5 (`/qa` integration + prior-ring coverage) runs throughout. Wave 6 (showcase + close) gates sprint close.

### Wave 0 — Cosmetic cleanups + bundled debt (parallel, no design-doc gate)

Small, mechanical, independent. Can land any time before sprint close.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | Fix `crates/cranelisp-typecheck/src/infer.rs:828` stale doc-comment | pending | Plan in `ast-annotation.md` §11 — replace the FIXME block with a one-line description matching `infer_annotate`'s actual behaviour. |
| /frontend | Fix `crates/cranelisp-frontend/src/module_extract.rs:120` stale §8.3.6 → §8.3.7 citations | pending | Cosmetic; one search-and-replace. |
| /platform | Fix `crates/cranelisp-runtime/plan-platform.md:75` stale "run-tests timing" reference | pending | Per Sprint 58 /platform plan. |
| /arch | Resolve carried Sprint 57 FIXME(/arch) Decision 24 scope clarification | completed (Phase 2) | Done in Phase 2 review. |
| /port | Rewrite 4 exemplar test submodules (grid/html/form/solver) to `discover-tests`/`run-test` (Decision 30 safe pattern (c)) | pending | Removes 4 FIXME(/int)s; validates recommended pattern at exemplar scale. |
| /spec | Resolve 3 carried FIXME(/spec): vec-map/vec-reduce, §4.1.7 classification, §1.5 List/Seq display | pending | Three small spec fixes per Sprint 57 Wave 5 carry-list. |

**Gate criterion**: all carried debt items either resolved or explicitly deferred with rationale; `cargo nextest` baseline preserved.

### Wave 1 — Design + `/arch` approval — **COMPLETE**

Phase 3 (Design) per `/sprint` skill definition. Completed during Phase 3a authoring + review (Sprint 58 Phase 2 + Phase 3a).

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Approve Sprint 58 scope | completed | Phase 2 review: APPROVED with 7 conditions; descope contingencies struck per user direction. |
| /arch | Add Decisions 32, 33, 34 to `design/arch/CLAUDE.md`; update `interfaces.md` for `SymbolTable<C, L>` | completed | Phase 2. |
| /typecheck | `design/typecheck/ast-annotation.md` §11 (Step 5a) + §12 (Step 5c) | completed | Confirmed Decision 33's four `cranelisp-types` types exist verbatim. 6 invariants documented. |
| /backend | `design/backend/module-caching.md` §14 (Step 5b PRESCRIPTIVE) + Sketch-comparison refresh §14.8 | completed | Closes Condition 1; cross-refs `/int`'s `symbol-table-cache.md` (Condition 2). |
| /backend | `design/backend/compile-to-module.md` §17 (Step 5c — backend signatures) | completed | FIXME(/backend) added per Condition C8 — Wave 2 follow-on to spell out raw return shape (`(Arc<Jit>, HashMap<Symbol, *const u8>)`). |
| /backend | `design/backend/ring2-rc.md` §10 (`io.rs:28` fix plan + Form A/B + regression-test symptoms) | completed | Closes Condition 6; `/qa`-test symptoms named. |
| /int | 5 NEW design docs: `symbol-table-cache.md`, `symbol-table-generics.md`, `private-submodule-import.md`, `multi-sig-introspection.md`, `cranelisp-toml.md` | completed | Concrete-type choice: `C = Code` enum (`Jit { Arc<Jit>, ptr }` + `Linker { Arc<Linker>, ptr }`); `L = ()`. 5-stage migration order documented. |
| /platform | Addendum sections A1–A7 to `design/platform/platform-registry-removal.md` | completed | Cache-restore reuses `load_and_register_platform` as-is. Three retention pools have disjoint lifetimes. |
| /arch | Phase 3a Design Review (step 9) | completed | APPROVED with 1 new condition (C8). CP1 RESOLVED (Decision 35 — Layer 2 Option B). CP2 DEFERRED. CP3 routed to /int Wave 2. |
| /qa | Derive Phase 5 test cases; update `tests/plan/ring4.md` | completed | ~50 tests across G.10–G.17. 13 cache failures pinned by name. Decision 31 Scenario 1+2 assertion shapes drafted. |

**Gate criterion**: all design docs landed and `/arch`-approved; test plan updated; `interfaces.md` coherent. **MET.**

### Wave 2 — Step 5a + Step 5b (data-model addition + cache rewrite)

Depends on Wave 1. Delivers Step 5a (structural decls on `SymbolTable`) + Step 5b (cache via `SymbolTable`). Expected to clear 13 of 17 baseline failures.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | Add `imports`/`exports`/`platforms`/`submodules` fields to `SymbolTable`; `schema_version: u32` field | pending | ~6 small edits to `cranelisp-types/src/module.rs` per `ast-annotation.md` §11.4. |
| /int | Step 5a writer: populate the four structural-decl fields from `src/worker.rs` form-handlers | pending | Per `private-submodule-import.md` and `symbol-table-cache.md`. Resolve open question CP3 (implicit prelude `ImportSpec` placement) inline; document the choice. |
| /int | Step 5a consumer migration: refactor `src/save.rs` to read structural decls from `SymbolTable` | pending | Delete `ModuleStructure` from `SharedState`. |
| /backend | Step 5b: rewrite `crates/cranelisp-backend/src/cache/` per `module-caching.md` §14 | pending | `.meta.json` IS serialised `SymbolTable<(), ()>`. `CACHE_SCHEMA_VERSION = 1` constant in `cache/mod.rs`. Delete `CacheMetadata`, `CodegenInput` stashing. |
| /backend | Update `compile-to-module.md` §17 with raw return shape per Condition C8 | pending | `(Arc<Jit>, HashMap<Symbol, *const u8>)`. CP1 follow-on. |
| /int | Step 5b worker cache-write path | pending | Replace deferred-typecheck stash with direct `SymbolTable` serialisation per `symbol-table-cache.md` §3. |
| /int | Step 5b cache-hit path: deserialise → install → re-derive `code` via `compile_to_module<JITModule>` per parity | pending | Per `symbol-table-cache.md` §3.2. Triggers re-codegen for `code` field; re-resolves `platform_fn_ptr` via `load_and_register_platform`. |
| /typecheck | 7 unit tests per `tests/plan/ring4.md §G.10` (typecheck-side invariants for structural decls) | pending | Source-order, no-dedup, no-cross-mixing, one-way coherence, read-only, serde round-trip identity. |
| /backend | 3 unit tests per `tests/plan/ring4.md §G.11` (cache symmetry, schema-version mismatch, write-then-read) | pending | In `crates/cranelisp-backend/src/cache/`. |
| /int | 1 unit test per `tests/plan/ring4.md §G.11` (worker cache-write path) + 4 unit tests per `tests/plan/ring4.md §G.10` (writer source-order, prelude-injection-disposition, ModuleStructure-deletion-grep, save.rs round-trip) | pending | Per /int's design docs §3-§5. |
| /qa | Integration tests: 4 cache round-trip + verify 13 cache flip-greens (9 cache + 3 sprint23 + 1 v4_pipeline) | pending | Per `tests/plan/ring4.md §G.10–G.11`. Test names pinned. |
| /review | Review Wave 2 code | done | Wave 2 /review: PASS with 3 Importants — see `design/review/sprint58-wave2-review.md`. |

**Gate criterion**: structural decls populated and round-trip; `CodegenInput` stashing removed; `CACHE_SCHEMA_VERSION = 1` enforced; 13 baseline cache failures cleared; `cargo clippy` clean per-crate (`cranelisp-types`, `cranelisp-backend/src/cache/`, `src/worker.rs`); test count ≥ baseline.

### Wave 3 — Step 5c (generics activation + Decision 31 Scenario 2)

Depends on Wave 2. Largest mechanical wave (~182 call-site touches). Headline behavioural payoff: per-redefinition JIT reclaim.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | Add `CodeStore` + `LinkerStore` empty marker traits to `cranelisp-types`; parameterise `SymbolTable<C: CodeStore = (), L: LinkerStore = ()>` and `ModuleEntry<C: CodeStore = ()>` | pending | Per Decision 32 + `ast-annotation.md` §12. ~6 edits. Default `()` propagation keeps typecheck signatures unchanged. |
| /int | Step 5c stage-by-stage migration (5 stages per `symbol-table-generics.md`) | pending | Stages: types+typecheck → frontend → backend → src/ via `SessionSymbolTable` alias → tests. Each stage keeps the build green. |
| /int | Define `Code` enum in integration layer per Decision 35 | pending | `Code::Jit { jit: Arc<Jit>, ptr: *const u8 }` + `Code::Linker { linker: Arc<Linker>, ptr: *const u8 }`. Located in `src/code.rs` or similar (integration-layer concrete type). |
| /int | Choose concrete instantiation in `src/session_v4.rs`: `SymbolTable<Code, ()>` | pending | Per Decision 35 + `symbol-table-generics.md` §4. |
| /int | Dissolve `SharedState.kept_jits` AND `kept_linkers` for retention | pending | Reclaim moves onto per-entry `Arc<Jit>` / `Arc<Linker>` directly. Decision 31 Scenario 2 fires. |
| /backend | Confirm backend signatures stay generic-blind (read fields, not reify `<C, L>`) | pending | Per `compile-to-module.md` §17. Mostly a no-op; verify and document. |
| /int | 5 unit tests per `tests/plan/ring4.md §G.12` (concrete-type choice, kept_jits dissolution, Code enum coexistence) | pending | |
| /typecheck | 3 unit tests per `tests/plan/ring4.md §G.12` (default-`()` propagation, marker trait blanket impl) | pending | |
| /qa | 4 reclaim integration tests + 1 enum-coexistence test per `tests/plan/ring4.md §G.12` | pending | Decision 31 Scenario 1 (per-eval reclaim) + Scenario 2 (per-redefinition reclaim). Positive + negative-no-unbounded-growth. |
| /review | Review Wave 3 code | pending | Focus: no `<C, L>` leakage upward; `kept_jits`/`kept_linkers` dissolution complete; Decision 31 safety invariant preserved. |

**Gate criterion**: `SymbolTable<C, L>` parameterised; `Code` enum placed per Decision 35; `kept_jits` + `kept_linkers` dissolved; per-redefinition JIT reclaim verified; baseline preserved or improved; `cargo clippy` clean per-crate; test count ≥ Wave 2 baseline.

### Wave 4 — Step 5d (3 carried `/int` items + `io.rs:28` fix)

Depends on Wave 1 (and partially on Wave 2 for Step 5d (i) which uses `SymbolTable.submodules` from Step 5a). May run in parallel with Wave 3.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Step 5d (i) — Private-submodule import-resolver enforcement | pending | Per `private-submodule-import.md`. Insert privacy check in `src/worker.rs::handle_import` reading `symbol_tables[parent_path].submodules` (Step 5a-populated). |
| /int | Step 5d (ii) — Multi-sig REPL bare-symbol display | pending | Per `multi-sig-introspection.md`. `format_overloaded_variants` helper; rewrite `format_def_entry` (~line 3150) and `format_entry_sig` (~line 342). |
| /int | Step 5d (iii) — Cranelisp.toml lookup | pending | Per `cranelisp-toml.md`. Add `toml = "0.8"` dep; `load_project_config_lib_dirs` in `src/session.rs`; tier 2 in `assemble_lib_dirs`. |
| /backend | `io.rs:28` RC residual fix per `ring2-rc.md` §10 (Form A or B) | pending | Per Condition 6. Audit all `extern "C"` in `platforms/*/src/lib.rs` + `crates/cranelisp-platform/src/lib.rs` — Form B preferred if >2 externs affected. |
| /qa | Verify 2 carried Wave-5 tests flip green: `tests/ring2.rs::neg_private_submodule_not_importable_from_peer` + `tests/repl_experience.rs::display_overloaded_fn_shows_all_variants` | pending | Per `tests/plan/ring4.md §G.13`. |
| /qa | New integration test for Cranelisp.toml lookup in `tests/e2e.rs` | pending | Cover precedence over `CRANELISP_LIB`, missing-config-falls-through, malformed-config-error. |
| /qa | 4 `/mem` E2E integration tests per `tests/plan/ring4.md §G.13` (Sprint 57 carry) | pending | Through `run_repl` with stdout assertions on `; live:` / `; allocs:` / `; delta:`. |
| /qa | 2 `io.rs:28` regression tests per `tests/plan/ring4.md §G.14` | pending | `decision24_print_string_input_rc_balanced` + `decision24_print_string_repeated_rc_no_growth`. |
| /review | Review Wave 4 code | pending | Per skill — privacy enforcement covers both surface + direct paths; multi-sig display matches §1.3 + §4.1.1; toml lookup precedence matches §8.11.4. |

**Gate criterion**: 2 Wave-5 carries flip green; Cranelisp.toml lookup demonstrated by test; `/mem` E2E tests pass; `io.rs:28` regression tests pass; baseline preserved or improved; `cargo clippy` clean per-crate.

### Wave 5 — `/qa` prior-ring coverage + re-triage (parallel throughout)

Parallel to Waves 2/3/4. Read-only against spec + tests. Gated by nothing.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Continue prior-ring negative-coverage promotion (per `spec/index.md:3` priority list) | pending | Module/import boundaries (§8); match exhaustiveness (§6.5); REPL category boundaries — pick what fits. |
| /qa | Re-triage `sketch_run_tests_pass_fn_called` + Sprint 57 follow-on `sketch_port` failures | pending | Per `tests/plan/ring4.md §G.16`. Likely cleared by Step 5b; if not, file FIXME on owning skill. |
| /qa | Re-pin 4th sprint23 cache/link failure name (documented "3", observed "4") | pending | Empirical at Wave 2 baseline; likely `cache_repl_writes_on_import`. |
| /spec | Close-time prior-ring coverage sweep | pending | Parallel to /qa Wave 5. File FIXMEs for any newly-discovered gaps. |
| /spec | Apply Step 5e auto-bump policy: when last sub-section gains `[Tested ...]`, bump heading annotation | pending | Per Step 5e + Sprint 57 Wave 5 architectural concern. Procedural change to `spec/CLAUDE.md`. |

**Gate criterion**: re-triaged failures resolved or filed; close-time coverage sweep clean.

### Wave 6 — Showcase + close (gates sprint close)

Depends on Waves 2 + 3 + 4.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /repl | Create `repl/demos/ring4p.demo` showcasing Phase 5 deliverables | pending | Vignettes: REPL redefinition with `/mem` showing live-bytes drop (Scenario 2 — headline); cache-hit fast restart; private submodule import rejection; multi-sig bare-symbol display. |
| /repl | Verify all prior demos play cleanly | pending | Regression gate. Reference Sprint 57 Wave 6 pattern. |
| /repl | Refine `repl/spec.md` for any §1.3 + §4.1.1 + §3.7 changes surfaced during Wave 4 implementation | pending | Per /repl plan in §Skill Plans. |
| /port | Run exemplar Sudoku Solver against Phase 5 build | pending | Sprint 19 stack-overflow remains pre-existing — does not block sprint close. Demo excerpt showing test scaffolding through `discover-tests`/`run-test` (after Wave 0 exemplar rewrite). |
| /stdlib | Run stdlib integration tests against Phase 5 build | pending | No surface change expected. |
| /examples | Run `examples/*.cl` against Phase 5 build | pending | 15/15 expected. |
| /docs | Audit `user/` for stale references; refresh if Cranelisp.toml lookup adds user-visible config | pending | Low burden — pipeline-internal sprint. |
| /qa | Full regression run + close-time coverage audit | pending | Per `tests/plan/ring4.md` step 22. Confirm spec-surface coverage; promote any newly-covered annotations. |
| /sprint | Update close checklist with Step 5e procedural change | pending | Per Step 5e. |
| /arch | Regenerate `design/arch/sequence-diagram/v4-target.svg` + `.png` from `.mmd` source | pending | Decision 31 reconciliation lag; one-line cosmetic. |

**Gate criterion (sprint close)**: all Phase 5b items in close checklist met; `ring4p.demo` plays cleanly; prior demos regression-free; **≤4 failing** (15 pre-existing − 13 cleared by 5b − 2 cleared by 5d (i)+(ii) + slack); 0 ignored tests for in-scope features; SIGBUS not regressed; Decision 31 Scenario 2 demonstrably active; Conditions 1–8 satisfied.

### Cross-wave notes

- **Parallelism**: Wave 0 cosmetic + Wave 5 prior-ring run throughout. Wave 4 (5d items) may run in parallel with Wave 3 (5c).
- **`/review` is invoked after each code-producing wave** — not batched at the end.
- **Tests are written spec-first**: failing-against-spec tests committed un-ignored; implementation passes must close them within the sprint.
- **Build must be green after each sub-step**. If a step breaks the build, fix before proceeding.
- **No descoping** per user direction. Burden risk surfaces as user escalation, not auto-deferral.
- **`/int` clean-its-own-crate discipline** (per project memory): every `/int` implementation sub-agent must run `cargo check` and fix warnings introduced by its changes.

## Notes

- Baseline at sprint open: 1679 passed / 17 failed (15 pre-existing + 2 explicit Sprint 58 carries) / 0 ignored.
- Expected failure count at close: ≤4 (Step 5b expected to clear 13 of 15 pre-existing; Step 5d (i)+(ii) clear the 2 carries).
- FIXME-after-close target: 0 on source tree; acceptable to file Step 5c-related forward FIXMEs if generics activation surfaces follow-on cleanups.
- Decision 31 Scenario 2 ships in this sprint — the headline REPL/`/mem` behaviour for the demo.

## Outcome

{Filled in when sprint closes.}

### Delivered

{...}

### Deferred

{...}

### Findings

{...}
