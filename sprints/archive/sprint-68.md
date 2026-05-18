# Sprint 68: Primitives as uniform module + facade lockdown + FQTypeName completion

**Status**: PHASE 7 CLOSE — OUTCOME DRAFTED; PENDING USER APPROVAL TO ARCHIVE. Phase 6 user-facing assessment + action SKIPPED per user direction 2026-05-18.

**Goal**: Collapse the `primitives` special-case into the standard cross-module call path via a statically-constructed SymbolTable + GotTable in the primitives crate, referenced at CompilerSession startup; lock down the resulting facade narrowing with `cargo public-api` baselines on every touched crate; complete the FQTypeName binding-facade-to-source migration.

## Scope

### In-scope (the simplification)

The pillar is FIXME 0210 — `primitives` becomes a uniform module via a **statically-constructed** SymbolTable + GotTable owned by the `cranelisp-primitives` crate:

- `cranelisp-primitives` exposes a single pub static `PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<Code, ()>>>` (the SymbolTable side already exists per FIXME 0159 work). The SymbolTable's `Arc<GotTable>` is populated at `LazyLock` init time with raw fn ptrs to every non-inlined primitive at prescribed slot indices (string ops, marshal, per-type to_string, int/float/bool conversions, `not`).
- Per Decision A2: raw `*const u8` is stored directly in the GOT slot's `AtomicPtr<u8>` — no `Code` enum wrapping. Decision 35 ("GOT is single source of truth; no per-entry pointer field") is the canonical alignment.
- Per Decision B (resolved as the user-named hybrid): the GOT is **statically constructed in the primitives crate** and referenced at CompilerSession startup. The session's primitives module entry holds an Arc-clone of the same GotTable. From that point on, dispatch is **functionally equivalent to any other module** — no special case in backend's `symbol_lookup_fn`. The Arc semantics already in `SymbolTable.got` carry the wiring; no third "static GOT" category is introduced in Decision 23's two-GOT model.
- Backend's existing cross-module call path (Decision 31) is the dispatch mechanism for primitives. No new codegen path.
- `JITBuilder::symbol(name, ptr)` narrows to ONLY intrinsics (genuinely runtime-special; the asymmetry becomes load-bearing — intrinsics aren't a module so they can't go through a GOT).
- Backend's `intrinsic_symbols()` primitives enumeration retires (FIXME 0191).
- `ring0_jit_symbols()` retires (FIXME 0182).
- `cranelisp-primitives` pub-API collapses to a single pub static (`PRIMITIVES_TABLE`); the ~22 individual `pub extern "C" fn` items demote to `pub(crate)` with `#[used]` discipline.
- exe-bundle's force-link `pub use cranelisp_primitives::string;` lines retire; replaced by an `init_primitives_got()` startup hook (or `#[used]` via an `extern crate cranelisp_primitives;` reference in `cranelisp_init_platform`) for `--link` mode.

Ring 0 inlined ops (`add-i64`, etc.) are unchanged — they remain raw Cranelift IR emission and never touch any symbol table or GOT.

`not` (per spec `appendix-a-builtins.md:79`, tested by `tests/ring0.rs::boolean_not_true`) is authored as a primitive in this sprint per Decision C1, alongside the existing primitives. Closes FIXME 0157.

### In-scope (facade lockdown)

For every crate touched by the simplification, the change-set MUST include:

1. Regenerated `crates/{crate}/public-api.txt` baseline.
2. Updated `design/arch/facades/{crate}.md` naming + dispositioning each added/changed/removed item.
3. The facade compliance test (S67 W0 scaffolding) green for the affected crates.

Touched crates: `cranelisp-primitives`, `cranelisp-intrinsics`, `cranelisp-backend`, `cranelisp-exe-bundle`, plus `src/` (int binary).

### In-scope (FQTypeName completion)

FIXME 0151 promotes from "deferred" to **in-scope** per user direction: facade-binding work was largely done in S65–S67 and the source-side migration is partial-but-substantial (verified pre-sprint: `cranelisp-types` defines it; `cranelisp-typecheck` 71 uses; `cranelisp-backend` 10 uses; `cranelisp-frontend` 0 uses — correct, pre-resolution). S68 verifies what is done and completes the remaining gaps at the crate edges that are already in the facade-lockdown blast radius (`primitives`, `intrinsics`, `int`, `platform`).

Work shape:
- Per-crate audit: grep for bare `TypeName` at resolved-stage API boundaries; promote to `FQTypeName` per `facades/types.md` binding language.
- The two named exceptions in `facades/types.md` (reverse-lookup; receiver-pinned) are respected, not migrated.
- Tests: typecheck/backend boundary tests proving `FQTypeName` round-trips across crate edges.

### In-scope (mechanical debt that naturally co-lands)

- FIXME 0162 — `design/int/platform-registry-removal.md` reflect post-rollback GOT-as-source-of-truth.
- FIXME 0163 — `design/backend/module-caching.md` same.
- FIXME 0164 — `design/typecheck/ast-annotation.md` same.
- FIXME 0157 — `not` as primitive per spec (resolved Decision C1; authoring lands with the primitives uniformity work).
- FIXME 0209 — `/spec` §4.12.9 reword (compile-time → link-time framing for `--link`-mode `(trace ...)`). Independent, small.
- FIXME 0196 — int facade inline-comment drift (5 → 7 variants). One-line.

### Out-of-scope (deferred with explicit rationale)

| Item | Why deferred | Target |
|---|---|---|
| FIXME 0194 — SymbolDescription.related population | Needs source-side cross-ref machinery work; orthogonal | S69+ |
| Harvest FIXMEs 0125–0149 (legacy test harvest) | Independent work stream; opportunistic | Any |
| FIXME 0121/0142/0145/0148 — pre-existing failing-test carries | Investigation work, not facade work | S69+ |
| FIXME 0181 — cross-module macro 3-module stack overflow | Defect investigation | S69+ |
| FIXME 0172 — trait-method short-name resolution | Defect investigation | S69+ |
| Wave 5 /review × 8 (skipped S67) | Pickup once S68 lands its own /review cycles | S69 |
| Performance baselines | Pre-requires stable codegen path | Post-FQTypeName |

## Decision review gate — RESOLVED 2026-05-17

Three architectural Decisions were reviewed before Phase 2 (`feedback_explicit_decision_review.md`):

- **Decision A — resolved A2**: raw `*const u8` stored directly in primitives GOT slots; no `Code` enum variant for extern origin. Aligns with Decision 35 ("GOT is single source of truth").
- **Decision B — resolved as the static-table-in-primitives-crate hybrid**: the SymbolTable AND GotTable are statically constructed inside `cranelisp-primitives` (extending the existing `PRIMITIVES_TABLE: LazyLock<SymbolTable>` work). CompilerSession startup references this static; the session's primitives module entry holds an Arc-clone of the same GotTable. From session-init onward, primitives are **functionally equivalent to any other module** — no special case in backend's `symbol_lookup_fn`. Closes FIXME 0161; supersedes the per-batch-vs-process-lifetime framing as a false dichotomy.
- **Decision C — resolved C1**: `not` is a primitive per spec `appendix-a-builtins.md:79`. Authoring lands in S68. Closes FIXME 0157.

`/arch` will be invoked with these resolutions; new Decision register entry (#0048 or next-free) captures the rationale.

## FIXME debt

| FIXME | Target | Status | Disposition |
|---|---|---|---|
| 0210 | /arch + cascade | open | **Primary** — drives Phase 3 design + Phase 5 implementation |
| 0161 | /arch | resolved by Decision B | Closes with one-line note: superseded by static-table-in-crate hybrid |
| 0182 | /dev (primitives, int) | partial | Closes when 0210 lands (ring0_jit_symbols deletes) |
| 0191 | /dev (backend) | open | Closes when 0210 lands (intrinsic_symbols shrinks) |
| 0157 | /arch | resolved by Decision C1 | `not` authored as primitive in S68 |
| 0151 | /dev (multiple) | promoted in-scope | Audit + complete FQTypeName threading at facade-locked crate edges |
| 0162 | /design (int) | open | Wave 6 — mechanical |
| 0163 | /design (backend) | open | Wave 6 — mechanical |
| 0164 | /design (typecheck) | open | Wave 6 — mechanical |
| 0196 | /design (int) | open | Wave 6 — one-line |
| 0209 | /spec | open | Wave 6 — small |

## Architecture review (Phase 2) — PASS

**Verdict**: PASS, no revisions required. Reviewed 2026-05-17.

### Outcomes

- **Decision 0048 filed** at `design/arch/decisions/0048-primitives-static-symboltable-and-got-in-crate.md` — `cranelisp-primitives` owns `LazyLock<Arc<SymbolTable>>` with its `Arc<GotTable>` populated at static-init; CompilerSession startup `Arc`-clones into the session's `SymbolTables`. Carves explicit exception against Decision 31 (primitives are process-static, not per-batch); aligns with Decision 35 (GOT remains single source of truth); requires NO new category in Decision 23's two-GOT model; primitives never enter the cache so Decision 30's `register_module_cached` path needs no special case.

- **Public-API trajectory confirmed** across 5 crates:
  - `cranelisp-primitives`: ~24 pub items → **1** (`PRIMITIVES_TABLE` static). All extern fns demote to `pub(crate) extern "C"` + `#[used]`. `ring0_jit_symbols()` retires. `not` added. Low regen risk.
  - `cranelisp-backend`: `intrinsic_symbols()` signature unchanged; body shrinks (no pub-api impact). Low risk.
  - `cranelisp-intrinsics`: no pub-api impact (`JITBuilder::symbol` narrowing is consumer-side).
  - `cranelisp-exe-bundle`: force-link `pub use` lines retire; replaced by an explicit `cranelisp_init_primitives()` no-op that forces `LazyLock::force(&PRIMITIVES_TABLE)` at startup (preferred over implicit `#[used]` discipline — see /arch's recommendation below).
  - `src/` (int binary): session init references `PRIMITIVES_TABLE`. No pub-api.

- **FQTypeName audit scope confirmed**: 5 crates (`primitives`, `intrinsics`, `platform`, `int`/`src`, plus a verification sweep on `backend` for the 10 known sites). 4 facades to verify against source. Two exceptions restated as binding for the audit agents: (1) reverse-lookup at primitive emission sites; (2) receiver-pinned lookups. **Edge case flagged**: a fn that takes `TypeName` syntactically but *performs* resolution inside (e.g., `resolve::*` in typecheck) is the lift site itself — bare in, FQ out; auditors MUST NOT migrate lift-site signatures.

- **Principle 8 risk**: bounded. The static-table-in-crate shape IS the target shape — the GOT-indirect cross-module call path is the existing mechanism, this Decision wires primitives onto it. Decision 48 becomes vestigial post-S68 (outcome embodied in source + facades).

### /arch recommendation for Phase 3 (non-blocking)

Adopt explicit `cranelisp_init_primitives()` (forcing `LazyLock::force`) in exe-bundle's startup hook over implicit `#[used]` discipline — makes the dependency legible at the site that needs it. Fold into Wave 2 `/design` brief for `/design (int)` or a dedicated `/design (exe-bundle)` slice.

## Skill plans (Phase 3) — DELIVERED

All 8 skill invocations complete. Resolved FIXMEs: **0162, 0163, 0164, 0196, 0209** (5 closed in-sprint via Phase 3 design work).

| Skill | Status | Notable outputs |
|---|---|---|
| `/spec` | done | §4.12.9 reworded for link-time framing; FIXME 0209 deleted |
| `/design (primitives)` | done | Facade: `pub static PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<Code, ()>>>` as single item; inventory table with `not` marked NEW; demoted-surface enumeration; BC invariants 3+6 |
| `/design (intrinsics)` | done | Facade: explicit `JITBuilder::symbol`-narrowing-to-intrinsics-only; Decision 48 cited as boundary-of-asymmetry; zero pub-api impact |
| `/design (backend)` | done | Facade: `intrinsic_symbols()` intrinsics-only enumeration; module-caching.md swept; FIXME 0163 deleted; primitives-never-cached carve-out added |
| `/design (int)` | done | int.md: new session-init + exe-bundle startup contract sections; platform-registry-removal.md swept; FIXMEs 0162 + 0196 deleted |
| `/design (typecheck)` | done | ast-annotation.md §11.3+§12.2+§12.5 swept of `platform_fn_ptr`; got_slot semantics restated; FIXME 0164 deleted |
| `/design (platform)` | done | Audit confirms 0 `TypeName`/`FQTypeName` hits in source — Phase 5 nothing-to-do on this workstream |
| `/qa` | done | 16-test plan with architectural invariant test #4 (CLIF inspection) as delivery proof |

## Phase 3 revisions — RESOLVED 2026-05-17

User-arbitrated revisions to Decision 0048; landed via focused `/arch` reconciliation. Resolved state:

- **Revision 1 — `Code::Primitive` marker variant**: Decision A2 amended. `Code::Primitive` (full word) added to the `Code` enum as a no-payload marker. `ModuleEntry::Def.code = Some(Code::Primitive)` on every primitives entry. GOT slot still holds raw `*const u8` (Decision 35 invariant preserved). Cleaner semantics: every callable entry's `code` field expresses its lifecycle category (JIT-owned / linker-owned / process-static-primitive).
- **Revision 2 — backend dep-ban**: `cranelisp-backend` MUST NOT depend on `cranelisp-primitives` (workspace and dev deps alike). The architectural invariant "primitives dispatch reaches code via GOT, never via direct extern" is enforced **structurally** by the workspace DAG, not by behavioral CLIF inspection. Test #4 reframed: from CLIF-shape regex to Cargo.toml structural assertion.
- **New Principle 18** filed: "Enforce architectural invariants structurally where possible." Generalizes the dep-ban pattern. `design/arch/principles/18-enforce-invariants-structurally.md`.
- **Cascade**: Decision 0048 amended in place (frontmatter + Shape + Relationship + new dep-ban § + Rationale alternatives + Consequences + Cross-references). Facades updated: primitives.md, backend.md, types.md, int.md, interfaces.md. Decision register index in `design/arch/CLAUDE.md` updated.

## Pre-Phase-4 atomic-edit requirement (from /arch)

Wave 4 implementation must treat the backend ↔ primitives Cargo.toml edge as an atomic edit:
- Backend-side: delete all `cranelisp_primitives::*` Rust-path references in `intrinsic_symbols()` and any other consumer; delete the `cranelisp-primitives` line from `crates/cranelisp-backend/Cargo.toml`.
- Primitives-side: add the `cranelisp-backend` line to `crates/cranelisp-primitives/Cargo.toml` (for the `Code::Primitive` variant import).

Both must land in the same commit. Else the workspace doesn't build in the intermediate state.

## Phase 3 exit-gate concerns — RESOLVED

Three concerns surfaced by design agents need resolution before Phase 4 wave organization:

### Concern A — new crate dep edge `cranelisp-primitives → cranelisp-backend` (raised by /design primitives)

Post-S68 facade specifies `pub static PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<Code, ()>>>`. The `Code` type parameter lives in `cranelisp-backend` per Decision 41. Three options:

- **A1**: introduce dep edge `cranelisp-primitives → cranelisp-backend` (acyclic, just-for-type-name).
- **A2**: relocate `Code` to `cranelisp-types` (re-opens Decision 41).
- **A3**: primitives crate exposes a raw-state struct (`Vec<EntryData>` + GOT slot mapping); session crate constructs the typed `SymbolTable<Code, ()>` wrapper at init time. Preserves DAG; small awkwardness at session-init site.

### Concern B — CLIF-inspection harness for architectural invariant test (raised by /qa)

Test #4 (primitive calls emit GOT-indirect, not direct extern) needs a way to read CLIF for a compiled snippet. Two options:

- **B1 (/qa recommended)**: `#[cfg(test)]`-only API inside `cranelisp-backend` that compiles a snippet and returns CLIF as `String`; test lives as in-crate unit test. No e2e harness change; preserves two-tier rule.
- **B2**: add `Cranelisp::with_codegen_trace()` to e2e harness; set `CRANELISP_CODEGEN_TRACE=1`; capture stderr and string-match CLIF idioms.

### Concern C — `facades/types.md` row misattribution (raised by /design platform)

`facades/types.md` lists `src/platform.rs:426` under §platform table, but that file lives in `src/` (int binary). One-paragraph row-move correction needed in an `/arch`-owned facade. Two options:

- **C1**: fold into Wave 6 mechanical doc work in Phase 5.
- **C2**: one-shot `/arch` invocation now to correct.

Recommendation: **C1** — defer to Wave 6.

## Waves (Phase 4) — PROPOSED

Wave structure respecting (a) Decision 0048's atomic-edit requirement at the backend ↔ primitives Cargo.toml edge, (b) the methodology's QA-first Phase 5 Stage 1 + per-crate D/D/R Stage 2 model, and (c) Principle 18's structural-enforcement preference.

**FQTypeName audit folded into per-crate /dev briefs** — only /design (platform) delivered a Phase 3 audit (found 0 hits). Other affected crates (primitives, intrinsics, int) get their audit + fix as part of their /dev work, not a separate wave.

### Wave 1 — QA Stage 1: failing-tests authoring (Phase 5 Stage 1)

| Skill | Crate | Task |
|---|---|---|
| /qa | tests/ | Author 16-test plan failing-not-ignored. Test #4 reframed: Cargo.toml dep-ban structural assertion (no CLIF inspection needed per Principle 18). |

### Wave 2 — Backend additive prep (Phase 5 Stage 2, serial gate)

Pure addition; lands before Wave 3 can start.

| Skill | Crate | Task |
|---|---|---|
| /design (backend) | cranelisp-backend | Light refine — record Code::Primitive variant authoring in design doc |
| /dev (backend) | cranelisp-backend | Author `Code::Primitive` marker variant on `Code` enum. Unit tests for constructibility + pattern-match. No removals. |
| /review | cranelisp-backend | Change-set review |

### Wave 3 — Partial: Static-table additive + exe-bundle wiring

Wave 3 PARTIAL landed: /dev (primitives) authored `PRIMITIVES_TABLE` with ~39 entries + `extern_shims()` harvest + unit tests, keeping transitional `<(), ()>` parameterization and `code: None`. Discovered Cargo.toml cycle (FIXME 0211); stopped before the cycle. /dev (int) Wave 3 work still to fire — independent of the cycle.

| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev (primitives) | cranelisp-primitives | Static table additive (39 entries, extern_shims, unit tests) | DONE (partial — pending Wave 4 atomic flip) |
| /dev (int) | src/, cranelisp-exe-bundle | Author `cranelisp_init_primitives()` in exe-bundle forcing `LazyLock::force(&PRIMITIVES_TABLE)`. Retire `pub use cranelisp_primitives::*` force-link lines. **No session-init wiring this wave** (deferred to Wave 5 because the session's SymbolTable type parameters don't yet match PRIMITIVES_TABLE's transitional `<(), ()>` shape). | PENDING |

### Wave 4 — Combined atomic dispatch: primitives + backend + src/ session-init (Phase 5 Stage 2)

**Option 1 resolution to FIXME 0211** (user-arbitrated 2026-05-17): single /dev agent edits all three crates atomically. Narrow-per-crate guideline yields to the atomic unit imposed by Decision 0048's structural-invariant dep-ban + the codegen-reach-primitives invariant. Closes FIXME 0211.

**Why session-init folded into Wave 4**: between backend stopping `intrinsic_symbols()` primitives registration AND session inserting `PRIMITIVES_TABLE` into `SymbolTables`, no codegen path exists to reach primitives. The session-init call must land in the same change-set.

| Skill | Crates | Task |
|---|---|---|
| /dev (combined: primitives + backend + src/) | all three | **Primitives**: Add `cranelisp-backend` dep to Cargo.toml. Flip `PRIMITIVES_TABLE` from `LazyLock<SymbolTable<(), ()>>` → `LazyLock<Arc<SymbolTable<Code, ()>>>` with `code: Some(Code::Primitive)`. Demote ~22 `pub extern "C" fn` items to `pub(crate)` + `#[used]`. Delete `ring0_jit_symbols()` + re-export. Regenerate primitives' `public-api.txt`. **Backend**: Shrink `intrinsic_symbols()` to intrinsics-only (regular cross-module dispatch handles primitives via PRIMITIVES_TABLE; no new codegen path needed). Delete all `cranelisp_primitives::*` Rust-path references. Remove `cranelisp-primitives` from `crates/cranelisp-backend/Cargo.toml`. Regenerate backend's `public-api.txt`. FQTypeName 10-site verification sweep at backend edges. **src/**: Insert `Arc::clone(&*PRIMITIVES_TABLE)` into the session's `SymbolTables` map at `ModuleFullPath::primitives()` during session init. FQTypeName audit at src/ (lift `TypeName::from("IO")` reverse-lookups at `src/{exe,pipeline,platform}.rs` to `FQTypeName` if not classified as exception). **On close**: delete FIXME 0211. |
| /review × 3 | each crate | Per-crate change-set review including dep-ban verification + pub surface collapse + session-init wiring + test flips |

### Wave 4b — Deep fix: uniform GOT-indirect emission — DONE

Surfaced post-Wave-4 by full-workspace nextest: 6 `mode_equiv_*` cache-reload tests failed (`unresolved symbol: str-eq`). Investigation found Wave 4 codegen unification was incomplete — `compile_resolved_call::BuiltinFn` arm in `apply.rs` bypassed `resolve_got_target` and emitted direct-extern; typecheck's `register_ring1/3/vec_primitives` overwrote PRIMITIVES_TABLE-derived session entries with `got_slot: None`. Fresh JIT worked via Cranelift's dlsym fallback; cache linker has no dlsym → fail.

| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev (backend) | cranelisp-backend + cranelisp-typecheck | apply.rs BuiltinFn arm probes resolve_got_target → GOT-indirect on Some, extern fallback on None (preserves trace ADT intrinsics). builtins.rs Ring 1/3/vec-len now allocate_got_slot() per Ring 0's existing shape. Updated 1 backend unit test to assert GOT-indirect contract. | DONE |

**Test results**: 6 `mode_equiv_*` tests PASS, 10/10 S68 tests PASS, 151/151 backend unit tests PASS, 346/346 typecheck unit tests PASS, no new regressions. Pre-existing 5 failures unrelated (verified via stash). Cached `.o` post-fix carries only `__cranelisp_got_primitives` relocations (data symbol); zero function-symbol direct externs for primitives.

### Wave 5 — Mechanical cleanup — DONE

| Skill | Task | Status |
|---|---|---|
| /arch | `facades/types.md` row-move (`src/platform.rs:426` §platform → §int per /design (platform) audit). Summary table updated: platform 0 keeps, int 4 reverse-lookup keeps. | DONE |
| /dev (int) | `cranelisp-exe-bundle` `public-api.txt` baseline generation (was missing per Wave 3 flag). 11 lines; `cranelisp_init_primitives` + `cranelisp_init_platform` present; zero `cranelisp_primitives::*` re-exports; 8 intrinsics re-exports retained. | DONE |

### Wave 6 — Facade compliance lockdown — DONE

| Crate | Verdict | Notable findings |
|---|---|---|
| primitives | PASS-with-concerns | FIXME 0212 filed: `#[used]` discipline contract gap (extern_shims() works in practice; facade contract drift) |
| backend | **PASS** | The 3 "orphans" flagged by primitives review (`ALIGN`, `Output`, `Owned`) resolved as auto-trait projections; not facade items |
| intrinsics | PASS-with-concerns | FIXME 0213 (facade §String primitives stale post-S67 W3); FIXME 0215 (heap_string null-deref SIGABRT vs spec §12.1.2 — pre-existing) |
| int | PASS-with-concerns | FIXME 0214 (facade should enumerate 8 intrinsics re-exports per baseline-diff discipline) |

All structural invariants verified: dep-ban, uniform GOT-indirect dispatch, Code::Primitive variant, session-init wiring, exe-bundle startup hook, FQTypeName lift-site pattern, s68 test suite 10/10. Decision 0048 fully embodied. 4 FIXMEs filed for S69 — non-blocking facade-doc drift + one pre-existing spec violation.

### Wave 7 — Phase 6a user-facing assessment

| Skill | Surface | Task |
|---|---|---|
| /repl | REPL | Assess REPL works against delivered state; file gap FIXMEs |
| /port | exemplar/ | Run Sudoku solver; assess; file gaps |
| /stdlib | stdlib/ | Assess stdlib against delivered state |
| /examples | examples/ | Verify all learning-sequence examples still play |
| /docs | user/ | Assess user docs against delivered state |

### Wave 8 — Phase 6b user-facing action

| Skill | Surface | Task |
|---|---|---|
| /repl | demos/ | New sprint demo; prior demos replay green |
| /port | exemplar/ | Exemplar refresh against delivered state |
| /stdlib, /examples, /docs | per-surface | Per-surface deliverables per 6a plans |

## Notes

- **Phase 3 concerns surfaced (track for exit gate)**:
  - `/design (primitives)` flagged: post-S68 facade uses `SymbolTable<Code, ()>` parameterization → introduces a `cranelisp-primitives → cranelisp-backend` dep edge (where `Code` lives per Decision 0041). Acyclic but new. Alternatives: relocate `Code` to `cranelisp-types` (re-opens D41), OR primitives crate exposes raw-state struct that session wraps with type params at init (preserves DAG). **Decide at Phase 3 exit gate.**
  - `/design (primitives)` flagged: `#[used]` and `cranelisp_init_primitives()` are orthogonal, both required in Wave 5 brief — `#[used]` for per-fn DCE; explicit `LazyLock::force` for population trigger legibility.
  - `/design (platform)` flagged: `facades/types.md` misattributes `src/platform.rs:426` to the §platform subsection — file actually lives in `src/` (int binary). One-paragraph row-move correction needed in this `/arch`-owned facade. Fold into Wave 6 mechanical work OR escalate to /arch one-shot.
- **Decision review gate**: RESOLVED 2026-05-17 (A2 / static-table-in-crate hybrid / C1). Awaiting user approval of overall scope to fire Phase 2.
- **Compliance enforcement**: every Wave 4/5 dev change-set must regenerate the affected `public-api.txt` baseline AND update the corresponding facade in the SAME commit (per `design/arch/CLAUDE.md` §"Baseline-diff discipline"). The facade compliance test gates the lockdown.
- **Test budget**: keep new tests narrow and small — the simplification path is internal; e2e coverage exists for primitives behaviour, this sprint adds tests for the dispatch-path invariant (primitives reached through standard cross-module GOT path; `--link` works without force-link; FQTypeName round-trips clean).
- **FQTypeName**: pre-sprint audit confirms partial migration — types (defined), typecheck (71 uses), backend (10 uses), frontend (0 — correct). S68 closes the source-side gap at the facade-locked crate edges.

## Outcome (Phase 7)

### Delivered

**Primary deliverable — Decision 0048 fully embodied**: `cranelisp-primitives` is now a uniform module, dispatched through the same cross-module GOT-indirect path as user-to-user calls.

- Static `PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<Code, ()>>>` in `cranelisp-primitives`; 45 entries with `code: Some(Code::Primitive)` and populated GOT slots.
- `Code::Primitive` marker variant added to `Code` enum (Wave 2, additive).
- Session-init wires `Arc::clone(&*PRIMITIVES_TABLE)` into the session's `SymbolTables` at `ModuleFullPath::from("primitives")` before any user module loads.
- exe-bundle authored `cranelisp_init_primitives()` extern fn (forces `LazyLock::force(&PRIMITIVES_TABLE)`) — called from `cranelisp_init_platform` at startup; retired the 7 `pub use cranelisp_primitives::*` force-link re-exports.
- Backend's `intrinsic_symbols()` enumerates intrinsics only — primitives entries retired.
- `ring0_jit_symbols()` retired.
- ~45 `pub extern "C" fn` items in primitives demoted to `pub(crate)` (with `#[unsafe(export_name = "...")]` retained for linker symbol exposure; `#[used]` discipline contract gap deferred to FIXME 0212).
- **Workspace structural invariant: `cranelisp-backend` MUST NOT depend on `cranelisp-primitives`** — verified by the new `crates/cranelisp-backend/tests/no_primitives_dep.rs` integration test. The dispatch invariant "primitives reach code via GOT, never via direct extern" is now enforced structurally by the workspace DAG.
- Wave 4b deep fix: `compile_resolved_call::BuiltinFn` arm in `apply.rs` probes `resolve_got_target` first → GOT-indirect on Some; extern fallback on None preserves trace ADT intrinsics. `register_ring1/3/vec_primitives` in typecheck now allocate session GOT slots per Ring 0's existing shape. Cached `.o` files post-fix carry only `__cranelisp_got_primitives` data-symbol relocations — zero function-symbol direct externs for primitives.

**Spec — Decision 0048 amendment** (in-sprint, 2026-05-17): `Code::Primitive` marker variant replaces the original A2 "code: None" framing. Backend dep-ban subsection added.

**New Principle 18 — "Enforce architectural invariants structurally where possible"**: filed at `design/arch/principles/18-enforce-invariants-structurally.md`. Generalises the dep-ban pattern (workspace DAG, sealed traits, `pub(crate)`, type-parameter constraints, single-source-of-truth fields). Distinct from Principle 05 (testability as boundary design); this one is about *replacing* tests with construction.

**FQTypeName completion at facade-locked crate edges**: `cranelisp-platform` audit confirmed 0 hits (no-op); reverse-lookup sites at `src/{exe,pipeline,platform}.rs` use the lift pattern `FQTypeName::new(ModuleFullPath, TypeName::from(...))` correctly. Backend FQTypeName boundary test (#15) green. `facades/types.md` row-move (Concern C from Phase 3) landed in Wave 5.

**FIXMEs closed (9)**: 0157, 0161, 0162, 0163, 0164, 0196, 0209, 0210, 0211. Pre-existing 5 FIXMEs (0162/0163/0164/0196/0209) also closed via Phase 3 design refreshes.

**New baselines**:
- `cranelisp-primitives/public-api.txt` — collapsed to 9 lines (1 crate + 7 submodule mentions + 1 static).
- `cranelisp-backend/public-api.txt` — regenerated (catches up pre-existing drift in `error.rs`, `artefact.rs`, `code.rs`, `got_observer.rs` module additions).
- `cranelisp-exe-bundle/public-api.txt` — **created** (was missing; 11 lines including `cranelisp_init_primitives`).

**Test results**:
- s68 sprint test suite: **10/10 pass**.
- 6 previously-failing `mode_equiv_*` cache-reload tests: **PASS** (Wave 4b fix).
- backend unit tests: 151/151 pass.
- typecheck unit tests: 346/346 pass.
- `cargo check --workspace`: clean.
- 5 pre-existing workspace failures verified pre-Sprint-68 via stash (unrelated): `mode_equiv_pattern_match_nested` (stack overflow), `stdlib_eq_string_mappable_path`, `stdlib_num_float_mappable_path`, 2 `trait_method_short_name_resolves_as_value_*`, 2 trace tests. Tracked as carries.

### Deferred (with rationale)

| Item | Rationale | Target |
|---|---|---|
| FIXME 0194 (SymbolDescription.related population) | Out of S68 scope per Phase 1; orthogonal to primitives uniformity | S69+ |
| FIXME 0181 (cross-module macro 3-module stack overflow) | Pre-existing defect, not S68 scope | S69+ |
| FIXME 0172 (trait-method short-name resolution) | Pre-existing defect | S69+ |
| FIXME 0121 (spec_08_modules) | Pre-existing failing-test carry | S69+ |
| FIXME 0145, 0148 (exemplar solver regression) | Pre-existing carries | S69+ |
| Harvest FIXMEs 0125–0149 (legacy test harvest) | Independent work stream | Opportunistic |
| FIXME 0212 (primitives `#[used]` discipline gap) | Filed in S68 Phase 7; `extern_shims()` works in practice; contract drift | S69 |
| FIXME 0213 (intrinsics facade §"String primitives" stale post-S67 W3) | Filed in S68 Phase 7; doc drift | S69 |
| FIXME 0214 (int facade enumerates 8 intrinsics re-exports) | Filed in S68 Phase 7; baseline-diff symmetry gap | S69 |
| FIXME 0215 (heap_string null-deref SIGABRT vs spec §12.1.2) | Filed in S68 Phase 7; pre-existing or platform-dependent | S69 |
| Phase 6 user-facing assessment + action | User direction 2026-05-18: skip; no need to update user-facing this sprint | S69+ |
| Performance baselines | Pre-requires stable codegen path; FQTypeName fully landed | Post-S69 |

### Findings

1. **Atomic cross-crate edit discipline** — Decision 0048's structural invariants (dep-ban + codegen-reach-primitives) imposed a multi-crate atomic-edit requirement that the "one-/dev-per-crate" guideline couldn't deliver. FIXME 0211 (filed mid-Wave-3 by /dev (primitives) when the Cargo.toml cycle surfaced) was resolved by Option 1 (combined Wave 4 dispatch). The narrow-per-crate guideline yields to atomic-edit pairs when Decision-driven structural invariants demand it. /sprint should anticipate this pattern in future sprints touching workspace DAG topology.

2. **Test-authoring drift surfaces architectural questions** — Wave 4 verification surfaced 4 FQTypeName tests that string-matched `TypeName::from("IO")` regardless of context, flagging legitimate lift-site patterns as violations. User pushback was decisive: source already conformed to Decision 0047; tests were too broad. The right move was test rewrite (3 deleted; 1 rewritten to scan `public-api.txt` for bare TypeName at pub fn signatures) rather than source migration. **Lesson**: when tests fail, validate against spec/facade BEFORE assuming source is wrong (per `feedback_validate_tests_against_spec.md`).

3. **Wave 4 incompleteness surfaced by cache-reload tests** — The first attempt at Wave 4 atomic dispatch missed `compile_resolved_call::BuiltinFn` and the typecheck-side session-slot allocation. Fresh-path tests passed via Cranelift's dlsym fallback for `extern_name = "..."` symbols; cached-path tests failed because the in-process Linker has no dlsym fallback. **Lesson**: codegen unification claims need cache-reload verification, not just fresh-mode verification. The two paths exercise different symbol-resolution machinery.

4. **`#[used]` vs `extern_shims()` as DCE-prevention** — Decision 0048 prescribed `#[used]` for the demoted extern fns. Implementation used `extern_shims()` (static-init reference) instead, which works in practice. Contract drift (FIXME 0212). Future Decisions naming a specific mechanism should distinguish between "this mechanism MUST be used" and "DCE prevention MUST happen (mechanism is implementation choice)."

5. **Pre-existing public-api.txt baseline drift** — Wave 2's `Code::Primitive` addition's baseline regen caught up substantial unrelated drift (error.rs, artefact.rs, got_observer.rs module additions from earlier sprints). The S67 baseline-diff discipline IS the durable enforcement mechanism, but earlier sprints didn't apply it uniformly. Recommend `/sprint` adopt a workspace-wide baseline-regen audit at sprint open going forward — would have caught this drift incrementally.

6. **Concurrency note** — Cargo backgrounding under harness load caused multiple agent reports to truncate before reporting cargo results. Workarounds: targeted scoped runs (single-test or single-package) tend to complete in foreground; full-workspace nextest often backgrounds and notifies. Not a workflow problem per se, but agents need cargo-result-reporting fallbacks.

### Methodology check

`/arch`'s architectural principles served this sprint well — Principle 18 emerged naturally from the dep-ban arbitration, Principle 8 (interim architecture risk) was correctly invoked at Phase 2 to confirm "target shape, not interim," and Decision 35's "GOT is single source of truth" carried through every architectural decision in this sprint. The Decision-amendment pattern (Decision 0048's in-sprint A2 → Code::Primitive revision; backend dep-ban subsection) demonstrates that the Decision register absorbs in-sprint architectural learning without re-litigation.

No principle adjustments suggested.
