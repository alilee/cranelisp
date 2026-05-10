# Sprint 66: Facade adoption at the edges

**Status**: PHASE 5 LANGUAGE (READY)

**Goal**: Adopt the S65 final-state facades at every crate edge — execute the 9 W4a implementation slices, close the substantive cross-crate-migration FIXMEs, and land D43 (runtime split into `cranelisp-primitives` + `cranelisp-intrinsics`) because the post-S65 facade requires it (Principle 8).

## Scope

### In scope

Execute the 9 implementation slices authored in S65 W4a, against the now-stable final-state facades:

- `design/frontend/implementation-slice-s66.md`
- `design/typecheck/implementation-slice-s66.md`
- `design/backend/implementation-slice-s66.md`
- `design/primitives/implementation-slice-s66.md`
- `design/intrinsics/implementation-slice-s66.md`
- `design/platform/implementation-slice-s66.md`
- `design/runtime/implementation-slice-s66.md`
- `design/int/implementation-slice-s66.md`
- `tests/plan/implementation-slice-s66.md` (QA test plan)

Substantive FIXMEs to close in this sprint:

- **0098** — ResolutionGap / CheckError / ExpansionError migration (frontend, typecheck, int)
- **0099** — GotObserver implementation (backend, int)
- **0100** — Relocate single-consumer types to originating crates
- **0103** — trace / io_trace relocation + IoObserver (cranelisp-intrinsics → int; Phase 1 home is intrinsics per /arch Phase 2 selection)
- **0104** — PlatformError adoption (types, platform, int)
- **0107** — `OwnedPlatformFnDescriptor` `#[non_exhaustive]` (platform)
- **0108** — Relocate `backend/src/display.rs` → int
- **0150** — D43 runtime split: `cranelisp-primitives` + `cranelisp-intrinsics` crates land; backend trait-knowledge tables delete; `cranelisp-runtime` retires; stdlib trait-impl audit (per /arch Option A — Principle 8 binding)

Enforcement gates introduced this sprint:

- `cargo public-api` baseline + per-crate diff enforcement
- 95% pass-rate gate (against post-S64 baseline of 932 / 953)

### Out of scope (deferred)

- **0151** — FQTypeName implementation — S67+ per roadmap line 153.
- **0109** — int decomposition (split `session_v4.rs` + `worker.rs`) — S67+.
- **0116–0149** — Harvest of quarantined `tests/legacy/` tests into owning crates — S67+.
- **Defect 6 cluster (FIXME 0145)** — explicit user re-approval required per S62 close note (4× implicit deferral); not picked up here.
- **S64 baseline carries** — 0121 cache, 0122 link GOT, 0140 import-below-use, 0142 REPL EOF, §8.10.1 SEGV (0149) — must not regress, but not chartered to fix.
- **Phase 6 (user-facing assessment + action)** — explicitly waived for this sprint by user direction. No `/repl`, `/port`, `/stdlib`, `/examples`, `/docs` invocations. Phase 5 closes directly into Phase 7.

## FIXME debt

| FIXME | Target skill | Status | Notes |
|---|---|---|---|
| 0098 | /dev (frontend, typecheck, int) | open | ResolutionGap / CheckError / ExpansionError migration — per slice plans |
| 0099 | /dev (backend, int) | open | GotObserver implementation — backend-side trait + int-side consumer |
| 0100 | /dev (multi) | open | Relocate single-consumer types to originating crates |
| 0103 | /dev (runtime, int) | open | trace / io_trace relocation + IoObserver |
| 0104 | /dev (types, platform, int) | open | PlatformError adoption |
| 0107 | /dev (platform) | open | `OwnedPlatformFnDescriptor` `#[non_exhaustive]` |
| 0108 | /dev (backend, int) | open | Relocate `backend/src/display.rs` → int |
| 0150 | /dev (multi: backend, runtime, primitives, intrinsics, int, stdlib) | open | D43 runtime split — bound into S66 per /arch Option A |
| 0096 | /design (backend) | open | Stale subordinate doc archival — opportunistic during backend slice |
| 0101 | /sprint | open | Runtime / platform audit pass — addressed implicitly by adoption |
| 0102 | /dev (runtime) | open | runtime CLAUDE.md missing — opportunistic during runtime slice |
| 0106 | /design (arch) | open | Archive PlatformRegistry removal — opportunistic during platform slice |

## Architecture review (Phase 2)

**Verdict**: PASS-WITH-REVISIONS — REVISIONS APPLIED 2026-05-07
**Reviewer**: /arch
**Date**: 2026-05-07
**Resolution**: User selected Option A (bind D43 into S66) — required revision #1 resolved. Revisions #2 (Wave 0 types-crate authoring), #3 (FIXME 0103 Phase 1 home → intrinsics), #5 (D43 reshape budget in Notes) applied to SPRINT.md. Revision #4 (/qa baseline-ownership editorial clarification) filed as FIXME `target: /qa`.

### Summary of finding

The 9 W4a implementation slices are individually well-authored, but **3 of the 9 (primitives, intrinsics, runtime-retiring) execute FIXME 0150 / Decision 43 — the runtime split — which the SCOPE DRAFT explicitly defers to S67+ (line 41).** This is not a minor row-level overlap; it is the centre of gravity of those three slices and is the proximate dependency of substantial work in the backend and int slices (backend rows 8–11 trait-knowledge deletions + Cargo.toml dep flip; int rows 17–19, 31 import sweeps; +retirement of `cranelisp-runtime` workspace-wide). The two readings — "S66 lands these because slices were authored" vs. "S66 defers per the SPRINT.md scope statement" — must be reconciled before Phase 3 can begin. Both readings break things: executing D43 in S66 turns this into a multi-crate vertical (S65's S67+ candidate #1) at the cost of the originally-scoped facade adoption; deferring D43 invalidates the primitives/intrinsics/runtime-retiring slices and forces re-authoring of substantial portions of the backend + int slices.

A second, smaller-but-substantive issue: **Wave 2 = "type-relocation foundation"** as drafted under-counts what must land. The types-crate work driving Waves 2/3 has no authoring slice in W4a (the types crate is /arch-owned per the skill def; /design (types) does not exist as a triad). Wave 2 prerequisites must be authored by /arch before Wave 3 begins — this is not a /design slice in any of the existing 9.

### Wave ordering

The proposed Wave 2 (0098, 0100, 0104) / Wave 3 (0099, 0103, 0107, 0108) split is **directionally sound** if and only if the D43 question is resolved **and** the types-crate authoring is sequenced explicitly.

Bilateral cross-slice review of dependencies:

- **0098 (types→frontend→typecheck→int)**: Phase 1 = types (`ResolutionGap` enum, `CodeStore`/`LinkerStore` markers verified) — must land first in Wave 2. Phase 2 = frontend (`expand` migrate-in, `ExpansionError`). Phase 3 = typecheck (`check_form` shape-pivot). Phase 4 = int (typed pattern-match in `process_form`). Frontend Phase 2 + typecheck Phase 3 are parallelisable; int Phase 4 cannot begin until both land.
- **0100 (multi)**: Phase 1 = typecheck pulls `CheckResult`, `CheckError`, `ReplSnapshot` out of types into typecheck (sources confirm `cranelisp-typecheck/src/lib.rs:39` re-exports those four from cranelisp-types today). Phase 2 = backend pulls `CompilationError` + `Got*` out into backend. Phase 1 must precede Phase 2 of 0098 in the int slice's import sweeps (rows 6, 9 of the typecheck slice depend on this).
- **0104 (types→platform→int)**: Phase 1 = types (`PlatformError` enum + `ErrorLocation` carriers) — Wave 2. Phases 2 (platform) + 3 (int) are paired and can land in Wave 3.
- **0099 (backend→int)**: Phase 1 = backend (GotObserver contract); Phase 2 = int (ring buffer + register). Backend Phase 1 → int Phase 2 ordering is straightforward; can land entirely in Wave 3.
- **0103 (runtime→int)**: Phase 1 = runtime (or post-D43, intrinsics) exposes `IoObserver`; Phase 2 = int receives `trace.rs` + `io_trace.rs` files. **This is the FIXME most entangled with D43** — its "Phase 1 home" is `cranelisp-runtime` if D43 is deferred and `cranelisp-intrinsics` if D43 lands. The runtime slice §2.4 surfaces this as a live choice; it needs an architectural answer not deferral to /sprint.
- **0107 (platform)**: single-attribute `#[non_exhaustive]` on `OwnedPlatformFnDescriptor` (confirmed missing at platform lib.rs:583). Independent; Wave 3.
- **0108 (backend→int)**: `display.rs` migration. Independent of the others; Wave 3.

**Required wave-structure correction**: A new **Wave 2a — types-crate authoring** must precede Wave 2 (which becomes 2b — consumer adoption against the new types). The types crate is /arch-owned with no /design slice; /arch must author the new enums (`ResolutionGap`, `CheckError`, `ExpansionError` *receivers*, `PlatformError`, `CompilationError` skeleton if 0100 Phase 2 runs in S66) before any consumer slice begins. This adds an explicit /arch task to Phase 3.

### `cargo public-api` introduction

The /qa slice §1 plumbing plan is coherent and well-structured: per-crate `public-api.txt` files in `crates/{crate}/`, a `cargo xtask api-check` (or `just api-check`) wired into the same CI lane as `cargo nextest run`, and a documented drift workflow (intentional facade change → regenerate baseline + commit both; unintentional drift → fix source). 95% pass-rate gate calibration against S64 baseline (932 / 953) is correctly preserved with a 26-test margin and per-FIXME pre-classified reshape budget.

**Concerns / required revisions**:

1. **Baseline ownership**: the slice assigns baseline regeneration to "/design (crate)" running `cargo public-api` once facade is final. /design does not edit source, only design docs (per the triad). Baseline regeneration is /dev work after each facade-conformant landing, not /design. The slice should clarify: /design verifies the *target* against the facade; /dev runs the tool and commits the baseline; /review approves the diff against /arch's facade approval.
2. **Crate-skeleton dependency**: per-crate baselines for `cranelisp-primitives` and `cranelisp-intrinsics` are listed (§1.1 rows 7–8). These cannot exist without D43 landing. If D43 defers, those baselines defer with it — the /qa plan needs a fork.
3. **Tool installation gate**: `cargo public-api` requires nightly toolchain. The /qa slice does not surface this. Recommend documenting in `tests/CLAUDE.md` and adding to CI doc.

Approach is otherwise approvable contingent on the D43 resolution.

### Verify → signature-change upgrades

Spot-checked high-risk verify rows across slices against current source. **Findings**:

- **frontend slice row 14** (`DefmacroInfo` `#[non_exhaustive]` audit): correctly flagged as "verify-then-attribute" — the slice already anticipates needing to add the attribute. Action class is appropriate.
- **platform slice row 5** (IO_TAG_* and `ABI_VERSION` public consts at lib.rs:1–52): confirmed already aligned post-S65 W1 (`25fa73a`). Verify class correct.
- **platform slice row 6** (`HostContext::dispatch` retirement): confirmed — the source has never carried `dispatch`, only `init()`. Verify class correct.
- **platform slice row 11** (`pub use cranelisp_types::SchedulingClass`): confirmed at lib.rs:41. Verify class correct.
- **platform slice row 10** (Cargo.toml deps unchanged by D43): the slice's "notable finding" is correct — runtime depends on platform, not the reverse. Platform's Cargo.toml is genuinely untouched. Verify class correct.
- **typecheck slice row 7** (`CheckPass`, `FormCheckResult`, `ModuleCheckAccumulator` already in typecheck): confirmed at typecheck/src/lib.rs:32. Verify class correct.
- **frontend slice row 12** (`parse_defmacro` re-exported from defmacro.rs): confirmed.
- **int slice row 38** (`Sess::trampoline(&mut self, module_name: &str)`): the slice flags it as verify-only — defensible. (Did not deep-dive.)

**Recommended upgrades** (signature-change candidates surfaced from the spot-check):

- **None among the rows checked.** The verify rows are conservatively classified.

The slice authors appear to have applied the verify class accurately. Confidence: **MEDIUM-HIGH**. The combination of (a) S65's "verify-and-tighten" framing for substance items partially landed in S64 and (b) /design's slice-authoring discipline produced rows that match source. Recommend /sprint not require a deeper audit at Phase 2; trust will be re-validated at Wave 3 close per /review's per-PR audit.

### Interim-architecture risk (Principle 8)

This is where the **D43 question becomes binding**.

If S66 runs the slices as-authored (executing D43): no Principle 8 risk introduced. Backend's trait-knowledge maps delete; runtime retires; intrinsics + primitives crates land. Every line of S66 source is a move toward the final-state facade. **No throwaway.**

If S66 defers D43 per the SCOPE DRAFT: the originally-scoped facade adoption work (0098, 0099, 0100, 0103, 0104, 0107, 0108) lands against the **runtime-retains-everything** intermediate state. Then S67+ executes D43, which:
- Forces the int-slice import sweep (rows 17–19, 31) to be redone (cranelisp_runtime → cranelisp_intrinsics for 30+ symbols).
- Forces backend's Cargo.toml + IntrinsicSymbol + trait-knowledge deletions (slice rows 8, 10, 11) to be redone.
- Forces FIXME 0103's IoObserver registration host migration from cranelisp-runtime → cranelisp-intrinsics — the runtime slice §2.4 explicitly identifies this as a 2x-cost path under Option (a).

**Principle 8 verdict**: deferring D43 to S67 creates ~1.5–2 weeks of throwaway adoption work (the `cranelisp_runtime::*` import paths land in S66 and re-roll in S67). This is exactly the interim-architecture cost Principle 8 was created to prevent. **The slices are authored coherently against the post-D43 final state for sound Principle 8 reasons.** S65 close note's deferral of FIXME 0150 to "S67+ per-crate vertical sprints" was an over-deferral; the slice authors correctly read the facade as binding and produced the work that the facade requires.

D43 ordering interaction is therefore: **D43 must land in S66 with the rest of the slices, OR D43 must be removed from the dep paths of the seven in-scope FIXMEs, which is structurally impossible because the facades have already absorbed it (Principle 15: facade types live with behavior; runtime has no behavior post-D43).**

### Public-API impact + cranelisp-types deltas

The seven in-scope FIXMEs collectively touch `cranelisp-types` at:

- **New types added** (FIXME 0098 Phase 1): `ResolutionGap` enum, `CodeStore`/`LinkerStore` markers (verify-class — already present per Decision 32).
- **New types added** (FIXME 0104 Phase 1): `PlatformError` enum + `CranelispError::Platform(PlatformError)` variant.
- **Types removed** (FIXME 0100 Phase 1): `CheckResult`, `CheckError`, `FormCheckResult`, `CheckPass`, `CheckState`, `TypeCheckEnv`, `ModuleCheckAccumulator`, `ReplSnapshot` migrate out into `cranelisp-typecheck`.
- **Types removed** (FIXME 0100 Phase 2): `CompilationError`, `GotEvent`, `GotEventTag`, `GotProvenance`, `GotObserver` migrate out into `cranelisp-backend`.

Net: the types crate gets ~3 new types and loses ~13. Public-API surface should *shrink* by S66 close — a healthy direction.

**S67 stability concern**: FQTypeName implementation (FIXME 0151) and D43 implementation (FIXME 0150 if deferred) will both touch the types crate again. If D43 lands in S66, only FQTypeName (single, well-scoped change) destabilizes types in S67 — which is fine. If D43 defers to S67, types takes two large hits in S67 — meaning S66's types-crate baseline is short-lived. This is a second-order argument for landing D43 in S66.

**cranelisp-types updates required** (/arch-authored, must land Wave 2a before any consumer):

1. `ResolutionGap` enum (3 variants per facade).
2. `PlatformError` enum (4 variants per Decision 42).
3. `CranelispError::Platform(PlatformError)` variant.
4. **Verify** `ErrorLocation`, `CodeStore`, `LinkerStore` already final per Decision 32 / 39 (likely yes — substance partial-landed S64).

The FIXME 0100 Phase 1 *removals* are not /arch's authoring — those land in the typecheck slice, but they require coordination because the typecheck slice cannot complete its Phase 1 until the relocations are atomic with int's import-rewrite landing.

### Required revisions to SCOPE DRAFT

Before Phase 3 can begin, the following must land in SPRINT.md:

1. **Resolve the D43 question.** The scope statement (line 41) defers FIXME 0150 to S67+ but the 9 authored slices implement it. Reconcile via one of:
   - **(a) BIND D43 INTO S66.** Update line 41 to remove the deferral; expand sprint goal to acknowledge "facade adoption + D43 split lands together because the post-S65 facade requires it"; update wave plan to integrate the runtime-retiring + primitives + intrinsics workstreams. Update the "Out of scope (deferred)" list. **/arch's recommendation: option (a)** — the slices are authored against final-state facades for sound Principle 8 reasons; deferring D43 creates 1.5–2 weeks of throwaway.
   - **(b) DEFER D43 PROPERLY.** Mark the primitives, intrinsics, runtime-retiring slices as out-of-scope for S66; rewrite the int slice's rows 17–19, 31 to use `cranelisp_runtime::*` paths; rewrite backend slice's rows 8, 10, 11 to keep trait-knowledge maps + cranelisp-runtime dep; rewrite FIXME 0103's IoObserver Phase 1 home as `cranelisp-runtime`. This is substantial slice rework.
   - **(c) PARTIAL.** Land D43 Phase 1 (skeleton crates) + Phase 5 (retirement) in S66; defer Phase 2–4 source migration. Not recommended — leaves `cranelisp-runtime` empty but present, which is its own interim state.

2. **Add Wave 2a — /arch types-crate authoring.** /arch authors `ResolutionGap` + `PlatformError` + `CranelispError::Platform` variant before Wave 2 consumer slices begin. This is /arch authoring work, not /design — clarify in Skill plans (Phase 3) section.

3. **Promote FIXME 0103's "Phase 1 home" question to a Phase 3 architectural input, not a /sprint runtime decision.** The runtime slice §2.4 surfaces options (a) and (b). /arch (this review) selects option (b) — bundle FIXME 0103 with FIXME 0150 Phase 2; IoObserver lands directly in cranelisp-intrinsics. This selection is downstream of revision #1's resolution.

4. **/qa slice §1.1 baseline ownership clarification.** Replace "/design (crate) — runs cargo public-api once facade is final" with "/dev runs the tool; /design verifies against facade; /review approves the diff in same change set as the facade-conformant landing". Editorial — file FIXME `target: /qa` if the resolution requires source change.

5. **Document the 95% gate's pre-classified reshape budget allowance for D43.** /qa slice §2.3 already lists D43 reshapes at "up to ~10–15 conformance tests" but the SPRINT.md "Notes" section should explicitly carry forward the ~13–23 expected-reshape budget within the 47-test envelope.

### Recommendations (non-blocking)

1. **The `process_form` shape-pivot in int slice row 3 + frontend slice row 7 + typecheck slice row 1 is the load-bearing critical path.** /sprint should plan to land all three in a paired Wave 3 sub-batch; if any one slips, the other two cannot validate end-to-end. Recommend a same-wave triad burst.
2. **The Wave 3 "parallel observer/error adoption" framing under-states int's load.** The int slice authors estimate ~10–13 working days = ~2.5–3 S66 waves. Wave 3 cannot complete in one wave-equivalent for int alone; parallelisability across other crates does not reduce the int total. Either accept a 2-wave int allocation, or split int's migration across S66 + S67 with explicit /arch FIXMEs documenting same-sprint deferral rationale.
3. **The 16 open questions surfaced across slices (1 frontend + 4 typecheck + 5 backend + 5 int + 5 runtime + 5 primitives + 3 platform + 1 intrinsics) should be triaged at Phase 3 open.** Most are editorial; a few are substantive (typecheck Q2 — check_form post-Gap state contract; int Q2 — SharedState vs decomposition sequencing). /arch dispatches narrow resolutions before Phase 4 wave plan locks.
4. **The /qa slice's pre-classified reshape table (§2.3) is the right shape but underweights FIXME 0150 Phase 4** (stdlib trait-impl audit). This is the highest-risk reshape per the slice author's own assessment ("up to ~10–15 conformance tests"). Recommend /sprint dedicate observability bandwidth (CRANELISP_RC_TRACE, CRANELISP_CODEGEN_TRACE) to catch circular-impl regressions early.
5. **`design/qa/implementation-slice-s66.md` does not exist; the QA slice lives at `tests/plan/implementation-slice-s66.md`.** SPRINT.md line 21 cites the wrong path. Editorial — fix in same revision.

## Skill plans (Phase 3)

{Filled in Phase 3. Anticipated invocations:}

- `/arch` — public-API + interface set sign-off; `cargo public-api` baseline plumbing approval
- `/design` — narrow per crate; refresh slice against any Phase 2 adjustments
- `/qa` — sprint-wide failing-test authorship covering facade adoption deltas + `cargo public-api` enforcement
- `/dev` — narrow per crate (8 surfaces): frontend, typecheck, backend, primitives, intrinsics, platform, runtime, int
- `/review` — narrow per crate; change-set review against slice intent

`/spec` not anticipated — no language semantics change. Will be invoked only if a slice surfaces a spec ambiguity.

## Waves (Phase 4)

Final wave plan per Phase 3 close (incorporates Option A binding + ParsedEntry + fn_ptr unification + canonical-set sweep):

### Wave 0 — `/arch` types-crate authoring (~2.5d, single-stream)

`/arch` authors in `crates/cranelisp-types/`:
- `ResolutionGap` enum (FIXME 0098)
- `PlatformError` enum + `ErrorLocation` carriers (Decision 42, FIXME 0104)
- `CranelispError::Platform(PlatformError)` variant
- `ParsedEntry` enum + `DefmacroInfo` move-in (FIXME 0156)
- `LinkerError` 2-variant baseline (FIXME 0154)
- `ModuleEntry::Def`: add `fn_ptr: Option<*const u8>`, remove `platform_fn_ptr`
- Reshape consumer-side `CranelispError` variants to use `ErrorLocation`

Single-stream because the `CranelispError` reshape touches every consumer crate's construction sites; parallelism would cause merge churn. Wave 0 must complete before any Wave 2 consumer work begins.

### Wave 1 — `/qa` sprint-wide bedrock (~1d, parallel with Wave 0 if /qa starts on test plan only)

- 35 failing-not-ignored e2e tests authored across 6 new files + 2 extensions (per /qa slice §5)
- Per-crate `cargo public-api` baselines (8 crates including new primitives + intrinsics)
- Mid-sprint check moved to end-of-Wave-3 (D43 source migration substantially complete)

### Wave 2 — D43 crate scaffolding + type relocations (~3d)

- `cranelisp-primitives` + `cranelisp-intrinsics` crate skeletons; workspace `Cargo.toml` member adds
- FIXME 0100 Phase 1: types → typecheck (CheckResult, CheckError, FormCheckResult, CheckPass, CheckState, TypeCheckEnv, ModuleCheckAccumulator, ReplSnapshot)
- FIXME 0100 Phase 2: types → backend (CompilationError, GotEvent/Tag/Provenance/Observer)
- FIXME 0098 Phase 2: ResolutionGap consumer wiring (frontend `expand` migration begins)
- FIXME 0104 platform-side: `PlatformError` adoption

### Wave 3a — Critical-path triad + structural migrations (~5–6d)

Parallel D/D/R cycles across crate surfaces. **Critical-path triad lands here as same-wave sub-batch** per /arch Phase 2 recommendation #1:
- frontend: `build_form -> Vec<ParsedEntry>` (FIXME 0156); `expand` migration completes (FIXME 0098 Phase 2)
- typecheck: `check_form` shape-pivot — pure function returning `Vec<(Symbol, ModuleEntry)>` (FIXMEs 0156 + 0160)
- int: `process_form` shape-pivot — parse → check → insert dispatch (FIXMEs 0098 Phase 4 + 0156 consumer)
- Plus int Wave A+B+C: physical relocations + Cargo/import sweep + SharedState extraction (FIXME 0153 Interpretation A)
- D43 source migrations: runtime → primitives + intrinsics
- FIXME 0107 non_exhaustive (single-attribute add)

### Wave 3b — Receive-side commitments + `Code` slim (~5–7d)

- int Wave D–I receive-side: D41 per-symbol JIT, D39 source-store collapse, D42 PlatformError adoption, observability bundle, ParsedEntry consumer end-to-end
- **`Code` variants slim** (`/dev (backend)` ~30–40 sites): `Code::Jit { jit, ptr }` → `Code::Jit(Arc<Jit>)`; ptr migrates to `fn_ptr` field (per fn_ptr unification)
- FIXME 0099: GotObserver (backend authoring + int consumer)
- FIXME 0103: IoObserver (cranelisp-intrinsics host) + trace.rs/io_trace.rs → int
- FIXME 0108: backend `display.rs` → int

### Wave 4 — Cleanup + `cranelisp-runtime` retirement (~2–3d)

- backend trait-knowledge deletions (D43 enabling)
- `cranelisp-runtime` retires from workspace (D43 close)
- stdlib trait-impl audit (D43 Phase 4 — highest-risk reshape, observability bandwidth reserved)
- Opportunistic FIXMEs: 0096 (stale doc archival), 0102 (runtime CLAUDE.md — closes-by-vacuum on retirement), 0106 (PlatformRegistry archive)
- Final `cargo public-api` reconciliation per /qa baseline ledger

### Wave 5 — Phase 7 close (~0.5d)

Outcome authoring, ROADMAP update, archive on user approval.

### Sizing summary

**~19–23 working days** across waves. Calendar with parallelism roughly 3.5 weeks. Critical path: Wave 0 (sequential) → Wave 3a triad (parallel) → Wave 3b receive-side → Wave 4 retirement.

## Notes

- Phase 6 waived by user direction. Phase 5 closes directly into Phase 7.
- 21 baseline-failing tests from S64 close carry forward; sprint must not regress them.
- Pre-existing failures (11 sketch_port + 2 v4_platform) continue to be excluded from pass-rate counting.
- **D43 reshape budget**: `/qa` slice §2.3 pre-classifies ~13–23 expected test reshapes within a 47-test envelope (D43 Phase 4 stdlib trait-impl audit alone budgets up to 10–15 conformance tests per author estimate). 95% gate calibration: 932 / 953 baseline + 26-test headroom.
- **Critical path**: `process_form` shape-pivot triad (frontend row 7 + typecheck row 1 + int row 3) — same-wave landing required per /arch recommendation #1.
- **Int load**: 2-wave-equivalent (~10–13 days) per /arch recommendation #2; not parallelisable away.
- **Observability bandwidth**: `CRANELISP_RC_TRACE` + `CRANELISP_CODEGEN_TRACE` reserved for D43 Phase 4 stdlib audit (highest-risk reshape per /arch recommendation #4).

### Phase 3 FIXME resolutions (user-arbitrated, 2026-05-08)

**Guiding principle for resolutions**: minimum work to realise the facade, minimal test loss. Adoption sprint is the forcing function for facade quality — don't duck structural choices to save days.

- **FIXME 0153** (int SharedState vs decomposition sequencing) — **Resolution: Interpretation A.** SharedState extraction lands in S66 as prerequisite shape pivot, separate from file-level decomposition. FIXME 0109 carries forward unchanged (decomposition still S67+). Wave C of int slice executes per current row design. Decision 38 invariant 16 (per-symbol mutability) lands receive-side this sprint.
- **FIXME 0154** (backend LinkerError variants) — **Resolution: accept slice's 2-variant proposal.** `#[non_exhaustive] enum LinkerError { SymbolNotFound { name: LinkerSymbol }, RelocationFailed { name: LinkerSymbol, cause: String } }`. Additional variants added as evidence accrues; can re-shape during /review triggered by future FIXME.
- **FIXME 0156** (frontend `build_ast` form-vocabulary) — **Resolution: deferred-creation shape with `ParsedEntry` transient.** Frontend exposes `pub fn build_form(sexp: &Sexp) -> Result<Vec<ParsedEntry>, CranelispError>`. `ParsedEntry` is a new transient type in `cranelisp-types` carrying parse-time-only fields. It NEVER lands in `SymbolTable`. Lifecycle: parse → ParsedEntry → check_form → ModuleEntry → SymbolTable.insert. SymbolTable invariant: "if it's in the table, it's checked." `SymbolTable::get` / `::insert` API unchanged (137 lookup sites untouched). `DefmacroInfo` moves from `cranelisp-frontend` to `cranelisp-types`; `parse_defmacro` becomes private inside frontend's build_form dispatcher; `FormKind::Defmacro` merges into `Regular`.
- **FIXME 0160** (typecheck `check_form` post-Gap state contract) — **Resolution falls out of 0156: structural Option B.** `check_form` becomes pure: `(parsed: ParsedEntry, ...) -> Result<Vec<(Symbol, ModuleEntry<C>)>, CheckError>`. Returns Ok with entries to insert; returns Err on Gap with nothing partial written (the orchestrator hasn't called insert yet). Snapshot-restore is structural, not behavioral — nothing to roll back. Closes Q2 escalation.
- **FIXME 0159** (primitives synthetic-module seeding) — **Resolution: static `LazyLock<SymbolTable>` in `cranelisp-primitives`.** No session-init seeding step; no special-case dispatch. The static lives in `cranelisp-primitives` (revises slice row 10 — "leaf purity: no helper" was aesthetic, didn't yield isolation). cranelisp-primitives gains an acyclic dep on cranelisp-types. Extern fns become `pub(crate)`; the only public surface is `pub static PRIMITIVES_TABLE: LazyLock<SymbolTable>`. Both int (session init: `tables.insert(ModuleFullPath::primitives(), PRIMITIVES_TABLE.clone())`) and backend (`register_intrinsics` walks the same static) read from it — single source of truth. Decoupled from compilation session lifecycle; never invalidates, never rebuilds. **GOT side**: stays at backend's existing `register_intrinsics` for S66; follow-up FIXME (filed during /arch Wave B) for post-S66 evaluation of static-GOT refinement.
- **FIXME 0156 + 0159 revision (2026-05-09)**: **fn_ptr unification.** Wave B's per-origin field proliferation (`platform_fn_ptr` + the proposed `primitive_fn_ptr`) replaced by a single unified `fn_ptr: Option<*const u8>` on `ModuleEntry::Def`. `Code` variants slim to lifecycle ownership only: `Code::Jit(Arc<Jit>)` / `Code::Linker(Arc<Linker>)` — ptr embedded in variants moves to `fn_ptr`. Origin encoded by `kind: DefKind`, not by which optional field is set. Cycle stays avoided (primitives use `SymbolTable<()>`; never name `Code`). Decision 31 Scenario 2 preserved (Arc<Jit> still owned by `Code::Jit` variant). Read-site simplification: codegen / IO trampoline / indirect-call all read `entry.fn_ptr` directly. Net cost ~+2d (mostly `/dev (backend)` Wave 3 — slim `Code::Jit { jit, ptr }` construction sites + match patterns; ~30–40 sites). Decisions 41 + 31 amended in `e67c1a6`. FIXME 0162 filed for `interfaces.md` narrative-sweep follow-up (next /arch invocation).
- **FIXME 0156 + 0160 revision (2026-05-10)**: **fn_ptr ROLLBACK.** Wave 0 implementation surfaced that the `fn_ptr` field duplicated `GotTable[got_slot]` — same address, two storage locations. Rollback (`1dc57ae`): `fn_ptr` field deleted; `got_slot: Option<usize>` becomes the canonical address handle for callable entries; `symbol_table.got().load(slot)` is the single read pattern. Comment at module.rs:430–434 rewritten — primitives DO get GOT slots (operator-as-value path requires it); `None` only for non-callable entries (special forms, type defs, trait decls, macros, overloaded bases, constrained-fn templates). Read sites in `src/worker.rs` migrated. Construction sites now use `got().store_slot(slot, ptr)`. Decisions 31, 35, 41 amended for the rollback (`4e1802a`); per-crate doc drift filed as FIXMEs 0162 (int) + 0163 (backend) + 0164 (typecheck) for downstream resolution.
- **FIXME 0156 + 0160 revision (2026-05-10, Wave 3a precondition)**: **cluster-atomic typecheck shape.** Wave 3a /dev attempt surfaced spec/design mismatch — single pure `check_form` cannot satisfy spec §5.13.1's two-pass mandate (Pass 1 Registration + Pass 2 Checking for forward refs / mutual recursion). Resolution per Decision 44 (`5d43041`): `check_form` splits into `check_form_signatures` + `check_form_body` (both pure; Principle 2 narrow interfaces over Pass-enum dispatch). Orchestrator owns transient staging `SymbolTable`; `View<'a, C, L>::union(staging, live)` newtype in cranelisp-types provides combined-read access; cluster-atomic commit (drain staging into live) on Pass-2 success or no-commit on any failure. REPL semantics per /spec FIXME 0165 resolution (`cfca8ac`): REPL input is a single top-level form; mutual recursion via `(begin form₁ … formN)`; spec §5.13.2 extended to non-macro defns; macro clause subsumed (option B(i)). Module-phase decls forbidden inside begin clusters; begin invalid at batch top-level. Wave 1 gate test in `tests/process_form_dispatch.rs` revises (positive begin-cluster path + negative cross-input error); /qa downstream action. Net cost +2d vs original Wave 3a triad estimate. Wave 3a re-fire unblocked.
- **Decision 44 amendment (2026-05-11) — Approach B + D1**: Wave 3a /dev re-attempt surfaced second blocker — Decision 44's invariant 2 ("Both passes are pure functions: neither mutates any SymbolTable") requires inverting 91 register-call sites + 51 SymbolTable-write accesses in typecheck (multi-week refactor). User-arbitrated resolution: **Approach B** — empty staging SymbolTable owned by orchestrator; reads via View::union(staging, live); writes via existing `current_symbol_table_mut` API redirected to staging via a `ClusterContext` enum at typecheck's accessor layer. Decision 44 invariant 2 amended in `413bf9e`. Cost: ~3.75d total Wave 3a. **Subsequently superseded by 2026-05-12 finding** (see below).
- **Module locality vertical (2026-05-12) — Wave 3a re-fire blocker #3 → solve in S66**: Wave 3a /dev re-re-attempt audit revealed Approach B insufficient: 40+ direct `self.modules.X` accesses bypass per-module accessors (12+ short-name searches that iterate every module; 4 impl-resolution sites; 11+ direct cross-module gets; 6 direct mutating writes). The agent argued for Approach A (clone-based staging); user re-arbitrated with sharper principle: **cross-module short-name searches should not exist; impl resolution traverses import chains; bulk reads (`all_type_defs` etc.) are current-module-only**. The audit's "40+ direct accesses" are NOT constraints to design around — they're anti-patterns to fix. User direction: **solve in S66**, do not defer. **Three architectural questions surface** that gate Wave 3a triad: Q1 (TraitImpl storage placement: writer's module vs trait's home vs type's home — non-local-update problem); Q2 (typecheck module-locality enforcement: short-name lookups via current_module + Import-following only; impl resolution via bounded import-chain walks); Q3 (import-chain traversal mechanism for impl visibility: direct vs transitive). Sprint envelope expands by ~6–9d (architectural rounds + locality refactor + triad). FIXMEs filed: 0168 → /arch (Q1 + Q2), 0169 → /spec (Q3). Wave 3a triad land downstream of these resolutions + locality refactor.

### Wave 3a-α structural notes (2026-05-12)

α landed with three structural notes flagged for round-by-round user discussion before Wave 3a-β fires. Resolutions accumulate here.

- **Note 1 — Implicit prelude injection in `imports` (FIXME 0034 — RESOLVED).** User-arbitrated answer (b): the implicit prelude does NOT appear in `SymbolTable.imports`. `imports` is the user-authored form-level record (drives regeneration); per-symbol `ModuleEntry::Import` / `Reexport` entries are the resolved-per-name record. The two stores record different facets at different granularities; both contribute valid edges to the import graph; consumers that need the **effective** import set walk both. α's `transitive_import_closure` (commit `ab068e2`) embodies the pattern. Path A (storage in `imports` + filter at regen) was rejected: shape-match filter cannot distinguish synthetic from user-authored `(import [prelude [*]])`. **Permanent landing**: the substance lives in `design/typecheck/ast-annotation.md` §11.3 item 4 (existing canonical home for `SymbolTable.imports` invariants) + a doc-comment cross-ref on `crates/cranelisp-types/src/module.rs`. No new Principle, no new Decision — §11.3 already articulates the one-way coherence rule and held the open question; flipping the bullet to resolved is the right edit. **FIXMEs filed**: 0170 → /typecheck (flip §11.3 + module.rs doc-comment); 0171 → /int (formal close of 0034, depends on 0170). 0034 amended with `status: resolved` + full Resolution block in-sprint as a transient bridge; deletes when 0171 fires.
- **FIXME 0155** (platform facade text — `load_manifest` / `parse_type_sig` placement) — **Resolution: reduce facade.** /arch Wave B tightens `facades/platform.md` to mark both as platform-internal `pub(crate)` helpers (called by platform's own `manifest_to_descriptors` entry). int never calls them directly. One-paragraph facade edit; no source impact.
- **FIXME 0158** (primitives `cargo public-api` versioning policy) — **Resolution: dissolves once 0159 lands.** cranelisp-primitives' Rust public API is one static declaration (`PRIMITIVES_TABLE`); cargo-public-api baseline is one line, stable across primitive churn. Semantic surface (which primitives exist + their signatures) is governed by spec conformance tests, NOT cargo-public-api. Two surfaces, two tools, no overlap. Standard /qa baseline-ownership process applies.

### Phase 3 SCOPE expansion (per FIXME 0156 resolution)

The deferred-creation shape adds **~3.75 days** to S66:

| Skill | Added work | Days |
|---|---|---|
| `/arch` Wave 0 | Author `ParsedEntry` in cranelisp-types; move `DefmacroInfo` to cranelisp-types | +1 |
| `/dev (frontend)` | `build_form -> Vec<ParsedEntry>`; private dispatch | +0.5 |
| `/dev (typecheck)` | `check_form` consumes `ParsedEntry`, returns `Vec<(Symbol, ModuleEntry)>`; gap returns leave nothing partial | +1 |
| `/dev (int)` | parse → check → insert pipeline; classify_form simplification (Defmacro merges into Regular) | +1 |
| `/qa` | check_form atomicity tests + ParsedEntry round-trip | +0.25 |

`/arch` Wave 0 also expands +0.5d for `ErrorLocation` authoring (Phase 2 verdict misclassified as "verify"). Total Wave 0 expansion: +1.5d.

User signed off on scope expansion 2026-05-08.

## Outcome (Phase 7)

### Delivered
- {filled at close}

### Deferred (with rationale)
- {filled at close}

### Findings
- {filled at close}
