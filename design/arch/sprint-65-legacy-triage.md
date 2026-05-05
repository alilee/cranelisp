# Sprint 65 Phase 2 — `design/arch/legacy/` triage

**Status.** Triage executed by `/arch` 2026-05-05, in-session. Pairs with `design/arch/sprint-65-phase-2-review.md` (the main Phase 2 review, which excluded `legacy/` from its brief).

**Scope.** Disposition every doc in `design/arch/legacy/` (and `design/arch/legacy/decisions/`) per `design/arch/CLAUDE.md` § "Sorting buckets" — promote / FIXME / archive — and surface findings the user must decide on before Phase 3 advances.

---

## Per-doc disposition

| File | Disposition | Rationale | Action taken |
|---|---|---|---|
| `legacy/substance-scoping.md` | **Keep in `legacy/`** | Cited by Decision 43 as the substantive analysis; §1.7 is the source the Decision distils from. Other §-sections also remain referenced from filed FIXMEs (0098/0099/0103/0104/0011 cite specific § entries). Promoting to canonical inflates surface; archiving severs Decision-43 traceability. Stays as the historical analysis it is. | None. |
| `legacy/substance-action-plan.md` | **Keep in `legacy/`** | Step 4 (per-crate implementation slices) per the doc's "Progress" header is still pending. Doc remains live until Step 4 closes. See finding F1 below. | None. |
| `legacy/fqtypename.md` | **Keep in `legacy/`** | Active migration commitment; carried as aspirational in `facades/types.md` (FQTypeName appears in 11 facade lines). User memory `memory/project_fqtypename_priority.md` flags as next-up after test stabilisation. See finding F2 below. | None. |
| `legacy/reconciliation-plan.md` | **Archive** | Sprint 63 close procedural reconciliation plan. Steps 1a/1b/1c executed and committed (`3316599`, `19124fa`, `9c33e0e`, `de98bf0`, `238a631`, `3ccbb44`, `56c75a8`, `c49d094`, `f79af54`, `1882569`, `1c8d519`, `3247647`). Substance commitments landed; subordinate-doc lifecycle pivoted to per-crate ownership per substance-scoping §2.14. Plan superseded by execution. | `git mv` to `archive/`; CLAUDE.md Archive index updated. |
| `legacy/roadmap.md` | **Archive** | Pre-S63 ring-by-ring architectural roadmap. Delivery now tracked by `sprints/ROADMAP.md`; per-crate intent now lives in `design/{crate}/{crate}.md`; ring axis itself is being retired (FIXME 0114). Doc is purely historical. | `git mv` to `archive/`; CLAUDE.md Archive index updated. |
| `legacy/pipeline-v4.md` | **Archive** | v4 scheduler-driven pipeline design. Per `pipeline-v4-roadmap.md` itself: "v4 scheduler-driven pipeline is the only pipeline." Lessons baked into Decisions 21–27, 31, 36–41 and per-crate design docs. | `git mv` to `archive/`; CLAUDE.md Archive index updated. |
| `legacy/pipeline-v4-roadmap.md` | **Archive** | Roadmap companion to `pipeline-v4.md`; the nine "structural gaps" it tracked have all closed via S58–S64 work and the Sprint-63 substance commitments (Decisions 38–42). | `git mv` to `archive/`; CLAUDE.md Archive index updated. |
| `legacy/concurrent-pipeline.md` | **Archive** | Scheduler design companion to `pipeline-v4.md`. Per-crate concurrency design now in `design/int/concurrency*.md`. | `git mv` to `archive/`; CLAUDE.md Archive index updated. |
| `legacy/substance-scoping-brief.md` | **Archive** | Input brief for the substance-scoping pass. Pass executed; output → `substance-scoping.md` → Decisions 40–43. Brief is purely historical. | `git mv` to `archive/`; CLAUDE.md Archive index updated. |
| `legacy/macro-resolver.md` | **Archive** | Sprint 50 macro-resolver design. Decision 8 (`MacroExpander` trait) retracted (per `legacy/decisions/0008-*.md`); FIXME 0098 explicitly drops the `MacroResolver` trait in favour of direct `&SymbolTables<C, L>` lookup. Design fully superseded; the parallel `design/frontend/macro-resolver-trait.md` remains as frontend-specific context. | `git mv` to `archive/`; CLAUDE.md Archive index updated. |
| `legacy/traitimpl-symbol-table.md` | **Archive** | Sprint 51 ImplRegistry-deletion design. Verified landed in source: `ModuleEntry::TraitImpl` exists in `crates/cranelisp-types/src/module.rs:309`; `ImplRegistry` removed per source comments at `crates/cranelisp-typecheck/src/checker.rs` and `traits.rs`. Design fully embodied; archive retains for narrative. | `git mv` to `archive/`; CLAUDE.md Archive index updated. |
| `legacy/sequence-diagram/` | **Archive** | Pre-S63 v4-target diagrams (`v4-target.{mmd,png,svg}`). Superseded by `design/arch/sequences/`. | `git mv` to `archive/`; CLAUDE.md Archive index updated. |
| `legacy/decisions/0001-…0039-*` | **Keep in `legacy/decisions/`** (status quo) | These are the "fully-embodied" Decisions per the Decisions index in `CLAUDE.md`. Already correctly homed; no action this triage. | None. |

**Counts.** 12 files dispositioned + 1 directory:
- Promoted to canonical: 0
- Filed as new FIXME / Decision: 1 file → spawns 1 Decision (0043) + 1 FIXME (0150)
- Archived: 9 files + 1 directory (`reconciliation-plan`, `roadmap`, `pipeline-v4`, `pipeline-v4-roadmap`, `concurrent-pipeline`, `substance-scoping-brief`, `macro-resolver`, `traitimpl-symbol-table`, `sequence-diagram/`)
- Kept in `legacy/`: 3 files (`substance-scoping`, `substance-action-plan`, `fqtypename`) + `legacy/decisions/`

---

## Newly filed artefacts

### Decision 0043

`design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md`

- **Subject.** `cranelisp-runtime` splits into `cranelisp-primitives` (language-level callable surface) + `cranelisp-intrinsics` (backend-emitted-call targets); backend has no trait knowledge; backend's substitution table is name-keyed (`Symbol`) only.
- **Retracts.** Decision 14 (backend recognises `(TraitName, Symbol, TypeName) → PrimitiveOp` map). 14 was already deleted from the register in commit `754d525`; Decision 43 is the formal replacement direction. CLAUDE.md Decisions-index legacy line updated to note the retraction-by-43 cross-reference.
- **Reframes.** Decision 15 (Ring 0–1 `BuiltinFn` coexists with Ring 2 `TraitMethod`). 15 was likewise deleted in `754d525`; the typecheck-level dual path is correct, the backend-level dual path is not — Decision 43 reframes the correct half explicitly.
- **Status.** `pre-implementation`. Tracked by FIXME 0150.

### FIXME 0150

`design/arch/fixmes/0150-runtime-split-primitives-intrinsics.md`

- **Target.** `/dev` (multi-crate). Coordinates with FIXME 0103 (trace/io_trace runtime → int relocation) — they share the IoObserver registration site.
- **Phasing.** 5 phases: (1) crate skeletons + facade placeholders, (2) source moves runtime → primitives + intrinsics, (3) backend trait-knowledge map deletions + `operators.rs` rename, (4) duplicate `cranelisp_op_*` deletions + stdlib trait-impl audit, (5) runtime crate retires + BC §4 → §4a + §4b, facade `runtime.md` → `primitives.md` + `intrinsics.md`.
- **Sequencing flexibility.** Not a blocker for current S65 facade-adoption scope; can run as S65 Wave 0 (delays facade adoption), S66 (after S65 stabilises), or a dedicated multi-crate sprint. Decision deferred to `/sprint` at next sprint-plan boundary. See finding F4 below.

### CLAUDE.md updates

- Decisions index: 0043 entry added; legacy-decisions line annotated with retracted-by-43 / reframed-by-43 + commit `754d525`.
- Archive section: 7 new entries (the 8 archived files + the sequence-diagram directory) with one-line provenance.

---

## Findings flagged for user decision

### F1 — Step 4 implementation slices were never written

**Status: missing.** `substance-action-plan.md` Step 4 (table at line 311) commits each `/design (crate)` and `/qa` to author a "first-sprint implementation slice" ready for `/sprint` to schedule into Sprint 65. Searched `design/{crate}/` and `tests/plan/` for any "implementation slice" / "S65 plan" / "sprint-65" / "first-sprint" docs: **zero matches**.

Inspected the per-crate `design/{crate}/{crate}.md` files: all six (frontend, typecheck, backend, runtime, platform, int) **do** cite the new Decisions (40, 41, 42 — verified by grep). So Step 2 (master-design-doc refresh) substantively landed. But Step 4 (the bridge between Step 2 + Step 3 outputs and Sprint 65's actual wave plan) did not.

**Implication.** Current S65 scope (the 7 cross-crate FIXMEs 0098/0099/0100/0103/0104/0107/0108 listed in `SPRINT.md`) was assembled from FIXME inventory, not from the Step-4 per-skill implementation-slice plans. Whether the two converge — i.e., whether the FIXME-driven scope captures everything Step 4 would have surfaced — is **unverified**. The risk is silent divergence: Step 4's plans would have surfaced cross-skill dependencies (e.g., `/dev (runtime)` exposing IoObserver before `/dev (int)` consumes it), test-infrastructure-uplift items, or scope Step 4 would have de-risked.

**Decision needed.** Three options:
- (a) **Accept the FIXME-driven scope.** Trust that the 7 FIXMEs cover what matters; Step 4 was a process artefact whose value got captured implicitly via the FIXME triage. No action.
- (b) **Author Step 4 retrospectively before S65 advances.** Each `/design (crate)` + `/qa` writes the implementation-slice plan now. Delays Phase 3 advance; surfaces hidden cross-skill dependencies before code moves.
- (c) **Surface to `/sprint` as a Phase 2 finding; let `/sprint` decide whether to retro Step 4 inside the wave plan or not.**

`/arch` recommends **(c)** — the substantive gap is not "Step 4 missing" per se but "scope-source disagreement Step 4 would have arbitrated"; the decision belongs to `/sprint` not `/arch`.

### F2 — FQTypeName: memory-flag vs S65-deferral conflict

**Status: conflict.**

- `memory/project_fqtypename_priority.md` flags FQTypeName migration as **"next-up after test stabilisation, NOT indefinitely deferred"**.
- `sprints/SPRINT.md:47` defers it to `"future"` with rationale **"Aspirational facade entry — accepted as committed-but-unimplemented this sprint"**.
- `sprints/ROADMAP.md:152` lists FQTypeName as one of several Sprint-65+ candidates.
- `facades/types.md` carries it on 11 lines as the resolved-position type for ADTs etc. — i.e., the facade is bound to it; source has not caught up.

The "test stabilisation" predicate the memory entry refers to is plausibly satisfied — S64 closed at 932 passing / 21 failing / 6 skipped, which is the baseline S65 freezes. But there's no FIXME tracking FQTypeName implementation; it lives only as facade aspiration + roadmap candidate.

**Decision needed.** Two options:
- (a) **File a FIXME now** (`design/arch/fixmes/0151-types-fqtypename-implementation.md`, `target: /dev`) to close the visibility gap. Decision on scheduling stays with `/sprint`; the FIXME just makes the commitment trackable.
- (b) **Confirm "post-harvest-arc" deferral** is the active commitment, supersedes the memory flag, and the memory flag should update.

`/arch` recommends **(a)** — the memory flag has higher specificity than the roadmap entry, and a tracked FIXME is cheap; scheduling can stay deferred. Did not file in this triage because the call belongs to the user, not to `/arch` reading the memory file.

### F3 — §2.8 / §2.9 / §2.14 deferred-FIXME landing: VERIFIED

`substance-action-plan.md:30–31` says §2.8, §2.9, §2.14 "were filed as deferred FIXMEs alongside the S64 commit". Verified:

- **§2.8** (Backend GOT-slot population log): captured by **FIXME 0099** (`/dev` GOT observer implementation). Note: FIXME 0099 supersedes the §2.8 filing template — `/arch` Phase 1 of FIXME 0099 chose option B (ring buffer + observer callback) over the §2.8 template's option A (Introspection extension). The filing template in §2.8 was superseded by Decision 40's IoObserver pattern; FIXME 0099 carries that decision forward. **Captured correctly, just under a different number than §2.8 anticipated.**
- **§2.9** (Effect-node scheduling class side-channel correlation): captured by **FIXME 0011** (with related FIXMEs 0038, 0103, 0118, 0128 covering adjacent slices). 0011 is targeted at `/backend`; §2.9's filing template targeted `/int` (correlation logic). The `/backend` framing is appropriate for the in-band-vs-side-channel decision; the int-side correlation work re-files at implementation time.
- **§2.14** (Int observability strategy formalisation): explicitly NOT a FIXME by §2.14's own resolution ("no new FIXME is filed"); deferred to per-crate rebuild wave. This is correctly handled by `design/int/observability.md` ownership.

**No missing FIXMEs.** Surface as an explicit verified-clean finding for the Phase 2 record.

### F4 — Decision 43 / FIXME 0150 scope choice for S65

The runtime split is large: workspace structure, two BCs, three Decisions, multiple crates, stdlib audit. Three options for S65:

- (a) **Pull §1.7 into S65 as Wave 0** — S65 starts with the runtime split, then proceeds to facade adoption. Delays facade-adoption work by ~1 wave's effort; ensures S65 closes with the corrected BC-§4 model rather than baking facade adoption against a known-stale BC.
- (b) **Defer §1.7 to S66 or later** — S65 proceeds as currently scoped. Facade adoption against `cranelisp-runtime` happens; the runtime split happens later; some of S65's facade work re-touches when the split lands. Throwaway risk: how much of `facades/runtime.md` adoption survives the split?
- (c) **Accept throwaway** — same as (b) but with explicit recognition that the runtime-side facade adoption is interim; document the throwaway scope in the S65 close note.

`/arch` recommends **(b) with re-scope review**. Substance-scoping §1.7's "Sequencing" already declared this a Sprint-65+ wave with its own action plan, "too big to fit alongside the other §1 substance commitments". The current S65 scope respects that. The throwaway question deserves attention but isn't catastrophic: `facades/runtime.md` post-split becomes `facades/primitives.md` + `facades/intrinsics.md`, and the categories were already conceptually distinct in the runtime facade — the split is more re-homing than re-authoring. The reach-around catalogue and `cargo public-api` baselines re-baseline naturally when the split lands.

If the user prefers (a), S65's wave plan needs Decision 43's implementation slice authored as Wave 0, the 7 in-scope FIXMEs slip to Wave 1+, and the 95% gate may need re-calibration (the split touches stdlib trait impls and may break tests during transit).

---

## Recommended S65 re-scope

**No re-scope required**, conditional on user accepting:

1. **F1: option (c)** — surface Step-4 gap to `/sprint` as a finding; `/sprint` decides whether to retro Step 4 inside the wave plan.
2. **F2: option (a)** — file a tracking FIXME for FQTypeName so the memory-flagged commitment is visible. Scheduling stays deferred.
3. **F3:** verified clean.
4. **F4: option (b)** — runtime split (FIXME 0150) defers to S66 or a dedicated sprint; current S65 scope advances to Phase 3 unchanged.

If user prefers F4 option (a), S65 needs Wave 0 inserted for FIXME 0150 implementation, and `/sprint` re-plans accordingly. That's a substantial sprint reshape — `/sprint` redrafts wave structure, baseline gates re-calibrate.

---

## Cross-references

- `design/arch/sprint-65-phase-2-review.md` — main Phase 2 review (predates this triage)
- `design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md` — newly filed
- `design/arch/fixmes/0150-runtime-split-primitives-intrinsics.md` — newly filed
- `design/arch/legacy/substance-scoping.md` §1.7 — substantive analysis Decision 43 distils from
- `design/arch/legacy/substance-action-plan.md` — Step 4 commitment (finding F1)
- `memory/project_fqtypename_priority.md` — FQTypeName memory flag (finding F2)
- `sprints/SPRINT.md` line 118 — user note 2026-05-06 surfacing the gap that triggered this triage
