# Sprint 103: Increment II — the write path (uniqueness → mutable-borrow → reuse)

**Status**: PHASE 2 ARCH REVIEW — COMPLETE (exit-gate PASS-with-revisions); ready for Phase 3

**Goal**: Land ownership-inference increment II's write path — the two designed-ready mechanisms (reuse tokens + R5 value-flattening) on the settled increment-I read-path spine — resting on the typecheck-drain foundation and the /arch write-path rulings, while draining the T1 full cure (now unblocked) and the consciously-dispositioned /dev unit-tier drain set.

## Scope

Three blocks, priority-ordered. Block B (the write path) is the centerpiece and the Phase-H spine; Block A front-loads the /arch + design rulings that gate it; Block C rides wherever a crate is already open.

### Block A — the /arch + design rulings, co-resolved in Phase 3 (NOT a hard gate on B2/B3 — Phase-2 ruling)

**Phase-2 correction**: these are **not** hard preconditions blocking the write-path mechanisms. B2/B3 (reuse tokens + R5) consume the S102-landed `ModeSummary`/`result_unique` carriers and the B1 foundation — none of them reads the A-FIXMEs' surfaces. What genuinely gates B2/B3 is **B1** (the typecheck-drain foundation). These A-items co-resolve inside Phase 3 alongside the per-crate /design plans.

1. **FIXME 0526** (/arch → content edits /backend) — §3.3 producer-side / interprocedural projection-elision reframe. **Phase-2 direction ruling**: consumer-driven elision is the increment-I *terminal* state (settled, I-G1 100%); the producer-side / escaping-projection model **promotes to the increment-II design**, gated by the uniqueness/confinement proof Q4 supplies. The §3.3 prose re-frame is a /backend doc edit co-landing with the backend increment-II design pass. **Kept open → Phase-3 backend design fire.**
2. **FIXME 0521** (/arch) — ResultMode multi-param may-alias ⊤ element. **Phase-2 ruling**: a soundness precondition *only if* a consumer reads the `AliasOf` **index**. The committed floor's discriminator is the dynamic rc==1 check + the `result_unique` **bool** — neither reads `AliasOf(k)`; 0520's lowest-index representative is sound for every live consumer. **Phase-3 conditional**: /design(typecheck) lands the ⊤ element (`AliasOfAny`, monotone-widening) in the B1 carrier change-set + schema bump *iff* the static-uniqueness subset introduces an index-reader; else deferred until the reader arrives.
3. **FIXME 0515** — S78 entry-module prelude silent-shadow. **Phase-2 RESOLVED by /arch**: re-targeted `/arch → /int` (doc-coherence re-anchor of `design/int/s78-entry-module.md §2`, not a memory-model ruling; the normative question is already answered — /spec enacted it, FIXME 0514 carries the impl). No /arch ruling owed. **Now blocks the Block C1 /int wave** (T1 full cure opens `design/int/`), not Block A.
4. **Design sizing — region arena** (/design backend, §4.4): confirmed CLEAN as a deferred rider (see §"Region-arena deferral"). Phase-3 only sizes whether the (a)-allocator co-design is implementation-ready enough to pull back before the B3 seam; default is deferred to a follow-on.
5. **FIXME 0506** (/design backend) — oracle-capture spec corrections. **FIXME 0507** (/design src/) — T1 full-cure trigger + 0491-exclusion design holes (feeds Block C's T1 full cure).

### Block B — increment II write path (the Phase-H spine; `design/arch/ownership-inference.md` §7, backend §6/§4.4/§6.3, qa plan §6 + §2 gates II-G1–G4)

1. **Typecheck foundation** — the drain quartet the write-path pass rests on, actioned in the /typecheck impl window increment II opens:
   - **0509** generalization-ordering resettle debt · **0510** `neq`/string has no primitive entry to carry declared facts · **0511** pass5 session-memo needs a threaded field · **0513** qualified-lookup prefers phantom-child gap over loaded absolute module.
   - Then the **write-path queries** (spine §7 Q4): static-uniqueness proof subset (`result_unique` chains, §2.1) + the general **dynamic rc==1** discriminator carried to the backend.
2. **Reuse tokens** (backend §6 — drop-guided Perceus reuse generalising the inline-COW precedent): function-local SSA maybe-null token, **never on the ABI** (spine §3.5); per-call entry check (copy-once-then-in-place); static proof (typecheck §7.2) *elides* the check but never replaces the mechanism. Delivers gate **II-G4** (reuse ≥50%, median ≤2× serial).
3. **R5 value-representation flattening** (backend §6.3 / spine §6.3 — `HeapCategory::Value` one-word flattening for Copy-eligible-within-the-tier concrete types). **The predicate is an /arch-authored `cranelisp-types` carrier change-set** (`value_layout(ty) -> Option<ValueLayout>` + `VALUE_LAYOUT_MAX_WORDS=1` in `heap.rs`), single-sourced (soundness-coupled: typecheck's mode classifier + backend's `HeapCategory::Value` arm both consume it — a `Copy`-moded param the backend didn't flatten is a UAF), co-scheduled with /design(typecheck) + /design(backend), carrying the `public-api.txt`/`interfaces.md`/BC §7 + `CACHE_SCHEMA_VERSION` 12→13 cascade. Lands **in the B3 implementing change-set, never ahead of the R5 mechanism design** (Principle-8 speculative-interface discipline). Delivers gate **II-G1** via the **F2v single-ctor witness fixture**.
4. **Region arena** (backend §4.4 — M7 shape, dynamic sizes, NoEscape) — **conditional on Block A4**; deferred to a follow-on if the allocator co-design isn't implementation-ready. Not required for II-G1–G4.
5. **H3 owed-signal** — `h3_rc_stats_reports_per_extern_adaptation_pairs` (the sole S102 intentional RED, the inc-II owed-signal guard) flips green with the per-extern-adaptation RC_STATS sibling-expansion (L-D5).

**Acceptance**: qa gates **II-G1–G4** (`tests/plan/s100-ownership-verification.md §2`): F2v rc_inc <1% + N-worker wall < serial (the **first parallel-must-pay gate**); F4 reuse ≥50%, median ≤2× serial. Differential oracle (`CRANELISP_NO_OWNERSHIP`) byte-identical off throughout.

### Block C — T1 full cure + the drain set

1. **T1 full cure** (0507 design → /int impl, `session-transaction.md` §10): end-of-turn-sequenced module reload (~3 CSes + flipping the two coherent-stale pins). S102's A2/A4 fixes (regen fidelity, 0489 floor, D3/0487 env) were the hard preconditions — **now landed**, so this is ready. The S102 print stays as the shipped mitigation until this replaces it.
2. **/dev unit-tier drain set** — consciously admit/defer per the drain-all rule (each rides only if its crate is opened by Block B):
   - **0495** backend `tests.rs` split + thin-submodule drain — **IN** (backend open for reuse-tokens + R5).
   - **0498** types marshal-drift guard + zero-modules — **IN** (types carrier extends for the R5 predicate + write-path fields).
   - **0496** src/ unit-tier (lifecycle.rs 1,918 LOC / 0 tests) — **IN** (src/ open for the T1 full cure).
   - **0499** e2e-lane refactor (/qa) — **IN**, rides the QA-first stage head.
   - **0500** frontend rendered-diagnostic · **0501** intrinsics io-guard strand · **0502** platform declare-concurrency — **DEFER** (frontend/intrinsics/platform not opened by increment II); capacity-gated tail, re-deferred with rationale if untouched.
3. **0505** (/repl) pin-mod turn environment parity — spec-half pin; slot with the T1-full-cure design or Phase 6a.

### Sizing + close-short seam (named up front)

This is a large sprint, like its predecessors. The clean **close-short seam is after Block B3** (reuse tokens + R5 land, region arena defers): the two designed-ready mechanisms deliver the full II-G1–G4 gate set on their own; region arena is additive perf that depends on the unresolved allocator co-design. Block A rulings and the typecheck-drain foundation (B1) do NOT slip past this seam — they gate everything downstream. If capacity runs out below B3, the seam is after B1 (typecheck foundation + one mechanism), with the second mechanism carrying to S104.

### Out of scope (deferred, with rationale)

| Item | Rationale | Target |
|---|---|---|
| `--release` efficiency tier (LLVM/inkwell) + polish pins 0050/0052/0365/0416 | Gated behind the settled memory model (both increments) per the Phase-H table | after increment II settles |
| 0408 port Sudoku parallel-search showcase | Depends on the write-path wins landing + measuring (vec unlock) — a Phase-6 validation candidate once B3 lands, else deferred | this sprint's Phase 6 / --release |
| 0463 network poll-shape example | Unmet trigger (re-verified) | trigger-based |
| 0466 GOT slot-hole reclamation | User-directed indefinite deferral, trigger-based | trigger-based |
| 0500/0501/0502 /dev drains (frontend/intrinsics/platform) | Crates not opened by increment II; capacity-gated tail | rides next open of each crate |

## FIXME debt

Open set at Phase 1 (27 files). Dispositions:

| FIXME | Target | Status | S103 disposition |
|---|---|---|---|
| 0526 | /arch→/backend | open | Block A1 — NOT a hard gate (P2 correction); direction-ruled, §3.3 re-frame co-lands with Phase-3 backend inc-II design |
| 0521 | /arch | open | Block A2 — Phase-3 conditional (land ⊤ element only if a static-uniqueness index-reader arrives; else defer) |
| 0515 | /int | **RE-TARGETED P2** (/arch→/int) | No longer Block A; doc-coherence re-anchor, blocks Block C1 /int wave |
| 0506 | /design (backend) | open | Block A5 — oracle-capture spec corrections |
| 0507 | /design (src/) | open | Block A5 → feeds Block C1 (T1 full cure) |
| 0509 | /design (typecheck) | open | Block B1 — typecheck foundation |
| 0510 | /design (backend) | open | Block B1 — primitive fact entry for `neq`/string |
| 0511 | /design (typecheck) | open | Block B1 — pass5 session-memo threaded field |
| 0513 | /typecheck | open | Block B1 — qualified-lookup phantom-child gap |
| 0495 | /dev (backend) | open | Block C2 — IN (backend open) |
| 0496 | /dev (src/) | open | Block C2 — IN (src/ open for T1 full cure) |
| 0498 | /dev (types) | open | Block C2 — IN (types carrier extends) |
| 0499 | /qa | open | Block C2 — IN, QA-first stage head |
| 0500 | /dev (frontend) | open | Deferred — crate not opened; capacity-gated tail |
| 0501 | /dev (intrinsics) | open | Deferred — crate not opened; capacity-gated tail |
| 0502 | /dev (platform) | open | Deferred — crate not opened; capacity-gated tail |
| 0505 | /repl | open | Block C3 — pin-mod env-parity spec-half |
| 0474 | /qa→/backend | **STALE — cured** | P2 CONFIRMED (17/17 guards green): COW leak cured across S102 B3.1/B3.1a seam. Route deletion to /backend at a wave gate |
| 0483 | /qa→/backend | **STALE — cured** | P2 CONFIRMED (guards green): cured by 0519 lossless FQ mono-mangler. Route deletion to /backend at a wave gate |
| 0408 | /port | open | Deferred — Phase-6 validation candidate once B3 lands, else --release |
| 0463 | /examples | open | Deferred — unmet trigger |
| 0050 | /int | deferred | Pin — `--release` polish |
| 0052 | /repl | open | Pin — `--release` polish |
| 0365 | /spec | open | Pin — `--release` polish |
| 0416 | /arch | deferred | Pin — `--release` polish (trigger-based) |
| 0466 | /design | deferred | Pin — indefinite, trigger-based |

## Architecture review (Phase 2)

**Verdict: PASS-with-revisions.** The DRAFT is technically coherent; reuse tokens + R5 rest correctly on the S102-landed carriers and the B1 typecheck-drain foundation. Revisions are all in Block A framing.

**Scope adjustments** (reflected above):
1. **Block A is NOT a hard gate on B2/B3.** The three A-FIXMEs (0526/0521/0515) don't gate mechanism implementation — the mechanisms consume the S102 carriers + B1, not the A-surfaces. Downgraded to Phase-3 co-resolution/drain. The real gate is B1.
2. **R5 predicate named as an /arch-authored `cranelisp-types` carrier change-set inside B3** (`value_layout` + `VALUE_LAYOUT_MAX_WORDS`, single-sourced, schema 12→13), landing with the mechanism design, never ahead.
3. Everything else stays: B1→B2/B3 sequencing, close-short seam after B3, region-arena deferred rider, Block C drains, Out-of-scope table.

**Public-API / interface needs-list** — exactly **one** genuinely-new cross-crate edge: the **R5 `value_layout` predicate** in `cranelisp-types/src/heap.rs` (consumed by both typecheck's mode classifier and backend's `HeapCategory::Value` arm — soundness-coupled, single-sourced), landing in the B3 change-set. **Reuse-token carriers: NONE** (off-ABI, spine §3.5 — confirmed). **`result_unique`: already landed** (S102 CS-A, advisory-false; II starts emitting true — no new carrier). **`ResultMode` ⊤ element: conditional** (0521 — only if an AliasOf-index reader lands). **Landed in Phase 2: nothing** — correct per the not-speculatively discipline.

**FIXME dispositions**: 0526 → kept open, Phase-3 backend design fire (direction ruled: consumer-driven = inc-I terminal; producer-side/escaping-projection promotes to inc-II, gated by Q4 uniqueness). 0521 → Phase-3 conditional (land ⊤ element iff index-reader arrives). 0515 → **RESOLVED this phase** by re-targeting /arch→/int (doc re-anchor, not a memory-model ruling; normative question already answered; now blocks Block C1 /int wave). None forced.

**Region-arena deferral verdict — CLEAN.** Checked against `s100-ownership-verification.md §2.3`: II-G1←R5, II-G2/G3/G4←reuse tokens; the only stack/region gate (I-G7) is delivered by increment-I Cranelift stack slots, not the arena. Arena serves NO gate in I-G1–G7 or II-G1–G4 — additive perf for dynamic-sized/extern-reached allocations, coupled to the unresolved (a)-allocator co-design. Deferral strands no half-built interface (§4.4 pins: same escape facts, shared immortal-header discipline, composes with the heap-allocated arm). Concur with the deferred-rider + close-short-after-B3 decision.

**Interim-architecture (Principle 8) check — no tear-out risk.** Reuse tokens off-ABI (no ABI to migrate); R5 predicate single-sourced + schema-gated (permanent home); `result_unique` bool additive; stack slots (I) compose with region arena (II) on shared escape facts. One watch item (pinned): land `value_layout` *with* the R5 change-set, never ahead.

**Stale-FIXME finding — 0474 and 0483 both CONFIRMED RESOLVED** (ran the guards on HEAD: 17/17 PASS). 0474 cured across S102 B3.1/B3.1a seam; 0483 cured by 0519's unified lossless mono-mangler. Both target /qa→/backend (not /arch-deletable) — **owners owe deletion; /sprint routes both to /backend at a wave gate.**

**Exit-gate readiness — READY for Phase 3.** Types carriers landed at S102 CS-A cover the committed floor; the one new edge (R5 predicate) is fully designed and lands in B3; reuse tokens are off-ABI. The two open A-FIXMEs resolve inside Phase 3 alongside the /design plans.

**Edit made this phase**: re-targeted `design/arch/fixmes/0515-*.md` /arch→/int (only file changed; no Rust touched).

## Skill plans (Phase 3)

_Pending Phase 3._

## Waves (Phase 4)

_Pending Phase 4._

## Notes

- 2026-07-05: **Phase 1 SCOPE DRAFT opened.** S102 archived (`sprints/archive/sprint-102.md`); ROADMAP updated (S102 CLOSED block + increment-I marked delivered, increment-II slotted S103). Scope inputs: S102 §"Carried to S103", the Phase-H sequence table, the 27-file FIXME set. Two FIXMEs (0474/0483) flagged for stale-open verification at Phase 2 (defects cured under S102 seam rework, guards green, owners owe deletion).
- 2026-07-05: **Phase 1 CLOSED — user approved scope.** Region arena confirmed as a deferred rider (not in the committed floor); close-short seam after B3 stands. → Phase 2 arch review issued.
- 2026-07-05: **Phase 2 COMPLETE — /arch PASS-with-revisions, exit-gate READY.** Block A downgraded from hard-gate to Phase-3 co-resolution (real gate = B1). R5 predicate named as an /arch-authored `cranelisp-types` carrier change-set (schema 12→13) landing in B3. 0515 re-targeted /arch→/int (now blocks Block C1). 0526 direction-ruled (kept open → Phase-3 backend fire); 0521 Phase-3 conditional. Region-arena deferral verified CLEAN (serves no I-G/II-G gate). **0474 + 0483 CONFIRMED stale-cured (17/17 guards green) — route deletions to /backend at a wave gate.** No `cranelisp-types` edit landed (not-speculatively). /arch's one edit: re-targeted FIXME 0515.

## Outcome (Phase 7)

_Pending close._
