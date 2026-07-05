# Sprint 103: Increment II — the write path (uniqueness → mutable-borrow → reuse)

**Status**: PHASE 5 LANGUAGE (ACTIVE) — Stage 1 QA-first

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
3. **R5 value-representation flattening** (backend §6.3 / spine §6.3 — `HeapCategory::Value` one-word flattening for Copy-eligible-within-the-tier concrete types). **The predicate is an /arch-authored `cranelisp-types` carrier change-set** (`value_layout(ty) -> Option<ValueLayout>` + `VALUE_LAYOUT_MAX_WORDS=1` in `heap.rs`), single-sourced (soundness-coupled: typecheck's mode classifier + backend's `HeapCategory::Value` arm both consume it — a `Copy`-moded param the backend didn't flatten is a UAF), co-scheduled with /design(typecheck) + /design(backend), carrying the `public-api.txt`/`interfaces.md`/BC §7 + `CACHE_SCHEMA_VERSION` **14→15** cascade (the live schema is already 14 — S102 Waves 8c-R/11; the earlier "12→13" figure was stale). Lands **in the B3 implementing change-set, never ahead of the R5 mechanism design** (Principle-8 speculative-interface discipline). Delivers gate **II-G1** via the **F2v single-ctor witness fixture**.
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
| 0506 | /design (backend) | open | §13.1 corrections actioned P3; stays open for any /dev residue at wave gate |
| 0507 | /design (src/) | open | Block C1 design DONE (Issues 1/2/3 + addenda 4/5/8); stays open — addenda 6/7/9 span downstream /dev·/frontend owners |
| 0509 | /design (typecheck) | **RESOLVED P3** | Doc ruling (`monomorphisation.md §5.1`); FIXME deleted at Phase-3 close |
| 0510 | /design (backend) | open | Block B1 — ruled option (a): register `neq-string` as ring1 primitive (Phase-5 /dev) |
| 0511 | /design (typecheck) | **RESOLVED P3** | Doc ruling (keep in-pass memo, defer session-threaded field); FIXME deleted at Phase-3 close |
| 0513 | /typecheck | open | Block B1 — design-specified (§14.1); Phase-5 /dev actions the `checker.rs::lookup` reorder |
| 0495 | /dev (backend) | open | Block C2 — IN (backend open) |
| 0496 | /dev (src/) | open | Block C2 — IN (src/ open for T1 full cure) |
| 0498 | /dev (types) | open | Block C2 — IN (types carrier extends) |
| 0499 | /qa | open | Block C2 — IN, QA-first stage head |
| 0500 | /dev (frontend) | open | **Wave 5** — pulled into scope (drain-all; user-approved 2026-07-05, no longer re-deferred) |
| 0501 | /dev (intrinsics) | open | **Wave 5** — pulled into scope (drain-all; user-approved 2026-07-05) |
| 0502 | /dev (platform) | open | **Wave 5** — pulled into scope (drain-all; user-approved 2026-07-05) |
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
2. **R5 predicate named as an /arch-authored `cranelisp-types` carrier change-set inside B3** (`value_layout` + `VALUE_LAYOUT_MAX_WORDS`, single-sourced, schema **14→15** — corrected in Phase 3 from the stale "12→13"), landing with the mechanism design, never ahead.
3. Everything else stays: B1→B2/B3 sequencing, close-short seam after B3, region-arena deferred rider, Block C drains, Out-of-scope table.

**Public-API / interface needs-list** — exactly **one** genuinely-new cross-crate edge: the **R5 `value_layout` predicate** in `cranelisp-types/src/heap.rs` (consumed by both typecheck's mode classifier and backend's `HeapCategory::Value` arm — soundness-coupled, single-sourced), landing in the B3 change-set. **Reuse-token carriers: NONE** (off-ABI, spine §3.5 — confirmed). **`result_unique`: already landed** (S102 CS-A, advisory-false; II starts emitting true — no new carrier). **`ResultMode` ⊤ element: conditional** (0521 — only if an AliasOf-index reader lands). **Landed in Phase 2: nothing** — correct per the not-speculatively discipline.

**FIXME dispositions**: 0526 → kept open, Phase-3 backend design fire (direction ruled: consumer-driven = inc-I terminal; producer-side/escaping-projection promotes to inc-II, gated by Q4 uniqueness). 0521 → Phase-3 conditional (land ⊤ element iff index-reader arrives). 0515 → **RESOLVED this phase** by re-targeting /arch→/int (doc re-anchor, not a memory-model ruling; normative question already answered; now blocks Block C1 /int wave). None forced.

**Region-arena deferral verdict — CLEAN.** Checked against `s100-ownership-verification.md §2.3`: II-G1←R5, II-G2/G3/G4←reuse tokens; the only stack/region gate (I-G7) is delivered by increment-I Cranelift stack slots, not the arena. Arena serves NO gate in I-G1–G7 or II-G1–G4 — additive perf for dynamic-sized/extern-reached allocations, coupled to the unresolved (a)-allocator co-design. Deferral strands no half-built interface (§4.4 pins: same escape facts, shared immortal-header discipline, composes with the heap-allocated arm). Concur with the deferred-rider + close-short-after-B3 decision.

**Interim-architecture (Principle 8) check — no tear-out risk.** Reuse tokens off-ABI (no ABI to migrate); R5 predicate single-sourced + schema-gated (permanent home); `result_unique` bool additive; stack slots (I) compose with region arena (II) on shared escape facts. One watch item (pinned): land `value_layout` *with* the R5 change-set, never ahead.

**Stale-FIXME finding — 0474 and 0483 both CONFIRMED RESOLVED** (ran the guards on HEAD: 17/17 PASS). 0474 cured across S102 B3.1/B3.1a seam; 0483 cured by 0519's unified lossless mono-mangler. Both target /qa→/backend (not /arch-deletable) — **owners owe deletion; /sprint routes both to /backend at a wave gate.**

**Exit-gate readiness — READY for Phase 3.** Types carriers landed at S102 CS-A cover the committed floor; the one new edge (R5 predicate) is fully designed and lands in B3; reuse tokens are off-ABI. The two open A-FIXMEs resolve inside Phase 3 alongside the /design plans.

**Edit made this phase**: re-targeted `design/arch/fixmes/0515-*.md` /arch→/int (only file changed; no Rust touched).

## Skill plans (Phase 3)

### /design (cranelisp-typecheck) — Block B1: drain foundation + write-path query emission — DONE

- **★ 0521 trigger verdict — NO.** The static-uniqueness subset introduces **no consumer that reads the `AliasOf` index** (uniqueness admits only `Fresh` results; the chaining discriminator reads the `result_unique` **bool** + `result==Fresh`, never `AliasOf(k)`). So the ⊤ element (`AliasOfAny`) does NOT land + there is NO schema bump for 0521. It stays the durable record; /arch takes no action. Full reasoning: `design/typecheck/ownership-inference.md §14.4`.
- **★ Schema-number correction** — the live `CACHE_SCHEMA_VERSION` is already **14** (verified: `cranelisp-backend/src/cache/mod.rs:261`); the R5 bump is **14→15**, not the plan's stale "12→13". Reconciled above.
- **Change-sets (dependency order)**: **CS-II-0** drain quartet (0509 + 0511 resolved doc-only; 0513 = one `checker.rs::lookup` qualified-arm reorder + unit; 0510 coordinated to backend) → **CS-II-1** uniqueness stratum + `result_unique` (third fixpoint stratum, greatest-fixpoint init-optimistic-true, cap-exhaustion resets to false) → **CS-II-2** `unique_static` site-fact (three-clause subset: fresh-unique-root ∧ single-consuming-use ∧ layout-eligible) → **CS-II-3 (rides B3)** the `Copy` classifier's R5 clause (delegates to /arch's `value_layout`).
- **Key frame**: increment II adds **no new typecheck-authored types carrier** — `result_unique`/`unique_static` landed at S102 CS-A (advisory-false); II starts *emitting them true* on the proven subset (value change, not shape change). The dynamic rc==1 discriminator is **backend-owned**; typecheck provides eligibility + proof (elide-where-proven), backend runs the check everywhere else. Monotone: absent/false/None ⇒ today's lowering.
- **Design refs**: `design/typecheck/ownership-inference.md §14` (new — write-path staging, §14.4 the 0521 verdict); `design/typecheck/monomorphisation.md §5.1` (new — 0509 record).
- **Acceptance**: per-CS unit seams (fixpoint/transfer/publish `#[cfg(test)]` incl. cap-reset ⇒ all-false, toggle-off ⇒ stratum-skipped) mapped to II-G1 (F2v R5 witness), II-G2/G3 (F4 reuse), L-C3 fence.
- **FIXME dispositions**: 0509 RESOLVED (doc) · 0511 RESOLVED (doc, keep in-pass memo, defer session-threaded field) · 0513 design-specified, stays open for Phase-5 /dev · 0521 verdict NO, stays open as record · 0510 coordinated, stays open (/design-backend).

### /design (cranelisp-backend) — Block B2/B3: reuse tokens + R5 arm + drains — DONE

- **Ladder (dependency order)**: **II-B1** R5 carrier consumption + `HeapCategory::Value` arm (bare-word move, no RC, drop-glue skip; consumes /arch's `value_layout`, schema 14→15 as consumer) → delivers **II-G1** (F2v witness) · **II-B2** reuse tokens (function-local SSA maybe-null token drop→alloc, **off-ABI confirmed §14.4**, per-call entry check, static-proof *elides* the rc==1 check without replacing the token; `reuse_hit`/`reuse_miss` counters) → delivers **II-G2/G3/G4** · **— CLOSE-SHORT SEAM —** · **II-B3** producer-side escaping-projection elision (0526 §3.3 promoted) = **DEFERRED RIDER** (serves no II-G gate; rides only if capacity survives the seam).
- **★ Region-arena readiness verdict — DEFER** (do not pull back before B3): serves no I-G/II-G gate; incremental reach gated on the unresolved (a)-allocator thread-region handoff co-design (not implementation-ready); §4.4 pins mean it composes additively later — deferral strands no interface. Pull-back trigger = allocator co-design ready ∧ an F-fixture with a `NoEscape` dynamically-sized/extern-reached hot allocation.
- **0510 ruled option (a)**: register `neq-string` as a `ring1` `DefKind::Primitive` entry (in `cranelisp-primitives`, symmetric with `str-eq`) — pure table registration, **no pass5 change owed**; scalar `neq-*` stay harvest-only.
- **0506** §13.1 capture-spec corrections actioned (doc-only). **0526** §3.3 re-frame authored, left open for /arch to close.
- **Design refs**: `design/backend/ownership-codegen.md` §3.3 (0526 re-frame), §4.4 (arena verdict), §6.4/§6.5 (elision seam + counters), §7.1/§7.3 (R5 arm + F2v path), §9.4 (0510), §13.1 (0506), new §14 (increment-II staging + seam×class scenario matrices); `ring2-rc.md §3.3` (neq-string row).
- **Acceptance**: II-G1 `value_layout`→classify→null-elem-fn graded by F2v rc_inc <1% of B2 ∧ F2v N-worker wall < serial; II-G2 counters hit-rate ≥50% on F4; II-G3 F4-hard median ≤2× serial; II-G4 F2 two-ctor honesty (NOT R5-graded). **L-C3 fence must cover a proof-elided reuse (UAF-critical — no dynamic backstop).** Differential-oracle byte-identical off (every else-arm = pre-increment-II helper; reuse/`value_layout` are host-side, no emitted IR → L-B1 golden diff EMPTY).

### /design (src/) — Block C1: T1 full cure + 0515 re-anchor — DONE

- **T1 full cure** (`src/`-only, no cross-crate edge): **CS-1** end-of-turn reload driver (post-regen `reload_module`(target) + dependent cascade through the §7.3 Replace gate, eval-synchronous per the S93 watcher discipline; reachable from both ordinary-def exit AND the `eval.rs:329` defmacro early-return — closes 0507 F5a) → **CS-2** module-grain report integration (reload recompiles exactly the callers `stale:` named ⇒ section renders **empty**, Principle-8 kept-machinery pin) → **CS-3** edge handling (reload-failure ⇒ §14.4 error-blocked, the 0489 floor, never a lockout).
- **Two prerequisite refinements fold into the trigger**: **F2 slot-refinement** (`is_t1_downgrade` gains `&& (new_slot.is_none() || old_slot.is_none())` — a slotted→slotted late-binding ctor re-entry does NOT trigger) + **0491-exclusion resolution** (`__macro_*` reachability CONFIRMED reachable via spec §9.3.4/§9.12 → **narrow the `ReverseIndex::build` caller exclusion to `__expr` only**, keep `__macro_*` reverse edges, render a macro-clause caller as its owning user macro `{name}`, disposition it to module-grain reload).
- **Two coherent-stale pins to flip**: `redefine_concrete_to_polymorphic_caller_survives_coherent_stale` + `redefine_concrete_to_overloaded_caller_survives_coherent_stale` (old-chain pin flips; `stale:` section empties), plus the L-U1 sibling + `t1_downgrade_report_*` pair.
- **0515** re-anchor DONE (doc-coherence: reversed `s78-entry-module.md §2`'s silent-shadow conclusion to the user's no-exception ruling; impl seam already landed via FIXME 0514).
- **Design refs**: `design/int/session-transaction.md` §9.1.1/§10/§11/§13; `design/int/s78-entry-module.md §2` (0515); `design/int/s102-defect-wave.md §2/§5.2`.
- **Sequencing**: Block C, rides where `src/` is open; S102 A2/A4 preconditions all landed; does NOT displace Block B (src/-only, `AbiSurface` seam untouched). **One precondition to *verify* not build (I-4)**: CS-1 reloads the regenerated backing file, so a trait/type/impl-bearing module's cure needs regen fidelity in sections 5–7 — /dev confirms before CS-1 reloads such a module.
- **0507 disposition**: Issues 1/2/3 + addenda 4/5/8 resolved by these edits; addenda 6 (I-1 repair carve-out), 7 (I-3 binder-position, /frontend), 9 (M-3) span downstream owners — **/design(src/) recommends 0507 stays OPEN** until dispositioned.

### /qa — increment-II test plan — DONE (`tests/plan/s103-test-plan.md`)

- **QA-first failing-test set by lane**: **R5 witness** (F2v single-ctor `(deftype Cell (Cell [:Int value]))` + parallel≡serial + rc_inc-collapse + **R5 soundness-couple negative fence**: a Copy-eligible-but-*unflattened* shape must NOT be moded `Copy` — sustained-use + ASan + heap-balance) → II-G1; **reuse-token set** (**L-C3 reuse-corruption fence**, 5 legs, new `tests/ownership_reuse.rs`; counter smoke on the landed S102 H2 grammar; chaining witness `(map inc (map dec v))`) → II-G2/G3/G4; **differential-oracle write-path extension** (L-B2 polarity + byte-differential; L-B3(4) schema-invalidation lane).
- **h3 flip** (S102's sole intentional RED, `h3_rc_stats_reports_per_extern_adaptation_pairs`): flips when the per-extern adaptation-pair attribution (Hook H3 / L-D5) emits into `CRANELISP_RC_STATS`, riding the `str-len$borrowed` sibling-expansion (owner /dev-for-/backend). Report-grade, gates nothing.
- **T1 cure acceptance pair** (repl §18.1.1 negative-MUST): `t1_full_cure_recompiles_stale_callers_stale_section_empty` (RED) + `t1_full_cure_body_only_edit_still_no_report_no_recompile` (GREEN over-trigger pin); S102 coherent-stale pins get flip-note reconciliation (none deleted/weakened).
- **Gate plan**: extend `ig_gates.py`; release binary, median-of-7, fresh toggle-off baseline on S103 HEAD. II-G1 ← R5 (F2v rc_inc <1% of B2 ∧ F2v N-worker < serial — first parallel-must-pay); II-G2 ← reuse hit-rate ≥50% (counter landed S102); II-G3 F4-hard median ≤2× serial; II-G4 F2 two-ctor honesty (NOT R5-graded); II-G5/G6 = I-G re-run incl. F2v serial.
- **0499**: lands **L-S1** (preamble-grid helper) + **L-M1's B3-wave growth** this sprint; all 4 drafting rules bind; deletion condition = if both land (all 7 lanes exist) /qa deletes 0499 at close, else annotate + carry.
- **Design refs**: `tests/plan/s103-test-plan.md` (new); `tests/CLAUDE.md` §Plan documents (registered); `design/arch/fixmes/0499-*.md` (per-lane status appended).
- **Exit-gate: READY for Phase 5.** Five landing dependencies flagged (G-1..G-5) — all Phase-3 co-resolution questions now answered by the sibling /design plans + the /arch Phase-2 needs-list (G-5 = the `value_layout` carrier /arch already owns). No new FIXME needed.

## Waves (Phase 4)

**Dependency spine** (from the Phase-3 plans): the /arch R5 `value_layout` carrier is consumed by BOTH typecheck's `Copy` classifier (CS-II-3) and backend's `HeapCategory::Value` arm (II-B1) → it lands first. Typecheck's `unique_static`/`result_unique` facts (CS-II-1/2) gate backend's reuse tokens (II-B2) → typecheck before backend. Block C (T1 full cure, src/-only, `AbiSurface` untouched) is independent of Block B. **Source work runs serially** (project single-writer rule — worktree isolation broken); waves order the ladder and set the gates. Each Stage-2 wave is /dev then /review, narrow to the named crate. Unit-tier drains fold into their crate's open window.

### Stage 1 — QA-first (sprint-wide, one /qa invocation)

/qa writes the full increment-II failing-not-ignored test set per `tests/plan/s103-test-plan.md` (R5 witness + soundness-couple negative fence, L-C3 reuse-corruption UAF fence, reuse chaining witness, differential-oracle write-path extension, the T1 cure acceptance pair, the h3 flip target). Also lands the **0499 L-S1 preamble-grid + L-M1 B3-wave growth**. Tests fail because the mechanisms don't exist yet — intended state. This is Wave 0.

### Stage 2 — per-crate D/D/R serial ladder

| Wave | Skill → | Crate | Task | Gate before advancing |
|---|---|---|---|---|
| 1 | /arch → /review | `cranelisp-types` | **R5 carrier**: `value_layout(ty) -> Option<ValueLayout>` + `VALUE_LAYOUT_MAX_WORDS=1` in `heap.rs`; `CACHE_SCHEMA_VERSION` 14→15 + public-api/interfaces/BC §7 cascade. **+ 0498** types marshal-drift-guard drain (types open). | scan `target:/arch` open FIXMEs; carrier surface matches Phase-2 needs-list |
| 2 | /dev → /review | `cranelisp-typecheck` | **B1 foundation + queries**: CS-II-0 (0513 lookup reorder + drain) → CS-II-1 (uniqueness stratum) → CS-II-2 (`unique_static` site-fact) → CS-II-3 (`Copy` R5 clause, consumes Wave-1 carrier). | scan `target:/typecheck`/`/design(typecheck)`; 0513 resolved; toggle-off skips stratum |
| 3 | /dev → /review | `cranelisp-backend` (+ `cranelisp-primitives`) | **Mechanisms**: II-B1 (R5 arm, consumes Wave-1 carrier) → II-B2 (reuse tokens, consumes Wave-2 facts; `reuse_hit/miss` counters) + **0510** ring1 `neq-string` primitive + **h3/L-D5** per-extern RC_STATS emission + **0526** close (§3.3 re-frame) + **0495** backend `tests.rs` split drain. **★ CLOSE-SHORT SEAM after II-B2** — II-B3 (producer-side projection elision) is a deferred rider, rides only if capacity survives. | scan `target:/backend`/`/design(backend)`; **route 0474 + 0483 stale-cured deletions to /backend here**; L-C3 fence green incl. proof-elided reuse; differential golden EMPTY |
| 4 | /dev → /review | `src/` | **T1 full cure (Block C1)**: CS-1 reload driver → CS-2 module-grain report (empty `stale:`) → CS-3 edge handling; + F2 slot-refinement + `__expr`-only exclusion narrowing + **0496** `lifecycle.rs` unit-tier drain + **0515** re-anchor verify. Verify I-4 regen-fidelity precondition before reloading a trait/type/impl-bearing module. | scan `target:/int`/`/design(src/)`; the two coherent-stale pins flip; §18.1.1 negative-MUST `[Tested+Neg]`; 0515 (→/int) resolved |
| 5 | /dev → /review ×3 | `cranelisp-frontend`, `cranelisp-intrinsics`, `cranelisp-platform` | **Unit-tier drains** (drain-all rule — pure test-coverage additions, not write-path-gated): **0500** frontend rendered-diagnostic unit tier · **0501** intrinsics io-guard strand coverage · **0502** platform declare-concurrency coverage. Three independent mechanical passes (serial per single-writer). | scan `target:/dev(cranelisp-frontend\|intrinsics\|platform)`; each crate's submodule-thinness map (S101 audit) improved; suite green |

**Wave 5 rationale (user-approved 2026-07-05)**: 0500/0501/0502 are actionable in any sprint (no Phase-H / concurrency / trigger gate); deferring them a 2nd time would be habit-deferral against the drain-all rule + approaching the METHOD §2.4 2× gate. Pulled into scope rather than re-deferred.

### Deferred tail (drain-all rule — each against an allowed reason)

- **II-B3** (backend producer-side projection elision, 0526 mechanism half) — deferred rider past the close-short seam (write-path dependency: needs Q4 uniqueness proof).
- **Region arena** (backend §4.4) — deferred rider (allocator co-design not implementation-ready).
- **0050 / 0052 / 0365 / 0416** — `--release`-polish pins (Phase-H-gated, after increment II settles).
- **0463** — unmet trigger. **0466** — user-directed indefinite/trigger-based.
- **0408** — inc-II write-path dependency; becomes a Phase-6 validation candidate once Wave 3 lands.

## Notes

- 2026-07-05: **Phase 1 SCOPE DRAFT opened.** S102 archived (`sprints/archive/sprint-102.md`); ROADMAP updated (S102 CLOSED block + increment-I marked delivered, increment-II slotted S103). Scope inputs: S102 §"Carried to S103", the Phase-H sequence table, the 27-file FIXME set. Two FIXMEs (0474/0483) flagged for stale-open verification at Phase 2 (defects cured under S102 seam rework, guards green, owners owe deletion).
- 2026-07-05: **Phase 1 CLOSED — user approved scope.** Region arena confirmed as a deferred rider (not in the committed floor); close-short seam after B3 stands. → Phase 2 arch review issued.
- 2026-07-05: **Wave 5 added (user-approved).** 0500/0501/0502 unit-tier drains pulled into scope rather than deferred a 2nd time (drain-all rule; no Phase-H/trigger gate excuses them). S103 now actions 18 of 24 open FIXMEs; the remaining 6 are Phase-H-polish/trigger-gated. → Phase 5 launched.
- 2026-07-05: **Phase 4 COMPLETE — waves organized.** Stage 1 QA-first (sprint-wide) + a 4-wave serial D/D/R ladder (types carrier → typecheck B1 → backend mechanisms [close-short seam after II-B2] → src/ T1 cure), unit-tier drains folded into their crate windows, wave gates set. Serial per the project single-writer rule. Deferred tail: 0500/0501/0502 + II-B3 + region arena.
- 2026-07-05: **Phase 3 COMPLETE — four design plans collected (typecheck/backend/src + qa test plan), exit-gate READY.** Cross-consistent. Load-bearing outcomes: **0521 verdict NO** (no AliasOf-index reader → ⊤ element stays deferred, no schema bump); **schema-number corrected 14→15** (live is 14, not the stale "12→13"); reuse-tokens confirmed off-ABI; **region-arena DEFER** re-confirmed by /design(backend); 0510 ruled option (a) ring1 primitive; T1 full cure design DONE with the **`__expr`-only exclusion narrowing** (keep `__macro_*` reverse edges) + F2 slot-refinement; /qa `s103-test-plan.md` authored with II-G1–G4 gate plan + L-C3 UAF fence + R5 soundness-couple negative fence + h3 flip criterion. FIXMEs resolved+deleted P3: **0509, 0511** (doc rulings by /design-typecheck). 0526 §3.3 re-frame authored (left open → /arch closes). 0513/0510/0506/0507 stay open for Phase-5 action. No new interface beyond the /arch-owned R5 `value_layout` carrier (schema 14→15, lands in B3).
- 2026-07-05: **Phase 2 COMPLETE — /arch PASS-with-revisions, exit-gate READY.** Block A downgraded from hard-gate to Phase-3 co-resolution (real gate = B1). R5 predicate named as an /arch-authored `cranelisp-types` carrier change-set (schema 12→13) landing in B3. 0515 re-targeted /arch→/int (now blocks Block C1). 0526 direction-ruled (kept open → Phase-3 backend fire); 0521 Phase-3 conditional. Region-arena deferral verified CLEAN (serves no I-G/II-G gate). **0474 + 0483 CONFIRMED stale-cured (17/17 guards green) — route deletions to /backend at a wave gate.** No `cranelisp-types` edit landed (not-speculatively). /arch's one edit: re-targeted FIXME 0515.

## Outcome (Phase 7)

_Pending close._
