# Sprint 118: Instrumented Ownership Closure

**Status**: PHASE 5 LANGUAGE (ACTIVE)

**Goal**: Land the memory-diagnostic instrumentation as the sprint's foundation, then drive the attributed RED baseline down by migrating the ownership consumers onto the canonical drop glue — every fix proven by a detector that has itself been proven to detect.

**Audit**: cranelisp-types (longest-unassessed context — last whole-context pass S87; it absorbed the S116 carrier work: `Sexp::Annotated`, `UnresolvedTraitMethodSig`/`TraitMethodKind`, `drop_glue_symbol_name`, schema 23)

## Standing context for this sprint

- **The S117 "cyber-check" constraint is lifted.** The user has stated explicitly (2026-07-25): the memory-allocation instrumentation is codegen-correctness work, not cybersecurity. The S117 deferrals grounded in that constraint (0848, 0850, 0857, 0859, the ownership consumer waves, load-dependent investigation) are all eligible again. No FIXME retains "cyber-blocked" as a valid deferral rationale.
- **RED baseline at open (verified by full run 2026-07-25): 5,514 run / 5,486 passed / 28 failed / 1 skipped.** All 28 are attributed: the S116 Waves-4/5 ownership-consumer family (0810 ×10 match-scrutinee, 0760 capture-glue, transitive-glue termination, 0745/program-result ×3, `conj` ×3, exemplar residue), the two M3 detection-proof guards (0848/0857), the load-dependent `launch_grid_corrupt` guard (0694), DF1/DF2 (0863), and the two Phase-6 cache guards (0868/0869). Zero unattributed.
- **First sprint under delegated review.** `/review` waves are executed by the external Codex reviewer via `scripts/codex-review.sh`, adjudicated and FIXME-filed by the invoking agent (ratified 2026-07-25; `.claude/commands/review.md` §Delegated execution, `artefacts.md` §II.3). Fallback to internal review is recorded per dispatch.

## Scope

Sprint 118 resumes the Phase-H memory-safety frontier where S116 left it, with the user-directed inversion: **instrumentation first**. S116 ordered consumers (Waves 4–5) before detector proofs (Wave 7); S118 lands the detectors first so that every ownership-consumer migration in Track B is verified against instruments that have positive proof they detect what they claim, and so Track C's load-dependent work finally has tools.

### Track A — detection instrumentation, proven (first, foundation)

The S116 Wave-7 remainder, now central:

1. Implement the closed test-only fault-injection plant protocol at the intrinsics alloc/diagnostics seam per `design/intrinsics/diagnostic-modes.md` (crate-private, armed only by exact child-environment values, byte-inert while off). Prove M1, M2, M3 and A1–A4 detect their planted faults: positive, clean-control, and disabled-detector fail-on-revert polarity for all eight detector rows (FIXME 0848). The two committed M3 e2e guards flip green here.
2. `/qa` witnesses the fail-on-revert evidence and regrades R8/detector modes honestly — asserted-but-unproven grades are replaced by proven or downgraded (FIXME 0857).
3. Converge the raw heap-read owner: `drop.rs` → `heap_access`/`vec_runtime` (FIXME 0850 — **aged: first flagged S87-era, already at its user-signed third deferral in S117; it ships this sprint**).
4. Close the remaining R-2 gap: the ProjectionOf production-artifact sensitivity witness that ordinary evidence could not reach in S117 (FIXME 0859) — per arch ruling 2: the existing detector surface as oracle, no new seam, graduating only after the detection proofs land.
5. Land the owed S116 ruling-5 subtractive API change (arch ruling 7): remove `reset_counts()` and `bytes_peak()` from `cranelisp-intrinsics`, clean their rustdoc references, regenerate the baseline — riding the 0850 change-set. Deferred once under the cyber constraint; does not slip again silently.

### Track B — ownership consumers onto canonical glue (the RED clearance payload)

S116 Waves 4–5, unchanged in design, executed with Track A's detectors live:

1. Backend consumer migration in the arch-ruled order (sprint-116.md ruling 1): 0835 SList construction first, then 0810 match-scrutinee lifetimes (all ten cells), 0760/0796 explicit+synthetic capture teardown, and the 0688-family TCO replacement/transfer predicate. `MAX_DROP_GLUE_DEPTH` and the legacy inline emitter are deleted atomically with the migration (the Wave-3 transitional condition). No per-seam shallow patch; everything routes through the canonical named/per-concrete glue landed in S116.
2. The unified program-result owner (0745) across REPL, `--run`, cache-hit, and linked startup per `design/int/result-owner.md` — observe/display/convert first, then exact-once type-directed release; `Pure` selects the inner type's glue.
3. The three `conj` ownership guards and the exemplar warm-residue threshold are expected consequents; they are verified, not separately patched.

Plans of record already exist and were arch-approved in S116 (`design/backend/transitive-drop-glue.md`, `design/int/result-owner.md`); Phase 3 refreshes rather than re-authors them.

### Track C — load-dependent characterization and certification

With detectors proven and consumers migrated:

1. Characterize the load-dependent heap-corruption family: `launch_grid_corrupt`, the 0694 flap set, and the 0604/0818 contamination discriminator. Controlled reproduction under load with the M-detectors armed; reduction before fix; no symptom-absence closure.
2. Re-establish the certification split S115 defined and S116/S117 could not meet: two identical deterministic full runs, plus at least three captured loaded runs for the corruption member. Zero-baseline-RED remains the exit contract for the deterministic suite except where an explicit user-approved carry is recorded at close.

### Track D — S117 forward-flow (bounded)

1. FIXME 0863: the cluster-wide prepared macro-presentation transaction (DF1/DF2), user-committed to S118 at the W3c deferral. It reopens the reviewed W3a seam in `src/`; it runs as its own late wave, serialized after Track B's int work.
2. FIXME 0867: `/testing` lands the permanent polymorphic-field-accessor repro.
3. FIXMEs 0868/0869: the two cache-restoration defects (private-child enrollment; sibling-written trait impls). 0869's cache-carrier question goes to `/arch` in Phase 2; implementation only if the ruling is cheap, else explicit defer with rationale.

### Track E — platform audit slice (user-accepted, bounded)

From the S118 Phase-1 disposition of `audits/cranelisp-platform-s117.md` (all
five recommendations accepted; trail recorded in the audit §4):

1. FIXME 0870 (R1): `/dev`(platform) repairs the source facade to one ABI-v9
   contract — documentation only, no semantic API delta.
2. FIXME 0873 (R4): `/design`(platform) authors the marker-binding ergonomics
   design — **user pulled this into S118**; design only, implementation is a
   follow-on; `/arch` reviews on any public-API contact.
3. FIXME 0874 (R5): `/dev`(platform) shares the raw heap-ADT test fixture
   across the three integration crates without merging schema isolation.

R2 (0871) targets S119; R3 (0872) is at `/arch`'s discretion within S118's
windows or S119. Track E is a small serial platform wave, independent of the
safety tracks; it slots wherever Phase 4 finds room and does not compete with
Tracks A–C for their surfaces.

### Explicitly out of scope

- Multi-field SROA and the LLVM `--release` tier — still gated behind Track C's certification; this sprint aims to *unlock* that gate, not jump it.
- Byte-backed text implementation (`Byte`, `Utf8Literal`, transparent products, stdlib Unicode) — design-only per the S117 record; its user gates are not reopened this sprint.
- Display protocol 0050 and `/learn` 0052 — remain on the release-polish schedule.
- Exemplar standalone Link parity (platform archive unresolved Rust symbols) — now FIXME 0875 (target `/qa` for attribution); scheduled S119 unless trivially adjacent to Track B's linked-startup work.

### Capacity honesty

Tracks A+B+C are the full S116 remainder plus certification — more than S116 itself absorbed. The declared priority order is A → B → C → D. If capacity forces a cut (refined per arch ruling 8): 0869's *implementation* defers first (schema-bearing; its carrier ruling still lands this sprint), then 0868 (schema-free, survives a 0869 cut independently), then Track C's three-run loaded certification (characterization evidence still required), and 0863 is renegotiated with the user rather than silently dropped (it carries a prior user commitment to S118). Track A and Track B items 1–2 are not cuttable — they are the sprint, and per arch ruling 10 the Track-B atomic legacy-emitter deletion is architecturally binding, not just capacity policy.

## Phase 1 user decisions — RESOLVED 2026-07-25

1. **Scope APPROVED as drafted**: Tracks A–D, instrumentation-first order, the
   stated cut priority, and 0850 shipping in Track A.
2. **S117 platform-audit disposition — ALL FIVE ACCEPTED.** Filed as FIXMEs
   0870 (R1), 0871 (R2, S119 target), 0872 (R3, `/arch` discretion), 0873
   (R4 — user pulled into S118), 0874 (R5). Disposition trail appended to
   `audits/cranelisp-platform-s117.md` §4. R1/R4/R5 form Track E.
3. **0850 ships** — confirmed within the scope approval; its third deferral
   (S117) was its last.

Additionally filed at Phase 1: FIXME 0875 (exemplar standalone-Link parity
blocked by unresolved Rust symbols in the platform archive — the S117 deferral
bullet had no durable record; `/qa` attributes before any fix dispatch).

## FIXME debt

| FIXME | Target skill | Proposed S118 status | Notes |
|---|---|---|---|
| 0848 | /dev(intrinsics) | Track A must-ship | Detection proofs for M1/M2/M3/A1–A4; the two M3 REDs flip here. |
| 0857 | /qa | Track A must-ship | Honest regrade after fail-on-revert evidence. |
| 0850 | /dev(intrinsics) | **resolved W2a** — deleted | Convergence landed with byte-identical-RED invariance verified; aged FIXME closed after S87-era origin. |
| 0879 | /design(intrinsics) | filed W2a | §7.5 alignment clause false-positives on ragged HeapString sizes; corrected Layout-validity predicate implemented; design doc owes the delta. |
| 0859 | /qa → narrow owners | Track A | ProjectionOf production witness via the smallest admissible instrument. |
| 0835 | /dev(backend) | Track B first consumer | SList construction; arch-ruled migration order. |
| 0810 | /dev(backend) | Track B must-ship | All ten match-scrutinee cells. |
| 0760 / 0796 | /dev(backend) | resolved as FIXMEs (P3) — work ships in Track B | Design asks satisfied and files deleted 2026-07-25; the committed REDs #11–#13 + the balance-exclusion removal cell are the sole record/trigger. |
| 0877 | /qa | **resolved P3** — attribution ruled (a) runtime-owned | Falsification probe run: residual scales with list length at constant type depth; backend hypothesis falsified. S2 rerouted out of backend order. |
| 0878 | /qa | **resolved P3** — fence extended | Plan §4.3 grep-zero now covers `build_adt_drop_glue_fn`/`build_elem_dec_fn`/`adt_drop_glue_name`. |
| 0835 | /design(intrinsics) → /dev(runtime pair) | retargeted P3 | Runtime consume-owner defect (`deep_rc_inc_slist` over-inc vs. correct tree-ownership `consume_slist`); `/design`(intrinsics) rules head-only-inc vs deep-consume first; `/testing` lands repros A+B in W1; decoupled from backend W3. Abort-face survival after the fix is a new attribution, never a backend re-open. |
| 0745 | /dev(src+exe-bundle) | Track B must-ship | Program-result owner; design of record exists. |
| 0782 | /dev(backend) | Track B | Var-pattern arm double-release — same consumer family. |
| 0694 / 0604 / 0818 | /qa | Track C | Load-dependent characterization with armed detectors. |
| 0863 | /design → /dev(src) | Track D | Prepared-presentation transaction; user-committed to S118. |
| 0867 | /dev(typecheck) | retargeted W1+ | Repro landed W1; real axis is constructor-arm field lists (`synthesise_field_accessors` product-only gate); spec requires partial sum accessors. Capacity-dependent implementation. |
| 0868 / 0869 | /arch → /dev(src) | Track D conditional | Cache-restoration defects; 0869 carrier ruling in Phase 2. |
| 0726 / 0761 / 0778 / 0779 / 0830 / 0831 | /qa | eligible again | Instrumented-matrix items unblocked by the lifted constraint; `/qa` triages which ride Track A vs. defer with rationale. |
| 0870 / 0873 / 0874 | /dev(platform), /design(platform) | Track E | Audit R1/R4/R5 accepted; R4 user-pulled into S118 (design only). |
| 0871 | /design(platform) | filed, S119 target | Audit R2 accepted; capacity rationale recorded in the FIXME. |
| 0872 | /arch | filed, discretionary | Audit R3 accepted; `/arch` folds into an S118 window or defers to S119. |
| 0875 | /qa | filed | Exemplar Link parity blocked by platform-archive unresolved Rust symbols; attribute (minimal repro) before fix dispatch; S118 if adjacent to 0745's link work. |

Remaining open FIXMEs (49 total) are carried without sprint action unless a track touches their surface; the Phase-4 wave gate scans per wave as usual.

## Architecture review (Phase 2)

**Verdict: PASS AFTER REQUIRED REVISIONS (2026-07-25).** Technically coherent; the instrumentation-first inversion is sound; Tracks A–B execute already-approved plans of record with no new interim architecture. Sign-off granted upon transcription of R7 (applied below). Rulings:

1. **0869 requires a typed cache carrier; the ruling is the S118 deliverable, implementation capacity-conditional.** A writer-side typed record (canonical `FQTraitName` + `FQTypeName` + writer module + method names + visibility — no mangled-name parsing, no foreign-table scan), persisted with the writer module's cache metadata, restored through one idempotent enrolment helper reusing fresh registration's conflict/coherence checks. Takes `CACHE_SCHEMA_VERSION` 23→24 in its own window; **no other S118 track is authorized a schema bump**. If capacity cuts the implementation, 0869 defers to S119 carrying the settled ruling.
2. **0859: no new seam.** The instrument is the existing env-gated detector surface (M1/M2/M3 + RC/parity counters) as oracle over isolated-declaration-mutation experiments in fresh subprocesses; the §7 fault-plant protocol is *not* the instrument (plants prove detectors, they don't witness declarations). The witness may only graduate after Track A's detection proofs land (0768 rule). If every production shape remains emission-inert, that is the FIXME's disposition 2 — returned to the user, not overridden with test-only facts.
3. **Ordering inversion confirmed — no dependency violation.** Detection proofs are self-contained plant triplets assuming nothing about consumer/glue state; the dependency runs the other way (§6 acceptance needs consumer REDs still red, which detectors-first preserves). Binding caution: consumer migration runs with **lane/subprocess-scoped arming only, never suite-global** — a globally-armed M3 aborts every still-red leak guard.
4. **0872 scheduled into S118's `/arch` Phase-7 close window** (doc-only, gates nothing); defers to S119 only if close is compressed.
5. **Track E R4/0873 — no pre-authorization.** Any mechanism touching `cranelisp-platform`'s public surface (new trait, derive crate, `CLAdtType` contract) returns to `/arch` before selection is final; docs and crate-internal choices need no gate.
6. **0850 target stands, verified at HEAD**: S117 W5 converged only the buffer-lifecycle half; `drop.rs` still carries a private `read_i64` and copied Vec offsets. Delete both, delegate to `heap_access`/`vec_runtime` layout authority; behavior-invariant, zero public-API delta.
7. **(REQUIRED — applied)** S116 ruling 5 is approved-but-unlanded: `reset_counts()`/`bytes_peak()` are still public and still baselined; retaining `reset_counts()` can invalidate M3's monotonic-counter evidence. Named explicitly in Track A; rides the 0850 change-set; subtractive intrinsics baseline regeneration.
8. **(Recommended — adopted)** Cut order split: 0869 defers first (schema-bearing, ruling-gated); 0868 is schema-free and ruling-free and survives a cut that drops 0869.
9. **S116 rulings status**: 1/2/3/6/7/8 stand unchanged and bind Tracks A–B; 4/9/10 landed in S116 and are executed facts; 5 is R7.
10. **The Principle-8 bridge closes this sprint.** The canonical `DropGlueRegistry` coexisting with the legacy inline emitter (`MAX_DROP_GLUE_DEPTH = 4` still live) was an approved transitional state whose closure condition is exactly Track B item 1: consumers migrate and the depth constant + inline emitter delete **atomically in the same wave**. Track B items 1–2 "not cuttable" is architecturally binding, not just capacity policy; a partial migration leaving both mechanisms is a `/review` REJECT.
11. **0863 confirmed READY**: int-only, no public API/types/cache change; serialize as a late wave after 0745 (same `src/` publication/result-owner seams; must not interleave).
12. **`/arch` self-obligations**: FIXME 0768 (register status vocabulary) actioned in the same window as `/qa`'s 0857 regrade so the regrade lands into the amended vocabulary; 0872 per ruling 4.
13. **0810 labelling nuance**: it is a test-record defect (the committed test file is the durable record); no FIXME file exists or should be created.

**Public-API impact**: `cranelisp-intrinsics` subtractive only (ruling 7); all other crates zero-delta / zero-diff checks; `cranelisp-types` delta only if 0869 implements (gated on ruling 1). No new cross-crate types for Tracks A–C.

## Skill plans (Phase 3)

### `/qa` — COMPLETE (2026-07-25)

Plan of record: `tests/plan/s118-test-plan.md`; durable rows in `tests/plan/PLAN.md` §S118 and `tests/plan/risks.md` (10-row S118 read + two permanent register lenses).

- **Certification split structural**: detector arming is child-env only; W1 adds a static grep gate against suite-scope arming; exactly one schema window (23→24, 0869-only) — any other schema delta is a close blocker.
- **28-name baseline enumerated from live sources** with per-cell flip attribution. Two low-confidence cells flagged for W1 reconciliation from the captured baseline log (the `conj` armed-parity leg; whether the M3 clean control is 0848-only or 0745-coupled); family arithmetic reconciles at 28 either way.
- **Track A**: eight detector triplets with per-row fail-on-revert as hard input to the 0857 regrade (sequenced after `/arch`'s 0768 vocabulary amendment). 0850 behavior-invariance pinned by "every baseline RED stays byte-identically RED in the 0850 change-set". Ruling-7 subtractive baseline cells specified. 0859 conditional per arch ruling 2; emission-inert outcome returns to the user as disposition 2.
- **Track B**: S116 matrix carried with an exists-vs-authors reconciliation; ruling-10 structural fence (grep-zero legacy emitter) planned; each fix wave re-demonstrates its flips under subprocess-armed detectors; `conj`/exemplar cells are verified consequents — residual RED is a new attribution, never a re-threshold.
- **Track C**: two identical captured deterministic runs vs. ≥3 captured loaded runs + mechanism + fail-on-revert; 0694 D1→D2→D3 with D1 gating; 0818 contamination experiment cheap-first.
- **Tracks D/E**: 0863 cells serialized after 0745; 0868 schema-free; 0869 conditional with stale-cache-rejection cell if shipped; 0874 preservation checklist (assertion inventory, zero weakenings).
- **Re-eligible FIXME triage**: 0726 + 0830 ride Tracks A/B now; 0831 + 0778 actioned and deleted (register/PLAN rows landed); 0761 + 0779 deferred with rationale recorded in their files as S119 triggers.
- **Exit verdict**: `/testing` has enough to draft W1 (baseline reconciliation, four intended-RED additions, arming-discipline static gate).

### `/design` (intrinsics) — COMPLETE (2026-07-25)

Plan of record: `design/intrinsics/diagnostic-modes.md` (+575/−120; §7.1–§7.4 numbering preserved for existing citations; new §7.5–§7.7); index updated.

- **§7.5 (load-bearing discovery): env-gated seam checks must become PREchecks.** As built, all four gated checks run after their mutation and after always-on `debug_assert!` twins — in the debug profile a plant trips the twin before reaching the gate, so positive proofs would fail against *working* detectors. One shared `diagnostics::seam_precheck` hoists to the top of the RC/dealloc funnels; byte-identical-off preserved. This gates the plant implementation: /dev implements the hoist first (§10 step 1) or four rows misread as detector failure.
- A2 gains its missing release face via a header-plausibility predicate (explicitly graded plausibility-not-proof for the 0857 regrade). §7.2 closes the plant-hook shape (three events, three actions, deterministic selection, one `pub(crate)` observation). Report identity pinned to what the committed e2e asserts. §7.3 lays the eight triplets out as a seven-column table with containment and debug-twin discrimination rules. §7.6: children are ordinary non-ignored tests that no-op unarmed, so byte-inertness is continuously executed.
- **Lane-scoped arming structural** (§7.1): never suite-global, never `set_var` (LazyLock ledger makes it a silent no-op that looks armed); child `Command` + `env_clear` + allow-list only. This is the invariant QA's W1 grep gate enforces.
- **0850 exact spec** (§9.1–§9.3): delete the private `read_i64` (13 call sites) and copied Vec offsets; delegate to `heap_access`/`vec_runtime`; derive tag/field offsets from `HeapHeader::SIZE`; adjacent `CLOSURE_DROP_GLUE_OFFSET` duplication folds only if zero-delta, else files. QA's byte-identical-RED invariance pin carried verbatim (§9.6).
- **Ruling 7** (§9.4): the rustdoc cleanup is the substantive half — four surviving accessors reference `reset_counts` and links would dangle. Rides the 0850 change-set.
- **0859** (§9a): short cross-reference only — existing detector surface as oracle, plant protocol explicitly not the instrument, begins after proofs land, protocol `/qa`-owned.
- Refreshed 9-row submodule matrix + 6-step serial order (step 1 precheck hoist gates steps 3–4).
- **Filed FIXME 0876** (`/arch`): BC §4b invariant 8 prescribes `reset_counts` at session start; ruling 7's removal makes the prescription actively wrong; doc fix rides the same window.

**Next skills:** `/dev`(intrinsics) per §10 order; `/arch` for 0876 + subtractive baseline approval; `/qa` 0857 regrade after step-6 records exist; `/review`(intrinsics) with §7.4 + §9.6 as reject criteria.

### `/design` (backend) — COMPLETE (2026-07-25)

Plan of record: `design/backend/transitive-drop-glue.md` (264→884 lines; §§1–6 are the S116 contract re-verified at HEAD, §§0/1.1/3.4/5.1/6.1/7–10 new); `backend.md` §8 rows updated.

- **As-built drift D1 (BLOCKING — why Waves 4–5 could not have run as designed):** the landed registry holds `&mut M` and so does `FnCompiler` — both cannot exist; and the registry is constructed *and finished* before body compilation. Resolution designed: reshape the registry module-borrow-free (module/symbol-tables become call arguments), `FnCompiler` gains a disjoint `glue` field, `finish()` moves after bodies. Mid-body definition proven safe from the existing capture path.
- **The glue census is five mechanisms, not two** (D3): `vec_codegen` mints a *second* named per-instantiation ADT glue under a backend-local mangle — same defect class, second identity scheme; it deletes with the inline emitter. A fourth unnamed inline consumer (`apply::emit_post_call_decs`) is absorbed by slice S1. Filed **0878** (`/qa`): the plan's grep-zero fence would pass with that second identity home alive — fence must extend.
- **D9 confirms the S116 per-arm plans and TCO predicate survive HEAD unchanged** — the S117 trait-identity work is whitespace-only across the five relevant backend files.
- **Serial slices S0–S6**: S0 registry reshape (behavior-neutral, invariance-pinned) → S1 `emit_typed_rc_dec` becomes the glue-call emitter → S2 0835 (**attribution-gated**, below) → S3 match per-arm (0782 ruled: var-pattern binder borrows; the release-gate deletes, the predicate survives for liveness) → S4 capture/curry (`CaptureRelease::Plain` → canonical glue) → S5 TCO (one pure `TransferOldOwner | Replace | BorrowedInvalid` predicate folding four HEAD fragments; two load-bearing fold constraints) → S6 deletion. After S1 the legacy emitter has exactly two call sites, so **the §8 atomic deletion (12 symbols/paths) is the final commit of S5's change-set** — satisfying arch ruling 10.
- **0835 finding (most wave-affecting):** no repro exists (no test, no PLAN row, absent from the 28-name baseline) — FIXME 0765's no-fix-without-repro rule blocks slice S2 as scheduled. Mechanism candidate read at HEAD: `marshal::sconcat` deep-incs every node/element, but intrinsics `consume_slist` returns at the first `old_rc != 1` node and never descends — a per-call leak proportional to list length, living in S116 ruling-2's *intrinsics consume-owner* inventory row, not the backend glue row. Filed **0877** (`/qa`) with a falsification recipe: attribution before S2; consumer migration does not reach it. Slice order otherwise unaffected.
- **FIXMEs 0760 and 0796 resolved and deleted** (design asks satisfied: site census explicit, curried reaching context folded in). Their acceptance obligations are transcribed into §7.4/§9 — notably 0796's real acceptance is *removing* the `curried_partial_application` balance-exclusion entry, not just flipping REDs #11–#13. The committed REDs are now the sole record/trigger.
- §9 records the armed-detector acceptance leg per slice (lane-scoped, cross-referenced to intrinsics §7.1).

**Next skills:** `/qa` (0877 attribution before S2; 0878 fence extension; confirm the 0796 exclusion-removal cell) → `/dev`(backend) per §7 with §8 deletion in S5's change-set → `/review`(backend) against §8/§11 reject criteria. W3 sequences after Track A's W2 (armed legs depend on 0848).

### `/design` (Binary/int + exe-bundle) — COMPLETE (2026-07-25)

Plan of record: `design/int/result-owner.md` (264→609 lines; §§1–5 semantics retained, seams re-cut onto HEAD); `s117-conformance-recovery.md` gains §6.5 (0863 delta note); `int.md` master reconciled; `CLAUDE.md` index rows added.

- **The 0745 wave shrinks: S117 already landed the fresh-JIT glue routing.** `SharedState.fresh_jit_drop_glues` is written by both publish paths as `{artifact, owner}` pairs; 0745 consumes, it does not build. The owner attaches at the two *execution* seams, not inside the turn transaction — so 0745 cannot destabilize W3a and leaves 0863's foundation untouched.
- Stale-assumption corrections: the S116 design named a seam with no production caller (`inline_jit_codegen_for_names` — test-only at HEAD, and it silently discards `drop_glues`; recorded as a `/dev` trap + `/review` reject); the "no global address map" claim is falsified by S117 and restated as three invariants; the shutdown hazard is de-rated to match HEAD (`/review` must not grade reordering as a safety Blocker; the real as-built fix is `main.rs:323-337` where shutdown precedes exit-code computation).
- **Absence-is-ambiguous ruling**: the glue projection emits no row for non-owning categories, so int classifies with the same public `HeapCategory::classify` predicate *before* any keyed lookup — a keyed miss is then a hard error; an int-side heap-type list fork is the resolver-mirror class, rejected.
- **Zero interface deltas confirmed** (§10): everything needed is already public; no types/`public-api.txt`/cache-schema change — the 23→24 window stays 0869's alone. Backend D1 reshape confirmed neutral here.
- **0863 §6.5 delta note**: preconditions re-verified still-holding-and-unmet (W3c removal was clean); two W7-introduced deltas recorded — seed classification must treat reserved-but-unpublished same-cluster cells as executable under absorption, and absorbed turns' compiled glues must move into the parent publish gate as `{artifact, owner}` pairs. Handoff order: 0745 lands *and reviews* first; the transaction functions themselves are untouched by 0745.
- FIXME 0747 verified backend-owned (left for a backend `/design` deployment). One rider owed to `/testing` with the flip: cell #15's `// defect:` locus line cites a falsified mechanism.

**Next skills:** `/dev`(int + exe-bundle) per §8 I0–I5 after backend W3; `/review` against §5/§7/§11; `/testing` re-locus rider; 0863 wave after 0745 per ruling 11.

### `/qa` reconciliation — COMPLETE (2026-07-25)

- **0877 ruled (a): 0835 is runtime-library-owned.** Both evidence legs: code-reading (`deep_rc_inc_slist` adds +1s no structural owner corresponds to; `consume_slist` is *correct* tree-ownership glue, so the interior +1s are undischargeable) and the falsification probe run live (4 fresh-tempdir subprocess sessions, RC_STATS armed: residual +3/+7/+6 scaling per-call and per-|ys| at constant type depth — the backend transitive-discharge hypothesis is falsified). Backend Track-B order becomes **S0→S1→S3→S4→S5→S6 with no waiting**. `/testing` lands 0835 repros A+B as abort-guarded W1 REDs (satisfies 0765); fix routes `/design`(intrinsics) → `/dev`(runtime pair) in the intrinsics windows. Honesty caveat recorded: the probe confirms the leak face; if the glibc abort face survives the runtime fix, that is a new attribution question.
- **0878 disposed**: the ruling-10 structural fence now greps-zero the second glue-identity home; `adt_instantiation_mangle` stays out of the fence (its deletion is conditioned in §8; a surviving consumer-less mangle is a `/review` dead-code catch, not a fence FAIL).
- **Plan deltas**: 0796's real acceptance (balance-exclusion entry removal) added to the flip change-set obligations; cell #15's `// defect:` re-locus rides I3; invariance pins extended to backend S0/S1; result-owner error-path negatives folded into the unit-matrix obligation; precheck-hoist sequencing note added (a positive failing before the hoist is a sequencing artifact, not detector evidence).

### `/design` (platform) — COMPLETE, /arch GATE PENDING (2026-07-25)

Plan of record: `design/platform/adt-marker-binding.md` (current-contract-only, right-sized; cited from `platform.md` §12). FIXME 0873 stays open with progress recorded (`blocked_on: /arch selection gate`).

- **Recommended (Option 3, minimal form):** an optional `adts:` key on `declare_platform!`'s schema arm emits each marker (struct + `impl CLAdtType`, author rustdoc preserved) plus a `const _: () = assert!(…)` against a new `pub const fn schema_declares_type` — a const byte-scanner beside `extract_layout_hash`, checking exactly the bytes the runtime parser sees. Name agreement becomes a **build error**, including for construct-only markers runtime never checks. Cost: one const fn + one macro arm + five call-site migrations; no new crate/dependency/`CLAdtType` change.
- **Derive rejected** (build dependency + second public surface on the external facade, and it *still* can't check the name without a second non-tracked source of truth). **Keep-explicit-impls rejected as primary** on a call-path asymmetry the audit hadn't separated: blocking effects are DLL-locally contained, but poll-shape leaves have no containment anywhere — a marker mismatch there is a process abort with no attribution, so "accept runtime failure with diagnostics" would first require poll-boundary containment (more work than the cure). Retained as documented fallback.
- Adjacent diagnostic defect recorded (rides the implementation): `resolve_field` misattributes a type-key miss as a field miss — the exact message a debugging author would read.
- **`/arch` gate delta**: one `public-api.txt` line + the `adts:` macro key as external-author surface; everything else unchanged. Implementation is S119+.

**Next skills:** `/arch` settles the selection at the Phase-3 exit gate; `/dev`(platform) implements S119+.

### `/arch` exit gate — PASS (2026-07-25)

- **0869 ruling authored**: `design/arch/trait-impl-cache-carrier.md` (binding). `WrittenTraitImpl { trait_name, impl_type, impl_module, methods, visibility }` as a serde-visible `SymbolTable` field (no serde-default; absence is a hard error), living in `cranelisp-types` — the only candidate public delta, landing with the implementation. Producer: typecheck's impl-check transaction success point, same resolved values as the D45 shell. Restore: one types-owned idempotent `enrol_written_trait_impl` (hard-error-on-divergence) + one hoisted `trait_impl_key` mint that also discharges the two hand-rolled `impl$` format sites. Schema 23→24 in the implementing change-set only; P7 second-home justification and five rejected alternatives recorded. FIXME 0869 open, ruling in force even if implementation defers.
- **0873 APPROVED (Option 3)** for S119+: one platform `public-api.txt` line + the `adts:` macro key; three conditions on the implementing change-set (grammar-coupling rustdoc both sides, baseline/rustdoc/BC-note same change-set, `resolve_field` diagnostic fix rides).
- **0876 resolved, 0768 actioned — both FIXMEs deleted.** BC §4b invariant 8 now records the *absence* of a reset seam as the load-bearing property. `safety-invariants.md` §4 vocabulary amended (cited capability proof required for `asserted`/`gated`/`dynamic-lane`); row re-audit in the same edit: R10/R13/R9 proven, R5 and R6 honestly downgraded to `asserted-but-unproven`, R8 deliberately awaits the 0857 regrade — the ruling-12 sequencing.
- **Interface set complete**: intrinsics subtractive-only; backend zero-delta (D1 reshape internal, consistent with S116 ruling 9 — only `finish()` moves, still before finalize); int/exe-bundle zero-delta; types zero-delta unless 0869 implements; typecheck zero even under 0869; platform S118-zero. 0877/0878 dispositions consistent with rulings 2/10; D2's STOP-and-FIXME escalation shape endorsed. 0872 remains in the `/arch` Phase-7 window.

## Waves (Phase 4 — organized 2026-07-25)

Source edits and test runs are serialized throughout; review rows are executed by the delegated Codex reviewer with the dispatching agent adjudicating (`.claude/commands/review.md` §Delegated execution). Armed-detector acceptance legs in W3+ depend on W2's detection proofs (0848).

### W1 — QA-first test surface (`/testing`, sprint-wide) — **COMPLETE 2026-07-25 (five commits)**

Baseline reconciliation of the two low-confidence cells from the captured log; 0835 repros A+B (abort-guarded, failing-not-ignored); the arming-discipline static grep gate; the extended ruling-10 fence cell (second glue-identity home included); 0726 tripwire cells; 0830 eliminator harness rows; 0867 polymorphic-accessor repro; remaining missing cells per `tests/plan/s118-test-plan.md` §2.3. Gate: intended REDs in place with correct polarity; 28-name baseline reconciled; `/qa` static check.

**Outcome.** Baseline verified at exactly 28 by focused per-binary runs (150 run / 122 passed / 28 failed across the eleven baseline binaries). Twelve new intended REDs landed with correct per-mechanism failure signatures plus six green discriminating controls; arming gate green; `cargo check --tests` clean; no ignores; no baseline renames. 0835's runtime attribution **confirmed** by repro B (+3/+7/+6 residuals reproduce `/qa`'s falsification table exactly); the abort face needs the `sconcat` ingredient (original two-cell repro A is green at HEAD, retained as control). Fence cell lists 7 surviving legacy symbols. Five baseline REDs (#5–#9) were failing for the **wrong reason** — stale pre-S116 nullary-constructor syntax was masking their real signatures behind parse errors; repaired, same names/colours, documented S115 mechanisms now reproduce exactly (same rot flagged untouched in `tests/agent.rs:4241`, agent-feature lane).

**Four reconciliation findings for `/qa` promotion (queued, not yet dispatched — user pause):**
1. **Baseline trade is not what the plan guessed**: `ms_p8_conj_leak::int_loop_control_balances_green` IS in the 28; the cell it displaces is #10 `…var_pattern_arm_consuming_owned_temporary_releases_it_once_linked` (0782), **green at HEAD with no fix landed** — a suspicious green needing the S98-rule investigation.
2. **The ambient 1143 prelude-load residue is an unowned defect.** All three `conj` cells and the M3 clean control (#23) actually measure a program-independent residual of exactly 1143 allocs whenever `CRANELISP_LIB` points at the real stdlib (0 with an empty prelude; conj's *marginal* residue over control is zero — the documented 0688 per-iteration signature is not what these cells read today). Neither 0848, 0745, nor Track-B glue names an owner for prelude-load residue: **cells #19/#20/#21/#23 cannot flip from Tracks A/B/W4 as planned.** Needs `/qa` attribution → likely a new FIXME and a flip-accounting amendment.
3. **0867 is wider than filed and mis-attributed**: the axis is not polymorphism — polymorphic forms mint accessors fine; a field list in a named constructor arm whose name differs from the type mints **no accessors at all** (every sum type, every distinct-name product; spec §5.2.6's own `Option.unwrap` example is non-conforming at HEAD). Invisibility cause: every prior guard used the one spelling that works — a coverage-by-definition-variants miss.
4. **0830's two planned harness rows don't reach the 0810 seam** (the repeater isolates frames); the third row `matched_in_tail_loop` — match *as* the loop body — is the one that goes RED. Landed all three; position axis now 12.

**Track C input:** the sibling-trait-impl cache guard silently passed once under a 4-binary interleaved run (6→5 failures), reproducibly red alone and in re-runs — the 0694 non-reproducibility family manifesting in a named cell.

**W1+ `/qa` promotion pass — COMPLETE 2026-07-25 (commit `abab7418`).** The ambient-residue attribution is **RULED: macro-expansion-execution residue on the 0835 marshal seam — the user's lead confirmed** by a five-step probe ladder (empty prelude 0; 8 real stdlib modules macro-free 0; `defmacro` defined-never-invoked 0; first invocation +2, two +4, larger argument +23; full stdlib 1143 — linear in expansion count and marshalled-sexp size, constant depth). Scope note appended to 0835 naming the prelude face; **binding W2b prediction: the consume-owner fix collapses the residual to 0** — W2b acceptance re-runs the P4 probe and `/testing` lands a prelude-face exact-balance cell in the W2b change-set. Flip accounting (plan §2.5, both branches): Branch H — #10/#19/#20/#23 flip at W2b, #21 needs W2b+W3; Branch F (residual survives) — five cells cannot flip from any scoped track and the scope question returns to the user at W2b's gate. Other dispositions: baseline §2.1 corrected name-for-name (0688's documented per-iteration signature is *absent* at HEAD — conj marginal residue is exactly zero; a suspicious green owed trace-to-mechanism at exit); **0867 re-attributed and retargeted to `/dev`(typecheck)** (owning seam: `synthesise_field_accessors` gated `if is_product` — the spec normatively requires partial sum accessors, no open /spec question); **0830 closed and deleted** (tail-loop frame-sharing lesson permanent in the risks lens); **0782's mechanism confirmed live in CLIF** (`/clif` shows both decrements still emitted — the green cell is layout-latency, not closure; 0782 closes only with fix + one-release IR evidence); the cache-guard flap is 0694's first inverse-polarity named member.

### W2 — Track A intrinsics (serial sub-waves)

**W2a** `/dev`(intrinsics) per `diagnostic-modes.md` §10 six steps — precheck hoist FIRST (step 1 gates 3–4), plant protocol, eight detection-proof triplets with per-row fail-on-revert records, then 0850 convergence + ruling-7 subtractive removal in one change-set → `/review`(intrinsics) with §7.4/§9.6 reject criteria.

**W2b `/design` — COMPLETE 2026-07-26** (commit `0274afc4`; plan of record `design/runtime/s118-structural-embedding-ownership.md`). **Ruled: head-only inc** — a helper embedding an existing heap structure by pointer takes exactly one `rc_inc` on the node it stores (invariant RE-1, primitives master #13; inc count per embed = 1 independent of size/depth). `consume_slist` unchanged (RE-2: consume glue structurally cannot discharge unowned references); deep-consume rejected on three grounds incl. it tears down genuinely shared tails. Seams S1–S4 all in `marshal.rs`: both call sites → nullary-safe `shallow_rc_inc`, **delete `deep_rc_inc_slist`**, rewrite the rustdoc that documents the defect as intent. Atomic traffic per embed drops 2|ys|+2 → 2. Coverage-miss finding: the seam's one unit row (`decision24_sconcat_rc_balanced`) sits exactly on the blind point — one-cell tail, bare tags ⇒ zero over-incs. **Abort face NOT explained by the over-inc** (surplus refs only delay frees): two candidates with opposite predictions — (i) a masked co-present premature-free (0810-B/0782 family; fix may make aborts *more* frequent) vs. (ii) the deep walk itself as the wild write (`fetch_add` at `addr+8` of a non-node; fix closes it). **Pre-fix detector plan D0–D4 is mandatory before S1** (the pre-fix state is unrecoverable): mode-divergence probe, RC_DEC_CHECK+precheck on the abort repros, M1 quarantine, M2 seam-name discrimination, post-fix M3. Acceptance §6: five 0835 REDs flip, P4 probe 1143→0 (Branch H binding), prelude-face cell rides the change-set, #10/#19/#20/#23 flip, armed re-demonstration; Branch-F contingency: fix stands regardless, remainder returns to /qa + user scope decision. **0879 and 0881 accepted-and-amended, deleted** (Layout-validity predicate canonical with residual recorded; first-hook-call timing canonical, pre-allocation seam rejected). **0883 filed** (/arch: RE-1 as safety-register row R14).

**W2a gate — PASS (re-review 2026-07-25).** 0880 resolved in `a934d62b` (27 sites; comment-only mechanically verified). The re-review checked the SAFETY arguments' *substance* against actual layouts/control flow (reads-before-dec, load-bearing tag tests, sole-owner frees, `free_io_branches` ordering) — all truthful. 0881 disposition concurred: Important, open, rides with 0879 into the W2b design dispatch. New Suggestion FIXME 0882: the W2a change-set introduced rustfmt drift in four files (adjudicator corrected /dev's "pre-existing, two files" framing against base — all four were clean at `d786ff80`); `/dev`(intrinsics) picks it up opportunistically. Evidence at gate: 320/320, guard 4/4, M3 pair as expected (#22 green, #23 on the known ambient residue). **Track A detector foundation is DONE; W2b opens.**

**W2a `/review` (first pass) — BLOCKED 2026-07-25 (first delegated review; flow verified end-to-end).** Codex (cli 0.145.0) reviewed the three-commit diff against §7.4/§9.6/arming criteria with adjudicator-supplied test evidence (320/320, guard 4/4, M3 pair as expected). Two findings, both verified at source before filing: **0880 (Blocker, /dev)** — the 0850 rewrite left `heap_access` unsafe blocks without per-site `// SAFETY:` comments (11 sites; behavior-preserving, mechanical fix; unsafe-audit rules admit no exceptions); **0881 (Important, /design)** — plant config-error timing fires at first hook call vs. the design's "before allocation" (never-a-partial-plant invariant holds; accept-and-amend vs. pre-allocation seam is /design's ruling, riding with 0879). All four flagged judgement calls concurred after verification (BYTES_PEAK removal = necessary completion of ruling 7; 0879's Layout-validity form catches both named faces). Disposition: 0880 fix → re-review; the Blocker does not hold W2b's design work.

**W2a `/dev` — COMPLETE 2026-07-25** (commits `cd935cae` hoist / `09c7f81e` plants+triplets / `64b4f1dd` 0850+ruling-7). All eight triplet rows committed green with recorded per-row fail-on-revert evidence (7 revert experiments; E6/E7 prove the *ordering* is load-bearing — reverting the hoist alone breaks A1/A2 with detectors present). **Baseline cell #22 (M3 positive detection) flips GREEN — first flip of the sprint**; #23 untouched per the ambient-residue record. 0850 invariance verified: eight affected binaries 22 RED/20 GREEN identical before/after; FIXME 0850 resolved and deleted after ~31 sprints of aging. Ruling-7 subtractive two-line baseline diff landed with grep-zero pin (judgement call flagged for review: the consumer-less private `BYTES_PEAK` CAS loop went with the accessor). Crate gate 320/320; clippy zero; arming-discipline guard 4/4. **FIXME 0879 filed** (`/design`): §7.5's literal alignment clause false-positives on ragged `HeapString` sizes; implemented the corrected Layout-validity form, fenced by a ragged-string clean control. Honest deviations recorded: plant config-error timing at first hook call; dead `PostFree.withheld` payload carried per contract. **W2b** 0835 runtime fix: `/design`(intrinsics) rules the consume-owner contract (head-only inc vs deep consume) → `/dev`(runtime pair) → `/review`. Gate: M3 e2e pair green; all eight triplet rows recorded; baseline REDs byte-identically unchanged by 0850/S-slices; 0835 repros green; `/qa` witnesses fail-on-revert and lands the 0857 regrade into the amended vocabulary.

### W3 — Track B backend consumers

`/dev`(backend) slices S0→S1→S3→S4→S5→S6 per `transitive-drop-glue.md` §7, review per slice group; the §8 twelve-symbol atomic deletion is the final commit of S5's change-set; extended fence cell green. Armed re-demonstration legs per slice. Gate: 0810 ×10, 0760/0796 REDs (+ balance-exclusion entry removal), TCO cells green in both toggles and required modes; grep-zero fence passes; no per-seam private releaser.

### W4 — Track B result owner (int/exe-bundle)

`/dev`(int + exe-bundle) I0–I5 per `result-owner.md` §8 → `/review` against §5/§7/§11. `/testing` re-locuses cell #15's `// defect:` line within I3's change-set. Gate: the three program-result REDs + cell #15 green across run/REPL/link; exact-once ordering pins; error-path negatives.

### W5 — Track C load characterization + certification (`/qa`-led)

0694 D1→D2→D3 with armed lanes; 0818 contamination experiment (cheap-first); `launch_grid` reduction; then certification: two identical captured deterministic full runs + ≥3 captured loaded runs. `conj`/exemplar cells verified as consequents of W2b/W3 (residual RED = new attribution). 0875 attribution after W4 (adjacent link seams).

### W6 — Track D (`src/`; capacity-conditional per the cut order)

0868 cache-hit lifecycle parity (`/dev`(src), schema-free); 0863 prepared-presentation transaction (`/dev`(src) → `/review`) strictly after W4 lands and reviews (ruling 11), rebasing on §6.5's two W7 deltas; 0869 implementation ONLY if capacity survives — `/arch` types change-set (carrier + helper + schema 23→24) then `/dev` narrow for the typecheck/int seams.

### W7 — Track E platform slice

`/dev`(platform): 0870 facade repair + 0874 shared fixture (doc/test-support only; zero-delta). May run opportunistically in any serialization gap after W1. 0873 implementation is S119+ (approved with conditions).

### W8 — Phase 5 gate

`/qa` evidence reconciliation (name-for-name flip accounting, no unexpected regressions); `/arch` public-API re-gate (intrinsics subtractive diff; all other baselines zero-diff; types/schema only if 0869 shipped); full `cargo nextest run --no-fail-fast`; open-FIXME wave-gate scan. Then Phase 6a/6b + `/audit`(cranelisp-types) and Phase 7 close with the user.

## Dispatch log

| Wave | Agent | Surface | Model | Effort | Non-default reason |
|---|---|---|---|---|---|
| P2 | /arch | sprint-wide scope review + standing questions a–f | fable (shim) | xhigh | — |
| P3 | /qa | sprint-wide test plan (`tests/plan/s118-test-plan.md`) | fable (shim) | xhigh | — |
| P3 | /design | cranelisp-intrinsics: diagnostic-modes refresh (0848/0850/0859 + rulings 2/3/6/7) | opus[1m] (shim) | high | — |
| P3 | /design | cranelisp-backend: transitive-drop-glue consumer-migration refresh (Track B + ruling 10) | opus[1m] (shim) | high | — |
| P3 | /design | Binary/int: result-owner refresh (0745) + 0863 sequencing check | opus[1m] (shim) | high | — |
| P3 | /design | cranelisp-platform: marker-binding ergonomics (0873, Track E) | opus[1m] (shim) | high | — |
| P3 | /qa | reconciliation: 0877 attribution, 0878 fence, plan deltas vs. refreshed designs | fable (shim) | xhigh | — |
| P3 | /arch | exit gate: 0869 carrier ruling, 0873 selection, 0876/0768, interface-set sign-off | fable (shim) | xhigh | — |
| W1 | /testing | sprint-wide RED surface: reconciliation, 0835 repros, arming gate, fence, 0726/0830/0867 | opus[1m] (shim) | high | — |
| W1+ | /qa | promotion pass: ambient-residue attribution (user macro-expansion lead), #10 green, 0867/0830 dispositions | fable (shim) | xhigh | — |
| W2a | /dev | cranelisp-intrinsics: precheck hoist, plant protocol, 8 detection triplets, 0850 + ruling-7 | opus[1m] (shim) | high | — |
| W2a | /review | cranelisp-intrinsics: three-commit Track A change-set | codex (delegated) + fable adjudicator | high | first production delegated review |
| W2a | /dev | cranelisp-intrinsics: 0880 SAFETY-comment fix | opus[1m] (shim) | high | Blocker resolution |
| W2a | /review | cranelisp-intrinsics: re-review after 0880 (delegated) | codex (delegated) + fable adjudicator | high | Blocker re-review |
| W2b | /design | cranelisp-intrinsics: 0835 consume-owner contract + 0879/0881 rulings | opus[1m] (shim) | high | first dispatch stalled at startup (harness watchdog, no work done, tree clean); re-dispatched |

## Notes

- 2026-07-25: Phase 1 draft authored from the S117 close record, the verified 28-RED baseline, `audits/cranelisp-platform-s117.md`, and the user's direction: instrumentation central, clearing failing tests the goal. The user's clarification that allocator instrumentation is correctness work (not security-sensitive) is recorded as standing context; it removes the S117 deferral rationale for 0848/0850/0857/0859 and the ownership waves.
- 2026-07-25: `/review` delegation to Codex ratified and validated pre-sprint (commit 46c9a0b3). This sprint's review rows are the first production use; dispatch log records reviewer identity per row.
- 2026-07-25: Phase 1 COMPLETE. USER approved scope as drafted (Tracks A–D + cut order + 0850 ships). USER accepted all five platform-audit recommendations; R4 pulled into S118. Filed 0870–0874 (audit) and 0875 (exemplar Link parity). Track E added. Advanced to Phase 2 architecture review.
- 2026-07-25: Phase 2 COMPLETE. `/arch` PASS AFTER REQUIRED REVISIONS; R7 (ruling-5 API removal into Track A) and R8 (cut-order split) transcribed and applied. Key rulings: 0869 carrier ruling is an S118 deliverable with schema 23→24 in its own window (no other track bumps schema); 0859 uses the existing detector surface, no new seam; the instrumentation-first inversion is confirmed sound with lane-scoped arming only; Track B's atomic legacy-emitter deletion is architecturally binding (P8 bridge closes this sprint). Advanced to Phase 3 design; `/qa` test plan dispatched first, then serialized narrow designs (intrinsics, backend, int, platform) and the `/arch` 0869 carrier ruling.
- 2026-07-25: USER directed a pause after W1 `/testing` completes — record W1's outcome, commit, and hold before any W2 dispatch.
- 2026-07-25: USER resumed the sprint with a directed attribution lead for the ambient 1143 prelude-load residue: the only code that *executes* during prelude load is macro expansion, so the leak likely lives in macro-expansion executions. `/sprint` notes the convergence with 0835's confirmed mechanism (the sconcat/SList marshal path IS the macro-expansion data path) — testable prediction: the W2b runtime fix reduces the residual. Routed to `/qa` for the promotion pass.
- 2026-07-25: W1 COMPLETE; sprint PAUSED per user direction. Queued next actions (in order, not dispatched): (1) `/qa` promotion of the four W1 reconciliation findings — most materially the unowned ambient 1143 prelude-load residue, which blocks the planned flips of #19/#20/#21/#23 and needs attribution + likely a new FIXME; the #10 suspicious-green S98 investigation; the 0867 re-attribution; (2) W2a `/dev`(intrinsics). The ambient-residue finding may warrant a scope conversation: it is a real, previously-invisible leak (~1143 allocations per session from prelude load) that no current track owns.
- 2026-07-25: Phase 3 COMPLETE, exit gate PASS. Every design pass caught a would-have-failed-in-implementation defect: intrinsics precheck-hoist (§7.5), backend registry borrow conflict (D1), int stale seams + the S117-already-landed glue routing, platform poll-frame containment asymmetry. `/qa` empirically re-attributed 0835 to the runtime pair (falsification probe: residual scales with list length, not type depth) — backend order S0→S1→S3→S4→S5→S6, no waiting. `/arch` authored the 0869 carrier ruling, approved 0873 Option 3 (S119+), resolved 0876, actioned 0768 with an honest register re-audit. FIXME motion this phase: filed 0876/0877/0878, resolved 0877/0878/0876/0768, resolved-by-design 0760/0796, retargeted 0835. Phase 4 waves organized; advanced to Phase 5; W1 `/testing` dispatched.
