# Sprint 118: Instrumented Ownership Closure

**Status**: PHASE 3 DESIGN

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
| 0850 | /dev(intrinsics) | Track A must-ship | Aged past 2× escalation; user-confirmed ship. |
| 0859 | /qa → narrow owners | Track A | ProjectionOf production witness via the smallest admissible instrument. |
| 0835 | /dev(backend) | Track B first consumer | SList construction; arch-ruled migration order. |
| 0810 | /dev(backend) | Track B must-ship | All ten match-scrutinee cells. |
| 0760 / 0796 | /dev(backend) | Track B must-ship | Capture/curry teardown through capture-glue builder. |
| 0745 | /dev(src+exe-bundle) | Track B must-ship | Program-result owner; design of record exists. |
| 0782 | /dev(backend) | Track B | Var-pattern arm double-release — same consumer family. |
| 0694 / 0604 / 0818 | /qa | Track C | Load-dependent characterization with armed detectors. |
| 0863 | /design → /dev(src) | Track D | Prepared-presentation transaction; user-committed to S118. |
| 0867 | /testing | Track D | Permanent polymorphic-accessor repro. |
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

_Pending Phase 2._

## Waves (Phase 4)

_Pending Phase 3. Indicative shape, serialized as always: W1 `/testing` (baseline reconciliation + missing detection-proof/0867 cells) → W2 intrinsics D/D/R (Track A) → W3 backend D/D/R (Track B consumers) → W4 int/exe-bundle D/D/R (0745) → W5 `/qa` certification + Track C → W6 src/ (Track D) → Phase 6._

## Dispatch log

| Wave | Agent | Surface | Model | Effort | Non-default reason |
|---|---|---|---|---|---|
| P2 | /arch | sprint-wide scope review + standing questions a–f | fable (shim) | xhigh | — |

## Notes

- 2026-07-25: Phase 1 draft authored from the S117 close record, the verified 28-RED baseline, `audits/cranelisp-platform-s117.md`, and the user's direction: instrumentation central, clearing failing tests the goal. The user's clarification that allocator instrumentation is correctness work (not security-sensitive) is recorded as standing context; it removes the S117 deferral rationale for 0848/0850/0857/0859 and the ownership waves.
- 2026-07-25: `/review` delegation to Codex ratified and validated pre-sprint (commit 46c9a0b3). This sprint's review rows are the first production use; dispatch log records reviewer identity per row.
- 2026-07-25: Phase 1 COMPLETE. USER approved scope as drafted (Tracks A–D + cut order + 0850 ships). USER accepted all five platform-audit recommendations; R4 pulled into S118. Filed 0870–0874 (audit) and 0875 (exemplar Link parity). Track E added. Advanced to Phase 2 architecture review.
- 2026-07-25: Phase 2 COMPLETE. `/arch` PASS AFTER REQUIRED REVISIONS; R7 (ruling-5 API removal into Track A) and R8 (cut-order split) transcribed and applied. Key rulings: 0869 carrier ruling is an S118 deliverable with schema 23→24 in its own window (no other track bumps schema); 0859 uses the existing detector surface, no new seam; the instrumentation-first inversion is confirmed sound with lane-scoped arming only; Track B's atomic legacy-emitter deletion is architecturally binding (P8 bridge closes this sprint). Advanced to Phase 3 design; `/qa` test plan dispatched first, then serialized narrow designs (intrinsics, backend, int, platform) and the `/arch` 0869 carrier ruling.
