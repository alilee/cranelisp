# Sprint 114: Typed Resolution Carrier + Settlement-Consumer Drain + Binding-Indirection Contract

**Status**: PHASE 5 LANGUAGE (ACTIVE)

**Goal**: Retire the S113 attributed-carry ledger (31 suite REDs) by landing the typed local/global resolution carrier (0653 prong 3), the settlement-consumer typecheck pass, the backend binding-indirection consume contract (0668/0669/0664), and the src/frontend defect drains — with the frontend-s113 audit disposed and its accepted recommendations actioned.

**Audit**: cranelisp-typecheck (FIRMED Phase 4 — last assessed S108; this sprint's heaviest surgery; /arch endorsed)

## Scope

Five tracks, all defect-drain or class-closing — no new language surface. Every suite RED at S113 close is either scheduled here or carries with explicit rationale.

### A. Typecheck: 0653 typed carrier + settlement-consumer family (anchor)

The S113 finding: the check-gate-leak class (×3 in one sprint) and the `Option<FQSymbol>` conflation are one story; the user's prong-3 directive (typed `Ref::Local | Ref::Global` closed sum — "unresolved" gets no constructor) is the structural close.

- **0653** three prongs: /arch ratification (P24 corollary + phase-boundary completeness gate), the typed-Ref carrier change, and the sweep it enables.
- Drain the ×10 typecheck REDs: F-D2-10 ×4 (nullary no-impl check-gate-leak — prong-3 evidence), MC-X4 + MC-X4b (P26-temporal consumer harvest; two faces fence partial fixes), MC-X5 (raw-name overload gates), MS-P7 (`--link` divergence — red-flag class: call-chain evidence before fix, per S98/S102 discipline), 0641 I-1 ×2 (capture let-alias), PS-SH1 (multi-sig value-ref matrix residual).
- **P26 full typecheck sweep** (carrier→pass→window classification, carried from S112 Phase-1 candidacy).
- **0553** (deferred, /typecheck): actioned in this track only if the carrier work reaches its seam ("W5-if-deep" per S113 close); deferral stands otherwise.

### B. Backend: binding-indirection consume contract

- **/design(backend) iteration** (the S113-named anchor): ONE pre-COW binding-indirection consume contract (0668), the family-pins + B-2 toggle-off face gap (0669), and **0664** reconciliation (§13.7 producer-seam inc was falsified in-sprint; the R14 count-truth ruling superseded it — the design doc must record the settled contract and retire the unsound fix shape).
- Drain the ×7 backend/intrinsics REDs: binding-indirection consume family ×3, F-R1 teardown fixed-residual ×2, MS-P8 conj/assoc leak ×2 (the 0408 never-freed face).

### C. src/: 0638 + persistence riders + 0604 escalation

- **0638 macro-alias double-free ×5 — MUST ship.** Attributed since S111, never wave-scheduled across two sprints; now mode-face-pinned both ways. Scheduling it is the point of this line.
- PS-D1 ×1 (0671 impl-confirmation display face), riders **0674** (startup restore notice) + **0675** (cheatsheet multi-sig settled facts).
- **0604** (index-feed → foreground-writer race, /qa, filed S109): 2×+ carry — **SCHEDULED this sprint** (user approved Phase 1, 2026-07-20; same shared-state-isolation story as the resolution-carrier theme).

### D. Frontend: BD-A family + audit-accepted recommendations

- Drain the ×7 frontend REDs: BD-A ascription family ×6 (one-seam fix shape recorded in S113), deftype-ctor trailing ×1 (pre-existing).
- **0660** enumeration completeness (/design(frontend): ctor/field/platform binder rows across all three sides — the (b) enforcement already landed S113).
- **0670** (/arch): int macro-pass qualifies local binders — blocks the value-level binder-reject seams; ruling here unblocks that residual.
- Frontend-s113 audit recommendations accepted at Phase 1 (disposal below).

### E. Cross-cutting inventories + user-facing debt

- **0652** (/arch keyed-consumer inventory) + **0590** (resolver-mirror convergence onto mint capability, /design) — the two S114-slated structural sweeps; P24 register frontend leg.
- Archive-demo de-rot continuation (18 classed demos remain).
- "in expansion of" on the def/const finalize path (S113 carry note).

### Out of scope

- **SROA / register-resident loop-locals + `--release` LLVM tier** — the standing frontier; next user-directed track after the drain.
- **0637** (borrowed-sibling slot-cache validation) — parked to first consumer with co-landing rule; trigger unmet.
- **0463 / 0050 / 0052** — deferrals stand (triggers unmet; targets /examples, /int, /repl).

## FIXME debt

| FIXME | Target skill | Status | Notes |
|---|---|---|---|
| 0653 | /arch | RESOLVED P3 | Ratified + carrier landed dormant; implementation = Track A waves |
| 0668 | /design (backend) | RESOLVED P3 | Contract designed (`binding-indirection-consume.md`); FIXME deleted |
| 0669 | /qa | RESOLVED P3 | Verdict: I-1 capture face → 0668 backend family; FIXME deleted |
| 0664 | /design (backend) | RESOLVED P3 | §13.5/§13.7 reconciled to R14; FIXME deleted |
| 0688 | /qa | RESOLVED P3 | Both BACKEND (run-discriminated); seams named; plan §2.1 durable record; FIXME deleted |
| 0689 | /arch | open | W2 review Important-1 — single-source concreteness predicate + fence (before P5 close) |
| 0660 | /design (frontend) | RESOLVED P3 | All three sides + 4 impl cells verified landed; FIXME deleted |
| 0670 | /dev (src) | open (ruled, re-targeted P3) | Track C — int fix → frontend reject → /testing cells |
| 0683 | /spec | RESOLVED P3 | §5 binder-position wording aligned to 0670 ruling; FIXME deleted |
| 0671 | /dev (src) | open | Track C — PS-D1 display face |
| 0674 | /dev (src) | open | Track C rider |
| 0675 | /dev (src) | open | Track C rider |
| 0604 | /qa | open (plan of record set P3) | Track C — census + freeze chokepoint; retires when guards land |
| 0676 | /qa | RESOLVED P3 | Standing matrices drawn in plan §5.1; FIXME deleted |
| 0677 | /dev (frontend) | open | Track D — audit R2 one qualified-name splitter |
| 0678 | /dev (frontend) | open | Track D — audit R3 single head classifier (3rd carry, accepted) |
| 0679 | /dev (frontend) | open | Track D — audit R4 shared synthetic-Sexp kit (3rd carry, accepted) |
| 0680 | /dev (frontend) | open (re-scoped P3) | Design half DONE; remaining: plan-frontend.md peg + defmacro.rs rustdoc |
| 0681 | /dev (frontend) | open | Track D — audit R6 hygiene batch |
| 0682 | /spec | RESOLVED P3 | Ruling scribed (§1.4.5/§2.3.8/§2.4/§2.8.3/§8.5.1); FIXME deleted |
| 0684 | /arch | RESOLVED P3 | Principle 16 bullet reconciled (user-directed immediate); FIXME deleted |
| 0685 | /arch | RESOLVED P3 | `synthetic_local_from_expr` landed dormant (option b, hardened); FIXME deleted |
| 0686 | /spec | RESOLVED W1 | `/bar` enumerated in §8.5.1 + §2.4 mirror; division fence reaffirmed; FIXME deleted |
| 0687 | /qa | RESOLVED P3 | RA-N6 `/bar` cell added (plan §5.2); FIXME deleted |
| 0652 | /arch | RESOLVED P3 | Doc-currency update landed; FIXME deleted |
| 0590 | /design | open | Track E — resolver mirrors → mint capability |
| 0637 | /design | open | Parked to first consumer — deferral stands |
| 0553 | /typecheck | deferred | Track A W5-if-deep only |
| 0463 | /examples | open | Deferral stands (trigger unmet) |
| 0050 | /int | deferred | Deferral stands |
| 0052 | /repl | deferred | Deferral stands |

## Audit disposal (frontend-s113, METHOD §2.6) — DECIDED

**User (2026-07-20): all seven ACCEPTED.** FIXMEs filed: R1→0676, R2→0677, R3→0678, R4→0679, R5→0680, R6→0681, R7→0682. Disposition trail appended to `audits/frontend-s113.md` §4. R7's embedded normative question (space-separated `: Name` / `:foo/`-degradation: conformance cells vs tolerated leniency, spec §1.4.5/§2.4) described to the user at Phase 1; user ruling pending on /qa's framed cells.

## Architecture review (Phase 2)

**Verdict: SIGN-OFF WITH REVISIONS** (/arch, 2026-07-20). Five-track scope coherent and correctly debt-weighted; revisions are sequencing constraints + two attribution gaps + explicit naming of implied work items. Nothing blocks Phase 3.

### Findings

- **F1 — 0653 carrier lands BEFORE the F-D2-10 gate-leak drains (Principle 8).** Draining those ×4 pre-carrier authors exactly the interim gate patches the `Ref::Local | Ref::Global` constructor obsoletes (the S82 accessor-stopgap pattern P20 retired). The F-D2-10 fixes RIDE the carrier change-set; any sweep is a migration aid, never the enforcement mechanism (= ratification wording).
- **F2 — Don't artificially serialize the other typecheck REDs behind the carrier.** MC-X4/X4b, MC-X5, PS-SH1, I-1 are inference/harvest defects orthogonal to the Ref shape — drain before/interleaved. The P26 sweep + 0653 helper-classification sweep run AFTER the carrier (the reshape changes the inventory they classify; the helper sweep IS the carrier's acceptance check).
- **F3 — Attribution overlap: I-1 capture face + let-bind alias claimed by both Tracks A and B.** The 0669 /qa disposition must run BEFORE Phase 4 wave assignment, else two skills patch one seam from both sides (the P7 mirror class).
- **F4 — Scope gap: the B-2 analysis-on fix is a TYPECHECK change-set** (match-var-pattern escape-recording bug, per 0664's landing record). The 0668 backend contract must NOT attempt a backend-side workaround (R14: the backend gate is correct and cannot distinguish wrong-`Some(false)`). Named as explicit typecheck work; joins the Track A deployment. Escape-fact correction is cache-visible → F7.
- **F5 — MS-P7's Track A placement is provisional.** 0664 localizes the divergence to the per-turn-JIT vs ObjectModule mode seam — may attribute to backend or int. Call-chain evidence first, then attribution, then wave assignment (S98/S102 discipline).
- **F6 — 0664 reconciliation has two halves**: (1) /design(backend) corrects §13.5/§13.7 inside — and logically FIRST within — the 0668 contract deployment; (2) /arch refreshes the stale R14 register row (`safety-invariants.md:208`) to honest partial status — /arch takes this in Phase 3 (P25).
- **F7 — ONE schema-bump window** (currently 21): the carrier reshape (serde-visible on persisted `codegen_view`) + the B-2 escape-fact correction (stale cached `Some(false)` would reproduce the UAF post-fix) coordinate into one bump, not two invalidation events (S111 0621 precedent). Rider: types-crate CLAUDE.md says "currently 16" — stale; /arch fixes in Phase 3.
- **F8 — 0670 chain explicit**: /arch ruling (Phase 3) → int fix (src-surface, Track C resident — Phase 4 must place it) → frontend value-level reject re-lands → /testing cells. Three waves, strict order.

### Required sequencing (Phase 4 must honor)

1. Phase 3 rulings (0653, 0670) gate their dependent waves.
2. Carrier change-set = ONE coordinated multi-crate wave (types + typecheck producer + backend consumer + schema bump; serial handoffs, never split across a wave gate).
3. Carrier → F-D2-10 (rides) → P26 + helper sweeps (after, as acceptance).
4. 0669 /qa disposition before the 0668 /design(backend) + any consume-seam /dev wave.
5. 0664 §13.5/§13.7 correction first-within the 0668 design deployment.
6. B-2 fix = typecheck work; MS-P7 wave assignment gated on call-chain evidence.
7. Both bump-worthy changes in one schema window.

### Public-API assessment

Carrier blast radius measured: `resolved_target` ×368 across 59 files but structurally narrow — producer cranelisp-typecheck, consumer cranelisp-backend (`compiler/apply.rs` dense, 12 refs incl. S25 TCO keyed read), **zero refs in src/** (boundary confirmed right). /arch resolves in Phase 3: (a) `Ref::Local` carries binder identity, slot mapping stays backend-side; (b) Apply-side sum models its third legal `None` ("identity rides the callee Var") separately from the Var-side sum — no shared shape re-smuggling ambiguous `None`; (c) prong-3 residuals (mono_expr sentinel, string-embedded mangles) stay helper-sweep audit items. **Confirmed: /arch updates crates/cranelisp-types in Phase 3** (mono_expr reshape, public-api.txt regen, interfaces.md, bump per F7).

### Rulings + scope adjustments

Both /arch rulings (0653 ratification, 0670) confirmed Phase 3 items, **neither needs user input** (shapes already user-directed; residual forks architectural). 0670 inclination: path 1 (int qualification pass skips binder slots — a binder is never a reference), with a spec-accuracy FIXME → /spec on §5's reader-reject claim (wording, not semantics). Adjustments: ADD B-2 typecheck fix + 0670 int-fix item + R14 row refresh (named, not new scope); **0652 pulled into Phase 3** (/arch doc-currency, zero interface consequence — off Track E's wave budget); **0590 sequenced LAST among typecheck deployments** — if carrier+drain consume the sprint it defers with a note that its `_hkt` never-error `Named` arms are a latent-defect suspicion left open. Audit rotation cranelisp-typecheck: supported. Cut: nothing.

## Skill plans (Phase 3)

### /arch — DELIVERED (2026-07-20)

- **0653**: P24 corollary ratified (`design/arch/principles/24-resolve-once.md` §Corollary); carrier design authored as `design/arch/typed-resolution-carrier.md` (binding for the typecheck/backend deployments). Types code LANDED DORMANT: `VarRef::Local{binder,binding_span} | VarRef::Global(FQSymbol)` + separate `ApplyRef::Dispatch(FQSymbol) | ApplyRef::ViaCallee` closed sums in `mono_expr.rs` (additive; workspace compiles; types tests 205/205). The FIELD FLIP is a pinned patch plan (doc §4): flip + total typed `var_refs`/`apply_refs` maps + `from_expr` `Unresolved{span,name}` arm + `CACHE_SCHEMA_VERSION` 21→22 — bump deliberately NOT taken yet; ONE window shared with the B-2 escape-fact fix (F7). **FIXME 0653 deleted** (arch asks done; implementation prongs = Track A waves).
- **0670 RULED path 1**: int's expansion-pass qualification skips binder slots (a binder is never a reference). FIXME **re-targeted /dev (src, Track C)**: int fix → frontend §5 value-level reject re-lands → /testing cells; mandatory expansion-seam unit test named. **0683 filed** (/spec — spec §5 reader-reject wording not as-built; accuracy only).
- **R14 row** in `safety-invariants.md` refreshed to honest partial (B-2 + MS-P7 carry). **0652 actioned + deleted** (`backend-keyed-consumer.md` §3 S25 row + fp2 note).
- Handoffs: /design(typecheck) reads carrier doc §3–§5 + P24 §Corollary; /design(backend) reads §4 + keyed-consumer §3 + R14 (0664 reconciliation first-within 0668; contract must NOT absorb B-2; MS-P7 gated on call-chain evidence).

### /spec — DELIVERED (2026-07-20)

- Ruling scribed: §1.4.5 (`^`-style reader macro, whitespace tolerance, type-expression constraint, dangling-qualifier error), §2.3.8 + §2.8.3 (annotation wording made whitespace-tolerant + consistent), §2.4 (symbol well-formedness), §8.5.1 (both-halves-non-empty as two bullets: bare-`/` MUST-NOT-over-reach fence + dangling-qualifier located error in every position). All `[S114]`-annotated. §5 binder-position wording aligned to the 0670 ruling (accuracy only). RA rows RA-P1/P2, RA-N1..N5 all have spec anchors (mapping in /spec's return).
- **0682 + 0683 deleted.** No open questions — checked the bare-colon "field separator" fork; §4.10/§2.8.3 already treated spaced `: (Option Int)` as annotation introduction, so no contradiction.
- Residual flagged → **0684 filed** (/arch): Principle 16's dangling-`foo/` pass-through bullet superseded (intent stands; wording conflicts). Frontend CLAUDE.md's mirror statement is /dev(frontend)'s at RA-row time — carried in the Phase 5 wave brief.

### /design × cranelisp-typecheck — DELIVERED (2026-07-20)

- **NEW `design/typecheck/typed-resolution-carrier.md`** (producer-side pass plan, subordinate to monomorphisation.md) + typecheck.md §10 row + §9.7 sequencing + CLAUDE.md index.
- **Flip change-set boundary confirmed**: types (field flip + `MethodResolutions` split + `from_expr`→`Result<_, ViewBuildError{NotConcrete, Unresolved}>` + 0685 resolution) + typecheck (chokepoint totality, provenance via per-frame `Vec<Span>` on ScopeStack ×6 seams, ~30 write-site re-targets, F-D2-10 rides) + backend exhaustive matches + schema 21→22 — ONE atomic wave; tree doesn't compile between parts.
- Key decisions: self-recursion stays `VarRef::Global` (0616 regression guard); `ViaCallee` recorded positively (absence = Unresolved = defect); `Unresolved` vs `NotConcrete` split is the crux (conflation re-opens the gate-leak class one level up); **F-D2-10 fixed at the dispatch chokepoint via settled-state re-resolution** (holds the trait identity + located error; carrier totality obligates the fix; view-build gate = safety net); PS-SH1 = value-position mirror of §11.8 Ruling 5 overload-gate-bypasses-local-scope.
- **0685 filed → /arch (BLOCKS the types half of the flip wave)**: the lenient synthetic all-local ctor/accessor bodies (adt.rs) are a legitimate-miss population — arch pins the sanctioned shape (direct construction vs named `synthetic_local_from_expr` all-local entry; designer inclines (b)).
- **~3 dev waves**: A = atomic carrier flip (+F-D2-10+B-2); B = orthogonal drain (MC-X4/X4b/X5, PS-SH1), not flip-gated; C = P26+0653 sweeps as acceptance; 0590 defers-if-squeezed (structurally disjoint: type-position resolver family); MS-P7 waveless until its evidence brief attributes.

### /design × cranelisp-backend — DELIVERED (2026-07-20)

- **0664 reconciled FIRST then deleted**: §13.7 SUPERSEDED banner (falsified producer-inc retracted; R14 two-halves contract operative: toggle-off all-Owned restore + analysis-on escape-gated inc; falsified analysis retained as correction record); §13.5 negative-cell claim corrected Var-source-only + escape axis added.
- **NEW `design/backend/binding-indirection-consume.md`** (0668 → resolved+deleted): ONE provenance-based consume contract — ownership at consume/cleanup sites decided by operand provenance traced through binding-indirection to a live-binding root, never immediate-node syntax; purely structural, so correct in BOTH toggle states by construction. Three emission rules off one shared classifier: R1 alias-binding registers non-owning (fixes G double-scope-dec); R2 consuming inc at every escape store/capture position (extends to closure capture → the re-attributed I-1 face, ctor field store); R3 forwarding suppresses temp-dec (fixes F, B-cow, B-2 toggle-OFF face). Explicitly does NOT absorb B-2 analysis-ON (typecheck, F4). Collapses the three fn-return patches.
- **backend.md §2.7.2**: consumer-flip backend specifics (exhaustive matches, `is_self_call` on `VarRef::Global`, hard-fail scope-miss).
- **F-R1/MS-P8**: leak-direction, mechanisms distinct from the UAF family; seam attribution genuinely unsettled backend-vs-intrinsics; fix-shape hypotheses + RC_TRACE discriminators recorded → **0688 filed (/qa adjudicates BEFORE Phase 4 assigns the wave)**.
- **Dev-wave map**: W-B1 shared classifier → W-B2 (BI-G) → W-B3 (BI-I1 ×2) → W-B4 (BI-F, B-cow ×2, C-off) → W-B5 patch collapse; Track A consumer flip separate. Consume family INDEPENDENT of the carrier flip (only file-level coupling at match_codegen.rs — serialize change-sets, no wave-gate ordering).

### /design × cranelisp-frontend — DELIVERED (2026-07-20)

- **NEW `design/frontend/enforcement-matrices.md`** (0676 M1 + RA standing matrices anchor); `binder-head-reject.md` §3.3/§8 record the 0660 family LANDED + new §3.4 (value-level re-landing, 0670-gated); frontend.md corrected (§2 false re-export claim, fresh counts, §4.3 overview, §9 register + §9.1 narrowing ruling); CLAUDE.md "What to Document" rewritten (PEG + macro-expander removed — both false); R5 prune executed (3 stale docs deleted to git history).
- **RA enforcement**: dangling-qualifier reject lives AT THE READER, single-sourced — the S87 F5 dotted-loop consolidation into ONE fallible `consume_dotted_module_path` makes `read_qualified_tail` propagate located errors (both swallow sites vanish free); `/bar` = new `read_operator` guard (fires only on exact `/` + next-byte symbol-start, so bare `/` division stays legal); RA-N5 (bound form must be a type) at `try_consume_annotation` (bare-`:` arm hard-errors on `build_type_expr` failure). Space tolerance CONFIRMED already-sanctioned — pins only.
- **BD-A one-seam**: all 4 unrouted body sites adopt ONE shared `build_body_to_end` (= `build_one_expr_at` + consumed-to-end) — flips the §2.2 six cells + satisfies the M1 structural grep; deftype-ctor trailing = the constructor-position sibling.
- **0660 DELETED** (all three sides + all 4 implementation cells verified landed). **0680 re-scoped → /dev(frontend)**, kept open (design half done; remaining: plan-frontend.md peg claim + the losing defmacro.rs narrowing rustdoc per the §9.1 ruling).
- **Flags**: (1) plan-vs-source drift — M2 `build_type_head` case-reject + the 0660 rejects ALREADY LANDED (W3/S113), so /testing's Stage-1 live-RED verification must reconcile the M2/§5.3 accounting; (2) `/bar` guard changes `/bar` from two tokens to an error — /dev+/testing confirm no corpus fixture relies on adjacent-`/` division (whitespaced form is fenced by RA-N4).
- **Dev-wave map**: W-D1 (independent: BD-A seam + ctor trailing + RA reader consolidation + RA-N5) → audit-FIXME batch (0677/0678/0679/0681/0680-remaining; 0677 rides close to W-D1) → W-D2 (0670-gated: value-level reject re-lands + NOTE/mirror-sentence retirement).

### /design × src/ — DELIVERED (2026-07-20)

- **Three NEW `design/int/` docs**: `macro-marshal-rc-protection.md` (0638), `expansion-qualification-scope.md` (0670), `prelude-table-write-isolation.md` (0604 contract); plus `macro-diagnostic-reanchoring.md` §2.1 ("in expansion of" finalize site), int.md §16.1 design-of-record, CLAUDE.md index.
- **0638 mechanism**: marshal-boundary RC-protection defect — `invoke_clause` protects only the TOP-LEVEL cell of each macro arg (+1), but the marshaller retains the WHOLE tree and clauses consume interiors deeply; 0638's clause returns a deep interior alias → interiors freed to 0 while still reachable → reuse ping-pong → double-free. The committed GREEN negative-control twin proves clause codegen nets exactly one dec/cell, so the fix is exactly +1 on EVERY cell (deep protect-on-build in marshal.rs) — provably sufficient, not a masking floor. Discriminator first (RC_TRACE + quarantine pin of first freed-while-reachable cell), then five-pin re-run; still-red re-attributes to backend with the trace (judged unlikely).
- **0670 fix design**: seam = `qualify_expanded_sexp` (scope-BLIND re-walk of the tree the expander already walked scope-aware). Fix: thread the shadow-set, qualify iff free reference; promote the expander's own binder helpers to one shared `pub(crate)` home (a second private copy would be the P7 mirror this removes). Fixes the binder AND the latent local-read qualification. Strict F8 order: C1 int fix → frontend reject re-lands → cells.
- **0671/0674/0675 dev-direct** (0671's one design constraint: resolve canonical homes ONCE, root the impl line there — P24/P26). No new FIXMEs.
- **Dev-wave map C1–C5** (all serial in src/): C1 = 0670 (MUST commit before the frontend reject wave); C2 = 0638 marshal-local; C3 = 0604 chokepoint+census (do NOT touch `insert_detecting_ambiguity`); C4 = finalize reanchor; C5 = riders batch. C2 kept marshal-local avoids the expander.rs coupling with C1.
- Process disclosure: one read-only `git status --short` against the no-git instruction (benign; logged — second such incident this phase).

### /qa — DELIVERED (2026-07-20)

- **Plan**: `tests/plan/s114-test-plan.md` — all five tracks; wave-flip ledger (§7); ~44 new cells (~14 born-green fences) + 4 F-D2-10 assertion re-shapes; unit-tier obligations enumerated.
- **0669 verdict (F3 discharged, FIXME deleted)**: the 0641 I-1 capture face **joins the 0668 backend family** — it fails under `CRANELISP_NO_OWNERSHIP=1`, and a crash that survives analysis-off cannot be owned by the analysis (post-R14 toggle-off consults no `transfer.rs` fact). Structurally it is cell G's let-bind alias with closure capture as the consume position. Track A drain 10→8; Track B acceptance 7→9; /testing updates the `// defect:` locus; re-attribution rider if the ON-face survives the backend fix.
- **0604 plan of record (FIXME updated, stays open)**: structural ship gate — foreground writer census (imports.rs/process_form//worker.rs) + ONE table-freeze/export-closure chokepoint (PS-R7 debug_assert → unconditional diagnosed error); twins already fence both poles; ≥25× recipe sweeps; /design(int) records the contract.
- **0676 DELETED**: both standing matrices drawn (plan §5.1) with one-seam structural grep as class-cure criterion.
- **0682 re-targeted → /spec** (qa half discharged: rows RA-P1/P2 + RA-N1..N5 incl. bare-`/` division green fence).
- **Phase 4 musts**: B-2 splits (toggle-off face → Track B contract; cache-coherence half → Track A schema window); MS-P7 in NO wave's flip set until the call-chain brief (CLIF identity across per-turn-JIT vs ObjectModule); 0670 = three strict waves and its IQ positives are Stage-1 authorable (RED today); 0682 /spec scribe precedes the /dev(frontend) fix (`// spec:` anchors); exactly ONE schema bump; /testing Stage-1 first act = live RED-inventory verification vs the 31-RED accounting.

## Waves (Phase 4 — FIRMED 2026-07-20; all source-touching waves SERIAL; wave-gate FIXME scan before each advance)

Ordering constraints honored: Stage-1 QA-first battery first; the carrier flip is ONE atomic multi-crate commit series (never split across a wave gate); C1 (0670 int fix) before W-D2; P26/helper sweeps AFTER the flip as acceptance; consume family independent of the flip (match_codegen.rs change-sets serialized); MS-P7 in no flip set until its evidence brief attributes; exactly ONE schema bump (in W2).

### W1 — QA-first battery (Stage 1) — DONE 2026-07-20
| Skill | Crate | Task | Status |
|---|---|---|---|
| /testing | sprint-wide | 45 new tests (17 RED defect cells + 28 born-green fences); RED reconciliation EXACT (31/31, zero drift, zero regressions); locus updates done; corpus check CLEAN (`/bar` guard breaks nothing) | **done** — suite 5033/4985/48/1 |
| /spec | spec/ | 0686 `/bar` enumeration (§8.5.1 + §2.4 mirror) | **done** — FIXME deleted |
| /qa | tests/plan/ | W1 findings disposition (6 items — see Notes) | **done** — all 6 disposed, no user arbitration needed |

### W2 — Atomic carrier flip — DONE 2026-07-20, committed `b0f03c96`, review APPROVED w/ follow-ups
| Skill | Crate | Task | Status |
|---|---|---|---|
| /arch | cranelisp-types | field flip + `MethodResolutions` split + `from_expr` Result-widening + `synthetic_local_from_expr` interior flip + public-api regen | pending |
| /dev | cranelisp-typecheck | producer totality (chokepoint + provenance + ~30 write-sites + adt.rs callsite swap) + F-D2-10 chokepoint fix + B-2 escape-recording fix + `CACHE_SCHEMA_VERSION` 21→22 | pending |
| /dev | cranelisp-backend | consumer exhaustive matches + `is_self_call` on `VarRef::Global` (backend.md §2.7.2) | pending |
| /review | typecheck + backend | change-set review of the whole flip series | **done** — approve-with-required-fixes; 0 Blockers, 3 Important, 3 Minor |

### W3 — Typecheck settlement drain (orthogonal to flip)
| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | cranelisp-typecheck | MC-X4/X4b (P26-temporal harvest), MC-X5, PS-SH1 (+ produce the MS-P7 call-chain evidence brief per plan §3.6) | pending |
| /review | cranelisp-typecheck | change-set review | pending |
| /qa | — | MS-P7 attribution from the brief (wave assignment or attributed carry) | pending |

### W4 — Backend consume family (Track B)
| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | cranelisp-backend | W-B1 classifier → W-B2 (BI-G) → W-B3 (BI-I1 ×2) → W-B4 (BI-F/B-cow/C-off) → W-B5 patch collapse; + F-R1 (`protect_return_value` entry-frame) + MS-P8 (tail-jump param flush) with both-polarity fences + the two over-correction hazards | pending |
| /review | cranelisp-backend | change-set review (incl. the §13.5 unit matrices) | pending |

### W5 — src/ Track C
| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | src/ | C1 0670 scope-aware qualify (COMMITS FIRST — gates W6's W-D2) → C2 0638 deep marshal protection (discriminator first) → C3 0604 chokepoint+census (≥25× sweeps) → C4 finalize reanchor → C5 riders (0671/0674/0675) | pending |
| /review | src/ | change-set review | pending |

### W6 — Frontend (Track D)
| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | cranelisp-frontend | W-D1 (BD-A seam + ctor trailing + RA reader consolidation + RA-N5) → audit batch (0677/0678/0679/0681/0680-rem) → W-D2 (value-level reject re-land + NOTE/mirror retirement; requires C1 committed) | pending |
| /review | cranelisp-frontend | change-set review | pending |

### W7 — Sweeps + acceptance (Phase 5 close)
| Skill | Crate | Task | Status |
|---|---|---|---|
| /design | cranelisp-typecheck | P26 full sweep + 0653 helper-classification sweep (carrier acceptance; register updates) | pending |
| /dev | cranelisp-typecheck | 0590 resolver-mirror convergence IF capacity remains; else defers with the `_hkt` latent-defect note | pending |
| /sprint + user | — | Phase 5 conclusion: suite state vs the wave-flip ledger (plan §7); defect disposition | pending |

Audit rotation FIRMED: **cranelisp-typecheck** (dispatched read-only in the Phase 6/7 window → `audits/cranelisp-typecheck-s114.md`).

## Dispatch log

| Wave | Agent | Surface | Model | Effort | Non-default reason |
|---|---|---|---|---|---|
| P2 | /arch | scope review (all tracks) | shim default | shim default | — |
| P3 | /arch | 0653 carrier + 0670 ruling + R14 + 0652 (design/arch + cranelisp-types) | shim default | shim default | — |
| P3 | /qa | sprint test plan + 0669 disposition + 0676 matrices + 0604 + 0682 framing | shim default | shim default | — |
| P3 | /spec | scribe reader-macro/dangling-qualifier ruling + 0683 | shim default | shim default | — |
| P3 | /design | cranelisp-typecheck (carrier + settlement family) | shim default | shim default | — |
| P3 | /arch | 0684 Principle 16 reconciliation (user-directed immediate; file-confined parallel to design×typecheck) | shim default | shim default | — |
| P3 | /arch | 0685 all-local synthetic-body shape (file-confined parallel to design×backend) | shim default | shim default | — |
| P3 | /design | cranelisp-backend (0668 consume contract + 0664 reconciliation) | shim default | shim default | — |
| P3 | /design | cranelisp-frontend (BD-A + 0660 + 0680 + RA enforcement) | shim default | shim default | — |
| P3 | /design | src/ (0638 + 0604 contract + 0670 int fix + persistence riders) | shim default | shim default | — |
| P3 | /qa | 0688 F-R1/MS-P8 seam adjudication (RC_TRACE discriminators) | shim default | shim default | — |
| W1 | /testing | sprint-wide Stage-1 battery (~46 cells + RED reconciliation) | shim default | shim default | — |
| W1 | /spec | 0686 `/bar` enumeration rider (file-confined parallel) | shim default | shim default | — |
| W1 | /qa | six-findings disposition + plan re-base | shim default | shim default | — |
| W2 | /arch | leg 1: types field flip + schema 21→22 | shim default | shim default | — |
| W2 | /dev | leg 2: typecheck producer totality + F-D2-10 + B-2 | shim default | shim default | — |
| W2 | /dev | leg 3: backend consumer flip + full-suite verification | shim default | shim default | — |
| W2 | /review | flip series review (b0f03c96, 3 crates) | shim default | shim default | — |
| W3 | /dev | typecheck settlement drain + MS-P7 brief + comment sweep | shim default | shim default | — |

## Notes

- 2026-07-20: Phase 1 draft authored. Escalation items: 0604 (2×+ carry), 0638 (twice unscheduled — hard-scheduled in Track C), audit R3/R4 (third audit carry — permanent-disposition point).
- 2026-07-20: **Phase 1 APPROVED (user)** — scope stands as drafted; all seven audit recommendations accepted (FIXMEs 0676–0682 filed, trail appended); 0604 scheduled to ship. R7's embedded §1.4.5/§2.4 normative question surfaced to user (ruling pending on framed cells). Advanced to Phase 2; /arch dispatched against the draft scope.
- 2026-07-20: **Phase 2 SIGN-OFF WITH REVISIONS** (transcribed above). Advanced to Phase 3. Serial dispatch order: /arch (carrier design + 0653/0670 rulings + R14 refresh + 0652 + types-crate edits) → /qa (test plan + 0669 disposition + 0676 matrices + 0604 + 0682 framing) → /design typecheck → /design backend (behind the 0669 disposition) → /design frontend → /design src. No /spec dispatch — no semantics change (0670 spec-accuracy rider arrives as a FIXME).
- 2026-07-20: /arch Phase 3 DELIVERED (see Skill plans). 0652/0653 resolved+deleted; 0670 ruled+re-targeted; 0683 filed.
- 2026-07-20: **USER RULING on 0682's normative half** (mid-Phase-3): `:` is a `^`-style reader macro — whitespace allowed, bound form MUST be a type; `:foo/` ERRORS; bare `foo/` ERRORS (Principle 16's degenerate pass-through overruled; bare `/` division stands). Recorded in 0682. **/spec dispatch now REQUIRED** (scribe ruling §1.4.5/§2.4/§8.5 + action 0683) — queued after /qa in the serial order.
- 2026-07-20: **USER CONFIRMED the symmetric reading — `/bar` (empty module half) errors too.** Principle 16's amended bullet already states it; 0686 (/spec, explicit enumeration) + 0687 (/qa, RA-N6 cell) filed to make it explicit on both sides.
- 2026-07-20: **W2 REVIEW: APPROVE with required follow-ups (0 Blockers).** Priorities 1–6 all CONFIRMED: totality airtight (ONE Local constructor, ONE ViaCallee stamp, all Dispatch writers plain-insert — the or_insert ordering safe both directions; lenient assert is always-on panic per arch §3.5); SYNTHETIC carve-out verified (no producer writes at the SYNTHETIC key); F-D2-10 propagation safe (both Err states genuine, already-propagated on the primary path); shim faithful (consumer-tests-only division — not the S87 F7 failure mode); riders mechanical; no recurring-class re-instantiation; suite reconciles at 5048/5004/44/1 serially (the spawn artifact passed). Follow-ups before Phase 5 close: **Important-1** → FIXME 0689 filed (/arch: single-source the strict-concreteness predicate + fence + Minor-1 rustdoc); **Important-2** ~13 stale `resolved_targets` comments → /dev(typecheck) sweep rider on W3; **Important-3** two surviving `if let Ok(Some(..))` swallow siblings (infer.rs:1233, mono_collect.rs:765) → /qa disposition + P26 sweep inventory (W3/W7); **Minor-2** "no producer writes at SYNTHETIC key" invariant → P26 sweep row; Minor-3 noted.
- 2026-07-20: **W2 leg 3 DONE (/dev backend) — WORKSPACE RESTORED, suite 5048 run / 5003 passed / 45 failed / 1 skipped.** Reconciliation EXACT: 48 − 4 (F-D2-10 ×4 FLIPPED GREEN — the wave's win) + 1 spawn-contention artifact (`agent::yes_flag` passes in isolation; not attributable) = 45; all 45 REDs trace to the ledger's post-carrier expected set. CS-1 nuance: the carrier-relevant ON face + CS-2 mechanism GREEN; the toggle-off arm stays RED by construction until BI-C-off (Track B) — not a regression. Consumer flip exhaustive (no `_ =>`); `VarRef::Local` scope-miss = hard diagnosed error carrying binder identity (soft double-miss unrepresentable; new KC pin); `is_self_call` keys on `VarRef::Global == current storage FQ`; ~15 test files adapted via ONE `resolved_targets_to_typed_maps` shim; backend CLAUDE.md stale-19 staleness class killed. Cross-crate note for /review: `src/worker/tests.rs` ×2 mechanical signature adaptation (int-owned — flag to /dev(int)). Nothing committed mid-wave; committing now as one series.
- 2026-07-20: **W2 leg 2 DONE (/dev typecheck)** — producer total: ~35 sites/13 files re-targeted (zero active `resolved_targets` reads remain); Apply-epilogue `or_insert(ViaCallee)` = totality by construction; provenance threaded at 6 seams; `callee_has_keyed_carrier` discriminates Local/Global (the totality-critical behavioural point). **F-D2-10 root cause: the settlement re-attempt SWALLOWED the located no-impl error via `if let Ok(Some(..))`** — now propagates; pins verified RED-on-revert. B-2 analysis fix confirmed already landed (S113 W5b transfer.rs) — owed unit pins authored (RED-on-revert verified). Validation obligation CLEAN (only the two adt.rs all-local bodies carry SYNTHETIC reference nodes; correctly routed). Deviation flagged for /review: `collect_universe` concreteness probe decoupled (local `body_is_strict_concrete` walk preserving the exact pre-flip universe; shared types-crate predicate = future /arch call). typecheck 780/780, types 216/216, 0 warnings. Nothing committed. Leg 3 dispatched.
- 2026-07-20: **W2 leg 1 DONE (/arch, types)** — field flip landed (`resolution: VarRef` / `dispatch: ApplyRef`, no serde defaults — absence unrepresentable); `MethodResolutions` → total `var_refs`/`apply_refs`; `ViewBuildError{NotConcrete, Unresolved}` with gate precedence Unresolved-before-NotConcrete (deviation 1); ONE shared verdict rule with the SYNTHETIC carve-out (deviation 2 + leg-2 validation obligation: no real-body SYNTHETIC-span table refs); schema 21→22 (window OPEN — B-2 rides it, no re-bump). Types 216/216 (+9 pins). Nothing committed; workspace expected-broken until leg 3. Leg 2 dispatched.
- 2026-07-20: **W1 findings DISPOSED (/qa, evidence-only, no cargo)**: (1) C1 ships as designed — RED-first expansion-seam UNIT tests are the live-defect demonstration (suppressor is table-state-dependent = 0604 heisenbug class; cannot supply W-D2's by-construction invariant); escalation clause if the failing fixture can't be constructed; IQ-P → must-hold fences; W6-W-D2 gate unchanged, acceptance = IQ-N1..N4 flips with twins green. (3) BD-A3 RULED spec-mandated (§2.2.2 MUST: type params lowercase) — M2-TP1 RED + M2-TP2 deftrait twin = /testing W-D1 rider. (4) BI-H-heap ×2 NEW row (inline heap-forward face was unaccounted) = /testing pre-W4 rider. (2)/(5)/(6) absorbed as-built. Plan §§2/3.5/4.3/5.1/5.2/6/7/8/10 re-based. **Wave-gate W2: PASS** (no open FIXMEs target W2 skills; 0553 deferral recorded).
- 2026-07-20: **W1 DELIVERED** — suite 5033 run / 4985 passed / **48 failed** (31 originals all present + 17 intended new REDs) / 1 skipped; zero regressions, zero born-green false-REDs. Six findings for /qa disposition: (1) **0670 does NOT reproduce e2e** — IQ-P shapes GREEN at HEAD (the skip guard + narrow seeding suppress the mis-qualification); IQ-P authored as born-green fences; C1's e2e flip target evaporates (unit-tier expansion-seam test becomes the guard; W5/W6 acceptance needs re-basing). (2) RA polarity drift — RA-N3/N4/P1/P2 already green at HEAD; only RA-N1/N2 RED; RA-N5/N6 RED via incidental-artifact assertions (flip with W-D1). (3) BD-A3 M2 probe: uppercase type param `(deftype (Box A) …)` silently accepted — /qa ruling requested (probe-first, no speculative RED authored). (4) plan's "H bare-match" green twin doesn't exist — heap-forward-through-match is broken wholesale; scalar control substituted. (5) PS-SH1 completed as matrix-missing positions (+2 RED + control) not net-new. (6) 0590 `_hkt` never-error masked by the form.rs pre-walk — born-green fence; latent defect is unit-tier for the 0590 deployment.
- 2026-07-20: **USER: baseline commit + Phase 5 GO.** Phase 1–4 state committed to main as the pre-W2 clean anchor; W1 dispatched (/testing sprint-wide + /spec 0686 rider, file-confined parallel).
- 2026-07-20: **Phase 3 COMPLETE** (all 6 authority/design deliverables in: /arch ×3 dispatches, /qa ×2, /spec, /design ×4). **Phase 4 waves FIRMED** (W1–W7 above); audit rotation firmed cranelisp-typecheck. FIXME ledger at Phase-4 entry: 12 resolved/deleted this sprint so far (0652/0653/0660/0664/0668/0669/0676/0682/0683/0684/0685/0687/0688 = 13), open in-sprint: 0604, 0670, 0671, 0674, 0675, 0677–0681, 0686; standing deferrals: 0050/0052/0463/0553/0590/0637. Awaiting user go for Phase 5 Stage-1 dispatch (W1).
- 2026-07-20: **0688 ADJUDICATED (/qa, run-discriminated — F3-style gate discharged for the leak REDs): BOTH BACKEND.** F-R1 = `protect_return_value` over-inc on entry-`main`'s IO return (RC_TRACE showed rc=2-at-return; `consume_io_tree` DID dec — intrinsics refuted; protect inc fires iff a heap cleanup target exists = G2/item-26 class at the entry frame). MS-P8 = missing release of the superseded heap loop-param at the TCO tail-jump slot overwrite (PARAM sibling of B3.1a; `flush_let_scopes_before_tail_jump` covers let only; conj's copy-arm source release IS emitted — polarity + intrinsics refuted; 1 leak/iter at rc=1). Both join the Track-B backend dev wave — NO intrinsics deployment. Over-correction hazards recorded (don't weaken general G2 protect; param flush must balance both conj arms). Pins verified RED exactly as accounted (4 fail / 8 pass on the two test files). 0687 actioned same run (RA-N6 added; counts ~46). Both FIXMEs deleted.
- 2026-07-20: **0685 RESOLVED (/arch)** — option (b) hardened: dormant `MonoExpr::synthetic_local_from_expr` (all-local license IS the signature — no resolution-map params; unconditional synthetic-span assert; `pattern_ctors` sidecar retained for match-arm ctor identity). Post-flip interior = all-local mode of the ONE shared lenient walk; signature stable across the flip, so the adt.rs callsite swap may land ahead of the wave. Types 207/207 green. §3.5 census CLOSED — the seam assert is now unconditional on real-span misses. **Disclosure**: the regen healed a two-update-discipline lapse (the earlier dormant-enums change-set had omitted its public-api.txt baseline regen; +23 lines now, all additive). Agent disclosed one read-only `git diff --stat` against its no-git instruction — benign, no index mutation, noted per process-incident practice.

## Outcome (Phase 7)

{pending}
