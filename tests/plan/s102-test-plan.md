# S102 test plan — QA-first stage, 0488 isolation, golden-CLIF corpus, guard-flip map

**Author:** `/qa` · **Date:** 2026-07-03 · **Status:** Phase 3 (design) deliverable —
planning only; test authoring is Phase 5 stage 1. Consumed by `/sprint` for wave
planning (`sprints/SPRINT.md` §Skill plans).

**Inputs:** `sprints/SPRINT.md` (all three blocks + the Phase-2 /arch review),
`tests/plan/coverage-audit-s101.md` (lane proposals §2.4, drafting rules §2.5, risk
register §4 — the baseline this plan executes), `tests/plan/s100-ownership-verification.md`
(§2 I-G gates, §3 lanes, §6 increment-I drafting list — amended this pass per FIXME 0503),
`tests/plan/ledger.md` §"Sprint 101 Phase 6a/6b defect set" (the 22 intentional REDs),
FIXMEs 0499 (lane refactor) + 0503 (golden-corpus pin — actioned + deleted this pass).

---

## §1 QA-first stage plan (Phase 5 stage 1 — the ordered drafting list)

Order is pinned by the audit's own recommendation (audit §4 close) and sprint scope:
**L-U1 first → L-S2 + L-S3 → L-N1 + L-N2 → increment-I set (with Block B) → L-S1 later
→ L-M1 rides B3.** The 4 standing drafting rules (audit §2.5) govern every item below
from the first drafted test: value-use × instantiation-count rows key on
artifact-minting; shape-pinning MUSTs get exact assertions; new session-visible state
kinds get restart + preamble rows at drafting; designed floors get flagged to
user-proxies in-phase.

All new tests carry `// spec:` anchors (`spec_link_check.py` on every drafting commit)
and ledger rows. RED-first drafting gets ONE ledger entry per the S101 §6.1 precedent
("S102 Phase-5 Stage-1 QA-first RED set", six fields); carried REDs at close get full
entries.

### 1.1 L-U1 — unannotated-default siblings (FIRST; backs Block A1 / T1)

- **Files:** extend `tests/repl_redefinition.rs` + `tests/repl_persist_redefine.rs`
  (the two transaction lanes). No new file.
- **Content, two legs:**
  1. **Siblings:** every transaction lane shape (trap, cascade report, recovery,
     persistence slot policy) gets ONE unannotated sibling — the fn(s) under
     redefinition carry no `:Type` annotations, so they generalize and take the T1
     downgrade. Each pins CURRENT behavior (coherent-stale, no report) with a
     flip-note naming the cure acceptance (report-or-recompile). GREEN at draft.
  2. **Interim-print acceptance (RED at draft):** Block A1's interim cure ships
     in-sprint (/int) — the T1 downgrade turn MUST print a transaction-report line
     naming the downgrade + affected callers (worded as a line the full cure keeps,
     per the /arch Principle-8 pin). One positive (report present, names the
     stale callers) + one negative (a NON-downgrade body-only turn does NOT print
     it — no over-triggering).
- **Size:** ~8–12 tests (≈6–9 siblings + 2–3 print acceptance).
- **Existing guards subsumed/re-anchored:** the 2 S101 coherent-stale pins + the
  Wave-5 Overloaded-T1 sibling get flip-notes reconciled to the new acceptance
  wording; none deleted or weakened.
- **Spec annotations:** anchors are `design/int/session-transaction.md` §10 at draft
  (T1 print wording is /int-shipped, spec-side text may trail); re-anchor to
  `repl/spec.md` §18 when /repl pins wording (the §6.1 anchor-policy bridge).
  `[S102]` rows on the affected §18 subsections.

### 1.2 L-S2 — session-lifecycle grid (backs Block A2: D1 + D2 + 0489)

- **File:** NEW `tests/repl_lifecycle_matrix.rs` (distinct from the existing
  `repl_lifecycle.rs`).
- **Content:** restart × session-end-state grid: end state {healthy defns, broken
  symbol (0489 cell), macro-defining-macro used (D1 cell), redefined-with-frozen-slot,
  `/mod`-touched module} × restart mode {clean, `--no-cache`, cache-wiped}; plus the
  dirty-world cells the tmpdir discipline structurally hid: pre-seeded hand-authored
  `user.cl` (D2 / §15.4.7 authorship fidelity), pre-seeded stale `.meta.json`. Staged
  dirty fixtures inside fresh tmpdirs (audit §2.4 — isolation preserved, contents
  staged). Populate the grid judiciously: every row that reproduces a 6a/6b defect is
  a RED cell; healthy neighbours are one-line GREEN controls.
- **Size:** ~15–20 tests (15-cell grid pruned to load-bearing cells + 3–4 dirty-world
  cells).
- **Existing guards:** the 0489 guard (`repl_persist_redefine.rs`), D1 + D2 guards
  (`repl_persist.rs`) STAY in place (spec citations must not rot); the grid
  cross-references them as its pre-populated cells and adds the surrounding cells.
  They flip with the A2 fix; the grid keeps the class shut afterwards.
- **Spec annotations:** `repl/spec.md` §15.1/§15.4.1 (round-trip), §15.4.7
  (authorship fidelity), §18.8 (restart-reaches-prompt floor, authored [S102] in
  S101) — `[S102]` at draft, upgrade to `[Tested]`/`[Tested+Neg]` as A2 lands.

### 1.3 L-S3 — file-backed dev-loop lane (backs Block A4: D3 + 0487)

- **File:** NEW `tests/repl_mod_devloop.rs`.
- **Content:** the exemplar-shaped loop as e2e: file-backed modules + `/mod M` turns
  × {fresh, cache-restored} × {same-module, cross-module dependents} × {prelude-using,
  prelude-free bodies} (the 0487 parity axis), then redefine → cascade → revert →
  restart. Seeded by the D3 guard + its fresh-session control. Includes the
  0487-introspection half: cascade-report names must be pasteable into `/info`.
- **Size:** ~10–14 tests. Cache-restored × prelude-using cells RED at draft (D3/0487);
  fresh-session cells GREEN controls.
- **Existing guards:** D3 guard + control stay in `repl_persist_redefine.rs`,
  cross-referenced as the lane's seed cells. Re-probe the two UNREDUCED residues
  (D2 hybrid-meta; exemplar false-`undefined variable: None` faces) once A2/A4 fixes
  land — risk-register #10's watch obligation lives in this lane.
- **Spec annotations:** `repl/spec.md` `/mod` sections + `spec/08-modules.md`
  (module-environment parity) — `[S102]` rows; 0487's testable invariant
  ("module-namespace turn compiles in the module-file's environment") gets stated as
  a spec-side row when /spec or /repl pins it (flag filed only if neither does —
  audit P5 lesson).

### 1.4 L-N1 — display-exact lane + L-N2 — no-internal-artifacts sweep (back Block A5)

- **L-N1 file:** NEW `tests/display_exact.rs`. Exact-output assertions
  (`assert_stdout_eq` on answer lines; `assert_golden_masked` on transcript blocks —
  first real adoption of both helpers) for every spec-pinned display class:
  value rendering incl. nested parameterized ADTs × {Vec, ADT-in-ADT, Option-in-Option}
  (0493 class); `/sig` + `/info` + bare-lookup primary-line AGREEMENT (assert the three
  render identically — 0492 class); §5.1 error format; §18.3 cascade report as a whole
  block; §18.5 trap line. Masks for spans/byte-counts/timings. Cells over open A5
  defects are RED at draft and are the A5 fixes' exact-shape acceptance; the 7
  existing A5 guards stay as the substring-level record and flip with the fixes.
  **Size:** ~12–18 tests.
- **L-N2:** harness edit (`tests/helpers/e2e.rs`) — a shared negative needle-set
  `assert_no_internal_artifacts`: `FQSymbol {`, `ModuleFullPath(`, `Symbol(`,
  `__expr`, `__macro_`, `at 0..0`, the `1000\d{3,}\.\.` internal-span shape (regex —
  first real use of `assert_stdout_matches`), `'...'` placeholder. Applied per-lane
  to diagnostic-producing tests (start: the A5 surfaces + `repl_negative.rs` +
  macro/module error tests), plus 2–4 new tests pinning the 0485/0490 diagnostic
  shapes (RED until those fixes land). Harness-DEFAULT with opt-out is assessed
  AFTER A5 lands — flipping it default now would RED dozens of tests over known
  defects and drown the signal. **Size:** 1 helper + applied to ~15–25 existing
  tests + 2–4 new RED tests.
- **Spec annotations:** `repl/spec.md` §1.4, §1.5, §5.1, §18.3, §18.4, §18.5 —
  upgrades toward `[Tested+Neg]` as A5 lands; `[S102]` at draft.

### 1.5 Increment-I QA-first set (with Block B; folded from `s100-ownership-verification.md` §6)

Drafted at stage 1 alongside the lanes above (Block B Wave 1 is the golden capture,
which may run before/parallel to Block-A waves per the /arch Q1 ruling):

| Item | File(s) | Size | RED/GREEN at draft |
|---|---|---|---|
| **L-B1 golden capture** | NEW `tests/fixtures/clif_baseline/` (corpus + MANIFEST + EXCLUSIONS), capture/diff script (`tests/scripts/clif_golden.sh` or `.py`), ONE in-suite smoke (single-module golden in nextest) | corpus ≈ 10–12 modules; 1 smoke test | smoke GREEN once captured; capture is the FIRST Block-B change-set |
| **S1–S4 + S6 starved-inc fences** | NEW `tests/ownership_fences.rs` (behavioral + balance legs, sustained 200–2000 crossings) | ~12–18 tests | GREEN at draft (conservative codegen satisfies them); load-bearing when mechanisms land |
| **L-D3a–f projection-escape negatives** | same file or NEW `tests/ownership_projection.rs`; fact-table per-row tests generated mechanically from the declared-fact audit table | ~8 + one per table row | GREEN at draft except L-D3f (needs H5 — RED/won't-compile until the hook exists) |
| **L-C1 suspension-UAF + L-C2 stack-slot lanes** | extend existing UAF guards (floor) + new micro-fixtures; ASan legs scripted (`tests/scripts/asan/`) | ~6–8 canonical + scripts | GREEN at draft |
| **S5 str-len sibling fence** | `ownership_fences.rs` | 1–2 | GREEN at draft; discriminating when the sibling lands |
| **H1/H2/H3/H5 hook smokes** | `ownership_fences.rs` or perf scripts | ~4 | RED at draft (H2/H5 don't exist — the loud signal that the hooks are owed in the B2/B3 change-sets) |
| **Perf lanes I-G1…I-G7** | extend `tests/perf/` — an `ig_gates` runner (extend `s99_measure.py`); `l_d1_turn_latency.py` already covers I-G6 | 1 runner script | scripts, not nextest entries; executed attended at wave gates |

L-B3(1)–(3) and L-B2(i) landed at stage M (S101) and stand; L-B3(4) waits for
increment II.

### 1.6 L-S1 — session-history preambles (LATER; capacity-gated tail)

Extend `repl_introspection.rs` + `repl_redefinition.rs` with a preamble-grid helper
(prepends {∅, bare lookup, expression turn, prior failed turn, `/reset`} to stdin).
Start with the 6a-burned surfaces (0486, 0491, 0484) — those specific cells already
have guards, so L-S1's marginal value is generalization to the surfaces 6a did NOT
burn. ~10–15 tests. Scheduled after L-N1/L-N2; may trail into the A5 wave or defer
to S103 with rationale at the gate (0499 partial-resolution protocol).

### 1.7 L-M1 — reference-shape × referent-kind × instantiation-count matrix (rides B3)

Extend `generic_value_use_mono.rs` + `vec_query_value_use.rs` per the audit's bounded
enumeration rule (one exemplar per artifact-minting kind per axis; crashing cells →
guards, passing cells → one-line controls). Grows WITH the `fn_as_value` seam rework:
the 0483/0474 flips, the corpus EXTENSION with newly-green shapes (§3 below), and the
new matrix cells land in the same wave. ~8–12 new cells.

---

## §2 FIXME 0499 execution plan (e2e lane refactor)

- **Stage 1 (this sprint's QA-first stage):** L-U1 (§1.1), L-S2 (§1.2), L-S3 (§1.3),
  L-N1 + L-N2 (§1.4), the increment-I set (§1.5), and adoption of the four §2.5
  standing drafting rules as binding on all S102+ drafting (restated in §1 head).
- **Rides later waves:** L-S1 (§1.6 — A5 wave or S103), L-M1 (§1.7 — B3 wave).
- **Item 3 housekeeping — DONE this pass:** `coverage-audit-s101.md` (and this plan)
  registered in `tests/CLAUDE.md` §Plan documents.
- **Disposition:** 0499 stays OPEN with per-lane status annotated at each sprint
  gate; deleted when all 7 lanes exist or are explicitly retired. Expected S102 exit:
  5–6 of 7 lanes existing (L-S1 the likely partial), L-M1 seeded.

---

## §3 FIXME 0488 isolation plan (Block A3 — isolation BEFORE fix dispatch)

**The three signatures** (guards in `tests/generic_value_use_mono.rs`, all stdlib-free):

| Sig | Guard | Shape | Error |
|---|---|---|---|
| (a) | `generic_fn_fq_call_monomorphises_like_bare_call` | FQ call of same-module generic | `undefined function: user/iden` |
| (b) | `imported_generic_in_value_position_monomorphises` | imported generic as value | `undefined variable: iden2` |
| (c) | `composition_over_fold_bodied_imported_generic_monomorphises` | composition over fold-bodied imported generic | `undefined function: vcount` blamed on the OUTER fn |

**The seam question the isolation must answer** (per audit §3.4 + tests/CLAUDE.md
§Isolating): typecheck's edge/instantiation recording is unit-verified complete
(`program/tests.rs::callees_records_fn_as_value_*`) — so for EACH signature, is the
mono instance (i) **never requested** (typecheck-side after all — the unit tier may
not cover these exact shapes), (ii) **requested but dropped from the codegen batch**
(the src/-side consuming-turn batch derivation, `process_form/dependency.rs` —
zero unit tier, FIXME 0496's territory), or (iii) **in the batch but failing symbol
resolution at emission** (backend naming/GOT)? The two distinct error classes
("undefined function" vs "undefined variable") suggest the signatures may NOT share
one home — the deliverable must attribute each independently.

**Method:**

1. Start from the three committed guards (already minimal; (c) is
   micro-shape-sensitive per the file header — any further reduction re-verifies RED
   before being kept).
2. Introspection + trace passes per signature: `/info`//`/sig`//`/list` on the missing
   symbol between defn and consuming turn; `CRANELISP_CODEGEN_TRACE=1` +
   `CRANELISP_MODULE_TRACE=1` on the guard runs to see whether the instantiation is
   missing / present-but-unbatched / batched-but-unresolved. Small CLIF read where it
   plateaus.
3. Attempt one cross-mode discriminator per signature (REPL vs `--run`) — a
   divergence localizes to the session-side derivation; parity points below it.
4. **Deliverable:** (i) a seam-attribution note per signature appended to the guard
   file header + a ledger annotation; (ii) where the attribution lands typecheck-side,
   an isolating unit-test SHAPE (parse + build_program + check, asserting the
   symbol-table mono/callees record) specified in the handoff for /dev(typecheck) to
   land; where src/-side, the isolation note names the `dependency.rs` seam and the
   first 0496 drain scenario that pins it; (iii) the handoff brief to /sprint naming
   the owner (possibly split per signature), the repro test names, and what stripping
   revealed. **No fix by /qa.**

**Early-wave recommendation: YES — run as its own early wave.** It is read/diagnose +
narrow test-file annotation only; it does not block and is not blocked by the golden
capture (0488's shapes are corpus-EXCLUDED per the /arch Q1 ruling); and Block A3's
fix dispatch is gated on it. Recommend scheduling it as the first /qa activity after
(or interleaved with) L-U1 drafting, serialized with other tests/-editing agents but
parallel-safe with /int design work and the Block-B capture wave.

---

## §4 FIXME 0503 intake — golden-CLIF corpus pins (ACTIONED)

The three pins are folded into `tests/plan/s100-ownership-verification.md` §3.1 L-B1
(this pass; FIXME 0503 deleted):

1. **Green-only construction + exclusion list.** The corpus excludes every shape
   under an open failing-not-ignored guard at capture time (0483 two-instantiation
   HOF, 0488 FQ-call/imported-value-use, 0484 shadow-order — the live list is
   whatever the ledger's intentional-RED set covers). The exclusion list is a
   committed `EXCLUSIONS.md` beside the corpus, each entry naming the guard whose
   flip triggers extension. This is what makes capture non-blocking on Block A.
2. **Extension ≠ re-baseline.** Fix makes an excluded shape green → the corpus is
   EXTENDED with the newly-green shape in the fix change-set; existing golden entries
   untouched; the EXCLUSIONS entry is struck. Emission-affecting change reshapes CLIF
   for shapes already in the corpus → SCOPED re-baseline in that change-set: re-dump
   only the entries whose CLIF changed, golden diff in the same commit, delta
   attributed to the change's seam (the `public-api.txt` discipline). Wholesale
   re-capture without attribution is forbidden.
3. **Emission-affecting classifier** (trigger test for a scoped re-baseline): a change
   is emission-affecting iff it changes backend emission, primitives entry shapes,
   monomorphisation derivation, or name-resolution precedence FOR GREEN PROGRAMS.
   Display/persistence/introspection/diagnostic fixes have no capture interaction.
   Canonical home of the ruling: `design/arch/ownership-inference.md` §6.2.

Bookkeeping mechanics added to the lane: a corpus `MANIFEST.md` (entry → source
fixture → provenance/capture SHA) so extensions and re-baselines stay attributable.

---

## §5 Guard-flip bookkeeping (the 22 intentional REDs)

| Guard set | Count | File(s) | Flips with | Close-short (after B2) behavior |
|---|---|---|---|---|
| 0474 COW copy-branch leak | 3 | `vec_cow_value_use_leak.rs` | **B3** (fn_as_value/COW seam rework) | **stays RED** (per /arch Q3 pin 3) |
| 0483 vec-op-as-value ≥2 instantiations | 3 | `vec_query_value_use.rs` | **B3** (same seam) | **stays RED** |
| 0488 generic-fn missing mono | 3 | `generic_value_use_mono.rs` | fix wave assigned at A3-iso close (nominally with the B3 seam work per the risk register) | stays RED if its fix rode B3; flips if dispatched as its own A-wave |
| 0489 restart lockout | 1 | `repl_persist_redefine.rs` | **A2** (persistence cluster) | flips (A2 does not slip the seam) |
| D1 def-poisons-directory | 1 | `repl_persist.rs` | **A2** | flips |
| D2 authorship fidelity | 1 | `repl_persist.rs` | **A2** | flips |
| D3 file-backed false-BREAK | 1 | `repl_persist_redefine.rs` | **A4** (dev-loop cluster) | flips |
| 0486 bare-lookup corruption | 2 | `repl_introspection.rs` + `repl_redefinition.rs` | **A5** | flips |
| 0484 import-shadow order | 1 | `spec_08_modules.rs` | **A5** (after /spec precedence pin; re-anchors if the ruling differs) | flips |
| 0491 `__expr` cascade leak | 2 | `repl_redefinition.rs` | **A5** | flips |
| trap-format §18.5 | 1 | `repl_redefinition.rs` | **A5** | flips |
| 0492 `/sig` FQ primary line | 1 | `repl_redefinition.rs` | **A5** (after /repl arbitration; re-anchors, possibly GREEN-by-amendment, if §18.4 changes) | flips or re-anchors |
| 0493 nested-ADT display | 2 | `repl_introspection.rs` | **A5** | flips |

Total 22 ✓ (3+3+3 + 1+1+1+1 + 2+1+2+1+1+2).

**Flip protocol per set** (the §7.1 precedent): fix + unit test in the same change-set
(/dev); /qa observes the flip (controls stay green), annotates the ledger entry in
place with sprint + SHA, updates the test-file "RED on HEAD" notes in the same
change-set. Tests are never deleted or weakened.

**New transient REDs this sprint** (QA-first drafting, expected to flip in-sprint):
the L-U1 interim-print acceptance, L-N1 exact-shape cells over A5 defects, L-S2/L-S3
new cells over A2/A4 defects, the H2/H5 hook smokes. One drafting-batch ledger entry;
any carried at close get full entries and join the intentional count.

**Root-`CLAUDE.md` §Testing count obligation at close** (noted, not edited here):
/qa supplies the exact close-state counts in its Phase-7 suite report; /sprint flags
the user edit. Full-sprint outcome → expected 22 → 0 (+ any carried drafting REDs);
close-short after B2 → 0474×3 + 0483×3 stay (count ≥ 6, +3 if 0488 rode B3, + carried
drafting REDs). Two consecutive `--no-fail-fast` runs with identical fail sets remain
the close-verification standard.

---

## §6 I-G gate harness readiness (before Block B3 can be judged)

**Exists and ready:**

- `CRANELISP_RC_STATS` (intrinsics `rc.rs`) — I-G1/I-G2 counters + balance legs.
- `CRANELISP_CODEGEN_DUMP` with filter grammar (backend `lib.rs:946`) — the L-B1
  capture mechanism.
- F1–F4 fixtures (`tests/fixtures/s99/`) + parallel≡serial guards (`s99_fixtures.rs`).
- `tests/perf/s99_measure.py` — the measurement discipline machinery (wall/user/sys,
  median-of-7, RC attribution, F4 distributions).
- `tests/perf/l_d1_turn_latency.py` — **I-G6 ready as-is**.
- `tests/scripts/suite_polarity.sh` — L-B2(i), certified at S101 close.

**Gaps (named, with owners):**

| # | Gap | Needed by | Owner / when |
|---|---|---|---|
| G-1 | **H1 decision** — deterministic CLIF dump ordering under the concurrent scheduler vs harness-side sort-by-function-symbol | L-B1 capture | decide at L-B1 drafting; harness-side sort is the default resolution unless the dump interleaves mid-function (then /backend) |
| G-2 | **H2 per-mechanism counters** (stack-slot hits, reuse hit/miss, non-atomic op share) — not implemented | **I-G3, I-G7** (gate-blocking) | /backend, same change-sets as the B3 mechanisms; QA's RED hook smokes are the tripwire |
| G-3 | **H5 `CRANELISP_OWNERSHIP_TRACE`** (per-cluster summary + per-site verdict dump) — not implemented | **I-G3** classification assertion, L-D3f | /typecheck, with `pass5_ownership` (B2) |
| G-4 | **H3 per-extern adaptation-pair attribution** — not implemented | L-D5 (report-only; not gate-blocking) | /backend (intrinsics seam), B3 or deferred with the sibling-expansion decision |
| G-5 | **`ig_gates` runner** — no toggle-on/off differential gating script for I-G1/I-G2/I-G4/I-G5 (s99_measure.py measures; it does not gate) | I-G1/2/4/5 | /qa, stage 1 (extend `s99_measure.py`) |
| G-6 | **Fresh toggle-off baseline on S102 HEAD** before any grading (§1.2 discipline) | all I-G | /qa run, after golden capture lands |
| G-7 | **I-G5 compile-time probe** (cold-cache `--run`-to-first-output on the fixture corpus, ≤ +10%) | I-G5 | /qa, small extension inside G-5 |
| G-8 | Micro-fixtures: stack-slot TCO shape, projection-escape shapes, sibling fixture | I-G7, L-C2, S5 | /qa, authored with §1.5 drafting |
| G-9 | ASan script skeleton (`tests/scripts/asan/`; aarch64 fallback `MALLOC_CHECK_`/`MALLOC_PERTURB_` documented) | fence two-condition rule | /qa, stage 1 skeleton; executed at B3 wave gates |

**Close-short seam pin (/arch Q3 pin 2, restated as a checklist obligation):** if the
sprint closes after B2, **I-G5 and I-G6 still run at the seam** — pass5's cost is live
the moment it runs. I-G6 is ready today (G-1..G-4 don't block it); I-G5 needs only
G-5+G-7 (the runner), which therefore lands in stage 1, not with B3. I-G1–I-G4 + I-G7
defer wholesale to S103 at a short close (they grade mechanisms).

---

## §7 Registration and cross-references

- Registered in `tests/CLAUDE.md` §Plan documents (this pass), alongside
  `coverage-audit-s101.md` (the 0499 item-3 housekeeping).
- Amends `tests/plan/s100-ownership-verification.md` §3.1 (L-B1 corpus pins, §4 above).
- Ledger rows for all new tests land with the drafting commits, not this plan.
