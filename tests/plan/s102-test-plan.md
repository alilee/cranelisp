# S102 test plan — QA-first lanes, 0488 isolation plan, I-G gate harness

> **Retained dated record (S122 consolidation).** Only the sections that current
> test sources, the perf harness and the ownership designs cite remain, with
> their original numbering: §1.1, §1.3, §1.4, §1.5, §3 and §6. They are the
> 2026-07-03 Phase-3 allocation, not current status: sizes, RED/GREEN-at-draft
> colours, `[S102]` band tags and specification section numbers are as drafted,
> and the named test files are the current record of what landed. The
> [0488 isolation record](0488-isolation.md) holds §3's outcome. The removed
> drafting order, §1.2, §1.6, §1.7, the 0499 lane-refactor plan (§2), the 0503
> golden-corpus intake (§4, whose pins live in
> [ownership verification](s100-ownership-verification.md) §3.1 and the
> [corpus manifest](../fixtures/clif_baseline/MANIFEST.md)), the guard-flip map
> (§5) and registration (§7) are recoverable with
> `git show 57253cf2:tests/plan/s102-test-plan.md`.

## §1 QA-first stage plan (cited lanes)

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
  (T1 print wording is /int-shipped, spec-side text may trail); re-anchor to the
  [REPL redefinition chapter](../../repl/spec/18-redefinition.md) when /repl pins
  wording (the anchor-policy bridge). `[S102]` rows on the affected subsections.

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
- **Spec annotations:** the REPL specification's
  [display format](../../repl/spec/01-display-format.md) type- and value-display
  sections, [error format](../../repl/spec/05-error-presentation.md) and the
  [redefinition chapter](../../repl/spec/18-redefinition.md)'s cascade-report and
  trap sections as numbered on 2026-07-03 (that chapter has since been
  renumbered) — upgrades toward `[Tested+Neg]` as A5 lands; `[S102]` at draft.

### 1.5 Increment-I QA-first set (with Block B; folded from `s100-ownership-verification.md` §6)

Drafted at stage 1 alongside the lanes above (Block B Wave 1 is the golden capture,
which may run before/parallel to Block-A waves per the /arch Q1 ruling):

| Item | File(s) | Size | RED/GREEN at draft |
|---|---|---|---|
| **L-B1 golden capture** | NEW `tests/fixtures/clif_baseline/` (corpus + MANIFEST + EXCLUSIONS), capture/diff script (`tests/scripts/clif_golden.sh` or `.py`), ONE in-suite smoke (single-module golden in nextest) | corpus ≈ 10–12 modules; 1 smoke test | smoke GREEN once captured; capture is the FIRST Block-B change-set |
| **S1–S4 + S6 starved-inc fences** | NEW `tests/ownership_fences.rs` (behavioral + balance legs, sustained 200–2000 crossings) | ~12–18 tests | GREEN at draft (conservative codegen satisfies them); load-bearing when mechanisms land |
| **L-D3a–f projection-escape negatives** | same file or a new projection-lane file (none was created; the cells are in [ownership fences](../ownership_fences.rs)); fact-table per-row tests generated mechanically from the declared-fact audit table | ~8 + one per table row | GREEN at draft except L-D3f (needs H5 — RED/won't-compile until the hook exists) |
| **L-C1 suspension-UAF + L-C2 stack-slot lanes** | extend existing UAF guards (floor) + new micro-fixtures; ASan legs scripted (`tests/scripts/asan/`) | ~6–8 canonical + scripts | GREEN at draft |
| **S5 str-len sibling fence** | `ownership_fences.rs` | 1–2 | GREEN at draft; discriminating when the sibling lands |
| **H1/H2/H3/H5 hook smokes** | `ownership_fences.rs` or perf scripts | ~4 | RED at draft (H2/H5 don't exist — the loud signal that the hooks are owed in the B2/B3 change-sets) |
| **Perf lanes I-G1…I-G7** | extend `tests/perf/` — an `ig_gates` runner (extend `s99_measure.py`); `l_d1_turn_latency.py` already covers I-G6 | 1 runner script | scripts, not nextest entries; executed attended at wave gates |

L-B3(1)–(3) and L-B2(i) landed at stage M (S101) and stand; L-B3(4) waits for
increment II.

## §3 FIXME 0488 isolation plan (Block A3 — isolation BEFORE fix dispatch)

**The three signatures** (guards in `tests/generic_value_use_mono.rs`, all stdlib-free):

| Sig | Guard | Shape | Error |
|---|---|---|---|
| (a) | `generic_fn_fq_call_monomorphises_like_bare_call` | FQ call of same-module generic | `undefined function: user/iden` |
| (b) | `imported_generic_in_value_position_monomorphises` | imported generic as value | `undefined variable: iden2` |
| (c) | `composition_over_fold_bodied_imported_generic_monomorphises` | composition over fold-bodied imported generic | `undefined function: vcount` blamed on the OUTER fn |

**The seam question the isolation must answer** (per audit §3.4 + tests/CLAUDE.md
§Isolating): typecheck's edge/instantiation recording is unit-verified complete
(the `callees_records_fn_as_value_*` cells, now in `crates/cranelisp-typecheck/src/program/callees/tests.rs`) — so for EACH signature, is the
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
