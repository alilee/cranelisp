# Sprint 82: Clean & Green II — pre-Phase-H decks clearing

**Status**: PHASE 7 CLOSE (awaiting user approval) — 0354 SIGSEGV resolved

**Goal**: Clear the pre-Phase-H backlog — flip all 7 Phase-6 defect guards green, harvest-and-delete the entire `tests/legacy/` quarantine corpus with confidence, and draw down the remaining actionable FIXMEs — so Phase H (`--release` / Tier-2 backend) opens against a clean ledger and a single, trusted test suite.

## Scope

S81's reinstated Phase-6 assessment surfaced 7 real defects (all captured as failing-not-ignored guards) and reaffirmed that the suite is "a strong regression guard but weak on real-composite-program coverage." Meanwhile the S64 test-port left **1,323 test functions quarantined under `tests/legacy/`** (vs ~980 active), tracked by 12 harvest FIXMEs but never measured against the current suite. This sprint closes both: the known defects and the unmeasured legacy backlog. Everything here is "pre-Phase-H mainline completion" — no new language capability.

Three workstreams, each independently shippable; partial completion still closes whole units (a defect guard flipped, a legacy file deleted, a FIXME resolved).

### Workstream D — Defect clearance (7 failing guards → green)

Each defect already has a failing-not-ignored repro (14 e2e + 2 unit). The fix flips the guard. Per CLAUDE.md, every fix lands with a unit test at its seam; e2e need assessed before the fix.

| FIXME | Defect | Severity | Seam |
|---|---|---|---|
| `0343` | `(mod child …)` load triggers source-regen that **rewrites the backing `.cl` without the submodule body** | **HIGH — destroys committed source** | `/dev src/` (save.rs / session_v4 regeneration) |
| `0340` | `(trace expr)` ~31s/call AND degenerate capture (args=`SNil`, name=`"::trace::"`) — **split into 2 repros** (Rev 2): timing → likely `/dev cranelisp-backend` (per-call rediscovery iterating all GOT slots); capture → likely `/dev cranelisp-intrinsics` (bodies/descriptor) | High (perf + correctness) | `/dev cranelisp-backend` + `cranelisp-intrinsics` |
| `0337` | sibling-file `(mod math)` unresolved when entry module is `main`; zero CI coverage | High | `/dev src/` (module resolution) |
| `0344` | `vec-reduce` polymorphic accumulator over-unifies to `(Vec a)` | Medium | `/dev cranelisp-typecheck` (infer.rs) |
| `0342` | `(import [super [name]])` child→parent doesn't resolve (ordering) | Medium | `/dev cranelisp-typecheck` + `src/` (load ordering) |
| `0341` | stacked trait bounds `[:Eq :Display a]` mis-parse as duplicate param | Medium | `/dev cranelisp-frontend` (param-list parser) |
| `0338` | bare `trace` drops `:Type` prefix; `/info`·`/sig` fail for all special forms | Low (self-doc) | `/dev src/` (REPL display + introspection) |

`0337` carries a coverage corrective intrinsic to its close: extend `tests/examples.rs` to run a multi-file directory example so multi-file module regressions are caught going forward. Start with the entry-name narrowing (`main` vs non-`main`) — may localize the fix to the entry-module-naming path (Rev/Rec).

**Repro-before-handoff gate (Rev 2):** `0342` and `0340` must NOT enter `/dev` until `/qa` produces an isolating repro that fixes the owning crate. `0342`: repro + `/info`-on-parent introspection decides *missing-symbol* (→ int load-ordering) vs *present-but-unreached* (→ typecheck resolution). `0340`: two separate repros (timing; capture) routing to backend vs intrinsics respectively.

### Workstream H — Legacy harvest-and-delete (confidence to delete)

The exercise that lets us delete `tests/legacy/` with confidence. **Per file**: (1) dedup-audit each legacy assertion against the active suite; (2) harvest the genuine gaps as `#[cfg(test)]` unit tests (or e2e where parity-shaped) in the owning crate, `// spec:`-annotated; (3) delete the file, remove its `tests/legacy/README.md` row, close the FIXME. A file is "done" only when deleted — so partial-sprint progress is measured in whole files removed, not assertions touched.

20 files / 12 FIXMEs, partitioned by owning crate (multi-skill anchors split per the FIXME bodies):

| FIXME | Files (tests) | Owning skill(s) |
|---|---|---|
| `0134` | e2e(309) + ring0(216) + ring1(380) + ring2(405) — **XL bulk** | `/dev` typecheck + backend + src/ (int slice e2e-covered → mostly delete) |
| `0124` | repl_experience(190) + repl_negative_old(31) | `/dev src/` (w/ typecheck, backend) |
| `0136` | sketch_port(296) — test-shape harvest | `/qa` |
| `0127` | io(76) + io_minimal(5) | `/dev src/` (w/ typecheck, backend) |
| `0149` | v4_pipeline(47) | `/dev src/` (w/ backend, frontend, platform) |
| `0125` | ring3_repl(41) | `/dev src/` (w/ typecheck) |
| `0144` | sprint23(61) | `/dev src/` |
| `0130` | ring4_trace_taxonomy(31) | `/dev cranelisp-typecheck` (w/ runtime) |
| `0135` | lenient(32) | `/dev cranelisp-backend` (w/ runtime) |
| `0143` | examples(15) + examples_run(1) + exemplar(3) + exemplar_solver_correctness(2) | `/port` |
| `0133` | v4_jit_reclaim(6) | `/dev cranelisp-backend` |
| `0148` | wave6_demo_repros(5) | `/dev src/` (w/ backend, stdlib, port) |

**Measurement gate (Phase 5 Stage 1, `/qa`):** before harvesting, produce a per-file dedup map (legacy assertion → covered-by active test | genuine gap | obsolete). This quantifies the real gap (somewhere between "mostly redundant" per S64's dedup intent and "12 files of gaps" per the open FIXMEs) and turns the harvest from "re-port 1,323 tests" into "port the measured N gaps, confirm the rest, delete." No silent drops: every legacy assertion is dispositioned in writing before its file is deleted.

### Workstream F — FIXME drawdown (actionable carries)

| FIXME | Work | Owning skill |
|---|---|---|
| `0336` | Expose in-process bench accessor for `record_event` via a narrow `#[cfg(feature = "bench")] pub fn` (NOT a `[lib]` target — Rev 1, Principle 8 / BC §6) | `/dev src/` |
| `0021` | Criterion microbench for IO-trace off-path overhead (<1% AC); tighten integration ceiling. **After `0336`.** | `/qa` |
| `0109` Wave D | Decompose `session_v4.rs` (5,417 LOC) + `worker.rs` into the §3.3 module map (eval.rs, repl.rs, …); collapse mirrored worker paths. Read **BC §6 + `design/int/`** for the target shape (not the retired `facades/int.md` — Rev 4). **Land early** (reshapes files the int harvest targets). | `/dev src/` |
| `0243` | Narrow remaining heavy typecheck fixtures (adt/checker/traits + shared helpers) to minimal presets | `/dev cranelisp-typecheck` |
| `0101` | Audit passes over the **post-D43 crates — `cranelisp-primitives`, `cranelisp-intrinsics`, `cranelisp-platform`** (NOT the retired `cranelisp-runtime` — Rev 3); `audits/{crate}-*.md`; file remediation FIXMEs from findings | `/sprint` schedules; audit-discipline pass |

## Out of scope — assigned to Phase H

Phase H (Release Compiler) is reframed by user direction (S82 planning) to be the
**release phase** — Tier-2 backend *and* release-polish features — not just the backend.
The two feature-shaped FIXMEs belong there, not to S82's decks-clearing sweep:

- **`0050` (List/Seq pretty-printer → MUST)** — requires a **type-directed display protocol** (a
  user-facing display trait the REPL dispatches through per value; `/arch` + `/dev src/` + `/stdlib`).
  A release-polish feature. → **Phase H.**
- **`0052` (`/learn` in-REPL guided tutorial)** — REPL feature work (watch mechanism, trigger
  evaluation, progress tracking) + `user/tutorial/` authoring; an onboarding/release-polish feature.
  → **Phase H.**
- **Tier-2 backend** (`--release`) — the genuinely-new-capability item. → **Phase H.**

These three are the known Phase-H scope; `0050`/`0052` are NOT S82 deferrals with TBD targets —
they have a home phase. Roadmap Phase-H row to be updated at S82 close to name them.

## FIXME debt

| FIXME | Target skill | Status | Workstream |
|---|---|---|---|
| 0337 | /dev src/ | open | D |
| 0338 | /dev src/ | open | D |
| 0340 | /dev backend+intrinsics | open | D |
| 0341 | /dev frontend | open | D |
| 0342 | /dev src/ (re-pointed from /typecheck — root = int load-ordering) | open | D |
| 0345 | /spec (+ /examples relayout) | RULED nested-only — fix §8.2.6 example; no int code | D dep |
| 0346 | /arch (+ frontend/typecheck cascade) | RULED option (a) `TypeExpr::Bounds`; types+tc halves done, frontend emit pending | D dep |
| 0347 | /design→backend | open (in-sprint: backend monomorphisation — lambda-name collision + recursive-fold wrong value; exposed by 0344 tc fix) | D (W2 backend) |
| 0343 | /dev src/ | open | D |
| 0344 | /dev typecheck | open | D |
| 0124 | /dev src/ | open | H |
| 0125 | /dev src/ | open | H |
| 0127 | /dev src/ | open | H |
| 0130 | /dev typecheck | open | H |
| 0133 | /dev backend | open | H |
| 0134 | /dev typecheck+backend+src/ | open | H |
| 0135 | /dev backend | open | H |
| 0136 | /qa | open | H |
| 0143 | /port | open | H |
| 0144 | /dev src/ | open | H |
| 0148 | /dev src/ | open | H |
| 0149 | /dev src/ | open | H |
| 0021 | /qa | open (blocked on 0336) | F |
| 0336 | /dev src/ | open | F |
| 0109 | /dev src/ | open (Waves A–C done S81; D remains) | F |
| 0243 | /dev typecheck | open | F |
| 0101 | /sprint | open | F |
| 0050 | /dev src/ | deferred | Phase H (display protocol) |
| 0052 | /repl | open | Phase H (/learn tutorial) |

## Architecture review (Phase 2)

**Verdict: APPROVE-WITH-REVISIONS** (/arch, S82). Coherent decks-clearing sprint, no new
language capability, near-zero public-API movement, no new `cranelisp-types` boundary type
required. The harvest partition respects bounded-context ownership. Four required revisions
(reflected in Scope/FIXME tables above) + sequencing recommendations.

**Public-API finding (key):** `int` has **no `public-api.txt` baseline** (a binary has no external
consumers; `facade_compliance.rs` excludes it; conformance gate = e2e suite, BC §6). So `0336`,
`0109` Wave D, and every int-internal defect fix carry **no baseline-diff obligation and no facade
update** — their contract lives in `src/` source rustdoc only. No defect fix touches a
`cranelisp-types` type (`0344` = internal infer.rs unification; `0342` uses existing
`SymbolTable`/`SymbolTableAccess`; `0341` = frontend parser; `0340` `DisplayDescriptor` already
authored). **S82 requires no `cranelisp-types` change.**

### Required revisions (applied to scope above)

1. **`0336` → mandate the `bench`-feature accessor, NOT a `[lib]` target.** A `[lib]` target on `src/`
   violates BC §6's application-root invariant ("Outward: nothing for other crates") and is a
   Principle-8 interim shape. Use a narrow `#[cfg(feature = "bench")] pub fn` over the filter-off
   `record_event` path, justified in source rustdoc.
2. **Repro-before-handoff wave gate for `0342` + `0340`** (root CLAUDE.md cross-skill rule). `0342`:
   `/qa` repro + Step-2 introspection must establish *missing-symbol* (→ int load-ordering) vs
   *present-but-unreached* (→ typecheck resolution) BEFORE `/dev` opens — typecheck's bounded
   module-locality walk (Principle 17) means "not found" is *correct* if the parent isn't committed
   yet, pointing at int orchestration. `0340`: **split into two repros** (timing — likely backend
   per-call rediscovery iterating all GOT slots; capture — likely intrinsics bodies/descriptor),
   each landing at its own crate.
3. **Re-scope `0101` to the post-D43 crates.** `cranelisp-runtime` no longer exists (split into
   `cranelisp-primitives` + `cranelisp-intrinsics` per D43; not a workspace member). The `0101` body's
   runtime LOC table is stale. Audit `cranelisp-primitives`, `cranelisp-intrinsics`, `cranelisp-platform`
   — auditing the as-was runtime crate would snapshot a superseded shape (the exact failure `0101`'s
   own sequencing note warns against).
4. **`0109` cites the retired `facades/int.md`** for its target export set — read BC §6 + `design/int/`
   + `src/` source rustdoc instead (facade retired S81 W-Retire, FIXME 0298). Pointer-only.

### Recommendations (non-blocking, carried to Phase 4)

- **Sequencing:** land `0109` Wave D *early* (it reshapes `session_v4.rs`/`worker.rs`); run the
  int-slice harvest against the *decomposed* shape, not the monolith.
- **Co-owner relabel:** `0130`/`0135` name "runtime" co-owner → post-D43 that is `intrinsics`
  (trace bodies) / `primitives`, not the retired runtime crate.
- **`0337`:** entry-name narrowing (`main` vs non-`main`) first — may localize the fix to the
  entry-module-naming path rather than general sibling-file resolution.
- **`0050`/`0052` → Phase H is architecturally correct** (`0050` needs new cross-crate surface: a
  display trait + backend dispatch + stdlib impls). No S82 action.

## Skill plans (Phase 3)

> Phase-3 design fan-out complete (6 agents: /qa + /design×5 crates). **Three findings reshape scope — see "Phase-3 escalations" in Notes.** Plans condensed below; full agent designs in their crate `design/{crate}/` docs + `tests/plan/sprint82-test-plan.md`.

### /qa — test plan + harvest measurement gate

- **Workstream D:** all 14 e2e guards + 2 unit repros already exist (S81). /qa's D work: the **repro-before-handoff probes** (`0342` introspection probe → already run, result = int ordering; `0340` split into timing+capture repros) and confirming each guard flips. **New Stage-1 authored failing-first:** `0340` timing guard (`(trace small)` <5s ceiling → backend); `0337` `tests/examples.rs` directory-entry coverage. **`0340` capture repro must be RE-SHAPED** (see escalation 3) — current repro traces `add-i64` (an invisible inline primitive), so empty trace is *correct*; re-point to a GOT-slotted callee.
- **Workstream H — harvest measurement gate (the confidence-to-delete centerpiece):** extends the existing S64 `wave-5.5/5.6` dedupe audits. Per file: every assertion → COVERED (name active test) | GAP (harvest as unit/e2e) | OBSOLETE (drop, written reason). Artifact `tests/plan/s82-harvest-{file}.md` with summary `N: C/G/O`. **A file is DONE only when deleted + FIXME closed.** Read-only audit fans out parallel; harvest edits serialize. `0134` partition confirmed; co-owner relabel `0130`→intrinsics / `0135`→primitives; `0136` sketch_port is /qa-internal (preserve 11 known-fail lineage as failing guards).
- **Acceptance:** 7 guards green; every legacy assertion dispositioned in writing; all 20 files deleted + 12 harvest FIXMEs closed.

### /design+/dev cranelisp-frontend — 0341

- **Parse fix** at `ast_builder.rs::build_annotated_params`: replace single `try_consume_annotation` with a loop accumulating the *run* of `:Trait` annotations onto the one following binder (single-bound = run-of-1, unchanged). Flips the existing frontend **unit** guard.
- **⚠ NOT self-sufficient (escalation 1):** the two **e2e** guards need (a) a `cranelisp-types` carrier for N>1 bounds (param slot is `Vec<(Symbol, Option<TypeExpr>)>` — one bound/binder) and (b) a typecheck try-type-then-trait change at `program.rs:1856`. Frontend fix alone flips only the unit guard.

### /design+/dev cranelisp-typecheck — 0344, 0342, 0243

- **0344:** root cause verified — Pass-2 sibling calls instantiate the callee's `Type::Fn` *verbatim* (empty `type_vars`, no fresh copy) so `b`/`a`/`Vec` fuse in the shared subst. Fix: per-defn post-body generalization writeback to `ModuleEntry::Def.scheme` in `check_form_body_single_defn` (reuse existing `generalize`); keep monomorphic recursion. Flips the present unit + e2e guards.
- **0342:** **investigated to root = int load-ordering, NOT typecheck → typecheck branch is a NO-OP.** Re-point `0342` ownership /typecheck → /int (escalation 2).
- **0243:** per-cluster narrowing adt.rs→checker→traits→shared-helpers (risk-ordered, one helper per test-run); add dependency-closure to `FixtureBuilder::seed()` if the order footgun bites.

### /design+/dev cranelisp-backend — 0340 timing + harvest 0133/0135

- **0340 timing:** root cause = **no memoization** of trace-wrapper compilation; every `(trace …)` discovers all GOT-slotted prelude+primitive callables (swap-all per `tracing.md §5`) and compiles a fresh Cranelift wrapper for each = hundreds of compiles ≈ 31s. Fix (Lever A): memoize wrappers once-per-compile keyed on traced-fn identity; preserve swap-all completeness (no project-root filter). Backend-internal — no cross-crate change. Unit guard: count-based (wrappers compiled = K once, not M×K per form).
- **Harvest 0133/0135:** backend slices already landed S81 W-C; only optional remainder = a 0135 Par-node CLIF-inspection unit. Non-backend remainders route to primitives/int.

### /design+/dev cranelisp-intrinsics — 0340 capture + harvest 0130 slice

- **0340 capture: NON-DEFECT (escalation 3).** Reproduced live: degenerate `(Trace.TraceCall "::trace::" SNil …)` is the *faithful* empty-trace rendering — `add-i64` is inline CLIF arithmetic with no GOT slot, never wrapped, so empty trace is *correct*. The 12 trace bodies capture name+operands correctly (2 passing sibling tests prove it). **Fix routes to /qa (re-shape repro to a GOT-slotted callee), NOT an intrinsics body change.** Durable intrinsics deliverable: a direct-body capture-fidelity `#[cfg(test)]` guard. If a non-degenerate empty-trace shape is later mandated → /arch+/spec (NOT filed — evidence says current shape is faithful).
- **Harvest 0130 slice:** trace-body/accessor-offset/RC, nested-guard transitions, empty/skip shapes, panic-unwind cleanup as direct-body units (disjoint from typecheck's type-taxonomy slice).

### /design+/dev src/ (int) — 0343, 0337, 0338, 0342, 0336, 0109 Wave D

- **0343 (HIGH):** role-gate `regenerate_backing_file` to the entry-module persistence role (S78 `eval_owned`/`entry_module`, not the `/mod` cursor, not a name match) + a submodule-body-preservation guard (don't blind-overwrite a `(mod …)`-bearing file the table can't round-trip).
- **0337:** **root = SPEC CONTRADICTION (escalation 2)** — §8.2.5 (nested-only, which the impl correctly follows) vs §8.2.6 example + `examples/16-modules/` (siblings). Needs `/spec` arbitration (FIXME 0345) BEFORE int work; fix is conditional on the ruling. NOT entry-name-specific (qa confirmed).
- **0338:** retire the hardcoded special-form signature table → read schemes from the root `""` SpecialForm entries (single source); route `/sig`//`/info` through the root-`""` fallback `describe_symbol` already uses. Folds into the repl.rs extraction. Cosmetic `(from module '')` → optional /arch.
- **0342:** int load-ordering fix — defer inline-`(mod)` submodule register+block from Pass-0 until the parent commits to live (`finalize_cluster`), then drive submodules; idempotent on retry; both worker + REPL entries.
- **0336:** `#[cfg(feature="bench")] pub fn bench_record_event_off_path` in `io_trace.rs` + `[features] bench` (NO `[lib]`).
- **0109 Wave D (land EARLY):** extract `eval.rs` → `repl.rs` (with the deliberate `pub(crate)` field-widening first) → residual `session_v4.rs` (now 6,893 LOC) → collapse `worker.rs` mirrored pairs. In-file tests migrate with code (harvest homes).

## Waves (Phase 4)

**Execution rule (project constraint):** source-editing agents run **serially** (shared working tree; worktree isolation broken). Only **read-only** fan-outs run truly in parallel — here that is the harvest measurement-gate audit. "Per-crate" batches below are logical groupings executed one-at-a-time; batching a crate's defect-fix + harvest + review together minimizes context-switching (the Stage-2 per-crate D/D/R model).

**Hard dependencies:** `TypeExpr::Bounds` (W0) ⇒ frontend+typecheck `0341` (W2); `0109` Wave D (W1) ⇒ int harvest + `0338` repl.rs fold (W2); measurement-gate audit (W0, read-only) ⇒ all harvest (W2); `0336` accessor ⇒ `0021` bench (W3); `0345`/`0346` rulings ⇒ already locked.

### Wave 0 — Foundations, rulings, QA-first (Phase 5 Stage 1)

| Skill | Crate | Task | Parallel? |
|---|---|---|---|
| /arch | cranelisp-types | Add `TypeExpr::Bounds(Vec<TraitRef>)` (param tuple unchanged); regen `public-api.txt`; interfaces.md narrative (FIXME 0346) | serial (source) |
| /spec | spec/ | Fix §8.2.6 worked example to nested layout (FIXME 0345); confirm §8.2.5 normative | serial (doc) |
| /qa | tests/ | **Harvest measurement-gate audit** — per-file dedup map for all 20 legacy files (`tests/plan/s82-harvest-*.md`) | **parallel (read-only fan-out)** |
| /qa | tests/ | Stage-1 failing-first: `0340` timing guard (<5s); `0337` multi-file-dir CI coverage; **re-shape `0340` capture repro** to a GOT-slotted callee | serial (source) |

### Wave 1 — int decomposition (0109 Wave D) — land EARLY

| Skill | Crate | Task |
|---|---|---|
| /dev → /review | src/ | Extract `eval.rs` → `repl.rs` (with deliberate `pub(crate)` field-widening) → residual `session_v4.rs`; collapse `worker.rs` mirrored pairs. In-file tests migrate with code. Suite stays green (14+2 known guards). |

### Wave 2 — per-crate defect fixes + harvest + review (Stage 2 D/D/R; serial by crate)

| Skill | Crate | Defects (flip guards) | Harvest (after gate) |
|---|---|---|---|
| /dev → /review | cranelisp-frontend | `0341` parse-loop + emit `Bounds` (after W0) | — |
| /dev → /review | cranelisp-typecheck | `0344` generalization writeback; `0341` typecheck half (try-type-then-trait + constraint accum); `0243` fixture narrowing | `0134` tc-slice; `0130` tc-slice |
| /dev → /review | cranelisp-backend | `0340` timing (memoize wrappers once-per-compile) | `0133`; `0135`; `0134` backend-slice |
| /dev → /review | cranelisp-intrinsics | `0340` capture-fidelity guard (no body fix — non-defect) | `0130` intrinsics-slice |
| /dev → /review | src/ | `0343` regen role-gate (HIGH); `0338` self-doc (folds into W1 repl.rs); `0342` load-ordering; `0336` bench accessor. `0337` = no int code (nested-only) | `0124`,`0125`,`0127`,`0144`,`0148`,`0149`; `0134` int-slice (mostly delete — e2e-covered) |
| /qa | tests/legacy | — | `0136` sketch_port (preserve 11 known-fail lineage) |
| /port | examples/exemplar | — | `0143` examples/exemplar |

Each harvested file: GAP tests landed green → **delete file + README row + close FIXME** (one commit). A file is DONE only when deleted.

### Wave 3 — F-tail (sequential)

| Skill | Crate | Task |
|---|---|---|
| /qa | benches/ | `0021` criterion microbench (<1% off-path) — after `0336` accessor lands; tighten integration ceiling |
| /sprint + audit | primitives/intrinsics/platform | `0101` audit passes (post-D43 crates); file remediation FIXMEs from findings |

### Wave gate (before any advance)
Scan `design/arch/fixmes/` for `target: /skill-in-wave` + `status: open`. Currently `0345` (/spec) + `0346` (/arch) are ruled-but-not-yet-executed — they resolve in W0. All harvest FIXMEs resolve as their files delete in W2.

### Phase 6 (after Phase 5 waves) — user-facing
`/repl`, `/port`, `/stdlib`, `/examples`, `/docs` assess delivered state + act. **`/examples` relays out `16-modules/` to nested** (0337 ruling). Prior demos replay green.

## Notes

- S82 planning opened from a between-sprints state (S81 closed clean: 1290 passed / 14 failing-not-ignored defect guards / 0 skipped).
- User direction (S82 planning): include the legacy-harvest folding exercise so the legacy tests can be **deleted confidently**; clear the other outstanding FIXMEs and defects too.
- **Harvest commitment — (a) FULL harvest committed in S82** (user, S82 planning): the harvest segregates cleanly (each legacy file is an independent unit: audit → harvest gaps → delete), so it parallelises logically including the XL `0134` bulk. **Execution constraint** carried to Phase 4: per CLAUDE.md "single agent at a time for source-touching work" (shared working tree; worktree isolation broken) — the read-only dedup-audit fans out in parallel, but harvest *edits* serialize per file (independent units, serial commits). The whole-file-deletion discipline keeps any under-run shipping complete units.
- **`0050` + `0052` assigned to Phase H** (user, S82 planning): Phase H reframed as the release phase (Tier-2 backend + release-polish features). Update the roadmap Phase-H row at S82 close to name the display protocol (`0050`) + `/learn` tutorial (`0052`) alongside the Tier-2 backend.

### Phase-3 escalations (design fan-out, S82) — change scope vs Phase-2

1. **`0341` is a 3-crate defect, not a frontend-only fix — overturns Phase-2 "no `cranelisp-types` change."** The frontend parse fix flips only the *unit* guard; the two *e2e* guards need a `cranelisp-types` carrier for N>1 stacked bounds (param slot is `Vec<(Symbol, Option<TypeExpr>)>` = one bound/binder) + a typecheck try-type-then-trait change (`program.rs:1856`). **Action: re-fire `/arch`** to decide the carrier shape (new boundary type / variant vs separate per-variant constraints field) — the Phase-3 interface set is NOT complete without it. File **FIXME `target: /arch`** (0346) for the carrier decision.
2. **`0337` needs a `/spec` arbitration before int work** — `spec/08-modules.md §8.2.5` (nested-only, which the impl correctly follows) directly contradicts `§8.2.6`'s sibling example + the `examples/16-modules/` layout. **Action: file FIXME `target: /spec` (0345)** + re-fire `/spec` to rule. Int fix is conditional on the ruling (no int code change if §8.2.5 wins → instead `/examples` relayouts + `/spec` fixes the example).
3. **`0340` capture half is a NON-DEFECT** — reproduced live: the degenerate output is the faithful empty-trace rendering of tracing an inline primitive (`add-i64`, no GOT slot). Bodies capture correctly. **Action: scope shrinks** — no intrinsics body fix; `/qa` re-shapes the capture repro to a GOT-slotted callee. The timing half (backend memoization) is the real `0340` defect.
4. **`0342` re-points /typecheck → /int** (root = int load-ordering; typecheck branch is a no-op). Clean; src/ design owns the fix.
- **Net:** S82 now touches `cranelisp-types` (via `0341` carrier) and adds `/spec`+`/examples` (`0337`).

**Escalation rulings (user, S82 Phase 3, 2026-06-14) — Phase-3 exit gate cleared:**
- **A / `0337` → nested-only (recommit to §8.2.5).** No int code. `/spec` fixes its §8.2.6 example; `/examples` relays out `16-modules/` to nested; `/qa` adds the multi-file-dir CI coverage. (FIXME 0345 ruled.)
- **B / `0341` → option (a) `TypeExpr::Bounds(Vec<TraitRef>)`.** Sidecar rejected (can't be concretely typed AND constrained — the slot is one-of {type, bounds}). `/arch` adds the variant to `cranelisp-types` (param tuple unchanged → minimal ripple) + regens baseline; frontend emits it; typecheck adds try-type-then-trait + constraint accumulation at `program.rs:1856`. (FIXME 0346 ruled.)
- Interface set is now confirmed (the one new boundary item is `TypeExpr::Bounds`). The actual `cranelisp-types` edit + spec-example fix are folded into Phase-5 Wave 0 (ratification), not re-fired as standalone design agents.

## Phase 5 execution log

### Wave 0 — DONE (foundations + measurement gate)
- **/arch — `TypeExpr::Bounds(Vec<TraitRef>)` landed** in `cranelisp-types` (`ast.rs`); baseline regenerated (`+pub …TypeExpr::Bounds…`); `interfaces.md` updated; `cargo check -p cranelisp-types` green. **Param tuple unchanged** (zero churn). FIXME 0346 updated (types-half done; frontend+typecheck cascade pending W2). **Build now RED** — typecheck has 5 exhaustive `match` sites needing a `Bounds` arm: `form.rs:404` (no-op), `resolve.rs:34` (the try-type-then-trait + `Scheme.constraints` accumulation = 0341 tc-half), `traits.rs:1744/1796/1861`. frontend = emission only (no match breaks); backend + src/ clean (catchall).
- **/qa — harvest measurement gate COMPLETE** (read-only; 9 disposition docs + `tests/plan/s82-harvest-rollup.md`). **1,323 tests → 356 GAP (57 reg-guards) / 960 COVERED / 7 OBSOLETE.** Harvest is ~73% audit-and-delete, 27% real porting. `0134` partition confirmed; `0130`→intrinsics / `0135`→primitives co-owners; `0136` 11-failure lineage preserved as failing-not-ignored GAP.
- **Remaining W0:** /spec §8.2.6 nested-example fix (doc); /qa Stage-1 failing-first tests (0340 timing, 0337 CI dir-coverage, re-shape 0340 capture repro) — deferred until build green.

### Wave 2 (started early — restore green) — IN PROGRESS
- **typecheck DONE — build GREEN restored.** `cargo check --workspace` green; typecheck 379/379; full suite 1290 pass / 14 known guards (no new regressions). 0341 tc-half (`Bounds` arms + `program.rs::resolve_bound_param` try-type-then-trait + constraint accumulation; new tc unit passes). 0344 tc-half (generalization writeback; **0344 unit guard flipped green**).
- **In-sprint discovery → FIXME 0347 (target /design→backend):** the 0344 tc fix exposed the e2e failure is downstream **backend monomorphisation** (improved type-error → runtime-wrong-value, exit 0 vs 6). Two backend bugs: (1) span-derived `__lambda_<start>_<end>__` name collision on monomorphising a lambda-bodied polymorphic fn; (2) monomorphised recursive fold returns wrong value. A typecheck-side `expr_contains_lambda` band-aid keeps 4 examples green until backend lands; remove it then. **0347 joins backend W2 scope.**
- **frontend DONE — 0341 FULLY CLOSED** (parse-loop + `Bounds` emission; run-length disambiguator N≥2→Bounds). Both 0341 e2e guards (`stacked_trait_bounds_{single,two}_param(s)_compiles`) flipped GREEN + frontend unit guard + 4 regression units. frontend 282/282; workspace green.
- **DISCOVERY — 3 pre-existing uncatalogued backend failures:** `cranelisp-backend tests::decision_23_got_data_{size_matches_slot_count, symbol_defined_as_export_in_object_path, symbol_not_in_bss}`. Confirmed pre-existing (backend/src byte-identical to S81-close HEAD; backend-internal GOT-emission units, not reachable by any S82 change). NOT in the documented 14-guard or "11 sketch_port + 2 v4_platform" sets — the "1290/14" integration count missed them (they're unit-tier). `__cranelisp_got_util` is present-in-list yet asserts fail → possibly stale assertion vs. real GOT bug. **Folded into backend W2 triage** (fits "clear outstanding defects"). Ledger entry owed at close.
- **Guards remaining:** 12 (0337×2, 0338×4, 0340×2, 0342×2, 0343×1, 0344-e2e×1) + 3 decision_23.
- **backend DONE.** **0340 timing FIXED ~37s→~130ms** — real cause was exponential descriptor re-baking over recursive ADTs (Sexp/SList), not wrapper-memo; fixed via `BakeMemo` cycle-break + DAG-share; bounded guard added. **0347 defect (1) lambda-name collision FIXED** (`inner_fn_discriminator` prefixes enclosing-fn name across 6 span-derived sites; guard added). **0347 defect (2) recursive-fold → re-attributed to int, FIXME 0348** (got_slot reassigned 2→0 between entry module's two compile passes; backend CLIF byte-identical; backend stopped at boundary). **decision_23×3 = STALE TEST** (Mach-O-only symbol matcher broke on ELF; real GOT emission correct) → fixed platform-agnostic, 3 GREEN. backend 219/219; workspace 2499 pass / 12 known guards.
- **0344 = 3-layer bug:** typecheck (over-unify, FIXED) → backend (lambda-name, FIXED) → int (got_slot reassignment, FIXME 0348). e2e flips when int fixes 0348. typecheck `expr_contains_lambda` band-aid now safe to remove (defect-1 fixed) — typecheck follow-up owed.
- **FIXME 0348 (target /design→int):** entry-module got_slot reassignment across its two compile_to_module passes; joins src/ W2 scope.
- **intrinsics DONE.** 0340 capture-fidelity durable guard + empty-trace-is-faithful companion guard added; **no trace-body change** (capture = non-defect confirmed). intrinsics 140/140. /qa to re-shape the e2e capture repro to a GOT-slotted callee.
- **0109 Wave D DONE (pure refactor, behaviorally equivalent).** `session_v4.rs` 6,893→3,946; new `eval.rs` (567) + `repl.rs` (2,475, with 4 migrated test modules); 6 fields → `pub(crate)`; `worker.rs` macro-clause mirror collapsed to `compile_macro_clause_core`. Workspace 12-guard equivalent. `src/CLAUDE.md` updated with §3.3 map. **0109 Wave D closes.**
- **src/ defects IN FLIGHT (background agent):** 0343/0338/0342/0336/0348.
- **/spec DONE (0345 spec-half):** §8.2.6 corrected to nested layout + 4 more sibling-implying passages aligned (§8.1.1, §8.7.3, §8.3.10, §8.15); `spec/08-modules.md` self-consistent on nested-only. 0345 stays open pending /examples relayout + /qa CI coverage (both Phase 6 / qa wave).
- **src/ defects DONE — suite 2514 pass / 6 fail** (from 16 guards at S81 close). FLIPPED: 0343 (regen role-gate), 0338 (×4 self-doc), 0336 (bench accessor, no [lib]), 0342 parent-fn (Pass-0 defer-submodule-drive). Boundary findings: **0348→typecheck (FIXME 0349)** — GOT slots stable; real cause = typecheck mono not creating `reduce$Int+Vec` variant under forward-ref order (kept the int commit-order sort as a real improvement + guard unit). **0342 ctor guard = bad fixture** (postfix `[b :superp/Box]` invalid; `:Type` binds following form) + typecheck self-qualified-type.
- **6 reds remain (none int-owned):** 0344-e2e→typecheck(0349); 0342-ctor→fixture+typecheck; 0337×2→guards still assert SIBLING (must rewrite to nested per ruling); 0340×2→/qa re-shape capture repro to GOT-slotted callee.
- **FIXME 0349 (target /typecheck):** monomorphisation must create the mono variant regardless of caller/callee definition order (the 4th + final layer of the 0344 bug).
- **typecheck DONE — 0344 FULLY CLOSED (4-layer bug resolved).** 0349 fix (pass4 scans all bodies excl. self-recursion; mono unifies return back into call-site; re-generalize after pass4) → 0344 e2e GREEN. typecheck 380/380. Workspace **2516 pass / 5 fail**. Band-aid NOT removed — backend defect-1 half-fixed (closure drop-glue name still span-derived → dup-def) → **FIXME 0350 (target backend)**; 4 examples stay green via gate. (Transient disk-full handled: cleared 9.4G incremental; stash/pop clean.)
- **FIXME 0350 (target /design→backend):** `runtime/closure_drop_glue_<start>_<end>` span-derived name collides on mono of a lambda-bodied poly fn; uniquify per-instance to allow band-aid removal + the 4 examples.
- **5 reds left (all /qa test-fix):** 0337×2 (guards encode OLD sibling expectation → rewrite to nested), 0342-ctor (postfix-annotation fixture bug + typecheck self-qualified-type tail), 0340×2 (capture repro → re-shape to GOT-slotted callee).
- **/qa test-fixes DONE — WORKSTREAM D COMPLETE: workspace 2523 pass / 0 fail / 0 skip.** 0337×2 rewritten to nested (+ self-contained multi-file-dir CI coverage in `tests/examples.rs`); 0340×2 re-shaped to GOT-slotted callee (`(trace (greet "bob"))`) + 0340 timing e2e (<5s); 0342 ctor fixture fixed (postfix→match) → green. ALL defect guards green.
- **0342 typecheck tail (2 newly-found pre-existing defects, NOT reds — guard green via match workaround):** (a) field-name accessor not a free callable (`(v b)` → undefined); (b) self-qualified type ref `:superp/Box` inside its own module → unknown type. Filed **FIXME 0351 (target /typecheck)**; failing repros owed (fold into harvest /qa) → deferred to S83 (tangential, late-discovered).
- **WORKSTREAM D: COMPLETE** (all 7 Phase-6 defects + discovered 0347-d1/decision_23×3/0348→0349). Debt: FIXME 0350 (backend drop-glue → band-aid removal), FIXME 0351 (0342 tail, S83).
### WORKSTREAM H — harvest (356 gaps port + 967 delete-on-confirm). Per-crate PORT (no delete) → final deletion sweep.
- **backend harvest DONE.** FIXME 0350 LANDED (drop-glue uniquified per mono-instance; unblocks band-aid removal). Ported: 0133 (6/6), 0135 backend slice (2 Par-codegen units; **3 gaps are /platform-owned** — DLL classification fixture), 0134 backend slice (Vec-COW/RC + recursive-descriptor bake suite). Workspace **2534 pass / 0 fail**. No legacy file deleted.
- **typecheck harvest DONE.** 0344 band-aid REMOVED (gate deleted; 4 examples green; 0350 confirmed → 0344 fully clean, no debt). 0243 RESOLVED (all fixtures narrowed, no remainder). 7 harvest units ported (0130/0125/0134 tc-slice); many dispositioned gaps re-judged e2e-owned/covered. typecheck 387; workspace **2541 pass / 0 fail**.
- **Harvest crate order:** ✅backend ✅typecheck ✅intrinsics (2550) ✅/platform (2555) ✅src/ (ZERO int units — all int gaps e2e-covered/cross-crate; 2555) → /qa endgame (0136 + 0351 + verify-and-delete sweep) → /port (0143) → W3 → Phase 6.
- **Coordination note for sweep:** repl_experience(0124, 85g) + io(0127, 38g) map to backend-display/typecheck-inference/qa-e2e (not routed to those crates' harvests — their prompts covered only 0134/0130/0133/0135). Sweep MUST re-verify coverage before deleting; carry genuine residue honestly with FIXME (don't delete a file with un-ported genuine gaps).
- Disk managed: cleared incremental cache (9.7G free).
- **HARVEST ENDGAME DONE.** **15/20 files DELETED** (incl. ALL XL bulk: e2e/ring0/ring1/ring2/sketch_port ~1,300 tests, every assertion re-verified covered) + **8 FIXMEs closed** (0125/0130/0133/0134/0136/0143/0148/0149). 0136 covered (+1 unit). 0351 repros authored (2 RED, S83; spec confirms BOTH genuine defects — accessors ARE free fns §5.2.6, self-qualified refs SHOULD resolve §8.5). Workspace **2556 pass / 2 fail (=0351 guards)**.
- **5 files KEPT (honest carry, 147 genuine gaps, FIXMEs OPEN w/ precise residue):** repl_experience(0124,85 display+typevar→backend/typecheck), repl_negative_old(0124,18), io(0127,38→platform/backend/typecheck/stdlib), lenient(0135,5→backend/platform), sprint23(0144,1→backend cache). These weren't routed to owning-crate harvests (my W2 harvest prompts scoped only 0134/0130/0133/0135).
- **FLAG:** `session_v4::persistent_worker_tests::reload_during_compile_race_completes` — real intermittent race (pre-existing; roadmap S82 candidate "deflake reload_during_compile_race"); /dev int.
- **DECISION (user): FULL-CLEAR all 5 residual files — one subagent per file, serial series.**
- ✅ **HARVEST COMPLETE — 20/20 legacy files DELETED; all 12 harvest FIXMEs CLOSED** (0124/0125/0127/0130/0133/0134/0135/0136/0143/0144/0148/0149). `tests/legacy/` = README only. Per-file full-clear: repl_experience (15 ported/175 covered), repl_negative_old (9/9 — closed 0124), io (28 ported/10 covered — closed 0127), lenient (1 ported/4 covered/2→FIXME 0353 — closed 0135), sprint23 (1 ported — closed 0144). Two socket-error agents resumed cleanly. Workspace **2604 pass / 2 fail (=0351 guards)**.
- **New S83-deferred FIXMEs filed during harvest:** 0351 (typecheck self-qualified-type + field-accessor, 2 RED guards), 0352 (/list raw type vars → backend), 0353 (ResourceSerial token e2e DLL fixture → platform/qa).
- **WORKSTREAMS D + H: COMPLETE.**
- ✅ **reload_during_compile_race FIXED at root** (/dev int) — scheduler publish-ordering race (`inmem_done` set mid-codegen → reload re-register skipped during `TypecheckWorking`); fix = `wait_module_typecheck_settled` before re-register + `completion.notify_all()` on typecheck-done. **0/150 stress iterations** (was ~20%). No FIXME needed.
- ✅ **0021 + 0336 CLOSED** — criterion bench `benches/io_trace_off_path.rs`; off-path guard ~0.29ns constant → <1% AC MET for all real event sites. Workspace **2604 / 2**.
- **0101 → SCHEDULE** (audits over post-D43 primitives/intrinsics/platform queued to a dedicated audit sprint per the FIXME's own "schedule in a future sprint" framing; re-scoped at close).

### PHASE 6 — user-facing (defect fixes unblocked stdlib features)
- The S82 fixes unblocked: 0341 (assert-eq stacked bounds), 0342 (super-import in `(mod test)`), 0343 (mod-test source-regen), 0344 (vec-reduce fold) — /stdlib can restore testing.assertions + `(mod test)` self-tests + the fold helper.
- ✅ /examples: 16-modules relaid out nested (exit 47=303%256), example suite green, **0345 CLOSED**.
- ✅ /stdlib: **0344 vec-reduce restored+verified** (scheme `(Fn [(Fn [a b] a) a (Vec b)] a)`, `(vec-reduce add-i64 0 [1 2 3])`⇒6); **0342+0343 verified** — `(mod test)` self-tests restored (assert-true/false based; 4 pass via in-language runner, source not clobbered); testing.assertions loads.
- ⚠ **Phase-6 DISCOVERY — FIXME 0354 (target /typecheck): 0341 cross-module path SIGSEGVs.** A stacked-bound fn defined in an IMPORTED module segfaults when called (same-module works → our 3 guards green). `Bounds` carrier corrupts across module serialize/reload (`:Display :Display :Eq` dup), mis-driving monomorphisation. assert-eq loads but can't be called cross-module. Forward-flow S83 (Phase-6-pattern, like S81's 7 defects). 0341 same-module DELIVERED+guarded; cross-module = deeper newly-found layer.
- ✅ /qa: 0354 failing repro authored; close-validation — all S82 fixes hold (exemplar + every defect guard green).

### 0354 SIGSEGV — RESOLVED IN-SPRINT (user: don't ship a SIGSEGV; take facade pain early)
- **Isolation** (2 subagent passes): NOT serialize/reload corruption. Root cause = a constrained *template* carries a phantom `got_slot` (`register_defn_signature` allocates in Pass 1 before constraint detection flips `kind` in Pass 2, leaving the slot); `resolve_got_target` reads it blind to `constrained_fn`; cross-module the slot is NULL → `call_indirect` through null → SIGSEGV. Slot-level evidence: `(helper, slot=0) = 0x0`. User's instinct confirmed — the call shouldn't have been emittable.
- **/arch** chose the SSOT-accessor form (Principle 18 SSOT, not full restructure — full-B = 180-site churn + Decision-35 reversal + Pass-1 timing wall): added `ModuleEntry::callable_got_slot()` (None for templates) + `mark_constrained_template()` (sole atomic writer) additively to cranelisp-types; baseline regenerated; BC §7 + interfaces.md updated.
- **/dev cascade:** backend `resolve_got_target` reads `callable_got_slot()` → **SIGSEGV becomes a clean type error (exit 1, not 139)**; typecheck uses `mark_constrained_template` (sole-writer); **Bug A fixed** (generalize dedup + production-path constraint reset → clean `[Eq, Display]` witness); 0354 repro repointed to assert clean rejection → GREEN; **0354 CLOSED**.
- **FIXME 0355** (target /typecheck, S83): cross-module-mono FEATURE (make the call RUN → exit 2). **FIXME 0356** (target /arch, S83, user-directed): make callability STRUCTURAL — the facade should EXPRESS the intent (constrained template can't hold a callable slot, unrepresentable), bundle with 0355.
- **Final red set: ONLY the 2 `0351` guards** (S83 /typecheck). Workspace **2607 pass / 2 fail / 0 skip**. No SIGSEGV.
- **Note (audit-and-delete working):** crate agents are re-judging many dispositioned GAPs as e2e-owned/already-covered → genuine crate-internal porting is lighter than the raw 356; deletion sweep re-verifies before deleting.

## Outcome (Phase 7)

**Final baseline: 2607 passed / 2 failing-not-ignored S83 guards / 0 skipped** (from S81 close 1290/14 — the corpus grew via harvest-ports + new units). The 2 reds are both `0351` (self-qualified-type ref, field-accessor-as-free-callable), targeting /typecheck for S83. **No SIGSEGV** — `0354` resolved in-sprint (see below).

### Delivered

**Workstream D — all 7 Phase-6 defects closed** (+ 5 discovered-and-fixed in-sprint):
- `0337` sibling-module — RULED nested-only (§8.2.5 normative); /spec fixed §8.2.6 + 4 sibling-implying passages; guards rewritten to nested; multi-file-dir CI coverage added; examples relaid out. No int code (impl was correct).
- `0338` REPL self-doc — special-form `:Type` prefix from root entries + `/info`/`/sig` root-fallback (4 guards).
- `0340` trace — **timing ~37s→~130ms** (real cause: exponential descriptor re-baking over recursive ADTs → `BakeMemo`; NOT the hypothesized wrapper-memo); capture confirmed non-defect (inline primitive) → repro re-shaped; timing e2e guard added.
- `0341` stacked trait bounds — `TypeExpr::Bounds` carrier + frontend emit + typecheck try-type-then-trait (same-module: unit + 2 e2e green). Cross-module path → `0354` (S83).
- `0342` super-import — int load-ordering fix (defer submodule drive past parent commit); typecheck branch confirmed no-op.
- `0343` (HIGH data-loss) — regen role-gate to entry-module + submodule-body-preservation.
- `0344` — **4-layer bug fully resolved**: typecheck over-unify → backend lambda-name → int got_slot (stable) → typecheck mono-variant (`0349`).
- Discovered+fixed: `0347`-d1 (lambda-name collision), `decision_23`×3 (stale Mach-O-only test assertion broke on ELF), `0348`→`0349` (forward-ref mono variant creation), `0350` (closure drop-glue uniquification → band-aid removed), **`reload_during_compile_race`** (scheduler publish-ordering race; 0/150 stress).

**Workstream H — legacy harvest COMPLETE**: measurement gate dispositioned all 1,323 quarantined tests (356 gap / 960 covered / 7 obsolete — 73% audit-and-delete); **20/20 files deleted; all 12 harvest FIXMEs closed**; genuine gaps ported across backend/typecheck/intrinsics/platform/qa (crate agents repeatedly re-judged dispositioned gaps as already-e2e-covered, shrinking real ports well below 356). `tests/legacy/` = README only.

**Workstream F**: `0109` Wave D (session_v4.rs 6,893→3,946; eval.rs+repl.rs extracted; worker mirror collapsed); `0243` (typecheck fixtures narrowed, resolved); `0021`+`0336` (criterion bench, off-path guard ~0.29ns < 1% AC, closed); `0345` (closed). `0101` → SCHEDULED (post-D43 primitives/intrinsics/platform audits to a dedicated audit sprint).

**Foundation**: `TypeExpr::Bounds` added to cranelisp-types (baseline regenerated). **Phase 6**: examples relaid out nested; stdlib vec-reduce + `(mod test)` self-tests restored.

### 0354 cross-module constrained-call SIGSEGV — RESOLVED IN-SPRINT (user-directed)
User declined to ship a SIGSEGV. 2-pass subagent isolation → root cause = constrained template carrying a phantom `got_slot` read blind by `resolve_got_target` → null `call_indirect`. /arch added SSOT accessors to `ModuleEntry` (`callable_got_slot`/`mark_constrained_template`, additive); /dev cascade converted the crash to a **clean type error** + fixed Bug A (constraint dedup). `0354` CLOSED; repro green. **FIXME 0355** (cross-module-mono FEATURE → make it run, S83 /typecheck) + **FIXME 0356** (user-directed: make callability STRUCTURAL so the facade expresses the intent — unrepresentable illegal state; bundle with 0355, S83 /arch).

### Deferred (with rationale) — all S83, all with failing repros / FIXMEs
- `0351` (typecheck self-qualified-type ref + field-accessor-as-free-callable; **2 RED guards**; spec-confirmed genuine defects) — tangential, late-discovered while fixing the 0342 fixture.
- `0355` (cross-module constrained-fn monomorphisation — the feature; /typecheck) + `0356` (callability-as-structural facade fix; /arch) — bundle in S83.
- `0352` (`/list` shows raw type vars `t1` vs normalized `a` → backend), `0353` (ResourceSerial token e2e needs DLL fixture → platform/qa).
- `0101` (post-D43 primitives/intrinsics/platform audits → dedicated audit sprint).
- `0356` (callability-as-structural facade fix; /arch) + `0357` (**model cross-field invariants by REPRESENTATION — sum type whose variants = legal states, "parse don't validate"; accessor only as fallback** — the systemic root of the recurring "180 locations" churn; candidate new Principle; amends Decision 0035; /arch). Bundle the `ModuleEntry`/`got_slot` collapse with `0355`/`0356`.

### Findings
- **Layered bugs dominated**: `0344` (4 layers), `0340` (timing/capture split), `0347`→`0348`→`0349`→`0350` cascade. The repro-before-handoff + stop-at-boundary discipline routed each correctly; agents re-attributed defects across crate lines 4× without forcing wrong-crate fixes.
- **Measurement-gate ROI**: 73% of the legacy corpus was already covered — "audit-and-delete" massively beat "re-port 1,323". The confidence-to-delete artifact (per-file disposition + rollup) made full deletion safe.
- **Field corrections beat design hypotheses**: 0340's real cause (descriptor re-bake) ≠ the Phase-3 wrapper-memo hypothesis; profiling found it. 0348's "got_slot reassignment" was actually stable slots + a missing mono variant.
- **Reinstated Phase 6 earned its keep again**: surfaced `0354` (a SIGSEGV) — the same value that surfaced S81's 7 defects.
- **Infra resilience**: 2 agents hit API socket errors mid-run; both resumed cleanly via SendMessage with no lost work. Disk pressure (30G VM) managed by clearing incremental cache between heavy waves.
- **nested-only ruling** dissolved a "defect" (0337) into a spec self-consistency fix + relayout — no compiler change.

### Close actions (on approval)
- Update `sprints/ROADMAP.md`: S82 row (Clean & Green II — defects + full legacy harvest + FIXME drawdown) COMPLETE; Phase-H row to name `0050` (display protocol) + `0052` (/learn) alongside Tier-2 backend; note S83 carries (0351/0352/0353/0354 + 0101 audit sprint).
- `git mv sprints/SPRINT.md sprints/archive/sprint-82.md`; commit to `main` (no push without request).
- Consider whether arch principles served the sprint: 6/8/17/18 + manifestation-site + repro-before-handoff all held. **ONE candidate gap surfaced (user-raised at close):** the recurring "180 locations" churn on cross-field invariant changes points to a missing **read-side encapsulation Principle** — construction is buildered but reads are raw `pub`-field pattern-matches (≈514 `ModuleEntry::Def` / 435 `got_slot` sites), so cross-field invariants have no read chokepoint. Filed `0357` for `/arch` to evaluate as a new Principle — **representation-first: model a cross-field invariant as a sum type whose variants are the legal states (illegal state unconstructable, "parse don't validate"); intent-accessor + sole-writer is the explicit fallback only where the collapse is blocked**. The recurring "180 locations" churn is the symptom; the root is correlated fields modelled as independent `Option`s (the illegal pair is constructable). This is the structural root the user pushed on via `0356`; amends Decision 0035.
