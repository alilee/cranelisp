# Sprint 77: Settle the architecture, then get to green — Stage 1 of the post-arc consolidation

**Status**: PHASE 5 LANGUAGE (ACTIVE) — W0 complete + committed (`ae4ede9`); QA-first + W-Fix underway

**Goal**: Establish that **the facade is genuinely sound** (survey + resolve all 21 outstanding architectural FIXMEs; land any facade changes they imply) AND drive the active suite to **full green** (all 38 failures resolved). The arc's Stages 2–4 assume the facade is settled — W0 makes that a verified fact rather than an assumption.

**Scope correction (2026-06-09, user-driven).** The Phase-1 scope was built from S76 close-notes prose, not a test run. A `cargo nextest run --no-fail-fast` showed **38 failed / 1094 passed / 8 skipped** — the draft covered ~13. Two large clusters were entirely unscoped (R1 primitive-type-resolution, R2 multi-file module/entry-point). User direction: (1) survey outstanding *architectural* FIXMEs too, since moving forward assumes the facade is sound; (2) **resolve all architectural issues** (do not defer R9/R10) in case they resolve to facade changes.

## Strategic framing — where this sits

S76 closed the **facade-retirement arc** (8 surfaces settled; source = canonical; no public-surface drift; first compile-clean workspace since S69; full e2e suite *enabled*). The language is feature-complete through Ring 4 and the architecture is now legible. What remains is **quality consolidation toward a releasable compiler**, sequenced as a four-stage arc (user-confirmed 2026-06-08):

1. **Stage 1 — Get to green (THIS SPRINT, S77).** Correctness floor: the enabled e2e suite must pass with no failing-not-ignored carries. Everything downstream rests on this — you cannot audit, optimise, or document behaviour that is still broken or still changing under defect fixes.
2. **Stage 2 — Component FIXME drawdown.** Status-hygiene triage (162 nominal opens, mostly stale/absorbed) → accurate per-component inventory; then action genuine gaps (platform-interface completion 0287/0289/0235/0238, stdlib runner 0273, legacy harvest 0116–0149, per-crate residuals).
3. **Stage 3 — Audit & optimise.** Perf benchmark infrastructure + the never-measured "within 2× of prototype" gate; the concurrency audit deferred since S62; per-crate internal-quality walks.
4. **Stage 4 — Documentation consolidation + user-facing.** Archive `design/` process cruft; **W-Retire** int doc-reorg (0298/0297 — the formal close of the facade arc, which is *documentation*); Phase 6 user-facing (`user/` docs, demos, examples, exemplar showcase). Docs go last so they describe the settled, green, measured system.

The order is strictly dependency-driven. The one cheap, tempting pull-forward — W-Retire's doc capstone — is **deliberately held to Stage 4**: pulling it in early is exactly the "document before settled" anti-pattern this arc exists to avoid.

## Scope

Two coupled workstreams: **W0 settles the architecture** (so the arc's facade-sound premise is verified, not assumed); **W1–W8 drive the suite to green**. Each green item lands a fix **or** a tracked-defect FIXME + failing-not-ignored repro per `feedback_repros_join_suite`. Exit criterion: `cargo nextest run` green across the active suite; the architectural-FIXME ledger is accurate (stale closed, live resolved); any facade change W0 surfaces is user-reviewed before commit.

### Root-cause map (from `cargo nextest run --no-fail-fast`, 2026-06-09 — 38 failed / 1094 passed / 8 skipped)

Phase-3 `/qa` triage refines this (code-defect vs fixture-defect vs gated; collapses to true roots; assigns owners). 38 tests ≈ ~8–10 roots:

| Root | Description | Failing tests (count) | Provisional owner |
|---|---|---|---|
| **R1** | Primitive type `:Int` won't resolve "from module ``" (type-annotation resolution, REPL + batch) | `imported_fn_as_higher_order_arg_in_repl_mode`, `impl_form_display_result…`, `every_example_runs` (~10 examples) (~3 test fns) | /dev typecheck (recon) |
| **R2** | Multi-file project entry-point / module resolution ("entry module has no `main`", "helper not found") | ~9 `spec_08_modules::*` + `cache_multi_module_transitive_imports` (~10) | /dev int + /qa (code vs fixture TBD) |
| **R3** | Macro cross-mode availability (clause-not-in-memory across REPL≟run) | `process_form_dispatch_macro_after_import`, `mode_equiv_macro_user_defined`, `persist_bug_macro_usage_in_defn` (3) | /dev int |
| **R4** | Trait-method-as-value + mappable dispatch | `trait_method_short_name…eq_string`/`…show_int`, `stdlib_eq_string_mappable_path`, `stdlib_num_float_mappable_path` (4) | /dev typecheck + backend |
| **R5** | Trace cluster | 6 `trace::*` | /dev intrinsics + backend |
| **R6** | Exemplar runtime overflow | 5 `regression::*` | /dev backend/runtime |
| **R7** | REPL introspection display format | `bare_primitive_add_i64…`, `data_constructor_product_no_dot_notation_display` (2) | /dev int |
| **R8** | REPL unclosed-paren parse error (FIXME 0142) | `parse_error_unclosed_paren_neg` (1) | /dev int |
| **R9** | Platform-interface error messages (0287/0289) — **architectural; resolve in W0, not defer** | 2 `platform_errors::*` | /dev platform/backend + /arch |
| **R10** | SharedState field count — **architectural; gated on 0176/0179, resolve in W0** | `facade_pif_rows::shared_state_field_count` (1) | /arch + /dev int |

### W0 — Architectural soundness pass (/arch + /design)

Survey **all 21 outstanding architectural FIXMEs** (12 /arch, 7 /design, 2 mis-targeted /runtime — enumerated 2026-06-09) and assess whether any of the failure roots above (esp. R1/R2/R9/R10) resolve to facade changes. For each architectural FIXME: **(a)** close-with-status-hygiene if stale/already-delivered (likely: 0114/0161/0210/0212/0241/0157/0106); **(b)** if live and pure-impl, hand to the green workstream; **(c)** if live and facade-touching (0176→int/BC §6; 0244→backend+primitives/D0048; 0266+0297→intrinsics/primitives+tracing; 0298+0214+0281→int; 0252+0253→backend design-doc; 0189→primitives; 0239; 0220), author the facade resolution and **return it for user review before commit** ([[feedback_explicit_decision_review]]). Re-target the 2 /runtime FIXMEs (crate retired by D43). **Per user direction (2026-06-09): R9 + R10 are resolved here, not deferred — they may resolve to facade changes.** Output: the "facade is sound" assumption becomes a verified fact + an accurate architectural-FIXME ledger.

### W1 — Trace/accessor defect cluster (R5)

The trace family was relocated to intrinsics in S76 (W1.5) and the backend accessor call-resolution landed (0292 backend half DONE + verified). Remaining defects, all with failing-not-ignored repros in `tests/trace.rs`:

- **0292 Defect A / 0285 (/int)** — `trace_nanos_accessor_resolves_in_repl`. REPL forward-reference under prelude-as-cwd-project: a program defining `work` before `id` errors `undefined variable: id` when the prelude loads as a cwd project (no `CRANELISP_LIB`). Real REPL module-resolution behaviour (and/or a test def-order fix). Owner `/int`.
- **0292 Defect B / 0285 / 0276 (/dev intrinsics — reframed by Phase 2)** — `trace_linked_accessor_consumption_parks_defect`. **Phase-2 /arch corrected the FIXME framing**: NOT a `--link`-specific relocation defect, NOT 0275-family. It is a **mode-independent RC double-consume / use-after-free** in the trace field-accessor consume path — the accessor is routed through `compile_consuming_arg_list` (caller consumes) AND each accessor body calls `consume_trace_call` (body consumes), double-freeing the Trace tree. Reproduced first-hand crashing non-deterministically in BOTH `--run`/REPL and `--link` (the FIXME's "JIT runs clean" claim was false — the printed value just precedes the heap fault); the match-based consume path is correct. **Owner: `/dev` (intrinsics); bounded, likely a quick win — not a rabbit hole.** Action: reconcile the caller-consumes vs body-consumes contract (mirror the match path); tighten the repro to assert the `--run`/REPL crash too so it stops masking the mode-independence. Re-point FIXMEs 0292/0285/0276 owner → /dev intrinsics.
- **0283 (/dev intrinsics)** — `trace_nested_lexical_raises_runtime_error`. Lexical `(trace (trace e))` does not raise per §4.12.5: no wrapper has fired before the inner `swap_got`, so the `TRACE_BODY_RUNNING` guard misses it. Needs a per-form sequence marker / swap-group count.
- **0284 (/dev backend)** — `trace_polymorphic_adt_result_renders` + `trace_adt_value_render_overflows_defect` (+ possibly `trace_trait_heavy_prelude_overflows_defect`). Tracing any fn returning a user ADT stack-overflows the production `DisplayDescriptor` baker/walk (the S76 W1.5 NOTE-1 gap was a crash, not an unverified path; in-crate unit tests passed only because they hand-built blobs). Triage with a CLIF/blob dump; verify the depth-16 TypeVar degrade actually fires; fix at bake-side or walk-side; add a production-baker round-trip unit test.

### W2 — Exemplar-solver runtime overflow (0296, /qa → /dev backend/runtime)

5 tests (`d6_exemplar_solve_all_dots`, `d6_exemplar_propagate_only`, `d6_exemplar_propagate_single_pass`, `d6_exemplar_solve_minimal_puzzle_no_io`, `wave6_exemplar_solver_full_run`) overflow the **main thread at runtime** — distinct from the now-resolved cyclic-subst root (0279/0295). Reduce to the minimal recursive shape that overflows, re-point the failing tests at that root, fix at the right layer. **Phase-2 /arch RETIRED the feared /spec TCO risk**: verified first-hand that TCO IS firing (self-tail recursion to 1M, exit 0, across all three §12.5 tail-position shapes incl. the `let`+`match` shape of `propagate-pass-helper`); the overflow reproduces at **depth 81** in a single propagate pass (no fixpoint, no backtracking), which cannot overflow if TCO fires — so the cost is **per-frame** (nested-ADT structural depth / RC drop-glue / Grid ADT-copy frame size), NOT unbounded recursion. **This is a pure backend/runtime codegen fix, NOT a language decision. Owner: `/dev` (backend/runtime). FIXME 0141 + the 5 TCO `#[ignore]` cases stay deferred — they are not this root.**

### W3 — Phase-5 language gaps (named in the S76 Outcome)

**Phase-2 /arch sharpened these** — the broad suites are 43/43 GREEN (`s76_macro_availability` + `spec_07_traits`); the live gaps are narrower than the S76 Outcome wording implied:

- **§7.6 trait-method-as-value** — narrowed to **trait-method passed to a HOF** (`(apply2 inc-by 10 5)` → `codegen error: undefined variable: inc-by`), while a *primitive* passed identically works and *direct application* (`(let [op +] (op a b))`) works. §7.6 is a MUST: the dispatch-wrapper closure is emitted for direct application but NOT when the method escapes as a HOF argument. **Owner: /dev typecheck + backend.** No /spec change (MUST already exists). Possible non-breaking `ResolvedCall::TraitMethodValue` variant — a Phase-3 design call, not pre-authored (Principle 8).
- **macro-after-import** — narrowed to **cross-module macro clause-in-memory with REPL≢`--run` divergence**: FQ macro ref in `--run` (`(mac/twice 21)`) → `macro 'mac/twice' clause 0 is not in memory`, yet the REPL test passes; imported-macro use in REPL → same error, yet `--run` works. The compiled clause pointer is not reliably available at expansion across both modes. **Implementation/orchestration gap (the macro model is LOCKED), owner: /dev int** (Pass-1 cross-module clause-ptr availability + REPL/`--run` parity). No /arch or /spec decision.

(W3 needs `/qa` to author failing-not-ignored repros at these *narrow* shapes before Phase-3 decomposition — the broad suites mask them.)

### W4 — FIXME status-hygiene triage (non-architectural; feeds Stage 2)

162 FIXMEs are nominally `open`; many are stale (absorbed by S64–S76 waves, never status-flipped) or the 34 harvest tests. (W0 owns the *architectural* subset.) Walk the rest, flip stale/absorbed ones (targeted skill resolves per the FIXME protocol — `/sprint` does not delete), produce an accurate per-component inventory for Stage 2. Bookkeeping, parallel.

### W5–W8 — the remaining green roots

- **W5 (R1)** — primitive type `:Int` resolution "from module ``"; the single biggest cluster (~3 test fns incl. ~10 examples). `/qa` narrows + recon owner (likely /dev typecheck).
- **W6 (R2)** — multi-file module/entry-point ("entry module has no `main`", "helper not found"). `/qa` classifies code-defect vs harness-fixture first (the `.tmp/main/user.cl` layout is suspect); then /dev int or /qa fixes.
- **W7 (R3 + R4)** — macro cross-mode availability + trait-method-as-value/mappable (supersedes the old W3; now full clusters, not partials).
- **W8 (R7 + R8)** — REPL introspection display format + unclosed-paren parse error (0142).

## Explicitly deferred (NOT S77)

- **W-Retire doc-reorg** (the *documentation* half of 0298 + intrinsics-facade trace cascade 0297) → **Stage 4**. NOTE: the int-facade *reframe* in 0298 is already RATIFIED (architectural decision settled); only the doc-reorg defers. W0 confirms 0298/0297 carry no un-landed architectural/facade change.
- **stdlib in-language test runner** (0273), **legacy harvest** (0116–0149) → **Stage 2** (coverage, not correctness or architecture).
- **Perf baseline + concurrency audit (S62)** → **Stage 3**.
- **5 TCO `#[ignore]` cases** (`spec_12_runtime.rs`) — blocked on `/spec` FIXME 0141; stay ignored (W2 confirmed not the exemplar root).
- **2 `s68` sentinels** (0221/0191) — blocked on the backend `Code::Primitive` deletion. **W0 decides**: FIXME 0244 (revert D0048 A2 / drop `Code::Primitive`) is architectural — if W0 resolves it, the sentinels un-ignore and join green; else they stay ignored with the disposition W0 sets.
- **1 perf-budget `#[ignore]`** (`build_confidence.rs`) — subprocess overhead, not a correctness gate.

*(R9 platform-interface + R10 SharedState are NO LONGER deferred — resolved in W0 per user direction, since they may resolve to facade changes.)*
- Decision 30 module-system redesign; long-session memory; FQTypeName residuals — out of consolidation-arc scope.

## FIXME debt

| FIXME | Target | Status | Disposition this sprint |
|---|---|---|---|
| 0292 | /dev intrinsics (re-pointed P2; was /int) | open | W1 — backend half DONE; **Defect B = RC double-consume (intrinsics)**; Defect A (REPL fwd-ref) = /int. |
| 0285 | /dev intrinsics (re-pointed P2; was /int) | open | W1 — closes with 0292 when both tests pass. |
| 0276 | /dev intrinsics (re-pointed P2; was /qa) | open | W1 — triage history; durable repros in `tests/trace.rs`. Closes with 0285/0292. |
| 0283 | /dev (intrinsics) | open | W1 — lexical nested-trace guard. |
| 0284 | /dev (backend) | open | W1 — DisplayDescriptor render overflow. |
| 0296 | /qa → /dev (backend/runtime) | open | W2 — exemplar runtime overflow; per-frame cost, **NOT TCO/spec** (P2-retired). |
| §7.6 trait-as-value | /dev typecheck + backend (P2) | (qa repro owed) | W3 — narrow shape: trait-method-as-HOF-arg. |
| macro-after-import | /dev int (P2) | (qa repro owed) | W3 — narrow shape: cross-module clause-in-memory, REPL≢`--run`. |
| (162 nominal opens) | all | mixed | W4 — status-hygiene triage; produce Stage-2 inventory. |

## Architecture review (Phase 2)

*Authored by `/arch`, 2026-06-09. All claims verified against source + first-hand reproduction with a freshly built `target/debug/cranelisp` (per the S76 retro's "FIXMEs are wrong in ways only a source walk catches" caution). No code/type/design edits required — Q4 surfaced no required cross-crate type. **Overall verdict: SOUND WITH NAMED REVISIONS** (both folded into the Scope above).*

**Q1 — Defect B (`--link` trace-consume crash).** **NOT a `--link` defect, NOT relocation, NOT 0275-family — the FIXME framing is materially wrong.** Reproduced crashing non-deterministically in BOTH `--run`/REPL and `--link` (exit 137/133/163/210/… and 165/76/160/100/213); the "JIT runs clean" claim was false (printed value precedes the heap fault). Match-based consume is clean exit 0; trace-bound-but-unconsumed is clean. Root: the accessor is routed through `compile_consuming_arg_list` (`apply.rs:178-181`, caller consumes) AND each accessor body calls `consume_trace_call` (`intrinsics/src/trace.rs:672-678`,:1117-1137, body consumes) → **double-consume / use-after-free of the Trace tree**. **Owner /dev intrinsics; bounded, likely a quick win.** Re-point 0292/0285/0276; tighten the repro to assert the cross-mode crash.

**Q2 — 0296 exemplar overflow.** **Pure codegen/runtime fix; does NOT route to /spec; the feared TCO blocker does not exist.** Verified TCO fires (self-tail recursion to 1M, exit 0, across all three §12.5 tail-position shapes incl. `let`+`match` = the `propagate-pass-helper` shape). The overflow reproduces at **depth 81** in a single propagate pass (no fixpoint, no backtracking) — impossible under working TCO, so the cost is **per-frame** (nested-ADT structural depth / RC drop-glue / Grid ADT-copy frame size). Independently confirmed: a 200k-deep linked-list build+traverse+drop overflows while TCO loops of the same depth do not. **Owner /dev backend/runtime.** FIXME 0141 + the 5 TCO `#[ignore]`s stay deferred — not this root.

**Q3 — Phase-5 gaps.** Both confirmed live, both decomposable in Phase 3, neither needs /spec or /arch decision — but the broad suites are 43/43 green; the real gaps are narrower. **(a) §7.6**: narrowed to trait-method-as-HOF-argument (`(apply2 inc-by 10 5)` → `undefined variable: inc-by`; a primitive passed identically works; direct application works) — the dispatch-wrapper closure isn't emitted when the method escapes as a HOF arg. §7.6 MUST already exists. Owner /dev typecheck + backend. **(b) macro-after-import**: narrowed to cross-module macro clause-in-memory with REPL≢`--run` divergence (`macro 'mac/twice' clause 0 is not in memory`) — model is LOCKED, this is orchestration. Owner /dev int. `/qa` authors narrow repros first.

**Q4 — Interim-risk + public-API.** No NEW cross-crate interface required by W1–W3; nothing authored in `cranelisp-types`. All fixes internal (intrinsics RC convention; backend/runtime codegen; intrinsics nested-trace guard; backend descriptor baker). One **possible** non-breaking addition flagged-not-built: a `ResolvedCall::TraitMethodValue` variant for §7.6 (`ResolvedCall` is `#[non_exhaustive]`) — deferred to the Phase-3 typecheck+backend design per Principle 8; if confirmed, /arch authors it then (variant + baseline regen + interfaces/BC cascade in one change-set). No interim-structure risk: every fix moves toward the settled state.

**Q5 — Scope coherence.** Sound, dependency-clean; four-stage sequencing and W-Retire-to-Stage-4 hold are correct; Stage-1 green is self-contained (no /spec dependency). W4 is correctly bookkeeping (`/sprint` does not delete; targeted skill resolves). Two required revisions, both folded above: (1) re-frame Defect B as the intrinsics RC bug; (2) sharpen W3 to the narrow shapes with /qa repros first. No item moves out; no missing prerequisite.

## Skill plans (Phase 3)

### W0 — Architectural soundness + FIXME hygiene — **COMPLETE (2026-06-09)**

**Facade verdict: SOUND.** `/arch` surveyed all 21 architectural FIXMEs against source. **Zero facade changes required** — every "facade-touching" candidate resolved to already-cascaded design (never status-flipped) or pure-impl/doc work moving source toward the settled facade. The arc's "facade is sound" premise is now a verified fact. R9/R10 confirmed pure-impl (no facade impact).

**Full FIXME survey (all 162 open, 3 parallel passes + arch):** classified every open FIXME against the 38-failure ground truth.
- **70 stale/obsolete CLOSED** (staged `git rm`, uncommitted): the S60 cache-SIGSEGV + drop-glue reduction cluster (fixed, tests pass under active names), the entire d45 series (retired `/run-tests`), and ~30 landed-but-never-flipped cascade/defect items. Plus /arch's 5 architectural closes (0114/0157/0161/0210/0244).
- **3 HELD** (real residual deliverables → Stage 2): 0014 (backend doc-fix), 0025 (neg-coverage to harvest into active suite), 0106 (platform doc-archival).
- **34 legacy-harvest** → Stage 2 (test porting, not defects).
- **~40 deferred-live** → Stage 2/3/spec-decision (recorded with owner + target).
- Mis-targeted /runtime FIXMEs (0128/0129) → re-target to /dev intrinsics + harvest.

### W-platform & W-sharedstate — pulled into S77 (user decision 2026-06-09)

- **R9 (platform-interface)** — user: "bring this forward… we want the solution working end to end." S77 delivers the FULL platform-interface end-to-end (own wave): the /qa synthetic-DLL fixture (clears the 2 `platform_errors` tests — these need `with_synthetic_dll`, NOT the heavy feature; the `PlatformError` variants already exist+wired) **AND** the DLL round-trip feature (0287 backend schema-gen + 0233/0288 int load-path + 0289 /qa e2e + 0293 residue). No facade change (platform-interface.md ratified S76).
- **R10 (SharedState field count)** — user: "do it this sprint, in its own wave." The 0176/0179 cluster-atomic PIF field moves (`module_sexps`/`suspend_states`/`current_module`/`repl_check_state` off SharedState). Internal `src/` work, no facade impact; clears `facade_pif_rows::shared_state_field_count`.

### Phase-5 Stage 1 (QA-first) — owed before /dev waves

`/qa` files tracking FIXMEs + confirms failing-not-ignored repros for the four un-FIXME'd green roots (RT5 macro, RT6 trait-value, RT10 display, RT1/RT2 fixtures), tightens the Defect-B repro to assert the cross-mode crash, and refreshes the ledger with the 38 + the W0 closes. RT11 needs `/spec`+`/repl` to formalize the EOF-error principle (user-ruled: complete forms submit → incomplete-at-EOF must error) before /int fixes 0142.

## Waves (Phase 4)

Stage-1 QA-first, then per-crate D/D/R, parallel across owners. Each `/dev` wave followed by narrow `/review`.

| Wave | Root(s) | Owner(s) | Tests | Notes |
|---|---|---|---|---|
| **W-Fix** | RT1 + RT2 | /qa + /examples | ~5 | Cheapest, no /dev dep — bare `:Int` imports + stale trait syntax in examples/fixtures. Land first. |
| **W-Trace** | RT7 + RT8 | /dev intrinsics ‖ /dev backend ‖ /int | 6 | 3 parallel owners: intrinsics (0292-B RC double-consume + 0283 nested-lexical guard), backend (0284 ADT-render overflow), int (0292-A REPL fwd-ref + 0285 accessor codegen). |
| **W-Exemplar** | RT9 | /dev backend/runtime | 5 | 0296 per-frame overflow (not TCO). Reduce → fix at codegen/runtime layer. |
| **W-Module** | RT3 + RT4 | /int | ~12 | 0121 `--run`/cache `(mod …)` discovery + cross-module resolution. One owner; serialize. |
| **W-MacroTrait** | RT5 ‖ RT6 | /int ‖ /dev typecheck+backend | 7 | macro cross-mode clause-in-memory (/int) ‖ trait-method-as-HOF-value (typecheck+backend; possible `ResolvedCall::TraitMethodValue` — /arch authors if Phase-5 confirms). |
| **W-Repl** | RT10 + RT11 | /int (+ /spec,/repl for RT11) | 2 | bare-primitive docstring + EOF-unclosed-paren error (0142, after the principle is formalized). |
| **W-Platform** (own wave) | R9 | /qa + /dev platform+backend+int | 2 + feature | synthetic-DLL fixture (clears 2 `platform_errors`) + full DLL round-trip end-to-end (0287/0233/0288/0289/0293). |
| **W-SharedState** (own wave) | R10 | /dev int | 1 | 0176/0179 cluster-atomic PIF field moves. Sequenced late (touches the pipeline). |

**Wave gate** (each → next): scan `design/arch/fixmes/` for `target: /skill-in-wave` + `status: open`; resolve or explicitly defer. **No concurrent cargo** — only the source-owning agent in a wave runs tests.

## Notes

- 2026-06-08: Phase 1 scope drafted. Strategy confirmed by user: four-stage consolidation arc (green → debt → audit/optimise → docs); S77 = Stage 1 (get to green); W-Retire held to Stage 4. Cyclic-subst root (0279/0295) confirmed resolved + deleted in S76 W4c. Defect cluster verified live against `design/arch/fixmes/`.
- 2026-06-09: Phase 2 /arch review complete — SOUND WITH NAMED REVISIONS (2 corrections folded: Defect B reframed as mode-independent intrinsics RC double-consume / quick-win; 0296 confirmed NOT TCO/spec, pure backend/runtime). No new cross-crate type required.
- 2026-06-09: **SCOPE CORRECTION (user-driven).** User challenged "seems small." Full `cargo nextest run --no-fail-fast` = **38 failed / 1094 passed / 8 skipped** — the prose-built Phase-1 scope covered ~13. Two large unscoped clusters: R1 primitive-type-resolution, R2 multi-file module/entry-point. Root-cause map (R1–R10) added. **User direction: (1) survey all outstanding architectural FIXMEs — moving forward assumes the facade is sound; (2) resolve all architectural issues (do NOT defer R9/R10) in case they resolve to facade changes.** Reframed to W0 (architectural soundness) + W1–W8 (green). 21 architectural FIXMEs enumerated (12 /arch, 7 /design, 2 mis-targeted /runtime). Advanced to PHASE 3 with two parallel investigation passes: /arch survey-all-architectural-FIXMEs + facade-impact-of-failure-roots; /qa triage-all-38 (root + code/fixture/gated + owner). Facade changes return for user review before commit.

- 2026-06-09: **FULL FIXME SURVEY + W0 COMPLETE.** User: "have we checked all the open fixmes? there are 100 or more." Surveyed all 162 against the 38-failure ground truth (3 parallel read-only passes + the arch survey). Facade verdict SOUND (no facade changes). Careful verify-then-close pass (user: "check each one, close if reasonably confident"): **70 closed** (staged), **3 held** (0014/0025/0106 — residual deliverables → Stage 2), 34 harvest + ~40 deferred-live recorded. User decisions: **R9 platform-interface pulled into S77 end-to-end (own wave)**; **R10 SharedState pulled in (own wave)**; RT11 EOF-unclosed ruled a code defect (complete forms submit → incomplete must error). Wave plan (Phase 4) drafted: W-Fix/W-Trace/W-Exemplar/W-Module/W-MacroTrait/W-Repl/W-Platform/W-SharedState. **Uncommitted W0 changeset**: root CLAUDE.md (ring-axis, 0114), 70 FIXME deletions, `tests/plan/ledger.md` (38-triage), SPRINT.md. Awaiting user go to PHASE 5 + commit decision.

- 2026-06-09: **Phase 5 underway (drive-sequentially, gate-report cadence — user-approved).** W0 committed `ae4ede9`; QA-first + W-Fix committed `5cdbee2` (fixtures/examples green; FIXMEs 0299–0302 filed; Defect-B mode-independence proven). **W-Module (RT3/RT4, FIXME 0121) DONE** — /dev (int) fixed two coupled real defects (entry-file-vs-dir resolution in `main.rs`; `(mod X)` short-name alias in `worker.rs`); the /qa-flagged "suspect harness layout" was a real resolver bug, not a fixture. 11 tests pass; 7 unit tests added; 0121 closed. /review PASS-WITH-FINDINGS (filed 0303 /arch Principle-7 dedup, 0304 /qa stale-comment sweep — both non-blocking). Green: ~36 → ~25 failing.

- 2026-06-09: **W-Trace (RT7/RT8) DONE — 14/14 trace tests pass.** Resolved as 2 real fixes + 3 corrected tests. **0283** (lexical nested-trace guard) fixed in intrinsics (`SWAPPED_GOT_BASES` thread-local). **0284** (ADT-render overflow) fixed in backend at two real layers (identity self-map elision in `schema.rs`; `emit_rc_dec_guarded(Mixed)` in `trace_codegen.rs`). **0292/0285/0276** accessor cluster: real bugs were S76-fixed; the 3 stragglers were TEST-DESIGN defects — `/sprint` verified first-hand (deterministic-return → exit 0 8/8; the "crash" was `main` returning a wall-clock `nanos` Int used as exit code; the REPL test had an invalid def-order, and REPL no-forward-ref is spec-intended §5.13.2). `/qa` reframed the 3 tests as positive guards. **Investigate-first paid off repeatedly**: the 0292 defect was mis-framed 3× (RC double-consume / backend spurious-inc / —) before first-hand repro proved no corruption. /review PASS (both RC/codegen fixes verified sound). FIXMEs closed: 0283, 0284, 0292, 0285, 0276. Green: ~25 → ~19 failing.

- 2026-06-09: **W-Exemplar (RT9, FIXME 0296/0031) DONE — real use-after-free fixed.** /arch's "per-frame structural-depth cost" hypothesis was WRONG (5th overturned framing). Root: `vec-set`'s COPY path (`vec_set_copy` in `cranelisp-intrinsics/src/vec_runtime.rs`) inc'd retained elements but NOT the new value → cell freed while the new grid still referenced it → garbage read → corrupt arg → `pow2` recursing ~260k deep → main-thread stack overflow. Fix: inc the new value (mirror the COW mutate path; NeverHeap → no-op). Root fix, not a stack bump (per `feedback_no_premature_perf`). **Solver now produces correct solutions.** /review PASS no-findings (inc provably symmetric → no leak). 5 tests pass; unit test added; FIXMEs 0296+0031 closed; 0032 (/port re-enable) now actionable. Green: ~19 → ~14 failing.

- 2026-06-09: **W-MacroTrait RT5 (FIXME 0299) DONE — 2 real /int defects fixed.** (1) `register_macro_in_module` discarded the macro sexp → `regenerate_backing_file` silently dropped every defmacro on cache-restart (`undefined variable: twice`); fixed by recording the sexp into Introspection + emitting defmacros-before-defns in regen. (2) cache-restore Linker lacked a `dlsym(RTLD_DEFAULT)` fallback for binary-exported primitives (`unresolved symbol: sconcat`); fixed mirroring the JIT. + cross-module cache macro-recompile step. /review PASS (dlsym tightly gated + sound; weakened assert justified; round-trip-safe). 2 tests pass; the 3rd (`process_form_dispatch_macro_after_import`) is a /qa fixture spec-violation → FIXME 0305. Green: ~14 → ~12.
- 2026-06-09: **W-MacroTrait RT6 (FIXME 0300) — BLOCKED on an /arch Decision (needs user review).** Investigation found both symptoms (escaping-wrapper-not-emitted + wrong-impl-dispatch) share ONE root: `Expr::Var` has no `resolved_call` field, so a trait method in value position gets no resolution → backend fails (`undefined variable: show`) or falls back to a hard-coded Int primitive (String `=`→false, Float `+`→inf.0). Decision 43 forbids reintroducing trait-keyed dispatch in backend. Fix = 3-step cascade: **(1) /arch add `Expr::Var.resolved_call: Option<Box<ResolvedCall>>` to `cranelisp-types`** (public-API change — USER REVIEW), (2) /typecheck deferred value-position resolution pass, (3) /dev backend `compile_var` wrapper emission. 4 tests stay failing-not-ignored; 0300 re-targeted /arch with the contract. Backend untouched.

## Outcome (Phase 7)

{Pending.}
