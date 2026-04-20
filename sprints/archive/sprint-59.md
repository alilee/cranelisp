# Sprint 59: Stabilisation + Dual-Path Persistence Collapse

**Status**: COMPLETE
**Ring**: 4 (Effects — stabilisation)
**Goal**: Collapse the dual-path persistence structural debt surfaced at Sprint 58 close into a single `register_module` recursion path, and clear the Sprint 58-carried demo-surfaced defects (3, 4, 5, 6, 7). After this sprint, the six carried failing tests at Sprint 58 close are green or explicitly re-triaged, and the Ring 4 acceptance-criterion gaps on cache/link/exemplar narrow to the measurement-and-polish items that are coherent with a post-convergence hardening sprint.

## Scope

Phase 5 of pipeline-v4 convergence closed the data-model. Sprint 58 §Findings identified **dual-path persistence** — divergent code paths between in-process REPL state and `.cranelisp-cache/` artifacts, leading to heisenbug-shaped cache/link failures — as "the next structural debt" and "warranted before Ring 4 release". Three of Sprint 58's six carried failing tests (`cache_repl_loads_on_startup`, `persist_import_survives_restart`, and a third flake-adjacent failure) all trace to this root cause. Sprint 58 /review I-3 also commissioned a stub design doc to be opened in Sprint 59.

Five workstreams:

- **Workstream A — Dual-path persistence collapse (Option B)** (primary, `/int`): single `register_module` recursion path for both cache-hit and fresh-compile module registration. Closes 2–3 `tests/sprint23.rs` failures + the `v4_cache_hit_dependency` cross-module restore residual. Requires a new design doc (`design/int/dual-path-persistence-collapse.md`) authored in Phase 3 before implementation; `/arch` reviews for Decision 37 alignment. Owners: `/int` (lead) + `/backend` (cache-read surface review) + `/arch` (design review).

- **Workstream B — Demo-surfaced defect cluster + IO-trampoline carry** (primary, `/backend` + `/int` + `/port`): clear the four demo-surfaced defects filed at Sprint 58 Wave 6 with failing-test durable records per the defect-handoff principle, plus the `sketch_run_tests` IO-trampoline carry. After this workstream closes, the "all Sprint 58 carries cleared" milestone is met and the baseline drops to 0 carried failures.
  - **Defect 3** (`/int`) — `wave6_demo_repros::display_defn_with_docstring_uses_dash_separator`: format-string fix in `src/session_v4.rs::append_docstring_comment` per `repl/spec.md §1.1` separator spec. Small.
  - **Defects 4 + 5** (`/backend`) — `wave6_demo_repros::run_tests_batched_invocation_no_crash`: exit codes 139 (html) + 133 (form) from batched `/run-tests` crash; codegen-incomplete path + RC/last-use issue in the exemplar html/form modules. Requires repro reduction (per `feedback_qa_reproduction.md`) before fix.
  - **Defect 6** (`/backend`) — `wave6_demo_repros::exemplar_solver_does_not_stack_overflow_on_small_puzzle`: pre-existing Sprint 19 stack overflow in the solver. Likely TCO or codegen depth issue; needs repro + diagnosis.
  - **Defect 7** (`/port`, unblocked by Defect 6): once `/backend` closes Defect 6, `/port` re-enables 3 puzzle tests in `exemplar/solver.cl`. Small.
  - **Defect 8** (`/int` primary; `/backend` confirms diagnosis) — `sketch_port::sketch_run_tests_pass_fn_called`: **Phase 3a repro reduction falsified Sprint 58's "IO-trampoline" hypothesis**. Actual root cause: `program_uses_test_forms` at `src/session_v4.rs:1778-1787` scans only `TopLevel::Expr`, ignoring `TopLevel::Defn` bodies — a `defn` whose body lexically references `run-test` / `discover-tests` slips through and the extern isn't added to `codegen_extra_symbols`, so JIT `finalize_definitions` fails with `can't resolve symbol run-test`. Localised fix in `src/session_v4.rs`. /arch Condition 2 does NOT trigger (invariants guard the trampoline path, which is never reached). Latent parallel bug in `program_needs_trace` (same file ~:1824) — same shape; fold into this fix. Repro notes at `design/backend/defect-8-repro-notes.md`.

- **Workstream C — `/backend` residuals** (primary, `/backend`): two /backend-local fixes:
  - **C-i** — `crates/cranelisp-runtime/src/io.rs:28` string-literal lifetime through `print` — Sprint 57 Wave 3 carry, Sprint 58 deferred under one-deferral-permitted policy (Condition 6). This is the **second-deferral threshold** per the `/sprint` deferral escalation policy — it ships this sprint unless the user explicitly approves a third deferral. Named regression-test symptoms in `tests/plan/ring4.md §G.14`.
  - **C-ii** — `crates/cranelisp-backend/src/cache/linker.rs:325` `ensure_got_slot` local-symbol lookup gap (Classification D per `design/backend/cache-repl-loads-triage.md`). Added Wave 1 after /int Workstream A revealed that `cache_repl_loads_on_startup` was **misattributed** to dual-path persistence — actual root cause is linker GOT slot-allocator not searching `local_symbols` when resolving `.L*` labels (Cranelift-emitted local data symbols). Sprint 58 Decision 23 regression-guard window. Effort: S (~2 hrs). Flips `tests/sprint23.rs::cache_repl_loads_on_startup` green + extends the Decision-23 guard to cover `.L*` locals.

- **Workstream D — Prior-ring coverage gaps (`/qa`)**: module-boundary negative tests flagged by the Phase 1 audit.
  - `spec §8.3.7` super-in-top-level-module MUST-error neg test (`/qa` integration test in `tests/ring2.rs`).
  - `spec §8.3.9` import-placement MUSTs (import inside `let` rejection; imports available before definitions) — 2 neg tests.
  - `spec §8.3.1` import-of-non-existent-name neg test.
  - Promote `[Tested]` → `[Tested+Neg]` on the affected §8.3.x headings once tests pass.

- **Workstream E — Sprint-opening cleanups** (bundled, various owners): clear the Sprint 58 close-time carries explicitly named for Sprint 59 opening.
  - `/stdlib` — verify the 3 missing files from Sprint 58 I-2 audit (candidates: `derive.cl`, `defs.cl`, `default.cl`); lock in the count (35 vs claimed 32). Small.
  - `/arch` — Decision 25 + Decision 31 Scenario 2 footnote tightening (cosmetic). Small.
  - `/arch` — regenerate `design/arch/sequence-diagram/v4-target.svg/.png` from updated `.mmd` (cosmetic). Small.
  - `/int` + `/sprint` — commission `design/int/dual-path-persistence-collapse.md` stub (the Phase 3 design doc for Workstream A — merges the "commission" from I-3 with the Phase 3 design-before-code requirement).
  - `/spec` — §8.11.5 platform directory list spec abstraction (Sprint 58 close-time named); small. Evaluate in Phase 1 whether this is in scope.

### Out of Scope (deferred with rationale)

- **Performance baseline / benchmark infrastructure** — Ring 4 acceptance-criterion `Performance within 2x of prototype` NOT MEASURED. Dedicated S60+ candidate: infrastructure workstream (criterion harness, prototype-parity benchmarks, CI reporting) — incoherent with stabilisation focus.
- **Long-session memory profiling** — adjacent to Decision 31 reclaim but properly belongs after dual-path stabilisation stabilises the cache-write surface.
- **Decision 30 module-system redesign** — parent↔child typecheck deadlock lift. Future research per Sprint 58 §Out of Scope.
- **Stdlib prelude monolith remediation** — stdlib-focused sprint; not a stabilisation item.
- **`FQTypeName` migration**, **BL range fix** — roadmap-deferred indefinitely.

### `/int` Burden Assessment

**HEAVY — but narrower than Sprint 58.** Workstream A (dual-path collapse) is the primary `/int` workstream; Workstream B Defect 3 is a small format fix. No Step-5c-scale mechanical sweeps. Sequencing:

1. Phase 3 Wave: `/int` authors the design doc; `/arch` reviews; `/qa` derives test cases (dual-path-specific failure modes, including the heisenbug parallel-run flake).
2. Implementation wave: `/int` lands the collapse behind cargo-check + targeted `tests/sprint23.rs` green gating, in parallel with `/backend` Workstreams B (Defects 4/5/6) + C (io.rs RC).
3. `/port` Defect 7 lands after `/backend` Defect 6 closes (cross-wave dependency).

If `/int` reports Workstream A burden risk during Phase 3 design or implementation, `/sprint` escalates to the user with concrete options (descope Workstream E items; split Workstream A across two sprints with a smaller increment this sprint). Does not auto-defer.

### Direct failure-fixing expectation

Sprint 58 closed at **1760 passed / 6 failed / 0 skipped**. Sprint 59 target clearance:

| Failure | Owner | Workstream | Expected clearance |
|---|---|---|---|
| `sprint23::cache_repl_loads_on_startup` | `/backend` (re-attributed Wave 1) | C-ii | Yes — linker GOT slot-allocator local-symbol fix |
| `sprint23::persist_import_survives_restart` | `/int` | A | Yes |
| `wave6_demo_repros::display_defn_with_docstring_uses_dash_separator` | `/int` | B (D3) | Yes |
| `wave6_demo_repros::run_tests_batched_invocation_no_crash` | `/backend` | B (D4/D5) | Target |
| `wave6_demo_repros::exemplar_solver_does_not_stack_overflow_on_small_puzzle` | `/backend` + `/port` | B (D6/D7) | Target |
| `sketch_port::sketch_run_tests_pass_fn_called` | `/int` (primary) + `/backend` (confirms) | B (D8) | Yes — localised fix per Phase 3a repro |

**Target**: **6 of 6 carried failures clear** ("all S58 carries cleared" milestone); baseline drops to **0 carried failures**. Plus 4 new passing neg tests from Workstream D.

## FIXME Debt

Phase 1 scan results summarised here (full inventory delivered by `/sprint` Phase 1 Explore subagent; 286 total FIXMEs across `.md` / `.rs` / `.cl`). In-scope for this sprint:

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `tests/sprint23.rs:1126` | `/int` | `cache_repl_loads_on_startup` — dual-path persistence | **Workstream A** |
| `tests/sprint23.rs:1307` | `/int` | `persist_import_survives_restart` — dual-path persistence | **Workstream A** |
| `tests/sketch_port.rs` (run_tests pass_fn) | `/int` + `/backend` | `sketch_run_tests_pass_fn_called` — IO-trampoline / `bind` over `(IO TestResult)` | **Workstream B (D8)** |
| `crates/cranelisp-runtime/src/io.rs:28` | `/backend` | String-literal lifetime through `print` RC residual | **Workstream C** (second-deferral threshold) |
| `design/int/` (new) | `/int` | `dual-path-persistence-collapse.md` stub (Sprint 58 /review I-3) | **Workstream E + A Phase 3 design** |
| `design/arch/CLAUDE.md` (Decision 25 + 31 Sc.2) | `/arch` | Footnote tightening | **Workstream E** (cosmetic) |
| `design/arch/sequence-diagram/v4-target.svg/.png` | `/arch` | Regen from `.mmd` | **Workstream E** (cosmetic) |
| `stdlib/` audit count drift | `/stdlib` | Sprint 58 I-2 — 32-vs-35 verification | **Workstream E** |
| `spec §8.3.7 / §8.3.9 / §8.3.1` neg coverage | `/qa` | Module-boundary negative tests | **Workstream D** |

Pre-existing FIXMEs not in scope (deferred with rationale) follow the pattern in Sprint 58 — design-doc forward pointers, stdlib-monolith, `/docs` survey items, `FQTypeName` migration, BL range fix — all explicitly carried to future stabilisation sprints.

## Architecture Review

**Reviewer**: `/arch`
**Verdict**: APPROVED WITH CONDITIONS

### Coherence

Sprint 59 is a coherent stabilisation increment: it takes the "next structural debt" named at Sprint 58 close (dual-path persistence) and couples it with the residual demo-surfaced defect clearance that Sprint 58 deferred under the defect-handoff principle. The increment is testable — the 6 carried failing tests + 4 new neg tests form a concrete acceptance surface, and the baseline contract ("drop to 0 carried failures") is falsifiable. Workstream sequencing is sound: Workstream A sits on a Phase 3 design doc before implementation (per the design-before-code rule); Workstreams B/C run in parallel on `/backend` without contending for the same surfaces; Workstream D is orthogonal negative-coverage work `/qa` can land in any wave; Workstream E is close-time cleanup. The only cross-wave dependency (Defect 7 on Defect 6) is correctly called out.

The `/int` burden assessment is honest — Workstream A is HEAVY but narrower than Sprint 58's Step 5c, and the auto-escalation path is explicit (no silent carry). Post-convergence "0 carried failures" is the right milestone framing for the first sprint after Phase 5 closed.

### Principle 8 (no interim architecture)

No workstream builds throwaway infrastructure. Workstream A converges ON the Decision-37 target shape (single `register_module` recursion) rather than scaffolding around the dual paths — the existing dual paths ARE the interim architecture, and this sprint removes them. Workstream B Defects 3/4/5/6/7 are bugfixes against the Phase-5 target data model, not temporary workarounds. Workstream C (io.rs:28 RC residual) fits Decision 29's extern-boundary contract without introducing new primitives. Workstream D adds tests against the committed spec. Workstream E is cosmetic cleanup of Phase 5 artefacts.

**One watch item**: Defect 8's "IO-trampoline interaction with `bind` over `(IO TestResult)`" has a re-scope clause ("if repro reveals a deeper redesign"). That is the correct posture — but if the repro lands on "the trampoline's RC contract needs to extend to continuation-produced ADT nodes whose fields are themselves IO trees," that is a Decision-24/-29 extension, not a local fix. The Phase 3 design artefact (if warranted) must be reviewed for Decision-24 scope before implementation.

### Design references

Per-skill design-ref completeness:

- **`/int`** — Workstream A refs (pipeline-v4.md §9, Decision 37, Sprint 58 §Findings) are complete and correct. **Addition**: Phase 3 design doc MUST cite Decision 31 Scenario 2 "Carry-forward invariant" (the upsert at `program.rs:2184-2232`) — the dual-path collapse touches the same upsert site, and breaking the carry-forward would regress JIT reclaim. Also cite Decision 25 (cache-hit LOADS the `.o`, does not re-codegen) as the normative post-5c shape the collapse must preserve.
- **`/backend`** — Refs listed (`ring2-rc.md §3.3` / Decision 24 extern audit) are correct. **Addition**: For Defect 8, add Decision 29 (`rc::dec_shallow_io` as the extern-boundary primitive) — if the repro points at continuation-produced IO-ADT nodes, Decision 29's "genuine Runtime primitive, not throwaway" framing applies.
- **`/qa`** — Refs OK; Phase 3 test-case derivation from the Workstream A design doc (including the 1755-vs-1754 heisenbug parallel-run repro named in Sprint 58 §Findings) is correctly called out.
- **`/frontend`, `/typecheck`, `/platform`** — "No implementation, review only" is the right posture given the scope.

### Interface gaps

No boundary-type extensions required. The `SymbolTable<C, L>` generics, the `Code` enum (Decision 35), `schema_version` (Decision 34), and structural decls (Decision 33) are all in place at Sprint 58 close. Workstream A operates on the `register_module` function body and the cache-hit branch inside it (per Decision 37's canonical flow); no new types cross the boundary. If Phase 3 design surfaces an interface need (e.g., a `CacheLoadError` variant richer than Sprint-58 shape), it must be filed as a FIXME(/arch) before landing, not edited in-situ.

### Response to /sprint questions

1. **Workstream A vs Decision 37**: Fully coherent. Decision 37 defines `register_module` as the SINGLE recursive flow with cache-hit decision + load as a branch INSIDE it (not a parallel `try_cache_hit_load`). Workstream A's "Option B" (single `register_module` recursion path for both cache-hit and fresh-compile) IS Decision 37 enacted at the REPL-persistence surface — where Sprint 58 Wave 2 deleted `try_cache_hit_load`, Sprint 59 deletes the REPL-side dual (`compile_dep_inline` vs `handle_*` paths named in Sprint 58 /review I-3). Option B needs one refinement before the Phase 3 design doc: it must state explicitly that "persistence dual-path collapse" and "cache-hit integration" are the SAME structural shape applied at different surfaces (scheduler-side vs session-side). If the Phase 3 design treats them as independent problems, the convergence will re-diverge. The design doc MUST open with a Decision-37 alignment section.

2. **Workstream C vs Decision 24**: **Local fix with Decision-24 context.** The io.rs:28 FIXME names the root cause as "string-literal heap alloc for the argument to Effect-thunk construction" where "the thunk's consume-on-call discipline is not propagated to the captured string." This is Decision 24 Scope Clause 2 (the extern-boundary consuming contract) applied to an intra-codegen site: the question is whether `print`'s extern shell or the codegen path that feeds it is the consumer. A localised `/backend` fix under `ring2-rc.md §3.3` is correct. Architectural review is NOT required for the fix itself; HOWEVER — if `/backend`'s investigation finds the bug lives on the codegen side of the capture-into-Effect boundary (not in the extern shell), that is a closure-capture-vs-consuming-convention interaction that should cite Decision 24 scope Clause 1 in the commit message for future-proofing. No design-doc update required unless that interaction generalises.

3. **Defect 8 co-ownership + Sprint 49 regression risk**: Co-ownership is CLEAN as specified. IO-trampoline sits structurally at the `/int` ↔ `/backend` boundary (per Decision 29: primitive owned by `/backend`, extern-boundary wiring owned by `/int`), and Sprint 59's framing correctly names both. Invariants the Phase 3 design doc (`design/int/io-trampoline-bind-over-io.md` or the co-authored equivalent) MUST call out: **(a)** the trampoline stays non-consuming of `io_ptr` (Decision 24, canonical illustration); continuation-produced intermediate nodes use `rc::dec_shallow_io` per Decision 29; the top-level tree is released by `consume_io_tree` after trampoline return. **(b)** `bind` over `(IO TestResult)` must preserve the carry-forward invariant (Decision 31) if the bind evaluation path touches a `ModuleEntry::Def.code` upsert — unlikely for test-fixture bind, but the test-capture platform's retention of fn pointers crosses the "callback platforms" prospective concern in Decision 31. **(c)** test-capture's `print` argument-consumption contract (named in the FIXME text at `io.rs:28`) must be specified explicitly if the fix routes to `/runtime`. **Sprint 49 regression surface**: the macro/prelude regression in Sprint 49 came from a prelude-load path that bypassed the macro expansion pipeline; dual-path collapse re-opens that surface ONLY IF the collapsed path re-introduces a branch where the REPL session startup loads the prelude via a different codepath than `register_module`. The Phase 3 design MUST include a sub-section "Prelude loading under the collapsed path" showing that prelude load enters via `register_module` for the "user" module (per the Sprint 58 Wave 5 `new_with_prelude` shape), with no REPL-special-case bypass. If that property cannot be stated without qualification, the design doc returns to `/arch` for review.

4. **I-2 stdlib audit drift**: Confirmed — no architectural implication. The 32-vs-35 count discrepancy is `/stdlib` verification hygiene; neither the audit method nor the audited property crosses a skill or crate boundary. `/stdlib` owns the reconciliation in Workstream E.

### Conditions

1. **`/int` (Phase 3, pre-implementation)** — `design/int/dual-path-persistence-collapse.md` MUST include: (a) an explicit Decision-37 alignment section stating that the persistence-dual and cache-hit-integration are the same structural shape at different surfaces; (b) a "Prelude loading under the collapsed path" sub-section showing prelude load enters through `register_module` with no REPL-special-case bypass (Sprint 49 regression surface); (c) a statement that the carry-forward invariant (Decision 31 Scenario 2, `program.rs:2184-2232`) is preserved at the collapsed upsert site. `/arch` reviews this design doc before implementation lands.

2. **`/int` + `/backend` (Phase 3, if Defect 8 warrants design)** — If Defect 8's repro reveals a fix surface beyond a local extern-wrapper adjustment, the co-authored design artefact MUST specify: (i) trampoline non-consuming contract preservation (Decision 24); (ii) continuation-produced-IO-node shallow dec via Decision 29; (iii) test-capture `print` argument-consumption contract. `/arch` reviews. If the repro reveals an IO-trampoline redesign beyond these invariants, `/sprint` re-scopes with user approval per the existing scope note.

3. **`/backend` (Workstream C, at commit)** — If Workstream C's investigation locates the bug on the codegen side of the capture-into-Effect boundary (rather than in `print`'s extern shell), the commit message cites Decision 24 Scope Clause 1 for future-proofing. No design-doc update required unless the interaction generalises beyond string-literal capture.

4. **`/sprint` (wave gate)** — Before advancing past the Phase 3 design wave, scan FIXMEs in the Workstream A design doc and confirm the three §Condition-1 sub-sections are present. Absence blocks advancement.

### Updates to design/arch/

None required for this review. The cosmetic close-time items bundled into Workstream E (Decision 25 + Decision 31 Scenario 2 footnote tightening; sequence-diagram SVG/PNG regeneration) are `/arch`'s own work to land in any wave this sprint — they are scope, not review output.

### Phase 3a Design-Doc Review

**Reviewer**: `/arch`
**Artefact 1 verdict**: APPROVED
**Artefact 2 verdict**: CONFIRMED NO DESIGN DOC

#### Artefact 1 — Workstream A design doc

Conditions 1(a), 1(b), and 1(c) are all present and substantive, not heading stubs. §2 Decision-37 alignment correctly identifies the persistence-dual as "the second half of the same structural move" Wave 2 made at the scheduler side, and reproduces the canonical recursion pseudocode. §4 prelude-loading states the unqualified property that every prelude-load invocation enters through `inject_prelude_if_needed` → `scheduler.register_module` with no REPL-special-case shortcut — the Sprint 49 regression surface is explicitly named as the risk pattern being avoided. §5 carry-forward states verbatim preservation of the `program.rs:2184-2232` upsert, correctly noting that the collapse is upstream of the typecheck-crate boundary where the upsert lives, and pins `v4_jit_reclaim::decision31_scenario2` as the regression guard. The target-shape (§3) is coherent with Decision 37: one `register_module` recursion, cache-hit as an internal branch (`try_cache_hit_install`), single persistent-worker pool driving all dep typechecking. All 10 structural sections (problem → D37 alignment → target → prelude → carry-forward → sites → migration → tests → risk → sketch) are substantive. The 5 enumerated collapse sites are line-accurate against current source (verified: `session_v4.rs:1938`, `worker.rs:1286/1703/1803`, and `worker.rs:2315` — the prelude site offset by 2 lines from the cited `:2243` header to the `publish_dep_sexps` call at :2315, both correct). The 7-step migration plan has a cargo-check checkpoint per step and a headline test-flip at step 4 with a halt-and-diagnose gate. §10 Sketch comparison is present and architecturally sharp: "the sketch is silent because it has no scheduler" correctly identifies `compile_dep_inline` as a v3-era holdover, and frames the collapse as convergence toward the sketch's single-orchestrator property — not divergence. No interim architecture is introduced (Principle 8): the collapse is a *deletion*, not a parallel replacement, and every migration step is independently revertible.

#### Artefact 2 — Defect 8 repro

The localised-fix conclusion stands. The panic at Cranelift JIT `finalize_definitions` with "can't resolve symbol run-test" fires before any IO tree is constructed, which falsifies Sprint 58's IO-trampoline hypothesis on the stack trace alone — no re-diagnosis needed. The root cause is a plain AST-scan gap in `program_uses_test_forms` (only scanning `TopLevel::Expr`, missing `TopLevel::Defn` bodies), with the identical latent gap in `program_needs_trace`. Condition 2 invariants (i)(ii)(iii) correctly do not trigger because they guard the trampoline path, which this repro never reaches. No interface, no invariant, no primitive is touched — the fix is a predicate-body widening entirely inside `src/session_v4.rs`. From an architectural lens, the out-of-scope observation #2 (brittle predicate-based extern gating) is a legitimate S60+ simplification candidate worth a FIXME, but does not elevate this defect to design-doc status for Sprint 59.

#### Revisions (if any)

None. `/int` is unblocked for the Workstream A implementation wave. For Artefact 2, `/sprint` may schedule the fix directly into `/int`'s implementation wave as an `/int`-primary ticket with `/backend` review at commit, per the repro report's ownership recommendation.

## Skill Plans

*To be filled during Phase 3 by each skill. Every compiler skill with implementation work (/int, /backend) MUST author or update a design doc in `design/{skill}/`. User-proxy skills (/repl, /port, /stdlib, /examples, /docs, /platform) MUST produce a demo update as part of Phase 5b showcase.*

### /sprint
**Task**: Coordinate sprint; track FIXMEs; run Phase 1→6 methodology.
**Approach**: This file; wave organisation after Phase 3; Phase 6 close protocol.
**Acceptance**: Sprint closes with all six archetype gates met (showcase, FIXME scan, coverage audit, tests, ROADMAP update).

### /arch
**Task**: Phase 2 architecture review; close-time Decision 25 + 31 Sc.2 footnote tightening; regen sequence-diagram SVG/PNG.
**Approach**: Most /arch work has already landed at sprint open — Phase 2 review is signed off (APPROVED WITH CONDITIONS), Phase 3a design-doc review is complete (Workstream A APPROVED; Defect 8 CONFIRMED NO DESIGN DOC), and Workstream E cosmetics are DONE (Decision 25/31 Sc.2 footnotes tightened, sequence-diagram SVG/PNG regenerated from updated `.mmd`). Remaining /arch work: monitor design-doc fidelity during implementation waves — flag any divergence from `design/int/dual-path-persistence-collapse.md` §§2/4/5 if implementation surfaces re-require review; close `/review` sign-off on /arch-owned items at sprint close.
**Design refs**: `design/arch/CLAUDE.md`, `design/arch/pipeline-v4-roadmap.md`, `design/arch/sequence-diagram/`.
**Acceptance**: Phase 2 review signed off; cosmetic items landed in any wave.

### /int
**Task**: Workstream A (dual-path persistence collapse, lead) + Defect 3 (docstring separator) + Defect 8 co-owner (IO-trampoline / `sketch_run_tests`).
**Design doc**: `design/int/dual-path-persistence-collapse.md` — **to be written in Phase 3** before any implementation work. Stub commissioned at sprint open. Defect 8 design shape depends on repro reduction; if a design doc is warranted, co-author with `/backend` in `design/int/io-trampoline-bind-over-io.md` or similar.
**Approach**: Execute the 7-step migration plan in `design/int/dual-path-persistence-collapse.md` §7, collapsing the 5 enumerated dual-path sites (`session_v4.rs:1938`, `worker.rs:1286/1703/1803/2315`) into the single `register_module` recursion shape, with a cargo-check checkpoint per step and a halt-and-diagnose gate at step 4 where the headline test flip is expected. Defect 3 is a 1-line format-string fix at `src/session_v4.rs::append_docstring_comment` per `repl/spec.md §1.1`. Defect 8 is the AST-scan gap at `src/session_v4.rs::program_uses_test_forms` (~:1778-1787) ignoring `TopLevel::Defn` bodies, plus the latent parallel bug in `program_needs_trace` (~:1824) — widen both predicates; `/backend` confirms diagnosis at commit. Keep cargo-check green between steps and preserve the Decision 31 Sc.2 carry-forward invariant at the collapsed upsert site (`program.rs:2184-2232`).
**Design refs**: `design/arch/pipeline-v4.md` §9 (target shape), Decision 37 (register_module recursion), Sprint 58 §Findings (root-cause narrative), Sprint 58 Defect 8 re-triage notes, `design/backend/defect-8-repro-notes.md`.
**Acceptance**: 2 `tests/sprint23.rs` failures green; `v4_cache_hit_dependency` residual resolved; Defect 3 + Defect 8 green; no regression in baseline.

### /backend
**Task**: Workstream B Defects 4, 5, 6 + Defect 8 co-owner (IO-trampoline repro + fix surface) + Workstream C io.rs RC residual.
**Design doc**: If the defects share a root cause (e.g., a common codegen path), capture in `design/backend/ring4-defect-triage.md`. Phase 3 review determines scope. Defect 8 likely requires its own design artefact once repro clarifies the fix surface.
**Approach**: Defect 8 scope has narrowed to *confirming* /int's diagnosis at commit (per Phase 3a repro reduction: localised fix in `src/session_v4.rs`, no backend touches required). Remaining /backend work is Workstreams B (Defects 4/5 batched /run-tests crash with exit codes 139/133, Defect 6 solver stack overflow) and C (io.rs:28 string-literal RC residual, second-deferral threshold). Start each defect with repro reduction to a minimal failing unit test per `feedback_qa_reproduction.md` before diagnosis — Defects 4/5 likely share a codegen-incomplete path + RC/last-use issue in exemplar html/form modules; Defect 6 likely TCO or codegen depth. Workstream C follows `ring2-rc.md §3.3` with Decision 24 Scope Clause 2 framing; cite Decision 24 Clause 1 at commit if the bug lives on the codegen side of the capture-into-Effect boundary.
**Design refs**: `design/backend/ring2-rc.md` §3.3 (Decision 24 extern audit), Sprint 58 Defect 4/5/6 triage notes, `design/backend/defect-8-repro-notes.md` (diagnosis to confirm).
**Acceptance**: 3 `wave6_demo_repros` failures green (Defects 4+5, 6) + `sketch_run_tests_pass_fn_called` green (Defect 8); `/port` unblocks Defect 7; io.rs RC symptoms named in `ring4.md §G.14` no longer reproduce.

### /frontend
**Task**: No implementation; Phase 3 review of any AST-surface implications of Workstream A design; confirm no cross-skill touches.
**Approach**: Review-only. Phase 3a design doc signed off; no AST-surface changes are indicated by the collapse. Act as cargo-check sentinel during /int's implementation waves, flagging any unexpected frontend touches that emerge from the 7-step migration; sign off at close if none appear.
**Acceptance**: Review sign-off or explicit "no concerns".

### /typecheck
**Task**: No implementation; Phase 3 review of Workstream A design for CheckState/SymbolTable interactions.
**Approach**: Review-only. Phase 3a design-doc sign-off confirms the collapse is upstream of the typecheck-crate boundary (the `program.rs:2184-2232` upsert carry-forward is preserved verbatim). Act as cargo-check sentinel during /int's implementation waves; flag if any SymbolTable `<C, L>` generics or CheckState interactions surface unexpectedly.
**Acceptance**: Review sign-off or explicit "no concerns".

### /qa
**Task**: Workstream D (module-boundary neg tests); Phase 3 derive test cases for Workstream A from the design doc (including heisenbug parallel-run repro); Phase 5b audit.
**Approach**: 6 new tests landed at Phase 3a per `tests/plan/ring4.md §G.19` — failing, un-ignored, `// spec:` annotated. Wave 2 work: verify each test flips green as /int Workstream A steps land (headline flip at migration step 4 per design doc §7) and as /int's Defect 3/8 + /backend's Defects 4/5/6 close; no #[ignore] churn since nothing is ignored. Wave 5 work: coverage audit — promote `[Tested+Neg]` on spec §8.3.1/§8.3.7/§8.3.9 headings once the 4 Workstream D neg tests pass; showcase verification that acceptance surface is green.
**Acceptance**: 4 new passing neg tests landed; `[Tested+Neg]` promotions on §8.3.1 / §8.3.7 / §8.3.9; Workstream A test plan in `tests/plan/ring4.md`.

### /review
**Task**: Code review of all waves producing code (A, B, C, D). Apply 2x-deferral escalation policy for any Important findings carried from Sprint 58.
**Approach**: Run at the close of every implementation wave (/int Workstream A; /backend Workstreams B + C; /qa Workstream D) with standard report shape — Blockers / Importants / Minors. No Sprint-58-carried Important findings are currently open, so the 2x-deferral escalation ledger starts clean this sprint; if any new Important is deferred, escalate on second deferral per policy. Final PASS report at sprint close.
**Acceptance**: /review report PASS; 0 Blockers at close; Importants resolved or explicitly deferred with rationale.

### /spec
**Task**: Evaluate §8.11.5 platform directory list spec abstraction (bundled Workstream E). If in scope, small update in Phase 3/4; if out of scope, explicit defer.
**Approach**: §8.11.5 platform directory list abstraction is DONE at sprint open — landed in scope during Workstream E cleanup. Remaining /spec work is responsive: action any FIXME(/spec) comments that /int or /qa file during implementation, and assist /qa with `[Tested+Neg]` promotions on spec §8.3.1/§8.3.7/§8.3.9 headings as the Workstream D neg tests flip green.
**Acceptance**: Spec updated or explicitly deferred.

### /stdlib
**Task**: Workstream E — verify the 3 missing files from Sprint 58 I-2 audit; lock in 35 vs claimed 32 count; refresh stdlib demo.
**Approach**: I-2 audit is DONE at sprint open — count reconciled at 35 files, all 3 suspected files (`derive.cl`, `defs.cl`, `default.cl`) verified clean. Remaining /stdlib work: refresh the stdlib demo for Phase 5b showcase and respond to any FIXME(/stdlib) comments filed during implementation waves.
**Acceptance**: Audit count reconciled; demo plays cleanly.

### /examples
**Task**: No implementation; validate examples compile/run against the current baseline.
**Approach**: No new implementation. At Phase 5b, run `cargo run -- --run examples/*.cl` against the S59 baseline to confirm all examples still compile and execute; update the examples demo script; flag any regressions introduced by Workstream A/B changes as FIXME(/int) or FIXME(/backend) for the owning skill.
**Acceptance**: `cargo run -- --run examples/*.cl` all green; examples demo current.

### /platform
**Task**: Phase 3 review of Workstream A for any platform-registry impact; no implementation expected.
**Approach**: Review-only. Workstream A operates on `register_module` and REPL-session persistence surfaces; no platform-registry or DLL-loading impact is indicated. At Phase 5b, run a currency check on the platform demo and update if `/backend`'s Defect 4/5 fixes touch DLL loading paths.
**Acceptance**: Review sign-off or explicit "no concerns"; platform demo current if Workstream B Defects 4/5 touch DLL loading.

### /docs
**Task**: Phase 5b — update user-facing docs if Workstreams A or B change observable behaviour (error messages, REPL output).
**Approach**: At Phase 5b, audit `user/` tutorials and guide for observable-behaviour changes introduced by Workstreams A (restart/import persistence semantics) and B (docstring separator per `repl/spec.md §1.1`, batched `/run-tests` behaviour, solver exemplar). Update affected passages; verify the docs demo plays cleanly against the S59 baseline.
**Acceptance**: Docs current; docs demo plays cleanly.

### /port
**Task**: Defect 7 (re-enable 3 puzzle tests in `exemplar/solver.cl` once Workstream B Defect 6 closes). Exemplar showcase update for Phase 5b.
**Approach**: Blocked on /backend Defect 6 close. Once the solver stack-overflow fix lands, re-enable the 3 previously-disabled puzzle tests in `exemplar/solver.cl` and verify they pass against the S59 baseline. At Phase 5b, refresh the exemplar demo to show the restored test surface.
**Acceptance**: 3 tests green; exemplar demo plays cleanly.

### /repl
**Task**: Phase 5b — create `repl/demos/ring4p.demo` (or equivalent) demonstrating the dual-path persistence fix (e.g., restart-survives-import) and the closed defects (docstring separator, batched run-tests).
**Approach**: At Phase 5b, author a new sprint demo (`repl/demos/ring4p.demo` or next-letter increment) exercising the dual-path persistence fix end-to-end (restart-survives-import scenario), the docstring `-` separator per `repl/spec.md §1.1`, and the batched `/run-tests` crash closure. Play all prior demos against the S59 baseline to verify no regressions, following `repl/demos/CLAUDE.md` conventions.
**Acceptance**: New sprint demo plays cleanly; all prior demos verified; `repl/demos/CLAUDE.md` conventions followed.

## Waves

Phase 3 closed with all artefacts landed: `/int` Workstream A design (APPROVED), `/backend+/int` Defect 8 repro (localised — no design doc), `/arch` Phase-3a review, `/qa` ring4 §G.19 + 6 new failing tests, `/arch` Workstream E cosmetics DONE, `/stdlib` I-2 audit DONE, `/spec` §8.11.5 DONE. Remaining work organises into three implementation/showcase waves plus a close wave.

### Wave 1: Implementation + test verification (parallel)

All fixes land in parallel; `/review` runs within the wave (not deferred); `/qa` verifies test flips as each fix lands. `/int` Workstream A proceeds via the design doc §7 7-step migration plan with cargo-check checkpoints between steps.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | Workstream A dual-path collapse (design doc §7 steps 1–7) | pending | 3 failing tests flip green (cache_repl_loads, persist_import_survives, v4_cache_hit_dependency); heisenbug parallel-run stress passes |
| /int | Defect 3 docstring separator — `src/session_v4.rs::append_docstring_comment` format fix | pending | `wave6_demo_repros::display_defn_with_docstring_uses_dash_separator` flips green |
| /int | Defect 8 — `program_uses_test_forms` AST-scan gap + parallel `program_needs_trace` fix | pending | `sketch_port::sketch_run_tests_pass_fn_called` + Phase-3a-authored `defn_body_with_trace_triggers_extern_registration_neg` flip green |
| /backend | Defects 4+5 — batched `/run-tests` crash (html exit 139, form exit 133) | pending | Start with repro reduction per `feedback_qa_reproduction.md`; `wave6_demo_repros::run_tests_batched_invocation_no_crash` flips green |
| /backend | Defect 6 — solver stack overflow | pending | Blocks /port Defect 7 (Wave 2); `wave6_demo_repros::exemplar_solver_does_not_stack_overflow_on_small_puzzle` flips green |
| /backend | Workstream C — `crates/cranelisp-runtime/src/io.rs:28` RC residual | pending | 2nd-deferral-threshold item; must ship; if codegen-side, commit cites Decision 24 Scope Clause 1 |
| /qa | Verify the 6 Phase-3a-authored failing tests flip green as fixes land | pending | `tests/sprint59_neg.rs` × 5 + `tests/sprint23.rs::cache_repl_loads_heisenbug_parallel_stress` |
| /review | Per-wave code review on every implementation skill's new code | pending | 2x-deferral escalation policy active; 0 Blockers at close |
| /frontend | Review-only sentinel — cargo-check green during /int implementation | pending | Sign-off or explicit "no concerns" |
| /typecheck | Review-only sentinel — SymbolTable/CheckState interactions preserved | pending | Sign-off or explicit "no concerns" |
| /platform | Review-only sentinel — no platform-registry impact indicated | pending | Sign-off or explicit "no concerns" |

**Wave 1 gate**: all 6 Phase-3a failing tests plus the 3 Workstream A flips go green; `/review` reports 0 Blockers; `/sprint` scans for unresolved FIXMEs introduced in this wave.

### Wave 2: Dependent fixes

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /port | Defect 7 — re-enable 3 puzzle tests in `exemplar/solver.cl` | blocked-by Wave 1 /backend Defect 6 | 3 tests green against S59 baseline |
| /qa | Final failure-sweep — confirm baseline at 0 carried failures (or document re-triage) | blocked-by Wave 1 completion | Sprint 58 close was 6/6; S59 target is 0/6 |

**Wave 2 gate**: 0 carried failing tests (or explicit re-triage with user approval per the Defect 8 re-scope clause — unlikely given Phase-3a localisation).

### Wave 3: Phase 5b showcase (user-proxy skills)

Mandatory showcase wave per `/sprint` archetype. Every user-proxy skill exposes the sprint's work via demos and docs.

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /repl | New sprint demo `repl/demos/ring4p.demo` (or next letter) — dual-path persistence + Defect 3/4/5/6 closures | blocked-by Wave 2 | Replay all prior demos for regression check |
| /port | Exemplar demo refresh — show restored puzzle test surface | blocked-by Wave 2 | Demo plays cleanly |
| /stdlib | Stdlib demo refresh | blocked-by Wave 1 | Reflects locked-in count/audit state |
| /examples | `cargo run -- --run examples/*.cl` sweep; examples demo update | blocked-by Wave 1 | All green; flag any regressions |
| /docs | User-facing docs audit for observable-behaviour changes; docs demo refresh | blocked-by Wave 1 | Docstring separator, restart/import semantics |
| /platform | Platform demo currency check; update if Defects 4/5 touched DLL loading | blocked-by Wave 1 | Demo plays cleanly |
| /qa | Coverage audit — confirm `[Tested+Neg]` promotions on §8.3.1/§8.3.7/§8.3.9 as Workstream D tests pass | blocked-by Wave 1 | Update spec annotations |

**Wave 3 gate**: new sprint demo plays cleanly; all prior demos play cleanly; all user-proxy demos current.

### Wave 4: Close (Phase 6)

| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /review | Final /review report — PASS required | blocked-by Wave 3 | Importants resolved or explicitly deferred with rationale |
| /qa | Pass-2 close-time audit — every spec requirement in scope has a passing test | blocked-by Wave 3 | FIXME scan clean; coverage audit clean |
| /sprint | Close checklist (every gate in §Sprint Archetype Phase 6); outcome section; archive; ROADMAP update | blocked-by /review + /qa close items | Status → COMPLETE; file moves to sprints/archive/sprint-59.md |

**Close gate**: all Phase-6 checklist items in `.claude/commands/sprint.md` §Sprint Archetype Phase 6 pass.

### Wave ordering rationale

- Implementation + /review + /qa verification co-located in Wave 1 (spec-first test model; no deferred review).
- /port and /qa finalisation in Wave 2 on /backend's Defect 6 dependency.
- Showcase is mandatory and gates close; cannot collapse into Wave 1 because user-proxy demos depend on fixes being in place.
- Close wave is single-skill synthesis — /sprint + /review + /qa only.

## Notes

**Deferral escalation active**: `crates/cranelisp-runtime/src/io.rs:28` RC residual is at the second-deferral threshold — Workstream C ships it unless the user explicitly approves a third deferral. Flag if `/backend` requests descope during Phase 3.

**Scope note**: The 286-FIXME total inventory is dominated by design-doc forward-pointers (healthy — they name owning skills and follow-on actions). In-scope FIXMEs are the 9 above. This is normal post-Sprint 58 debt distribution.

**S59 milestone**: First post-convergence sprint to target **0 carried failing tests**. If Workstream B Defect 8 repro reveals an IO-trampoline redesign that cannot land in-sprint, `/sprint` re-scopes with user approval (per the `Defect 8` note in Workstream B). Otherwise the baseline at close is 0 pre-existing + 0 new carries.

**FIXME(/arch + /backend) for S60 — CRITICAL: JIT vs object codegen divergence is an architectural red flag.** Sprint 59 Wave 1 `/backend` RC-underflow fix (`protect_return_value`) flipped REPL-entered defns green 5/5 — but the SAME source, imported from a module (object-file path), still fails ~75%. Two code paths producing different behavior for identical source is a fundamental architectural violation: JIT finalization and object-file emission should produce **byte-identical code**, differing only in the fixup mechanism (JIT direct-finalize-then-invoke vs `.o`-relocations + link-loading). The divergence points at one of: (a) codegen context state that leaks between the two paths (e.g., context-dependent optimization decisions), (b) different compilation *sessions* producing different monomorphisations, (c) `.o`-serialization-roundtrip dropping metadata needed by link-loading, (d) Decision 31 JIT-page reclaim interacting with captured `func_addr` values in a way the `.o` path doesn't exercise. **S60 work**: /arch-driven audit to confirm the invariant (same source → same code bytes, only fixup mechanism differs), then root-cause the divergence. This is likely the root cause of the 5 remaining S59 carries (Defects 4/5/6 + `d45_solution_cell_single_call_no_rc_underflow` + new d45_html_min). Candidate S60 primary workstream.

**FIXME(/backend) for S60 consideration — object-file build marker for cache invalidation across compiler rebuilds.** Today's debugging cost hours to paths that were ultimately driven by repeated cache interactions. Current `.meta.json` carries `schema_version: u32` (Decision 34) but only guards metadata layout; it does NOT auto-invalidate when the `cranelisp` binary itself is rebuilt (codegen evolution, RC convention change, GOT layout change, new relocation types). Proposal: embed a build marker in every `.o` / `.meta.json` — simplest is exe mtime (cheap, local-dev good), more reliable is an `env!("CARGO_PKG_VERSION")` + `option_env!("GIT_SHA")` from `build.rs` compile-time constant, checked on cache load. Mismatch → recompile the affected module. ~50 LOC of `build.rs` + 2-3 lines at cache-load site. Defensive against a bug class that's expensive to diagnose and costs zero to prevent. Candidate for a backend-stabilisation sprint alongside the CLIF-dump infrastructure FIXME.

**Wave 1 /int finding — cache_repl_loads_on_startup is not a dual-path defect** (filed 2026-04-20 during Workstream A implementation): The FIXME at `tests/sprint23.rs:1126-1131` attributed this failure to the Sprint 58 dual-path persistence root cause, and it was listed in the Workstream A clearance table. Phase 3 design doc §8 also predicted this test would flip at Step 4. In fact, the session-2 failure mode is a backend cache-linker error — `module 'prelude' failed: codegen error at 0..0: GOT_LOAD relocation: unresolved symbol '.Ldata0' (cannot allocate slot for unknown address)` at `crates/cranelisp-backend/src/cache/linker.rs:148` — which reproduces *identically* on the baseline (pre-my-changes) binary. Confirmed via `git stash` + rebuild + manual REPL repro: first session populates the cache, second session fails loading prelude from `.o` with an unresolved `.Ldata0` symbol. This is /backend territory (cache-loading Linker integration), not /int dual-path persistence. The other two Workstream A target tests (`persist_import_survives_restart`, `v4_cache_hit_dependency`) flipped green as predicted, the heisenbug parallel-run stress (`cache_repl_loads_heisenbug_parallel_stress`) passes rock-solid, and the Sprint 58 W6 Defect 1 end-to-end guard (`repl_dep_load_no_race_with_persistent_workers`) remains green — so Workstream A's actual scope landed successfully. FIXME(/backend) should be filed at `crates/cranelisp-backend/src/cache/linker.rs` for the `.Ldata0` relocation; FIXME(/int) at `tests/sprint23.rs:1126-1131` to re-attribute the comment.

## Outcome

**Closed 2026-04-21. Baseline: 1801 tests total; 5 expected carries (pre-existing defect cluster), 0 new regressions.**

### Delivered

- **Workstream A — Dual-path persistence collapse** — `register_dep` shim consolidates 5 previously-duplicated per-dep prologue sites in `src/worker.rs` + `src/session_v4.rs`. New `wait_module_inmem_complete_blocking` scheduler primitive avoids whole-world-wait deadlock. 3 target failing tests flipped green: `sprint23::persist_import_survives_restart`, `v4_pipeline::v4_cache_hit_dependency`, `sprint23::cache_repl_loads_heisenbug_parallel_stress` (new 20-iter stress test, rock-solid). Decision 31 Scenario 2 carry-forward invariant preserved. See `design/int/dual-path-persistence-collapse.md` for the approved design + 7-step migration plan.
- **Cache-hit prelude glob-import parity** (late-discovered /int follow-on, same workstream scope) — `inject_prelude_if_needed` cache-hit arm now calls `register_imports(prelude_spec)` to match the else arm. Flips `sprint23::cache_repl_loads_on_startup` + 2 new `tests/sprint59_cache_repro.rs` tests green (single-function prelude survives session restart).
- **Defect 3** — docstring separator in `src/session_v4.rs::append_docstring_comment` uses `-` per `repl/spec.md §1.1`. `wave6_demo_repros::display_defn_with_docstring_uses_dash_separator` green.
- **Defect 8** — `program_uses_test_forms` + `program_needs_trace` AST scans now walk `TopLevel::Defn` bodies (not just `TopLevel::Expr`) via a shared `any_expr_in_program` helper. Plus a `needs_test_state` transitivity fix. `sketch_port::sketch_run_tests_pass_fn_called` + new `sprint59_neg::defn_body_with_trace_triggers_extern_registration_neg` green.
- **Workstream C-i** (RC residual) — `CLHeap::into_owned_consuming` trait method added; `platforms/stdio` + `platforms/test-capture` externs migrated off the leaky `CLString::own()` pattern. FIXME at `io.rs:28` cleared. 3 new unit tests in `cranelisp-platform`. Fix is extern-shell-side; Decision 24 Scope Clause 1 not invoked. `design/backend/ring2-rc.md §3.3` audit table updated.
- **Workstream C-ii** (linker GOT local-symbol) — `Linker::ensure_got_slot` signature extended to accept caller-supplied address; `.L*` Cranelift-emitted local data symbols now allocate slots correctly. Originally scoped by triage to flip `sprint23::cache_repl_loads_on_startup` green — that turned out to be a layered-bug case (C-ii was real but the user-visible test flip needed the cache-hit prelude parity fix above).
- **`protect_return_value` RC-underflow fix** — `/backend` narrowed the "has heap bindings" predicate in `crates/cranelisp-backend/src/compiler/mod.rs:1123-1139` to exclude `borrowed_vars` and `consumed_vars` so the protective inc only fires when scope cleanup will actually dec. CLIF-confirmed: REPL-entered defns pass 5/5 after the fix. Does not resolve the module-imported failure class — see §Findings.
- **Workstream D — Module-boundary negative coverage** — 4 new neg tests in `tests/sprint59_neg.rs` all green. Spec promotions to `[Tested+Neg ...]`: `§8.3.1`, `§8.3.7`, `§8.3.9`, `§4.12`.
- **Workstream E — Sprint-opening cleanups** — `design/arch/CLAUDE.md` Decision 25 + Decision 31 Sc.2 footnote tightening; `design/arch/sequence-diagram/v4-target.svg`/`.png` regenerated from updated `.mmd`; `stdlib/plan-stdlib.md §15` audit reconciliation (count locked at 35, I-2 closed); `spec/08-modules.md §8.11.5` restructured to parallel §8.11.4.
- **Phase 1 discipline codification (root `CLAUDE.md` + 2 new memory entries)** — three new paragraphs in §"Usability Findings and Defects": (a) cross-skill defect handoff requires minimal repro before handoff; (b) reproduced defects join the test suite permanently; (c) keep reductions small to enable CLIF-by-eye inspection. Memory files: `feedback_cross_skill_minimal_repro.md`, `feedback_repros_join_suite.md`. These disciplines paid for themselves in-sprint twice over (discovered layered bugs in cache_repl_loads_on_startup + identified JIT/object divergence as the root finding for Defects 4/5/6).
- **Phase 5b showcase**: `repl/demos/ring4q.demo` (49 LOC) authored; 25 prior demos replayed green; `/repl` validated; stdlib/platform/port/docs demos current.

**Test metrics (close)**:
- Total runnable tests: ~1801
- Sprint 59 new tests: 13+ (6 /qa Phase 3a + 7+ defect-repro reductions committed during fix attempts)
- Passing flips this sprint: 8 (3 Workstream A + Defect 3 + Defect 8 + C-ii + cache-hit parity × 2)
- Failing carries to S60: 5 (Defects 4/5 html, Defect 6 solver, `d45_solution_cell_single_call_no_rc_underflow`, `d45_html_min_v1`, `d6_exemplar_propagate_only`)
- Regression sentinels: 6/6 green

### Deferred

**5 failing tests carried to S60** — all trace to the same underlying issue (see §Findings — JIT/object divergence):
- `wave6_demo_repros::exemplar_solver_does_not_stack_overflow_on_small_puzzle`
- `wave6_demo_repros::run_tests_batched_invocation_no_crash`
- `sprint59_defects456_repro::d45_html_min_v1_no_crash`
- `sprint59_defects456_repro::d6_exemplar_propagate_only_does_not_segv`
- `sprint59_defects456_repro::d45_solution_cell_single_call_no_rc_underflow`

**/port Defect 7 carried** (blocked on Defect 6): re-enable 3 puzzle tests in `exemplar/solver.cl` once /backend resolves the JIT/object divergence.

**3 Wave-1 /review Importants (first-time defer; FIXME'd + `design/review/sprint-59-wave-1.md` recorded)**:
- **I-1** — `register_dep_for_eval` passes `delays_other=false`; worker-side sites pass `true`. FIXME at `src/session_v4.rs:1307`.
- **I-2** — `recurse_into_transitive_deps` at `src/worker.rs:~1637` is a 6th per-dep prologue site the collapse missed. FIXME at that site.
- **I-3** — deleted unit guard `compile_dep_inline_publishes_sexps_before_register` — folded into I-2 FIXME.

**S60 /arch + /backend FIXMEs filed in this SPRINT.md**:
- **JIT vs object codegen divergence** (CRITICAL) — architectural invariant audit; likely root cause of the 5 carries.
- **Object-file build marker for cache invalidation** — defensive against cache-staleness across compiler rebuilds.
- **CLIF-dump infrastructure** (`CRANELISP_CODEGEN_TRACE=1`) — captured at `design/backend/defects-456-reduction.md` §Phase 2.
- **`cache_repl_loads_on_startup` original misattribution** — the FIXME at `tests/sprint23.rs:1126-1131` has now been updated in-sprint (resolution text) but was documented during Wave 1.

**Observations recorded (not S59-scope)**:
- **Examples `--run` path broken since Sprint 1** — 27 `.cl` files in `examples/` use bare primitive names (`add-i64`, `eq-i64`, etc.) not exposed by the stdlib prelude re-export shell; `tests/examples.rs` green via test-fixture prelude path. `cranelisp --run examples/FOO.cl` fails. S60 examples-focused sprint candidate.
- **`/sig` docstring display gap** — `/sig add` on a docstring'd defn shows `:(Fn [Int Int] Int) add ; defn` (dash + docstring omitted); `repl/spec.md §1.1` mandates universal format. Separate from Defect 3 (which fixed the defn-confirmation-line separator). Candidate for a `/repl` compliance audit.
- **FIXME(/docs)** at `user/plan-docs.md:218-232` — docstring example format uses old `; <doc>` pattern. Planning artefact drift, no user-facing gap.
- **`cargo nextest list` hung twice post-compile during Wave 2** — transient; not a defect yet; worth watching.

### Findings

**Structural — JIT vs object codegen divergence** (load-bearing for S60 scope):

After the `protect_return_value` RC-underflow fix landed, REPL-entered defns pass 5/5 deterministically but module-imported defns still fail ~75% with raw SIGTRAP (no stderr, no Rust panic). **Same source, same mechanism should produce same code bytes — only the fixup mechanism should differ** (JIT direct-finalize-then-invoke vs `.o`-relocations + link-loading). The observed divergence is an invariant violation, not just a specific bug symptom. This finding is named as an S60 /arch + /backend audit: confirm the invariant, then root-cause the divergence. Likely the single root cause for all 5 remaining carries.

Three sub-hypotheses for the divergence (from `design/backend/defects-456-reduction.md §"Still to resolve"`):
1. Monomorphised defn codegen context divergence across module boundaries
2. Auto-curry closure-over-polymorphic-dispatch RC contract mismatch between paths
3. Cross-module GOT drop-glue `func_addr` interacting with Decision 31 JIT-page reclaim

The raw-trap-no-stderr signature (vs a Rust `debug_assert!` which flushes stderr) implicates (3).

**Process — minimal-repro discipline paid for itself, multiple times**:

Sprint 59 codified three new rules (cross-skill handoff needs minimal repro; repros join the suite for eternity; keep reductions small for CLIF-by-eye inspection). Each rule was exercised in-sprint and returned value:
- Cross-skill minimal-repro discipline caught the layered-bug case in `cache_repl_loads_on_startup` (C-ii linker fix was real but didn't flip the test; the second bug was in /int cache-hit prelude parity). Without discipline, we'd have thought C-ii "fixed" it and missed the parity bug entirely.
- Repros-join-the-suite converted 20+ reduction tests into durable guards. The 39-LOC Defects 4/5 minimal repro and the single-call `(solution-cell g g 0)` repro would have been thrown away in the prior workflow.
- Keep-reductions-small made CLIF inspection tractable and surfaced the double-inc pattern in `protect_return_value` (a real bug, now fixed).

**Process — scope re-assessment happened twice mid-sprint, both times correctly**:
1. /int's Workstream A reported `cache_repl_loads_on_startup` as "not dual-path, looks like /backend linker". /sprint correctly spawned a 30-min /backend triage before committing scope (user-directed Option 3). Triage recommended fold; fold landed; layered-bug structure surfaced; /int parity fix completed it.
2. /backend's TCO-scope-cleanup fix didn't flip the minimal repros but didn't regress either. /sprint asked user for disposition; user authorized further reduction; reduction yielded the unified JIT/object-divergence finding.

**Sketch lesson**: In both mid-sprint re-scopes, the project's own rule ("reduce before handoff; repros join the suite") was the discipline that made the decisions tractable. Honor it in S60 and beyond.

**Sprint burden**: /int HEAVY (Workstream A + Defect 3 + Defect 8 + cache-hit parity + /review I-1/I-2 FIXMEs); /backend HEAVY (C-i + C-ii + `protect_return_value` + reduction agent work + Defects 4/5/6 triage + diagnostic CLIF capture). User-proxy skills LIGHT (showcase + demo replay). Actual /int burden matched the scope assessment ("HEAVY — but narrower than Sprint 58"). Actual /backend burden was higher than planned due to the defect-reduction cycles.
