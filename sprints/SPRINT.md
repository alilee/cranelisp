# Sprint 124: Type concreteness at codegen

**Status**: PHASE 5 LANGUAGE — W5 accepted; W6 next

**Goal**: Make every type that reaches codegen concrete — census, typecheck
producer obligations, backend structural close — and clear the crash-class and
frontend carries behind it.

**Audit**: `cranelisp-typecheck` (approved 2026-11-17: longest unassessed, last
audited S114, and S124 completes a major arc there). Read-only, in the Phase 6/7 window.

## Phase approvals

| Transition | Checkpoint presented | User approval | State |
|---|---|---|---|
| Start → Phase 1 | "let's plan the next sprint" | 2026-11-16 | approved |
| Phase 1 → Phase 2 | scope draft with seven included items | 2026-11-16, "advance to phase 2" | approved |
| Phase 2 → Phase 3 | `arch` review, API packet D1–D8, six decisions | 2026-11-16, "advance to phase 3" | approved |
| Phase 3 → Phase 4 | designs, packet rows D1–D12/R10-9/R10-10, S124-Q2..Q9, `qa` readiness | 2026-11-17, "approved to advance" | approved |
| Phase 4 → Phase 5 | wave plan W0–W9, audit choice, two decisions | 2026-11-17, "approved" | approved |
| Phase 5 → Phase 6a | — | — | pending |
| Phase 6a → Phase 6b | — | — | pending |
| Phase 6b → Phase 7 | — | — | pending |

## Opening state (2026-11-16)

- **Shared package converged** at the opening gate: `.agents` fast-forwarded
  26 commits to se-agentic `5ee3cb9`, then to `cfc0a4e` (below). `check_consumer.py` reports conformant.
- **Allocation change (user, 2026-11-16):** `arch` and `qa` run on
  `claude-fable-5-2` at `medium`. Edited in `.agents/agents/`,
  `.agents/CONSUMING.md` and `.claude/agents/`; published as se-agentic
  `cfc0a4e`, which the superproject pins.
- **Suite on the opening tree:** 7,024 run, 6,976 passed, 48 failed, 1 skipped.
  44 are the filed guards recorded at the S123 close. The other four:
  - three `citation_drift` tests fail because the converged document checker
    requires `inventory.root_memory = "AGENTS.md"`; the documented checker
    invocation exits 2 for the same reason;
  - one `user_samples` test failed once in the full run and passed alone.
- **`qa` classification (Phase 3, [evidence delta](../tests/plan/s124-evidence-delta.md)):**
  the stable failing set is 47 — the 44 guards and the three `citation_drift`
  maintenance checks. Two `user_samples` tests fail run-dependently under
  load (ACT-1061). No genuine regression.
- The suite leaves an untracked `ctx.txt` in the repository root; a module
  test writes it (ACT-1060, to `dev` on `src/`).
- **Lead for `sprint`:** `sprints/s123-api-packet.md` and
  `sprints/s123-architecture-review.md` remain in the standing tree after the
  S123 close.

## Scope

### Settling target (proposed; observable on a fresh build of the final tree)

- The armed category census reports zero RC operations on a word whose type
  is not concrete, and the non-concrete release and retain arms no longer
  compile ([FIXME 0903](../design/arch/fixmes/0903-s4-1-frame-key-excludes-two-measured-escapee-families.md)).
- The twelve `bind_unused_heap_argument` guards (ACT-1050) and the
  cached-restore guard (ACT-1052) pass in every mode.
- The document checker and `citation_drift` pass against the converged package.
- `cargo nextest run --no-fail-fast` reports zero failures: every guard failing
  on the opening tree passes, or is carried on recorded evidence that it is
  unreachable this sprint.

### Included

1. **Type concreteness (lead, user ruling at the S123 close).** In order: run
   the census; typecheck's producer obligations
   (`design/typecheck/non-concrete-producer-obligations.md` — trait-method
   instances, synthetic accessors, the lenient view); the backend structural
   close of FIXME 0903;
   [ACT-1050](actions/ACT-1050-inline-bind-continuation-unused-heap-argument-leak-intake.md)
   grouped with it.
2. **Crash-class:** [ACT-1052](actions/ACT-1052-restored-entry-text-stale-dependent-slot-intake.md)
   — an importer's cached object calls a moved slot after a reverted
   ABI-changing edit.
3. **Raise-helper hardening** (P-15): a raise-helper bypass does not compile.
4. **Principle 27 retirements:** stack placement (resolving ACT-1049), value
   flattening, the spark-density axis, the borrow-elision carrier, and the
   mode-ABI redefinition gate with
   [ACT-0953](actions/ACT-0953-decouple-live-slot-abi-from-ownership-inference.md)
   and its spec ruling.
   The S123 packet's unlanded rows K11-a to K11-d and R10-1 to R10-8 land
   with this sprint (user, 2026-11-16; see Notes).
5. **Frontend:** the [audit](../audits/cranelisp-frontend-s123.md)'s R1–R5 as
   disposed below, with ACT-1055, ACT-1056 (and ACT-0997 at the `arch` gate)
   and ACT-1057, each of which has committed REDs.
6. **Package convergence (new, from the opening pull):** adopt the `AGENTS.md`
   repository-memory convention the converged checker requires — 103
   `CLAUDE.md` memories, `standing-documents.toml`, `.codex/config.toml` and
   the references to them; declare the provisional `ux` role as not
   dispatched; decide adoption or non-adoption of the newly offered standards
   and hooks (spec traceability, Rust build, Rust context checks,
   session-environment hooks, shared-tree guard).

7. **Get to green (user direction, 2026-11-16).** Every remaining guard
   failing on the opening tree, by root (mapping verified by `arch` against
   each guard's citation, Phase 2).

   | Action | Guards | Failure |
   |---|---|---|
   | ACT-1034 | 4 | Parametric impl instance calling another impl or generic function is undefined at codegen; likely rides item 1 |
   | ACT-1038, ACT-1039 | 3 | Run-mode trace omits user functions; traced spark-worker calls leak and go unrecorded |
   | ACT-0973 | 2 | Non-entry platform declarations accepted; needs a spec answer and a naming decision |
   | ACT-1016 | 3 | Closed export cycle not reported as a cycle; a failed re-export dependency reloads differently from restart |
   | ACT-0985 | 1 | Impl body uses an impl declared later in the cluster |
   | ACT-1001 | 1 | Ambiguous trait name does not name both candidates |
   | ACT-1036 | 1 | `main` return refusal carries a synthetic location |
   | ACT-1018 | 1 | Warm Sudoku solve retains allocations; re-measure after ACT-1050 first |

### Frontend audit disposition (all five accepted by the user, 2026-11-16)

| Rec | Finding | Route |
|---|---|---|
| R1 | Macro declaration shapes the spec forbids are accepted | `qa` allocates reproductions; joins ACT-1057 |
| R2 | Module extraction does not implement the compositional entry grammar | `qa`, with ACT-0997/1055/1056; `arch` frames any public-API delta |
| R3 | Signed reader branches skip the operator/digit rule | `qa` for a paired reproduction and control |
| R4 | Expression-width plumbing always returns 1; parallel test routing | frontend `design` → `dev` |
| R5 | Frontend memory and rustdoc contradict source | frontend `design`/`dev`; `arch` for boundary promises |

### Excluded

- Fixes for the carried groups with no failing guard (runtime concurrency,
  persistence, diagnostics and discovery, run-dependent residuals); their
  reproductions are in scope (user, 2026-11-16; see Notes).
- ACT-1054 (primitive checked/unchecked direction), ACT-0962, ACT-0960 and
  LLVM, by user direction.
- FIXME 0907's remaining legs, the `io-trampoline.md` rewrite, the §17.4
  combination cell and the stale status prose named in the S123 close summary
  — unless the user pulls them in.

### Size and order

Very large. Item 7 widens the sprint mainly in typecheck and the module and REPL
surfaces, alongside the backend chain. Item 6 runs first (W0) because it restores the document gate and
touches every memory file, so nothing else can share the tree with it. Item 1
is sequential and gates items 3 and 4 in the backend. Items 2 and 5 are
independent of the backend chain. If item 1 proves unreachable it narrows to
the census plus the producer obligations, never by dropping the census.

### External operations

Approved 2026-11-16: publish the allocation change to se-agentic `main`
(done, `cfc0a4e`) and commit the opening state. No push to `origin` without a
separate request.

## Architecture review (Phase 2)

`arch`'s [review](s124-architecture-review.md) and [API packet](s124-api-packet.md)
(rows D1–D11) carry the outcome. Verdict: the scope fits the existing crate
boundaries; sign-off is conditional on six user decisions and the D1–D7 gate.

## Phase 3 outcome

- **Spec:** REPL §18.1.2 removed; §4.12.2 strict tracing; REPL §1.5 and
  §12.1.1 after flattening. S124-Q2..Q9 ruled 2026-11-17 (Notes). The type-size question is an accepted risk (Notes).
- **Architecture:** `design/arch/` carries the S124 targets; the
  [packet](s124-api-packet.md) holds every row approved: D1–D12, R10-9 and
  R10-10.
- **Designs:** backend, intrinsics, typecheck, frontend and `src/` are
  written, each with its own order section.
- **Evidence:** `qa`'s [delta](../tests/plan/s124-evidence-delta.md) is the
  single handoff for `test`; readiness (restated 2026-11-17) is "ready with
  two conditions": the evidence wave runs before D1 with REPRO-1062 first;
  `spec` and `design`(typecheck) settle what the depth integer counts before
  `dev`(typecheck) fixes it in T4. Held: F-PR-3 (type-size question) and
  T-DEPTH-c (counting unit).
- **Attribution changes:** ACT-1034 is typecheck's; ACT-1050 is the binary's
  bind-chain rewrite; ACT-1039 is the backend's.
- **New defect:** ACT-1062, a match on a type whose fields are out of
  parameter order corrupts memory; corrected by row D1.
- **Defects confirmed from Phase 3 leads:** ACT-1064 (two impls for
  same-named types collapse at save; corrected by row D10's design),
  ACT-1065 (a user function named `bind` is rewritten as the primitive;
  wrong value) and ACT-1063 (`bind` as a value refused at codegen). ACT-1065
  and ACT-1063 are in scope by the user's 2026-11-17 decision (Notes).
- **Found by `qa` on 2026-11-17:** ACT-1066, a direct `quote-sexp` call
  aborts on a stale reference-count release (spec §9.11.1's own example);
  `design`(backend) attributes it to stack placement meeting the debug
  release check, and the control confirms: with `CRANELISP_NO_STACK_ALLOC=1`
  the subject exits 5 (coordinator probe, 2026-11-17). It is expected to
  close with the stack-placement retirement already in scope (row D5);
  `qa` re-attributes the action. ACT-1063's extent is
  wider than filed: partial `(bind io)` aborts on a misaligned pointer and
  `(race a)` panics the compile worker.

## Waves (Phase 4)

Source-editing agents run one at a time; only the wave's `dev` runs the suite.
Each source wave is `dev` → `review` (fresh subagent) → `qa` adequacy, with
module rows from the [delta](../tests/plan/s124-evidence-delta.md) §6 RED
before their correction. Change-set order inside a wave is the owning design's
order section ([backend §9](../design/backend/backend.md#9-s124-open-work-and-its-order),
[typecheck §12](../design/typecheck/typecheck.md#12-designed-changes-not-yet-in-source-s124),
[int §16.0](../design/int/int.md#160-open-binaryint-obligations-verified-against-source-2026-09-21),
[heap layout §5](../design/intrinsics/heap-layout.md#5-order)). A public-API
delta outside the approved packet stops the wave and returns to the user.

### W0 — Package convergence (item 6), alone on the tree

- **Agent:** `arch`, then `test` for the `tests/AGENTS.md` listing of the delta
  and the REPRO-1067 vocabulary class `qa` names.
- **Scope:** the `AGENTS.md` repository-memory convention across the 103
  memories, `standing-documents.toml`, `.codex/config.toml`; `ux` declared not
  dispatched; shared-tree guard adopted.
- **Exit:** the document checker inspects (exit 0 or 1, not 2) and its
  findings are repaired or disposed; the three `citation_drift` tests pass;
  `check_consumer.py` reports conformant.

### W1 — Evidence, with document alignment alongside

- **Agent:** `test` against the delta §6 first row, REPRO-1062 first; `qa`
  accepts the returned clause map before any correction starts.
- **Alongside (document-only, disjoint files):** `spec` and
  `design`(typecheck) settle the depth counting unit and clear appendix D's
  stale paragraph and typecheck §12 row T4's wording; `design`(backend) and
  `design`(int) take their delta §6 rows.
- **Exit:** each RED fails on its stated assertion, each control and fence
  passes, nothing in the delta §10 "Held" column is written.

### W2 — Stack-placement retirement and the census

- **Agents:** `dev`(intrinsics), then `dev`(backend).
- **Scope:** B1 with row D5 (closes ACT-1049 and ACT-1066); B2, the armed
  category census with both detection legs.
- **Exit:** REPRO-1066 green; census readings recorded for `qa`.

### W3 — Typecheck producers

- **Agent:** `dev`(typecheck).
- **Scope:** T1 (ACT-1001), T2 (ACT-0985), T3 and T4 with the depth chain
  (ACT-1034, S124-Q7), T6, and the producer obligations that do not wait on
  census output.
- **Exit:** the ACT-1034, ACT-0985 and ACT-1001 guards and the T-Q7, F-PR and
  T-DEPTH cells green; Q7-S read on the T4 tree. The type-size question, if
  still open, leaves as a named risk.

### W4 — Bind-chain rewrite

- **Agent:** `dev`(`src/`).
- **Scope:** ACT-1050 and ACT-1065 as one change-set
  ([bind-chain analysis](../design/int/bind-chain-analysis.md)).
- **Exit:** the twelve `bind_unused_heap_argument` guards and the REPRO-1065
  cells green in every mode.

### W5 — The structural close

- **Agents:** `qa` reads the census; `dev`(typecheck) for census-attributed
  corrections (row C); `arch` for the `cranelisp-types` half of rows D1 and
  D4; `dev`(backend) for B3, B4, B5; `dev`(`src/`) for the D4 display arm.
- **Gate inside the wave:** B4 starts only on a census reading of zero.
- **Exit:** the non-concrete release and retain arms do not compile; census
  zero on the suite; REPRO-1062 green; ACT-1018 re-measured.

### W6 — Backend and intrinsics changes independent of the close

- **Agents:** `dev`(intrinsics), `dev`(backend), `dev`(`src/`) for readers,
  serially, callee first.
- **Scope:** B6 (row D2, then the panic handle, item 3); B7 (R10-1, -2, -3,
  -5, -7); B8 (rows D6, D9); B9; B10 with row D8 (ACT-1038, ACT-1039); B11
  with rows R10-9 and R10-10; B12 (ACT-1063); row D11 (ACT-1033). Each
  emission-affecting change-set carries its own scoped re-baseline.
- **Exit:** the trace guards and REPRO-1063 cells green; a raise-helper bypass
  does not compile.

### W7 — Frontend and the entry carrier

- **Agents:** `arch` (types half of D3 and D10), `dev`(frontend),
  `dev`(typecheck) for T5 and T7, `dev`(`src/`) for the consumers.
- **Scope:** row D3 with ACT-0997, ACT-1055, ACT-1056; ACT-1057; ACT-1059;
  ACT-1064; frontend audit R1–R5; S124-Q2, Q3, Q4.
- **Exit:** their guards and delta §9.5 cells green.

### W8 — Session and batch entry

- **Agents:** `arch` (types half of D7), `dev`(`src/`), `dev`(backend) for the
  schema constant and the `dependency_hashes` rustdoc.
- **Scope:** ACT-1052; row D7 with ACT-0953; ACT-1016; ACT-0973; ACT-1036 with
  row D12, S124-Q8 and Q9 as one change-set; ACT-1061; ACT-1060.
- **Exit:** their guards and cells green in every mode.

### W9 — Baseline format and the integrated gate

- **Scope:** rows K11-b, -c, -d land with the waves that touch their crates;
  K11-a lands here, alone and last. Then one fresh build of the final tree:
  full suite, census, document checker, `public-api.txt` regenerated once and
  compared with the packet, `review` of the integrated diff, `qa` adequacy and
  the traceability band.
- **Exit (the settling target):** zero failures, or each remaining RED
  carried on recorded evidence; any baseline line outside the packet returns
  to the user.

### Carried with a committed reproduction, not corrected

The third-deferral groups and ACT-1067 (Notes).

## Dispatch log

| Wave | Agent | Surface | Model | Effort | Harness |
|---|---|---|---|---|---|
| Phase 2 | `arch` | S124 scope, cross-crate | claude-fable-5-2 | medium | primary (native subagent) |
| Phase 2 | `arch` | Rust context standard evaluation | claude-fable-5-2 | medium | primary (native subagent) |
| Phase 3 | `spec` | `spec/`, `repl/` — S124 rulings | gpt-6.1-sol | medium | cross-harness (`codex_role.py`) |
| Phase 3 | `arch` | `design/arch/` contracts | claude-fable-5-2 | medium | primary (native subagent) |
| Phase 3 | `qa` | intake, attribution, reproduction allocation | claude-fable-5-2 | medium | primary (native subagent) |
| Phase 3 | `design` | backend | claude-opus-5-5 | medium | primary (native subagent) |
| Phase 3 | `design` | frontend | claude-opus-5-5 | medium | primary (native subagent) |
| Phase 3 | `spec` | REPL §1.5, §12.1.1 — S124-Q1 | gpt-6.1-sol | medium | cross-harness (`codex_role.py`) |
| Phase 3 | `design` | `src/` (`design/int/`) | claude-opus-5-5 | medium | primary (native subagent) |
| Phase 3 | `design` | intrinsics | claude-opus-5-5 | medium | primary (native subagent) |
| Phase 3 | `arch` | answers to backend and frontend design questions | claude-fable-5-2 | medium | primary (native subagent) |
| Phase 3 | `design` | backend (revision) | claude-opus-5-5 | medium | primary (native subagent) |
| Phase 3 | `design` | typecheck | claude-opus-5-5 | medium | primary (native subagent) |
| Phase 3 | `spec` | frame seven open questions (appendix D) | gpt-6.1-sol | medium | cross-harness (`codex_role.py`) |
| Phase 3 | `arch` | remaining gate rows (R10-9, T7, D8 final) | claude-fable-5-2 | medium | primary (native subagent) |
| Phase 3 | `qa` | evidence plan, readiness, two observations | claude-fable-5-2 | medium | primary (native subagent) |
| Phase 3 | `design` | typecheck — confirm row D10 | claude-opus-5-5 | medium | primary (native subagent) |
| Phase 3 | `design` | `src/` — confirm row D10, alias collision | claude-opus-5-5 | medium | primary (native subagent) |
| Phase 3 | `arch` | finalise row D10 | claude-fable-5-2 | medium | primary (native subagent) |
| Phase 3 | `design` | `src/` — ACT-1050 placement | claude-opus-5-5 | medium | primary (native subagent) |
| Phase 3 | `spec` | §3.10 — S124-Q7 re-ruling; frame Q9 | gpt-6.1-sol | medium | cross-harness (`codex_role.py`) |
| Phase 3 | `design` | typecheck — conform to Q7-B | claude-opus-5-5 | medium | primary (native subagent) |
| Phase 3 | `qa` | evidence delta — Q7-B, D12, ACT-1066 | claude-fable-5-2 | medium | primary (native subagent) |
| Phase 3 | `spec` | depth limit, reporting turn, Q9 closed | gpt-6.1-sol | medium | cross-harness (`codex_role.py`) |
| Phase 3 | `design` | typecheck — depth limit unit | claude-opus-5-5 | medium | primary (native subagent) |
| Phase 3 | `qa` | closing pass, traceability band, ACT-1067 | claude-fable-5-2 | medium | primary (native subagent) |

## Notes

- 2026-11-16: opening suite run and package convergence recorded above.
- **W0 landed (`ae011366`):** 29 tracked memories renamed to `AGENTS.md`
  (the scope's "103" counted ignored copies); `.codex/config.toml` deleted;
  shared-tree guard hooked. The document checker inspects and reports about
  590 pre-existing findings, 577 of class ignored-path; their disposal is
  with the user, so W0's checker exit is open and one `citation_drift` test
  stays RED.
- **W1 accepted by `qa` (`b630252b`):** suite 7,423 run, 267 failed — 44
  opening guards, 216 new cells RED on their assertion, 6 RED on setup
  (returned to `test` by wave, delta §14), one document-gate check, no
  regression. FIXME 0934 and ACT-0975 closed on passing fences.
- **ACT-1068 filed, unscheduled:** saving a session omits every
  multi-signature function from the module file (data loss; predates S124).
  Scheduling is with the user.
- **W2 accepted by `qa` (`cc5b11db`):** row D5 (`b0f48914`, `8f44040e`),
  the census (`1a3ab46e`, frame record `3ca6086e`). Row D1 (B3) was pulled
  forward from W5 and landed (`3deee350`, cardinality fix `24c42430`).
- **W3 accepted by `qa` (`688bf2c0`):** T1–T4 and T6 (`a49bc340` to
  `616c0d0a`); suite 190 failed. Review findings open: ACT-1072 (sibling
  members overcount depth; introduced by T4, fixed in this sprint), three
  weak module rows returned to `dev`(typecheck).
- **W4 accepted by `qa` (`1db7b1d8`):** ACT-1050 resolved, ACT-1065 open only
  for T-1065-d (W7), ACT-1060 met (`32e434dc`, `8667a868`). Suite 7,597 run,
  194 failed: 26 opening guards, 166 S124 cells RED on their assertion, two
  maintenance checks, nothing unattributed (delta §14.1).
- **CEN-4 met after W4:** zero census records from any program in all four
  partitions, each with frames; the two remaining records are backend module
  fixtures. B4 is licensed.
- **W5 accepted by `qa` (`7697cad3`):** B4 (`152a0def`, `1d965ed5`) deletes
  the non-concrete arms; B5 / row D4 (`441e31ea`) makes one-word
  single-constructor values heap values in backend and display; cache schema
  32. Census at HEAD: 225,515 frames, zero records from programs. Suite
  7,609 run, 192 failed, nothing unattributed (delta §14). ACT-1069 and
  ACT-1072 closed. Row C: nothing owed. REPRO-1062-e/-f stay RED (no
  correction scheduled). ACT-1018 re-measured at 2.
- **Filed at W5 exit:** ACT-1076 (trait dispatch selects on the first
  argument, not the `self` position; crash, wrong value or refusal, including
  two spec §7.1.4 examples; predates S124), ACT-1077 (a same-named local
  leaves an unrelated bind chain sequential).
- **Awaiting the user's gate:** `CallableOrigin::TraitMethod` carrying its
  member (`cranelisp-types`; raised by review of `951622cf`, half-fixed in
  `240b3a8a`). Not started.
- **Filed during Phase 5, scheduling with the user unless stated:** ACT-1068
  (save omits multi-signature functions), ACT-1069 (trace formats a one-word
  ADT as a pointer; fixed by D4/B5 in W5), ACT-1070 (JIT direct call out of
  range), ACT-1071 (imported parametric instance calls a multi-signature
  function through an empty slot), ACT-1073 (refused cluster leaves an
  implementation shell registered), ACT-1074 (implementation body cannot
  call a same-cluster multi-signature function), ACT-1075 (call selecting a
  polymorphic function from a multi-candidate spelling fails at codegen).
  ACT-1062 widened to the trace and display readers; ACT-1039 widened to
  cached traced callees.
- **Queued for the user:** ignored-path disposal; category of refusals about
  an existing `main`; whether method-level re-entry counts toward depth; the
  T-D7-b overload-leg residual; ACT-1018 carry on 2 blocks; scheduling of
  ACT-1068, ACT-1070, ACT-1071, ACT-1073, ACT-1074, ACT-1075 and ACT-1062's
  two readers; duplicate same-key implementations in one cluster.

### User rulings on the Phase 2 decisions, 2026-11-16

Numbering follows the [review](s124-architecture-review.md) §8 as presented.

- **Import/export carrier (review §8.3): agreed.** One entry type shared by
  imports and exports, carrying the bound local name. Implemented by row D3
  with ACT-0997, ACT-1055, ACT-1056 and audit R2 in the frontend/typecheck
  wave; D3 itself remains at the API gate.
- **Tracing under parallel evaluation (review §8.4): deterministic for now.**
  Evaluation inside a trace is strict for its whole dynamic extent; recording
  parallel work is revisited when a need arises. Implemented with ACT-1038;
  `spec` confirms §4.12.2 states it in Phase 3.
- **Package adoption (review §8.5): agreed.** Adopt `AGENTS.md` and the
  shared-tree guard; Rust context standard stays unadopted; Rust build
  standard declined for now; spec traceability held for `qa` and `spec`;
  `ux` declared not dispatched. All land in W0. The user also asked for a
  deeper evaluation of the Rust context standard's impact on cranelisp —
  dispatched to `arch` in Phase 2.
- **Interim ownership-ABI gate (review §8.1): removed.** REPL §18.1.2 and its
  diagnostic are retired; inference, `ModeSummary` and the stored summaries
  stay for a release tier. `spec` scribes the removal in Phase 3; the root
  gate and row D7 land in the Principle 27 wave; `qa` allocates the
  mode-change redefinition cell as the premise's falsifier.
- **Unlanded S123 rows (review §8.6): land them in S124.** Rows K11-a to
  K11-d and R10-1 to R10-8 of the [S123 packet](s123-api-packet.md) Part B,
  approved in S123. R10-4 and R10-8 are rows D2 and D6. R10-1/2/3/5/6/7 land
  in one backend wave; K11-b/c/d with the crates they touch; K11-a (the
  auto-trait baseline format) as its own mechanical change-set last. R10-9
  waits on its design listing.
- **Rust context standard: stays unadopted**, on `arch`'s
  [evaluation](s124-rust-context-standard-evaluation.md). The dependency-edge
  check is taken and scheduled after S124:
  [ACT-1058](actions/ACT-1058-measure-declared-crate-dependency-edges.md).
- **Public-API gate: rows D1–D7 approved** as written in the
  [packet](s124-api-packet.md). D8 returns when its designs list it.
- **Row D9 approved (2026-11-16):** remove the backend
  `CacheStale::SiblingSlotOutOfRange` variant; it lands with D6.
- **S124-Q1 ruled (2026-11-16):** REPL §1.5 drops the claim that the value is
  stored flattened and keeps its display guarantees as ordinary requirements;
  language §12.1.1's description follows. `spec` scribes it in Phase 3.
- **Rows D8, R10-9, D10 and D11 approved (2026-11-17)** as written in the
  [packet](s124-api-packet.md) Part B. R10-9 supersedes S123 row R10-6. D10's
  schema bump rides D3's.
- **S124-Q2 to Q6 ruled (2026-11-17)**, each as candidate recorded in
  [appendix D](../spec/appendix-d-open-questions.md); `spec` scribes them.
  - **Q2 — A:** a macro rest parameter binds a symbol only; `[& [a b]]` is
    rejected.
  - **Q3 — A:** a macro return mismatch is located at the offending clause
    body.
  - **Q4 — B:** an import alias and an export mount sharing a spelling are
    refused only when their targets differ; equal targets form one public
    route. An empty export list is a definite no-op.
  - **Q5 — A:** persistence moves a redefined function after a macro it newly
    depends on; macro availability stays source-ordered.
  - **Q6 — A:** a watched save completed by a turn's own `/sh` is rebuilt and
    reported before the next prompt. ACT-1061 is therefore a defect in S124
    scope.
- **Row R10-10 approved (2026-11-17)** as written in the
  [packet](s124-api-packet.md): the backend and the binary read the existing
  `vec_runtime` offset constants.
- **S124-Q7 ruled B (2026-11-17), superseding an A ruling of the same day:**
  a trait dispatch from an implementation's body to that implementation at
  another instantiation is an ordinary dispatch, whether direct, through a
  helper or through another implementation. A program whose instantiation of
  implementations does not terminate is a type error. The rule for functions
  is unchanged. No impl-body check is added.
- **S124-Q8 ruled B (2026-11-17):** a "no `main`" refusal names the entry
  file and the missing `main` with no form span, as a stated exception to
  REPL §5.5.
- **Instantiation depth limit ruled (2026-11-17):** spec §3.10 states a limit
  of at least 64 on a chain of implementation instantiations, refused as a
  type error; a growing implementation is accepted when declared and refused
  when an instance is demanded.
- **S124-Q9 ruled no (2026-11-17):** a trait method named `main` does not
  define `main`; a multi-arity `main` stays refused.
- **Type-size limit: accepted as a named risk (user, 2026-11-17).** A
  re-entry whose type doubles each step exhausts time or memory before depth
  64 (by `design`(typecheck)'s analysis): a hang on a program the spec
  refuses, never a miscompile. No second limit is added; F-PR-3 is not
  written. Falsifier: a non-contrived program that hits it.
- **Open inside the increment: depth counting unit.** `qa` reads the design
  as counting method instances, which could refuse a chain shallower than the
  spec floor when members call each other. `spec` and `design`(typecheck)
  settle it in Phase 4; appendix D's Q7 gap paragraph is stale.
- **ACT-1067 carried (user, 2026-11-17):** an expression nested about 56
  forms deep overflows the compile worker's stack (exit 134). Its
  reproduction lands in W1 and stays RED past S124.
- **ACT-1065 and ACT-1063 are in S124 scope (2026-11-17).** ACT-1063 returns
  to the user as a named carry if attribution shows its correction crosses
  more than one surface.
- **Row D12 approved (2026-11-17)** as written in the
  [packet](s124-api-packet.md), with the refusal keeping its error category:
  the S124-Q8 exception lifts the location only (REPL §5.1 item 1).
- **Third deferrals confirmed, with reproductions owed this sprint.** The
  runtime-concurrency (ACT-0977, ACT-0975, ACT-0981, FIXME 0934), persistence
  (ACT-1005, ACT-0994), diagnostics and discovery (FIXME 0915, ACT-0986) and
  run-dependent (FIXME 0694, ACT-1025) groups carry past S124. For each that
  is a defect, `qa` allocates and `test` commits a minimal failing
  reproduction with its control in the S124 evidence wave; `qa` decides which
  are defects and reports any that cannot be reproduced.
