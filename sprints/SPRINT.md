# Sprint 124: Type concreteness at codegen

**Status**: PHASE 4 — WAVE ORGANIZATION

**Goal**: Make every type that reaches codegen concrete — census, typecheck
producer obligations, backend structural close — and clear the crash-class and
frontend carries behind it.

**Audit**: selected at Phase 4 from the [rotation](METHOD.md#27-rolling-whole-context-audit).

## Phase approvals

| Transition | Checkpoint presented | User approval | State |
|---|---|---|---|
| Start → Phase 1 | "let's plan the next sprint" | 2026-11-16 | approved |
| Phase 1 → Phase 2 | scope draft with seven included items | 2026-11-16, "advance to phase 2" | approved |
| Phase 2 → Phase 3 | `arch` review, API packet D1–D8, six decisions | 2026-11-16, "advance to phase 3" | approved |
| Phase 3 → Phase 4 | designs, packet rows D1–D12/R10-9/R10-10, S124-Q2..Q9, `qa` readiness | 2026-11-17, "approved to advance" | approved |
| Phase 4 → Phase 5 | — | — | pending |
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
  §12.1.1 after flattening. S124-Q2..Q9 ruled 2026-11-17 (Notes). Open with the user: a type-size
  limit for instantiation (Notes).
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

## Notes

- 2026-11-16: opening suite run and package convergence recorded above.

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
- **Open with the user: type-size limit.** By `design`(typecheck)'s analysis a
  re-entry whose type doubles each step exhausts time or memory before depth
  64. Unanswered at the typecheck wave's exit, it is a named unprotected risk
  (a hang on a non-terminating program, never a miscompile).
- **Open inside the increment: depth counting unit.** `qa` reads the design
  as counting method instances, which could refuse a chain shallower than the
  spec floor when members call each other. `spec` and `design`(typecheck)
  settle it in Phase 4; appendix D's Q7 gap paragraph is stale.
- **ACT-1067 filed (2026-11-17), unscheduled:** an expression nested about 56
  forms deep overflows the compile worker's stack (exit 134). Scope decision
  goes to the user with the wave plan.
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
