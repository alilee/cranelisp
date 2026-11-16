# Sprint 123: One ownership answer, contained panics, agent on by default

**Status**: PHASE 5 LANGUAGE — W3

**Goal**: Decide the ownership stratum's shape on a measured number and fix
the observed memory-unsafe faults under it; make a callee's runtime panic a
contained, reported panic; ship the REPL agent on by default with
file-supplied environment; refresh the user-facing outputs.

**Audit**: `cranelisp-frontend` (proposed at Phase 4: longest unassessed, last
whole-context pass S113; little S123 change, so the assessment reads a stable
context; ACT-0969's frontend row is its input). Dispatched read-only in
Phase 6a.

**Settling target** (observable at acceptance, on a fresh build of the final
tree):

- the option-2 measurement is recorded and the user has decided option 2;
- the ACT-1030 use-after-free guard and the ACT-1040 panic cells pass in every
  mode, with their controls;
- a plain `cargo build` REPL prints the agent banner, and a project `.env`
  supplies a `CRANELISP_*` setting;
- the modules and macros guides exist and the suite executes `user/` samples.

## Phase approvals

| Transition | Checkpoint presented | User approval | State |
|---|---|---|---|
| Start → Phase 1 | Post-S122 status and the REPL-agent default question | 2026-11-15, conversation: "yes build with default as agent on" in reply to scoping the agent default into S123 | approved |
| Phase 1 → Phase 2 | Phase 1 scope, carries, size and the Phase 2 `arch` proposal | 2026-11-15, conversation: "yes. A" | approved |
| Phase 2 → Phase 3 | Architecture review, carry triage, both option-2 pre-checks, and the Phase 3 proposal | 2026-11-15, conversation: "accept the panics / accept the scope changes. approved to move to phase 3" | approved |
| Phase 3 → Phase 4 | Designs, API packet P11–P13, QA readiness with one gap, decisions 1–10 and the Phase 4 proposal | 2026-11-15, conversation: "approved" | approved |
| Phase 4 → Phase 5 | Wave plan W0–W5, audit choice, and the checkpoint commit | 2026-11-15, conversation: "yes"; checkpoint commit `b35bfb87` | approved |
| Phase 5 → Phase 6a | — | — | pending |

## Scope

Sources: the [roadmap](ROADMAP.md#next-sprint--s123), the
[backend S122 audit](../audits/cranelisp-backend-s122.md), and the S122
[carry list](archive/sprint-122.md) with its
[package table](../tests/plan/s122-evidence-delta.md). Every carried filing
still exists and its `refers_to` sources resolve (inventory 2026-11-15).

### Included: the ownership decision and the faults under it

Dependency order, each step gating the next:

1. **Option-2 measurement** (audit R1). The S119 method in
   [PLAN.md](../tests/plan/PLAN.md) — the all-Owned toggle against current
   emission on the exemplar warm solve, the contention benchmark and the full
   suite — with `design`(backend) enumerating the structural elisions the
   toggle leaves in place, so the number is not only a lower bound. Owners:
   `qa` allocates, `arch` owns the
   [option paper](../design/arch/ownership-stratum-options.md).
2. **User decision on option 2**, presented with the number.
3. **ACT-1031 resumes under the chosen shape**: the ACT-1030 use-after-free,
   the ACT-1029 alias-map lead and leads L2–L7, L9, L10; the ACT-1026 and
   ACT-1028 leaks sit in the same machinery. Audit R7 and R8 follow the
   decision.
4. **Evidence that can see this class** (audit R3, R4, R11): the batched lead
   measurement armed with `CRANELISP_RC_DEC_CHECK`, generator axes for tail
   arguments, COW steps, alias shadowing and consume position, and the record
   repairs — `qa`, then `test`.

### Included: contained panics

- [ACT-1040](actions/ACT-1040-panic-sentinel-reaches-heap-consumer-intake.md):
  a callee's panic sentinel reaches a heap consumer, which dies with SIGSEGV.
- [ACT-1042](actions/ACT-1042-callee-panic-with-scalar-result-resumes-caller-intake.md):
  with a scalar result the caller resumes with `0` — a loop can hang, and a
  later panic replaces the first message.
- ACT-1041 (`--run` reports an uncaught panic as a codegen error) and the
  panic-prefix wording question for `spec`.
- `design`(backend) costed the options in
  [s122-closure §10](../design/backend/s122-closure.md#10-act-1040--panic-propagation-proposal).
  User ruling, 2026-11-15: option A is in scope — it closes ACT-1040 and
  ACT-1042. Its new intrinsic takes the inter-crate public-API user gate;
  the mechanism stays `design`'s.

### Included: two high-harm REPL carries

- [ACT-1047](actions/ACT-1047-never-recorded-backing-file-overwritten-intake.md):
  a `user.cl` created after the session started is overwritten (data loss).
- [ACT-1035](actions/ACT-1035-repl-concrete-impl-crashes-after-later-parametric-impl-intake.md):
  the REPL crashes calling a concrete impl after a later parametric impl.

### Included: backend audit housekeeping

- R5, R6: backend design status sweep and crate-memory repairs —
  `design`(backend), `dev`(backend).
- R9: spec §12.1 descriptive layouts — `spec`, wording approved by the user.
- R12, applied at Phase 2 entry: ACT-0969's backend row is struck (the audit
  re-judged it; `fn_compiler.rs` 4,824 and `apply.rs` 2,977 lines at
  `f747990f`). ACT-0964 items 1–2 stay with `design`(backend) in this sprint.
- At close: move the four S122 working files from `sprints/` to the archive,
  with the link repairs their citing owners make (`arch`, `qa`, FIXME 0907,
  ACT-0959).

### Included: REPL agent on by default

User rulings, 2026-11-15:

- The default build compiles the embedded agent in.
- A REPL session enables the agent unless `--no-agent` is given.
- The agent activates only when `CRANELISP_AGENT_PROVIDER` is set explicitly;
  an ambient `ANTHROPIC_API_KEY` alone leaves it dormant. Without an explicit
  provider, `/ask` gives the dormant notice and that notice names the variable.

Rationale for the third ruling: many shells carry `ANTHROPIC_API_KEY` for
other tools, so with the agent on by default, the current fallback to
Anthropic (`src/agent/provider.rs:34`) would send REPL source off the machine
without a Cranelisp-specific choice.

Further user rulings, 2026-11-15:

- Every environment variable the compiler reads — the agent's settings and
  every `CRANELISP_*` switch, including diagnostic and runtime gates — is also
  supplied from a project `.env` and from a user-level configuration file
  under `~/.config/cranelisp/`, read the same way for all of them.
- The repository ignores `.env` files (applied to `.gitignore` 2026-11-15).
- REPL startup prints one banner line declaring the agent's state.

- Precedence is conventional: the process environment wins over the project
  `.env`, which wins over the user configuration file.
- The banner states the agent's state (active, dormant or off) and, when
  active, its provider and model. It does not report which file supplied a
  setting, and startup does not list the files loaded.

Open for the owning roles: whether switches the compiler reads repeatedly
during a session (for example `CRANELISP_CODEGEN_DUMP`, noted in the backend
audit) become values read once at startup (`arch`, `design`); and how the
suite keeps a developer's own `.env` or user file from changing test results
(`qa`).

These rulings supersede:

- `repl/spec/00-cli-invocation.md` §0.6.1 "agent off" default and the §0.6
  flag table, with the agent spec's opt-in-twice text — `spec`;
- `user/cli-reference.md`, which must agree with the CLI spec's flag table — `docs`;
- `design/int/agent.md` §6.4, which keeps the agent out of default builds and
  the default suite — `arch`, then `design`.

Open for the owning roles, not decided here: how the feature-off error rules
for `--agent` and `--yes` stay evidenced once the feature-off binary is no
longer the default (`qa`); the build and suite cost of compiling the agent
dependencies by default (`arch`).

### Included: user-facing carries

User ruling, 2026-11-15, after a fresh run of the user-facing outputs (all 13
showcase demos exit 0; exemplar `user.cl` exits 0 and `tests.cl` 40; examples
pass; the only exemplar failure is the ACT-1018 guard):

- modules and macros guides under `user/guide/` — `docs`;
- a session-lock and live-reload REPL demo, carried from S122 — `test`, with
  `spec` where the demo needs `repl/spec.md` behaviour stated;
- code samples in `user/` executed by the suite, so a guide that stops
  matching the compiler fails a check — `qa` decides the evidence form, `test`
  builds it.

Dependent on the agent work above: the startup banner changes demo
transcripts, the getting-started walkthrough and the CLI reference, so those
passes follow it.

### Excluded and carried to S124

Each was first deferred in S122, so carrying it again is its second deferral:
the [method](METHOD.md)'s second-deferral escalation trigger requires one `qa`/`arch` triage that
explains structurally why it keeps deferring before the user confirms the
carry. That triage runs once, over the whole set, in Phase 2.

- K5 names read by their written spelling (ACT-0997, ACT-1001, ACT-0985,
  ACT-0987, ACT-1003) — needs the `ImportNames` public-API gate.
- K6 platform admission (ACT-0973, ACT-0979, FIXME 0933) — needs a spec answer
  and a naming decision.
- K7 runtime concurrency (ACT-0977, ACT-0975, ACT-0981, FIXME 0934); K8
  persistence leads (ACT-1005, ACT-0994); K9 diagnostics and discovery
  (FIXME 0915, ACT-0986); K10 run-dependent residuals (FIXME 0694, ACT-1025),
  open since S114, so its count may already require §2.4.5 sign-off; K11
  assurance maintenance and the public-API baseline batch.
- ACT-1015, 1016, 1017, 1020, 1022, 1032, 1033, 1034, 1036, 1038, 1039 and
  1048.
- ACT-1018 (warm Sudoku solve leaves 51 allocations) is re-measured after the
  ownership work rather than worked directly.
- Audit R10 (public items with no consumer) — public-API gate; with K11's
  batch.
- LLVM, by user direction; ACT-0962 and ACT-0960, the roadmap's later
  increments.

### Size and order

Large: S122's comparable ownership work ran three weeks. The ownership steps
are sequential and gate on a user decision mid-sprint. The agent and
environment work and the user-facing carries are independent of the backend
and of each other, so they run alongside it; demo and documentation refreshes
follow the banner. If the ownership chain proves unreachable, it narrows to
steps 1–2 plus the ACT-1030 fix, never by dropping the measurement.

### External operations

None beyond the repository: no push, no deployment, no live model calls (the
agent lane uses the stub provider). Commits only at user-approved checkpoints.

## Phase 2 proposal

`arch` reviews, read-only, and returns one report:

- reversing `design/int/agent.md` §6.4 (agent in the default build, default
  suite cost, how the feature-off rules stay evidenced);
- environment-file loading as a cross-crate fact: `CRANELISP_*` readers live
  in `src/`, the backend and intrinsics, so the load must precede every
  reader; whether linked executables also read the files; whether switches
  read repeatedly become startup values;
- the option-2 measurement's framing in the option paper, and the panic
  options' gate (A's new intrinsic);
- the second-deferral triage over the carry set, with `qa`.

Exit: the architecture report and triage come back to the user; Phase 3 needs
separate approval.

## Dispatch log

| Phase | Agent | Surface | Model | Effort | Harness | Outcome |
|---|---|---|---|---|---|---|
| 2 | `arch` | architecture review → `sprints/s123-architecture-review.md` | claude-opus-5-5 | high | primary (Claude Code subagent) | delivered 2026-11-15; one public-API delta proposed; checker exit 0 |
| 2 | `qa` | second-deferral carry triage → `tests/plan/s123-carry-triage.md` | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; probe binary sha256 `aa01c46b…` at `f747990f` |
| 2 | `qa` | option-2 discriminator 1 → triage §7 | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; all three faults survive the toggle |
| 2 | `qa` | option-2 discriminator 2 → triage §8 | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; exemplar 0 in-place of 11,593 updates |
| 3 | `design` | backend, intrinsics, int (native subagent) | gpt-6.1-sol (stale session definition) | medium | primary (Claude Code subagent) | failed at start: model not found; no files touched |
| 3 | `design` | backend → `design/backend/` | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-15; `uniform-counting.md`, `backend.md` §7; 4 user questions |
| 3 | `design` | intrinsics → `design/intrinsics/` | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-15; `process-lifecycle.md`; API delta for `arch`; 3 user questions |
| 3 | `design` | int → `design/int/` | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-15; `environment.md`, `int.md` §16.0; ACT-1035 mechanism probed |
| 3 | `arch` | option paper, positions, `sprints/s123-api-packet.md` | claude-opus-5-5 | high | primary (Claude Code subagent) | delivered 2026-11-15; `s123-panics-and-environment.md`; packet P1–P10, B1–B3 |
| 3 | `spec` | record the Phase 3 rulings; retire answered Appendix D questions | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; session `e99fb972`; Q1–Q11 retired; checker exit 0 |
| 3 | `design` | int: align to opaque switch capture, restarting test child, broken-symbol refusal | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-15; new deltas in `int.md` §16.0; checker exit 0 |
| 3 | `arch` | packet completion, retired-question references, redefinition receipt | claude-opus-5-5 | high | primary (Claude Code subagent) | delivered 2026-11-15; P11–P13 need the gate; checker exit 0 |
| 3 | `qa` | readiness check and S123 evidence delta | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; ready with one blocking gap (stdlib runner process launch) |
| 3 | `design` | intrinsics: retire question refs, P11, align to evidence delta | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-15; dispatch-fault report unprefixed; checker exit 0 |
| 3 | `design` | int: P12 names, receipt retirement, align to evidence delta | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-15; checker exit 0; one `qa` citation slip and one P12 reading for `arch` |
| 5 W0 | `test` | M-1, K-1 to K-5, `tests/CLAUDE.md` link | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; session `db4fe4ea`; 9 REDs, controls pass; evidence `.local/s123-w0/test-evidence.md` |
| 5 W0 | `qa` | accept W0 test evidence; classify green faces | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; returned C1–C4 (`.local/s123-w0/qa-return.md`); ACT-1016 and ACT-1017 remeasured |
| 5 W0 | `test` | corrections C1–C4 | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; session `d8335a43`; 3 REDs, 6 passes; `.local/s123-w0/test-evidence-2.md` |
| 5 W0 | `qa` | accept corrected cells C1–C4 | claude-opus-5-5 | medium | primary (Claude Code subagent, resumed) | delivered 2026-11-15; all accepted; 4 REDs trace to ACT-0997 and ACT-1017 |
| 5 W0 | `dev` | `src/`: ACT-1025 (M-2) | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; fixture wait plus scheduler seam test; 154 worker and scheduler tests pass |
| 5 W0 | `review` | W0 diff under `tests/` and `src/` | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; session `669db68f`; one required finding predating W0 (stdlib supplied to four test files) |
| 5 W0 | `qa` | close-out: ACT-1025, startup residual, review finding | claude-opus-5-5 | medium | primary (Claude Code subagent, resumed) | delivered 2026-11-15; ACT-1025 resolved; residual to `design`(int); finding becomes M-7 in W1 |
| 5 W1 | `test` | M-7; P-1 to P-12, P-18, P-19, T-1 to T-5, T-7; C-1, C-2, C-3, C-5, C-9 | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; session `218eb67a`; 110 cases, 64 pass, 46 RED; stopped on P-3, P-7, P-10 |
| 5 W1 | `qa` | accept W1 test evidence; rule P-3, P-7, P-10 and the startup row | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; most accepted; returned P-4 sparks, P-7, P-3, P-10, renames (`.local/s123-w1/qa-return.md`) |
| 5 W1 | `test` | W1 corrections 1–5 | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; session `1537f6f7`; 9 pass, 17 RED, 2 unbuilt; P-4 twins spawn 2 |
| 5 W1 | `qa` | accept corrections; P-7 `--test` leg; grammar citation; re-rule M-2 | claude-opus-5-5 | medium | primary (Claude Code subagent, resumed) | delivered 2026-11-15; accepted except P-7 stderr rule; `--test` leg narrowed; M-2 restated |
| 5 W1 | `test` | P-7 stderr rule; evidence-record fix | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; session `0524b973`; batch cells pass, two REPL REDs, as `qa` pre-accepted |
| 5 W1 | `dev` | intrinsics: terminator, catalog derivation, P1–P7, P11 | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; 364 crate tests pass; `public-api.txt` +4/−28 equals packet; root crate does not compile until `src/` step |
| 5 W1 | `design` | intrinsics: `sleep_pollfn` catalog row; runtime-defect report wording | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-15; poll-leaf constructor for the row; defect wording confirmed; `public-api.txt` +0 |
| 5 W1 | `dev` | backend: single raise helper; removable sentinel code | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; 637 backend tests pass; `public-api.txt` +0; census graded measured |
| 5 W1 | `dev` | intrinsics follow-up: poll-leaf constructor, defect-report test | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; 369 tests pass; `public-api.txt` +0; reported intermittent ivar heap corruption |
| 5 W1 | `qa` | attribute ivar test heap corruption | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; pre-existing test race (baseline 24/20,000 aborts, W1 16/22,000); product correct |
| 5 W1 | `dev` | intrinsics: ivar test frees only after the worker releases | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; 0 aborts in 25,000 isolated runs; 369 crate tests pass |
| 5 W1 | `dev` | types: P9 | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; 292 crate tests pass; `public-api.txt` −4 as P9 states |
| 5 W1 | `dev` | `src/`: hosts, ACT-1041, test supervisor (P12), ACT-1017 prefix, startup settle | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; root compiles; 1,056 root tests pass; W1 e2e cells green except named waits |
| 5 W1 | `dev` | primitives: `checked-quot`; dead sentinel returns | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; 108 tests pass; `checked_quot_*` e2e green; `public-api.txt` +0; trusted-base census 19/20 → 18/19 |
| 5 W1 | `arch` | ruling: primitives trusted-base census change | claude-opus-5-5 | high | primary (Claude Code subagent) | delivered 2026-11-15; within P6 and the `checked-quot` approval; no user gate; report at the Phase 5 checkpoint |
| 5 W1 | `dev` | platform: retire or re-point the `DispatchError` test; stale rustdoc | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; test retired (no error value remains); 87 tests pass; `public-api.txt` +0 |
| 5 W1 | `dev` | stdlib: runner without isolation (T-8); `catch-runtime-error` users | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; conformance 17/17; T-8 7/7; `testing.runner` public surface changed |
| 5 W1 | `dev` | exemplar: panic-free request paths | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; `safe-handle` and the 500 page removed; one guarded `get`; `tests.cl` now exits 41; exemplar tests pass |
| 5 W1 | `dev` | `src/`: `--test` fail reason carries the last stderr line | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; row 9 failing then passing; 16 test-runner e2e cells green |
| 5 W1 | `training` | `examples/` without `catch-runtime-error` | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; session `2744c58e`; example 11 teaches `checked-quot` (exit 69 → 71); 32 and 38 updated |
| 5 W1 | `spec` | `Int.MIN / -1` wraps; S123-Q13 messages | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15 |
| 5 W1 | `test` | `MIN / -1` re-point; four stale cells; example 11 re-pin; golden CLIF; dispatch prose | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; session `77c7c41c`; 12 pass, `MIN / -1` RED; 16 goldens re-baselined, function-ID and GOT-offset shifts recorded separately |
| 5 W1 | `dev` | backend: `Int.MIN / -1` wraps in `emit_checked_div` | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; branch-free wrap; 643 backend tests pass; e2e direct-call cell green |
| 5 W1 | `test` | value-use `MIN / -1` cell; five golden re-captures | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; session `d8ada60d`; value-use cell RED in all three modes; goldens match the lowering change |
| 5 W1 | `dev` | primitives: `div_i64` wraps `Int.MIN / -1` | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; row failing then passing; four division e2e cells green in all modes; `public-api.txt` +0 |
| 5 W1 | `review` ×9 | intrinsics, backend, primitives, types, platform, `src/`, `stdlib/`, `exemplar/`, `examples/` | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; findings in `.local/s123-w1/review/`; required: src R1, intrinsics I1, platform 1, primitives 1 |
| 5 W1 | `dev` | `src/`: review R1–R3 | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; R1 forged-record reproduction now reports 1 passed; R2 0 duplicates; 160 targeted tests pass |
| 5 W1 | `dev` | intrinsics: review I1 (one-line reports), I2 | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; `OneLine` escaping; 375 crate tests pass; `public-api.txt` +0 |
| 5 W1 | `dev` | primitives: guidance for the wrapping division | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; one stale `CLAUDE.md` bullet fixed |
| 5 W1 | `dev` | platform: thunk and `EffectOutcome` rustdoc | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; 87 tests pass; docs build without warnings |
| 5 W1 | `dev` | stdlib: runner batch-availability guidance | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; the module is REPL-only, verified in all modes |
| 5 W1 | `qa` | W1 adequacy: full suite, filings, band | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; 6,738 run, 6,711 pass, 27 fail (23 filed guards, 4 W1 consequences, 0 regressions); adequate with residuals |
| 5 W1 | `test` | re-pin two CLIF witnesses; delete the obsolete 0889 macro cell and ACT-0976 cell | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; session `0b92b93f`; 10/10 focused; `qa` repointed the two citations |
| 5 W2 | `test` | W1 `fixed=` stamps (`f5822487`); U-1 to U-5 test-first | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; session `11321ff2`; 13 stamps; 69 cells, 40 pass, 29 RED; generator 288 legs; stopped on U-3/L4 |
| 5 W2 | `qa` | accept U-1 to U-5; attribute U-3/L4 control fault | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; all accepted except L4 (misbuilt control); L4 is the predicted over-release; ACT-1040 count is seven |
| 5 W2 | `test` | U-3/L4 control and subject cells | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; session `e4c43b6c`; faces match `qa`'s prediction (controls balance, subjects stop armed) |
| 5 W2 | `dev` | backend: U′ cutover (U1, U2), ACT-0964 hardening | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; every W2 cell green (72 e2e, 501 module); wrappers 999/999 in place; backend net about −10,000 lines; `public-api.txt` +0 |
| 5 W2 | `test` | golden CLIF re-capture for U′ (C-6, C-7) | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; 15 files, 74 of 159 frames changed; G-1 accessor release missing; G-2 capture contract; C-10 three retirements |
| 5 W2 | `review` | backend: U′ cutover | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; required R1 (in-place `vec-set` strands an owning old element), R2 (operand order), R3 (wrappers outside the plan), R4 (confinement); advisory R5 |
| 5 W2 | `design` | backend: U′ departures 1–4; retire superseded sections | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-16; departures 2–4 adopted; 1 framed for the user; superseded sections retired |
| 5 W2 | `arch` | safety register, FIXMEs 0891/0903, test-discovery, bounded-contexts | claude-opus-5-5 | high | primary (Claude Code subagent) | delivered 2026-11-15; 0903 open (U′ cannot fix it, exposure widened); 0891 subsumed, pending delete; R14 provisional |
| 5 W2 | `qa` | intake: R1, G-1, C-10, G-2, 0916 guard, W2 filings | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; R1 and G-1 confirmed by execution; U-11 to U-14, C-10a, M-8 allocated; ACT-1028/1029/1030/1031 resolved; ACT-1049 opened |
| 5 W2 | `test` | U-11, U-12 RED; U-13; U-14; C-10a; M-8 | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `b1213aff`; 23 pass, 7 intended RED; no rows stopped |
| 5 W2 | `qa` | accept intake cells; R2/R3 evidence conditions | claude-opus-5-5 | medium | primary (Claude Code subagent, resumed) | delivered 2026-11-16; all cells accepted; U-15, U-16, U-17 and the C-10a addendum allocated |
| 5 W2 | `test` | U-15 operand order, U-16 wrapper template, U-17 moves-off faces, C-10a addendum | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `7cad84c5`; 29 pass, 9 intended RED; launch-continue row has no free-standing program |
| 5 W2 | `audit` | literal annotation on a quoted locus token | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `9946b437`; checker exit 0 |
| 5 W2 | `dev` | backend: R1, G-1, R2 shared operand order, R3 wrapper template, R5 and stale comments | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; 508 backend and 75 W2 e2e tests pass; all four detection proofs as allocated; `public-api.txt` +0 |
| 5 W2 | `test` | golden re-capture for the fixes; U-12 locus | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `2d085d75`; five fixtures, seven frames, no other drift; 134/134 |
| 5 W2 | `review` | finding-scoped re-review: R1, R2, R3, R5, G-1 | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; no required finding survives; R5 residual comments advisory |
| 5 W2 | `qa` | intake: `race` tail self-call lowered as a loop jump | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; real since S96; U-18 allocated; recommends fixing in W2 |
| 5 W2 | `test` | U-18 `race` tail self-call cells | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `a0990404`; both subjects RED (7, not 99) in six mode/cache combinations; controls pass |
| 5 W2 | `dev` | backend: `race` operand tail position; R5 comments; `CLAUDE.md` bullet | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; 511 backend tests; U-18 green in six combinations; goldens unchanged; `public-api.txt` +0 |
| 5 W2 | `qa` | U-8 cost measurement, U-10, full suite, W2 adequacy | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; U-8 within the bound (U′ faster); U-10 51 → 2; suite 6,679 run, 0 regressions; adequate pending C-10b, C-10c, U-18 retag |
| 5 W2 | `test` | C-10b, C-10c, U-18 retag, U-19 RED pair | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `7c2137d0`; 20 pass, 12 intended U-19 REDs; no U-19 filing yet |
| 5 W2 | `qa` | accept the last W2 test changes; file U-19 | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; U-19 filed as ACT-1050; C-10b and U-19 accepted; C-10c name and U-18 comments returned |
| 5 W2 | `test` | C-10c rename; U-18 past-tense comments | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `a482f1e5`; `qa` accepted |
| 5 W3 | `test` | W2 `fixed=` stamps (`3bdf398e`); E-0 to E-6, B-1 to B-4, A-1 to A-6 test-first | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `785f2933`; 41 stamps (95/95); stopped at E-0, whose detection proof cannot discriminate |
| 5 W3 | `qa` | correct E-0 detection proof; accept the stamps | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; E-0 split into two plants, one per export; all 41 stamps accepted |
| 5 W3 | `test` | W3 evidence from the corrected E-0 | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `28651769`; both E-0 declaration plants detected; isolation plants and masked clause proofs owed after `dev` |
| 5 W3 | `qa` | accept W3 evidence | claude-opus-5-5 | medium | primary (Claude Code subagent, resumed) | delivered 2026-11-16; most accepted; three groups returned (`HOME` leg setup, banner wording assumption, dormant reason location); owed-proof order set |
| 5 W3 | `test` | three returned W3 groups | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `e0c531d0`; environment 4 pass/24 RED; agent lanes as expected |
| 5 W3 | `dev` | intrinsics: runtime switch module, P8, core-count pool | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; 22 switches through one module; 395 tests pass; `public-api.txt` +3 as P8 |
| 5 W3 | `dev` | `src/`: loader, link-time embedding, agent default and banner, Cargo default features | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; 28/28 environment cells; three agent lanes pass; 1,235 root tests; transcript cells red on the new banner |
| 5 W3 | `test` | E-0 isolation plants; masked-clause rechecks; C-6 banner re-baseline | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; both E-0 plants fired; environment 28/28, agent 91/91, agent-free 23/23; C-6 13/13; eval self-check 18/18 |
| 5 W3 | `design` | int: `NO_ENV` value, extra malformed reason, banner wording, `AgentState` residual | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-16; exactly `1`; extra reason adopted; banner wording diagnostic; `AgentState` must be structural |
| 5 W3 | `dev` | `src/`: `AgentState` agreement by construction; stub model reading | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; `AgentLink` single field, structural; 3,973 root tests; three agent lanes pass |
| 5 W3 | `test` | A-1 duplicate-line and provider assertions | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `e045de20`; both planted faults caught; three lanes pass |
| 5 W3 | `design` | int: `agent.md` §3.4 as built | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-16 |
| 5 W3 | `review` ×2 | intrinsics; `src/` with `Cargo.toml` | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; intrinsics: one advisory; `src/`: required R1 (NUL value panics and prints the credential), R2 (multi-line model splits the banner), R3 (root API widened beyond the packet), nit R4 |
| 5 W3 | `review` | finding-scoped re-review: R3 under P14 | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `649a5de0`; no finding survives; R3 closed |
| 5 W3 | `qa` | W3 adequacy, full suite | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; adequate with three §0.8 assertion gaps; suite 6,960 pass / 33 fail (32 known guards, 1 timing race filed ACT-1051); no guard turned green |
| 5 W4 | `spec` | §14.9 deleted-file rule revision; retire S123-Q12 | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `899afcb0`; §14.9 revised, S123-Q12 retired, ACT-1048 resolved and deleted; follow-up §15.1 consent clause removed (session `36eeed55`); `design` citation repair; checker 0 findings |
| 5 W4 | `qa` | accept W4 evidence; rescope R-2 to the revised rule | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; R-1, R-3, R-4 and the refusal cell accepted (6 reds for `dev`); R-2 returned to `test` with R-2a and ACT-1051; plan §3.6 refreshed |
| 5 W4 | `test` | R-2/R-2a rewrite, ACT-1051, fmt revert | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `67d79afb`; R-2/R-2a green on current code; ACT-1051 fixed (10 × 12/12) and deleted; 28 pass, six accepted reds unchanged |
| 5 W4 | `arch` | dev-path optimisation principle and inventory | claude-opus-5-5 | high | primary (Claude Code subagent) | delivered 2026-11-16; Principle 27 drafted (ratify at close); 15-row inventory; keep U1, U2, push doubling; defer stack placement, flattening; retire spark density, sibling carrier, mode-ABI gate; questions for the user |
| 5 W4 | `dev` | `src/`: ACT-1047, ACT-1020, ACT-1035; delete superseded redefinition residue | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; six reds green; residue deleted (`redefine.rs` 3165 → ~1300 lines); cache-load retirement of persisted mono instances and absent-dependent reload skip added; lib 1184/1184; 23 binaries 1180/1191, the 11 pre-existing; two `main.rs` sites need a root helper (`arch`) |
| 5 W4 | `review` | `src/` W4 change | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `194c794b`; one required finding R1: cache preload retires persisted mono instances as permanent tombstones, so each cached restart consumes GOT slots (128 generics: 7th cached `--run` and `--link` exhaust 1,024 slots); residue deletion, absent-dependent filter and file protection clean |
| 5 W4 | `qa` | evidence for W4 review R1 | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; attribution confirmed (5 launches × 129 tombstones; monomorphic control +1/launch); R-5 allocated (e2e in `tests/cache.rs`, dev unit row); ACT-1025 citation fixed |
| 5 W4 | `test` | R-5 cached-restart slot growth RED | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `4dcb5f63`; `tests/cache.rs::cached_restarts_keep_generic_instance_slot_capacity_across_modes` RED on exhaustion at the third cached launch; control and six fences green |
| 5 W4 | `qa` | accept R-5 cell | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; accepted; `test` drops a stray word in the cell comment before commit |
| 5 W4 | `arch` | R1 fix boundary: slot release on cache load | claude-opus-5-5 | high | primary (Claude Code subagent) | delivered 2026-11-16; no fix inside the current API; packet P15 (`SymbolTable<(), ()>::release_callable`) and P16 (`cranelisp::project_root_candidate` for ACT-1020's `main.rs` sites) awaiting the user; `performance.md` citations repaired |
| 5 W4 | `design` | backend: audit R5/R6 remainder; Principle 27 records; classifier retirement design | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-16; `ownership-codegen.md` gains a per-mechanism disposition table and the retirement change-set (`RcAtomicity` collapses to the global probe); ACT-0964 items 1–2 met; R5 partial (history stubs still cited by other owners; `io-trampoline.md` rewrite ~1 wave, carried); R6 is `dev`'s |
| 5 W4 | `dev` | backend: classifier retirement, `compile_trap_stub`, citations, R6 | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; classifier, census, `RcAtomicity` and `RaiseMessage` gone; CLIF byte-identical pre/post; `public-api.txt` −1 (`compile_trap_stub`); 497 lib tests; probe detection proven; crate memory rewritten; golden lane already red on the W4 tree (4 renumbering drifts) |
| 5 W4 | `review` | backend W4 change-set | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `937059fd`; no correctness or API finding; `public-api.txt` −1 matches P13; doc handoffs: `qa` plan citation, `design`(backend) probe-coverage claim |
| 5 W4 | `qa` | attribute golden-lane drift on the W4 tree | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; benign renumbering from `derive_codegen_batch`'s sorted batch (control: HEAD plus `targets.sort()` reproduces all 14 captures); scoped four-entry re-baseline by `test`; plan citation repaired |
| 5 W4 | `test` | scoped golden re-baseline (four entries); R-5 comment | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `68171dc8`; 130 declarations changed, `u0:K` only; ten goldens unchanged; lane passes; attribution for the commit at `.local/s123-w4/golden-rebaseline/commit-message.txt` |
| 5 W4 | `dev` | types: P13 (`Life::Broken` and its items) and P15 (`release_callable`) | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; `public-api.txt` −26/+1 as approved; 290 lib tests; refusal-restore detection proven; downstream arms: typecheck `adt.rs` ×2, backend `lib.rs:241`, `src/worker.rs:85` |
| 5 W4 | `dev` | typecheck: `Life::Broken` arms | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; two arms in `adt.rs`; nextest 972/972; `public-api.txt` +0 |
| 5 W4 | `spec` | §7.7: stdlib arithmetic semantics leave the language spec | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `dff303ea`; §7.7.1 prescriptions and §7.7.1a removed; §7.5 examples use locally declared traits; checker 0 findings; `qa` regrades §7.4.2a and §7.7 at W4 adequacy |
| 5 W4 | `dev` | backend: `Life::Broken` arm | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; one arm; nextest 498/498; `public-api.txt` −1 only; no schema bump |
| 5 W4 | `dev` | `src/`: `Life::Broken` arm, P15 caller and R-5 unit row, P16 | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; R-5 unit row red then green, e2e cell 6/6 legs; P16 guards red with the old mapping; 1,608/1,613 with 5 known guards (ACT-1034 ×4, ACT-1016); preload function renamed `release_bodies_the_recompile_restages` (coordinator repaired the packet citation mechanically) |
| 5 W4 | `review` | finding-scoped R1 and the P13/P15/P16 change-set | gpt-6.1-sol | medium | `codex_role.py` | declined 2026-11-16 (session `4c66beb3`): spanned four surfaces; split per METHOD §1.1 |
| 5 W4 | `review` | types: P13, P15 | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `8202d217`; no implementation finding; baseline −26/+1 matches; advisory doc handoff already with `arch` |
| 5 W4 | `review` | `src/`: R1 re-review, P15 caller, P16 | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `ad702ed1`; R1 closed in every mode; P16 matches; one advisory: safety comment at `lifecycle.rs:4456` repeats the rejected no-cross-module claim |
| 5 W4 | `dev` | `src/`: P15 safety comment | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; rustdoc states P15's safety grounds with the falsifier; comments only |
| 5 W4 | `qa` | W4 adequacy, full suite, traceability | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; adequate; suite 6,969 pass / 31 fail (30 filed guards; `role_wiring` principle count from Principle 27); seven guards green; ACT-1047, ACT-1020, ACT-1035 closable after stamps; ACT-1052 carries; spec band regraded; coordinator repaired the Appendix D anchor mechanically |
| 5 W4 | `test` | `role_wiring` principle count; stamp seven green guards | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `9026ed10`; count updated (34/34); one spec anchor split; stamps follow the W4 commit |
| 5 W4 | `design` | int: P15 built; rename citations | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-16; P15 and P13 recorded as built; citations renamed |
| 5 W4 | `design` | backend: as-built records and probe claims | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-16; four files; probe coverage stated as a reach table; §5.3 fence corrected |
| 5 W4 | `design` | int: trap-stub remnants; P15 records as proposed | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-16; five files; §8.2 records the confirmed defect and P15 as proposed; flips to built after `dev` |
| 5 W4 | `arch` | W4 as-built records: types crate memory, symbol-table lifecycle, deleted-item mentions | claude-opus-5-5 | high | primary (Claude Code subagent) | delivered 2026-11-16; the types crate memory, the symbol-table lifecycle design, the interfaces record, principle 22's facts and the architecture ownership-inference record updated; redefinition sequence diagram deleted; checker and wiring 0 findings |
| 5 W4 | `arch` | amend Principle 27 to the user's rulings | claude-opus-5-5 | high | primary (Claude Code subagent, resumed) | delivered 2026-11-16; parallelism carve-out with reasons; scope and inline-table sections; related records aligned; checker and role wiring 0 findings |
| 5 W4 | `design` | int: W4 as-built records | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-16; 8 files +265/−380; residue recorded deleted; cache-load retirement recorded with an independent slot-growth concern (= review R1); freeing instead of retiring would need a types-crate function (`arch`, gate) |
| 5 W4 | `design` | int: `int.md` stale consent paragraph | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-16; two `int.md` remnants fixed; `design/int/` sweep clean; checker 0 findings |
| 5 W4 | `design` | int: drop deletion detection and consent from the lifecycle design | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-16; session `e7c1d798`; `repl-lifecycle.md` deletion rule now "needs nothing"; current code already conforms (`src/watch.rs`), no `dev` change |
| 5 W4 | `test` | REDs R-1 to R-4 and the template-caller refusal cell | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `44b54cb4`; 20 tests, 7 intended REDs (R-1 overwrite and no lock; R-2 notice, written to the superseded rule; R-3 dotted empty start; R-4 SIGSEGV), controls green; refusal cell already passes |
| 5 W3 | `dev` | `src/`: the three §0.8 loader assertions | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; four `env_files` tests, green first run (implementation conforms); unit 27/27, environment 32/32 |
| 5 W3 | `qa` | §0.8 annotations for the new tests | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; gaps closed; §0.8 heading `[Tested]`; both checkers exit 0 |
| 5 W3 | `spec` | CLI §0.8: the three agreed loader readings | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `bc8f3826`; all three recorded in `repl/spec/00-cli-invocation.md` §0.8; checker clean; `qa` reassesses evidence |
| 5 W3 | `dev` | `src/`: P14 crate-private `AgentState` and builders | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; `build_agent_state` deleted, test callers moved; both builds warning-free; agent lanes 91/91, 91/91, 23 pass; R3's `agent_activation` part was already crate-private |
| 5 W3 | `test` | REDs for `src/` review R1, R2 | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; session `c5861cfa`; both RED (value leaked, exit 101; two state lines); controls pass |
| 5 W3 | `dev` | `src/`: review R1–R4 | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-16; R1 values refused before any setter; R2 one-line banner; R3 narrowed except `AgentState` field removal; environment 32/32; three lanes pass |
| 5 W3 | `arch` | ruling: `AgentState` public field removal | claude-opus-5-5 | high | primary (Claude Code subagent) | delivered 2026-11-16; gate applies; packet row P14 (make `AgentState` and its builders crate-private) approved by the user 2026-11-16 |
| 5 W3 | `review` | finding-scoped re-review: `src/` R1–R4 | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; no required finding survives; one advisory comment |
| 5 W3 | `design` | int: NUL refusal and one-line banner records | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-16; three §0.8 readings for `spec` and the user |
| 5 W2 | `review` | finding-scoped: the `race` fix | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-16; no scoped finding; separate leak observed (ignored heap `bind` result) |
| 5 W2 | `arch` | delete FIXME 0891 | claude-opus-5-5 | high | primary (Claude Code subagent) | delivered 2026-11-16; verified at source and deleted; 0903 records its two remaining obligations |
| 5 W2 | `design` | backend: R2 operand order, R3 wrappers | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-16; R2 one shared order definition (§3.2); R3 constrained fixed template (§3.3) |
| 5 W1 | `review` ×2 | finding-scoped re-reviews: `src/` R1–R3, intrinsics I1–I2 | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; no finding survives |
| 5 W1 | `design` | intrinsics: report escaping rule; as-built wording | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-15; both escaping points accepted; no `dev` change |
| 5 W1 | `design` ×3 | platform invariant 10; primitives and runtime records; backend records | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-15; no checker findings in their files |
| 5 W1 | `design` | int: as-built updates (trace ring, §6.1.2 census, §6.5 cache, child arguments) | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-15; no findings in `design/int/` |
| 5 W1 | `design` | int: dispatch-fault cause in the `--test` outcome line | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-15; the fail reason carries the child's last stderr line (test-runner design, "The cause of a fail" and test-child row 9) |
| 5 W1 | `spec` | dispatch-fault report form; open-test result wording | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; session `4936b313`; dispatch-fault form recorded in `spec/12-runtime.md` §12.7.6; S123-Q13 opened |
| 5 W1 | `design` | int: startup-settle assurance grade (`design/int/int.md` §6.1.2) | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-15; revised to a structural scheduler transition |
| 5 W1 | `design` | int: startup typecheck-settled wait; `int.md` §6.11 | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-15; `int.md` §6.1.2 and §6.11; no cross-crate change |
| 5 W0 | `spec` | record the accepted design readings | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; session `bf7ab0fe`; S123-Q12 (recreate-question sentence) open, needed by W4 |
| 5 W0 | `qa` | evidence-delta citation repair; G1 updated to the runner ruling | claude-opus-5-5 | medium | primary (Claude Code subagent) | delivered 2026-11-15; readiness now has no blocking gap; T-7, T-8 added |
| 5 W0 | `design` | int: runner-isolation wording in `test-runner.md` §6.5 | claude-opus-5-5 | medium | `claude_role.py` | delivered 2026-11-15; checker exit 0 |
| 5 W0 | `arch` | runner-isolation wording in `s123-panics-and-environment.md` §1.5; packet approval status | claude-opus-5-5 | high | primary (Claude Code subagent) | delivered 2026-11-15; P11–P13 marked approved; checker exit 0 |
| 3 | `spec` | panic, CLI, environment and linking requirements; five questions; R9 | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; session `b4a26384`; 11 questions in Appendix D |

## Phase 2 outcome — awaiting the Phase 2 → 3 checkpoint

- Architecture: [S123 architecture review](s123-architecture-review.md).
- Carry triage: [S123 carry triage](../tests/plan/s123-carry-triage.md).
- Coordinator spot-checks at source, 2026-11-15: the catalog row for
  `runtime/panic` declares `has_return: true` while `runtime_panic` returns
  nothing (`crates/cranelisp-intrinsics/src/catalog.rs`, `panic.rs`); in-place
  `vec-set` rests on a dynamic `rc == 1` probe unless a static uniqueness proof
  existed (`compiler/vec_codegen.rs`, `node_unique_static` at the Phase 2 checkpoint; retired by the W2 U′ cutover).

### User rulings on the Phase 2 decisions, 2026-11-15

- **Privacy interaction** (review §1.3): accepted as it stands; no change in
  S123. A project `.env` that sets the provider, combined with an ambient key,
  remains an accepted residual.
- **Linked executables** (review §2.3): link-time parameters are baked into
  the executable. This replaces the review's proposal that linked programs
  read only their process environment.
- **Accepted file keys:** the `CRANELISP_` prefix plus `NO_COLOR`,
  `ANTHROPIC_API_KEY` and `OLLAMA_API_BASE_URL`; all others ignored.
- **Default-build cost:** accepted (OpenSSL headers and `pkg-config` on Linux;
  112 → 211 packages; debug binary about 170 → 257 MB; about 21 s per clean
  build).
- **An agent-free build stays supported**, kept honest by one test
  configuration.
- **Third deferral:** the 16 FIXMEs named in the carry triage and ACT-0962
  carry, on the expectation that option 2 resolves the leaks; they are
  re-judged after the option-2 decision.
- Open, answered next: option 2's reading for "simplest, most robust for
  dev", and where option A's slot query is called.
- **Option-2 pre-check** (user-directed, 2026-11-15; `qa`,
  [triage §7](../tests/plan/s123-carry-triage.md)): ACT-1030, ACT-1026 and
  ACT-1028 still fail with `CRANELISP_NO_OWNERSHIP` set, armed and unarmed,
  and their controls balance in both polarities. Reading R leaves these
  faults in place; whether U′ removes them depends on its retained rules.
  `--run` only; binary sha256 `aa01c46b…` at `f747990f`.

### User rulings, 2026-11-15 (continued)

- **Option 2: reading U′ is the target**: uniform counting except a closed,
  named list of complexity-preserving rules, each checked against the
  uniform rule (review §3.4). The second discriminator (in-place versus copy
  updates on the exemplar warm solve) runs now.
- **Panics end the process.** A runtime panic reports its message and exits
  the process, in every mode, the REPL included; there is no propagation and
  no recovery. Programs avoid panics through checked operations that return
  `Option`, for example a checked integer division. Uncovered matches become
  compile errors (scheduled separately). Consequences for scope, to confirm
  at the Phase 3 checkpoint:
  - option A, its `runtime/panic_pending` API delta and the empty-slot
    invariant leave the scope;
  - ACT-1040 and ACT-1042 resolve by the process exiting at the panic;
    ACT-1041 and the panic-prefix question stay, because the exit message
    still has to be right;
  - `catch-runtime-error` loses its purpose; the exemplar's per-request 500
    handler and the stdlib test runner's "panicked" outcome depend on it.
- **Linked executables:** `ANTHROPIC_API_KEY` and the other agent variables
  are REPL-only and never baked. A linked program reads its environment only
  through a platform. Coordinator reading, for `spec` to confirm: the
  `CRANELISP_*` switches in force at `--link` are fixed in the executable,
  and its runtime does not read them from its process environment.
- **Option-2 pre-check 2** (user-directed, 2026-11-15; `qa`,
  [triage §8](../tests/plan/s123-carry-triage.md)): the exemplar's warm solve
  makes 11,593 dynamic vector updates, all on the copy arm, with analysis on
  and off. In-place updates occur only when the update is written directly in
  a self-tail loop; wrapping it in a function, including the stdlib's `conj`
  and `assoc`, makes every update copy. The toggle also makes the direct loop
  copy, which corrects review §3.2. Not filed: the solve retains 556
  allocations with the toggle on.

### User rulings at the Phase 2 → 3 checkpoint, 2026-11-15

- **The three panic consequences are accepted:** the REPL exits on a panic;
  the exemplar's web server exits on a panic, so it needs checked operations
  wherever a request could panic; `catch-runtime-error` is removed, and the
  stdlib test runner starts each test as its own process.
- **The review's scope changes are accepted into S123:** ACT-1032; ACT-1025;
  committed REDs for ACT-0997, ACT-1016, ACT-1017, ACT-1001 P-3 and ACT-0973;
  ACT-1033's catalog derivation (no gate); the loader's process-environment
  override and off switch; `spec` frames K6 C3 and C4, ACT-1020, ACT-1048 and
  ACT-0986 item 1; `arch` prepares one combined API packet for K5 N1, the K11
  baseline batch and audit R10 (not implemented). The ACT-1041, ACT-1036 and
  ACT-1017-prefix correction proceeds without FIXME 0915, which carries.
- **`design` moves to Claude in the shared package** (`claude-opus-5-5`,
  medium), for every consumer. Applied 2026-11-15 to `.agents/agents/design.md`,
  `.agents/CONSUMING.md`, `.claude/agents/design.md` and root `CLAUDE.md`;
  package unit tests, `check_consumer.py` and `tests/role_wiring.rs` pass. The
  `.agents` change is uncommitted; committing and pushing it to se-agentic and
  updating the pin are close operations needing their own approval.

### User rulings on the Phase 3 decisions, 2026-11-15

The user accepted every coordinator recommendation in the Phase 3 decision
list (conversation, 2026-11-15: "accept all other recommendations"), except
the treatment of the panic function itself:

- **API gate:** packet rows P1, P2, P5, P7, P8 approved; platform dispatch
  faults end the process, so P3, P4 and P9 are approved; P10 approved with U′;
  Part B — B2 and B3 at close with the baseline regeneration, B1 in S124.
- **Panic function (P6):** approved as proposed — it stays the
  `runtime/panic` intrinsic and becomes "never returns" (the user withdrew
  "pull the panic function" as a mistake, 2026-11-15).
- **Panics:** a panic during macro expansion ends the process; a call to a
  symbol a redefinition left broken is refused at compile time; concurrent
  panics report the first to reach the exit path; prefix
  `error: runtime panic:`; plain text on stderr; checked division is the
  primitive `checked-quot`, returning `None` for a zero divisor and for the
  most negative integer divided by −1; the test runner uses one child that
  restarts after a panic.
- **U′:** the measurement bound is no cost cliff and the exemplar within the
  same order of magnitude, measured on the U′ build; a binder is released
  where it dies; stack placement and confined non-atomic counting stay for
  now; ACT-0964's two soft lookup arms are hardened.
- **Environment and linking:** project-root `.env` and
  `~/.config/cranelisp/env`, with `XDG_CONFIG_HOME` honoured; dotenv syntax; a
  malformed or unreadable file is a startup error; `CRANELISP_NO_ENV` in the
  process environment turns the loader off; every applicable non-agent
  `CRANELISP_*` switch is fixed at link time; the worker pool uses the core
  count; an unrecognised provider value gives a dormant notice naming it; the
  agent-free build's banner says the agent is not built in; `discover-tests`
  is refused inside a test child.
- **REPL carries:** ACT-1047 loads a `user.cl` that appears mid-session;
  ACT-1048 keeps definitions, notifies, and asks before recreating a deleted
  file; ACT-1020 maps `core.str` to `core/str.cl`.
- **Carried questions answered:** K6 C3 checks named ADT fields transitively;
  K6 C4 keeps source names and distinguishes internal identities; ACT-0986
  item 1 warnings come only from the compiler's runners.

### User rulings at the Phase 3 → 4 checkpoint, 2026-11-15

The user answered "approved" to the checkpoint. The coordinator records it as
accepting every recommendation presented with it:

- **Runner gap (`qa` G1):** the in-language stdlib runner drops panic
  isolation; `cranelisp --test`'s supervisor, which restarts its child after
  a panic, is the isolation. This narrows the earlier "each test as its own
  process" ruling for the in-language runner only. P1 is no longer blocked.
- **Packet:** P11, P12 (with `arch`'s names) and P13 approved; P13 lands at
  close if the superseded redefinition code is deleted in Phase 5, otherwise
  in S124. The S121 redefinition outcomes and publication receipt retire.
- **Evidence readings:** `qa`'s U′ cost reading (a cliff is fewer in-place
  updates in any update loop than today, or a slowdown that grows with
  workload; the exemplar warm solve under 10× slower); the banner prints in
  piped sessions too; the panic exit status is asserted non-zero and not a
  signal, never as exactly 1; a second named stdlib-dependency exception in
  root `CLAUDE.md` for running the `user/` samples; the eight residuals in the
  evidence delta §5 accepted at unit or construction grade.
- **Spec details:** the designs' readings are accepted (dotenv dialect,
  internal test-child arguments, panic message placement, deletion-notice
  wording); `spec` records them at the start of Phase 5.
- **Dispatch faults** report without the panic prefix, so a test child shows
  them as a failed test naming the cause.

### User rulings in W3, 2026-11-16

- **P14 approved** as proposed: `AgentState` and `build_agent_state_with`
  become crate-private, and `build_agent_state` leaves the public surface.
- **CLI §0.8 readings agreed** (`design/int/environment.md` §5):
  `CRANELISP_NO_ENV` takes exactly `1`; text after a closing quote is
  malformed; a chosen value containing a NUL byte stops startup without
  printing the value. `spec` records them.

- **Deleted backing file (revises the 2026-11-15 deletion ruling; resolves
  S123-Q12 and ACT-1048).** The REPL owns its backing files. A deleted loaded
  file needs no detection, notice or consent: its definitions stay live and
  the next definition rewrites the file as usual. The rule for a file that
  appears mid-session is unchanged.

- **Dev-path optimisation (resolves `uniform-counting.md` §9.1).** The user's
  words: "simplify the dev path. we just need enough optimisations to avoid
  exponential time. otherwise we'll defer to release build. however, we
  should be retaining the type annotations that release optimisations might
  rely on, even if dev does nothing with them." The backend's confined
  non-atomic classifier retires; typecheck keeps producing its confinement
  and escape facts. `arch` records the principle and assesses the other
  dev-path optimisations against it. Coordinator's reading, for the user to
  correct: "exponential" covers any super-linear blow-up, such as the
  quadratic update loops U′ removed.

- **Principle 27 questions (2026-11-16).** The user accepted the
  recommendations, except parallelism:
  1. "Blow-up" means a change of growth rate, not literally exponential;
     U1, U2 and `Vec` capacity doubling stay.
  2. Principle 27 replaces the 2026-11-15 ruling that kept stack placement
     pending a cost measurement.
  3. No new dev-tier optimisation from now. The confined classifier retires
     in W4; the other retirements and deferrals (stack placement,
     flattening, spark density, the borrow-elision carrier, the mode-ABI
     redefinition gate) are scheduled for S124 with their API packets and
     spec rulings.
  4. **Parallelism stays on the dev tier:** lenient evaluation and the
     spine §0 parallelisation goal remain in force. `arch` amends
     Principle 27 to say so.
  5. The inline scalar primitive table is the direct lowering of a scalar
     op, not an optimisation; it stays.
  6. Compile-time machinery (module cache, incremental JIT) is outside
     Principle 27, which covers emitted code.

- **P15 and P16 approved** as proposed (packet §A6): `SymbolTable<(), ()>::release_callable`
  for the cached-restart slot fix (review R1, R-5), and
  `cranelisp::project_root_candidate` for ACT-1020's two `main.rs` sites.

- **§7.7.1 `Num` overflow and §7.7.1a `Unchecked` (2026-11-16).** The
  user's words: "this is a stdlib decision - so not part of language.
  different stdlibs could have different levels of panic-aversion." The
  language spec prescribes only the primitives' arithmetic (§12.7.3); how a
  stdlib's `Num Int` treats overflow, and whether it offers an unchecked
  variant, is that stdlib's choice. `spec` removes the prescription from
  §7.7.1 and §7.7.1a and replaces §7.5's `Unchecked` examples.

## Waves (Phase 4 proposal)

Rules for every wave:

- One source-touching agent at a time, and one Cargo owner at a time; `test`
  and `dev` alternate inside a wave. Read-only roles may run alongside.
- Test-first: `test` lands the wave's cells from the
  [evidence delta](../tests/plan/s123-evidence-delta.md) §7 and sees each RED
  fail on its assertion; `qa` accepts them; then `dev` implements, with its
  module rows; then `review` inspects; then `qa` judges adequacy.
- `dev` is narrow-deployed, one crate-shaped surface per dispatch; a wave
  touching several surfaces runs them in the order listed.
- Routing: `dev`, `qa`, `arch` and `design` on Claude; `test`, `review`,
  `spec`, `docs` and `training` through `codex_role.py`.
- A wave closes with its targeted suite green apart from filed guards, and the
  document checker at exit 0. The full suite runs at W5.

### W0 — Preparation (no compiler behaviour change)

| Role | Surface | Work |
|---|---|---|
| `spec` | `spec/`, `repl/spec/` | record the accepted design readings (dotenv dialect, internal test-child arguments, panic-message placement, deletion-notice wording) |
| `qa` | `tests/plan/` | fix the evidence delta's R-2 citation (REPL lifecycle §1.3.2) |
| `test` | `tests/` | ACT-1032 cache isolation (M-1); the five committed REDs K-1 to K-5; link the evidence delta from `tests/CLAUDE.md` |
| `dev` | `src/` | ACT-1025 test-fixture fix |

### W1 — Panics end the process

| Order | Role | Surface | Work |
|---|---|---|---|
| 0 | `design` | int | converge both startup paths on the typecheck-settled wait (W0 residual, Invariant SW); correct `int.md` §6.11 with the ACT-1017 prefix |
| 1 | `test` | `tests/` | M-7 stdlib-free fixtures (before P1); P-1 to P-12, P-18, P-19, T-1 to T-5, T-7 and the C-1, C-2, C-3, C-5, C-9 re-points |
| 2 | `dev` | intrinsics | the terminator, ACT-1033 catalog derivation (first compile first), P1–P7, P9, P11 |
| 3 | `dev` | backend | the single raise helper; removable sentinel and leak-caveat code |
| 3b | `dev` | intrinsics | `design`(intrinsics) follow-up: poll-leaf catalog constructor for `runtime/sleep_pollfn`; defect-report module test (`process-lifecycle.md` §1.1, §1.7, §2.2) |
| 3c | `dev` | types | P9: remove `PlatformError::DispatchError` |
| 4 | `dev` | `src/` | host boundaries, ACT-1041, the test supervisor and child (P12); the ACT-1017 single prefix (`int.md` §6.11); the fused scheduler transition so in-memory completion implies a terminal pool (`int.md` §6.1.2) |
| 4b | `dev` | primitives | `checked-quot` (P-10 unit rows first) |
| 5c | `dev` | backend, then primitives | `Int.MIN / -1` wraps in the inline division and in `div_i64` |
| 4c | `dev` | platform | retire or re-point `platform_error_dispatch_error_carries_fn_name`; stale dispatch-error rustdoc in `lib.rs` |
| 5 | `dev` | `stdlib/`, `exemplar/` | the in-language runner without isolation (T-8); the web server with checked operations; `checked-quot` users |
| 5b | `dev` | `src/` | the `--test` fail reason carries the child's last stderr line (`test-runner.md` §6.5, row 9) |
| 6 | `training` | `examples/` | `examples/32-concurrency-combinators.cl` without `catch-runtime-error` |
| 7 | `review` | per surface | intrinsics, backend, `src/` |

### W2 — U′ uniform counting

| Order | Role | Surface | Work |
|---|---|---|---|
| 1 | `test` | `tests/` | U-1 to U-5: ACT-1030, ACT-1026, ACT-1028 cells; the lead batch; the moves-on/off differential; in-place counts on direct and wrapper loops |
| 2 | `dev` | backend | the U′ cutover in one change-set (U-6, U-7, U-9); ACT-0964 items 1–2 hardening |
| 3 | `test` | `tests/` | C-6, C-7: golden CLIF re-baseline in the same change-set |
| 4 | `review` | backend | U′ cutover |
| 5 | `qa` | — | U-8 cost measurement against the agreed bound; U-10 |

If the cost measurement breaks the bound, the wave stops and returns to the
user before W3.

### W3 — Environment, baked switches, agent on by default

| Order | Role | Surface | Work |
|---|---|---|---|
| 1 | `test` | `tests/` | E-0 suite isolation with its detection proof; E-1 to E-6, B-1 to B-4, A-1 to A-6; the agent-free lane |
| 2 | `dev` | intrinsics | runtime switch capture and install (P8), core-count worker pool |
| 3 | `dev` | `src/` | the loader, link-time embedding, the agent default and banner, Cargo default features, `src/CLAUDE.md` |
| 4 | `review` | intrinsics, `src/` | |

### W4 — REPL carries and cleanup

| Order | Role | Surface | Work |
|---|---|---|---|
| 1 | `test` | `tests/` | R-1 to R-4 (ACT-1047, the deleted-file rule R-2/R-2a, ACT-1020, ACT-1035), the template-caller refusal cell, and ACT-1051 |
| 2 | `dev` | `src/` | ACT-1047, ACT-1020, ACT-1035 (ACT-1048 needs no change under the 2026-11-16 ruling); delete the superseded redefinition machinery and its outcomes |
| 3 | `dev` | types, backend | P13 and `compile_trap_stub`, if the deletion landed; retire the backend confined classifier (`rc_atomicity_for_node`) and its census hook |
| 4 | `design` | backend | audit R5/R6 remainder after the U′ landing |
| 5 | `review` | `src/`, types | |

### W5 — Integrated gate

`sprint` runs, on a fresh build of the final tree: the full suite, the agent
lane and the agent-free lane, all showcase demos, the exemplar, the document
checker, the spec link and coverage checks, and the public-API baselines,
regenerated once for the phase and returned to the user if non-empty. `qa`
judges adequacy for the Phase 5 → 6a checkpoint.

### Phase 6a and 6b (planned; separate approvals)

- 6a: `audit` on `cranelisp-frontend`; `docs`, `training` and `test` assess
  the user-facing surfaces against the delivered behaviour.
- 6b: the modules and macros guides, `user/cli-reference.md`, the runnable
  `user/` sample harness (M-3, with the root `CLAUDE.md` exception), the
  session-lock demo (M-4, M-5), and transcript re-baselines for the banner.

### Phase 5 notes

- W0, 2026-11-15: `qa` remeasured two carried filings. ACT-1017's location
  face was fixed by `aed0fcb1`; its prefix face is open at every seam.
  ACT-1016's export-cycle reload leg is fixed; face 1 and the fresh-load legs
  stay RED. Handoff to W1: `design`(int) corrects `int.md` §6.11's "Diagnostic
  as delivered" text with the ACT-1017 prefix correction.
- W0, 2026-11-15: `dev`(src) found a possible residual beside ACT-1025. On
  normal startup a non-empty entry can return from registration still
  `TypecheckWorking`; only the empty-entry path waits for typecheck to settle.
  Invariant SW in `src/CLAUDE.md` holds only once the worker reaches
  `notify_typecheck_done`. No observed harm. Routed to `qa` for a ruling, with
  `design`(int) if a source change is wanted.
- W0 closed 2026-11-15. `arch` repairs the ACT-1025 link in FIXME 0694 when
  convenient; `qa` then deletes the resolved action.
- W1, 2026-11-15, `dev`(intrinsics) handoffs to carry: P9
  (`PlatformError::DispatchError` in `cranelisp-types`) is still to do with the
  `src/` step; `dev`(primitives) has three unreachable-code warnings after
  raisers; `test` updates `platforms/poll-pool`'s survival-policy description
  (P-11); `qa` grades the two-raiser detection as probabilistic; ACT-1042 and
  ACT-1033 name removed symbols, so `qa` disposes them at W1 close.
- W1, 2026-11-15: `design`(intrinsics) suggests, not blocking, that backend
  `compile_sleep` take `runtime/sleep_pollfn`'s `FuncId` from the catalog
  declarations; carried to `design`(backend) with the W2 cutover.
- W1, 2026-11-15, `dev`(backend) handoffs: 13 golden-CLIF fixtures to
  re-baseline once the root crate compiles (`test`); `design`(backend) updates
  `backend.md` §7 status and removes the trap-stub leak caveat in
  `ownership-codegen.md` §8.1; making the single-emitter property structural
  needs a wrapper for `CompileContext::panic_func_id`, an API change, and is
  noted for `arch`, not scheduled; `context.rs:383` cites a cell C-2 may have
  deleted.
- W1, 2026-11-15: `dev`(intrinsics) observed an intermittent heap corruption
  in `ivar::tests::hier_decline_worker_spark_runs_at_parent_plus_one_depth`
  (`malloc(): unsorted double linked list corrupted`). `ivar.rs` changed in
  W1, so W1 `dev` work is paused until `qa` attributes it.
- W1, 2026-11-15: `qa` attributed the ivar abort: pre-existing, in the test
  only. The test freed the cell on `RESOLVED` while the spark worker still held
  an RC; the worker's late decrement corrupted glibc's free list. Controls:
  quarantine removes it (0/40,000); the RC word shows the late decrement
  (1,978/2,000); a sibling waiting for RC 1 never aborts (0/20,000). Fix routed
  to `dev`(intrinsics) inside W1. W1 `dev` work resumes.
- W1, 2026-11-15: `dev`(intrinsics) noted a second ordering in the same test,
  unobserved: `IN_FLIGHT_SPARKS` is restored before the worker's guard drops.
  Harmless under nextest's process-per-test; for `qa` to judge at W1 close.
- W1, 2026-11-15, after P9: stale "dispatch error" prose remains in backend
  comments (`apply.rs`, `dispatch_tests.rs`), `platforms/boom`,
  `platforms/test-capture` (`qa`'s) and `tests/platform_errors.rs` (`test`'s);
  swept at W1 close by their owners.
- W1, 2026-11-15, `dev`(src): the exit hook could not read the exiting
  thread's trace ring, because glibc destroys thread-locals before exit hooks;
  `dev` added a shared publishing ring (`src/trace_ring.rs`) with a
  planted-fault check. Four `test` cells assert the retired stdout display and
  need re-pointing: `lenient_binding_panic_not_swallowed_neg`,
  `lenient_binding_panic_surfaces_with_no_lenient_control`,
  `trace_nested_dynamic_raises_runtime_error`,
  `trace_nested_lexical_raises_runtime_error`.
- W1, 2026-11-15, `spec`: the user ruled that under `--test` a dispatch fault
  shows as a failed test naming the cause; as built, the outcome line gives only
  the exit status and the cause appears on the relayed stderr. Routed to
  `design`(int) and `qa` to reconcile. S123-Q13 (exact wording of the two
  open-test messages) goes to the user.
- W1, 2026-11-15, `arch` ruling: the primitives trusted base narrows from 19
  functions / 20 sites to 18 / 19, within P6 and the `checked-quot` approval;
  no user gate, reported at the Phase 5 checkpoint. Rule recorded: a helper
  that never receives a raw word from callers is not a new site; one that
  adopts a caller's raw word is. Stale records to repair: `design/runtime/s119-typed-consume-funnel.md`
  §3 and `design/primitives/primitives.md` §2.4 (`design`(primitives));
  `design/backend/s122-closure.md` §10.2 (`design`(backend)).
- W1, 2026-11-15, `dev`(stdlib): `testing.runner`'s public surface changed:
  `Outcome` loses `Panicked`, `Tally` has two counts, and `tally-line` prints
  "P passed, F failed". Handoffs: `docs` for `user/guide/testing.md`
  (lines 107–113 still present `catch-runtime-error`); `arch` for
  `design/arch/test-discovery.md`, which is titled after and describes
  `catch-runtime-error`; `qa` for traceability.
- W1, 2026-11-15, `design`(int): under `--test`, a child that ends with a
  non-zero status and no result is reported with its last stderr line (the
  fault report) as the cause; a signal death names the signal. Unit-grade
  only: no eligible test can force a platform effect. S123-Q13's proposed
  wording needs revising by `spec` to carry that line; `qa` allocates row 9
  under T-6.
- W1, 2026-11-15, `dev`(exemplar): `exemplar/tests.cl` now exits 41 (a new
  malformed-body form test), replacing 40 in evidence lines. A comment in
  `exemplar/platforms/web/src/lib.rs` claims a 400 for unparseable requests;
  the router sends 405. Left for a later `dev`(exemplar) pass.
- 2026-11-15: the user adopted the three `--test` fail-reason messages as
  normative (S123-Q13): `test process exited with status N without a result`,
  with `: <final stderr line>` appended when the child wrote one, and
  `test process was killed by signal N`. `spec` records them.
- 2026-11-15: the user authorized committing ("commit"). Checkpoint commit of
  W0 (complete) and W1 (implementation done; review, re-points, golden
  re-baselines and `qa` adequacy still open). `.agents`, the local `design`
  adapter and the root allocation sentence stay out until close.
- 2026-11-15, user ruling: `Int.MIN / -1` wraps to `Int.MIN`, matching the
  wrapping rule for `+`, `-` and `*`; it is no longer a panic source.
  `checked-quot` still returns `None` for it. Checkpoint commit `0a9842c6`
  holds W0 and W1's implementation before this ruling.
- W1, 2026-11-15: `spec/07-traits.md` §7.7.1 contradicts the runtime arithmetic policy in `spec/12-runtime.md` §12.7: it says
  `Num`'s `Int` `+`, `-`, `*` panic on overflow and defines an `Unchecked`
  trait that was never built. The built `impl Num Int` maps them to the
  wrapping `add-i64`, `sub-i64`, `mul-i64`. Put to the user.
- W1, 2026-11-15, `dev`(backend): regenerating the backend `public-api.txt`
  differed from the committed file by 85 derive-impl lines at `-s`; `dev`
  judged it generator flag or version drift, not its change (no `pub` line
  changed). The earlier W1 backend dispatch reported an identical
  regeneration. Check at the W5 baseline regeneration with the exact
  `tests/CLAUDE.md` command.
- W1, 2026-11-15: `crates/cranelisp-primitives/CLAUDE.md`'s "Deliberate
  asymmetries" bullet still says `div-i64` reports `Int.MIN / -1` as
  "division by zero"; `dev`(primitives) removes it in the W1 review-fix pass.
- W1 review basket, 2026-11-15 (`.local/s123-w1/review/`):
  - required: `src/` R1, the `--test` supervisor accepts a pre-existing
    predictable record directory (demonstrated forged pass); intrinsics I1,
    a multi-line fault payload breaks the one-line report contract;
    platform 1, `design/platform/platform.md` invariant 10 still requires the
    retired dispatch-error path; primitives 1, trusted-base design records.
  - advisory: `src/` R2, worker trace events print twice on normal REPL
    return (demonstrated); backend B1, the single-emitter census matches
    spelling, not identity; intrinsics I2, platform 2, primitives 2 and
    stdlib 1, stale guidance or rustdoc.
  - clean: types, `exemplar/`, `examples/`.
  Order: `dev`(src) R1–R3, then `dev`(intrinsics) I1–I2, then the
  guidance-only `dev` passes (primitives, platform, stdlib); design records in
  parallel; then `qa` adequacy.
- W1, 2026-11-15: `design/arch/bounded-contexts.md` line 552 cites "§5
  invariant 9" for `PlatformError`, which that invariant does not cover;
  routed to `arch`.
- W1 adequacy, 2026-11-15 (`qa`): adequate. New §5 residuals for user
  acceptance at the Phase 5 checkpoint: P-15's single-emitter claim is
  asserted with a named falsifier (an alias bypasses the spelling-based
  census; structural form needs an `arch` API decision); the two-raiser cell
  detects a planted no-claim fault 2 of 3 runs. Filings resolved in place:
  ACT-1017, ACT-1040, ACT-1041, ACT-1042, ACT-1033 (catalog part), ACT-0976;
  deletion waits on inbound link repoints. Not blocking, to route:
  `spec/09-macros.md` §9.9.4 still says a runtime error during expansion is a
  compile error; stale `DispatchError` wording in `platforms/test-capture/`
  (`qa`); ACT-1036 scheduling.
- W1 closed 2026-11-15: evidence accepted, nine surface reviews and two
  finding-scoped re-reviews clean, `qa` adequate with residuals, full suite
  6,738 run with 0 regressions. Carried from W1 to later waves: `fixed=`
  stamps (`test`, after the commit); `spec/12-runtime.md` §12.3.1 item 2's
  stale RED tag for ACT-0974 (`qa`); `spec/09-macros.md` §9.9.4 (`spec`);
  `platforms/test-capture/` wording (`qa`); `design/arch/test-discovery.md`
  and `bounded-contexts.md` line 552 (`arch`); `user/guide/testing.md`
  (`docs`, Phase 6b); the exemplar web-platform 400/405 comment
  (`dev`(exemplar)); inbound link repoints so the resolved filings can be
  deleted.
- W1 committed as `f5822487`.
- W2 evidence, 2026-11-15 (`qa`): confirmed live before U′ — ACT-1030
  use-after-free (all modes), ACT-1026 and ACT-1028 leaks (residual 1),
  ACT-1029 R1 and leads L2, L5, L6, L10 faults, and L4's over-release
  (smaller than predicted: `(go … p p)`); refuted — L9's leak; L7 holds.
  Wrapper loops update in place 0 of 999 times. The moves-on/off comparison
  never disagrees at this checkpoint, so its equality clause is unobserved
  firing; per-leg balance carries detection.
- W2, 2026-11-15, `dev`(backend) U′ departures from `design/backend/uniform-counting.md`, for `design` and `qa`:
  1. confined non-atomic counting (`rc_atomicity_for_node`) lost its only
     consumer, so the user's "keep for now" ruling has no effect; kept as dead
     code pending a decision;
  2. under moves off, a last use in a result position still allows an
     in-place update, so "every update copies under moves off" holds only for
     operands;
  3. spark thunk captures duplicate and drop at the forcing point instead of
     moving at their last use;
  4. a local callee in tail position is no longer taken as a TCO self-call.
  29 stale citations of deleted backend symbols remain in `design/`,
  `sprints/`, `tests/plan/` and `audits/`.
- W2, 2026-11-15, `arch`: FIXME 0903 (an RC operation on a word that may
  not be a reference) is not resolved by U′ and its exposure widened: every
  U′ drop and duplicate goes through the guarded `emit_release`/`emit_dup`.
  No W2 cell exercises the family-2 guard (`tests/trait_scrutinee_scalar_payload_0916.rs`);
  `qa` measures it on the U′ build. Backlog item 0526 in
  `design/arch/backlog/performance.md` relies on borrow elision, which U′
  retired: a re-entry decision for the user at close. Stale comments citing
  deleted symbols remain in the backend for `dev`.
- W2 intake, 2026-11-16 (`qa`): R1 is a pre-existing leak that U′ widened
  (`vec-set` as a value now takes the in-place arm and leaks); G-1 was
  introduced by U′ (100 `Point.y` calls leak 100 allocations). FIXME 0903's
  guard cell passes but no longer reaches the risky arm, and no program was
  found that does: a residual for the user. ACT-1049 opened: the armed
  stale-release check stops on releasing a stack-placed constructor (false
  positive), for `design`/`dev`(intrinsics). For routing: `fmap` passed as a
  value hits a `carrier-loss` refusal on both builds; under `--link`, one
  program printed RC counters only when `CRANELISP_RC_STATS` was also set at
  run time (touches C-5 and baked switches, W3).
- W2, 2026-11-16, `dev`(backend): G-1's cause was the lenient builder's
  placeholder `Int` node type on a synthetic body, not the plan; the
  scrutinee release now uses the binder's recorded concrete type
  (`counted_type`). New pre-existing defect: a `race` operand that is a tail
  self-call is lowered as a loop jump, so the race never runs; routed to
  `qa`. The §3.4 item 1 corpus measurement (synthetic frames that fall back
  to a body-derived parameter type) is carried.
- W2, 2026-11-16: FIXME 0891 deleted (subsumed by 0903, verified at source).
  Stale plain-text mentions remain for their owners:
  `design/backend/transitive-drop-glue.md:268` (`design`(backend));
  `tests/plan/s123-carry-triage.md:142` (`qa`); `ACT-0962`'s carried-tails
  list (`sprint`, at close); and a `crates/cranelisp-backend/CLAUDE.md`
  bullet still citing a residual-typed `Box.v` parameter (`dev`(backend)).
- W2, 2026-11-16: the `race` tail self-call defect (since S96; `spec/10-io.md`
  §10.12.8 violated, a silent wrong result, not memory-unsafe) is fixed in W2
  on `qa`'s recommendation: one ordering line in the `Race` arm of
  `compile_builtin_fn_call`, in a surface W2 already has open. The coordinator
  took the fix-now decision; reported to the user, who may overrule. A new
  `// defect:` class for a tail-position flag leaking into operand compilation
  is owed by `qa`.
- W2, 2026-11-16, `dev`(backend): the `Sleep` arm has the same ordering as
  the `race` defect, but its `Int` operand cannot hold a self-call returning
  `IO`; left as is, for `review` to confirm. `test` handoff:
  `tests/launch_grid_corrupt.rs:54` and `tests/spec_10_io.rs:24` cite the
  deleted `emit_capture_return_inc`.
- W2, 2026-11-16, `review`: `(bind (Pure [49]) (fn [v] (Pure 49)))` leaves
  one allocation outstanding (5/4); a continuation that uses the value
  balances (5/5). Possibly an unused continuation parameter not dropped at
  introduction under U′. Added to `qa`'s W2 adequacy run for attribution;
  repro in `.local/s123-w2/bind-residue/`.
- W2 U-8, 2026-11-16 (`qa`): within the user's bound; U′ is faster. Exemplar
  warm solve ×64: 2.78 s → 1.53 s; in-place updates per solve 0 → 11,585 of
  11,593; allocations 25,517 → 13,932. Wrapper loops: quadratic → linear (L3 at
  10⁷: 17.1 s → 30 ms). No count below the control; no ratio grows with size.
  U-10: the exemplar residue fell from 51 to 2 (one stranded block per `print`,
  pre-existing, ACT-1018). U-19 (an inline `bind` continuation with an unused
  heap parameter leaks one block) is pre-existing and carried to S124 under the
  correction-loop stop rule. FIXME 0889's remaining cold-compile residual may be
  fixed on U′ (1,197/1,197); `qa` and `test` re-measure.
- W2, 2026-11-16: the coordinator ran `cargo fmt` over six W2 test files (formatting only), leaving the tree format-clean.
- W2 closed 2026-11-16. Open from W2 for the user: confined non-atomic
  counting (`rc_atomicity_for_node` has no consumer under U′; retire, give it a
  new consumer, or keep as dead code). Carried: ACT-1050 (U-19), ACT-1049
  (checker false positive on stack-placed values), ACT-1018 at 2 (`print`),
  FIXME 0903 (no program reaches its guard), the §3.4 item 1 corpus
  measurement, the R2/R3 planted-run logs not kept, and FIXME 0889's possible
  fix to re-measure.
- W2 committed as `3bdf398e`.
- W3, 2026-11-16, `qa`: the `stub` provider's active banner must show the
  configured `CRANELISP_AGENT_MODEL` (A-1); today the stub labels itself
  `stub (test)` with no model. Owed proofs after `dev`: E-1 to E-6 and B-1 to
  B-4 green after the loader; E-0's isolation plants before `review`; A-6 (all
  of `tests/agent.rs` in the default build) and A-5 after the Cargo default
  features change, with the exact-transcript re-baseline (C-6).
- W3, 2026-11-16, `dev`(src) build cost of the agent in the default build:
  123 → 225 packages in the binary's dependency tree; debug binary 171.3 MB →
  257.7 MB. `pkg-config` and OpenSSL 3.5.5 were present.
- W3 `src/` review, 2026-11-16: R1 is a secret-disclosure path, demonstrated
  (a NUL in a `.env` credential panics in `set_var` and prints the value, exit
  101, even with the agent off). R2: a quoted multi-line model value splits the
  banner and can forge a second state line. R3: `pub mod agent_activation` and
  the changed `AgentState` fields widen the root crate's public surface beyond
  packet A4 with no external consumer; resolved by making them crate-private,
  not by an API gate.
- W3 closed 2026-11-16 and committed as `efd09d29`. Open for the user: confined non-atomic counting (`uniform-counting.md` §9.1) and `spec/07-traits.md` §7.7.1 wrapping with `Unchecked` removed. Carried: ACT-1051 (idle-save lock test race, `test`).
