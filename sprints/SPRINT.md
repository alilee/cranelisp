# Sprint 123: One ownership answer, contained panics, agent on by default

**Status**: PHASE 4 WAVE ORG

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
| Phase 4 → Phase 5 | — | — | pending |

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
| 3 | `spec` | panic, CLI, environment and linking requirements; five questions; R9 | gpt-6.1-sol | medium | `codex_role.py` | delivered 2026-11-15; session `b4a26384`; 11 questions in Appendix D |

## Phase 2 outcome — awaiting the Phase 2 → 3 checkpoint

- Architecture: [S123 architecture review](s123-architecture-review.md).
- Carry triage: [S123 carry triage](../tests/plan/s123-carry-triage.md).
- Coordinator spot-checks at source, 2026-11-15: the catalog row for
  `runtime/panic` declares `has_return: true` while `runtime_panic` returns
  nothing (`crates/cranelisp-intrinsics/src/catalog.rs`, `panic.rs`); in-place
  `vec-set` rests on a dynamic `rc == 1` probe unless a static uniqueness proof
  exists (`compiler/vec_codegen.rs::node_unique_static`).

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
| 1 | `test` | `tests/` | P-1 to P-12, P-18, P-19, T-1 to T-5 and the C-1, C-2, C-3, C-5, C-9 re-points |
| 2 | `dev` | intrinsics | the terminator, ACT-1033 catalog derivation (first compile first), P1–P7, P9, P11 |
| 3 | `dev` | backend | the single raise helper; removable sentinel and leak-caveat code |
| 4 | `dev` | `src/` | host boundaries, ACT-1041, the test supervisor and child (P12) |
| 5 | `dev` | `stdlib/`, `exemplar/` | the in-language runner without isolation; the web server with checked operations; `checked-quot` users |
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
| 1 | `test` | `tests/` | R-1 to R-4 (ACT-1047, ACT-1048, ACT-1020, ACT-1035) and the template-caller refusal cell |
| 2 | `dev` | `src/` | ACT-1047, ACT-1048, ACT-1020, ACT-1035; delete the superseded redefinition machinery and its outcomes |
| 3 | `dev` | types, backend | P13 and `compile_trap_stub`, if the deletion landed |
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
