# S123 evidence delta

> **Owner:** `qa`. **Readers:** `test` and `dev`, dispatched against it;
> `sprint`, sequencing it; `review`, checking delivered evidence against it.
> **Authority:** the [S123 sprint plan](../../sprints/SPRINT.md) scope and user
> rulings; `spec/12-runtime.md` §12.4.3 and §12.7; `spec/10-io.md` §10.12.7–
> §10.12.8; `spec/appendix-a-builtins.md` (`checked-quot`); `repl/spec/00-cli-invocation.md`
> §0.5.6, §0.6 and §0.8; `repl/spec/14-file-watching.md` §14.9;
> `repl/spec/16-test-discovery.md` §16.2 and §16.6; `repl/spec/17-embedded-agent.md`
> §17.4 and §17.10; `repl/spec/18-redefinition.md`. Designs:
> [panics and environment](../../design/arch/s123-panics-and-environment.md),
> [uniform counting](../../design/backend/uniform-counting.md),
> [backend §7](../../design/backend/backend.md#7-runtime-failure),
> [process lifecycle](../../design/intrinsics/process-lifecycle.md),
> [environment](../../design/int/environment.md),
> [int §16.0](../../design/int/int.md#160-open-binaryint-obligations-verified-against-source-2026-09-21),
> [test runner §6.5](../../design/int/test-runner.md#65-the-test-child),
> [session transaction §2.5 and §5.2](../../design/int/session-transaction.md#52-no-symbol-is-left-broken),
> [REPL lifecycle §1.2](../../design/int/repl-lifecycle.md#12-poll-and-reload),
> and the [API packet](../../sprints/s123-api-packet.md).
> **Checkpoint:** HEAD `f747990f` plus the uncommitted Phase 3 specs and
> designs, 2026-11-15. No compiler source is changed at this checkpoint.

Each design's "evidence conditions for `qa`" is a proposal; this record is the
allocation. Condition IDs are local to this record.

## 1. Readiness

**Verdict: ready for Phase 4, with one blocking gap scoped to the P1
change-set.** Every other changed surface is testable through an existing or
named observation seam, and no other ambiguity blocks evidence.

### 1.1 Blocking

- **G1 — the stdlib in-language runner has no per-test process mechanism.**
  The user ruled that `stdlib/testing/runner.cl` starts each test as its own
  process. No design states the launch capability; the
  [arch contract](../../design/arch/s123-panics-and-environment.md) §1.5 calls
  it a platform concern and [test runner §6.5](../../design/int/test-runner.md#65-the-test-child)
  assigns it to `dev`(stdlib) without a platform. No platform in `platforms/`
  launches a process. Packet row P1 removes `catch-runtime-error`, which
  `stdlib/fn/result.cl`, `stdlib/testing/runner.cl`, `exemplar/main.cl`,
  `examples/32-concurrency-combinators.cl` and `tests/fixtures/web_fanout/main.cl`
  import. At P1's landing `stdlib_conformance::stdlib_all_public_modules_compile_and_run`,
  the exemplar tests and `examples` fail for a reason unrelated to the
  change under test.
  - **Owner:** `arch` (the launch capability's boundary and owner), then
    `sprint` (whether the language-facing rewrites co-land with P1 or P1
    waits for them).
  - **Blocks:** the P1 change-set's wave only. An interim runner that a
    panic ends is a narrowing of the ruling and needs the user.

### 1.2 Not blocking — readings this record takes

Each is stated so the owner can overturn it before Phase 5; none changes a
condition's shape.

- **Banner in piped sessions.** §0.6.1 does not gate the state line on a
  terminal, and the existing banner prints in non-TTY sessions, so the line
  prints in piped sessions too. Every exact REPL transcript gains it (C-6).
- **Panic exit status.** §12.7.4.2 requires non-zero in batch; process
  lifecycle §1.1 fixes `1` for every mode. Cells assert non-zero and not
  signal-terminated, never the value `1`.
- **Located panic form.** §12.7.5 permits `error: runtime panic: <file>:<line>: <message>`.
  Cells accept both forms.
- **Unstated wordings.** The deletion notice (§14.9), the banner text and the
  dormant notice are not fixed by `spec`. Cells assert the named file, the
  state word (`active`, `dormant`, `off`, `not built in`) and the named
  variable or value only.
- **The U′ cost rule** (U-8) is this record's operational reading of the
  user's "no cost cliff, and the exemplar within the same order of magnitude".
  `sprint` presents it at the Phase 4 checkpoint for the user to confirm.
- **Piped consent.** REPL lifecycle §1.2 makes non-interactive input decline
  recreation, so the yes leg is not observable without a terminal (R-2).

## 2. Existing evidence the rulings change

`test` finds members by grep over `tests/` and by walking the `// spec:`
backlinks of every row §6 lists. At the checkpoint about 61 tests in 16
files name a panic message, `catch-runtime-error`, `runtime error:`,
`PANIC:` or a dispatch fault directly; helper callers add more. The class,
not the count, governs.

| Class | Members | Handling | Evidence class after |
|---|---|---|---|
| C-1 Recovery or continuation after a panic | REPL cells asserting the session continues (`spec_12_runtime::panic_then_session_continues` and its callers), empty-`select` REPL parity, dispatch-fault survival in `platform_errors.rs`, `display_exact` `runtime error:` rows | Re-point to the P-1 assertion shape. Each re-pointed cell is RED on the checkpoint binary, which is its pre-fix proof | Acceptance |
| C-2 `catch-runtime-error` users | `spec_12_runtime.rs`, `concurrency_spark.rs`, `regression.rs`, `concurrency_v9_select.rs`, `fixtures/web_fanout/main.cl` | Where the cell tested the combinator, delete it; P-9 replaces it. Where the combinator was an observation device, rewrite the cell to observe the process exit | Acceptance (P-9); otherwise as the rewritten cell |
| C-3 ACT-1040, ACT-1041, ACT-1042 guards | `spec_12_runtime.rs` from the §12.7.8 banner to the ACT-1041 cells | Re-point to P-1, P-2 and P-19 and update their `// defect:` lines; they stay RED until the terminator lands | Acceptance, then safety fence |
| C-4 In-process slot readers | Backend `test_support` readers and `vec_codegen/index_guard_tests.rs` executing cells; root pipeline and runner tests reading the slot | `dev` converts them to CLIF structure rows (P-15) or child-process cells (P-14) in the change-set that removes the slot | Safety fence |
| C-5 Linked runs that set a runtime switch only on the produced program | `tests/helpers/marginal.rs` `Drive::LinkThenRun` arms the instrument on the produced binary only, so every armed `--link` pair loses its counters; any cell that sets a switch-source member only on the run | Arm on the `--link` step. A cell that already sets the same variable on both steps keeps reaching it. B-2 proves the run-only setting is inert | Unchanged |
| C-6 Exact REPL transcripts | Every cell asserting the startup lines exactly | Re-baseline in the agent change-set, after A-1 is green | Maintenance |
| C-7 Golden CLIF fixtures | `tests/scripts/clif_golden.sh` and its baselines | Re-baseline in the U′ change-set, after U-1 to U-5 are green; `review` inspects the diff for counting decisions outside the plan | Maintenance |
| C-8 Feature-gated agent tests | `#[cfg(not(feature = "agent"))]` cells in `tests/agent.rs` leave the default suite; `#[cfg(feature = "agent")]` cells join it | The agent-free lane (A-5) runs the first group; the second must pass in the default suite with the stub provider and no network | Acceptance |
| C-9 Broken-symbol trap cells | `repl_redefinition.rs` rows that call a cascade-broken symbol | Re-point to the P-18 refusal, or delete with the residue | Acceptance |
| C-10 Retired mechanisms | `CRANELISP_CAPTURE_BORROW` (`s99_fixtures.rs`), borrow-elision and static-uniqueness CLIF assertions, the consuming-claim cells | Delete in the change-set that retires the mechanism; the change-set report names each deletion | — |

## 3. Conditions, ranked by harm

Every allocated `test` cell is a committed, spec-traced e2e test. A cell
marked **RED now** must be observed failing on its clause assertion before
its fix lands. A setup failure, a parse error or an unbuilt stub is not a
RED.

### 3.1 Ownership under U′ (memory safety)

- **U-1 — ACT-1030 use-after-free.** *Harm:* freed memory read by the next
  iteration. *Wrong:* the `let`-wrapped tail argument still forwarded without
  a reference; a fix confined to `--run`. *Seam:* the committed
  `vec_push_match_binder_same_name_shadow` pair, armed with
  `CRANELISP_RC_DEC_CHECK`, halves observed separately. *Fixture:* the
  subject and owned-binder control of
  [triage §7.3](s123-carry-triage.md#73-per-cell-faces); add `--link` (armed
  at the link step, C-5) and REPL faces. *Class:* acceptance, then safety
  fence. *Owner:* `test`. Required now.
- **U-2 — ACT-1026 and ACT-1028 leaks.** *Wrong:* `vec-len` or a forwarding
  join still not consuming; a let-bound `vec-set` result retained. *Seam:*
  `join_forwards_its_binder` D1-M and D1-L, armed; a new ACT-1028 cell whose
  balanced half is `(defn f [v] (vec-set v 0 5))` (triage §7.3). **RED now**
  (ACT-1028). All three modes. *Class:* acceptance. *Owner:* `test`.
- **U-3 — the unmeasured leads batch** (audit R3). ACT-1029's R1 pair; L2,
  L4–L7, L9, L10; an `if`, `let` or `match` over bindings at a consuming
  argument; a shadowed borrow root. *Wrong:* any counting rule that survives
  U′ in another site. *Seam:* armed marginal pairs, `--run`, halves
  separately. Each lead is committed whatever its checkpoint face; its
  checkpoint face (RED or balanced) is recorded in the cell comment, and all
  are balanced after U′. *Class:* acceptance for U′'s §6 coverage table.
  *Owner:* `test`. Required now.
- **U-4 — the moves-on/moves-off differential** (U1's check, audit R4).
  *Wrong:* a plan that drops twice or moves before a later duplicate.
  *Seam:* `gen_ownership_flows.rs` with `CRANELISP_NO_OWNERSHIP` per child,
  armed, with the stale-release check on, and four new product axes:
  tail-argument shape, COW step, alias shadowing, consume position.
  *Limit:* both polarities share the plan's death points, drop glue and the
  `rc == 1` probe; the differential cannot see a fault there. U-1 to U-3 and
  U-6 carry that residual. *Class:* acceptance. *Owner:* `test`.
- **U-5 — in-place updates stay linear.** *Wrong:* moves applied only to a
  bare `Var` argument, so wrapper loops still copy; a direct loop regressing
  to copy. *Seam:* `CRANELISP_RC_STATS` `reuse_hit`/`reuse_miss`, exact for
  in-place counts ([triage §8.3](s123-carry-triage.md#83-instrument-and-its-proof)).
  *Fixture:* D1, D2 and D4 direct loops and the L1 and L3 same-module wrapper
  loops of [triage §8.2](s123-carry-triage.md#82-counts), 1,000 iterations:
  each in place on every iteration after the first. **RED now** for L1 and
  L3. The stdlib `conj`/`assoc` rows (L2, L4) are a diagnostic observer,
  because tests stay stdlib-free. *Class:* acceptance for U1's "direct or
  wrapped update loop is linear". *Owner:* `test`.
- **U-6 — the plan linearity check** (`dev`, module). A planted missing drop
  and a planted extra move each fire; an unplanted body is silent. *Class:*
  safety fence.
- **U-7 — one decider.** Structural once the plan pass is the only producer
  of move, duplicate and drop. `review` checks the falsifiers of
  [uniform counting §9](../../design/backend/uniform-counting.md#9-open-questions):
  a counting decision in emission that reads anything but the plan; a move
  followed by a duplicate of the same binder. *Class:* safety fence.
- **U-8 — cost under the user's rule** (`qa`, one window `sprint`
  allocates, after U-1 to U-5 are green). *Control:* the last pre-U′ binary,
  copied with its sha256 recorded before the U′ change-set builds.
  *Subject:* the U′ build. *Workloads:* exemplar warm serial solve at driver
  N ∈ {1, 8, 64} with RC op counts; the on-demand contention benchmark
  `concurrency_spark::alloc_rc_heavy_parallel_cpu_floor_benchmark_ignored`;
  one full suite run, wall time and failures by name. In-tree caches are
  purged first (M-1). *Reading of the rule:* a cliff is any U-5 in-place
  count lower than the control's, or a U′/control ratio that grows with N;
  the exemplar is within the order of magnitude when its warm U′/control
  wall ratio is below 10. *Class:* acceptance for the user's U′ cost
  decision.
- **U-9 — ACT-0964 soft lookup arms** (`dev`, backend module). A planted
  missing lookup is a hard error, not a soft fallback. *Class:* safety fence.
- **U-10 — exemplar residue** (`qa`, at U-8). The ACT-1018 warm residual and
  the moves-off warm residual on the U′ build, side by side. A moves-off
  residual above moves-on is intake. *Class:* diagnostic observer. The
  as-built 556-allocation toggle residue
  ([triage §8.2](s123-carry-triage.md#82-counts)) is **not filed**: it
  observes a lowering U′ replaces in one change-set, and U-10 observes its
  successor.

### 3.2 Panics end the process

The P cells observe: exit status non-zero and not by signal; stderr holding
exactly one line matching `error: runtime panic: ` then an optional
`<file>:<line>: ` then the message; for the REPL, a marker form after the
panicking one producing no output and no further prompt. "Every mode" is the
REPL, `--run` and `--link`.

- **P-1 — a callee's panic with a heap consumer** (ACT-1040 R1–R4, R6).
  *Harm:* SIGSEGV with no message. *Wrong:* sentinel resume; the REPL
  re-prompting; a doubled or codegen-category report; the report on stdout;
  exit 0. *Fixture:* the R1–R4 and R6 shapes with the C1–C4 controls of
  ACT-1040, re-pointed (C-3). An in-frame panic (C4) now also ends the
  process. Every mode. **RED now.** *Class:* acceptance. *Owner:* `test`.
- **P-2 — a callee's panic with a scalar result** (ACT-1042). Q1: the
  calling loop exits within a bound with the index message. Q2: the index
  message, and no `division by zero`. Every mode. **RED now.** *Class:*
  acceptance. *Owner:* `test`.
- **P-3 — panic sources.** Non-exhaustive match, division by zero,
  `MIN / -1`, `vec-get` and `vec-set` out of range: each message exact,
  `--run`; the existing `vec_set_*` cells re-pointed (C-1). *Class:*
  acceptance. *Owner:* `test`.
- **P-4 — concurrent sources.** A panic in a spark, a `Par` branch, a
  detached strand and an empty `select` each ends the process with its
  message. Two sparks panicking with distinct messages produce exactly one
  report, whose message is one of the two. *Wrong:* a worker panic ferried
  to a join and resumed; two reports. `--run`, plus the REPL for empty
  `select`. *Class:* acceptance. *Owner:* `test`.
- **P-5 — output before the panic is delivered first.** `print` output and
  a prior REPL result precede the report on one merged stdout/stderr pipe.
  *Wrong:* exit without flushing host output. `--run` and the REPL.
  *Class:* acceptance. *Owner:* `test`.
- **P-6 — a panic during macro expansion ends the process** in `--run` and
  the REPL with its message, not an expansion compile error, and the REPL
  evaluates nothing after. *Class:* acceptance. *Owner:* `test`.
- **P-7 — a platform dispatch fault ends the process.** The `boom` fixture:
  one report naming the platform function and its cause, every mode.
  *Wrong:* `PlatformError::DispatchError` returned and the REPL continuing.
  *Class:* acceptance. *Owner:* `test`.
- **P-8 — negative leg.** A program with no panic prints no report and exits
  with its result; the P-1 in-range control (C3) carries it in every mode.
- **P-9 — `catch-runtime-error` is removed.** A reference is an unbound-name
  compile error in every mode. *Class:* acceptance. *Owner:* `test`.
- **P-10 — `checked-quot`.** `None` for a zero divisor and for `MIN / -1`;
  `Some` truncated toward zero otherwise (`7 / -2` and `-7 / 2` give `-3`);
  no panic. `--run` and REPL display `(Option Int)`. *Wrong:* panicking,
  floor division, `MIN / -1` wrapping to `Some`. *Class:* acceptance.
  *Owner:* `test`, and `dev`(primitives) unit rows.
- **P-11 — `poll-pool` survival fixture** becomes a process-exit fixture.
  *Owner:* `test`.
- **P-12 — trace sinks flush on a panic exit**
  ([observability §7.1](../../design/int/observability.md#71-process-exit-and-panic-wiring)):
  one `--run` cell with a file trace sink holding the pre-panic events.
  *Class:* acceptance. *Owner:* `test`.
- **P-13 — exit-time diagnostics** (`dev`, intrinsics, child process). M3
  parity armed with a panic exits with the panic status and one stand-down
  line, not an abort; `[RC_STATS]` still prints. *Class:* safety fence.
- **P-14 — the terminator** (`dev`, intrinsics). Report composition per
  fault kind; claim-once as a pure transition; child-process cells for
  status and report, ordering and two simultaneous raisers. *Detection
  proof:* a terminator that returns turns the ordering and one-report cells
  red. *Class:* safety fence.
- **P-15 — no reachable code after a raise** (`dev`, backend). CLIF
  structure rows: each site (match, division, Vec bounds) emits the call and
  the terminator through one helper. Until the helper is the only emitter,
  the census falsifier of arch §1.3 stands. *Class:* safety fence.
- **P-16 — `runtime/panic` declares no result** (`dev`, intrinsics; ACT-1033's
  derivation). A planted wrong row fails. *Class:* safety fence.
- **P-17 — crash-consistent writers.** Named residual (§5); `dev` unit rows
  show cache and backing-file writes replace by rename.
- **P-18 — broken-symbol refusal.** A language-type change of `f` whose only
  caller `g` is a template is refused naming `g`, with `f`'s prior callable
  intact; control: no caller, admitted. After the residue deletion the
  `tests/repl_redefinition.rs` cells stay green, and `test` commits QA's S122
  generic-edit probe as a fence: generic `f`, compiled caller `g`, a
  same-type body edit, and a concrete twin control. `dev` owns the guard
  rows of [session transaction §5.2](../../design/int/session-transaction.md#52-no-symbol-is-left-broken)
  with their detection proof. *Class:* acceptance. *Owner:* `test`, `dev`.
- **P-19 — report wording.** ACT-1041: the `--run` report is P-1's single
  line, with no `codegen error` and no `0..0`. ACT-1036's committed RED flips
  unchanged. *Class:* acceptance.

### 3.3 The compiler test runner

- **T-1 — a panicking test does not end the run.** Tests `a` pass, `b`
  panics, `c` pass, under `--test` and `/run-tests`. *Observed:* `ok`,
  `PANIC: <message>`, `ok` in FQ order, each FQ exactly once; the summary
  counts the panic as a failure; `--test` exits 1; after `/run-tests` the
  REPL evaluates a marker form. *Wrong:* an in-process runner (REPL dies, `c`
  absent); a restart re-running `a`; the panic counted as a pass.
  **RED now** for the REPL marker. *Class:* acceptance. *Owner:* `test`.
- **T-2 — two panics.** Both reported, every other test run once.
- **T-3 — warnings once.** A mistyped `test-` function beside a panicking
  test warns once.
- **T-4 — `discover-tests` in a test child.** A `/run-tests` module that
  references it fails the run with the §16.6 diagnostic and runs no test.
  **RED now.**
- **T-5 — negative leg.** An all-pass run's report is unchanged from the
  existing `test_runner.rs` expectations.
- **T-6 — supervisor and child** (`dev`, root module): the
  [test runner §10](../../design/int/test-runner.md#10-unit-test-design)
  test-child rows 1–8, including the child-count bound as the termination
  detection proof. *Class:* safety fence.

T-2 to T-5 are acceptance and `test`'s.

### 3.4 Environment supply and baked switches

- **E-0 — the suite never reads a developer's files or activates a provider.**
  *Harm:* REPL source sent to a live endpoint; results changed by a local
  file. *Declaration:* the nextest setup stage exports
  `CRANELISP_NO_ENV=1` and an empty `CRANELISP_AGENT_PROVIDER` to every test
  through `$NEXTEST_ENV` (probed 2026-11-15 on nextest 0.9.140: the export
  reaches tests and their children and overrides a shell value). It lands in
  the loader's change-set. `tests/helpers/marginal.rs` already clears the
  environment. *Detection proof:* a child given a user file (via `HOME`) and
  a project `.env` that select `stub` shows the dormant banner; the same
  child with `CRANELISP_NO_ENV` removed shows `active`. *Class:* safety
  fence. *Owner:* `test`.
- **E-1 — a project `.env` supplies a switch.** `CRANELISP_RC_STATS=1` in
  `.env` prints `[RC_STATS]` in `--run`, `--test` and the REPL; control: no
  `.env`. *Class:* acceptance. *Owner:* `test`.
- **E-2 — precedence.** Observed through the banner, with
  `CRANELISP_AGENT_PROVIDER` as process `stub`, `.env` `bogus1`, user file
  `bogus2`: active `stub`; without the process value, dormant naming
  `bogus1`; without both, `bogus2`. An empty process value wins: dormant
  naming the variable. *Wrong:* files over the environment; user over project;
  an empty value treated as unset. *Class:* acceptance. *Owner:* `test`.
- **E-3 — user file location.** `XDG_CONFIG_HOME/cranelisp/env` is used and
  `HOME/.config/cranelisp/env` ignored when `XDG_CONFIG_HOME` is set; `HOME`'s
  file is used otherwise.
- **E-4 — admission.** A `.env` key `S123_FOREIGN=x` is absent from `/sh`'s
  environment; `CRANELISP_S123_PROBE=y` from the same file is present.
- **E-5 — loader controls.** `CRANELISP_ENV_FILE` and
  `CRANELISP_USER_ENV_FILE` each redirect only their file;
  `CRANELISP_NO_ENV=1` reads neither; a file line setting a control is
  ignored.
- **E-6 — refusals.** An unterminated quote on a foreign-key line, and a
  directory at the `.env` path, are startup errors exiting 1 that name the
  file (and the line when malformed). A sentinel value on another line of
  the same file appears in neither stream. `--run` and the REPL. *Protected
  value:* the sentinel stands for `ANTHROPIC_API_KEY`.
- **E-7 — loader units** (`dev`, root): the
  [environment §4](../../design/int/environment.md#4-module-evidence-dev) rows
  1–5. *Class:* acceptance at the module layer.

E-3 to E-6 are acceptance and `test`'s.

- **B-1 — a switch set at `--link` takes effect.** Link with
  `CRANELISP_RC_STATS=1`; run with a cleared environment: `[RC_STATS]`
  prints. *Class:* acceptance. *Owner:* `test`.
- **B-2 — negative leg.** Link without it; run with it set: nothing prints.
  *Wrong:* the runtime still reads its launch environment; the install not
  called. Same pair for `CRANELISP_SPARK_STATS`, a member of a second
  module. *Class:* acceptance. *Owner:* `test`.
- **B-3 — a file-supplied value bakes.** A `.env` in the link directory
  supplies the switch; the program runs elsewhere with a cleared environment.
- **B-4 — agent settings are never baked.** Link with sentinel values in
  `ANTHROPIC_API_KEY` and `CRANELISP_AGENT_KEY`: neither is in the
  executable's bytes. *Positive control:* a sentinel value of
  `CRANELISP_QUARANTINE_MAX_BYTES` is (process lifecycle §2.4: plain text).
  *Class:* acceptance. *Owner:* `test`.
- **B-5 — switch source** (`dev`, intrinsics): capture/install round trip
  per member; unknown name and format refused; install after a read refused
  (child process); the crate census failing on a planted environment read;
  the linked pool built explicitly. *Class:* safety fence.

### 3.5 Agent on by default

- **A-1 — the default build prints the state.** The suite's binary is a
  default-feature build. A REPL prints one state line after the existing
  banner: `dormant` with no provider; `active` with provider and model under
  `stub`; `off` under `--no-agent`. No state line in `--run`, `--test` or
  `--link`. **RED now.** *Class:* acceptance. *Owner:* `test`.
- **A-2 — an ambient key alone transmits nothing.** `ANTHROPIC_API_KEY` set,
  no provider, `CRANELISP_AGENT_TRACE` pointed at a file: the banner is
  dormant, `/ask` names `CRANELISP_AGENT_PROVIDER`, a multi-form prose line
  evaluates deterministically, and the trace records no request. *Wrong:*
  the current fallback to Anthropic. **RED now.** *Class:* acceptance.
- **A-3 — an unrecognised provider** is dormant and the notice names the
  value, with no request.
- **A-4 — flags.** `--agent` accepted; `--no-agent` wins over it; `--yes` is
  an accepted no-op when no agent is active.
- **A-5 — the agent-free configuration.** One lane, inverting
  `tests/scripts/run-agent-lane.sh`: `--no-default-features` in its own target
  directory, so it never replaces `target/debug/cranelisp`. It runs the
  feature-off `tests/agent.rs` cells, the `not built in` banner and `/ask`
  notice, the `--agent` and `--yes` errors (exit 1, usage hint, never
  `unknown flag`) and `--no-agent` accepted. *Required at:* the agent
  change-set, any change-set touching `src/agent/`, `main.rs` flag parsing
  or the Cargo features, the Phase 5 checkpoint and close. `dev` makes the
  flag validation a function of the built-in fact with unit rows for both
  values in the default suite. *Class:* acceptance. *Owner:* `test`, `dev`.
- **A-6 — feature-on cells in the default suite** pass with the stub
  provider and no network (C-8).

A-3 and A-4 are acceptance and `test`'s.

### 3.6 REPL carries

- **R-1 — ACT-1047.** The committed FC-1 cell and its controls stay. New load
  leg: after the external save, `(k)` gives 9 and the final file holds `k`
  and `h`. A mid-session file that fails to compile locks the session and
  keeps its bytes. **RED now** (load leg). *Class:* acceptance. *Owner:*
  `test`, with new `Stage` variants for deletion and rename.
- **R-2 — ACT-1048.** Deleting a loaded `user.cl` prints a notice naming the
  file, and its definitions stay callable; in a piped session later
  definitions leave the file absent. Negative legs: a write-then-rename save
  gives no notice; a file restored after deletion is reloaded. The consent
  yes leg is `dev`'s unit row (REPL lifecycle §5, Deletion). **RED now.**
  *Class:* acceptance. *Owner:* `test`.
- **R-3 — ACT-1020.** `cranelisp core.str` loads `core/str.cl` under
  `--run`, `--test`, `--link` and the REPL (§0.5.6 says every mode); a REPL
  empty start writes `core/str.cl`. Control: the path target `core/str`.
  **RED now.** *Class:* acceptance. *Owner:* `test`.
- **R-4 — ACT-1035.** The committed RED and its controls, plus the
  [session transaction §2.5](../../design/int/session-transaction.md#25-trait-implementation-redefinition)
  pair: the parametric impl inside `begin` with `(defn keep [] 0)` gives 5;
  without `keep` the session must survive. That pair is the mechanism's
  discriminating control. `dev` owns the `worker`-seam rows. *Class:*
  acceptance. *Owner:* `test`, `dev`.

### 3.7 Committed REDs for carried defects

Each is failing-not-ignored at close unless its fix lands. Each names its
control.

| ID | Cell | Control | Fix in S123 |
|---|---|---|---|
| K-1 ACT-0997 | `(import [lib [(Box B)]])` binds `B` to `lib/Box`; the self-rename `(Box Box)` is accepted | The unrenamed import | No (packet B1, S124) |
| K-2 ACT-1016 | Face 1: a session's reload accepts a module that a restart on the same files fails. Face 2: an `export`-closed cycle is reported as a cycle | Face 1's twin defining `(defn g2 [] (a/f))` | No |
| K-3 ACT-1017 | Two cells. Prefix: one located prefix. Location: a location in the named file | A refusal of a non-failed import | Prefix only |
| K-4 ACT-1001 P-3 | An `impl` of an ambiguous trait spelling is rejected as ambiguous, naming both | An unknown trait spelling is `unknown trait` | No |
| K-5 ACT-0973 | A platform declaration in a root-level non-entry module, and in a nested one, is a compile-time error | The entry placement loads the platform | No |

*Class:* acceptance (safety fence once fixed). *Owner:* `test`.

### 3.8 Maintenance and diagnostics

- **M-1 — ACT-1032.** No suite test writes under a checked-in path. The
  three identified writers copy their fixture to a fresh directory or pass
  `--no-cache`; the in-tree `.cranelisp-cache/` directories under `tests/`,
  `examples/` and `exemplar/` are purged before U-8, with the purge recorded.
  At the Phase 5 checkpoint `qa` runs `git status --ignored` after the suite
  and attributes any new cache. *Owner:* `test`. Required before U-8.
- **M-2 — ACT-1025.** `dev`(src) makes
  `dispatch_without_a_stored_continuation_retires_nothing` assert `user`'s
  pool state, naming it, before the requeue. `qa` classifies from the next
  occurrence. *Class:* diagnostic observer.
- **M-3 — `user/` samples execute.** Every fenced block in `user/` carries a
  classification `docs` assigns: a REPL transcript (input lines after the
  prompt, expected output on the following lines), a definition block that
  must load with no error, or an illustrative block, exempt. A harness in
  `tests/` executes the first two in fresh directories with the default
  prelude, normalising the timing prefix of the prompt and the startup
  lines. An unclassified `clojure` block fails the census. *Detection
  proof:* a planted wrong expected line and a planted unclassified block
  each fail. The default prelude makes this harness stdlib-dependent. The
  stdlib-separation rule admits one named exception today (stdlib
  conformance, `tests/CLAUDE.md` §Test isolation), so this harness needs a
  second, equally visible exception; `sprint` records it in the root
  guidance's stdlib-separation principle before `test` builds the harness. It carries no language
  authority. *Class:* maintenance
  check for `user/`. A failure blocks the doc's claim; a compiler that
  departs from the spec is intake. *Owner:* `test` (harness), `docs`
  (classification and new guides).
- **M-4 — the session-lock and live-reload demo** replays green against the
  final binary, with file saves driven by the demo player. *Class:*
  maintenance. *Owner:* `test`, in Phase 6b.
- **M-5 — demo narration.** `optimization.demo` narrates borrow elision and
  static uniqueness, which U′ retires; its narration is re-read after U′.
  Demos that show a recovered panic are rewritten. *Class:* maintenance.
- **M-6 — audit R11 records.** `test` repairs the guards' `// defect:` lines
  and owed `fixed=` stamps; `qa` refreshes
  [memory-safety coverage](memory-safety-coverage.md) §5 after U′ lands.

## 4. Traceability band

`qa` restores each row after `test` reports the walk of its backlinks:

- `spec/12-runtime.md` §12.4.3, §12.7.2.1 (three rows), §12.7.3; the
  headings §12.7.2, §12.7.4–§12.7.4.2, §12.7.5, §12.7.8 and §12.7.9, tagged
  `[S123]`.
- `spec/10-io.md` §10.12.7 item 3 and §10.12.8 empty `select`.
- `repl/spec/05-error-presentation.md` §5.1 and §5.2 rows; the cited tests
  are compile errors and are expected to restore unchanged.
- `repl/spec/16-test-discovery.md` §16.2; `repl/spec/00-cli-invocation.md`
  §0.8; `repl/spec/14-file-watching.md` §14.9; `repl/spec/17-embedded-agent.md`
  §17.4, §17.10.1 and §17.10.2, tagged `[S123]`.

K6 C3 and C4 (`spec/10-io.md` §10.10.1, `spec/08-modules.md` §8.9.3) carry
with their realisation; their annotations stay as they are.

## 5. Named residuals

`sprint` presents these at the Phase 4 checkpoint; each needs the user's
acceptance.

| Residual | Why not evidenced end to end | What covers it |
|---|---|---|
| TTY consent yes leg (R-2) | Piped input declines by design; no pty harness | `dev` unit row |
| A test child dying by signal (T-6) | No legitimate program raises a signal | `dev` scripted rows |
| A REPL test child writes no cache | Indistinguishable from the REPL's own writes | `dev` unit row 8 |
| Crash-consistent writers (P-17) | No controllable mid-write exit | `dev` rows; arch §1.7 falsifier |
| The agent-free build between lane runs (A-5) | The lane is not continuous | Lane at every listed trigger; low harm |
| Linked worker count ignores `RAYON_NUM_THREADS` | No program observes the pool size | `dev` row (B-5) |
| A platform sees the launch environment | No platform in the suite reads it | Structural: the stub does not mutate the environment |
| Stack overflow panic row (§12.7.2.1) | Implementation-defined message | Unchanged `[S18]` |

## 6. Completion criteria

- Every **RED now** cell, and every C-1 and C-3 re-pointed cell, was observed
  failing on its clause before its fix, and passes on a fresh build of the
  final tree; K-1 to K-5 remain failing-not-ignored unless fixed.
- No committed test asserts recovery after a panic, uses
  `catch-runtime-error`, or sets a runtime switch only on a linked program's
  run (C-1, C-2, C-5 censuses empty).
- U-8's numbers are recorded with both binaries' sha256 and put to the user.
- `test`'s clause map covers every condition here; `qa` accepts it before
  `dev` builds on it.
- Every §4 row is restored or carried with a record.
- `python3 .agents/tools/check_documents.py --root . --config standing-documents.toml`
  exits 0.

## 7. Dispatch

- **`test`, now (Phase 5, test-first):** E-0's declaration and detection
  proof with the loader change-set; the C-1, C-2, C-3, C-5 and C-9 re-points;
  every **RED now** cell; U-1 to U-5; P-1 to P-12, P-18 and P-19; T-1 to
  T-5; E-1 to E-6; B-1 to B-4; A-1 to A-6; R-1 to R-4; K-1 to K-5; M-1. Then
  C-6 and C-7 in their change-sets, M-3 with `docs`, M-4 and M-5 in Phase 6b.
- **`dev`, with each surface:** U-6, U-7's structure, U-9; P-10's unit rows,
  P-13 to P-17, P-18's guard rows; T-6; E-7; B-5; A-5's flag function; R-2's
  consent row and R-4's worker rows; M-2.
- **`qa`:** U-8, U-10, M-1's post-suite census, M-6's §5 refresh, §4.
