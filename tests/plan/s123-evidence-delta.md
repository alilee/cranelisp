# S123 evidence delta

> **Owner:** `qa`. **Readers:** `test` and `dev`, dispatched against it;
> `sprint`, sequencing it; `review`, checking delivered evidence against it.
> **Authority:** the [S123 sprint plan](../../sprints/archive/sprint-123.md) scope and user
> rulings; `spec/12-runtime.md` §12.4.3 and §12.7; `spec/10-io.md` §10.12.7–
> §10.12.8; `spec/appendix-a-builtins.md` (`checked-quot`); `repl/spec/00-cli-invocation.md`
> §0.5.6, §0.6 and §0.8; `repl/spec/14-file-watching.md` §14.9;
> `repl/spec/16-test-discovery.md` §16.2 and §16.6; `repl/spec/17-embedded-agent.md`
> §17.4 and §17.10; `repl/spec/18-redefinition.md`. Designs:
> [panics and environment](../../design/arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics),
> [uniform counting](../../design/backend/uniform-counting.md),
> [backend §7](../../design/backend/backend.md#7-runtime-failure),
> [process lifecycle](../../design/intrinsics/process-lifecycle.md),
> [environment](../../design/int/environment.md),
> [int §16.0](../../design/int/int.md#160-open-binaryint-obligations-verified-against-source-2026-09-21),
> [test runner §6.5](../../design/int/test-runner.md#65-the-test-child),
> [session transaction §2.5 and §5.2](../../design/int/session-transaction.md#52-no-symbol-is-left-broken),
> [REPL lifecycle §1.2](../../design/int/repl-lifecycle.md#12-poll-and-reload),
> and the S123 API packet (retired; in Git history).
> **Checkpoint:** HEAD `b35bfb87`, 2026-11-15; design citations verified
> against the designs committed there. §3.2, §3.3 and M-2 were re-verified
> against the W1 tree on 2026-11-15; §3.9 against the W2 U′ tree on
> 2026-11-16; §3.4 E-0 against nextest 0.9.140 on 2026-11-16; §3.6 R-2
> against the 2026-11-16 deletion ruling at `bc57cbf1`; §3.6 R-5 and the W4
> adequacy against the W4 working tree on 2026-11-16; §8 against the W5
> integrated gate at `b89cc7cc` on 2026-11-16; §3.7 K-6 against `390201c3` on
> 2026-11-16; §8.11 against `de20a40e` on 2026-11-16.

Each design's "evidence conditions for `qa`" is a proposal; this record is the
allocation. Condition IDs are local to this record.

## 1. Readiness

**Verdict: ready.** Every changed surface is testable through an existing
or named observation seam, and no ambiguity blocks evidence.

### 1.1 The stdlib runner carries no panic isolation

- **Ruling** ([S123 sprint plan](../../sprints/archive/sprint-123.md), user rulings at the
  Phase 3 → 4 checkpoint): the in-language runner `stdlib/testing/runner.cl`
  drops panic isolation. `cranelisp --test`'s supervisor, which restarts its
  child after a panic, is the isolation (T-1 to T-6). The P1 change-set is
  unblocked.
- **Consequence.** A panicking test in a direct in-language run ends the
  process like any other panic (§12.7.4): the tests after it do not run and
  no tally prints. T-7 evidences it.
- **Language-facing rewrites.** P1 removes `catch-runtime-error`, which
  `stdlib/fn/result.cl`, `stdlib/testing/runner.cl`, `exemplar/main.cl`,
  `examples/32-concurrency-combinators.cl` and `tests/fixtures/web_fanout/main.cl`
  import. Between P1's landing and the W1 `stdlib/`, `exemplar/` and
  `examples/` rewrites, `stdlib_conformance::stdlib_all_public_modules_compile_and_run`,
  the exemplar tests and `examples` fail on the unbound name. That failure is
  expected inside W1, not a regression; W1 closes only with them green (T-8).

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
- **Unstated wordings.** The banner text and the dormant notice are not
  fixed by `spec`. Cells assert the named file, the
  state word (`active`, `dormant`, `off`, `not built in`) and the named
  variable or value only.
- **The U′ cost rule** (U-8) is this record's operational reading of the
  user's "no cost cliff, and the exemplar within the same order of magnitude".
  `sprint` presents it at the Phase 4 checkpoint for the user to confirm.

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
| C-10 Retired mechanisms | `CRANELISP_CAPTURE_BORROW` (`s99_fixtures.rs`), borrow-elision and static-uniqueness CLIF assertions, the consuming-claim cells | Delete in the change-set that retires the mechanism; the change-set report names each deletion. Members on the U′ tree are ruled in §3.9 (C-10a) | — |

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
  - *L4 fixture:* `(defn go [n p q] …)` forwarding the parameter `p` into
    `q`'s slot, bare, `(go (add-i64 n -1) p p)`, and through a branch,
    `(go (add-i64 n -1) p (if (eq-i64 n 1) p q))`. Each control changes only
    that argument, to `q` and to `(if (eq-i64 n 1) q q)`. At `f5822487` both
    subjects stop armed on a stale release and both controls balance. In
    the CLIF the frame increments only `q` at entry, so the forwarded `p`
    reaches a slot released at the jump and at exit with no reference of
    its own; the mechanism is L4's. With moves off the bare subject also
    stops: that face belongs to the analysis-off lowering U′ replaces. The
    bare subject also discriminates a U′ lowering that moves `p` before its
    duplicate.
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

The P cells for language panics observe: exit status non-zero and not by
signal; stderr holding exactly one line matching `error: runtime panic: `
then an optional `<file>:<line>: ` then the message; for the REPL, a marker
form after the panicking one producing no output and no further prompt.
"Every mode" is the REPL, `--run` and `--link`. A platform dispatch fault is
not a language panic and has its own report shape (P-7).

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
  `vec-get` and `vec-set` out of range: each message exact, `--run`; the
  existing `vec_set_*` cells re-pointed (C-1). The runtime match face is
  reached through an IO value built by `bind`, because exhaustiveness
  checking rejects every other incomplete match; its matched twin is the
  control. `Int.MIN / -1` wraps to `Int.MIN` without a panic (§12.7.3, user
  ruling 2026-11-15), in a direct call and through a function value, in every
  mode; each compares the full quotient with `Int.MIN`, and the same shape
  with divisor `1` is the control. *Wrong:* a panic or hardware signal on
  `MIN / -1`; a quotient other than `Int.MIN`, including one sharing its low
  exit byte; the inline division and `div-i64` disagreeing. *Class:*
  acceptance. *Owner:* `test`, with `dev`(backend) and `dev`(primitives) unit
  rows.
- **P-4 — concurrent sources.** A panic in a spark, a `Par` branch, a
  detached strand and an empty `select` each ends the process with its
  message. Two sparks panicking with distinct messages produce exactly one
  report, whose message is one of the two. *Wrong:* a worker panic ferried
  to a join and resumed; two reports. *Fixture:* in each spark cell the
  panicking computation is itself the sparked one, and a non-panicking twin
  of the same program reports `[SPARK_STATS] spawns=` at least 1 (at least 2
  for the two-spark cell). A fixture whose panic runs on the calling thread
  cannot see either wrong outcome. `--run`, plus the REPL for empty `select`.
  *Class:* acceptance. *Owner:* `test`.
- **P-5 — output before the panic is delivered first.** `print` output and
  a prior REPL result precede the report on one merged stdout/stderr pipe.
  *Wrong:* exit without flushing host output. `--run` and the REPL.
  *Class:* acceptance. *Owner:* `test`.
- **P-6 — a panic during macro expansion ends the process** in `--run` and
  the REPL with its message, not an expansion compile error, and the REPL
  evaluates nothing after. *Class:* acceptance. *Owner:* `test`.
- **P-7 — a platform dispatch fault ends the process** (§12.7.6; the
  Phase 3 → 4 user ruling that dispatch faults report without the panic
  prefix; [process lifecycle §1.1](../../design/intrinsics/process-lifecycle.md#11-one-terminator)).
  The `boom` and `test-capture` `fault-now` fixtures, every mode: exit
  non-zero and not by signal; exactly one stderr line naming the platform
  function's FQ name, which also carries the platform's fault text; no stderr
  line beginning with `error: runtime panic: `; the fault text absent from
  stdout; in the REPL, no later marker evaluated and no further prompt. The
  DLL's own panic hook prints the fault text first, from the DLL's runtime
  ([platform §4.2](../../design/platform/platform.md#42-effect-forcing)), so the stderr line count
  is not asserted. Connective wording such as `dispatch failed` is not fixed
  by `spec` and is not asserted. *Wrong:* `PlatformError::DispatchError`
  returned and the REPL continuing; the fault reported with the panic
  prefix; two reports. *Limit:* an eligible test returns `(Option String)`
  and cannot force a platform effect, so no `--test` cell can raise a dispatch
  fault in a test child. The supervisor's classification of a status-1
  ending without a prefixed line as a failure is
  [test runner §10](../../design/int/test-runner.md#10-unit-test-design)'s
  `dev` row (T-6). *Class:* acceptance. *Owner:* `test`.
- **P-8 — negative leg.** A program with no panic prints no report and exits
  with its result; the P-1 in-range control (C3) carries it in every mode.
- **P-9 — `catch-runtime-error` is removed.** A reference is an unbound-name
  compile error in every mode. *Class:* acceptance. *Owner:* `test`.
- **P-10 — `checked-quot`.** `None` for a zero divisor and for `MIN / -1`;
  `Some` truncated toward zero otherwise (`7 / -2` and `-7 / 2` give `-3`);
  no panic. `--run` and REPL display `(Option Int)`. *Wrong:* panicking,
  floor division, `MIN / -1` wrapping to `Some`. *Detection:* the primitive
  does not exist before its change-set, so the committed cells fail on the
  unbound name, which is not a clause red. The fixture values carry the
  discrimination: each wrong implementation yields a different observable
  (a panic report for `None`, `Some -4` for `Some -3`, `Some` of `MIN` for
  `None`). The cells aggregate per-clause failures, and they are accepted
  when they pass on the implementing build. `dev`'s unit rows are observed red
  first. *Class:* acceptance. *Owner:* `test`, and `dev`(primitives) unit rows.
- **P-11 — `poll-pool` survival fixture** becomes a process-exit fixture.
  *Owner:* `test`.
- **P-12 — trace sinks flush on a panic exit**
  ([observability §7.1](../../design/int/observability.md#71-process-exit-and-panic-wiring)):
  one `--run` cell whose trace dump, captured from the child's stderr to a
  file, holds the pre-panic events. It passes before the terminator lands and
  guards the exit path that would bypass the flush. *Class:* acceptance.
  *Owner:* `test`.
- **P-13 — exit-time diagnostics** (`dev`, intrinsics, child process). M3
  parity armed with a panic exits with the panic status and one stand-down
  line, not an abort; `[RC_STATS]` still prints. *Class:* safety fence.
- **P-14 — the terminator** (`dev`, intrinsics). Report composition per
  fault kind, one line for every payload; claim-once as a pure transition;
  child-process cells for status and report, ordering and two simultaneous
  raisers. *Detection proof:* a terminator that returns turns the ordering
  and one-report cells red. *Limit:* the two-raiser cell detects a skipped
  claim only when both threads reach the report together (two of three runs
  under the planted fault); the pure transition row is the deterministic
  evidence for claim-once, and the cell is a diagnostic observer of its
  wiring. *Class:* safety fence.
- **P-15 — no reachable code after a raise** (`dev`, backend). CLIF
  structure rows: each site (match, division, Vec bounds, trap stub) emits
  the call and the terminator through one helper. *Grade:* measured for the
  emitted shape of each site. The single-emitter claim is
  asserted with a named falsifier: the source census matches a
  `declare_func_in_func` whose first argument is spelled with `panic`, so an
  emitter reaching the `FuncId` through another name passes it. *Falsifier:*
  a `runtime/panic` `FuncRef` made outside `raise.rs`, or an emitted
  `runtime/panic` call followed by reachable code. The structural form needs
  a wrapper for `CompileContext::panic_func_id`, an `arch` API decision.
  *Class:* safety fence.
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
  line, with no `codegen error` and no `0..0`. *Class:* acceptance.
  ACT-1036's RED (`spec_10_io::batch_main_non_io_return_refusal_is_located_at_main`)
  is a compile-time refusal raised in `src/exe.rs::classify_main_return_type`
  at a synthetic span; the panic terminator does not reach it, so it flips
  only with its own location fix.

### 3.3 The compiler test runner

- **T-1 — a panicking test does not end the run.** Tests `a` pass, `b`
  panics, `c` pass, under `--test` and `/run-tests`. *Observed:* `ok`,
  `PANIC: <message>`, `ok` in FQ order, each FQ exactly once; the summary
  counts the panic as a failure; `--test` exits 1; after `/run-tests` the
  REPL evaluates a marker form. *Wrong:* an in-process runner (REPL dies, `c`
  absent); a restart re-running `a`; the panic counted as a pass.
  **RED now** for the `PANIC:` message and its single forwarding to stderr.
  The REPL marker passes before the terminator lands and turns red if an
  in-process runner meets it. *Class:* acceptance. *Owner:* `test`.
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

- **T-7 — a direct in-language run ends at a panicking test.** The C-2
  rewrite of the former `discover_tests_and_catch_runtime_error_user_composition`, now `discover_tests_direct_run_stops_at_panicking_test`,
  stdlib-free: in the REPL, user code calls the `discover-tests` callables of
  `a` (passes), `b` (panics) and `c` (prints a marker) in order. *Observed:*
  `a`'s result, then the panic report on stderr, a non-zero exit that is not
  a signal, no `c` marker and no evaluation of a later form. *Wrong:* a
  runner that survives the panic, through a retained catch or an in-process
  recovery; `c` running. **RED now.** *Class:* acceptance. *Owner:* `test`.
- **T-8 — the rewritten stdlib runner** (`dev`, stdlib). The runner's
  self-tests (`stdlib/testing/runner/test.cl`) pass with no panicked
  outcome, and `stdlib_conformance::stdlib_all_public_modules_compile_and_run`
  is green at W1 close. *Class:* acceptance at the module layer for the
  rewrite.

T-2 to T-5 and T-7 are acceptance and `test`'s.

### 3.4 Environment supply and baked switches

- **E-0 — the suite never reads a developer's files or activates a provider.**
  *Harm:* REPL source sent to a live endpoint; results changed by a local
  file. *Declaration:* the nextest setup stage exports
  `CRANELISP_NO_ENV=1` and an empty `CRANELISP_AGENT_PROVIDER` to every test
  through `$NEXTEST_ENV`. On nextest 0.9.140 the exports reach tests and
  their children, and an empty value arrives set and empty, overriding a
  shell value (probed 2026-11-15; the empty value re-probed 2026-11-16). It
  lands in the loader's change-set. `tests/helpers/marginal.rs` already
  clears the environment.
  - *Two exports, two leak paths.* `CRANELISP_NO_ENV` stops a developer's
    files. The empty provider stops a provider exported in the developer's
    shell, which no loader control governs, and under E-2's precedence it
    also outranks a file-supplied provider. A provider observable therefore
    cannot show the file leak while the empty export stands, so each export
    is proven against its own path.
  - *Declaration cell:* the test process sees `CRANELISP_NO_ENV` as `1` and
    `CRANELISP_AGENT_PROVIDER` as set and empty.
  - *Isolation cell:* a child that inherits the suite environment, with
    `XDG_CONFIG_HOME` and `HOME` pointing at fresh directories holding a
    user file, and a project `.env` in its own directory. Both files set
    `CRANELISP_RC_STATS=1` and select `stub` with a loadable script. `--run`
    prints no `[RC_STATS]`, and the REPL banner is dormant.
  - *Detection proof, plant 1:* remove only the `CRANELISP_NO_ENV` export.
    The declaration cell fails, and the isolation cell's `--run` prints
    `[RC_STATS]`. Its banner stays dormant, as E-2 requires of the empty
    process value; the proof records that reading, and an `active` banner
    under this plant is a precedence defect, not a detection.
  - *Detection proof, plant 2:* remove only the empty provider export, and
    launch nextest from a shell exporting `CRANELISP_AGENT_PROVIDER=stub`
    and `CRANELISP_AGENT_STUB_SCRIPT`. The declaration cell fails, and the
    isolation cell's banner is `active`. Its `--run` still prints no
    `[RC_STATS]`, because the files stay unread.
  - *Controls:* with both exports, the same shell leaves both cells green,
    which shows the export overrides the shell value on the delivered tree.
    With no plant and no shell values, both cells are green.
  - The file legs observe the loader and the banner, so the plants run
    against `dev`'s `src/` change-set before `review`. Before the loader
    exists the isolation cell cannot fail, and only the declaration cell's
    plants are observable.
  - Cells that need a file read or an unset provider remove the inherited
    export in their own child, as environment §2.4 requires of loader tests.
  - *Limit:* other switches exported in the developer's shell still reach
    the suite. They are process values, not files.
  - *Class:* safety fence. *Owner:* `test`.
- **E-1 — a project `.env` supplies a switch.** `CRANELISP_RC_STATS=1` in
  `.env` prints `[RC_STATS]` in `--run`, `--test` and the REPL; control: no
  `.env`. *Class:* acceptance. *Owner:* `test`.
- **E-2 — precedence.** With `CRANELISP_AGENT_PROVIDER` as process `stub`,
  `.env` `bogus1` and user file `bogus2`, the banner is active naming `stub`.
  Without the process value it is dormant, and `/ask`'s dormant notice names
  `bogus1`; without both, `bogus2`. An empty process value wins: dormant, and
  the notice names the variable. The banner carries the state word and an
  active provider; a dormant reason is observed in the notice (§1.2,
  unstated wordings). "Without the process value" removes the suite's
  inherited empty export, and every leg removes `CRANELISP_NO_ENV` (E-0).
  *Wrong:* files over the environment; user over project;
  an empty value treated as unset. *Class:* acceptance. *Owner:* `test`.
- **E-3 — user file location.** `XDG_CONFIG_HOME/cranelisp/env` is used and
  `HOME/.config/cranelisp/env` ignored when `XDG_CONFIG_HOME` is set; `HOME`'s
  file is used otherwise.
- **E-4 — admission.** A `.env` key `S123_FOREIGN=x` is absent from `/sh`'s
  environment; `CRANELISP_S123_PROBE=y` from the same file is present.
- **E-5 — loader controls.** `CRANELISP_ENV_FILE` and
  `CRANELISP_USER_ENV_FILE` each redirect only their file;
  `CRANELISP_NO_ENV=1` reads neither; a file line setting a control is
  ignored. Every leg except the disable leg removes the inherited
  `CRANELISP_NO_ENV`; the disable leg sets it explicitly.
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

**Acceptance of `test`'s W3 cells, 2026-11-16.** The source is
`.local/s123-w3/test-evidence.md` (§W3 resumed). Every observed RED failed on
a clause assertion; none failed on setup.

- *Accepted:* E-0's declaration cell and its two detected plants, and its
  isolation cells (file leg vacuous until the loader lands, as §3.4 says);
  E-1; E-2's process leg; E-3's XDG leg; E-4; E-5; E-6; B-1 to B-4 with the
  spark capability control; A-1's dormant, active and off legs after the
  return below; A-2; A-4; A-5's lane; A-6's membership cell. The `stub`
  active leg requires the banner to name the configured
  `CRANELISP_AGENT_MODEL`, which is §0.6.1's "provider and model" for `stub`.
- *Returned to `test`; each fails a conforming build:*
  - `environment_supply::home_file_supplies_without_xdg`: the harness
    applies every `env_remove` before every `env`, so `base()`'s
    `XDG_CONFIG_HOME` survives the removal. The child reads an empty XDG
    tree and never reaches `HOME`. The leg must start without
    `XDG_CONFIG_HOME`.
  - `agent::s123_defaults::state` and `batch_modes_have_no_agent_state_neg`
    require the word `agent` on the state line, which §1.2 does not fix. A
    line without it fails the REPL cells and passes the batch negative
    vacuously. Count state lines in the REPL prologue, before the first
    prompt, by state word only. The batch negative compares against the
    state line the same environment prints in the REPL, on both streams.
    A-3's `/ask` notice would otherwise count as a second state line.
  - `unknown_provider_is_dormant_and_names_value`, and E-2's `bogus1`,
    `bogus2` and empty legs, read the dormant reason from the banner. Read
    it from `/ask`'s notice (E-2 above); the banner asserts the state word.
- *Owed, in `dev`'s order:* nothing is observable at the intrinsics step
  beyond B-5's `dev` rows. After the `src/` loader lands, rerun E-1 to E-6
  and B-1 to B-4 green, including the masked clauses (E-5's companion-file
  counter, E-6's file and line, A-1's model and count, A-3's notice and
  trace, A-4's off order), and return any masked clause that does not
  discriminate. After the agent default and banner land, and before
  `review`, run E-0's isolation plants (§3.4). After the Cargo default
  changes, run all of `tests/agent.rs` in the default build with the stub
  and no network (A-6) and the agent-free lane (A-5). C-6's transcript
  re-baseline follows A-1 green in the same change-set.

**W3 adequacy, 2026-11-16: adequate with named residuals.** The tree is
`3bdf398e` plus the uncommitted W3 work, after review R1–R4 and P14. The full
suite (`.local/s123-w3/qa-full-suite.log`) ran 6,993 tests: 6,960 passed,
33 failed, 1 skipped.

- *Met.* E-0's plants each fail their own export's legs, and the controls are
  green: the `NO_ENV` plant leaks `[RC_STATS]` with the banner dormant, and
  the provider plant makes the banner `active` with the files unread
  (`.local/s123-w3/post-e0-*.log`). In the default build the suite passes
  E-1 to E-6, B-1 to B-4 and the R1 and R2 cells (`environment_supply`
  32/32), and A-1 to A-4 and A-6 (`agent` 91/91). The agent-free lane passes
  A-5 (`p14-lane-agent-free.log`, 23 passed). The golden transcripts pass on
  the new banner, which is C-6. E-7 and B-5 have their module rows.
- *The three §0.8 readings of 2026-11-16.* The implementation conforms to all
  three, and each clause now has a discriminating `dev`(src) module row in
  `src/env_files/tests.rs` (`.local/s123-w3/gaps-unit.log`, 27 passed;
  `gaps-e2e.log`, `environment_supply` 32/32):
  - **Exactly `1`.** `no_env_values_other_than_exactly_one_leave_loading_enabled`
    keeps loading enabled for `true`, the empty string, ` 1`, `1 `, `01` and
    `0`, which rejects a truthy, trimming or numeric reading.
  - **After a closing quote.** `a_comment_may_follow_a_closing_quote_without_whitespace`
    accepts `'v'#c` and `"v"#c`, which rejects a reading that needs
    whitespace before `#`. `text_after_a_closing_quote_is_a_located_error`
    refuses text after a double-quoted value, single- and multi-line, on a
    foreign key and on `ANTHROPIC_API_KEY`, with the line and no value.
  - **The NUL error names the key.** `the_nul_refusal_message_names_the_key_without_its_value`
    asserts the rendered message carries the file, line and
    `ANTHROPIC_API_KEY`, and none of the value, its suffix or the NUL.
- *REDs.* 32 are filed guards, the same set as at W2's close: the twenty
  listed in §3.10 and ACT-1050's twelve `bind_unused_heap_argument` cells.
  None turned green. The 33rd,
  `repl_persist::watch_idle_unreadable_save_locks_before_the_next_definition_overwrites_it`,
  passed five isolated reruns. In the failing run the definition was admitted,
  with the write chokepoint's warning, the bytes were kept, and the lock
  reported one turn late. That is the late-event limit
  [REPL lifecycle §1.2](../../design/int/repl-lifecycle.md#12-poll-and-reload)
  names. The `Stage::Write` stage sends the next line without waiting for the
  watcher, so the fixture lacks the idle interval the cell's §14.2 clause
  assumes. W3 changed neither the poll nor the stage, so this is not a W3
  regression. It is an ordering race between event delivery and the next
  line, with two candidate owners. *Provisional attribution:* `test`, if the
  stage must wait for delivery so the cell observes an idle save. The
  alternative is `design`(int), if §14.2 requires the reload regardless of
  delivery latency, which the accepted limit does not meet; `spec` then
  frames that for the user. *Refuted if* the cell fails in isolation, or a
  stage that waits for delivery still admits the definition. *Owner:* `qa`
  intake, an action routed to `test` first.
- *§4.* `repl/spec/00-cli-invocation.md` §0.8's rows are restored, and its
  heading is `[Tested]`, the grade of its dialect rows. One clause has no
  cell: that a compile-time build variable in a file is not a runtime
  setting.

### 3.6 REPL carries

- **R-1 — ACT-1047.** The committed FC-1 cell and its controls stay. New load
  leg: after the external save, `(k)` gives 9 and the final file holds `k`
  and `h`. A mid-session file that fails to compile locks the session and
  keeps its bytes. **RED now** (load leg). *Class:* acceptance. *Owner:*
  `test`.
- **R-2 — deleted backing file** ([§14.9](../../repl/spec/14-file-watching.md#149-backing-file-appearance-and-deletion),
  second paragraph; [REPL lifecycle §1.2](../../design/int/repl-lifecycle.md#12-poll-and-reload),
  "A deleted backing file needs nothing").
  - *Harm:* a deletion read as a change or a failure unloads live
    definitions, locks the session, or regenerates from a reset module, so
    source the user holds only in the session is lost. R-1's watcher change
    is the likeliest way to introduce it.
  - *Wrong implementations:* the deletion resets the module, so a later
    `(g)` fails or the recreated file lacks `g`; the deletion locks the
    session; regeneration skips a file whose record predates the deletion,
    leaving it absent; recreation asks `[y/N]`, which in a piped session
    consumes the next line.
  - *Seam:* the piped REPL; `Stage::Remove` at a prompt, the idle wait, then
    turns; `user.cl` read after exit.
  - *Cell:* `(g)` gives 1 before and after the deletion; `(defn h [] 2)` and
    `(defn i [] 3)` are live; the session exits 0; no `[y/N]` prints; the
    final file holds `g`, `h` and `i`. No `// defect:` line: the checkpoint
    binary conforms, so the cell is green with no pre-fix red.
  - *Controls:* the same deletion with no definition leaves the file absent
    and `g` callable, which proves the removal is real and that the
    definition causes the recreation. A file restored before the next
    definition is reloaded, and persists with the later definition.
  - *Not asserted:* the absence of a deletion notice. §14.9 requires none
    and forbids none; the lifecycle design's "prints nothing" is a module
    row.
  - *Class:* acceptance, and the safety fence for R-1's change. *Owner:*
    `test`. Required now.
- **R-2a — rename-over save.** An editor's save that writes a temporary
  file, removes `user.cl` and renames the temporary over it is an ordinary
  save ([§14.2](../../repl/spec/14-file-watching.md#142-eager-recompilation)).
  *Harm:* a watcher that loses the event, or reads the removal as an
  appearance or a reset, lets the next definition overwrite the save.
  *Cell:* `(g)` gives the saved 7, and after `(defn h [] 2)` the final file
  holds `(defn g [] 7)` and `h`. *Class:* acceptance. *Owner:* `test`.
  Required now.
- **Placement (R-1, R-2, R-2a; ACT-1051).** Every cell that writes, removes
  or renames a file at a prompt waits idle before its next line, the
  `idle_save_then` cells included. The REPL prints nothing before its
  pre-turn poll, so no output can be awaited. The wait is placement, not
  proof of delivery. *Falsifier:* such a cell failing with the wait in
  place, which routes to `design`(int) under ACT-1051's attribution.
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
- **R-5 — cached restarts keep GOT capacity** (W4 review R1;
  [session transaction §7.5](../../design/int/session-transaction.md#75-got-exhaustion):
  a restart consumes no capacity; §8.2 entry slot preload;
  [§0.6](../../repl/spec/00-cli-invocation.md) `--no-cache` bypasses an
  acceleration).
  - *Harm:* an unchanged program that compiles stops compiling after a fixed
    number of cached launches, in every mode, and only `--no-cache` recovers
    it; `--link` cannot take `--no-cache`.
  - *Attribution (confirmed, 2026-11-16, W4 tree binary):* R-4's preload
    retires every persisted minted instance with `retire_abi_changing`, and
    the tombstones persist. Seam: `retired_slots` in the entry's
    `.meta.json`. With 128 generic identities and concrete callers, five
    cached launches persisted 645 tombstones (5 × 129: each instance and
    `Pure`'s); the seventh launch exhausted 1,024 slots. Control: 128
    monomorphic functions of the same shape persisted one tombstone per
    launch, all `Pure`'s instance, and stayed callable through ten launches.
    Refuted if a build without the preload retirement grows the same way.
  - *Wrong implementations:* tombstone per launch (current); per-launch
    growth smaller than `k + 1`; dropping the retirement, so a preloaded
    instance keeps a slot with no code (R-4's six cells, below).
  - *Cell* (`tests/cache.rs`): 300 generic identities, each with a concrete
    caller; `main` returns `(add-i64 (use0) (use7))`. Legs on one project:
    `--no-cache --run` gives 7 and writes no cache; cold `--run` gives 7 and
    writes the cache; cached `--run` gives 7; cached `--link`, whose
    executable gives 7; piped REPL `(use7)` gives `:primitives/Int 7`; cached
    `--run` gives 7. Measured: the third launch exhausts now.
  - *Fixture property:* a leak of `k + 1` slots per launch must exhaust by
    the third launch while `2(k + 1)` slots fit. At `GOT_TABLE_SIZE` 1,024
    that bounds `k` to 256–340. The cell comment names the dependency.
  - *Arming:* each leg asserts its exit status and output separately and
    shows stderr. The red must fail on the third launch with "GOT slot table
    exhausted". A `--no-cache` failure or a missing cache directory is a
    fixture error, not the red.
  - *Fence:* R-4's preload cells stay green —
    `tests/repl_persist::{persist_bad_import_then_run_succeeds_e2e,
    persist_bare_expr_then_run_module_clean_e2e,
    persist_macro_defining_macro_use_survives_restart}` and
    `tests/spec_07_traits::return_type_dispatch_{annotation_context,
    float_impl_selected,argument_context}_all_modes`.
  - *`dev` unit row* (`src/session_v4/lifecycle.rs`): three sessions over
    one cache and unchanged source with `k` minted instances. After the
    second and third, the persisted `retired_slots` and the slot high-water
    equal the first's. Each authored definition keeps its slot, and each
    instance has code. The row replaces the `retired_slots` growth assertion
    in `preload_releases_the_bodies_the_recompile_restages` (named
    `preload_retires_the_bodies_the_recompile_restages` in the red run), which
    pinned the defect. It must be observed failing on the count before the fix. The
    existing in-session ABI-changing tombstone rows stay green.
  - *Not asserted e2e:* the tombstone count. It is cache-internal; the unit
    row owns it.
  - *Class:* acceptance (cell), safety fence (R-4 cells). *Owner:* `test`
    (cell), `dev` (unit row). Required now; **RED now**.
  - *Accepted, 2026-11-16:* `tests/cache.rs::cached_restarts_keep_generic_instance_slot_capacity_across_modes`.
    It fixes `k` at 300 and runs the six legs in plan order. Every leg
    asserts its exit status and output and prints stderr, and the two
    fixture-error guards hold. The RED is "GOT slot table exhausted" at
    cached `--link`, the third cache-enabled launch, after the `--no-cache`,
    cold and cached `--run` legs passed (`.local/s123-w4/r5-red-final.log`).
    The six R-4 fences pass (`.local/s123-w4/r5-fences.log`). The REPL and
    final `--run` legs are not reached before the fix. They count only
    when they pass on the fixed build (§6). Before commit, `test` repairs the
    sizing comment's broken last sentence ("leaks are belong to").

**W4 adequacy, 2026-11-16: adequate, with one RED to clear before the commit.**
The tree is `bc57cbf1` plus the uncommitted W4 work, after every W4 review
and the P15 comment fix. The full suite (`.local/s123-w4/qa-full-suite.log`,
133 s) ran 7,000 tests: 6,969 passed, 31 failed, 1 skipped.

- *Met: R-1 to R-5, R-2a and the refusal cell.* Every cell and control
  named above passes on this build. That includes R-5's REPL and final
  `--run` legs, which the red run never reached, and R-4's six preload
  fences. The P-18 refusal pair
  (`repl_redefinition::template_only_caller_refuses_language_type_change_keeps_prior_callable`
  and its admitted control) passes. The golden lanes pass on the four-entry
  re-baseline, and `public_api_relocations` passes on the −26/+1 and −1
  baselines.
- *Met: the `dev` unit rows.* Each was observed red before its fix and
  passes in the full run.
  - ACT-1047 and ACT-1020's three persistence rows.
  - ACT-1035's `worker::tests::parametric_impl_turn_does_not_compile_live_sibling_impl`.
  - R-5's `cached_restarts_persist_no_new_tombstones_or_slots`.
  - P16's two `src/main.rs` rows.
  - The absent-dependent reload-plan row.
  - The template-caller guard, by a planted fault.
  - P15's refusal-restore row, by a planted mutation.
  - The backend RC probe rows, by inverting the probe.
  The red and green logs are `.local/s123-w4/dev-*.log`.
  ACT-1035's mechanism is confirmed: the control pair
  differs only in a concrete body in the same `begin`, and the worker row
  observes the seam.
- *REDs.* 30 are filed guards, all in W3's set:
  - ACT-1050, the twelve `bind_unused_heap_argument` cells.
  - ACT-0973 ×2, ACT-0985, ACT-0997 ×2, ACT-1001 and ACT-1016 ×3.
  - ACT-1018, `sudoku_warm_serial_solve_retains_nothing`.
  - ACT-1034 ×4, ACT-1036, and ACT-1038/ACT-1039 ×3.
  The 31st, `role_wiring::role_wiring_gate_detects_shared_and_local_faults_and_clears_a_sound_copy`,
  is a W4 consequence and not a product regression. The negative leg pins
  the clean copy's output to `26 principles`, and W4 adds
  `design/arch/principles/27-dev-tier-optimises-only-against-blow-up.md`.
  The gate reports 27 principles and 0 findings, so the instrument is
  working. Its count is stale. *Owner:* `test`, in the change-set that
  lands Principle 27. *Class:* maintenance check.
- *Turned green.* Two W3 guards:
  `repl_persist::persist_save_creating_backing_file_survives_definition`
  (ACT-1047) and `spec_07_traits::repl_concrete_impl_call_survives_later_parametric_impl`
  (ACT-1035). Five W4 REDs also turned green:
  `persist_appearing_backing_file_loads_before_definition`,
  `persist_appearing_bad_backing_file_locks_without_overwrite`,
  `cli_missing_entry::dotted_empty_entry_persists_at_mapped_path`,
  `spec_07_traits::repl_concrete_impl_call_survives_parametric_impl_only_begin` and
  `cache::cached_restarts_keep_generic_instance_slot_capacity_across_modes`.
  `test` stamped all seven `fixed=S123/91acf712`, with their comments in
  the past tense.
- *Not a W4 finding.* `tests/plan/spec_link_check.py` reports twelve
  `// spec:` anchors that do not resolve. Eleven are in
  `tests/projection_elision_guard.rs`, which cites sections 3.3 and 3.4 of
  the backend ownership-codegen design. HEAD's copy already lacks them. The twelfth
  is the two-target comment at `tests/environment_supply.rs:51`. These
  are `test`'s, as maintenance.
- *ACT-1052 carries; it does not block W4.* The hazard is unmeasured and
  predates W4. P15 releases preloaded instance bodies, not authored entry
  slots, so it neither causes nor widens the hazard. Reaching it takes a
  cached dependent of the entry, an ABI-changing edit reverted within one
  session, and a later cached launch. No W4 cell exercises that path. Its
  first act is a `qa` probe of the action's candidate on the final binary.
  If the probe reproduces it, `test` commits the RED, and `qa` attributes
  the owner from a control.
- *Closed, 2026-11-16: ACT-1047, ACT-1020 and ACT-1035.* Each central claim
  was re-read against source on the W4 tree, and each stamped guard passes
  (`.local/s123-w4/stamps2-guards.log`, 7 of 7).
  - ACT-1047: `CompilerSession::backing_file_changed_unseen` keeps a file
    with no record, and `register_entry_module` records an absent REPL
    entry. The load ruling is in REPL §15.1 and §14.9, and in REPL
    lifecycle §1.2.
  - ACT-1020: the absent REPL entry and the batch refusal both use
    `pipeline::project_root_candidate`, which applies §8.1's mapping. The
    ruling is in CLI §0.5.6.
  - ACT-1035: `worker::derive_codegen_batch` selects only staged bodies.
  - ACT-1035's last obligation, C1's REPL leg, moves to ACT-1034, whose
    control it is.

### 3.7 Committed REDs for carried defects

Each is failing-not-ignored at close unless its fix lands. Each names its
control.

| ID | Cell | Control | Fix in S123 |
|---|---|---|---|
| K-1 ACT-0997 | `(import [lib [(Box B)]])` binds `B` to `lib/Box`: a `B` value meets a `lib` function over `Box` in both directions, which a freshly minted type `B` fails. The self-rename `(Box Box)` is accepted | The unrenamed import | No (packet B1, S124) |
| K-2 ACT-1016 | Face 1: a session's reload accepts a module that a restart on the same files fails. Face 2: an `export`-closed cycle is reported as a cycle at startup and under `--run`. Face 2's reload leg passes and is a regression guard | Face 1's twin defining `(defn g2 [] (a/f))`; face 2's acyclic re-export | No |
| K-3 ACT-1017 | Prefix: a failed-import refusal repeats no category-and-span prefix, under `--link` and in the reload notice. Location: the refusal is located in the failed module's file and never at its offset in the dependent; this face passes and is a regression guard | A refusal of a non-failed import | Prefix only |
| K-4 ACT-1001 P-3 | An `impl` of an ambiguous trait spelling is rejected as ambiguous, naming both | An unknown trait spelling is `unknown trait` | No |
| K-5 ACT-0973 | A platform declaration in a root-level non-entry module, and in a nested one, is a compile-time error | The entry placement loads the platform | No |
| K-6 ACT-1052 | A cached importer of a module whose slots moved in a REPL session, under unchanged text, gives the uncached result in every mode (below) | The ABI-preserving edit and revert; `--no-cache` | Not scheduled |
| K-7 ACT-1055 | `(import [m [Shade.Blue]])` binds bare `Blue`, and nothing else (§8.10) | `[Shade.*]` | Candidate (small, `src/` only) |
| K-8 ACT-1056 | An export mount re-exports and mounts; a member glob in a mixed list keeps its neighbours (§8.10) | The unmounted export; two separate module specs | No (`arch` gate with ACT-0997) |
| K-9 ACT-1057 | A macro clause with no fixed parameter and a non-`Sexp` body is rejected at its `defmacro` form (§8.10) | The quoted body; the `[x]` shape | Candidate (frontend) |

*Class:* acceptance (safety fence once fixed). *Owner:* `test`.

**K-6 — a cached importer embeds a slot its dependency moved**
([int §7.6](../../design/int/int.md#76-dependency-record-and-validity): an
importer's `.o` embeds its dependencies' GOT slot indices, and a cached module
restores only if every source its artefact derives from is unchanged;
[session transaction §7.1](../../design/int/session-transaction.md#71-the-commit-gate-is-the-single-slot-policy-authority):
an `AbiChanging` commit mints a fresh slot; §0.6 `--no-cache` bypasses an
acceleration).

- *Harm:* a program that runs correctly crashes in `--run`, in a linked
  executable and in the REPL after its developer edits a definition and
  reverts it. Only `--no-cache` or deleting the cache recovers it, and
  `--link` cannot take `--no-cache`.
- *Observed* (HEAD `390201c3`, `target/debug/cranelisp`, 2026-11-16): SIGSEGV
  (exit 139) in `--run`, in the linked executable, and at the REPL call
  through a `/mod`-loaded module. Seam: the restored `lib.o`'s `g` loads
  `__cranelisp_got_user` at offset 0, which is slot 0. `user.meta.json`
  holds `f` at slot 2 with slots 0 and 1 retired, and the manifest's
  recorded `user` hash equals the current one.
- *Wrong implementations:*
  - validation by dependency source hash alone (current);
  - a correction confined to the entry preload: the failing launch's `user`
    is a cache-restored dependency, not the entry;
  - a correction that covers `--run` but not the linked executable or a
    transitive restore under `/mod`;
  - a refusal or diagnostic where the uncached result is 41.
- *Fixture* (one project): `user.cl` holds `(defn f [] 41)`; `lib.cl`
  holds `(import [user [f]])` and `(defn g [] (f))`; `app.cl` holds
  `(import [primitives [Pure]])`, `(import [lib [g]])` and
  `(defn main [] (Pure (g)))`. `app` is the batch entry, so `lib` restores
  from cache without recompiling. `/mod lib` would recompile `lib` and mask
  the defect.
- *Legs, in order on one project:*
  1. Cold `--run app.cl` exits 41 and writes `lib.o`.
  2. Piped REPL on the default entry: `(defn f [] "s")` echoes
     `(Fn [] primitives/String) user/f`, then `(defn f [] 41)` echoes
     `(Fn [] primitives/Int) user/f`. `lib` is not loaded, so §18 admits
     both edits. `user.cl` is byte-identical to the fixture afterwards.
  3. `--no-cache --run app.cl` exits 41 (control).
  4. `--run app.cl` exits 41.
  5. `--link app.cl`; the executable exits 41.
  6. Piped REPL: `/mod app`, then `(g)` gives `:primitives/Int 41`.
- *Sibling control* (a second project, differing only in whether the slot
  moves): leg 2 enters `(defn f [] 42)` then `(defn f [] 41)`. The slot
  stays, and legs 4 to 6 give 41 on the current binary.
- *Arming:* each leg asserts its exit status and output separately and
  shows stderr. Collect the failing legs instead of stopping at the first,
  so all three faces report. The red must fail at legs 4 to 6 on a signal
  exit or a missing `41`. A failure at legs 1 to 3, a refused edit at leg
  2, a `user.cl` that differs from the fixture, or a missing `lib.o` is a
  fixture error, not the red.
- *Not asserted:* whether `lib` restores or recompiles. That is
  cache-internal; the correction's unit row owns it.
- *Notation:* `// defect: class=artifact-underkey
  locus=src/cache/dependency_record.rs::DependencyRecord found=S123
  owner=/dev`, with prose after the token: provisional until `design`(int)
  places the fix.
- *Class:* acceptance (safety fence once fixed). *Owner:* `test` (cell);
  `dev`'s unit row is allocated when `design` places the correction.
  Required now as a committed RED; the fix is not scheduled.

### 3.8 Maintenance and diagnostics

- **M-1 — ACT-1032.** No suite test writes under a checked-in path. The
  three identified writers copy their fixture to a fresh directory or pass
  `--no-cache`; the in-tree `.cranelisp-cache/` directories under `tests/`,
  `examples/` and `exemplar/` are purged before U-8, with the purge recorded.
  At the Phase 5 checkpoint `qa` runs `git status --ignored` after the suite
  and attributes any new cache. *Owner:* `test`. Required before U-8.
- **M-2 — ACT-1025, a fixture assumption.**
  `dispatch_without_a_stored_continuation_retires_nothing` asserts `user`'s
  terminal pool, naming it, before the requeue. *Class:* maintenance check
  for the worker module fixtures. *Owner:* `dev`.
  The product residual, a hand-off of the entry before its pool is terminal,
  is [int §6.1.2](../../design/int/int.md#612-the-entry-is-settled-before-the-eval-thread-owns-it)'s:
  one scheduler transition publishes in-memory completion and
  `TypecheckDone` together, so in-memory completion implies a terminal pool.
  That grade is structural for every session hand-off. *Evidence:* the
  scheduler unit row (the fused transition gives a terminal pool and an
  accepted requeue) and its negative legs, of which
  `notify_inmem_codegen_complete` leaving a `TypecheckWorking` module
  incomplete is the executing check on the one remaining partial writer.
  The W0 seam test that built the unsettled state was deleted with the
  change; its compile failure alone is not detection, because the removed
  argument breaks it whether or not another call can still build the state.
  The session and recovery rows are
  reachability checks. *Residual:* a scheduler edit adding a fourth writer of
  in-memory completion, asserted with the design's falsifier; `review` runs
  the writer census on any change-set touching the field. *Class:* safety
  fence. *Owner:* `dev`.
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
  conformance, `tests/AGENTS.md` §Test isolation), so this harness needs a
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
- **M-7 — compiler web tests load no stdlib.** The `--run` spawns in
  `concurrency_fanout_web.rs`, `launch_grid_corrupt.rs` and
  `launch_vec_send_corrupt.rs` set `CRANELISP_LIB` to the workspace
  `stdlib/`, and their fixtures do not suppress the implicit prelude, so a
  stdlib failure stops them before the behaviour they test. P1 creates
  exactly that failure until the W1 stdlib rewrite lands. `test` makes each
  fixture module stdlib-free, for example by a null prelude import or by
  dropping the stdlib from the spawn, in or before P1's change-set. Each
  test then passes with `CRANELISP_LIB` pointing at an empty directory.
  *Wrong:* a fixture that still resolves a name through the stdlib prelude.
  *Class:* maintenance check for suite isolation (root stdlib-separation
  rule). *Owner:* `test`, W1.

### 3.9 W2 intake on the U′ tree

Verified 2026-11-16 against `f5822487` plus the uncommitted U′ cutover
(compiler `86402bc0…`), with the checkpoint compiler `ee8959c0…`
(`.local/s123-w2/pre-uprime-control/`) as control. Every probe below ran
`--run --no-cache` in a fresh directory with an empty `CRANELISP_LIB`, no
prelude, `CRANELISP_RC_STATS` and `CRANELISP_RC_DEC_CHECK` armed. Allocs and
deallocs are shown as `a/d`.

- **U-11 — in-place `vec-set` releases an owning old element shallowly**
  (review R1). *Harm:* every in-place replacement of an element that owns
  heap strands that element's graph: one block per replacement, unbounded in
  a loop. *Classification:* defect, `rc-miscount` (leak), not memory-unsafe.
  It predates U′: the checkpoint compiler gives identical counts, and the
  same `drop_glue = None` release is in `emit_vec_set_in_place` at
  `f5822487`. It entered with the in-place arm. Existing evidence used only
  flat elements, so this is a coverage miss.
  *Measured:* the first three rows are identical on both compilers.

  | Shape | Subject | Control |
  |---|---|---|
  | Vec element: `(vec-len (vec-set [["old"]] 0 ["new"]))` | 6/5 | `(vec-len [["new"]])` 4/4 |
  | ADT with a `String` field: `(vec-set [(MkB "old")] 0 (MkB "new"))` | 6/5 | `[(MkB "new")]` 4/4 |
  | Closure capturing a `String` | 6/5 | the unreplaced closure 4/4 |
  | Value-position `vec-set`, `(ap vec-set [["old"]] 0 ["new"])` | U′ 7/6; checkpoint 8/8 on the copy arm | the same with flat `"old"`/`"new"`, 5/5 |
  | `--link`, Vec element (U′) | 6/5 | 4/4 |

  U′ widens the exposure. Its move sends wrapper updates to the in-place arm
  (U-5), so the value-position face leaks only on U′.

  *Mechanism controls:* a flat `String` replacement in place balances, at
  4/4 with `reuse_hit=1`. The same nested element on the copy arm, where the
  source is shared, balances at 7/7. An old element that is still shared
  balances on the in-place arm, at 6/6 for both the Vec and ADT elements.
  So the fault needs three things together: the in-place arm, an owning
  element, and that element's last reference. *Refuted if* a correction
  that runs the element type's release on the in-place arm leaves the
  nested subject at 6/5.
  *Wrong implementations to reject:* a fix that covers only the static site
  and not the value-position wrapper, which shares `emit_vec_set_in_place`;
  a fix that covers `Vec` elements but not ADT or closure elements; a
  release that frees an old element that is still shared.
  *Seam:* a `MarginalPair` per face, with each control changing only the
  element kind or arm from the table above. Use the Vec, ADT and wrapper
  faces under `--run`, and the Vec face under `--link`, armed at the link
  step (C-5). Each subject asserts `assert_balanced` and is **RED now**, at
  residual 1. Keep the flat-element and shared-old controls as passing
  guards. *Class:* acceptance, then safety fence. *Owner:* `test`, then
  `dev`(backend).
- **U-12 — a concrete synthetic accessor leaks its input** (golden G-1).
  *Harm:* every call of a canonical field accessor of a concrete product
  leaks the product. A heap field leaks too, so one call of `Box.items`
  leaks two blocks. *Classification:* defect, `rc-miscount` (leak),
  **introduced by the U′ cutover**: the checkpoint compiler balances every
  subject below. Loops of 100 calls:

  | Shape | U′ | Checkpoint |
  |---|---|---|
  | `(Point.y (Point n 7))` | 101/1 | 101/101 |
  | `(vec-len (Box.items (Box [n 2 3])))` | 201/1 | 201/201 |
  | Control: `(py (Point n 7))`, where `(defn py [p] (match p [(Point x y) y]))` | 101/101 | 101/101 |
  | Control: the same `defn` twin for `Box` | 201/201 | 201/201 |
  | Generic product `(P.y (P [n] [n 2]))` | 301/301 | 301/301 |

  *Mechanism, observed at the CLIF seam:* `user::Point.x` returns its field
  on the success path with no release of `v1`. The monomorphised generic
  accessor, `user/P.y [(user/P (Vec Int))]`, releases its scrutinee there <!-- doc-check: literal reason="Language symbol of a CLIF frame name" -->
  (`call fn0(v1)`). So the missing release belongs to the concrete
  synthetic accessor body, which the lenient builder produces, not to the
  accessor rule as a whole. *Hypothesis to probe before the fix:* the
  concrete accessor body is planned without its parameter's drop.
  *Refuted if* the user-written twin leaks on the same build.
  *Wrong implementations to reject:* a fix that covers scalar fields but
  not heap fields, or concrete accessors but not generic ones (the generic
  twin is a guard); a release placed before the field load, which the armed
  check stops; a caller-side release, which double-releases with the user
  `defn` twin. *Seam:* a `MarginalPair` per face, with the accessor as the
  subject and the user `defn` twin as the control. Use the `Point.y` and
  `Box.items` loops above under `--run`, and `Point.y` under `--link`
  (measured 101/1 on U′, with the instrument set on both the link and the
  run steps). Each
  subject asserts `assert_balanced` and is **RED now**. The generic face is
  a passing guard. Do not put a fresh constructor in `main` into either
  half: it is stack-placed and the armed check stops on its release
  (M-9). *Class:* acceptance, then safety fence. *Owner:* `test`, then
  `dev`(backend). `design`(backend) confirms the synthetic body's
  obligations.
- **U-13 — W-M returns to `assert_balanced`** (ACT-1026's completion).
  `cow_result_consumed_in_frame::parameter_set_at_its_last_use_and_forwarded_by_a_match_arm_balances`
  fails on U′ because it measures residual 0 against its `assert_residual(1)`
  pin. Both halves read 2/2. The pin recorded ACT-1026's leak, which U′
  removes. `test` restores `assert_balanced` and rewrites the comment in the
  past tense. In the same change, `test` puts the D2-C comment in
  `join_forwards_its_binder.rs` in the past tense, because its control now
  balances at 3/3, where it read 3/2 at the checkpoint (ACT-1028). *Class:*
  safety fence. *Owner:* `test`.
- **U-14 — retag the R1 lead.** `uniform_counting::lead_r1_subject` and its
  control differ only in the inner binder's name. At the checkpoint the
  subject stopped with a use-after-free and the control balanced, so the
  name alone decides the outcome. `test` changes its `// defect:` line to
  `class=binder-name-underkey` and `locus=crates/cranelisp-backend/src/heap.rs::register_alias`, <!-- doc-check: literal reason="Prescribed historical locus token; U-14 records that U-prime deleted the seam" -->
  noting in prose that U′ deleted that seam, and removes the "provisional"
  sentence. The other lead subjects keep their tokens. *Owner:* `test`.
- **C-10a — retired-mechanism cells on the U′ tree.** Delete them; there is
  nothing to re-point.
  - `ownership_fences::borrowed_declared_primitive_explicit_import_no_percall_rc`
    and `…_prelude_fallback_no_percall_rc` observed typecheck's declared
    borrow fact only through backend borrow elision. Under U′ no emission
    reads borrow modes ([uniform counting §7](../../design/backend/uniform-counting.md#7-as-landed)),
    so the seam is gone. Both read 51 and 1001 increments at N = 50 and
    N = 1000. The S110 `prelude-scope-miss` repro goes with them, because its
    only observable consequence was that elision. If `arch`'s follow-on
    packet keeps borrow modes with a new consumer, `qa` allocates their
    reachability at that consumer.
  - `s99_fixtures::s99_f2_capture_borrow_drops_rc_inc`, and the five
    `s99_f{1,2,3,4}_capture_borrow_parallel_equals_serial` and
    `s99_f2v_single_ctor_capture_borrow_parallel_equals_serial` cells. No
    source reads `CRANELISP_CAPTURE_BORROW` any more, so each `*_capture_borrow_*`
    equivalence cell duplicates its `*_parallel_equals_serial` sibling. Remove
    the switch's `env_remove` lines in `ownership_fences.rs` and
    `golden_clif_w0b.rs` in the same change. No backend source names the
    switch.
  - *Owner:* `test`.
- **M-8 — the W0.b capture asserts each program's outcome** (golden G-2).
  *Risk:* a corpus entry whose program is refused still passes its golden,
  so the corpus's "green by construction" claim goes unchecked. Entry 04
  exits 1 with `entry module has no 'main' function`, because `--run`
  requires `main`. *Classification:* a maintenance-check defect in the
  capture contract, not a product defect. The refusal is the specified
  batch behaviour. *Ruling:* `golden_clif_w0b.rs` asserts each entry's exit
  status against a pin the W0.b MANIFEST records, as the L-B1 corpus
  records its exits. Entry 04 gains `(defn main [] (Pure 0))` and keeps its
  top-level expression. Measured: `user::__expr` is still emitted and the
  run exits 0. Re-capture only entry 04, attributing its new `user::main`
  frame to the fixture change. *Wrong:* pinning exit 1 for 04, which would
  encode a refusal as the corpus's expected outcome. *Class:* maintenance.
  *Owner:* `test`.
- **M-9 — the armed release check stops on a stack-placed value**
  (ACT-1049, closed at S124 when stack placement retired).
  `(Pure (match (Point 3 7) [(Point x y) x]))` stops armed on both compilers
  with `STALE RC DEC … Freed-value … = None`, while it exits 3 at 1/1
  unarmed. The constructor lives in a stack slot with the immortal header,
  and the check does not recognise the address. An armed stop whose
  `Freed-value` is `None` is therefore not evidence of a use-after-free.
  Until ACT-1049 is resolved, cells keep NoEscape constructors out of armed
  halves. *Class:* intake against a diagnostic instrument.
- **The 0916 guard on the U′ build.** All three cells of
  `trait_scrutinee_scalar_payload_0916.rs` pass on U′ and on the checkpoint
  compiler. So do four variants at n = 1023 and n = 1024: base, dropped
  payload, duplicated payload, and a generic caller. The cell is no longer
  a family 2 witness on either build: typecheck now compiles
  `Functor.fmap$user/Option [(Fn [Int] Int) (Option Int)]` at a concrete
  payload, and the instance's only atomic operation is the closure's
  release. No free-standing program reaching a residual-`Var` trait
  instance was found: `fmap` passed as a value fails earlier, with a
  `carrier-loss` refusal. So nothing measures FIXME 0903's widened
  exposure. The 0903 armed category census is its measured instrument
  (§5). The cell's `// defect:` lines need `fixed=` stamps, and `test`
  finds the fixing commit.

**Acceptance of `test`'s W2 intake, 2026-11-16.** The source is
`.local/s123-w2/test-evidence-2.md`. QA's own targeted run on compiler
`86402bc0…` gave 129 run, 122 pass and 7 RED. Each RED failed at
`assert_balanced`: four at residual 1 (U-11), two at 100 and one at 200
(U-12). No half stopped, and every guard passed.

- **U-11**, in `vec_set_owning_old_element.rs`: accepted. The cells cover the
  Vec, ADT, value-position and `--link` faces, with the flat-element and
  shared-old guards. The closure face is covered by the shared release
  source (uniform counting §3.4 item 5) and is not separately required.
- **U-12**, in `synthetic_accessor_input_release.rs`: accepted. The
  `locus=…ownership_plan.rs` token is the unconfirmed planning hypothesis.
  `dev` names the seam its fix changes, and `test` sets the token to that
  seam in the fix change-set.
- **U-13, U-14, C-10a and M-8:** accepted. M-8's planted missing-`main`
  form failed at the exit assertion.
- **C-10a addendum.** `ownership_fences::s5_str_len_borrowed_sibling_hot_loop_value_and_balance`
  stays, because a consuming read inside a self-tail loop is a U′
  property. Its `// spec:` cites a section 9.2 of the backend ownership
  codegen design, which U′ removed. `test` re-points it to
  [uniform counting §1](../../design/backend/uniform-counting.md#1-the-rule)
  and drops the "borrowed sibling" and "adaptation inc" narration. *Owner:*
  `test`.

**Conditions for the R1, G-1, R2 and R3 change-set.** Uniform counting §8
proposes these. This record allocates them. `test` lands U-15 to U-17
before `dev`(backend) starts. `dev` supplies the detection proofs inside its
change-set.

- **U-15 — operand order** ([uniform counting §3.2](../../design/backend/uniform-counting.md#32-operand-order-decision-s123-w2)).
  *Harm:* an emitter that consumes operands in an order other than the
  plan's moves a binder before its earlier duplicate, which is a
  use-after-free. *Wrong implementations:* the emitter iterates the shared
  evaluator's values in another order; a lowering evaluates an operand
  expression directly instead of through the evaluator. *Seam:* one armed
  `--run` cell per §3.2 row that has a free-standing program. In each, a
  binder is used twice in one operand sequence, as a duplicate and then as
  the move, and the cell asserts the program's value and its balance. The
  rows are a builtin or static Apply, `(add-i64 (vec-len v) (vec-len v))`;
  a closure call, `(f (vec-len v) v)`; a tail self-call,
  `(go (add-i64 n -1) (add-i64 acc (vec-len v)) v)`; a Vec literal, `[v v]`;
  a constructor with two heap fields; and `par-bind` and launch-continue
  where a binding expression and the continuation both use the binder. Use
  moves on as the discriminating polarity. Moves off is a value-equivalence
  leg, because under moves off every use duplicates. QA measured the Apply,
  closure, tail and Vec-literal shapes as balanced, with the right value, in
  both polarities. These cells are passing guards, not REDs. A row with no
  free-standing program is reported, not invented.
  *Detection proof*, which `dev` supplies with the change: reversing only
  the evaluator's iteration makes the Apply cell and the Vec-literal cell
  RED under the armed check. Reversing the shared sequence itself leaves
  every cell green.
  *Limit:* branching and binding nodes are asserted by construction (§3.2),
  with the §9.2 falsifier. These cells do not measure them. *Class:* safety
  fence. *Owner:* `test`; the detection proof is `dev`'s.
- **U-16 — the wrapper template** ([uniform counting §3.3](../../design/backend/uniform-counting.md#33-generated-wrappers-the-forwarding-template-decision-s123-w2)).
  *Harm:* a template that drops or doubles a capture's increment frees the
  environment's capture or leaks it. *Wrong implementations:* one of the
  three wrappers keeps its own increment path instead of the assembly site;
  a curried closure-value target duplicates and releases around the call.
  *Seam:* armed `--run` cells in both polarities, asserting value and
  balance:
  - a curried heap capture called twice,
    `(let [g (f [1 2])] (add-i64 (g 1) (g 2)))`;
  - a curried closure-value target;
  - a function value over a consuming heap target, `(ap vec-len [1 2 3])`;
  - a constructor used as a value with a heap field;
  - a non-higher-kinded trait method used as a value with a heap argument.

  QA measured the first four shapes balanced in both polarities. A trait
  method passed as a value over a higher-kinded trait is refused with a
  `carrier-loss` error before codegen, so use a single-parameter trait; if
  none reaches codegen, report it. *Detection proof*, which `dev` supplies:
  removing the template's capture increment makes the first cell stop under
  the armed check; a second increment leaves an allocation outstanding; the
  unplanted template balances. *Class:* safety fence. *Owner:* `test`; the
  detection proof is `dev`'s.
- **U-17 — moves-off legs for U-11 and U-12** (uniform counting §3.4). Add
  the U-11 Vec face and the U-12 `Point.y` face with
  `CRANELISP_NO_OWNERSHIP=1` set on both halves. *Wrong:* a fix that reaches
  only the moves-on lowering. Both are **RED now**: QA measured 6/5 and
  101/1 under moves off. *Owner:* `test`.
- **U-18 — a tail self-call operand erases its `race`** (`dev`(backend)
  lead). *Requirement:* `spec/10-io.md` §10.12.8, the `race` row and item 1:
  both effects run and the first to complete wins. *Harm:* when a `race` is
  in tail position and an operand is a call to the enclosing function, that
  call is lowered as the loop jump. The race node is never built: the other
  branch never runs, no deadline bounds the recursion, and the program gets
  the recursion's value with no diagnostic. Either operand position is
  affected. *Classification:* defect, wrong value. It is not memory-unsafe,
  and `--run` and `--link` agree. It predates S123: the checkpoint compiler
  gives the same results and CLIF, and the `Race` arm of
  `compile_builtin_fn_call` restores tail position before its operands are
  compiled at `f747990f` too. It entered with the S96 combinator lowering.
  Existing `race` evidence never used a self-call operand, so this is also a
  coverage miss.
  *Measured* on both compilers, with
  `S` = `(bind (sleep 1000) (fn [u] (Pure 7)))`, `(defn main [] (f 1))`, and
  `f` as shown. A correct `race` returns 99 at once.

  | `f`, for `n` ≠ 0 (`n` = 0 is `S`) | Exit | Wall |
  |---|---|---|
  | Subject: `(race (f (add-i64 n -1)) (Pure 99))` | 7 | ≈1 s |
  | Subject: `(race (Pure 99) (f (add-i64 n -1)))` | 7 | ≈1 s |
  | Control: the same operand, calling `(defn g [n] S)` | 99 | 15 ms |
  | Control: the self-call let-bound before the `race` | 99 | 18 ms |
  | Control: `(select [(f (add-i64 n -1)) (Pure 99)])` | 99 | 12 ms |

  *Mechanism, observed at its seam:* the subject's CLIF for `f` ends its
  `n` ≠ 0 block with `jump block1`, and the race node's block is
  unreachable; the non-self control's block builds the node. *Refuted if*
  a correction that compiles the operands outside tail position leaves the
  subjects at 7.
  *Wrong implementations to reject:* a fix to the first operand only; a fix
  that also stops a `race` in tail position being the function's result;
  a change to `select` or `bind`, which already compile their operands
  outside tail position.
  *Seam:* the exit code, through every mode, as the suite requires for
  language semantics. The branches cannot finish together, so the
  unspecified tie of item 2 does not arise. Both subjects are **RED now** at
  exit 7; QA observed 7 under `--run` and `--link`, and the REPL is
  unmeasured. The non-self and let-bound controls are passing guards.
  *Class:* acceptance.
  *Owner:* `test`, then `dev`(backend), who also owes the module row at the
  `Race` arm.

### 3.10 U′ cost and residue readings, and the W2 suite

Measured 2026-11-16 by `qa`. Raw programs, scripts and results are in
`.local/s123-w2/u8/`.

- **Binaries.** The control is `.local/s123-w2/pre-uprime-control/cranelisp`,
  sha256 `ee8959c02460c64dfc31393f5f2a7b4c955a644c69c0fe2046466238c0e7555b`.
  The subject is the build of `f5822487` plus the W2 tree, copied to
  `.local/s123-w2/u8/subject/`, sha256
  `77bb2dd98414ea0317d2256e2fbeb75c7bd33d04ee8bda7dc0aba6bc5a5dbe46`. Both
  `--link` bundles are `c86dd29d…0948`.
- **Method.** The module caches under `examples/` and `exemplar/` were
  purged first (M-1); `tests/` had none. Every child ran in a fresh
  directory with a cleared environment. Wall time is from single runs with
  stats off. Counts are from separate runs with `CRANELISP_RC_STATS`.

**U-8 is within the user's bound.** No in-place count falls below the
control's, no U′/control ratio grows with workload, and the exemplar warm
solve is faster on U′.

| Workload | Control | U′ |
|---|---|---|
| In-place hits, iterations 2–1,000: D1, D2, D4 | 999 each | 999 each |
| In-place hits, iterations 2–1,000: L1, L3 wrappers | 0 | 999 |
| Stdlib `conj` (L2), `assoc` (L4), 1,000 iterations | 1 hit, 1,000 copies | 1,001 hits, 0 copies |
| Wall, D1/D2/D4 at 10⁵, 10⁶, 10⁷ | 11–36 ms | ratio 0.87–1.33, flat |
| Wall, L1 at 10³, 10⁴, 3×10⁴ | 14 ms, 0.32 s, 2.37 s | ratio 0.79, 0.04, 0.007 |
| Wall, L3 at 10⁵, 10⁶, 10⁷ | 0.20 s, 1.84 s, 17.1 s | ratio 0.064, 0.009, 0.002 |
| Exemplar warm serial driver, N = 1, 8, 64 | 0.69, 0.93, 2.78 s | 0.68, 0.76, 1.53 s; ratio 0.97, 0.81, 0.55 |
| Exemplar in-place hits per solve | 0 of 11,593 | 11,585 of 11,593 |
| Exemplar allocations per solve | 25,517 | 13,932 |
| Contention benchmark, parallel/serial wall | 0.12/0.14 s | 0.15/0.14 s |
| Contention benchmark, parallel/serial CPU ratio | 1.46 | 1.57 |

- Moves off, every loop copies on both compilers.
- The driver solves the `solver.cl` puzzle N times, consumes each result and
  prints nothing. Every N balances on both compilers.
- The contention workload's `vec-set` source is shared, so it copies on both
  compilers. U′ tallies the 48,000 copies as `reuse_miss`; the control's
  static copy arm was untallied (carry triage §8.3).
- **Limits.** Debug builds; one run per cell, so the millisecond rows carry
  noise well inside the margins. Small allocation probes ran beside the
  N = 64 driver row. The contention CPU ratio depends on scheduling, which
  is why its benchmark is ignored in the suite.

**U-10.** The warm serial `solver.cl` solve retains 51 allocations on the
control with moves on and 556 with moves off. On U′ it retains 2 in both
polarities. Moves off is not above moves on, so nothing is filed for it. The
2 is one block for each of `main`'s two `print` calls; the attribution is in
ACT-1018.

**The full suite on the subject:** 6,679 run, 6,656 pass, 23 RED, 1 skipped.
There are no regressions. 20 REDs are filed guards:

| Filing | REDs |
|---|---|
| ACT-0973 | `platform_errors` root and nested non-entry declarations |
| ACT-0985 | `spec_05_definitions::impl_body_uses_impl_declared_later_in_cluster` |
| ACT-0997 | `spec_08_modules::box_import_renamed_binds_canonical_type`, `box_import_self_rename_is_accepted` |
| ACT-1001 | `spec_08_modules::impl_ambiguous_trait_names_both_candidates_neg` |
| ACT-1016 | `spec_08_modules` export-cycle run and startup; `repl_persist::reload_failed_reexport_dependency_matches_restart_neg` |
| ACT-1018 | `exemplar_ownership_residue_s116::sudoku_warm_serial_solve_retains_nothing`, now at 2 |
| ACT-1034 | four `spec_07_traits` parametric-impl instance cells |
| ACT-1035 (fixed in W4) | `spec_07_traits::repl_concrete_impl_call_survives_later_parametric_impl` |
| ACT-1036 | `spec_10_io::batch_main_non_io_return_refusal_is_located_at_main` |
| ACT-1038, ACT-1039 | three `trace` cells |
| ACT-1047 (fixed in W4) | `repl_persist::persist_save_creating_backing_file_survives_definition` |

The other three are W2 consequences that `test` owes:

- **C-10b — two more retired-mechanism cells.**
  `s117_ownership_witnesses::r2_borrowed_scalar_result_has_production_clif_polarity`
  and `r2_may_alias_summary_protects_control_flow_merged_return` assert the
  CLIF polarity of typecheck's borrow facts through backend elision. That is
  C-10a's seam, which U′ removed. On `(defn borrowed-live [s] (add-i64
  (str-len s) (str-len s)))` the control emits two increments and U′ one.
  Delete both, as C-10a does. *Owner:* `test`.
- **C-10c — the S111 return-copy fence's third flip.**
  `vec_cow_value_use_leak::vec_set_let_wrapped_in_place_return_does_not_leak`
  measures 0 against its pin of 200. The control measures 200, with 200
  copies; U′ updates in place 200 times and balances. The fence names this
  flip as its own trigger: `test` changes the assertion to a residual of 0
  and rewrites its narration in the past tense. *Owner:* `test`.

**Not intake: the `--link` statistics observation.** A program linked with
`CRANELISP_RC_STATS` printed its counters only when the variable was also set
at run time. That is the pre-W3 behaviour: the runtime still reads its launch
environment, which is the wrong implementation B-2 rejects and W3 removes.
`tests/helpers/marginal.rs` arms both the link step and the run, so W2's
`--link` cells measure today and keep measuring after W3 (C-5).

- **U-19 — an inline `bind` continuation leaks an unused heap argument**
  (the `race` review's separate observation). *Harm:* each such `bind`
  strands its input value; in a loop the leak is unbounded.
  *Classification:* defect, `rc-miscount` (leak), not memory-unsafe: the
  armed check is silent. It predates U′: the control compiler gives the same
  counts in both polarities. *Measured* armed, `--run --no-cache`, no
  prelude, a/d on both compilers and both polarities:

  | Program | a/d |
  |---|---|
  | Subject: `(bind (Pure [49]) (fn [v] (Pure 49)))` | 5/4 |
  | The same with `_`, an annotated `(Vec Int)` parameter, or an `Int` capture | 5/4 |
  | Nested payload `[[49]]` | 6/4 |
  | Control: the same lambda let-bound, then passed: `(let [k (fn [v] (Pure 49))] (bind (Pure [49]) k))` | 5/5 |
  | Control: a `defn` with an unused parameter passed to `bind` | 5/5 |
  | Control: the lambda uses `v`, `(Pure (vec-get v 0))` | 5/5 |
  | Control: the same inline lambda passed to a user higher-order function, `(app (fn [v] 49) [49])` | 3/3 |

  *Mechanism:* the hypothesis is that the inline continuation's lambda node
  reaches `compile_lambda` without a heap parameter type. Its planned drop
  at introduction then emits nothing, because `FnCompiler::emit_release`
  returns without a release for an absent or non-heap type. The let-bound
  control differs only in where the lambda is written, so the leak follows
  the node's recorded type, not the parameter's use. The annotated subject
  still leaks, so a source annotation does not reach that type. The seam was
  not observed: `CRANELISP_CODEGEN_DUMP` does not print lambda bodies.
  *Refuted if* the subject lambda's CLIF releases its parameter. The
  attribution is provisional: the producer may be typecheck's type for a
  lambda in a builtin's argument, and `dev` probes before fixing.
  *Wrong implementations to reject:* a fix for `Vec` only (the nested
  payload is a guard); a release in the `bind` node or its disposer, which
  double-releases on the used control; a fix that covers only `bind`
  continuations when the type is lost for every inline argument.
  *Seam:* a `MarginalPair` with the subject above and the let-bound
  control, under `--run`, `--link` (both steps armed) and the REPL, moves on
  and moves off. The subject asserts `assert_balanced` and is **RED now**,
  at residual 1. The used and `defn` controls are passing guards.
  *Class:* acceptance, then safety fence. *Owner:* `test`, then
  `dev`(backend). It does not block W2's commit. It predates the wave, is a
  leak, and was found after W2's first review round, so it carries to S124
  under the correction-loop stop rule unless the user pulls it in. Filing:
  ACT-1050 (closed).
  The cells are `tests/bind_unused_heap_argument.rs`: twelve subjects, one
  per mode, polarity and payload depth, and six control tests.

**Acceptance of the W2 `fixed=` stamps, 2026-11-16.** The source is
`.local/s123-w3/test-evidence.md`. The tree diff over `tests/` changes
comments and `// defect:` metadata only.

- *`fixed=S123/3bdf398e`, 38 lines.* 36 lines are W2 guards and 2 are U-18's.
  Each was recorded failing on its clause before W2 in `.local/s123-w2/` logs,
  except two pinned-residual fences. Those two are U-13's W-M cell (pinned at
  1) and C-10c's return-copy fence (pinned at 200), and §3.9 records each
  leak measured on the control and gone on U′. The shadowed-binder guard's
  `owner=` moves from `/design` to `/dev`, the role that delivered its fix.
- *`fixed=S121/992cb595`, the three 0916 lines.* Its parent `18bca20d`
  (S120 close, no compiler-source change) lists 0916 among the open
  failures. The S121 close run's four failures exclude it, and the S122
  checkpoint suite passes all three cells. No run of the parent tree was
  made; the attribution rests on those records.
- *Not stamped, correctly.* These are the previously green S122 COW
  use-after-free guards in `cow_result_consumed_in_frame.rs` and
  `join_forwards_its_binder.rs`, and ACT-1050's twelve open lines.

## 4. Traceability band

`qa` restores each row after `test` reports the walk of its backlinks:

- `spec/12-runtime.md` §12.4.3, §12.7.2.1 (three rows), §12.7.3; the
  headings §12.7.2, §12.7.4–§12.7.4.2, §12.7.5, §12.7.8 and §12.7.9, tagged
  `[S123]`.
- `spec/10-io.md` §10.12.7 item 3 and §10.12.8 empty `select`.
- `repl/spec/05-error-presentation.md` §5.1 and §5.2 rows; the cited tests
  are compile errors and are expected to restore unchanged.
- `repl/spec/16-test-discovery.md` §16.2; `repl/spec/00-cli-invocation.md`
  §0.8; `repl/spec/14-file-watching.md` §14.9 and the matching
  `repl/spec/15-session-persistence.md` §15.1 ruling; `repl/spec/17-embedded-agent.md`
  §17.4, §17.10.1 and §17.10.2, tagged `[S123]`.

Restored at W4 (2026-11-16): `repl/spec/14-file-watching.md` §14.9 and its
§14.2 rename-over row, `repl/spec/15-session-persistence.md` §15.1,
`repl/spec/05-error-presentation.md` §5.1 and
`repl/spec/00-cli-invocation.md` §0.5.6. `spec/07-traits.md` §7.7 and §7.7.1
are graded partial on their non-normative examples. Section 7.4.2a stays
partial, because the new `Text`/`Debug` example has no cell.

K6 C3 and C4 (`spec/10-io.md` §10.10.1, `spec/08-modules.md` §8.9.3) carry
with their realisation; their annotations stay as they are.

## 5. Named residuals

The user accepted the first eight rows at the Phase 4 checkpoint. Phase 5
added the last three, which `sprint` presents at the Phase 5 → 6a
checkpoint (§8.5).

| Residual | Why not evidenced end to end | What covers it |
|---|---|---|
| A test child dying by signal (T-6) | No legitimate program raises a signal | `dev` scripted rows |
| A REPL test child writes no cache | Indistinguishable from the REPL's own writes | `dev` unit row 8 |
| Crash-consistent writers (P-17) | No controllable mid-write exit | `dev` rows; arch §1.7 falsifier |
| The agent-free build between lane runs (A-5) | The lane is not continuous | Lane at every listed trigger; low harm |
| Linked worker count ignores `RAYON_NUM_THREADS` | No program observes the pool size | `dev` row (B-5) |
| A platform sees the launch environment | No platform in the suite reads it | Structural: the stub does not mutate the environment |
| Stack overflow panic row (§12.7.2.1) | Implementation-defined message | Unchanged `[S18]` |
| A `runtime/panic` emitter outside the raise helper (P-15) | The census reads spelling, not identity; the structural form is an `arch` API decision | Per-site CLIF rows; the census for spelled references; `review` on any backend change-set naming `panic_func_id` |
| FIXME 0903 family 2 on the U′ build (§3.9) | No free-standing program is known to reach a residual-`Var` trait-method instance; the 0916 cell now compiles at a concrete payload | The 0903 armed category census (its §7.3), owned by `design`(backend) and `dev`(backend); the family 1 accessor frame `Grid.cells` is a static witness only |
| A terminator wired to skip its claim (P-14) | Two raisers meet at the report only probabilistically | The deterministic claim-transition row; the two-raiser cell as observer |

## 6. Completion criteria

- Every **RED now** cell, and every C-1 and C-3 re-pointed cell, was observed
  failing on its clause before its fix, and passes on a fresh build of the
  final tree; K-1 to K-5's failing cells remain failing-not-ignored unless fixed.
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
  T-5, T-7; E-1 to E-6; B-1 to B-4; A-1 to A-6; R-1 to R-5 with R-2a; K-1 to K-6; M-1; M-7. Then
  C-6 and C-7 in their change-sets, M-3 with `docs`, M-4 and M-5 in Phase 6b.
- **`dev`, with each surface:** U-6, U-7's structure, U-9; P-10's unit rows,
  P-13 to P-17, P-18's guard rows; T-6; T-8; E-7; B-5; A-5's flag function;
  R-4's worker rows; R-5's unit row.
- **`test`, W2 intake (§3.9):** U-11 to U-14, C-10a and M-8 are landed and
  accepted. Before `dev`(backend) starts the R1, G-1, R2 and R3
  change-set: U-15, U-16, U-17 and the C-10a addendum. `qa` accepts their
  clause map first. U-18's two subjects and two controls, before any
  `race` correction.
- **`test`, W2 close (§3.10):** C-10b and C-10c in the W2 change-set; U-18's
  two `class=pending` lines retagged `class=tail-context-leak`; U-19's
  pair, committed RED, whether or not its fix is scheduled in S123. Two
  corrections remain before the W2 commit. C-10c's cell is renamed so its
  name states the balanced result it now asserts, and its section heading
  no longer calls the workload a copy arm. U-18's two subject comments
  state the fixed defect in the past tense, as the
  [defect-repro notation](../AGENTS.md#defect-repro-notation-defect) requires.
- **`qa`:** U-8 and U-10 are recorded (§3.10); M-1, M-6 and §4 are
  discharged (§8).

## 8. Phase 5 adequacy

**Verdict, 2026-11-16: adequate, with named residuals.** Phase 5's evidence
across W0–W5 supports the Phase 5 → 6a checkpoint. Each wave's own adequacy
is recorded with its conditions: W1 in the sprint plan, W2 in §3.9 and
§3.10, W3 in §3.5 and W4 in §3.6.

The tree is `b89cc7cc` on a fresh build. The source is `sprint`'s
integrated gate, `.local/s123-w5/gate-summary.md` and the logs it names.
QA's targeted reruns used the same binary.

### 8.1 Acceptance evidence

- The full suite ran 7,001 tests: 6,972 passed, 29 failed, 1 skipped. Every
  RED is a filed guard. There are no regressions and no unclassified REDs.

  | Filing | REDs |
  |---|---|
  | ACT-1050 | the twelve `bind_unused_heap_argument` subjects |
  | ACT-1034 | four `spec_07_traits` parametric-impl instance cells |
  | ACT-1016 | `spec_08_modules` export-cycle run and startup; `repl_persist::reload_failed_reexport_dependency_matches_restart_neg` |
  | ACT-0973 | `platform_errors` root and nested non-entry declarations |
  | ACT-0997 | `spec_08_modules::box_import_renamed_binds_canonical_type`, `box_import_self_rename_is_accepted` |
  | ACT-0985 | `spec_05_definitions::impl_body_uses_impl_declared_later_in_cluster` |
  | ACT-1001 | `spec_08_modules::impl_ambiguous_trait_names_both_candidates_neg` |
  | ACT-1036 | `spec_10_io::batch_main_non_io_return_refusal_is_located_at_main` |
  | ACT-1018 | `exemplar_ownership_residue_s116::sudoku_warm_serial_solve_retains_nothing`, at 2 |
  | ACT-1038 | `trace::trace_records_every_call_of_spark_admitted_callee` |
  | ACT-1039 | `trace::trace_records_user_function_calls_in_every_mode` |

  Each failed on its clause assertion. No premise or setup message appears
  in the log.
- *The two W4 REDs absent here.* Neither is a guard turning green.
  - `role_wiring::role_wiring_gate_detects_shared_and_local_faults_and_clears_a_sound_copy`
    was W4's stale principle count, repaired by `test` with Principle 27.
  - `trace::traced_spark_admitted_callee_releases_every_formatted_string`
    (ACT-1038) passes when no worker runs a traced call. On this binary it
    fails 20 of 20 isolated runs at residual 926, the action's per-call
    arithmetic. With every core busy it passes 2 of 10. The full-suite pass
    is that interleaving, so it is neither a fix nor a misattribution.
    `test` does not stamp it. A green run of either ACT-1038 cell is not
    flip evidence until the subject child observes its own premise. The
    action records this.
- The agent lane passes 91 of 91, and the agent-free lane 23 with 10
  skipped, which is A-1 to A-6.
- The exemplar exits 0, 41 and 41 for `user.cl`, `tests.cl` and the serial
  run. The server answers HTTP 200 with its page.
- Every inter-crate public-API delta for the phase matches its approved
  packet row, and the live baselines equal the committed ones.
- §6's criteria hold.
  - Each RED now and each re-pointed cell was observed failing before its
    fix and passes on this build.
  - The C-1, C-2 and C-5 censuses were emptied at W1 and W3. On this tree
    `catch-runtime-error` appears only in `spec_12_runtime`'s cell asserting
    that the name is unbound.
  - U-8's numbers and binaries are in §3.10.
  - The clause maps were accepted per wave.
  - §4 is discharged (§8.4).
  - The document checker exits 0.

### 8.2 Safety fences

- The U′ fences and the P-1 to P-19 fences pass, with the residuals of
  §8.5.
- **M-1 holds.** After the suite, `git status --ignored` shows no new
  cache under `tests/` or `examples/`. The one cache written,
  `exemplar/.cranelisp-cache/`, dates from 15:13:24. The suite ended at
  15:12:43, so the cache came from the gate's exemplar runs.

### 8.3 Diagnostic observers

- **The demo sweep.** All 13 active demos and 26 archived demos exit 0.
  The player's exit status is not evidence that a demo played. It never
  checks whether the REPL is still running, so it reaches `[demo complete]`
  after the REPL has exited.
  - `ring4i` and `ring4d` narrate recovery after a panic. Under §12.7.4.1
    the REPL now exits on a panic, so their later segments never play.
    These are stale expectations from the W1 ruling, which M-5 already
    covers. They are not defects. `ring4d`'s panic is its last input.
    `ring4i` loses its `fmap`, test, `/source` and `/run-tests` segments.
  - `test`, in Phase 6, rewrites both per M-5 and the archive's
    stale-expectation rule. `test` also makes the player fail when the REPL
    exits before the script ends. That check is cheap, and without it a
    stale expectation and a crash both read green.
- **Spec-to-test coverage reconcile** exits 0.

### 8.4 Maintenance checks

- **Spec link check, 11 stale anchors.** These are all in
  `tests/projection_elision_guard.rs`, which cites two sections of the
  backend ownership-codegen design that U′ retired. They do not block the checkpoint. No
  Phase 5 acceptance condition rests on this file, and its fourteen cells
  pass. Their assertions are a moves-on/off output oracle and an
  iteration-independent balance on `vec-get` arguments, and both remain
  meaningful under U′. The module documentation and citations describe a
  mechanism that no longer exists, which is a missed C-10 member.
  - *Owner:* `test`. Re-cite each cell to the
    [uniform counting](../../design/backend/uniform-counting.md) section
    its assertion now observes, and rewrite the module documentation. A
    cell that duplicates a U-3 differential may be deleted instead.
  - *Timing:* before S123 closes, or carried with a record.
- **§4 is discharged.**
  - Restored at W5: `repl/spec/17-embedded-agent.md` §17.4, §17.10.1 and
    §17.10.2. §17.4 is graded partial: no cell observes a file-supplied
    provider combined with a process-environment key. An offline cell can
    observe it, because an `anthropic` provider with a model and a key
    reports `active` at startup without transmitting. That cell is a
    `test` gap for S124.
  - Repaired: `spec/12-runtime.md` §12.3.1 item 2's stale RED tag for the
    resolved ACT-0974. Its cell passes.
- **`fixed=` stamp owed.** The `// defect:` line of
  `string_primitive_value_discharge::str_len_as_function_value_releases_its_argument_once`
  has no stamp, and the cell is green. *Owner:* `test`.
- **M-6.** [Memory-safety coverage](memory-safety-coverage.md) §5 is
  refreshed with the W5 reach.
- **The test-capture contract.** `platforms/test-capture/spec.md` no longer
  names the removed `PlatformError::DispatchError`. The same wording remains
  in the rustdoc of `platforms/test-capture/src/lib.rs` line 85. `qa` owns
  that file; the fix is a doc-comment change for a source-editing dispatch.

### 8.5 Residuals for the Phase 5 → 6a checkpoint

The user decides each of the three rows Phase 5 added to §5:

- **P-15, a `runtime/panic` emitter outside the raise helper.** Grade:
  asserted with a named falsifier. The census reads spelling, so an alias
  passes it. The structural form needs an `arch` API decision, a wrapper
  for `CompileContext::panic_func_id`. Until that decision, `review`
  inspects any backend change-set that names `panic_func_id`.
- **P-14, a terminator wired to skip its claim.** Grade: measured
  deterministically at the pure claim-transition row. The two-raiser cell
  detects a planted skip in 2 of 3 runs, so it is a diagnostic observer and
  not a fence.
- **FIXME 0903 family 2 on U′.** Unmeasured. No free-standing program is
  known to reach a residual-`Var` trait-method instance, and the 0916 cell
  no longer reaches the arm. The 0903 armed category census is the
  instrument. `design`(backend) and `dev`(backend) own it.

### 8.6 Carries into S124

| Item | Why it carries |
|---|---|
| ACT-1050 (closed) | Unbounded leak in a loop, not memory-unsafe. It predates U′ and was found after W2's first review, so the correction-loop stop rule applies. Twelve REDs stand |
| ACT-1049 (closed at S124) | A false positive of the armed release check that keeps NoEscape constructors out of armed halves. It narrows the safety signal, not the product. Principle 27 schedules stack placement's retirement in S124, which may remove the case; decide there |
| ACT-1018 | The warm solve retains 2, one block per `print`. That is down from 51, and its attribution is recorded |
| ACT-1052 (closed) | Reproduced on `390201c3`: SIGSEGV in `--run`, `--link` and the REPL. K-6 is the committed RED. The correction needs `design`(int) to place it and may change the cache schema |
| ACT-1038 (closed at S124; Git history), ACT-1039 (closed at S124; Git history) | The carry is planned in the sprint scope. ACT-1038's cells carry the same-child premise (§8.8); their REDs stand |
| ACT-0973, ACT-0985, ACT-0997, ACT-1001, ACT-1016, ACT-1034, ACT-1036 | Planned carries (sprint scope K5, K6 and the ACT list). Their REDs stand |
| §8.4 maintenance items | The projection-guard re-citation if S123 does not close it; the §17.4 combination cell |

### 8.7 What Phase 6a needs from this evidence

- **Demo re-baselines (M-5, `test`).** Rewrite `ring4i` and `ring4d` so no
  segment follows a panic, and fail the player on an early REPL exit.
  Re-read `optimization.demo`'s narration of borrow elision and static
  uniqueness against `/clif` on this binary. Replay the active set and the
  archive after the rewrite. `test` attributes any change in an active
  demo's output, not `docs`.
- **Transcript re-baselines for the banner (C-6's remainder).** The suite's
  exact transcripts were re-baselined in W3. The `user/` and `examples/`
  transcripts that show the startup lines are `docs`' and `training`'s to
  assess in 6a and change in 6b. Each new expectation asserts only the
  state word, the named file and the variable (§1.2).
- **The `user/` sample harness (M-3, Phase 6b).** It needs `docs`'
  classification of every fenced block, and a second named
  stdlib-dependency exception in root `AGENTS.md`, recorded by `sprint`
  first. The user accepted that exception at Phase 4. The harness is a
  maintenance check for `user/`, and its detection proof is the two
  planted faults M-3 names.
- **Audit on `cranelisp-frontend`.** Nothing in this evidence constrains
  it.

### 8.8 Phase 6a acceptance of `test`'s maintenance

QA accepted the following against §8.4 and §8.7 on 2026-11-16 (`f091a8f3`
plus the uncommitted 6a change). `test`'s report and logs are under
`.local/s123-6a/`; QA's focused runs are in `.local/s123-6a/qa/`.

- **Player early-exit check — accepted.** Maintenance check for
  `repl/demos/`. `repl/demos/test_demo_player.py` drives the real player
  against a stub PTY REPL.
  - *Positive leg:* an exit at startup and an exit after the first of two
    inputs both returned 0 before the change, and both fail after it.
  - *Negative leg:* complete playback, an exit on the final input, and a
    `/quit` restart all return 0.
  - *Limit:* exit 0 proves playback reached the last script line. It does
    not prove expected values or a clean final input. That is the accepted
    allocation, not a demo-output oracle.
- **`ring4i` and `ring4d` — accepted.** Each ends on its intentional panic,
  with no segment after it, and plays under the strict player.
- **ACT-1038 premise — accepted.** Every run without a worker-executed
  traced call fails as `PREMISE LOST`; the action records the predicate and
  its limits. Both guards fail on their clause at peak 2: 288 frames, and a
  residual of 354. The three controls pass. The sparks-disabled control
  proves the premise refuses a serial run.
- **Projection-guard re-citations — accepted with one return to `test`.**
  The fixtures and assertions are unchanged. The eleven retired anchors now
  cite [uniform counting](../../design/backend/uniform-counting.md) §1, §2.1
  and §3.3, and each section states what its cell asserts.
  - *Returned:* the two `sprint61_*` cells moved from
    `spec/12-runtime.md` §12.3.1 to a design-only citation. That drops the
    file's only trace to a normative requirement. Restore §12.3.1, and add
    the design section if wanted.
  - *Returned:* `tests/trace.rs`'s `untraced_fib_12_spawns` and its no-spawns
    control lost their consumer when the premise moved. Delete them or give
    them a consumer.
- **`optimization.demo` narration — 6b demo maintenance.** It is narration
  debt under intended U′, not a defect. The nine IR blocks equal W5's byte
  for byte after ANSI stripping (`.local/s123-6a/test-demos-final/w5-ir-comparison.txt`).
  The rewrite belongs in Phase 6b, with the owned demo guide's borrow-elision
  wording. `test` re-reads every narrated IR claim against `/clif` and does
  not pin block or function numbers.

### 8.9 Phase 6b attributions of the archive replay

QA attributed two archive-demo observations from `test`'s 6a replay on
2026-11-16, probing `target/debug/cranelisp` at `640d2ec7` in scratch
projects. Neither is a 6a change: both match the W5 logs.

- **`ring4p`'s ownership-ABI refusal: spec-conformant; the demo is stale.**
  - Replacing `(defn f [:Int x] x)` with `(defn f [:Int x] (+ x 1))` leaves
    the language type unchanged and moves the `ModeSummary` result from
    `AliasOf(0)` to `Fresh`. The interim ownership-ABI gate of the REPL redefinition specification
    (section 18.1.2, retired in S124) required that refusal even without callers, with the old body kept live.
    The diagnostic carries all three required items, and `(f 41)` stays 41.
  - Control: `(+ x 1)` to `(+ x 2)` (`Fresh` to `Fresh`) is accepted and
    late-binds to 43. A doc-only edit is accepted. The reverse,
    `(+ x 1)` to `x`, is refused with the modes swapped. Only the
    ABI-bearing mode separates the outcomes. The refusal comes from
    `src/redefine.rs` through `ModeSummary::abi_eq_opt`.
  - This is the gate that [Principle 27](../../design/arch/principles/27-dev-tier-optimises-only-against-blow-up.md)
    schedules for retirement in S124 with its spec ruling and API packet
    ([ACT-0953](../../sprints/actions/ACT-0953-decouple-live-slot-abi-from-ownership-inference.md)).
    Until then the behaviour is conformant, so no defect RED is owed.
    `tests/repl_redefinition.rs::same_type_ownership_abi_change_is_rejected_before_slot_patch` <!-- doc-check: literal reason="Cell as it stood at S123; row D7 retired the gate and deba008a removed the cell" -->
    already covers the gate on a parameter-mode change.
  - The demo dates from Sprint 58, before the S121 gate. *Handoff to
    `test`:* make step 5c's replacement ABI-preserving, such as `(+ x 1)` to
    `(+ x 2)`. That form holds both before and after the S124 retirement.
- **`ring4s`'s `then` segment: FIXME 0907's refusal is fixed, not masked.**
  - The segment compiles in the REPL, `--run` and `--link`, and evaluates to
    50 (`999` is discarded, then `42 + 8`). It returns nothing named 42.
  - The release is requested. The linked program defines the canonical
    `IO Int` drop glue for its module, and that glue calls through the GOT
    on the last release. `DropGlueRegistry::shape` classifies
    `primitives/IO` as `GlueShape::Io` before `ctor_shapes`, which holds the
    only `disagrees on declared parameter identity` site. `Bind` is the only
    seeded constructor, so no other type reaches that site with independent
    variables.
  - Four REPL calls leave `/mem` balanced at 0 live bytes. IO values dropped
    unrun, inside `Option`, `Vec` and a closure capture, and as an unrun
    `bind` all compile in `--run` and `--link` and exit 57 with
    `CRANELISP_RC_DEC_CHECK` set. The seven S118 cells and the balance cell
    pass in `.local/s123-w5/full-suite.log`.
  - *What would refute this:* any `IO T` release that reaches
    `ctor_shapes`, or a new seeded constructor with independent type
    variables.
  - *FIXME 0907's owner (`qa`) closes it after these legs:*
    - `test`: remove the stale `// defect: … ctor_shapes … S118` notation
      from `spec_10_io` (`pure_pattern_accepted`, `match_arms_all_io_pure`,
      `io_internal_ctors_stay_excluded_from_exhaustiveness_neg`) and
      `ctor_as_value` (the two `bare_ctor_*_map_io_*` cells).
    - `test`: rewrite `ring4s`'s attributed-red narration as a working
      segment and correct `repl/demos/AGENTS.md`'s 0907 reference.
    - `dev` on `stdlib/`: the six `core.io` self-tests in
      [`plan-stdlib.md` §6.2](../../stdlib/plan-stdlib.md), which this
      acceptance opens.
    - `spec` on `repl/`: obligation 3. `/info Bind` and `/info IO` still
      report unknown symbols while `/info Pure` introspects.

### 8.10 Phase 6b intake from docs

QA classified three observations from `docs`'s modules and macros guides on
2026-11-16 (`target/debug/cranelisp` at `640d2ec7`, scratch projects; the
`docs` fixtures are in `.local/s123-6b/docs-scratch/`). All three are
defects against unambiguous requirements. No spec question arises. None has
a committed RED, so each gets a cell below, listed in §3.7. *Class:*
acceptance (safety fence once fixed). *Owner:* `test` for the cells; `dev`
for the unit rows when each fix is dispatched.

**K-7 — a selective member entry binds its member
(ACT-1055 (closed at S124; Git history);
[§8.3.11](../../spec/08-modules.md#8311-accessibility-after-import))**

- *Harm:* a documented import form does nothing, and the only workaround,
  the member glob, imports names the user did not ask for.
- *Wrong implementations:* the current one, which binds nothing bare; a fix
  that also binds the parent `Shade`; a fix with glob semantics, which also
  binds `Red`; a fix for constructors only, not trait methods; a fix for
  value position only, not patterns.
- *Fixture:* `mathx.cl` holds `(deftype Shade Red Blue)`,
  `(deftrait Seven (seven [x] primitives/Int))` and
  `(impl Seven primitives/Int (defn seven [x] 7))`. No prelude.
- *Cells* (`--run`; the REPL shares the import path, and its parity was
  observed):
  1. After `(import [mathx [Shade.Blue]])`, `(match Blue [Blue 7 _ 0])`
     exits 7. The bare value and the bare pattern are both required. Red today.
  2. After `(import [mathx [Seven.seven]])`, `(seven 1)` exits 7. Red today.
  3. Negatives after `[Shade.Blue]`, each a compile-time error: bare `Red`;
     dotted `Shade.Blue`; the annotation `:Shade`. The first two pass today
     and are guards against the glob and parent-binding fixes.
  4. Control: `[Shade.*]` with the cell 1 body exits 7.
- *Arming:* cells 1 and 2 must fail on `undefined variable` or
  `unknown constructor in pattern` for the member. A module-load or parse
  failure is a fixture error.
- *Unit row (`dev`, `src/imports/tests.rs`):* a dotted specific entry
  yields one exposure whose local name is the bare member and whose source
  is `mathx/Shade.Blue`, and no exposure named `Shade`.
- *Notation:* `// defect: class=wrong-reject locus=src/imports.rs::collect_specific found=S123 owner=/dev`. <!-- doc-check: literal reason="Defect locus as it stood at S123; row D3 (42e6d929) removed the function" -->

**K-8 — export mounts and mixed member-glob lists
(ACT-1056 (closed at S124; Git history);
§8.4, §8.4.4, §8.3.11; audit R2)**

- *Harm:* a specified re-export pattern cannot be written, and a mixed
  names list silently drops entries, so a name the user listed is missing.
- *Wrong implementations:* the current parse rejection; a mount that parses
  but registers no alias; a mount that reaches only the re-exported subset;
  a mount-only form that re-exports names bare; a union that keeps only the
  first or only the last classification.
- *Fixture:* `mathx.cl` defines `square`, `cube` and `(deftype Shade Red Blue)`.
  `api.cl` holds the export under test. `app.cl` imports from `api` and
  returns the exit code.
- *Cells* (`--run`):
  1. `(export [(mathx math) [square]])`: bare `square` and qualified
     `api.math/cube` both resolve through `api`. Red today.
  2. Mount-only `(export [(mathx math) []])`, with `api` also defining one
     function and `app` importing `[api [*]]`: `api.math/square` resolves,
     and bare `square` in `app` is a compile-time error. The glob import is
     what lets the negative detect a bare re-export. Red today.
  3. `(import [mathx [Shade Shade.*]])`: `Shade.Blue` and bare `Blue` both
     resolve. Red today.
  4. `(import [mathx [Shade.* square]])`: bare `Blue` and `square` both
     resolve. Red today.
  5. Export symmetry: `api` holds `(export [mathx [Shade.* square]])`, and
     `app` imports `[api [*]]` and uses `square`. Red today.
  6. Controls: `(export [mathx [square]])`; the two-spec import
     `[mathx [Shade] mathx [Shade.*]]`.
- *Arming:* the mount cells must fail on the module-path rejection or an
  unresolved name, not on a missing fixture module.
- *Named residual:* §8.4.4's two mount-collision negatives belong to the
  correction's dispatch, once a mount can be represented.
- *Notation:* `// defect: class=wrong-reject locus=crates/cranelisp-frontend/src/module_extract.rs::parse_export_entries found=S123 owner=/dev` <!-- doc-check: literal reason="Defect locus as it stood at S123; row D3 (42e6d929) removed the function" -->
  on the mount cells, and `…::parse_names_list` on the union cells,
  provisional until `arch` frames the carrier.

**K-9 — a macro without fixed parameters is held to `Sexp`
(ACT-1057 (closed at S124; Git history);
[§9.2.3](../../spec/09-macros.md#923-return-type-constraint), §9.9.1)**

- *Harm:* an ill-typed macro is accepted, and invoking it aborts the
  compiler or the REPL process (`src/marshal.rs` misaligned dereference,
  exit 134).
- *Wrong implementations:* the current one; a check only at invocation,
  where §9.9.1 requires the error at the definition even when unused; a fix
  for the nullary shape that leaves rest-only or a nullary clause of a
  multi-clause macro open; a rejection at a synthetic location; a marshal
  guard that converts the abort but still accepts the definition.
- *Cells* (`--run`, no prelude; each `main` is `(primitives/Pure 0)` and
  never invokes the macro):
  1. `(defmacro bad [] 3.14)`, `(defmacro bad [& xs] 3.14)` and
     `(defmacro bad ([] 42) ([x] (quote 1)))` each exit non-zero with a
     diagnostic naming `Sexp`. Red today.
  2. Location: `(defmacro bad [x] 42)` on line 1 of a two-line file reports
     line 1. Red today: it reports `app.cl:3:1`.
  3. REPL: `(defmacro bad [] 3.14)` gives an error and no `; defmacro`
     echo, and a following `42` evaluates. Red today.
  4. Control: `(defmacro good [] (quote 7))` invoked in `main` exits 7.
- *Maintenance (`test`):* `tests/spec_09_macros.rs::macro_body_non_sexp_int_rejected_neg`
  and `::macro_body_non_sexp_bool_rejected_neg` accept any output that
  contains `Sexp`, which the success echo also contains. Assert the
  mismatch diagnostic and the absence of the `; defmacro` echo instead.
- *Not allocated:* a separate marshal guard. Rejecting the definition makes
  the abort unreachable.
- *Unit row (`dev`, frontend `defmacro` tests):* the synthesized clause
  constrains its body to `macros/Sexp` for nullary, rest-only and fixed
  clauses, located at the clause.
- *Notation:* `// defect: class=wrong-accept locus=crates/cranelisp-frontend/src/defmacro.rs::synthesize_macro_clause_defn found=S123 owner=/dev`.

*Fix recommendation.* K-7 is small and confined to `src/`, so it could
enter S123 with the user's approval. K-9 is small but needs frontend
`design` because it moves a diagnostic location. K-8 waits for the `arch`
gate with ACT-0997.

### 8.11 Phase 6b adequacy

**Verdict, 2026-11-16: adequate, with the limits below.** The 6b evidence
supports the Phase 6b → 7 checkpoint. No regression, no unclassified RED, and
no guard turned green.

The tree is `de20a40e` plus uncommitted coordination edits that touch no source
or test. The binary is `target/debug/cranelisp`, sha256 `684cc1e2…`. The
binary was unchanged across the sweep. QA's logs are under `.local/s123-6b/`:
`qa-full-suite.log`, `qa-user-samples.log`, `qa-demo-sweep.log` and
`qa-demos/`.

#### 8.11.1 Full suite (acceptance evidence)

There were 7,024 tests: 6,980 passed, 44 failed and 1 was skipped, in 196 s.
Every RED is a filed guard and fails on its clause assertion. No premise or
setup message appears.

| Filing | REDs |
|---|---|
| ACT-1050 | the twelve `bind_unused_heap_argument` subjects (marginal 1 or 2) |
| ACT-1056 (K-8) | six `spec_08_modules` mount and union cells |
| ACT-1057 (K-9) | five `spec_09_macros` cells |
| ACT-1034 | four `spec_07_traits` parametric-impl instance cells |
| ACT-1016 | `spec_08_modules` export-cycle run and startup; `repl_persist::reload_failed_reexport_dependency_matches_restart_neg` |
| ACT-1055 (K-7) | `selective_member_ctor_binds_bare_value_and_pattern`, `selective_member_trait_method_binds_bare_name` |
| ACT-0973 | `platform_errors` root and nested non-entry declarations |
| ACT-0997 | `box_import_renamed_binds_canonical_type`, `box_import_self_rename_is_accepted` |
| ACT-1038 | `trace_records_every_call_of_spark_admitted_callee` (288 of 465); `traced_spark_admitted_callee_releases_every_formatted_string` (residual 354) |
| ACT-1052 (K-6) | `cache::cache_restored_text_after_abi_change_preserves_importer_calls_across_modes`, leg 4 SIGSEGV |
| ACT-0985 | `spec_05_definitions::impl_body_uses_impl_declared_later_in_cluster` |
| ACT-1001 | `spec_08_modules::impl_ambiguous_trait_names_both_candidates_neg` |
| ACT-1036 | `spec_10_io::batch_main_non_io_return_refusal_is_located_at_main` |
| ACT-1018 | `exemplar_ownership_residue_s116::sudoku_warm_serial_solve_retains_nothing`, at 2 |
| ACT-1039 | `trace::trace_records_user_function_calls_in_every_mode` |

- *Delta from §8.1's 29 REDs:* 13 are K-7 to K-9, one is K-6 (committed
  after the W5 gate) and one is ACT-1038's second cell. That cell now fails
  deterministically because §8.8's premise holds.
- *Limit:* `export_mount_only_does_not_reexport_bare_names_neg` fails on the
  mount parse refusal. Its bare-name clause becomes reachable only after the
  fix (§8.11.5).
- **M-1 holds** (safety fence). No new cache exists under `tests/` or
  `examples/`. `exemplar/.cranelisp-cache/` dates from the W5 gate. The
  ignored root `user.cl` and `.cranelisp_history` date from September.

#### 8.11.2 M-3, the `user/` sample harness (maintenance check)

- QA's direct run of `tests/scripts/user_samples.py --binary
  target/debug/cranelisp` executed 83 fresh groups with no failure. The
  census found 18 documents and 158 classified fences: 67 REPL, 57
  definition and 34 illustrative.
- Both suite cells pass, the corpus cell and the detection cell.
- **Detection, accepted.** The fixture corpus moves sound (0) → planted wrong
  value (1) → unclassified fence (1) → restored (0). Each planted fault fails
  on its clause.
- *Limit:* no mutation proves the definition-error branch. The wrong outcome
  it leaves open is a definition whose diagnostic the checker misses. The
  sound-fixture docstring containing `error:` bounds this, and its harm is a
  doc claim, not compiler acceptance. QA accepts it as a named limit.
- Every exemption carries a specific reason. *Advisory to `docs`:* the two
  "input-only catalogue" exemptions (qualified and dotted binder rejections)
  could be exact REPL transcripts, per the prefer-repair rule.
- *Advisory to `docs`:* `user/guide/modules.md` links a reader to
  `sprints/actions/ACT-0997…`. That link breaks when the action is resolved
  and deleted. The document checker will catch it, but at someone else's
  change.

#### 8.11.3 M-4 and M-5, demos (diagnostic observer)

- QA's sweep completed 40 of 40: 14 active and 26 archived.
- Values were read from the transcripts, not inferred from the exit code.
  - `11-live-reload`: 10, 20, three lock refusals, help and source shown while
    locked, `/reset` unavailable, then 30, and 30 again after restart.
  - `ring4s` gives 50. `ring4p`'s replacement gives 43 with no ABI refusal.
  - `ring4e` shows `Module 'math' not found.`
  - `ring4i` and `ring4d` end on their panic.
- Every diagnostic line in the sweep is narrated as intended.
- *Not re-run by QA:* the `optimization.demo` IR comparison. QA accepts
  `test`'s nine byte-identical blocks
  (`.local/s123-6b/test-demos/optimization-ir-comparison.txt`).

#### 8.11.4 The `examples/` replay

- `training` reports 152 of 152: 38 entries in four cells each.
- The suite's seven `examples` cells pass. These include
  `every_example_runs_with_documented_exit` and
  `every_example_links_and_executes_with_documented_exit`.
- QA did not re-run `training`'s replay. The two suite cells are the
  executing evidence for the documented exits.

#### 8.11.5 K-7, K-8 and K-9 (acceptance; safety fences once fixed)

QA accepts `test`'s clause map against this record's §8.10, with no return.
The map is in `.local/s123-6b/test2-report.md`.

- *K-7.* Both REDs fail on `undefined variable: Blue` and `seven`. The three
  negatives and the `[Shade.*]` control pass. The negatives are vacuous until
  the positive row passes; they are guards against glob and parent-binding
  fixes.
- *K-8.* The mount cells fail on `expected symbol for export module path`.
  The union cells fail on an undefined `square` or `Shade.Blue`. Both
  controls pass. The mount-collision negatives remain owed by the
  correction's dispatch.
- *K-9.* The three shapes fail on acceptance with exit 0. The REPL cell fails
  on the `; defmacro` echo. The location cell fails on `app.cl:3:1` at span
  `1000007..1000006`. The quoted-body control passes.
  - The tightened observers detect acceptance: substituting a valid body made
    both fail (`test2-macro-success-detection.log`).
- *Not claimed:* the clauses behind today's refusal points are not yet
  independently reached. Each fix's GREEN run is their first observation.

#### 8.11.6 FIXME 0907: not closed

The legs listed in §8.9 that are met at source on `de20a40e`:

- `test`: no `ctor_shapes` notation remains in `spec_10_io.rs` or
  `ctor_as_value.rs`, and the two fixed-S102 notes are kept. The five cells
  pass.
- `test`: `ring4s` replays the working segment at 50.
  The demo guide now links QA's attribution.
- `docs` and `training` were satisfied in S122.

Still open, both carried to S124 by the dispatch log:

- `dev` on `stdlib/`: the six `core.io` self-tests.
  [`plan-stdlib.md` §6.2](../../stdlib/plan-stdlib.md) is still open, and
  `stdlib/core/io/` holds no `test.cl`.
- `spec` on `repl/`: obligation 3, whether `/info Bind` and `/info IO` must
  introspect.

#### 8.11.7 Traceability band

Restored on 2026-11-16. Annotations only; the requirement prose is unchanged.

- `spec/08-modules.md`:
  - §8.3.11 names the K-7 and K-8 union REDs, the vacuous negatives and the
    controls.
  - §8.4 is graded partial: export symmetry is RED, and §8.4.4 fails.
  - §8.4.4 names the three mount REDs. It records that its two older citing
    cells observe unmounted re-export.
- `spec/09-macros.md`:
  - §9.2 and §9.9 are graded partial.
  - §9.2.3 is Tested+Neg for the fixed-parameter shape, with the four K-9
    acceptance REDs.
  - §9.9.1 names the location RED.
- The 6b re-grade of the REPL redefinition specification's interim
  ownership-ABI section (18.1.2, retired in S124) stands.
- The export link in ACT-1056 no longer embeds the old annotation.
- The spec reconcile shows 0 dead citations and 0 cleared awaiting QA. The
  link check shows 0 malformed and 0 mis-cited.

#### 8.11.8 What Phase 7 needs from this evidence

**Action dispositions.**

- *Open and carried, each with a standing RED:* ACT-1050, ACT-1049,
  ACT-1018, ACT-1052, ACT-1038, ACT-1039, ACT-0973, ACT-0985, ACT-0997,
  ACT-1001, ACT-1016, ACT-1034 and ACT-1036 (§8.6).
- ACT-1056 carries with ACT-0997 to the `arch` gate.
- ACT-1055 and ACT-1057 carry unless the user pulls them in (§8.11.9).
- ACT-1049 has no RED. It is a false positive of an instrument.

**The carries list adds:**

- FIXME 0907's two legs (§8.11.6);
- §17.4's file-supplied-provider combination cell (`test`);
- the missing `fixed=` stamp on
  `string_primitive_value_discharge::str_len_as_function_value_releases_its_argument_once`
  (`test`);
- the `PlatformError::DispatchError` wording in the rustdoc of
  `platforms/test-capture/src/lib.rs` (QA-owned, needs a source-editing
  dispatch);
- the §8.11.2 advisories (`docs`).

**Acceptance on a fresh build of the final close tree.** A pull-in, or any
source change after `de20a40e`, voids the reuse of this run.

1. Run `cargo build` and the full `cargo nextest run --no-fail-fast` once.
   The RED set must equal §8.11.1's 44 names, less any cells a pulled fix
   flips. Any other RED is a regression, and any other flip needs attribution.
2. Run `bash tests/scripts/run-agent-lane.sh` if anything under `src/`
   changed after `b89cc7cc`. It must give 91 of 91 and 23 passed with 10
   skipped.
3. Check the plain-build REPL banner and a project `.env` supplying a
   `CRANELISP_*` setting. These are the settling target's third item, with
   cells in the suite.
4. Run the `user/` harness and the demo sweep once each. Run the document
   checker, the spec reconcile and the link check. Each must exit 0.
5. Confirm the public-API baselines equal the live output. A src-only or
   frontend-interior fix must show +0/−0.

#### 8.11.9 Evidence for a pull-in of ACT-1055 or ACT-1057

**ACT-1055 (`dev` on `src/`).**

- *Before the fix:* the K-7 unit row in `src/imports/tests.rs`, observed red.
  It expects one exposure with bare local name `Blue` from `mathx/Shade.Blue`
  and none named `Shade`.
- *Recommended, cheap:* one REPL leg of K-7 cell 1. This guards the
  `mode-divergence` class.
- *After the fix:*
  - both K-7 REDs pass;
  - the three negatives pass, and now non-vacuously;
  - the two K-8 union cells and the six K-8 cells stay RED, because their
    loci are frontend. If a K-8 cell flips, QA attributes it before it counts.
- *Also required:*
  - `dev`'s gate;
  - `review` in a fresh subagent;
  - `docs` removes the `Symbol.member` limit from the modules guide, with
    the harness re-run;
  - QA restores the `Symbol.member` row of spec §8.3.11.
- *Size:* small. No public type changes.

**ACT-1057 (`design`(frontend), then `dev` on the frontend).**

- *Before the fix:* `design` places the `Sexp` constraint and the
  definition-site location. The K-9 unit row covers nullary, rest-only and
  fixed clauses at the clause location, observed red first.
- *After the fix:*
  - all five K-9 REDs pass;
  - both tightened observers and the control stay green;
  - `display_exact.rs`'s synthetic-span pin and every other located-macro
    diagnostic are re-read for movement.
- *Highest collateral risk:* the fix newly rejects an existing macro without
  fixed parameters. The stdlib has two such generators in `stdlib/defs.cl`,
  and `user/`, `examples/` and the exemplar hold others.
  - So the whole-suite run is not enough on its own. Name these as
    discriminating evidence: `stdlib_conformance`, both `examples` replay
    cells, the exemplar runs, and the `user/` harness.
- *Also required:*
  - `review` in a fresh subagent;
  - `docs` re-reads the macros guide's return-type statement;
  - QA restores §9.2.3 and §9.9.1.
- *Size:* larger than ACT-1055, and it has a design step. A pull-in adds a
  Phase 5-style wave, not a 6b edit.
