# `--test` and the shared test runner

**Owner:** `design` (int). **Status:** implemented and verified in `src/`,
except §6.5 (the test child) and the location of the batch refusal of
`discover-tests` (§7.3, Location), which is built at `52de1aad` and awaits
review and the suite run. `dev`(src) built §6.5 in S123 W1, and `design`
(int) checked it against source on 2026-11-15. Independent review and the
suite run are still to come. The child runs §§6.2–6.3 in its own process.
Verification evidence and acceptance status are recorded in `sprints/archive/sprint-122.md`.
A missing entry file is refused at entry registration, not by the runner
([int §6.1.1](int.md#611-a-missing-entry-source-file)).
**Subordinate to:** [`int.md`](int.md). **Scope:** `src/`.

Governing inputs, cited rather than restated:

- Requirements: [CLI invocation §0.2.2](../../repl/spec/00-cli-invocation.md#022-test-mode---test-s122)
  and [test discovery](../../repl/spec/16-test-discovery.md) §§16.1–16.2 and
  §16.6. The user's rulings of 2026-09-28 in `sprints/archive/sprint-122.md` ("Automatic
  test-runner scope settled") govern wherever `spec` has not yet absorbed
  them, notably the library stop and the `--test` refusal (section 2).
- Boundary: [test discovery, explicit harness](../arch/test-discovery.md#explicit-test-harness--the-compiler-runner).
- Public entry point: the user-approved delta of 2026-09-28, recorded in
  `sprints/archive/sprint-122.md`. It adds `CompilerSession::run_tests(&self) ->
  Result<TestRunReport, CranelispError>`, a `TestRunReport` with private fields
  and `text`, `warnings` and `exit_code` accessors, and one `session_v4`
  re-export. As built, this design adds no other public item. The S123 test
  child (§6.5) adopts packet row P12 (`sprints/s123-api-packet.md`), which
  awaits the user's gate: `run_tests` becomes the child's engine and
  `session_v4::supervise_tests` returns the report.

## 1. Solution

`--test`, `/run-tests` and `/run-all-tests` are one runner. Scanning, running,
reporting and the `discover-tests` refusal are one implementation each. The
clients differ only in which modules they select and in what the host does
with the report (§16.2): `--test` writes it and exits with its code, and the
REPL displays it and continues.

1. **Select.** Each client names a set of modules:
   - `--test` walks the entry module's chain over published symbol tables,
     stopping at non-project modules (§4.2);
   - `/run-tests` selects the current or named module;
   - `/run-all-tests` selects every loaded module that is not a library module
     under the §4.1 classifier.
2. **Scan.** One eligibility scan lists each selected module's tests, in fully
   qualified (FQ) name order. It excludes every `test-` function whose scheme
   is not exactly `(Fn [] (Option String))` and records a warning for it (§5).
   The `discover-tests` extern uses the same scan.
3. **Prepare.** For each test, one entry read captures its code pointer, its
   code owner and its result-release target (§6.1). Any failure before this
   point is `Err`, and no test has run.
4. **Execute.** Each test runs on the calling thread with runtime errors
   captured. Its outcome is pass, fail or panic. A clean result is observed and
   then released exactly once through the program-result owner (§6.2).
   Execution has no error return. Under §6.5, steps 1–4 run in a child
   process that restarts after a panic, because a panic now ends its process;
   the client's process supervises it and reports (§6.5).
5. **Report.** The outcomes, the warnings and the exit code form one
   `TestRunReport`, whose text is identical for every client (§6.4).

As built, the `--test` driver in `main.rs` compiles exactly as `--run` does,
then calls `run_tests` instead of `trampoline` (§7.1). Under §6.5 that driver is
the test child, and `--test` itself is the supervisor. `main` is neither validated nor
called: `validate_main` runs only at the `--run` and `--link` driver seams.
`discover-tests` is REPL-only. The three batch driver seams — `trampoline`,
`link_by_name` and `run_tests` — refuse a compiled reference to it through
one gate with one diagnostic (§7.3). The runner never installs the extern's
runner state (§6.3).

| § | Topic |
|---|---|
| 2 | Rulings applied |
| 3 | Module map |
| 4 | Selection: classification and the chain walk |
| 5 | The eligibility scan |
| 6 | Prepare, execute and report |
| 7 | Clients: `--test` and the REPL commands |
| 8 | Failure behaviour |
| 9 | Assurance |
| 10 | Unit-test design |
| 11 | Rejected alternatives and potential extensions |
| 12 | Residual leads |

## 2. Rulings applied

| Ruling | Carrier | Design |
|---|---|---|
| `--test`, `/run-tests` and `/run-all-tests` use exactly the same code; only selection and the host's handling of the outcome differ | User, 2026-09-28; §16.2 | One scan, runner and report (§§5–6); no client-specific report or refusal text |
| Chain edges: an `import` or `export` with a non-empty names list, and a declared child; not a null import, an alias-only import or an FQ auto-load | §0.2.2 | Edge admission (§4.2) |
| The walk stops at library modules: a library module contributes no tests, and its imports and declared children are not followed | User, 2026-09-28 | Traversal (§4.2) |
| The implicit prelude is an edge only when the prelude is a project module | §0.2.2 | Falls out of the library stop (§4.2) |
| Library by resolution tier, even for a lib directory inside the project | §0.2.2 | The classifier (§4.1) |
| `--run`, `--link` and `--test` refuse any compiled reference to `discover-tests`; an import alone is allowed | §16.6; user, 2026-09-28, for `--test` | One gate at the three batch seams (§7.3) |
| `discover-tests` is REPL-only; under `--test` the compiler's runner discovers and runs tests | §16.6 | No runner state (§6.3) |
| `--run` output equals the linked executable's output, with the same capabilities | §0.2.1 | One §7.3 gate serves both; `--test` neither links nor calls `main` |
| `--test` with `--run` or `--link` is a usage error; `-o` is rejected; a missing entry file exits 1; warnings go to stderr; agent, worker and `--no-cache` flags behave as for `--run` | §0.2.2 | Flag parsing, entry registration's batch refusal ([int §6.1.1](int.md#611-a-missing-entry-source-file)) and the `--test` arms (§7.1) |
| An empty run reports `No tests found`; `--test` exits 0 | §16.2, §0.2.2 | The report (§6.4) |

Two readings follow from the standing text:

- **The entry module is a test module.** §0.2.2 names "the entry module
  resolved from `[target]`" in the set before the project-module condition.
- **A declared child takes its parent's class.** §0.2.2 classifies by
  "submodule of a project module" and "submodule of a library module". §8.2.5
  places a child's file in its parent's directory, so a conforming resolver
  never gives a child a tier different from its parent's. Where the current
  resolver does, the divergence is a §8.2.5 conformance lead (§12).

## 3. Module map

The runner lives under `src/session_v4/test_runner/`, one submodule per
responsibility, each with its own test module (Principle 23):

| Home | Responsibility |
|---|---|
| `discovery` | The shared definition predicate, the runner scan and its warnings (§5); `/tests-for` uses the predicate directly |
| `selection` | The classifier and the chain walk (§4) |
| `run` | Preparation, execution, the report and `TestRunReport`, plus the `impl CompilerSession` block holding `run_tests` |
| `child` | The test-child protocol (§6.5): the record codec that `run_tests` writes and the supervisor reads, the child command line, the ending classifier and `supervise_tests`. The process launch is injected so its unit rows script child endings |
| parent `test_runner.rs` | `discover-tests`, `TestRunnerState` and the heap marshalling, REPL-only; the extern lists tests through the shared scan |

The extern stays in the parent rather than a fourth submodule; the runner
does not change its behaviour, so moving it would buy no separation.

`src/repl/commands.rs` keeps only what is specific to each command: its
selection, its readiness wait and displaying the report.

The batch refusal gate (§7.3) is `refuse_dev_session_externs` in the
crate-private `exe` module beside `validate_main`, the one gate for all three
batch seams.

## 4. Selection

### 4.1 Classifier

A module's class is one of **project**, **library** or **unfiled**. Every read
is a keyed read of settled state:

1. The session's entry module is **project**.
2. A declared child takes its parent's class, recursively. A module `m` is a
   declared child when its parent's table records a `submodules` declaration
   whose derived child path equals `m`. The comparison uses the same
   `imports::declared_child_path` derivation that enrolment uses.
3. Otherwise, a module whose recorded `TypecheckProduct.file_path` equals its
   **project-root candidate path** is **project**. A module with any other
   recorded file is **library**, and one with no recorded file is **unfiled**.
   Synthetic, platform and REPL-created modules are unfiled.

Rule 3 applies the search tier, as §0.2.2 requires, and is not a path-prefix
test. The resolver tries the project-root candidate first, so a recorded file
equals that candidate exactly when tier 2 resolved the module.

- `pipeline::project_root_candidate` is the one candidate derivation; both
  `resolve_module_file` and the classifier call it, so the two cannot build
  the path differently (Principle 7).
- Under the default `{project_root}/stdlib/` lib directory, module `stdlib.foo`
  and module `foo` can resolve to the same file. `stdlib.foo` is project,
  because its candidate is `{root}/stdlib/foo.cl`. `foo` is library, because
  its candidate is `{root}/foo.cl`. A path-prefix test gets this case wrong
  (§11).

**`file_path` is recorded in every mode.** The fresh dependency prologue
(`process_form/dependency.rs`, `register_dep`) and entry registration
(`register_entry_module`) record the resolved file whether or not
introspection is on, as cache restore does, so batch and REPL, fresh and
cached, classify alike. `source_text` remains REPL-only.

Membership by client:

- `--test` selects project modules only (§4.2).
- `/run-all-tests` selects every loaded module except library modules. This
  includes REPL-created (unfiled) modules; synthetic and platform modules
  define no `test-` functions.

### 4.2 Chain walk (`--test`)

The walk is breadth-first from the entry module over the published tables.
Principle 17 forbids import-closure walks for name resolution; this walk
selects modules and resolves no name.

- **Edges from module `m`:**
  - each `imports` entry and each `exports` entry, resolved through
    `imports::DeclaredChildren` built from `m`'s recorded `submodules`. This is
    the settled-table reader row of [int.md §6.9](int.md#69-bare-module-names-in-import-and-export);
  - each `submodules` declaration, taken as its derived child path;
  - the prelude, when `m`'s implicit-prelude bit (`SharedState.prelude_fallback`)
    is on and the prelude has a published table. The bit can be on in a session
    with no prelude file; that adds no edge and is not the missing-table error
    below. The prelude's identity is `expander::PRELUDE_MODULE`, the one the
    int-side installer uses to set that bit and load the prelude; the walk does
    not add another spelling of the name (Principle 7).
- **Admission.** `import` and `export` entries are classified by their names
  form. Specific, glob and member-glob entries are admitted. Alias-only and
  null (`ImportNames::None`) entries are not (§0.2.2). An FQ auto-load leaves
  no entry and is never an edge. None of the excluded forms loads a module, so
  the admitted edges are a subset of what `--run` compiles (Principle 11).
- **Traversal.** A reached module is visited once and classified. A project
  module is selected and its edges are followed. Any other module is neither
  selected nor expanded: the walk stops there. A library prelude, whether
  reached through the implicit edge or an explicit `import`, therefore brings
  in nothing, and a project module reachable only through a library module is
  not selected.
- **Missing table.** An admitted edge whose target has no published table is an
  int invariant error, returned as `Err` before any test runs. Successful
  compilation loads every admitted edge's target, so this can occur only
  through a defect.
- **Cache parity.** Cache restore enrols declared children through the fresh
  path's mechanism (`process_form/cache_restore.rs`, which calls
  `enrol_declared_submodule`). The walk's input tables are therefore the same on
  fresh and cached runs. The permanent discriminator for that property is
  FIXME 0868's cache-restored-child cell. The FIXME's disposition belongs to its
  target role.

## 5. The eligibility scan

`/tests-for` filters through discovery's `classify_test_definition` predicate.
The runner scan uses the same predicate and reports warnings for mistyped
definitions; `/tests-for` only filters its referers and emits no warnings.

One scan reads a module's table. For each **callable definition homed in that
module** whose name starts with `test-` (internal listing entries excluded), it
applies one check: is the recorded scheme exactly `(Fn [] (Option String))`?

- If yes, the scan returns the test's typed identity, the module and symbol.
  Identities are not passed on as `"module/name"` strings (Principle 24,
  corollary). The FQ string is formatted only for display.
- If no, the test is excluded and a `Warning` is recorded with
  `WarningKind::Other`, the definition's span, and a message giving the FQ name
  and the actual scheme.

The exact-scheme check is a soundness condition: execution decodes the returned
word as an `(Option String)` (test-discovery §"Explicit test harness"). Imported
and re-exported candidates are not definitions of the importing module, so a
test appears once, under its home module. Results are sorted by FQ name.

The recorded scheme is the one typecheck publishes. Typecheck pins a
degenerate polymorphic `test-` function to its concrete test type
([monomorphisation §3.2](../typecheck/monomorphisation.md#32-roots)), so, for
example, `(defn test-e [] None)` records `(Fn [] (Option String))` and is
admitted.

The scan does not require a GOT slot or code; preparation reads those (§6.1),
so an eligible test without code is reported, never skipped.
The `discover-tests` extern, reachable only in the REPL, calls the same scan.
It runs inside compiled code, has no warning channel and discards the
warnings (§12).

## 6. Prepare, execute and report

### 6.1 Prepare

Preparation is fallible, and all of it happens before any test runs.
`run_tests` first refuses a run that cannot start: an entry module with no
recorded source file (§7.1), then a compiled reference to `discover-tests`
(§7.3). Then:

1. **Readiness.** Call `wait_cached_loads_settled` to obtain the
   `ExecutionReadiness` value ([int.md §7.1](int.md#71-cache-hit-flow-inside-register_module)).
   `run_tests` obtains it itself; the REPL commands obtain it after their own
   per-module waits. `run_tests`'s documented precondition is that
   `register_module` and `wait_inmem_complete` have returned `Ok`.
2. **Selection and scan.** Selection (§4) and the eligibility scan (§5).
3. **Entry read.** One read per test, under one table guard, captures the code
   pointer from the test's GOT slot, a clone of its `Code` owner and the
   release key from its codegen view. This is result-owner §4.3's same-read
   rule. The guard is dropped, and the release target is then resolved through
   the program-result adapters (§6.2), before any test is called.
   - A test with no compiled body code or a null slot is not an error. It is
     marked unavailable and reported as `FAILED: test function not found`. It
     never counts as a pass.
   - A release-target failure is one of result-owner §5's hard integration
     errors, and preparation returns it as `Err`.

### 6.2 Execute

For each prepared test, in FQ order. Under §6.5 this runs in the child, and
step 4 is followed by the test's outcome record. Steps 1 and 3 are the
pre-S123 shape. S123 retired them: a panic ends the process, so no slot is
left to read, and the runner has no error slot:

1. Clear the calling thread's runtime-error slot.
2. Call the captured pointer while holding the cloned code owner (Principle 22).
   The runner compiles no form, so a test never runs inside a `(trace …)`
   wrapper (REPL §16.2, *Tracing*, and §16.4).
3. If the error slot is now set, the outcome is **panic**. No owner is created
   and no release glue runs, because a trap produces no result (result-owner §5).
4. Otherwise build the owner from the prepared target. That step cannot fail.
   Observe the word: `None` is **pass**; for `(Some reason)`, copy the reason
   out, and the outcome is **fail**. Then release the word exactly once.
   `(Option String)` is a `Mixed` result, so a `None` is released too. The
   canonical glue's nullary guard handles the bare tag.

The owner code is split so that preparation can run first:

- a crate-private **release plan** does the key, classification and adapter
  resolution, and is fallible;
- an infallible step then builds the owner from a plan and a word.

`OwnedProgramResult::new` is itself plan-then-own, so the classification path
has one implementation. Tests are therefore another execution seam of
[the result owner](result-owner.md). A cache-restored test module reaches the
`Code::Linker` adapter (§3.2).

### 6.3 Runner state

The runner never installs the `discover-tests` runner state. Under `--test` no
test can reach the extern, because `run_tests` refuses a compiled reference
before preparation (§7.3). As built, a test that calls `discover-tests`
during `/run-tests` sees the state that REPL evaluation already maintains.
Under §6.5 every test runs in a `--test` child, so that reference is refused
in every client.

### 6.4 Report

The outcomes, the warnings and the elapsed time produce a `TestRunReport`. Its
text is the same for every client:

- one line per test gives the FQ name, dot padding, and `ok`,
  `FAILED: <reason>` or `PANIC: <message>`; a blank line and the summary
  follow;
- with no eligible test, the text is exactly `No tests found`, in every
  client.

The exit code is 0 when no test failed or panicked, including an empty run;
otherwise 1. It is computed only inside the report from its own outcomes.
Because the fields are private, a report whose code disagrees with its text
cannot be built (Principle 20).

### 6.5 The test child

Status: designed in S123 Phase 3. Built in S123 W1 and checked against
source on 2026-11-15; the as-built departures are recorded under *Cache
use* and *Child arguments* below. *The cause of a fail* was decided after
that check. As built, the reason names only the exit status, and the change
is for `dev`. A runtime panic ends its
process ([io-integration §1.2](io-integration.md#12-a-runtime-panic-ends-the-process-the-host-side)).
The user's ruling (2026-11-15) is one child process that restarts after a
panic. The runner therefore splits into a **supervisor**, which never
compiles or runs a test, and a **child**, which runs the §§4–6.2 runner and
streams one record per test.

- **Entry points** (packet row P12, adopted as named):
  - `session_v4::supervise_tests(child_args, modules) -> Result<TestRunReport, CranelispError>`
    is the supervisor. It needs no session. `--test` calls it before any
    session exists (§7.1), and `/run-tests` and `/run-all-tests` call it with
    their selection (§7.2). `Err` means the run could not start, or a child
    ended with neither an open test nor `end` (table below).
  - `CompilerSession::run_tests(records, modules, resume_after) -> Result<(), CranelispError>`
    is the child's engine. It runs the selected tests in its own process,
    appends one record per test to `records`, and runs only tests after
    `resume_after`. `modules` is the REPL's selection; `None` walks the entry
    chain (§4.2). `Err` keeps its meaning: the run could not start, and no test
    has run.
- **The supervisor** is the client's process: `main.rs` under `--test`, or the
  REPL under `/run-tests` and `/run-all-tests`. It:
  1. starts the child: `current_exe()` with `child_args`, then `--test` and the
     child arguments: a record-file path in a per-run temporary directory,
     the selected modules when the client is the REPL and, after a restart, a
     resume point. `child_args` are the client's own command-line arguments
     without its mode flag: `main.rs` drops `--test`, and the REPL passes the
     arguments its process started with, which hold no mode flag. Every such
     argument parses under `--test` (§7.1), so the child resolves the same
     target with the same worker and cache settings, through the same parser,
     and no second list of compile-affecting flags exists. P12's
     compile-affecting `child_args` are therefore these arguments; the rest,
     such as colour and agent flags, change nothing under `--test`. Library, platform
     and prelude locations come from the environment and the project files,
     which the child shares. The child inherits the parent's environment,
     which already holds the file supply, with `CRANELISP_NO_ENV=1` added
     ([environment §2.2](environment.md#22-algorithm));
  2. reads the record file when the child ends and classifies the ending
     (below);
  3. restarts the child after the open test if a test was open, and otherwise
     stops;
  4. builds the one `TestRunReport` (§6.4) from the records and the elapsed
     wall time.
- **Selection input.** Under `--test` the child walks the entry chain itself
  (§4.2), so the supervisor compiles nothing and `--test` costs one compile, as
  before. The REPL commands pass the module list they selected (§4.1, §7.2).
  The child loads each module and what it reaches.
- **The child** runs selection, the eligibility scan (§5), preparation (§6.1)
  and execution (§6.2) as one process does today. For each test, in FQ order,
  it appends `start <fq>` before calling it and the outcome after releasing
  its result: pass, fail with its reason, or unavailable. Warnings precede
  the first `start`, and `end` follows the last outcome. Each record is one
  `write` on the record file, so it survives the process ending at a panic.
  The record format is private to the runner module and encodes reasons that
  span lines.
- **The resume point** is an FQ name. A restarted child runs only the eligible
  tests that sort after it. The order is the FQ order, so the resume point is
  well defined even if a restart sees a different set.

| The child ended with | Outcome |
|---|---|
| `end` | done; the run is complete |
| an open `start <fq>`, the panic exit status, and a stderr line beginning with the panic report prefix | `<fq>` is **panic**: `PANIC: <message>`, where the message is the rest of the last such line. Restart after `<fq>` |
| an open `start <fq>` and another exit status | `<fq>` is **fail**. The reason carries the status and the child's final stderr line, when it wrote one (*The cause of a fail*, below). Restart after `<fq>` |
| an open `start <fq>` and a signal | `<fq>` is **fail**, naming the signal. Restart after `<fq>` |
| no open `start` and no `end` (a compile error, the §7.3 refusal, a readiness failure, or a death between tests) | the run is `Err`. The child's diagnostic has already reached stderr. A restart would not progress, so none is made |

- **Termination is structural.** Every restart follows a child that consumed
  at least one test, so a run of `N` tests uses at most `N + 1` children.
- **Warnings** come from the first child only. A restart rescans the same
  sources, so its warnings would repeat.
- **The panic constants.** The classifier reads
  `cranelisp_intrinsics::panic::PANIC_EXIT_STATUS` and `PANIC_REPORT_PREFIX`
  (packet row P11), so the terminator and the supervisor share one copy
  (Principle 07). The status is shared with other failures, so the table
  classifies a panic by the status and the prefixed line together, never by
  the status alone. If the user declines P11, int keeps a crate-private copy,
  and the end-to-end panic cell is the measured guard against drift.
- **Streams.** The child's stdout is inherited, so a test's output appears as
  it is written. Its stderr is piped and relayed line by line to the parent's
  stderr as it arrives. The parent keeps the last line that starts with the
  prefix. So a panic's own report appears on stderr when it happens, and its
  message appears again in the report's `PANIC:` line. Whether that repetition
  is wanted is `spec`'s. The parent also keeps the last line of any kind, for
  the next bullet.
- **The cause of a fail.** The user ruled that a test child shows a dispatch
  fault as a failed test naming the cause (2026-11-15). The cause must be
  in the test's `FAILED:` line. The relayed stderr is not enough:
  - it is not attributed to any test, and it reaches a different stream from
    the report, so a reader of the report under `--test`, or of the REPL's
    report text, sees only an exit status;
  - a panic's message already appears in its `PANIC:` line, and a fail
    should name its cause the same way.

  The supervisor therefore uses the child's final stderr line. That line is
  the fault report whenever the runtime ended the process. The terminator is
  the only fault exit. It flushes stdout, writes its one-line report in one
  write and exits, and any later claimant parks without writing
  ([process lifecycle §1.1](../intrinsics/process-lifecycle.md#11-one-terminator)).
  A platform DLL's own panic hook writes the fault text before that report,
  so the report is still last. The rule covers every non-panic fault the
  terminator reports, so it needs no prefix for dispatch faults and no
  shared wording constant. §12.7.6 leaves the wording unfixed.

  A signal leaves no report, so a signalled fail names only the signal. A
  status ending with no stderr line names only the status. The reason's
  wording is `spec`'s (S123-Q13).
  - *Residual.* Two writers can follow the report: the opt-in statistics
    printers registered with `atexit` (`CRANELISP_RC_STATS`, for example),
    and a host Rust panic, whose final line is the backtrace hint. In both
    cases the reason names the wrong line, and the whole stderr has still
    been relayed. *Grade: asserted, with a named falsifier:* a child ended by
    the terminator, with no statistics variable set, whose final stderr line
    is not the terminator's report.
  - *Reachability.* An eligible test is `(Fn [] (Option String))` and cannot
    force a platform effect, so no test can raise a dispatch fault today
    ([evidence delta](../../tests/plan/s123-evidence-delta.md), P-7). The
    same row reports any other non-panic fault the terminator ends a test
    with, such as a runtime defect caught in a spark. The evidence is unit
    grade (§10, test child row 9). Trigger for an end-to-end cell: an eligible
    test that can force a platform effect.
- **Cache use.** Children run one at a time.
  - **Under `--test`**, the child reads and writes the object cache as
    `--run` does, so a later run and a restarted child start warm.
  - **The REPL child** is the child given a module selection. It must not
    write the cache, because the REPL's own background workers write the
    same entries. As built, it runs as if `--no-cache` were given
    (`Action::forces_no_cache` in `src/main.rs`) and skips the object wait.
    `--no-cache` turns off cache reads as well as writes, so the REPL child
    compiles its selection from source, again after each panic.
  - **Why reads are off too.** The process has no mode that reads the cache
    without writing it. In-memory-only codegen would need a new
    `cranelisp_types::CodegenBehaviour` variant. A read-only cache setting
    would need a new `SessionSettings` field in the root crate. Each change
    goes to the inter-crate public-API gate. The as-built child keeps the
    one rule this design needs, that it never writes, without either change.
  - **A panic can end a child mid-write.** Cache writes are atomic (arch
    §1.7), so the next child or session only misses. The object's atomic
    publication is designed and not built
    ([int §7.7](int.md#77-one-generation-beside-an-entry-act-1083)); until it
    is, a child ended mid-write can leave a partial object.
- **`discover-tests` in a child is refused** (user ruling, 2026-11-15). The
  child is a `--test` process, so `run_tests`' existing gate refuses a compiled
  reference before preparation (§7.3). Under `/run-tests` this is now the
  run's `Err`, where the test used to run. No new check exists.
- **Measured cost** (2026-11-15, debug binary at `f747990f`, single shots,
  order of magnitude). A project importing the exemplar's modules ran 44 tests
  under `--test` in 16.0–16.9 s, of which startup and compile were about
  0.8–1.7 s. Under this design a run costs one child startup plus one compile,
  usually from cache, for each panic. With no panic, `--test` costs what it
  costs today plus one process start. A REPL `/run-tests` adds a compile
  that the in-session run did not have. Because the REPL child reads no
  cache, that compile is cold: one at the start, and one more for each panic.
  The 0.8–1.7 s figure above is not split into warm and cold compiles, so the
  cold-compile penalty has not been measured. *Grade: asserted, with a
  named falsifier.* The cost matters if a cold child compile of the
  exemplar selection takes as long as that selection's tests, which run for
  about 15 s. The falsifier is one REPL `/run-tests` of that selection
  with no panic, timed against `--test` with a warm cache. Trigger for the
  read-only cache mode: that measurement, or a user report that `/run-tests`
  is slow. Falsifier for the restart estimate: a measured restart whose
  startup differs from that non-test time by more than a factor of two.
- **Consequences to state (`spec`).** A REPL child compiles from the files on
  disk, so a definition held "in the session only" after a refused
  regeneration ([REPL lifecycle §1.3.1](repl-lifecycle.md#131-session-lock))
  is not what the child tests. The record format is private to the runner.
- **Child arguments.** §0.2.2 makes them internal and undocumented, and
  leaves their spelling to the implementation (user ruling, 2026-11-15).
  As built:

  | Argument | Carries |
  |---|---|
  | `--test-child-records <path>` | The record file. Its presence makes a `--test` process the child |
  | `--test-child-module <module>` | One selected module, repeated in selection order. Absent under `--test`, where the child walks the chain |
  | `--test-child-resume <fq>` | The resume point |

  - The usage text does not list them.
  - Without `--test` they are a usage error. With `--test`, the module and
    resume arguments require the record file.
  - The spellings live in two places: the launcher constants in `child.rs`
    and the parser constants in `main.rs`. They are not shared because
    `main.rs` is the binary target, and sharing them would need a public
    item in the root library. *Grade: measured.* If the copies drift, the
    parser rejects the child's command line, and every `--test` cell in
    `tests/test_runner.rs` fails.
- **The stdlib runner carries no panic isolation** (user ruling, 2026-11-15,
  [evidence delta §1.1](../../tests/plan/s123-evidence-delta.md#11-the-stdlib-runner-carries-no-panic-isolation)).
  This supervisor is the isolation. A panicking test in a direct in-language
  run ends that process like any other panic (`spec/12-runtime.md` §12.7.4):
  later tests do not run and no tally prints. Int adds no host extern or
  launch capability for that runner, and it does not launch this child.
- **Potential extension.** A per-test timeout. Trigger: a hanging-test
  requirement.

## 7. Clients

### 7.1 `--test` (`main.rs`)

- Each `--test` action is binary-private. It maps to
  `CodegenBehaviour::InMemoryAndObject` and to `RunMode::Run`, which is
  Principle 11's one compile path. The steps below are the in-process run
  that the S123 child keeps, with the changes listed at the end of this
  section.
- `parse_args` recognises `--test`, and one mode validation decides the action
  from the parsed flags:
  - at most one of `--run`, `--test` and `--link`; any combination is a usage
    error;
  - `-o`/`--output` only with `--link`, so it is rejected under `--test`;
  - `--no-cache` is rejected only with `--link`;
  - every usage error prints its message and the usage hint to stderr and
    exits 1 (§0.3);
  - the target, worker flags, `--no-cache` and agent flags parse as for
    `--run`.
- The arm runs these steps in order:
  1. `startup?`, then `wait_inmem_complete`. A compile failure goes to stderr
     with exit 1 through the existing `run` error path, and no test runs. A
     missing entry source file (§0.5.5) fails here: batch entry registration
     refuses it, naming the expected file
     ([int §6.1.1](int.md#611-a-missing-entry-source-file)).
  2. Call `run_tests`. An `Err`, including the §7.3 refusal, takes the same
     error path.
  3. Write each warning to stderr.
  4. Write the text and a newline to stdout, then flush stdout explicitly,
     because `process::exit` skips destructors.
  5. `wait_object_complete`, so the cache is written for later runs, then
     `shutdown`, then `flush_traces`.
  6. `process::exit(report.exit_code())`.
- The `RunMode::Run` rustdoc and the `src/lib.rs` consumer comment name
  `--test`.
- **The test child (§6.5).** Mode validation yields two binary-private
  actions, `Action::TestSupervisor` and `Action::TestChild`, where it
  yielded `Action::Test` before S123:
  - **The supervisor**, for `--test` without the child arguments. `run`
    dispatches it before `CompilerSession::new` and entry registration, so the
    supervising process compiles nothing. It calls `supervise_tests` with its
    arguments less `--test` and no module selection, writes each warning to
    stderr and the text to stdout, flushes, and exits with the report's code.
    An `Err` takes the existing error path.
  - **The child**, for `--test` with the child arguments. It runs the arm
    above with step 2 calling `run_tests(records, modules, resume_after)` and
    steps 3 and 4 removed: warnings and outcomes go to the record file, and
    the child writes no report. With a module selection it runs without the
    cache and skips the object wait (§6.5, *Cache use*). It exits 0 after
    `end` is recorded.
  The child arguments without `--test` are a usage error.
- **Execution environment** ([CLI §0.7](../../repl/spec/00-cli-invocation.md#07-execution-environment-variables-s93);
  user ruling of 2026-10-01). `CRANELISP_NO_LENIENT` and
  `CRANELISP_SPARK_BUDGET` apply under `--test` as in every mode, with no
  int change. Each is read once per process by its owner:
  `CRANELISP_NO_LENIENT` by backend's sparkability decision at codegen,
  and `CRANELISP_SPARK_BUDGET` by intrinsics' spark gate at the first
  admission. `--test` compiles through `RunMode::Run`, and its tests run in
  process through the same emitted spark sites and gate, so no mode branch
  exists for a knob to miss. Do not add a `--test`-specific read or
  override.
  - **Measured 2026-10-01** on the debug binary from `88bbbd12` with the
    Phase-6 tree, `--test --no-cache`, one test calling a doubly recursive
    `fib 20`, with `CRANELISP_SPARK_STATS=1`: the default run spawned 14
    sparks; `CRANELISP_SPARK_BUDGET=0` spawned 0, with every gate taking
    the direct arm; `CRANELISP_NO_LENIENT=1` emitted no spark site, so no
    statistics were printed. The test passed in all three.
  - Grade: measured once, not continuously. A permanent cell is QA's to
    allocate. Falsifier: a `--test` run in which either knob leaves the
    spawn count of a sparking test unchanged.

### 7.2 REPL commands

- **`/run-tests [module]`** keeps its selection and its per-module readiness
  wait, then calls the shared runner.
- **`/run-all-tests`** selects as §4.1 states, then calls the shared runner.
- Both display the report text unchanged, and each warning through the
  REPL's existing `; warning:` line builder.
- Neither applies the §7.3 refusal; `discover-tests` is available in the REPL.
  Under §6.5 the child applies it, so a test referencing `discover-tests`
  fails the run in the REPL too.
- Under §6.5 both call `supervise_tests` with their process's arguments and
  their selected module list, and display its report as above
  (`handle_run_tests`).

Through the shared runner the REPL commands conform to standing text:

- a mistyped `test-` function is excluded and warned, never run (§16.1);
- a library module under the project root is excluded from `/run-all-tests`
  (§16.2.2);
- the empty run reports `No tests found` (§16.2);
- a failing test's value is released (§6.2).

### 7.3 Batch refusal of `discover-tests`

§16.6 makes the primitive absent from every non-REPL mode. One gate realises
that for all three batch seams:

- **Detector.** One structural body walk is the only detector
  ([test discovery §4.5](../arch/test-discovery.md#45-what---run---link-and---test-users-see)).
  It scans every loaded module's concrete bodies. It matches a bare name in
  `DEV_SESSION_ONLY_EXTERNS`, or an FQ name whose terminal entry is that
  host-promised primitive. An import alone is not a reference.
- **Seams.** Each batch entry calls the gate before it runs or writes
  anything:
  - `trampoline` (`--run`), before `main`'s entry read;
  - `link_by_name` (`--link`), after `validate_main`;
  - `run_tests` (`--test`), before preparation.
  The REPL runs code through none of these, so the gate needs no mode test.
- **Diagnostic.** One diagnostic, taking no mode: it names `discover-tests` and
  one referencing function, names the REPL as where the primitive is
  available, and names `--test` as the way to have the compiler discover and
  run the tests (§16.6). It never offers `--run`.
- **Location (ACT-1036; designed 2026-11-18, built at `52de1aad`).**
  The refusal is located at the written top-level form that defined the
  function it names, in that function's module file (REPL §5.5, §5.1).
  Before `52de1aad` it was raised at the synthetic span with no file, so
  every seam printed `1:1` and `0..0`.
  - *Span source.* The definition origin the session keeps for every
    definition it publishes, in every mode. It is the record the `main` gate
    reads ([io-integration §1](io-integration.md#1-running-a-program),
    Location; [Principle 7](../arch/principles/07-single-source-of-truth.md)),
    and for a function a macro produced it is the written macro call. The
    reference's own span is not used: in a macro-produced function it is the
    expansion's synthetic span, and the message's subject is the function, so
    the location points at the subject.
  - *A cache-restored definition.* A restore records no origin. The restored
    body keeps the source spans of its module's file, whose hash the restore
    matched, so the location is the restored declaration's span. For a
    directly written `defn` that is the written form, the span a fresh build
    records.
  - *Residual: a macro-produced function restored from cache.* Its
    declaration carries the expansion's synthetic span, so its refusal would
    still render at `0..0`. Reaching it takes a macro-produced function that
    references `discover-tests`, cached by a REPL session and restored into a
    batch run. *Falsifier:* `qa` observes it. *Remedy if triggered:* the
    stored module carries each definition's origin, which is a backend schema
    change and a facade change through `arch` and the user gate. It is not
    taken now because the refusal and its wording stay correct in that case;
    the missing position is a known nonconformance for the user to accept or
    schedule.
  - *Which function.* When several functions reference the primitive, the
    gate names a located candidate before an unlocated one, then the first by
    module path, then the earliest origin in that module, so the choice does
    not depend on table order.
  - *What `dev` builds* (`src/exe.rs` and the three seams). The gate takes
    the session's origin record and each module's file beside the tables.
    It is crate-private, so no public item changes. The text and category of
    the diagnostic are unchanged. Unit row: §10, refusal gate, row 4.
  - *Cells.* Turn green: `tests/test_runner.rs::s124_discover_batch_location_run`
    and `_link`. Stay green, in `tests/test_runner.rs`:
    `batch_modes_neg_refuse_uncalled_discover_tests_reference_with_one_diagnostic`,
    `run_neg_refuses_discover_tests_reference_restored_from_cache`,
    `batch_modes_accept_import_only_of_discover_tests` and
    `repl_test_child_refuses_discover_tests_before_any_test_runs`; and
    `tests/link.rs::link_module_referencing_discover_tests_extern_fails_with_friendly_message`.
    For `qa` to allocate: the `--test` leg; a reference in an imported
    module, located in that module's file; a macro-produced referencing
    function, located at the written call; and the line of the restored leg.
- **Exit.** The error takes each driver's existing error path: stderr and
  exit 1.
- **Cached bodies load before the refusal.** A cache-restored module that
  references the extern must load for a seam to refuse it. The session JIT and
  the cache-restore linker take the extern's host body from one source in
  `worker`, so restored code loads exactly as fresh code does. The batch seam
  then refuses it; in the REPL it runs, as fresh code does.

Placing the refusal in compilation behind `RunMode::Run` was rejected. It
would add a mode-gating origin, and the driver seams already own the
pre-execution checks.

## 8. Failure behaviour

| Event | Outcome |
|---|---|
| `--test` with `--run` or `--link`, or with `-o` | usage error to stderr, exit 1 |
| Compile or startup failure under `--test` | stderr, exit 1, no report |
| Missing entry source file under `--test` | Refused at entry registration, naming the expected file ([int §6.1.1](int.md#611-a-missing-entry-source-file)): stderr, exit 1, no report |
| A compiled reference to `discover-tests` under `--run`, `--link` or `--test` | refused at the driver seam (§7.3): stderr, exit 1; nothing runs and no executable is written |
| Readiness failure: a failed or incomplete cached load | `Err` from `run_tests`; no test runs |
| An admitted edge to a module with no table | `Err`, naming the module; no test runs |
| A test's release target cannot be resolved | `Err` (result-owner §5); no test runs |
| An eligible test has no code at preparation | That test is reported `FAILED: test function not found`; the run continues |
| A test panics | The panic ends the child. The supervisor reports `PANIC: <message>`, counts it as failed and restarts the child after that test (§6.5); nothing is released |
| The child ends with another status while a test is open, including a dispatch fault | that test is reported failed. The reason carries the status and the child's final stderr line, which is the fault report. The child restarts after it (§6.5) |
| The child ends by signal while a test is open | that test is reported failed, naming the signal; the child restarts after it (§6.5) |
| The child ends with no open test and no completion | `Err`; the child's diagnostic is already on stderr; no restart (§6.5) |
| A test returns `(Some reason)` | `FAILED: <reason>`; released once; the run continues |
| A mistyped `test-` function | excluded, with one warning |
| No eligible test | `No tests found`, exit 0; warnings are still reported |
| Object wait fails after the report | the error goes to stderr with exit 1, as `--run` does after `main` |

## 9. Assurance

- **Structural.**
  - Execution returns no `Result`, so `Err` can arise only in preparation. This
    enforces the rustdoc promise that no test has run when `Err` is returned.
  - The report's private fields tie the exit code to its outcomes.
  - One report builder serves every client, so client texts cannot diverge.
  - The refusal diagnostic takes no mode, so the three seams cannot diverge.
  - The resolver and the classifier share one candidate derivation.
  - Test identities travel typed.
- **Measured.** The §10 unit rows, and QA's end-to-end cells for §0.2.2 and
  §16.2.
- **Asserted, with named falsifiers.**
  - *All clients use one scan.* Falsifier: a second `starts_with("test-")` scan
    in `src/` outside the discovery submodule.
  - *Every recorded `file_path` has the resolver's path form.* The only writer
    that stores another form is `introduce_module`'s cache branch, which uses
    the canonical watcher path and has no production caller. Falsifier: a test
    in a project module, reached by import on a fresh or cached run, that is
    absent from the `--test` report.
  - *Every batch entry refuses `discover-tests`.* Falsifier: a public
    `CompilerSession` method, reachable from `main.rs`, that executes compiled
    code or writes an executable without calling the §7.3 gate.
  - *The detector sees cache-restored bodies.* It reads each entry's retained
    body. Falsifier: a second, cache-hit run of a program whose only
    `discover-tests` reference is in a cached module, where `--run` executes
    instead of refusing.

## 10. Unit-test design

Rows are grouped per seam. Rows whose seam existed before the runner were armed
RED against it; the others arrived green with the seam they test.

- **selection**
  1. Entry → `import` a → `export` b; b declares `(mod c)` and `(mod- d)`. The
     selection is {entry, a, b, b.c, b.d}.
  2. The walk stops at a library module: it is not selected, its declared child
     is not selected, and a project module reachable only through it is not
     selected.
  3. A child of a library parent whose file is the project-root candidate is
     not selected.
  4. A bare import resolved through `DeclaredChildren` selects the declared
     child, not root `q`, and vice versa.
  5. A cycle terminates, and each module is visited once.
  6. An admitted edge to an absent table returns `Err` naming the module.
  7. Classifier cases: `stdlib.foo` at `{root}/stdlib/foo.cl` is project; `foo`
     resolved from lib dir `{root}/stdlib` is library; no recorded file is
     unfiled; the entry is project.
  8. The fresh prologue records `file_path` with introspection off.
  9. Alias-only and null imports and exports of a project module are not
     edges; that module is not selected.
  10. With the prelude bit on, a project prelude is selected and expanded. A
      library prelude is neither selected nor expanded, whether reached through
      the implicit edge or an explicit `import`.
  11. `/run-all-tests` membership excludes a library module and keeps project
      and unfiled modules.
- **discovery**
  1. An exact scheme is eligible.
  2. `(Fn [] Int)`, `(Fn [Int] (Option String))` and `(Fn [] (Option Int))` are
     each excluded with one warning naming the FQ test.
  3. An imported or re-exported test is not listed under the importer.
  4. Results are in FQ order.
- **run** (the recording resolver of result-owner §6)
  1. The sequence pass, fail, panic, pass gives four outcomes in order, and the
     last test runs.
  2. A `(Some reason)` is observed, then released exactly once.
  3. A `None` is released exactly once.
  4. A panic produces no glue call.
  5. A test without code is reported as a failure, never a pass.
  6. A planted target-resolution failure returns `Err` and no test body runs.
  7. The exit code is 0 for all passing, 1 for any failure or panic, and 0 for
     an empty run. The empty text is exactly `No tests found`; the REPL
     handlers return it unchanged.
  8. An entry whose file exists but defines no test is an empty run
     (`run_tests_reports_an_existing_entry_without_tests_as_an_empty_run`).
     The missing-file rows are entry registration's
     ([int §6.1.1](int.md#611-a-missing-entry-source-file)).
- **refusal gate** (`exe`)
  1. A bare and an FQ body reference are each refused with the one §16.6
     diagnostic, which does not offer `--run`.
  2. An import alone, and an FQ reference to a user definition
     `mod/discover-tests`, are not refused.
  3. `run_tests` on a session whose program references the extern returns
     `Err` and runs no test body; the REPL runner is unaffected.
  4. The refusal carries the referencing function's origin span and its
     module's file (§7.3, Location). A definition with no origin record is
     located at its declaration span. With referencing functions in two
     modules, the function named does not depend on table order. RED before
     the change on the span and the file.
- **`main.rs`**:
  1. `--test` parses to a test action, with `RunMode::Run` and
     in-memory-and-object codegen.
  2. `--test` with `--run`, with `--link`, or with `-o` is a usage error.
  3. `--test` and `--run` parse the target, worker flags, `--no-cache` and
     agent and colour flags identically, in either target order.
  4. `--test` selects the supervisor and `--test` with the child
     arguments selects the child; the child arguments alone are a usage error.
- **test child (§6.5)**:
  1. The supervisor's classification maps each row of the §6.5 table. That
     includes a panic-status ending with no prefixed stderr line, which is a
     fail and not a panic, and an open `start` after a death by signal.
  2. A scripted sequence of child endings — pass, panic, pass, signal, pass —
     gives five outcomes in order, three children, and restarts after the
     panicking and the signalled test.
  3. A child ending with no record after a restart stops the run with `Err`;
     a planted classifier that restarts it anyway is caught by a bound on
     child count, the detection proof for termination.
  4. The child command line is the client's arguments less its mode flag,
     then `--test` and the child arguments, for both clients; a `--test`
     client's `--test` is not repeated. The child environment adds
     `CRANELISP_NO_ENV=1`.
  5. A resume point runs only the tests that sort after it.
  6. The record codec round-trips a reason spanning lines.
  7. Warnings in the report come from the first child only.
  8. A REPL child writes no object cache and no project file.
  9. *The cause of a fail.* An open test, status 1, no prefixed line, and
     stderr consisting of DLL panic-hook lines followed by
     ``platform fn `p/f` dispatch failed: boom`` is a fail. Its reason carries
     the status and that final line, and it is not a panic. Three negative
     legs:
     - with no stderr, the reason names only the status;
     - with a signal, it names only the signal, though the stderr has lines;
     - the panic row is unchanged when a later line follows the prefixed one.

     The stderr relay keeps the final line and, separately, the last
     prefixed line. The first leg fails against the as-built status-only
     reason.

QA allocates the end-to-end cells.

## 11. Rejected alternatives and potential extensions

- **Client-specific report or refusal text.** The user ruled one code path;
  a per-client variant would reopen the same behaviour as mode policy.
- **Record a search tier per module at resolution.** This needs a new tier
  type, a changed resolver return type at about ten call sites, a session map
  and a converged `file_path` setter. The recorded path already determines the
  tier.
  - Potential extension. Trigger: a `file_path` writer in production that
    cannot use the resolver's path form.
- **Classify by `file_path.starts_with(project_root)`.** This includes lib
  directories that lie inside the project, the defect the earlier
  `/run-all-tests` had.
- **A missing-entry check in `run_tests`, or at each batch caller.** Once
  `--run` and `--link` needed the same refusal (ACT-1004), a caller-side check
  would re-derive absence at three seams. Entry registration, where the
  resolver decides absence, refuses it once for every batch mode
  ([int §6.1.1](int.md#611-a-missing-entry-source-file)).
- **Run first, then build the owner fallibly.** A glue failure after the first
  test would break the promise that `Err` means no test has run.
- **Re-read the GOT slot at call time.** This would split the same read that
  result-owner §4.3 requires, and it has no retention owner for the code
  being called.
- **Admit an edge by loading its module.** `--test` would then compile a
  different graph from `--run` (Principle 11). Every admitted edge already
  loads its module, so the walk never loads.
- **A child per test.** It would add about 0.8 s per test at exemplar size
  (44 tests, about 35 s on a 16 s run; measured 2026-11-15). The user chose the
  restarting child (§6.5), whose extra cost scales with panics instead.
- **Configurable module selection.** Future work under ACT-0988. Trigger: a
  user ruling admitting library modules or other roots.

## 12. Residual leads

These are for `qa` intake and are not designed here:

- **In-language discovery has no warning channel.** A mistyped test found by
  `discover-tests` is excluded silently in running code. This is within the
  scope of ACT-0986.
- **The wrapper reads a null slot as `None`.** The late-bound wrapper returns
  `None` for a null slot, which an in-language runner counts as a pass.
  Readiness makes this unreachable for a ready module, but the wrapper does not
  assert it.
- **In-language failure values.** An in-language runner's `(Some reason)`
  follows ordinary language RC, so the §6.2 release applies only to host-run
  tests.
- **Declared-child file resolution diverges from §8.2.5.** The fresh prologue
  resolves a declared child's dotted path through the root-then-lib search. It
  does not use the parent's directory only. A child of a lib-dir parent is
  therefore taken from the project root when a file exists there, and a missing
  child of a project parent falls back to a lib dir instead of failing. This
  was read from source and is not reproduced. The classifier takes the parent's
  class either way.
- **The detector matches bare spellings, not resolutions.** A bare reference
  to a user function that shadows `discover-tests` is refused, although it
  does not reference the primitive, at all three seams. It was read from source
  and is not reproduced.
- **REPL cache-hit parity for the extern.** A cache-restored module that
  references `discover-tests` now loads and runs in the REPL, as a fresh one
  does (§7.3). No REPL cell observes it.
- **Compile-time macro execution precedes the refusal.** §16.6 refuses "before
  any code executes". A macro clause that calls `discover-tests` would execute
  during expansion, before any driver seam, and the detector scans callable
  bodies rather than macro clauses. This was not reproduced; `qa` classifies
  it.
