# `--test` and the shared test runner

**Owner:** `design` (int). **Status:** implemented and verified in `src/`.
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
  re-export. This design adds no public item.

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
   Execution has no error return.
5. **Report.** The outcomes, the warnings and the exit code form one
   `TestRunReport`, whose text is identical for every client (§6.4).

The `--test` driver in `main.rs` compiles exactly as `--run` does, then calls
`run_tests` instead of `trampoline` (§7.1). `main` is neither validated nor
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
| `--test` with `--run` or `--link` is a usage error; `-o` is rejected; a missing entry file exits 1; warnings go to stderr; agent, worker and `--no-cache` flags behave as for `--run` | §0.2.2 | Flag parsing, entry registration's batch refusal ([int §6.1.1](int.md#611-a-missing-entry-source-file)) and the `Action::Test` arm (§7.1) |
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

For each prepared test, in FQ order:

1. Clear the calling thread's runtime-error slot.
2. Call the captured pointer while holding the cloned code owner (Principle 22).
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
before preparation (§7.3). In the REPL, a test that calls `discover-tests`
during `/run-tests` sees the state that REPL evaluation already maintains.

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

## 7. Clients

### 7.1 `--test` (`main.rs`)

- `Action::Test` is a new binary-private variant. It maps to
  `CodegenBehaviour::InMemoryAndObject` and to `RunMode::Run`, which is
  Principle 11's one compile path.
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
| A test panics | `PANIC: <message>`; counted as failed; no release; the run continues |
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
- **`main.rs`**:
  1. `--test` parses to `Action::Test`, with `RunMode::Run` and
     in-memory-and-object codegen.
  2. `--test` with `--run`, with `--link`, or with `-o` is a usage error.
  3. `--test` and `--run` parse the target, worker flags, `--no-cache` and
     agent and colour flags identically, in either target order.

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
