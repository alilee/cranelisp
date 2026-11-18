# Host IO entry and platform-DLL load orchestration

Int's host-side use of the IO runtime and its orchestration of platform-DLL
loading. The runtime seam is `design/intrinsics/reactor.md` §0. Result
ownership and exit codes are [result-owner.md](result-owner.md). The platform
contract is `design/arch/platform-interface.md`.

## 1. Running a program

- **One driver.** `--run`, the REPL and the linked stub all call the runtime's
  `cranelisp_run_program(code, is_io)`. It clears the error slot, calls the
  compiled code, drives an IO result to completion, releases the IO tree and
  reports the outcome. Int never reaches into the reactor.
  - `--run` enters through `CompilerSession::trampoline`.
  - The REPL enters through `pipeline::execute_compiled_expr`.
  - `cranelisp_run_io` is the catalog's `runtime/run_io` import, not a host
    entry.
- **`main`.** Before running, `exe::validate_main` requires `main` to be
  an ordinary function of type `(Fn [] (IO _))` (`spec/10-io.md` §10.6). It also refuses an unresolved
  return-type-polymorphic dispatch in `main`'s body. `--run` and `--link`
  share this gate. A missing entry source file must not reach it: batch entry
  registration refuses that first ([int §6.1.1](int.md#611-a-missing-entry-source-file)).
  - **What "the entry defines `main`" means.** The entry module's table binds
    `main`. Every refusal about that binding is located (below); an entry
    whose table binds no `main` takes the unlocated refusal (S124-Q8).
  - **Location (S124, ACT-1036; built at `e294852f`).** Every
    refusal the gate raises about an existing `main` is located at the
    written top-level form that declared it (REPL §5.5, §5.1): the wrong
    shape, and a `main` that is not a function. The refusal stays at this
    gate: the REPL is exempt from the requirement (`spec/10-io.md` §10.6.2),
    so typecheck cannot own it. Its message and category are unchanged.
    - *Why not the declaration's own span.* Read from source and probed on
      2026-11-17: a declaration carries a span of the written form only when
      the user wrote the definition directly. A `main` produced by a macro,
      including the prelude's `def` and `const`, which expand to a
      `defmacro`, carries the expansion's synthetic span on its
      `DefnVariant` and on its macro form (`(mk main)` with
      `(defmacro mk [n] `(defn ~n [x] …))` renders at `1:1`, `0..0`). REPL
      §5.5 requires the triggering user form there. A multi-arity `main` has
      no single definition span either. A types-owned declaration span would
      be a public-API row; the root already holds the fact, so none is
      needed.
    - *The definition-origin span.* The form processor already attributes
      every definition, direct or produced by expansion, to the written
      top-level form it came from: each built definition and each macro
      checkpoint carries that form (`process_form`'s `authored_origin`).
      Today only the REPL's introspection record keeps it. The session also
      keeps that form's span for every published definition, in every mode
      ([Principle 11](../arch/principles/11-single-pipeline-mode-parameters.md)),
      and publishes it with the definition: an ordinary definition's span
      rides the prepared turn's staged records, and a macro's is written at
      its checkpoint's publication, so a refused turn leaves none.
      The gate reads `main`'s span from it. The introspection record keeps
      its REPL-only fields; the span is the one fact both readers share,
      taken from one attribution
      ([Principle 7](../arch/principles/07-single-source-of-truth.md)).
    - *No synthetic fallback.* A bound `main` with no recorded span is an
      invariant violation, not a refusal. The entry is never cache-restored
      ([result owner §3.2.1](result-owner.md#321-reach-in-production)), so
      the record exists for it. A change that restores the entry must carry
      the span with it; the located-refusal cells are its falsifier.
  - **A `main` that is not a function.** The entry binds `main` to a
    declaration that is not a single callable: a macro (`defmacro`, or
    `def`/`const`) or a multi-arity definition. It takes the located
    refusal above. Nothing else is needed for it.
    - *Multi-arity `main`.* `(defn main ([] …) ([x] …))` is refused although
      one arm takes no argument (`spec/10-io.md` §10.6). The gate refuses it
      for its shape, never by selecting the zero-argument arm, and locates it
      at the written `defn` form's line. It renders today's category for this
      refusal, `codegen error`, which the spec does not fix.
  - **A trait method named `main` is not `main`** (`spec/10-io.md` §10.6). The
    gate reads only the entry table's `main` binding. A trait method's
    binding lives under its canonical name, and the bare `main` holds only a
    name candidate that lets typecheck resolve a bare `main` to the method.
    An entry whose only `main` is a trait method is therefore an entry with
    no `main` and takes the unlocated refusal below (row D12). It needs no
    trait-method attribution and no separate check; `qa`'s T-Q9-a is the
    falsifier, and T-Q9-b the multi-arity one.
  - **An entry with no `main` (S124-Q8, ruled B; row D12).** REPL §5.5's
    missing-`main` exception applies: the refusal names the entry file and
    the missing `main`, and carries no form span. That means no line and
    column and no `at 0..0`. It keeps its error category (REPL §5.1 item 1;
    the exception lifts the location only).
    - *One producer* (built at `e294852f`). The gate, now crate-private, is
      the only producer. It runs in `--run` and `--link` whether or not the
      entry table exists, and an absent table counts as an entry with no
      `main`. After the gate, a missing `main` at `read_main_entry`,
      `link_by_name`'s absent-table arm and `entry_main_got_slot` is an
      invariant violation, not a user refusal.
    - *The file.* The gate receives the entry module's source path, which
      registration already holds. A missing entry file never reaches the
      gate ([int §6.1.1](int.md#611-a-missing-entry-source-file)).
    - *The value.* The gate returns the root's
      `session_v4::BatchError::MissingMain { entry_file }`, and
      `trampoline` and `link_by_name` return `BatchError`
      ([bounded contexts §6](../arch/bounded-contexts.md#6-binary-int-src-cratescranelisp-exe-bundle),
      known architectural constraints). Every other refusal, including the
      located ones above, is `BatchError::Compiler`. `CranelispError` and
      `ErrorLocation` do not change.
    - *Rendering.* `src/main.rs` matches the outcome once. `Compiler` goes
      through the existing formatter unchanged. `MissingMain` renders as
      `<file>: error: module error: <message>`: the formatter's own shape
      with the `:line:col` and the `at <span>` removed. The file is
      displayed by the formatter's rule, the file name alone when it is in
      the working directory, so the two renderings name a file the same way
      and share that helper. The message names `main` and the form batch
      mode requires; its words are `dev`'s.
    - *The category is `module error`.* Before `e294852f` the refusal showed
      `codegen error` or `module error` by site. Of the two, `module error` names
      the subject the refusal is about, the entry module's contents. `codegen
      error` names a stage that has not failed, which REPL §5.5 keeps out of
      the user's vocabulary. The category is the renderer's constant for
      this one case, not a field of the sum. It restates the label
      `CranelispError`'s `Display` prints for the same category; the label
      is presentation text, and a drift would show in the T-Q8 cell, so a
      shared constant across the crate boundary is not worth a row.
    - *Evidence, for `qa`.* In `--run` and `--link`, an existing entry file
      with no `main` exits non-zero. Its one stderr line names the file,
      `module error` and `main`, and contains no `:line:col`, `0..0` or
      `codegen error`. Controls: a `main` with the wrong shape keeps its
      location at its definition form, and a macro-produced `main` is
      located at the written macro call, not at `1:1`. `(defmacro main []
      …)` is a non-function `main` written in core forms only; probed
      2026-11-17, it is refused today at `1:1` and `0..0`. Under ACT-1019's
      rule, an unreadable entry is still refused before the gate.
- **Exit code.** An `Int` inner result is the exit code, and any other inner
  result exits 0. The rule has one predicate
  (`result_owner::result_is_exit_code`), which the linked stub bakes in as
  well.
- **REPL expressions.** An IO-typed expression is forced by the same driver.
  Its result displays the returned payload under the payload's own
  fully qualified type, as
  [REPL display §1.2.1](../../repl/spec/01-display-format.md#121-io-expression-results)
  requires. The driver unwraps `IO a` once and
  [result-owner.md](result-owner.md) owns the payload. A definition turn
  executes nothing. A runtime panic ends the process (§1.2).

### 1.2 A runtime panic ends the process: the host side

Status: designed in S123 Phase 3 (2026-11-15); not implemented. The position
is arch's [panic contract](../arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics) (§4b invariant 13), and the
requirement is `spec/12-runtime.md` §12.7.2. The runtime's terminal funnel
reports the message, chooses the exit status and ends the process. The host
never sees a panic, chooses no panic status and formats no panic text.

- **Every driver returns only after a clean run.** Without a runtime-error
  outcome, each host arm that read the slot is deleted in the change-set that
  makes it unreachable:
  - the REPL's trap arm in `pipeline::program_outcome_to_result` and its
    `runtime error:` display;
  - `CompilerSession::trampoline`'s slot read, which is the ACT-1041 locus;
  - the expander's slot read (macro expansion, below);
  - the test runner's per-test bracket ([test runner §6.2](test-runner.md#62-execute)).
  With these gone, no int path can format a panic, so `--run` cannot report
  one as `codegen error at 0..0` or double its prefix (ACT-1041). The funnel
  prints the ruled prefix `error: runtime panic:` once, as plain text on
  stderr, in every mode. Of concurrent panics, the first to reach the exit
  path is reported. Both are intrinsics' (`design/intrinsics/process-lifecycle.md` §1).
- **Dispatch faults end the process** through the same funnel (user ruling,
  2026-11-15). `compose_dispatch_error`, the driver's outcome kinds, and the
  linked stub's error block and `cranelisp_check_runtime_error` call retire.
  `cranelisp_run_program` returns the program's result word. The stub's
  sequence is `install → init → run → exit`, where the install is
  [environment §3.1](environment.md#31-mechanism).
- **What the process owes before it ends.** The funnel exits through the
  process's normal exit path, which runs registered exit hooks.
  - *Program and REPL output.* Platform output is unbuffered `write(2)`. The
    REPL's own text and the `Executing IO…` notice are written and flushed
    before the driver runs (§1.1). Arch §1.1 makes the funnel deliver
    buffered output before the message.
  - *Traces.* `main` registers one process-exit hook at startup that drains
    the observability sinks ([observability §7.1](observability.md#71-process-exit-and-panic-wiring)).
    It neither exits nor changes the status.
  - *REPL history (TTY).* Each accepted input line is appended to the
    per-project history before its turn is dispatched, so the line that
    panicked can be recalled after a restart. This replaces the save at
    session end. The cost is one small append per line.
  - *Definitions* are already on disk: a turn that regenerates the backing
    file executes nothing, and loading a backing file runs no top-level
    expression (probed 2026-11-15 on the debug binary at `f747990f`: a
    `user.cl` holding `(vec-get [1] 5)` starts the REPL without running it).
    The final cache persist and pending object writes are lost. The next
    session misses the cache for those modules, just as after `SIGKILL`.
    Cache writes replace files atomically by temp-and-rename (arch §1.7).
- **Macro expansion ends the process on a panic** (user ruling, 2026-11-15).
  The expander keeps its signal recovery, because signals are not panics, and
  loses only its slot read. Accepted consequences: a panicking macro in a
  backing file ends REPL startup each time until the file is edited, and a
  model proposal that expands a panicking macro ends the REPL during silent
  validation ([agent §16.1](agent.md#161-the-dry-run)).
- **A call to a broken symbol never runs.** The user ruled that such a call is
  refused at compile time. Int meets it before any call exists: the
  redefinition that would break a caller is the refusal
  ([session transaction §5.2](session-transaction.md#52-no-symbol-is-left-broken)),
  so no call to a broken symbol is compiled. The backend's trap stub is
  removed in the S123 W4 tree (packet row P13).
- **No mode branch.** The REPL, `--run`, `--test` and the linked stub delete
  the same arms. The REPL keeps no panic arm
  ([Principle 11](../arch/principles/11-single-pipeline-mode-parameters.md)).

### 1.1 REPL IO execution notice

- **One determinant.** `pipeline::execute_compiled_expr` reads IO-ness once
  from the expression's settled type. The same value selects driver forcing
  and, when true, writes the notice line to process stdout and flushes it
  immediately before the driver call. Notice and forcing cannot disagree, and
  the notice precedes every effect and any code the driver runs
  ([Principle 07](../arch/principles/07-single-source-of-truth.md),
  [Principle 24](../arch/principles/24-resolve-once.md)). The driver is
  runtime-owned, so the notice is not placed inside it
  ([Principle 02](../arch/principles/02-narrow-interfaces.md)).
- **A flushed write, not returned data.** The notice is ordered against
  output that platforms write to fd 1 during the driver call. Data returned
  after the call cannot precede that output, so the notice is exempt from the
  binary's rule that warnings are returned data (`src/AGENTS.md`).
- **Text and style.** The REPL display module owns the notice text, rendered
  through the `styled::render` seam. The pipeline decides only when it is
  written.
- **REPL-only by construction.** `--run` and `--link` do not reach
  `execute_compiled_expr`, so batch output never contains the notice. There is
  no mode flag ([Principle 11](../arch/principles/11-single-pipeline-mode-parameters.md)).
- **Every executing REPL caller shows it.** This covers user turns, the EOF
  flush, `/time`, `/mem` and agent submissions, with no per-caller code. The
  agent's tool result and the recent-turn ring carry the formatted result
  only, so they contain neither the notice nor effect output. Turns that do not
  execute show no notice: definitions, introspection, compile errors and
  typecheck-only agent probes.
- **Accepted residual.** Degraded startup recovery re-drives a backing file
  through the eval path. A hand-edited file holding a top-level IO expression
  prints the notice alongside the effect output it already prints. A
  suppression flag would cost more than this risk.

## 2. Platform-DLL loading

### 2.1 Form routing

The frontend extracts `(platform …)` forms, and `process_form` routes each one
to `handle_platform` (`src/process_form/platform.rs`).

**Entry only (S124, ACT-0973; not in source at `f3f9cc47`).** A `platform`
form in any module other than the session's entry module is a compile-time
error located at the form (`spec/10-io.md` §10.9.1). The handler decides it by
comparing the compiling module with the session's entry module, never by the
shape of the module's name
([BC](../arch/bounded-contexts.md) §6; Principle 19).

- **The fact.** The entry module is fixed at session construction and never
  changes. It moves onto the shared session state beside the other
  session-wide facts, so the dependency handler reaches it through the
  compiling context's shared-state handle, as it reaches every other session
  fact. `/mod` changes the REPL's current module, not the entry. Built at
  `109f008b`.
- **Held.** The refusal is built as a patch and not landed:
  `exemplar/solver.cl`, which `exemplar/main.cl` imports, declares
  `(platform stdio)`. Spec §10.9.1 makes that an error, so the exemplar moves
  the declaration to its entry (a `dev`(exemplar) change), and the refusal
  lands after it.
- **Order.** The refusal precedes the DLL load and the platform's recording
  on the table, so a refused form loads nothing and is not persisted.
- **Replaces** the source's skip of any module whose path contains `.`. That
  skip ignored a nested non-entry form without a diagnostic and loaded a
  root-level non-entry one. Both now refuse.
- **Restore parity (§2.6).** A table restored for a module that is not the
  entry and that records a platform declaration is a cache miss, so the fresh
  build reports the error. Such a table is reachable: a module cached while it
  was the entry of an earlier session is a dependency in this one. Restoring
  it would load a platform that a fresh build refuses (Principle 11).
- **Evidence (for `qa`).** A child declaring the platform, nested and
  root-level, refuses in `--run`, `--link` and the REPL; the entry placement
  control loads. A cached former entry imported as a dependency refuses
  rather than restoring. A non-entry module that imports `platform.<name>`
  after the entry declared it still works.

### 2.2 Search order

`src/platform.rs::resolve_platform_path` implements `spec/08-modules.md` §8.11.3:

1. A name containing `/` or ending in a DLL extension is an explicit path.
2. `{project_root}/platforms/`.
3. `{lib_dir}/platforms/` for each library directory.
4. Each platform directory ([cranelisp-toml.md §2](cranelisp-toml.md#2-directory-assembly)).

Each directory accepts `{name}.{ext}` and the Cargo name
`libcranelisp_{name}.{ext}`.

### 2.3 Load and ABI gate

`load_platform_dll` opens the DLL, reads its manifest through the
`cranelisp_platform_manifest_<name>` export with the host callbacks, and
finds its GOT slab and optional layout hash.

- **ABI gate.** `check_abi_version` refuses a manifest whose ABI version
  differs from `cranelisp_platform::ABI_VERSION` with
  `PlatformError::AbiVersionMismatch`. Int propagates the refusal and never
  loads such a DLL.
- **Name check.** `load_platform_checked` also checks that the declared name
  matches.

### 2.4 Registration

`register_platform_in_tc` wraps the DLL's GOT slab in place, without copying.
It then installs each function through `SymbolTable::install_platform`, with
the manifest index as the GOT slot, so calls are GOT-indirect.

- A signature that does not return `IO` is refused.
- A checked type with a free type variable is refused as a load error naming
  the platform and function (`int.md` §16.0).

### 2.5 Layout-hash gate

If the DLL's embedded layout hash differs from the host's regenerated hash,
the two modes act differently (`layout_hash_gate`):

- the REPL warns, names `/platform-schema`, and loads;
- `--run` and `--link` refuse with `PlatformError::LayoutHashMismatch`.

An empty host hash is accepted.

### 2.6 Retention and cache

The session keeps each loaded DLL handle in `kept_dlls`, so the wrapped GOT
stays mapped for the life of the session. A cache hit re-runs the same load
from the persisted declarations, and a failure is a cache miss
([int.md §7.1](int.md#71-cache-hit-flow-inside-register_module)).

## 3. Open gaps

None is open here. The non-entry platform form, the one gap read from source
on 2026-09-25, is designed in §2.1 and carried by ACT-0973 until it lands.
