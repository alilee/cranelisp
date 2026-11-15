# Process-ending panics and the environment supply

**Owner:** `arch`. **Reader:** `design`, `dev` and `review` for backend,
intrinsics and Binary/int, and `qa` allocating evidence for them.

**Status: approved target, not implemented.** The user's S123 rulings of
2026-11-15 (`sprints/SPRINT.md`, User rulings) set the behaviour; the
requirements are `spec/12-runtime.md` §12.7 and `repl/spec/00-cli-invocation.md`
§0.8. This contract states the boundaries and invariants that realise them.
The current contracts it replaces, listed in the
[fold table](#3-where-each-section-folds-on-landing), describe the as-built
system until the Phase 5 change-sets land. At that point `arch` folds each section
into its listed home and retires this file.

Exact public-API deltas are in the [S123 API packet](../../sprints/s123-api-packet.md).

## 1. A runtime panic ends the process

### 1.1 Position

- **One terminator.** A crate-private terminator in `cranelisp-intrinsics`
  is the only place a runtime panic is handled. It reports the message once,
  as plain text on stderr with the prefix `error: runtime panic:`, and
  terminates the process with the specification's non-zero status
  (`spec/12-runtime.md` §12.7.5). Intrinsics publishes the prefix and the
  status for the test supervisor (packet row P11), so the terminator holds
  the only copies.
  `runtime/panic` is the published raiser that calls it, and it never
  returns: the Rust signature diverges (`-> !`) and every emitted call to it
  ends its block. Every panic source routes through it: emitted checks (match
  failure, division, Vec bounds), intrinsic bodies (empty `select`, nested
  trace), primitive bodies and platform code that calls the symbol.
- **No mode distinction.** The terminator reads no mode and no host state. The
  REPL, `--run`, `--test` and linked executables terminate identically
  (Principle 11, single pipeline, mode parameters). The REPL host does not
  intercept a panic.
- **No slot, no sentinel, no ferry.** Nothing is recorded for a caller to
  find, so no caller can resume with a placeholder value. The ACT-1040 and
  ACT-1042 class (`unpropagated-panic`) has no construction left: there is no
  return to propagate from.
- **Concurrent panics produce one report.** The first thread to enter the
  terminator reports and exits; any later entrant waits until the process ends.
  The report is the first panic to reach the terminator, and which of several
  concurrent panics that is stays unspecified (`spec/12-runtime.md` §12.4.3).
  A deterministic, sequentially-first report would need the join-side ferry
  this position removes.
- **Output already written is delivered.** Program output buffered before the
  panic is flushed before the message, so a reader sees output and message in
  causal order. A diagnostic exit hook must not replace the panic's message or
  status. For example, the allocation-parity check (`CRANELISP_ALLOC_PARITY`)
  must not abort on the leak a panic exit legitimately leaves
  (`spec/12-runtime.md` §12.7.8 permits it).
- **A Rust panic inside runtime code is an internal defect, not a language
  panic.** It must still terminate the process rather than be caught and
  dropped. The detached-strand `catch_unwind` in the reactor becomes a
  terminating arm, not a recovery policy; elsewhere a Rust panic cannot unwind
  out of an `extern "C"` entry and aborts, as today.
- **Other terminations share the terminator's claim.** The platform dispatch
  fault (§1.6) and the reactor's `OneShot` backstop expiry end the process
  through the same terminator, so only one report is ever written. The
  interior is `design/intrinsics/process-lifecycle.md` §1.

### 1.2 What the position removes

Each item is retired in the change-set that makes it unreachable; none is kept
"probe-reachable".

| Mechanism | Owner | Replaced by |
|---|---|---|
| The thread-local runtime-error slot and its Rust accessors | intrinsics | The terminator |
| The fork-join error ferry: the IVar error field and the `Par` carry ([test discovery](test-discovery.md) §2) | intrinsics | Nothing; a worker panic ends the process from the worker |
| The trampoline's pending-error peeks and the driver's runtime-error outcome | intrinsics | Nothing; the trampoline never resumes after a panic |
| `catch-runtime-error`, its catalog row and bootstrap registration | intrinsics, int | Checked operations returning `Option`, first the primitive `checked-quot` (`spec/12-runtime.md` §12.7.3) |
| The trace guard's panic cleanup ([tracing](tracing.md) §6) | intrinsics | Nothing; no later form runs |
| The detached-strand fault policy, "500 + log + drop" ([effect concurrency](effect-concurrency.md) §10) | intrinsics | Nothing; a detached strand's panic ends the process (`spec/12-runtime.md` §12.7.9) |
| The REPL host's slot read and its post-panic recovery | int | Nothing |
| The macro expander's slot read | int | Nothing ([macro expansion](#14-macro-expansion-and-broken-symbols)) |
| The compiler test runner's per-test slot bracket | int | [The test child](#15-the-compiler-test-runner) |
| The dispatch-fault slot, the driver's outcome kinds and the stub's slot printer | intrinsics, int | The terminator ([dispatch faults](#16-platform-dispatch-faults)) |
| The broken-symbol state and its trap stub | int, types, backend | The redefinition guard's compile-time refusal ([broken symbols](#14-macro-expansion-and-broken-symbols)) |

Cancellation is unchanged and is not a panic (`spec/10-io.md` §10.12.9).

### 1.3 Invariant: no continuation past a panic

Replaces safety register R13 (the fork-join ferry).

- **Statement.** After `runtime/panic` is entered, no user code, no runtime
  code other than the terminator's own exit path and no emitted code runs on
  that thread.
- **Structural for Rust callers.** `runtime/panic`'s diverging signature makes a
  continuing Rust caller unwritable.
- **Structural for emitted code only if one emitter exists.** `design`(backend)
  converges every emission of the call onto one helper that also emits the
  block terminator, so a call site without a terminator cannot be written.
  Until that convergence is shown, the emitted half is asserted with a named
  falsifier: an emitted `runtime/panic` call followed by reachable code, found
  by a census of call sites.
- **Measured.** The ACT-1040 and ACT-1042 cells, re-pointed to the new
  behaviour: the process exits non-zero with the panic message, with no
  SIGSEGV and no resumed caller, in every mode.

### 1.4 Macro expansion and broken symbols

- **A panic during macro expansion ends the process like any other** (user
  ruling; `spec/12-runtime.md` §12.7.2). A macro clause is user code that the
  compiler runs on the expander's thread in every compiling mode, so one
  terminator with no mode covers it, and no containment entry exists. The
  expander's slot read retires. Consequence: a macro that panics on its input
  ends the REPL, including a model proposal under the embedded agent's silent
  pre-flight validation (`design/int/agent.md` §16.1).
- **A call to a symbol a redefinition left broken is refused at compile time**
  (user ruling). The refusal is the redefinition guard's: a language-type
  change is admitted only when its target has no blocking dependent
  (`repl/spec/18-redefinition.md` §18.1), so no publication leaves a callable
  broken and no compiled call can reach a trap. The interior is
  [session transaction §5.2](../int/session-transaction.md#52-no-symbol-is-left-broken).
- **The broken state becomes unrepresentable.** The superseded redefinition
  residue is deleted, and then packet row P13 removes `Life::Broken`,
  `SymbolTable::mark_broken`, `BrokenProvenance`, `BrokenTransition` and
  `cranelisp_backend::compile_trap_stub` (Principle 20). Grade until the
  deletion lands: asserted, with the falsifiers of session transaction §5.2.
  After it and before P13: structural in the binary, with one hole, a new
  caller of the public `mark_broken`. After P13: structural.
- **Redefinition outcomes retire with the residue.** After the deletion,
  nothing consumes the commit gate's `RedefinitionOutcome`s: their fields
  feed only the deleted transaction, the T1 reload and the broken-record
  clearing, while the slot-policy decision and the rematerialization check
  read `classify_redefinition` directly. So the outcomes, their
  `ProcessedCluster` carrier and `apply_redefinition_outcomes` are deleted, not
  settled. The approved S121 publication receipt
  (`design/int/s117-conformance-recovery.md` §1.1.3) existed so that a later
  `Err` could not discard the dependent work those outcomes drove. The REPL
  redefinition rules (`repl/spec/18-redefinition.md`) now require no such
  work, so the receipt is never built and its rule retires with its subject.
  That follows from the user's redefinition and broken-symbol rulings, as
  propagation of approved substance (`sprints/METHOD.md` §1.3). If a later
  requirement needs post-publication work to survive a later `Err`, the
  receipt's recorded shape in Git is the reference. The change is
  binary-private and passes no API gate.

### 1.5 The compiler test runner

`--test`, `/run-tests` and `/run-all-tests` share one runner, which reports a
panicking test as `PANIC: <message>` and continues
(`repl/spec/16-test-discovery.md` §16.2). Under [the position](#11-position)
a panic ends the process running the test.

- **One child, restarted after a panic** (user ruling). The runner splits into
  a supervisor in the client's process, which never compiles or runs a test,
  and a child of the same binary, which runs the existing runner and streams
  one record per test. After a panic the supervisor records the open test and
  restarts the child after it. It is still one runner for the three adapters
  (Principle 07). The interior and its measured cost are
  [test runner §6.5](../int/test-runner.md#65-the-test-child).
- **The supervisor classifies an ending by the terminator's published
  constants**, the report prefix and the exit status (packet row P11), so the
  producer and the consumer share one copy.
- **The root-crate entry points change** (packet row P12): `run_tests` becomes
  the child's engine, and a supervisor entry that needs no session returns the
  unchanged `TestRunReport`. The child's arguments are a CLI surface `spec`
  states; the record format is private to the runner.
- **`discover-tests` is refused inside a test child** (user ruling), through the
  batch refusal the child already applies (`repl/spec/16-test-discovery.md`
  §16.6).
- **The reference standard library's runner** starts each test in its own
  process (user ruling). That needs a process-launching capability, which is a
  platform concern owned by `dev`(stdlib), not a `discover-tests` one. The
  binary adds no host extern for it.

### 1.6 Platform dispatch faults

A dispatch fault (a Rust panic or signal in DLL code at the platform-effect
force site) ends the process through the same terminator (user ruling;
`spec/12-runtime.md` §12.7.6). Foreign code that faults leaves the process in
an unknown state. The second slot, the driver's outcome kinds and the stub's
slot printer retire, and the dispatch-fault text has one intrinsics-side
printer for every mode. `PlatformError::DispatchError` loses its producer and
is removed (packet rows P3, P4 and P9).

### 1.7 Consequences outside the compiler

- **Writers must be crash-consistent.** A panic on a spark worker can end the
  process while another thread writes, for example a background worker
  writing a cached object. Every file the compiler writes must be replaced atomically, as it
  must already be for `SIGKILL`. Named falsifier: a truncated or partial
  artifact readable after an exit mid-write.
- **The `poll-pool` test platform** signals a fault by calling `runtime/panic`
  and expects to return. It now ends the process. Its survival fixture
  becomes a process-exit fixture (`qa`, `test`).
- **Language-facing work:** the exemplar's per-request 500 handler and the
  stdlib test runner use `catch-runtime-error`. The handler is rebuilt on
  checked operations such as `checked-quot`, and the stdlib runner on
  per-test processes (user rulings).

## 2. The environment supply

### 2.1 Position

- **The process environment stays the single source every library crate
  reads** (Principle 07). No library crate reads a configuration file.
- **The binary is the only supplier.** At startup, before any thread starts
  and before the earliest reader, it reads the project `.env` and
  the user file under `~/.config/cranelisp/` and sets each admitted key that
  the process environment does not already define. Precedence is therefore
  process environment, then `.env`, then the user file. Argument parsing and
  project-root resolution are pure and may run first; their placement inside
  that window is `design`(int)'s.
- **Admitted keys** are the `CRANELISP_` prefix plus `NO_COLOR`,
  `ANTHROPIC_API_KEY` and `OLLAMA_API_BASE_URL`; all others are ignored (user
  ruling). Injected keys are inherited by child processes, including the
  system linker, as ordinary environment variables are.
- **Soundness of the supply.** The crate is on edition 2024, where
  `std::env::set_var` is `unsafe`. It is sound only while no other thread
  reads or writes the environment, which that placement gives.
- **The loader can be redirected and disabled from the process environment
  only** (user-accepted scope change): the file locations follow overridable
  locations, and one disable switch that no file can set turns the supply off.
  `qa` places the suite's one repository-level declaration in the change-set
  that introduces the loader, so a developer's own files cannot change test
  results or reach a live agent endpoint.
- **Repeated reads need no API change.** After the supply the production
  environment does not change, so a repeated read returns the startup value.
  A crate may memoise inside its interior; turning a read into a parameter
  would be a public-API change with no correctness benefit.
- **One configuration channel.** The environment and its files are the only
  channel for agent provider, model and key settings
  (`repl/spec/17-embedded-agent.md` §17.10). `Cranelisp.toml` stays the
  project's directory configuration. Project-level agent configuration
  (ACT-0960) extends these keys and files rather than adding a TOML channel,
  which would be a second source for the same fact.

### 2.2 Linked executables have their parameters baked in

- **Compile-time switches are baked by compilation.** A switch the compiler
  reads while compiling, for example the ownership toggle or a codegen dump,
  takes effect at `--link` time and is fixed in the emitted code.
- **Runtime switches are baked by a table.** `cranelisp-intrinsics` reads its
  runtime switches through one source with a closed set of members. In the
  compiler process (`--run`, `--test`, the REPL), the source reads the
  process environment after the supply. In a linked executable, the startup
  stub installs a table of the switches' values captured at link time, as its
  first call, and the source answers only from that table. The executable's
  runtime therefore never reads `CRANELISP_*` from its own process
  environment.
- **Intrinsics owns the names and the encoding.** At `--link` the binary asks
  intrinsics for an opaque capture of the current values and embeds the bytes
  in the startup object; the stub passes them back to the install entry. The
  binary never names a switch or parses the format, so the member set has one
  source (Principle 07) and the facade is two items (Principle 02). This is
  the shape of `design/intrinsics/process-lifecycle.md` §2.2.
  `design/int/environment.md` §3.1–§3.2, which has the binary read each
  listed name and emit name-value pairs itself, aligns to it.
- **Installation is checked.** Installing after the switch source has
  answered a read is a hard failure, so an early read cannot silently use the
  wrong source.
- **Agent settings are never baked, by construction.** The agent keys are read
  only in the binary's agent module, never by the runtime's switch source,
  so they cannot appear in the table. Shipped artifacts carry no agent code either:
  `crates/cranelisp-exe-bundle` does not depend on the root crate.
- **A linked program reads its environment only through a platform.** The
  table does not alter the program's process environment, so a platform and
  any child process see the environment the program was started with.
- **Why a table, not environment mutation.** Setting the baked values into
  the executable's environment at startup would need no reader change, but
  then the runtime still reads its process environment, a platform would see
  compiler values in place of the caller's, and child processes would inherit
  them.
- **Census.** The members are the `std::env` reads in the intrinsics
  modules `alloc`, `diagnostics`, `ivar`, `rc` and `reactor`
  (`design/intrinsics/process-lifecycle.md` §2.1). A reader in another crate
  linked into the executable would join the same source. The one candidate,
  `cranelisp_types::ownership_analysis_off`, is read only at analysis time;
  falsifier: a linked-runtime path that calls it. `rayon` would read
  `RAYON_NUM_THREADS` when its pool is built, an environment read outside a
  platform. In a linked executable the install step builds the pool with the
  machine's available core count, and no link-time value is baked (user
  ruling; `repl/spec/00-cli-invocation.md` §0.8).
- **Consequence for evidence.** A linked-executable cell that sets a runtime
  switch on the run of the produced program, rather than on the `--link`
  step, stops reaching it (`qa`).

The capture function and the install entry are additive intrinsics exports,
approved at the gate ([packet](../../sprints/s123-api-packet.md) row P8). Every
applicable non-agent `CRANELISP_*` switch effective at `--link` is fixed in the
executable (user ruling; `repl/spec/00-cli-invocation.md` §0.8): the
compile-time switches by compilation, and the runtime switches by the closed
member set.

## 3. Where each section folds on landing

| Section | Home after landing |
|---|---|
| §1.1, §1.3 | [Bounded contexts](bounded-contexts.md) §4b (runtime-error slot, invariant 13) and §6 (one program driver); [safety invariants](safety-invariants.md) (R13 replaced; `catch-runtime-error` leaves R11's roster and R22's host-promised list) |
| §1.2 | [Test discovery](test-discovery.md), [tracing](tracing.md) §6, [effect concurrency](effect-concurrency.md) §10, [total concreteness](total-concreteness.md) §3.3 |
| §1.4 | [Bounded contexts](bounded-contexts.md) §6 (macro execution; the redefinition guard), and, once P13 removes `Life::Broken`, the [symbol-table lifecycle](symbol-table-lifecycle.md) and safety register R22's entry-convention list |
| §1.5 | [Test discovery](test-discovery.md) and [bounded contexts](bounded-contexts.md) §6 |
| §1.6 Dispatch faults | [Bounded contexts](bounded-contexts.md) §4b |
| §2.1 | [Bounded contexts](bounded-contexts.md) §6 |
| §2.2 | [Bounded contexts](bounded-contexts.md) §4b and §6, and rustdoc on the switch source |
