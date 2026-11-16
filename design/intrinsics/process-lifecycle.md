# Process start and termination — runtime switches and panic exit

Owner: `/design` (intrinsics). How the runtime gets its configuration when a
process starts, and how it ends the process when a panic is raised.

**Status: S123 design, ruled.** §1, termination, is built (packet rows P1–P7
and P11). §2, runtime switches (P8), is approved and not yet built: until it
lands, the crate's modules read the process environment directly, as the §2.1
census records.

The boundary contract is `arch`'s
[process-ending panics and the environment supply](../arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics) (bounded contexts §4b invariants 13 and 18).
This document is the intrinsics interior that realises its §1 and §2.2: the
terminator's shape, the switch-source census its §2.2 asks of this surface, and
the evidence seams.

Governing requirements:

- `spec/12-runtime.md` §12.7.2, §12.7.4, §12.7.8 and §12.7.9: a panic reports
  its message and ends the process in every mode, with no propagation and no
  recovery. §12.4.3's panic rule and `spec/10-io.md` §10.12.7 item 3 apply it to
  workers, IO branches and detached strands.
- `spec/12-runtime.md` §12.7.5: one report, plain text on stderr, prefix
  `error: runtime panic:`, in every mode. §12.7.6: a platform dispatch fault
  ends the process.
- `repl/spec/00-cli-invocation.md` §0.8: every applicable non-agent
  `CRANELISP_*` switch effective at `--link` is fixed in the executable, agent
  settings are never baked, a linked program reads its environment only
  through a platform, and the linked worker pool uses the core count.
- The S123 user rulings in
  [`sprints/SPRINT.md`](../../sprints/archive/sprint-123.md#user-rulings-on-the-phase-3-decisions-2026-11-15).

The environment-file supply that precedes every reader in the compiler process
is `design/int/`'s ([environment](../int/environment.md)).

---

## 1. Termination on panic

### 1.1 One terminator

The crate has exactly one way to end the process because of a fault: a
crate-private terminator that takes a closed fault value and never returns.
`runtime/panic` is its language-panic entry. The other rows enter the same
body, so every exit shares one claim, one flush and one report path.

| Fault kind | Raised by | Report content |
|---|---|---|
| Language panic | `runtime/panic`: every emitted panic site, the nested-`trace` raise in `trace.rs`, `cranelisp-primitives`' out-of-line raisers, and platforms that resolve the symbol (for example `poll-pool`) | the panic prefix, then the message |
| Empty `select` | the select arm (`reactor.md` §9) | `select over empty collection`, as a language panic |
| Platform dispatch fault | the IO dispatch guard (`io_guard`) after a platform `Effect` thunk faults ([arch §4b invariant 14](../arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics)) | the platform function name and the cause, without the panic prefix |
| Runtime defect | the supervised-strand boundary's `catch_unwind` (`reactor.md` §2.12) | `error: runtime defect: `, then the Rust panic payload |
| `OneShot` backstop expiry | the reactor drive (`reactor.md` §8.2) | the existing backstop diagnostic |
| Switch-install misuse | the switch install entry (§2.1) | a located configuration message |

The backend's broken-symbol trap stub is not a row. It still calls
`runtime/panic` until packet row P13 removes it, at S123 close or in S124. The
redefinition guard refuses the change that would leave a symbol broken, so no
compiled call is meant to reach a stub
([arch §6](../arch/bounded-contexts.md#6-binary-int-src-cratescranelisp-exe-bundle)).

The terminator, in order:

1. **Claims termination once per process.** The first caller wins a
   process-wide atomic claim. Every later caller, on any thread, parks forever
   and never returns. Returning would resume user code with a fabricated value,
   which §12.7.8 forbids. Two concurrent `exit` calls would be unsound, because
   libc `exit` is not safe to call concurrently.
2. **Flushes the process's buffered standard output** so that output written
   before the panic precedes the report. The `stdio` platform writes unbuffered
   through `write(2)`, so the flush only matters for host-side Rust output, such
   as the REPL echo and the `Executing IO…` notice.
3. **Writes the report** as one preformatted buffer in one write, so another
   thread's stderr output cannot split the line.
4. **Exits the process** with the fault kind's status through
   `std::process::exit`. Exit-time handlers run (§1.4).

Report composition is a pure function of the fault value. The terminator's
module holds the only copies of the panic prefix, the dispatch-fault template,
the report stream and the exit statuses:

- **Prefix:** `error: runtime panic: `, one constant for every mode (§12.7.5).
  The terminator inserts nothing between the prefix and the message. A raiser
  that knows a source location leads its message with `<file>:<line>: `, which
  gives §12.7.5's located form.
- **Stream:** stderr, plain text, in every mode. The terminator reads no mode
  and no host state, so the REPL needs no formatter registration (packet A4).
- **Status:** `1` for language panics, dispatch faults, runtime defects and
  switch-install misuse, which keeps today's batch status; §12.7.4.2 requires
  only that it be non-zero. `70` (`EX_SOFTWARE`) for the backstop, as
  `reactor.md` §8.2 already specifies.
- **Published for the test supervisor** (packet row P11): the prefix and the
  status `1` are `pub const` items of the `panic` module, and the terminator
  composes from them, so the producer and its one consumer share one copy. The test supervisor classifies a child's ending as
  a panic only when both the status and a prefixed stderr line are present
  ([test runner §6.5](../int/test-runner.md#65-the-test-child)). The status is
  shared with the other fault kinds, which is why the dispatch-fault report
  does not carry the panic prefix: a dispatch fault in a test child reads as a
  failed test naming its cause, not as `PANIC:`.

**Every report is one line.** Each piece of text the terminator inserts — a
panic message, a platform function name, a dispatch cause, a defect payload or
the backstop diagnostic — passes through one wrapper:

- **Escaped:** every control character (`char::is_control`) and the Unicode
  line and paragraph separators, U+2028 and U+2029. Each is written as its
  Rust-style escape, such as `\n`, `\t`, `\u{1b}` or `\u{2028}`.
- **Unchanged:** all other text.

So no inserted text can end the report's line or start a second line that
imitates another report, such as a dispatch cause that contains
`\nerror: runtime panic: …`. The line's only terminator is the one the
template appends. The rule applies to framing only. It is not a content filter
(§1.5).

Two characters are deliberately not escaped:

- **The backslash.** A message that contains a literal backslash and `n` reads
  the same as an escaped line break, so the report cannot always be decoded
  back to the original text. That is accepted. No consumer decodes the text:
  the test supervisor matches only the prefix and quotes the line, and people
  read it. Escaping the backslash would double every backslash in ordinary
  messages, such as Windows paths and regular expressions, to protect a
  decoding that nobody performs.
- **Other Unicode format characters,** such as bidirectional overrides
  (U+202A–U+202E, U+2066–U+2069) and zero-width joiners. They can change how a
  terminal displays the rest of the line. They cannot add a line or change the
  line's leading bytes, which are the only part a consumer matches. The text
  comes from the program and its platforms, which the operator controls
  (§1.5). Escaping the whole format category would corrupt legitimate text,
  for example emoji sequences that use zero-width joiners. **Trigger to
  revisit:** a report sink that renders text from a party the operator does
  not control.

**The runtime-defect report (S123 ruling).** It is
`error: runtime defect: <payload>`, on one line.

- The payload is the Rust panic payload when that payload is a `&str` or a
  `String`. Any other payload is reported as one fixed placeholder.
- The report must not begin with the panic prefix. A runtime defect is a
  fault in the runtime, not a language panic. So, like a dispatch fault, it
  reads as a failed test in a test child, not as `PANIC:`. The
  `error: runtime defect: ` lead differs from the prefix at its second word,
  and the test supervisor matches the whole prefix
  ([test runner §6.5](../int/test-runner.md#65-the-test-child)).
- The text is diagnostic, not normative. §12.7.5 governs panic reports only.
  The defect template lives in the terminator's module beside the prefix.

The dispatch-fault template is the only copy of that text. No host composes a
dispatch-fault report, and packet row P9 removed `PlatformError::DispatchError`.

**Why the runtime ends the process, rather than returning a fault to a host:**
the fault is raised inside JIT frames that have no unwind tables, so control
cannot reach a host boundary without either returning a placeholder value
(ACT-1040, ACT-1042) or a non-local jump that skips Rust destructors
(`design/backend/s122-closure.md` §10.3, option C). Exiting at the raise needs
neither. Destructors that do not run are leaks, which `spec/12-runtime.md`
§12.7.8 permits.

### 1.2 Threads

- **Any thread may terminate.** A panic on a rayon worker running a spark, a
  `Par` blocking branch, the reactor thread or a REPL evaluation thread calls
  the terminator directly on that thread. `exit` ends every other thread. No
  thread joins another.
- **The reported panic is the first to win the claim.** Under concurrent
  evaluation it need not be the source-order-first panic; which one wins is
  unspecified (§12.4.3). A source-order-first report would need the join-side
  ferry that §1.3 retires.
- **Losers never run user code again.** A parked loser holds whatever JIT frame
  raised it. It is reclaimed by the exit.
- **A Rust panic in intrinsics code is a defect, not a language panic.**
  Outside the supervised-strand boundary it keeps today's behaviour: it cannot
  unwind out of an `extern "C"` entry, so the process aborts with Rust's
  message.

### 1.3 What the terminator retired

No fault is ever carried back to a host, so everything that existed to carry
one was removed. The crate has none of the following, and none should return:

- **The two thread-local error slots** (runtime error and dispatch fault) and
  every take, set and peek over them.
- **The fork-join ferry.** This means the IVar `error` field and its
  re-raise on every reader (`ivar.rs`), the `Par` worker-to-join ferry at both
  sites (`reactor.md` §2.6), and the inline-claim save and restore around a
  thunk. The IVar cell has no `error` word. The layout is intrinsics-private:
  the backend reads only the IVar RC offset.
- **The trampoline's post-arm slot checks** (`reactor.md` §4) and the
  fault arm of its stopped outcome. Stopping remains for cancellation only.
  This also removed the abort-path leak in
  [trampoline ownership transitions](ownership-and-disposal.md#7-trampoline-ownership-transitions):
  no fault path returns through the loop.
- **The supervisor's failure policy,** `LogAndDrop` and the `StrandFailed`
  event. The supervisor still owns completion, result disposal, the global
  permit and cancellation (`reactor.md` §2.12).
- **The trace guard's panic cleanup.** No same-thread evaluation follows a
  panic, so a guard left set cannot be observed.
- **The program driver's outcome struct.** `cranelisp_run_program` returns the
  program's reduced result word and has no error kind. The linked stub's drain
  export (`cranelisp_check_runtime_error`) is gone.
- **`catch-runtime-error`**, its export and its catalog row.

The dispatch guard stays. It is still the one place that turns a faulting
platform thunk (a Rust panic payload or a caught hardware signal) into a
reported termination instead of a raw signal death. It calls the terminator.

### 1.4 Exit-time diagnostics

`std::process::exit` runs the registered exit handlers on the terminating
thread while other threads may still be running.

- **`[RC_STATS]` and `[SPARK_STATS]` still print.** They read atomic counters;
  under concurrent workers the counts are approximate, as for any exit.
- **M3 parity stands down after a fault termination.** A panic leaks
  frame-owned values by permission, so an imbalance after one is expected, not
  an invariant breach. The hard check reads the termination claim. When the
  claim is held, it prints one line saying that parity was not checked because
  the process ended by a fault, and it does not abort. It does not change the
  exit status. The dump face prints its ledger as usual. Detail is in
  [`diagnostic-modes.md`](diagnostic-modes.md) §3.
- **Host flushes are the host's.** int registers its trace-sink flush as an
  exit handler, because a runtime termination bypasses its own `process::exit`
  sites ([observability §7.1](../int/observability.md#71-process-exit-and-panic-wiring)).
  It needs no runtime API.

### 1.5 Diagnostic data

The report carries:

- the panic message: source literals, or the primitives' and intrinsics'
  fixed raise texts;
- or a platform function name with its fault cause, which is a platform panic
  payload or a signal name.

These are program and platform text that the operator already controls. They go
to the process's own stderr. No credible protected value reaches this sink, so
no filtering is designed.

### 1.6 Consequences for other surfaces

These are stated for their owners; the rulings that govern them are the arch
contract's §1.4–§1.6.

- **`design`(int).** The REPL ends at a panic. The `--run` and REPL hosts have
  no slot drains and no dispatch-fault composition. The linked stub calls
  `cranelisp_run_program`, then exits through its clean path only. A
  macro-expansion panic ends the process. The compiler test runner runs tests
  in a child restarted after a panic, classifying endings by P11's constants
  ([test runner §6.5](../int/test-runner.md#65-the-test-child)).
- **`design`(backend).** `runtime/panic` declares no return (§2 of
  [`intrinsics-table.md`](intrinsics-table.md)), so code after the call is
  unreachable and the `0` sentinel has no reader. The backend converges every
  emission onto one helper that also ends the block
  ([safety invariant R13](../arch/safety-invariants.md)). Backend unit
  tests observe a raise in a child process, because no slot remains to read.
- **`dev`(primitives).** The ring-0 and marshal raisers call a function that
  does not return, so code after the call is unreachable.
- **Platforms.** `poll-pool` resolves `runtime/panic` by name. The C ABI is
  unchanged; its fault ends the process and never reaches a supervisor.

### 1.7 Evidence seams

`qa`'s allocation is the [S123 evidence delta](../../tests/plan/s123-evidence-delta.md)
§3.2. This crate's module rows are P-13, P-14 and P-16. The design-specific
seams they need:

- **In process:** report composition is a pure function of the fault value,
  and the claim is a pure state transition, so both are unit-testable without
  exiting. `has_return: false` for `runtime/panic` comes from ACT-1033's
  derivation.
- **The defect report:** a module test composes a runtime-defect fault and
  asserts the whole report line. It also asserts that the line does not start
  with `PANIC_REPORT_PREFIX`, which is the negative leg.
- **One-line framing:** module tests compose every fault kind with a
  multiline payload and assert one line, and assert that a dispatch cause
  holding a prefixed line yields no prefixed line. The control is a
  single-line payload reported verbatim in every kind. A child-process cell
  writes a multiline dispatch cause through the real terminator.
- **Child process:** status, report, ordering, the two-raiser single report
  and the M3 stand-down use the harness shape in
  [`diagnostic-modes.md`](diagnostic-modes.md) §7.6. The detection proof is a
  terminator that returns instead of exiting, which turns the ordering and
  one-report cells red.

---

## 2. Runtime switches

### 2.1 One switch source

Every configuration value the runtime reads comes from one module, the
`runtime_switches` module of packet row P8. No other code in the crate reads
the process environment.

- **A closed set.** The switches are a closed enumeration, one member per
  value the runtime reads. Each reader names its member, never a string, so an
  undeclared switch cannot be read. The census below, read at source on
  2026-11-15, is the arch contract's §2.2 census for this crate:

  | Module | Switches |
  |---|---|
  | `alloc.rs` | `CRANELISP_HEAP_SCAN` |
  | `rc.rs` | `CRANELISP_RC_TRACE`, `CRANELISP_NONATOMIC_RC`, `CRANELISP_RC_STATS` |
  | `diagnostics.rs` | `CRANELISP_QUARANTINE_FREED`, `CRANELISP_QUARANTINE_MAX_BYTES`, `CRANELISP_SCRUB_FREED`, `CRANELISP_ALLOC_PARITY`, `CRANELISP_ALLOC_PARITY_DUMP`, `CRANELISP_RC_DEC_CHECK`, `CRANELISP_TEST_FAULTS`, `CRANELISP_TEST_FAULT` |
  | `ivar.rs` | `CRANELISP_SPARK_STATS`, `CRANELISP_IVAR_SPIN`, `CRANELISP_SATURATION_GATE`, `CRANELISP_SPARK_CORE_MULT`, `CRANELISP_SPARK_BUDGET`, `CRANELISP_SPARK_MAX_DEPTH`, `CRANELISP_HIER_DECLINE` |
  | `reactor.rs` | `CRANELISP_DRIVE_MODE`, `CRANELISP_REACTOR_BACKSTOP_MS`, `CRANELISP_DEGREE` |

  The other crates linked into an executable — `cranelisp-primitives`,
  `cranelisp-platform` and `cranelisp-exe-bundle` — read no environment. The
  one remaining case is the `rayon` pool (§2.3).
- **Snapshot once.** The first read anywhere takes one snapshot of every
  member. Each gate still memoises its parsed value, so
  [`diagnostic-modes.md`](diagnostic-modes.md) §4's "off means no work" holds:
  one cached load per gate.
- **Two sources, chosen before the snapshot.**
  - *Process environment* is the default. It serves the compiler process
    (`--run`, `--test`, the REPL), where int's file supply has already run, so
    file-supplied values reach the runtime.
  - *Baked* is installed by a linked executable's startup stub. The runtime
    then never reads its launch environment.
- **Installing after the snapshot is refused.** If any switch was read before
  the install, the install calls the terminator with a located configuration
  fault. A stub ordering error therefore fails loudly at startup rather than
  silently reading the launch environment.

### 2.2 Baking at link, installing at startup

- **Capture** (the compiler, at `--link`). The runtime encodes the current
  snapshot (each member that is set, and its value) into an opaque byte block.
  The encoder and decoder are both in this crate, so int never knows a switch
  name or the format (Principle 07). The block carries a format byte. The
  runtime ships with its compiler, so the decoder rejects an unknown format or
  an unknown name as a configuration fault rather than skipping it.
- **Embed** (`design`(int)). The link step places the block in the startup
  object as read-only data.
- **Install** (the stub's first act). The stub calls the runtime's install
  export with the block's address and length before anything else, including
  primitives GOT population and platform initialisation, because those can
  allocate and allocation reads the heap-scan gate.
- **The baked set is the closed set.** The agent's variables, other
  `CRANELISP_*` settings and foreign keys are not members, so they cannot be
  baked. This satisfies the agent ruling by representation, not by a filter.
  Compile-only switches are already fixed in the emitted code. Switches read
  both at codegen and at runtime, such as `CRANELISP_RC_STATS` and
  `CRANELISP_RC_DEC_CHECK`, now agree in a linked program; today the runtime
  half can differ from the code it runs.

### 2.3 The worker count

`rayon`'s global pool reads `RAYON_NUM_THREADS` from the process environment
when the pool is first built. In a linked executable, that would be an
environment read outside a platform. So the install step builds the global
pool explicitly with the machine's available core count, and
`RAYON_NUM_THREADS` is neither baked nor read (§0.8). The compiler process
keeps `rayon`'s default.

### 2.4 Data and residuals

- Baked values are stored verbatim, as plain text in the executable. They are
  diagnostic and scheduling knobs. The set holds no credentials, by
  construction. Verbatim storage also makes a baked value observable in the
  executable's bytes, which the evidence relies on.
- `cranelisp-types`' `ownership_analysis_off` reads the environment, but only
  at analysis time. **Falsifier:** a linked-runtime path that calls it.
- Platforms read the environment on the program's behalf. That is the
  sanctioned path. The stub does not alter the environment, so a platform sees
  the launch environment.

### 2.5 Evidence seams

`qa`'s allocation is the evidence delta §3.4: B-1 to B-4 end to end, and B-5
as this crate's module rows. The design-specific seams:

- the capture/install round trip is a pure encode and decode, testable per
  member without a link;
- install after a read must exit, so that row is a child-process cell;
- the source census is a crate test that fails on a process-environment read
  outside the switch module, with a planted read as its detection proof;
- the explicit pool build is observable only from inside the crate, because
  no program observes the pool size.

---

## 3. Public-API delta

The exact rows, consumers and `public-api.txt` effects are `arch`'s
[S123 API packet](../../sprints/s123-api-packet.md). This crate's rows:

| Row | Change | Gate |
|---|---|---|
| P1 | remove `panic::catch_runtime_error` (export `catch-runtime-error`) and its catalog row | approved |
| P2 | remove `panic::take_runtime_error`, `panic::set_runtime_error` | approved |
| P3 | remove `panic::DispatchFault`, `panic::set_dispatch_fault`, `panic::take_dispatch_fault` | approved |
| P4 | remove `panic::ProgramOutcome` and `panic::cranelisp_check_runtime_error` | approved |
| P5 | `panic::cranelisp_run_program(main_ptr, main_returns_io) -> i64` (was `-> ProgramOutcome`) | approved |
| P6 | `panic::runtime_panic(msg_ptr, msg_len) -> !` (was `()`); C ABI unchanged | approved |
| P7 | the `runtime/panic` catalog row declares `has_return: false`, by ACT-1033's derivation; no public item changes | approved |
| P8 | add `runtime_switches` with `capture_runtime_switches() -> Vec<u8>` and export `cranelisp_install_runtime_switches(ptr: *const u8, len: usize)` | approved |
| P11 | add `panic::PANIC_REPORT_PREFIX` and `panic::PANIC_EXIT_STATUS` (§1.1) | approved |

P1–P7 and P11 are built; P8 is not yet built.

- **Consequence outside this crate:** P9 removed
  `PlatformError::DispatchError` from `cranelisp-types`, because §1.1 left
  it with no producer.
- **No new crate edge.** int and exe-bundle already depend on intrinsics; the
  exe-bundle `pub use` that force-links P8's export is a source change in a
  crate with no baseline.
- **Cache.** No sidecar shape changes. Build identity invalidates stale
  objects that import the removed `catch-runtime-error`.
- **Owed, not settled here:** packet row R10-9 needs the closure, ADT and Vec
  layout constants that intrinsics will own listed jointly with
  `design`(backend) before it can return to the gate.
