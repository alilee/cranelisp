# Test discovery and error capture — `discover-tests` / `catch-runtime-error`

**Status.** Owner `arch`. The language surface (§§1–7) is an adopted,
landed contract: settled by the user on 2026-06-06, implemented S76–S77, with
the fork-join error-slot ferry landed S76 (BC §4b invariant 13) and its
Par-boundary witness S85. The compiler test runner and the batch refusal of
`discover-tests` (§2, "Explicit test harness") were user-approved and
implemented in S122 (`src/session_v4/test_runner/`).
Companion: [execution tracing](tracing.md) (shares the runtime shape). Interior
of the runner: [`--test` and the shared test runner](../int/test-runner.md).
Normative surface: `spec/appendix-a-builtins.md` §A.3, `spec/03-types.md`
(`Result`, `Pair`), `spec/12-runtime.md` §12.4.3 and §12.7,
`repl/spec/16-test-discovery.md`, `repl/spec/00-cli-invocation.md` §0.2.2.

## 1. Overview

Test discovery lets a Cranelisp program find the tests in a module from inside
the language and run any of them, so that selection, execution and presentation
compose as ordinary user code. A test is nothing special: a zero-argument
function whose name begins `test-` and whose type is exactly
`(Fn [] (Option String))` — `None` = pass, `Some reason` = fail.

The language surface is two `primitives`-module entries plus the existing macro
system. Both parse as plain `Expr::Apply`, type by ordinary scheme resolution and
require import or FQ reference like any other `primitives` name — zero frontend
and zero typecheck special-casing.

- **`discover-tests`** — returns the eligible tests of the named modules as
  `(Vec (Pair String (Fn [] (Option String))))`: pairs of fully-qualified name
  and a **late-bound callable** that performs a GOT-slot-indirect call, so a
  redefined test runs its current body and a fresh call sees the current test
  set.
- **`catch-runtime-error`** — a standalone protected-call combinator,
  `forall a. (Fn [(Fn [] a)] (Result a String))`, usable by any code. It invokes
  a thunk and returns `(Err message)` if the thunk raised a language-level
  runtime error, else `(Ok result)`. It is the one capability a pure,
  `catch`-less language cannot compose for itself.

Everything a program builds over them — selection, filtering, iteration, result
interpretation, reporting, timing via `trace` — is in-language code, such as
the stdlib's `stdlib/testing/runner.cl`. `discover-tests` is available only in
the REPL.

Separately, the compiler owns **one test runner**. `/run-tests`,
`/run-all-tests` and `--test` are argument adapters to it
(`repl/spec/16-test-discovery.md` §16.2). It does not use the primitives or any
library code.

## 2. Settled rulings + the fork-join ferry

The user's rulings, recorded as decided. Each carries the reason a competent
contributor would otherwise be tempted to undo it.

- **Return shape — fn-value pairs, not names (ruling 1, composability).** A
  helper that wraps discovery and returns names freezes the test set at the
  helper's own expansion or compile time; every composition over it inherits
  the frozen set. Freshness must live in the returned **values**: each callable
  is a closure over a GOT slot, late-bound, and each `discover-tests` call
  rescans. A names-only return with a stdlib macro doing name→call was built and
  overturned on exactly this ground. Do not reintroduce it.
- **`run-test` — subsumed.** Running a test is invoking a discovered callable.
  No separate invoke-by-name primitive.
- **`catch-runtime-error` — a bracket combinator, not a slot reader (ruling
  2).** The thunk is handed in; the combinator clears, calls, reads-and-clears,
  and marshals `Ok`/`Err`. The language name is `catch-runtime-error`; the
  intrinsics-internal Rust slot reader keeps its name `take_runtime_error`
  (two-layer naming, §6).
- **Scope — an empty vector means the session's current module.** All-modules running is the
  `/run-all-tests` case or an explicit module list.
- **One extern taking `(Vec String)`.** Calls pass the vector:
  `(discover-tests [])` for the session's current module,
  `(discover-tests ["user.math"])` for a named module. There is no
  no-argument or single-`String` shape of the primitive and no overloads: the
  multi-signature machinery serves typed in-language bodies monomorphised per
  call site; a host-promised extern with one body and one return type does not
  fit (Principle 6). `stdlib/testing/runner.cl` provides the optional variadic
  `discover-here` macro: its no-argument form emits
  `(primitives/discover-tests [])`; named arguments become a vector of paths.
  The empty vector means the session's current module, not the caller's
  lexical module, and discovery does not extend scope through imports; see
  [REPL module scope](../../repl/spec/16-test-discovery.md#163-the-primitives-uncovered-s122).
- **Eligibility — prefix AND exact signature.** A `test-*` fn contributes a pair
  only if its scheme is exactly `(Fn [] (Option String))`. A mis-typed `test-*`
  is excluded, and warned at discovery time, so a silently skipped test cannot
  read as "no failures". Rejected: refusing at `defn` (a legitimately non-test
  `test-`-prefixed helper would error) and widening the return type.
- **Visibility — binary.** The entries are ordinary `primitives` names:
  import-required or FQ, shadowable, not reserved. Whether the prelude
  re-exports them is a stdlib packaging choice.
- **Discovery is REPL-only; capture works everywhere.** `discover-tests` needs
  a live dev session, so a program that references it is refused under
  `--run`, `--link` and `--test` (§4.5). Under `--test` the compiler runner
  discovers the tests; test code does not. `catch-runtime-error` is a
  self-contained intrinsic and resolves in every mode. Making `discover-tests`
  available outside the REPL, by a stub, an elision or installed runner state,
  reopens a settled ruling and needs the user.

### Explicit test harness — the compiler runner

The requirements are [CLI invocation](../../repl/spec/00-cli-invocation.md)
§0.2.2 and [test discovery](../../repl/spec/16-test-discovery.md) §16.2 and
§16.6. The interior, including its module map, is [`--test` and the shared
test runner](../int/test-runner.md).
[ACT-0988](../../sprints/actions/ACT-0988-project-regression-discovery.md)
retains only the deferred scope: configurable selection, discovery beyond the
import chain, and option-controlled failure diagnostics.

- **One runner; the modes are argument adapters.** `/run-tests`,
  `/run-all-tests` and `--test` supply a module selection to one runner and
  otherwise behave identically. Eligibility, warnings, execution, the report
  (including the empty-run `No tests found`) and failure handling are the same
  code ([Principle 7](principles/07-single-source-of-truth.md)): the REPL
  commands and `run_tests` all call `CompilerSession::run_test_modules`, and
  that runner and the `discover-tests` extern list tests through the one scan,
  `discovery::scan_modules`. Only the host's use of the result differs: the
  CLI writes the report to stdout, writes warnings to stderr and exits with the
  report's status; the REPL displays both and continues. A mode-specific
  message, report or failure policy is a defect.
- **Selection is the only input that varies.** `/run-tests` selects the current
  or named module and `/run-all-tests` every loaded module that is not a
  library module ([test runner §4.1](../int/test-runner.md#41-classifier)). `--test`
  selects the entry module's import chain over published symbol tables, and
  traversal stops at library modules (§0.2.2).
- **Binary-only, one public entry point.** Selection, running and reporting
  stay in the root crate. The edges the chain needs are already on each
  published symbol table, so no library crate, cache schema, ABI or
  `public-api.txt` baseline changes. The binary target reaches the runner
  through the user-approved `CompilerSession::run_tests(&self) ->
  Result<TestRunReport, CranelispError>` and the report's `text`, `warnings`
  and `exit_code` accessors. The report carries the verdict, so the binary
  applies no policy of its own. The runner core, the eligibility scan and any
  new session state stay crate-private.
- **One compile path.** `--test` compiles exactly as `--run` does
  ([Principle 11](principles/11-single-pipeline-mode-parameters.md)), in the
  same batch run mode (there is no `RunMode::Test`). Only the post-compile
  driver differs: it calls `run_tests` where `--run` calls `trampoline`.
  `main` is neither required nor called; its shape checks sit at the `--run`
  and `--link` driver seams, not in compilation.
- **One refusal across the batch modes.** Each batch driver seam
  (`trampoline`, `link_by_name`, `run_tests`) applies the one existing
  compiled-reference detector before anything runs or is written (§4.5). The
  REPL enters through none of them, so the refusal needs no mode test.
- **Library classification comes from resolution.** Classify a module by the
  search tier that resolved its file
  ([Principle 24](principles/24-resolve-once.md)), not by a path prefix: the
  default library directory `{project_root}/stdlib/` lies inside the project
  root. `SelectionInputs::classify` compares the recorded file with the
  resolver's own `pipeline::project_root_candidate`.
- **The exact scheme is a soundness condition.** The runner reads a test's
  return word as an `(Option String)`, so a `test-` function returning any
  other type would be misread. Do not relax the predicate to the prefix.

### The fork-join error-slot ferry obligation

The error slot is `thread_local!`. Lenient evaluation (`compile_let_lenient`,
IVars over rayon) and Par branches (`dispatch_par_branches_with_trace`) run pure
work on worker threads, so a panic inside a thunk's body can land in a worker's
slot rather than the one the combinator reads. Before S76 neither join path
checked the worker's slot: the panic was swallowed, the joined value was the
sentinel, and the worker's slot stayed polluted — a violation of spec §12.4.3's
promise that lenient evaluation is observationally equivalent to sequential.

**Every fork-join boundary ferries the slot** (landed S76; BC §4b invariant 13):

1. worker-side — after running a work item, `take_runtime_error()` on the
   worker and carry `(result, Option<err>)` back;
2. join-side — re-raise the **first** error into the joining thread's slot via
   `set_runtime_error` and yield the sentinel. First-error-wins matches
   sequential semantics, where the first panic aborts the whole expression;
   aggregation is rejected.

**Why this keeps the combinator simple.** Both parallelism forms are structured
fork-join: the expression does not return until every branch has joined. So
every spark joins back inside the dynamic extent of any enclosing
`catch-runtime-error` bracket, and by the time control returns to the
combinator's frame any worker error is already in its own thread's slot. The
combinator stays a plain own-thread reader with **zero special-casing**; the
ferry lives entirely in the join paths (intrinsics-owned). Spec §12.4.3 pins the
same property as a conformance rule. Evidence: `tests/spec_10_io.rs` Par-boundary
guards (S85) and the lenient-binding guard; a swallowed worker panic flips them.

## 3. The requirement

- **Tests are ordinary functions** (`repl/spec/16-test-discovery.md` §16.1):
  no registration construct, no module restriction, only the prefix and the
  exact signature.
- **Composition belongs in the language** (`repl/spec/16-test-discovery.md` §16.5): discovering,
  selecting, running and presenting are expressible as user code, and a
  composition stays aware of tests defined after its helpers were written —
  which is why discovery returns late-bound callables.
- **Runtime observation instead of a `super` import.** In the REPL,
  `spec/08-modules.md` §8 directs test submodules that would need their
  parent's symbols to `discover-tests`, which observes the parent's symbol
  table at runtime through the live GOT, so no parent↔child import cycle is
  constructed. Under `--test` the compiler runner selects the parent's tests
  itself.
- **Minimal language surface, maximal in-language composition.** The language
  owes nothing beyond the two entries. Every richer concept — a `TestCase`
  carrier, tallies, progress dots, timing, substring selection — is stdlib code
  over them. The compiler's own runner (§2) is a host facility, not language
  surface.

## 4. The user experience

### 4.1 Defining tests

```clojure
(defn test-add []
  (if (= (+ 1 2) 3) None (Some "addition broke")))

(defn test-div-zero []
  (match (catch-runtime-error (fn [] (/ 1 0)))
    [(Ok _)   (Some "expected an error")
     (Err _)  None]))
```

### 4.2 Discovering and running from the REPL

```
user> /run-tests
  user/test-add ........................... ok
  user/test-div-zero ...................... ok

2 passed, 0 failed in 2.34ms
```

`/run-tests [module]` runs the current or named module; `/run-all-tests` runs
the loaded project modules; `cranelisp --test` runs the entry module's import
chain and prints the same report (`repl/spec/16-test-discovery.md` §16.2).
A `test-` function excluded for its type produces one warning, shown before the
report.

### 4.3 The in-language runner over discovered pairs

The runnable examples — an in-language runner (`run-all`, `run-matching`) and a
direct `catch-runtime-error` use (`safe-div`) — are specified once, in
[REPL §16.5](../../repl/spec/16-test-discovery.md#165-programmatic-use);
`stdlib/testing/runner.cl` is the shipped runner. The architecture facts they
rest on:

- The three-way outcome is the two rulings composing: ruling 2 turns "did it
  panic?" into the outer `Result`, and the test's own `(Option String)` is the
  inner pass/fail.
- Selection is ordinary user code over the pairs; no discovery-side filter
  exists.
- Each callable is late-bound, so a `discover-tests` call evaluated after a new
  `test-*` is defined includes it.

### 4.4 The `catch-runtime-error` combinator, directly

The combinator invokes the thunk on the calling thread, reads-and-clears the
thread-local slot, and returns `(Err msg)` on a lowered `runtime_panic` (match
non-exhaustion, division by zero, vec out-of-bounds) or `(Ok result)`. It is
usable by any code, not only tests.

### 4.5 What `--run`, `--link` and `--test` users see

A program in which any compiled function references `discover-tests` — by bare
imported name or FQ, called or not — is refused before any code runs or any
artifact is written. The diagnostic names the symbol and a referencing
function, and its remedy is the one `repl/spec/16-test-discovery.md` §16.6
specifies. Detection is
structural: a body reference whose terminal entry is a host-promised
`RustPrimitive` named in `worker::DEV_SESSION_ONLY_EXTERNS`. An import alone
is not a reference (the prelude glob re-exports every primitive), and a user
`mod/discover-tests` definition is not caught.

The one gate is `src/exe.rs::refuse_dev_session_externs`, called by
`trampoline` (`--run`), `link_by_name` (`--link`) and `run_tests` (`--test`)
with one mode-free diagnostic. Because the REPL enters through none of those
seams, the primitive stays available there.

`catch-runtime-error` works in every mode: it is a self-contained intrinsic that
calls a closure already in the program and constructs a heap `Result`. This is
the deliberate asymmetry — error capture is a runtime capability available
everywhere; discovery is a dev-session capability.

**History that binds.** The refusal replaced the interim raw `cc`
`undefined reference to discover-tests`. When a S86 repro asserted that the
linked build should resolve the extern and exit 0, `arch` rejected that oracle:
resolving discovery outside the REPL erases the asymmetry and needs a user
re-convergence. `--run` and the linked executable must also produce the same
program output (`repl/spec/00-cli-invocation.md` §0.2.1), which is why both
refuse identically rather than `--run` resolving what `--link` cannot.

## 5. The language constructs

### `discover-tests`

```
discover-tests :: (Fn [(Vec String)] (Vec (Pair String (Fn [] (Option String)))))
```

One `(Pair name callable)` per eligible test across the named modules, sorted by
name; an empty `Vec` means the session's current module.

- **`name`** — the fully-qualified `"module/test-name"` as a `String`.
- **`callable`** — a `(Fn [] (Option String))` value whose body performs a
  GOT-slot-indirect call to the test. It closes over the slot's **address**,
  not a baked code pointer, so a redefinition the JIT writes into the same slot
  runs through the same wrapper.
- **Eligibility** — `test-` prefix AND scheme exactly `(Fn [] (Option String))`
  (`src/session_v4/test_runner/discovery.rs::is_test_scheme`). The wrapper's own
  type and the eligibility filter are the same contract.
- **`Pair`** is the minimum product the two-field return needs. It is seeded in
  `primitives` by bootstrap (`register_pair_type`), as is `Result`; a richer
  carrier is stdlib code.
- **Pure result.** The vector is returned directly, as notionally constant
  introspection. The governing contract and freshness requirement are in
  `repl/spec/16-test-discovery.md` §16.3.

### `catch-runtime-error`

```
catch-runtime-error :: forall a. (Fn [(Fn [] a)] (Result a String))
```

- **One body serves all `a`.** A plain forall scheme with empty constraints
  (modelled on `bind`); every value is a uniform i64 at the ABI, so no per-`a`
  specialisation and no constrained-fn machinery.
- **Types pure.** The bracket consumes only the error its own thunk produced and
  leaves slot state as it found it; there is no observable effect beyond
  running the thunk. If `a` instantiates to `(IO x)` the bracket covers only the
  pure construction of the IO value — a panic raised later when the trampoline
  runs it is outside the bracket and fatal (spec §A.3 catchability boundary).
- **Cross-thread soundness** comes from the fork-join ferry (§2), not from the
  combinator.
- **What it captures.** Language-level runtime errors the compiler lowers to
  `runtime/panic`: `runtime_panic` stores the message in the thread-local and
  the JIT fn returns the sentinel `0`; the combinator reads the slot after its
  synchronous call.
- **What it cannot capture.** Hard signals (`SIGSEGV`, `SIGBUS`, `SIGILL`,
  `SIGFPE`). The `sigsetjmp`/`siglongjmp` bracket exists only around
  macro-clause invocation (`src/expander.rs::invoke_jit_protected`);
  signal-protected user invocation would be a separate host primitive.
- **RC / partial-value caveat.** After a panic the aborted expression's heap
  values are in an indeterminate RC state — drop glue did not run. `(Err msg)`
  recovers the message, not a consistent heap: treat the evaluation as void.
  Documented, not fixed.
- **Trace-guard cleanup.** A panic crossing an actively tracing `(trace …)`
  body would leave the trace guard held and make the next same-thread trace
  raise "nested trace"; the combinator's `Err` path clears it
  (`crate::trace::clear_trace_guard_on_panic`).
- **Thunk ownership.** The thunk is a one-shot closure passed by move; the
  combinator consumes it on both paths, so a catch in a loop leaks nothing.

### Visibility, import and shadowing

Both entries require import or FQ reference — `(import [primitives
[discover-tests catch-runtime-error]])` or `(primitives/discover-tests …)`. They
shadow like any imported name; there is no reserved-binder enforcement.

### Untraceability of the entries

Neither entry has a GOT slot, so a call to either has no GOT-indirect callee to
redirect: structurally untraceable, the same status as an inline primitive (spec
§4.12.3 exclusion). The callables `discover-tests` returns are GOT-indirect and
therefore traceable.

### What is retired

`run-test`; `TestResult`/`TestPass`/`TestFail`; reserved-word and
keyword-dispatch rows for the two names (`trace` stays reserved); the raw
unresolved-symbol `--link` interim (§4.5).

## 6. The implementation

### Two publication kinds

Both entries are slot-less `primitives` callables of origin `RustPrimitive`
with `Life::HostPromised`, keyed by their ABI name (`src/bootstrap.rs`
`register_test_infrastructure`). The backend lowers a call to either as a
`Linkage::Import` against the key (`compiler/apply.rs`, the host-promised arm).
They differ in **who supplies the body**:

- **`discover-tests`** reads the binary's live typed session state (the
  per-module `SessionSymbolTable` + GOT) and constructs `Pair` and closure
  values. `cranelisp-intrinsics` cannot name `Code` (Principle 18), so the body
  lives in the binary and is promised at session init through
  `Jit::define_symbol` (`worker::build_session_jit`).
- **`catch-runtime-error`** needs no session: its body is the
  `cranelisp-intrinsics::panic` C-ABI export, catalogued in
  `intrinsics_table()` and therefore resolved by name at all three registration
  points (JIT setup, cache-hit linking, the linked executable).

The historical name `DefKind::PrimitiveExtern` in older comments denotes this
same host-promised class; `DefKind` no longer exists.

### Calling a language fn value from an intrinsic — the precedent

The combinator needs no backend support. Calling a closure from runtime code is
an established capability (`io::call_continuation`, the IVar thunk call), and
every thunk it can receive is a closure of the one layout `[header | code_ptr |
drop_glue_ptr | captures…]` — `compile_lambda` produces that even with zero
captures, and a named fn used as a value goes through `compile_fn_as_value` to
the same shape. So "load `code_ptr` at `CLOSURE_CODE_PTR_OFFSET`, call
`extern "C" fn(env) -> i64` with the closure as `env`" handles every thunk with
no normalisation.

### The discovery extern

`discover_tests_extern` (`src/session_v4/test_runner.rs`) reads the
`TEST_RUNNER` thread-local state, decodes the `(Vec String)` argument (empty →
current module), lists each module's tests through the shared scan
(`discovery::scan_modules`) and, per test, builds a heap `String` name and a
heap closure `[header | code_ptr=wrapper | drop_glue_ptr=0 | slot-address]`
whose wrapper loads the slot and calls the current body. A null `TEST_RUNNER`
(no eval active) returns an empty `Vec`. The extern runs inside compiled code
and has no warning channel, so it discards the scan's warnings; the slash
commands show them ([test runner §12](../int/test-runner.md#12-residual-leads)).

### The combinator intrinsic — two-layer naming

- **`catch-runtime-error`** — the language-level name: the `#[export_name]`,
  the `intrinsics_table()` entry and the `primitives` key.
- **`take_runtime_error()` / `set_runtime_error()`** — the internal Rust
  take-and-clear and first-error-wins set over the thread-local. Not C-ABI
  exports, not language names. The combinator and the ferry call them.

Body (`cranelisp_intrinsics::panic::catch_runtime_error`): clear the slot;
load `code_ptr` from the thunk and call it with the closure as `env`; consume
the one-shot thunk; read the slot; on `Some(msg)` clear the trace guard and
allocate `(Err msg)`, else `(Ok result)`. Both `Result` variants carry data and
are heap allocations.

### The fork-join error-slot ferry (intrinsics-owned)

The mechanism §2 obliges, landed S76 on both join paths:

- **Lenient-let spark/join (IVars).** The worker in `ivar_spark`/`ivar_force`
  takes its slot after running the thunk and stashes the error on the IVar;
  the joining `ivar_force` re-raises the first error via `set_runtime_error`
  and yields the sentinel (`crates/cranelisp-intrinsics/src/ivar.rs`).
- **Par fork-join.** `dispatch_par_branches_with_trace` carries
  `(result, Option<err>)` from each worker and re-raises the first at the join
  (`crates/cranelisp-intrinsics/src/io.rs`).

A dropped (cancelled) effect is not routed through the ferry, and a detached
strand has no join to deliver to (spec §12.4.4, §12.7.9;
[effect concurrency](effect-concurrency.md)).

### `Pair` and `Result` seeding

`register_pair_type` and `register_result_type` (`src/bootstrap.rs`, steps 4b
and 4c) seed `(Pair a b)` (one 2-field data ctor) and `(Result a b)`
(`Ok`/`Err`, tags 0/1 in declaration order — the combinator's `RESULT_TAG_*`
constants match) into `primitives`, on the `register_option_type` pattern. No
nullary ctors are involved, so all three are heap allocations. Stdlib may
re-export or restate them; that is a packaging choice.

### Frontend — nothing (zero special-casing)

Both forms parse as plain `Expr::Apply` to an `Expr::Var`. The former
head-position builders and keyword rows for `discover-tests`/`run-test` are
deleted; `trace` keeps its builder. No `Expr` variant, no reserved-word status.

### Typecheck — nothing (zero special-casing)

The callee resolves like any symbol in the `primitives` table; the combinator's
forall instantiates at each call site as `bind`'s does. Discovery-driven entry
points are monomorphisation roots like `main` (BC §2 invariant 12).

### Backend — one host-promised call arm; `Jit::define_symbol`

A host-promised callee lowers as a `Linkage::Import` against the entry key,
identical in shape to the platform-effect and intrinsic import paths. The
combinator needs no arm of its own — it is an ordinary catalog import — and no
codegen change: the closure call is inside the intrinsic body.

`Jit::define_symbol(name, ptr)` inserts into the map the JIT's
`symbol_lookup_fn` consults at module finalization, so an unresolved
`Linkage::Import` against `name` settles to the promised pointer. It is the one
additive host-symbol escape hatch — no forked constructor, no registry (BC §3
invariant 8). `catch-runtime-error` does not use it.

### Binary — bootstrap, the extern, the batch refusal gate

`src/bootstrap.rs` seeds both entries and the two ADTs; `worker::build_session_jit`
promises each name in `DEV_SESSION_ONLY_EXTERNS` (today `discover-tests`) via
`define_symbol`; `src/exe.rs::refuse_dev_session_externs` is the
refusal gate at the three batch driver seams (§4.5). `TestRunnerState`
lives on `SharedState` and serves only the REPL extern; the compiler runner
does not install it.

### Stdlib and REPL

`stdlib/testing/runner.cl` is the in-language runner over the pairs — ordinary
functions, no macro. The `/run-tests` and `/run-all-tests` commands
(`src/repl/commands.rs::handle_run_tests`, `handle_run_all_tests`) select
modules and call the compiler runner (§2), which brackets each test call with
the same slot clear/read (`take_runtime_error`) the combinator uses.

## 7. Data structures, functions & sequence

- `discover-tests`: `primitives` callable, `RustPrimitive` +
  `Life::HostPromised`, scheme `(Fn [(Vec String)] (Vec (Pair String (Fn []
  (Option String)))))`, no slot, key = ABI name, body promised by the binary.
- `catch-runtime-error`: `primitives` callable, same class, scheme
  `forall a. (Fn [(Fn [] a)] (Result a String))`, key = ABI name = the
  intrinsic's `#[export_name]`; internal mechanism `take_runtime_error` +
  `set_runtime_error`.
- Bootstrap-seeded ADTs in `primitives`: `(Pair a b)`, `(Result a b)`,
  alongside `Option`.

```mermaid
sequenceDiagram
    participant SRC as User code (run-all)
    participant DT as discover-tests extern (host-promised via define_symbol)
    participant ST as Live SessionSymbolTable + GOT
    participant TRE as catch-runtime-error (intrinsic)
    participant W as Discovered wrapper closure (late-bound)
    participant T as Compiled test fn (current GOT body)

    SRC->>DT: (discover-tests [])            [import-required primitives entry]
    DT->>ST: scan eligible test-* fns (prefix + (Fn [] (Option String)))
    ST-->>DT: slot addresses + FQ names
    DT-->>SRC: (Vec (Pair name wrapper))  [wrappers late-bound through GOT]
    loop per pair
        SRC->>TRE: (catch-runtime-error wrapper)
        Note over TRE: clear slot; call closure code_ptr(env)
        TRE->>W: call wrapper()  (extern "C" fn(env)->i64)
        W->>T: GOT-slot-indirect call (current body)
        T-->>W: (Option String)  (or panic -> sentinel 0 + slot set)
        W-->>TRE: i64 result
        Note over TRE: consume thunk; read slot -> Ok(result) | Err(msg)
        TRE-->>SRC: (Result (Option String) String)
    end
```

Freshness lives in the wrapper (late-bound through the live GOT) and in
re-calling `discover-tests` (a rescan) — never in expansion timing.
