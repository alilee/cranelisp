# Test discovery and error capture — `discover-tests` / `catch-runtime-error`

**Status.** Adopted subsystem contract, landed. The surface was settled by the
user across four convergences on 2026-06-06 and implemented S76–S77; the
fork-join error-slot ferry landed S76 (BC §4b invariant 13) with its Par-boundary
witness in S85; the friendly `--link` rejection landed S87. Owner `arch`.
Companion: [execution tracing](tracing.md) (shares the runtime shape). Normative
surface: `spec/appendix-a-builtins.md` §A.3, `spec/03-types.md` (`Result`,
`Pair`), `spec/12-runtime.md` §12.4.3 and §12.7, `repl/spec/16-test-discovery.md`.

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

Everything else — selection, filtering, iteration, result interpretation,
reporting, timing via `trace` — is in-language code in the stdlib
(`stdlib/testing/runner.cl`). The `/run-tests` slash commands are a convenience
over the same core, not the capability itself.

### Document map

| Section | Contents |
|---|---|
| §2 | The settled rulings and the fork-join ferry obligation |
| §3 | The requirement |
| §4 | The user experience — defining, running, the in-language runner, the combinator, `--link` |
| §5 | The language constructs — signatures, eligibility, capture scope, visibility |
| §6 | The implementation — publication kinds, the extern, the combinator, the ferry, seeding, per-crate obligations |
| §7 | Data structures and sequence walk |
| §8 | Retired section remaps |

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
- **`--link` — discovery is dev-session-only; capture works everywhere.** A
  linked executable has no live session to scan, so `discover-tests` is refused
  under `--link` (§4.5); `catch-runtime-error` is a self-contained intrinsic and
  resolves in every mode. Resolving `discover-tests` under `--link` (a stub or
  elision) reopens a settled ruling and needs the user.

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
- **Runtime observation instead of a `super` import.** `spec/08-modules.md`
  §8 directs test submodules that would need their parent's symbols to
  `discover-tests`, which observes the parent's symbol table at runtime through
  the live GOT, so no parent↔child import cycle is constructed.
- **Minimal surface, maximal in-language composition.** Nothing more is owed by
  the compiler than the two entries. Every richer concept — a `TestCase`
  carrier, tallies, progress dots, timing, substring selection — is stdlib code
  over them.

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
  test-add ................................ ok
  test-div-zero .......................... ok

2 passed, 0 failed in 2.34ms
```

`/run-tests [module]` runs the current or named module; `/run-all-tests` runs
every project-root module (`repl/spec/16-test-discovery.md` §16.2). *As built* they
scan through `discover_test_names`, a separate walk from the extern's
`discover_eligible_tests` that checks prefix, zero parameters and compiled code
but not the return scheme (§6, source-read lead).

### 4.3 The in-language runner over discovered pairs

```clojure
(import [primitives [discover-tests catch-runtime-error]])

;; (catch-runtime-error run) :: (Result (Option String) String)
;;   (Err msg)        — the test panicked
;;   (Ok None)        — the test passed
;;   (Ok (Some why))  — the test reported an assertion failure
(defn run-one [pair]
  (match pair
    [(Pair name run)
     (match (catch-runtime-error run)
       [(Err msg)  (str-concat name " PANIC: " msg)
        (Ok r)     (match r
                     [None       (str-concat name " ok")
                      (Some why) (str-concat name " FAIL: " why)])])]))

(defn run-all []
  (vec-map run-one (discover-tests [])))

(defn run-matching [substr]
  (vec-map run-one
           (vec-filter (fn [p] (match p [(Pair nm _) (contains? nm substr)]))
                       (discover-tests []))))
```

The three-way fold is the payoff of the two rulings composing: ruling 2 turns
"did it panic?" into the outer `Result`, and the test's own `(Option String)` is
the inner pass/fail. Selection is plain `vec-filter` over the pairs, and because
each callable is late-bound a `discover-tests` call evaluated after a new
`test-*` is defined includes it. (Match arms are one bracket of alternating
pattern/body pairs and constructor patterns bind symbols only, so the fold is a
nested match — `stdlib/testing/runner.cl` is the shipped form.)

### 4.4 The `catch-runtime-error` combinator, directly

```clojure
(import [primitives [catch-runtime-error]])

(defn safe-div [a b]
  (match (catch-runtime-error (fn [] (/ a b)))
    [(Ok q)   q
     (Err _)  0]))
```

The combinator invokes the thunk on the calling thread, reads-and-clears the
thread-local slot, and returns `(Err msg)` on a lowered `runtime_panic` (match
non-exhaustion, division by zero, vec out-of-bounds) or `(Ok result)`.

### 4.5 What `--link` users see

A `--link` build whose function bodies reference `discover-tests` — by bare
imported name or FQ — is refused **before linking** with a diagnostic naming the
symbol, the referencing site and the remedy
(`src/exe.rs::reject_dev_session_externs_in_link`, S87). Detection is
structural: a body reference whose terminal entry is a host-promised
`RustPrimitive` named in `worker::DEV_SESSION_ONLY_EXTERNS`. An import alone
is not a reference (the prelude glob re-exports every primitive), and a user
`mod/discover-tests` definition is not caught.

`catch-runtime-error` works in `--link`: it is a self-contained intrinsic that
calls a closure already in the program and constructs a heap `Result`. This is
the deliberate asymmetry — error capture is a runtime capability available
everywhere; discovery is a dev-session capability.

**History that binds.** The refusal replaced the interim raw `cc`
`undefined reference to discover-tests`. When a S86 repro asserted that the
linked build should resolve the extern and exit 0, `arch` rejected that oracle:
resolving discovery at `--link` erases the asymmetry and needs a user
re-convergence. The guard (`tests/link.rs`) asserts non-zero exit and a message
naming `discover-tests`; only the channel and phrasing changed when the friendly
diagnostic landed.

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
  (`src/session_v4/test_runner.rs::test_scheme_is_eligible`). The wrapper's own
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
current module), scans each module's table for eligible entries and, per test,
builds a heap `String` name and a heap closure `[header | code_ptr=wrapper |
drop_glue_ptr=0 | slot-address]` whose wrapper loads the slot and calls the
current body. A null `TEST_RUNNER` (no eval active) returns an empty `Vec`.

*Source-read leads, unresolved (routed to `qa`):*

- The discovery-time warning for a mis-typed `test-*` (§2 eligibility) has no
  emission site found — the extern defers it to the slash-command path and
  `handle_run_tests` emits none. Exclusion is implemented; the warning is not.
- `/run-tests` discovers through `discover_test_names` (prefix, zero
  parameters, compiled body), not `discover_eligible_tests` (which also
  requires the exact scheme). Two scans with different eligibility can disagree
  on a mis-typed `test-*`; `src/CLAUDE.md` §Test discovery states they share a
  core.

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

### Binary — bootstrap, the extern, the `--link` gate

`src/bootstrap.rs` seeds both entries and the two ADTs; `worker::build_session_jit`
promises each name in `DEV_SESSION_ONLY_EXTERNS` (today `discover-tests`) via
`define_symbol`; `src/exe.rs::reject_dev_session_externs_in_link` is the
`--link` gate (§4.5). `TestRunnerState` lives on `SharedState`.

### Stdlib and REPL

`stdlib/testing/runner.cl` is the in-language runner over the pairs — ordinary
functions, no macro. The `/run-tests` commands are a Rust path
(`src/repl/commands.rs::handle_run_tests` → `run_test_by_name`, which brackets
the GOT call with the same slot clear/read the combinator uses); the two leads
above apply to it.

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

## 8. Retired section remaps

Earlier revisions carried the four-convergence deliberation, an as-built
archaeology and a dated change history; Git holds them. For readers holding an
old citation:

| Old citation | Now |
|---|---|
| §1 "Why the names-only / macro-runner design fell (ruling 1)"; §8d | §2 "Return shape" |
| §1 "What `catch-runtime-error` becomes (ruling 2)" | §2 "`catch-runtime-error`" and §5 |
| §2 q-scope / q-overload / q-rte-name / q-eligibility / q-cascade | §2 bullets (the spec cascade is landed; see the normative surface in Status) |
| §2 / §5 / §6 "the fork-join error-slot ferry obligation" | §2 "The fork-join error-slot ferry obligation" (rationale) and §6 "The fork-join error-slot ferry" (mechanism) |
| §4.5 "S86 D5a ruling" and FIXME 0406 | §4.5 (the friendly rejection is landed) |
| §5 "scope item 5" (trace-guard cleanup) | §5 "Trace-guard cleanup" |
| §5 "The Pair tradeoff"; §6 "Pair + Result seeding delta" | §5 `discover-tests` bullet and §6 "`Pair` and `Result` seeding" |
| §6 "`DefKind::PrimitiveExtern`" | §6 "Two publication kinds" (host-promised `RustPrimitive`) |
| §6 "Spec — the cascade" | landed; normative homes listed in Status |
| §8 superseded explorations; §9 as-built archaeology; §10 change history | Git history |
| Line-number citations `§150` (q-overload), `§162` (q-eligibility) | §2 "One extern taking `(Vec String)`", §2 "Eligibility" |
