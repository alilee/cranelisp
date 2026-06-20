# `discover-tests` / `catch-runtime-error` / `/run-tests` — test discovery & error capture

**Status.** Subsystem design. §TARGET is the current design statement
(user-converged 2026-06-06, **fourth convergence** — the user answered every open
question of the third convergence; the design is now SETTLED). The fork-join
error-slot ferry obligation decided in this document **landed in S76** and is recorded
**closed** in `bounded-contexts.md` §4b invariant 13 (both join paths ferry; the prior
"pre-existing defect / neither boundary ferries" reading is closed, the ferry is the
regression guard). The design rationale below (the correctness argument for why
ferrying makes `catch-runtime-error` sound under lenient/Par evaluation) is retained as
the record of *why* the mechanism is shaped as it is — read it as the rationale for a
landed mechanism, not as outstanding work. **The only residual is the Par-boundary e2e
witness**, gated on the S85 0367 wiring (FIXME 0398).
Supersedes the names-only / macro-runner §TARGET of the same day's PM (now §8d).
Owner `/arch`; companion to `tracing.md` (the two features share a runtime shape and
the same S76 collapse that created the defect this mechanism resolves).

---

## 1. Overview

Test discovery lets a Cranelisp program **find the tests in a module** from inside the
language and **run any of them**, so that selection, execution, and presentation can be
composed by ordinary user code. A test is nothing special: it is an ordinary
zero-argument function whose name begins `test-` and whose return type is
`(Option String)` (`None` = pass, `Some reason` = fail).

The third convergence (2026-06-06) overturned two pillars of the morning/PM
names-only design; the **fourth convergence** (same day) settled every remaining open
question (§2). The corrected surface is exactly two `primitives` entries plus the
existing macro system:

- **`discover-tests`** — returns the eligible tests of a module as a `(Vec (Pair String
  (Fn [] (Option String))))`: pairs of **(fully-qualified test name as `String`,
  late-bound callable wrapper)**. The callable is a language fn value that, when invoked,
  performs a GOT-slot-indirect call to the test — so a *redefined* test runs its current
  body. **Names-and-callables** — not names only, not a carrier ADT. *(fourth
  convergence: no-arg form = the **current** module; eligibility = the `test-` name
  prefix AND the exact signature `(Fn [] (Option String))`; the overload is **one**
  extern taking `(Vec String)`, with the no-arg and single-`String` shapes as sugar
  normalising to it.)*
- **`catch-runtime-error`** — promoted out of the test feature to a **standalone
  `primitives` entry** usable by any user code and by the stdlib, and **reshaped into a
  protected-call combinator**: `(Fn [(Fn [] a)] (Result a String))`. It invokes a
  thunk; if the thunk hit a language-level runtime error it returns `(Err msg)`, else
  `(Ok result)`. This is the one capability a pure, `catch`-less language cannot
  compose for itself. *(fourth convergence: named **`catch-runtime-error`** — the
  language-level combinator name. The intrinsics-internal Rust slot-reader keeps its
  name `take_runtime_error`: it becomes the combinator's internal mechanism — §6 makes
  the two-layer naming explicit.)*

Everything else — selection, filtering, iteration, result interpretation, reporting,
timing (via `trace`) — is **ordinary in-language code in the stdlib**. This minimal
surface is the design's center of gravity (§3.7).

Both entries are ordinary `primitives`-module symbols. They parse as plain
`Expr::Apply`, type by ordinary scheme resolution, and require import or FQ reference
like any other `primitives` name — **zero frontend and zero typecheck special-casing**.
That absence of special-casing is the whole point of the design and the reversal that
replaced the earlier root-special-form proposal (now §8b).

### Why the names-only / macro-runner design fell (ruling 1)

The PM convergence (§8d) made discovery return **names only** (`(Vec String)`) and
moved the name→callable step into a **stdlib macro** that calls `(discover-tests …)` at
expansion time and emits FQ test calls. The user overturned this on **composability**:

> "If you wrap the function (i.e. in stdlib helpers) then it suddenly stops being aware
> of new tests. It needs to be composable."

The defect is precise. A stdlib helper (a macro or a fn) that wraps the discovery call
**freezes the test set at the helper's own expansion/compile time**. Any composition
built on top of that helper inherits the frozen set; a test defined after the helper
compiled is invisible to it. **Freshness must live in the returned values, not in
expansion timing.** A `(Vec String)` of names cannot deliver freshness on its own,
because a `String` is not callable — the only way to turn it back into a call is a
macro, and the macro is exactly the freezing wrapper. Returning **fn values** moves the
freshness into the value: each wrapper is a closure over a GOT slot, late-bound, so it
always runs the test's *current* body, and a `discover-tests` call evaluated fresh
returns the *current* test set. Composition over those values stays fresh by
construction. Therefore fn-value returns come **back** from the superseded first-PM
appendix (§8c) as the target, and the names-only/macro-runner layer is retired to §8d.

### What `catch-runtime-error` becomes (ruling 2)

The PM design exposed `take_runtime_error` as a read-the-slot primitive
(`(Fn [] (Option String))`) and asked the user to clear/invoke/read around it. The user
reshaped it into a **bracket combinator** taking the protected thunk directly, and the
fourth convergence **named the language-level combinator `catch-runtime-error`**:

```clojure
(match (catch-runtime-error (fn [] (deep-func x)))
  [(Ok x)  (show x)]
  [(Err x) x])
```

The combinator invokes the thunk; if the runtime-error slot fired, it clears the slot
and returns `(Err msg)`; otherwise it returns `(Ok result)`. The user noted: "This does
need backend support probably unless overloaded works." **The honest answer (§6): it is
a plain intrinsic, no backend codegen change.** Calling a language fn value from an
intrinsic is already a load-bearing as-built capability (§6 / §9 precedents), so the
combinator's body is "load code_ptr from the closure, call it, check/clear the slot,
construct `Ok`/`Err`."

**Two-layer naming (fourth convergence).** The *language* name is
`catch-runtime-error` — what user code imports and calls, and the `#[export_name]` the
intrinsic carries. The *mechanism* it uses internally is the existing Rust slot-reader
`cranelisp_intrinsics::panic::take_runtime_error()` (`panic.rs:43`), which the new C-ABI
combinator wrapper calls to read-and-clear the thread-local. The slot-reader keeps its
name; only the user-facing combinator is `catch-runtime-error`. §6 spells out the
layering at the source level.

### Document map

| Section | Contents |
|---|---|
| §1 Overview | The feature, the minimal surface, the two rulings, the document map. |
| §2 Settled rulings + the fork-join ferry | The fourth-convergence rulings (recorded as decided) and the fork-join ferry obligation — its correctness argument, now landed S76 (BC §4b invariant 13, closed). |
| §3 The requirement | Why discovery exists; tests as ordinary fns; minimal-surface center of gravity; D30 deadlock; spec promises. |
| §4 The user experience | Defining tests; a REPL session; the three-way folding runner over discovered pairs; the protection-placement payoff; what `--link` users see. |
| §5 The language constructs | `discover-tests` (signature + overloads + eligibility + module arg + the closure wrapper); `catch-runtime-error` (combinator signature + capture scope + lenient/Par soundness + the ferry obligation + caveats); visibility; what retires. |
| §6 The implementation | The two entry kinds; closure-from-intrinsic precedent; bootstrap publication; the discovery extern building Pair+closure values; the combinator intrinsic + its two-layer naming; the fork-join ferry requirement on the Par/lenient join paths; Pair/Result seeding; spec deltas. |
| §7 Data structures, functions & sequence | Entry shapes; the discovery extern; the combinator intrinsic; the stdlib runner; an end-to-end sequence walk. |
| §8 Appendix: superseded explorations | (a) five-option A–E; (b) root-special-form; (c) first-PM fn-value/pairs/run-test-keep; (d) the names-only / macro-runner convergence with its composability disproof. Compressed. |
| §9 Appendix: as-built archaeology | The current pipeline as built, compressed to what still informs the design. |
| §10 Change history | Dated evolution of this document. |

---

## 2. Settled rulings + the fork-join ferry

The fourth convergence (2026-06-06) answered every open question of the third. They are
recorded here **as decided**, not as questions. The fork-join error-slot ferry
obligation (q-rte-purity's "how does it work for lenient eval?" — the worked answer is
below and in §5) was the one item that carried as design-ahead-of-implementation; it
**landed in S76** and is recorded **closed** in `bounded-contexts.md` §4b invariant 13.
The correctness argument below is retained as the rationale for the landed mechanism.

### Settled rulings

- **return shape** — fn-value pairs (ruling 1, third convergence): `discover-tests`
  returns `(Vec (Pair String (Fn [] (Option String))))`.
- **`run-test` fate** — subsumed; running is invoking a discovered wrapper. No separate
  `run-test` primitive.
- **`catch-runtime-error` shape** — protected-call combinator (ruling 2, third
  convergence).
- **visibility taxonomy** — binary; primitives require import/FQ.
- **`--link` rejection** — none; missing host symbol unresolved at link, interim.
- **q-scope (settled)** — the no-arg `(discover-tests)` form discovers the **current**
  module. All-modules running stays the `/run-all-tests` whole-project case (or the
  explicit `(discover-tests names)` over a runner-assembled module list). The no-arg
  sugar bakes the caller's module path as a literal `String` arg (§5) — no ambient
  runtime lookup; the bake is about *which table to scan* and is unaffected by the
  fn-value return shape.
- **q-overload (settled)** — **ONE extern taking `(Vec String)`**. The no-arg and
  single-`String` shapes are **stdlib-macro sugar** normalising to the `Vec` form.
  `DefKind::Overloaded` is for typed in-language multi-clause user fns monomorphised at
  call sites (§9); a host-promised extern with no in-language body and one shared return
  type does not fit. One extern + one normalising arg is the minimum mechanism
  (Principle 6).
- **q-rte-name (settled)** — the combinator is named **`catch-runtime-error`** (renamed
  from the third convergence's `take-runtime-error`). The semantics are a protected call,
  not a slot read, so "take" described the old behaviour; `catch-runtime-error` describes
  the bracket honestly. The intrinsics-internal Rust `take_runtime_error` slot-reader
  (`panic.rs:43`) **keeps its name** — it becomes the combinator's internal mechanism
  (§6 makes the layering explicit).
- **q-eligibility (settled)** — discovery returns wrappers for fns matching **BOTH** the
  `test-` name prefix **AND** the exact type signature `(Fn [] (Option String))`. A
  mis-typed `test-*` is excluded and warned at discovery time so a silently-skipped test
  cannot masquerade as "no failures." The wrapper's own type is `(Fn [] (Option
  String))`, so the eligibility filter and the returned callable type are the same
  contract (§5).
- **q-cascade (settled — list now FINAL)** — the spec deltas are agreed (§6 detail):
  §2.9 retraction, grammar keyword-row retraction, appendix-A re-typing of both rows,
  §4.12.3 exclusion note, `TestResult` retirement, `Result`+`Pair` joining the
  `primitives` docs. The fourth convergence **adds one cascade item**: spec §12.4.3
  (Lenient Evaluation) gains a sentence pinning error propagation across fork-join
  boundaries (proposed wording in §6) — because the ferry obligation below is the
  mechanism that makes §12.4.3's "non-determinism is not observable" promise hold for
  panics.

### The fork-join error-slot ferry obligation (q-rte-purity, answered; landed S76, closed)

**The question.** The user stated `catch-runtime-error` "only works for pure functions"
— which the thunk type `(Fn [] a)` already enforces — and asked "how does it work for
lenient eval?" The thunk's *body* can, under lenient evaluation, fork pure work onto
rayon worker threads. The error slot is `thread_local!`. Does a panic on a worker get
back to the combinator's thread?

**Lenient eval is LIVE (the doc's prior "does not move work off-thread" claim was
wrong — struck).** `compile_let` checks sparkability and routes to `compile_let_lenient`
(`control_flow.rs:34` → :55 → :122); the spark/join path is implemented over **IVars**
(`compile_let_lenient` emits `cranelisp_ivar_create` :151, `cranelisp_ivar_spark` :156,
`cranelisp_ivar_force` :172). `find_sparkable_bindings` is at :1902+; the
`CRANELISP_NO_LENIENT=1` kill-switch is at :1880–1883; design doc
`design/backend/lenient-eval.md`. So a pure thunk's body genuinely can fork pure work
onto rayon workers.

**At the time of this design pass (pre-S76), no fork-join boundary ferried the error
slot — a pre-existing defect. This was fixed in S76: both join paths now ferry (BC §4b
invariant 13, closed). The pre-S76 as-built is recorded below as the motivation for the
ferry mechanism.**

- **Lenient-let spark/join (IVars).** `ivar_spark` (`ivar.rs:84`) does `rayon::spawn`
  running `ivar_force`; `ivar_force` (`ivar.rs:115`) loads the thunk's `code_ptr`, calls
  it (:137), and stores the i64 result — **no `take_runtime_error()` check on the
  worker**. The main thread's `ivar_force` join (or spin-wait) reads only the stored
  i64; a panic inside a sparked binding sets the *worker's* `RUNTIME_ERROR` slot
  (`panic.rs:34`), the thunk returns sentinel `0`, the join collects `0` with no slot
  check → the error is silently swallowed on the caller's thread, and the worker's slot
  is left polluted (a later unrelated bracket on that worker could read a stale error).
- **Par fork-join.** `dispatch_par_branches_with_trace` (`io.rs:405–484`) — the rayon
  `into_par_iter().map(...)` (`io.rs:456–473`) calls `run_io_trampoline` and returns the
  i64 result; **no `take_runtime_error()` check on the worker**. Same swallow + slot
  pollution.

This was a **pre-existing defect independent of the combinator**. Spec §12.4.3 requires
lenient evaluation to be observationally equivalent to sequential — "the non-determinism
in evaluation order is not observable" and "Lenient evaluation is semantically
transparent." Sequential evaluation panics the whole expression; parallel silently
yielded the sentinel — an observational divergence. **This defect was resolved in S76 by
landing the ferry on both join paths** (BC §4b invariant 13, closed); the only residual
is the Par-boundary e2e witness, gated on the S85 0367 wiring (FIXME 0398).

**The design obligation that makes `catch-runtime-error` sound under lenient eval.**
Every fork-join boundary MUST ferry the error slot:

1. **worker-side** — after running a work item, call `take_runtime_error()` on the
   worker and return `(result, Option<err>)` rather than a bare `i64`.
2. **join-side** — the **first** error (first-error-wins matches sequential semantics,
   where the first panic aborts the whole expression; aggregation is rejected as not
   matching the sequential model) is re-raised into the **joining** thread's slot via
   `set_runtime_error`, and the joined expression yields the sentinel.

**Soundness argument.** Both parallelism forms are **structured** (fork-join): §12.4.3
pure lets and §10.12 Par both have the property that *the expression does not return
until all branches complete*. Therefore every spark joins back **inside the dynamic
extent** of any enclosing `catch-runtime-error` bracket. With ferrying in place, by the
time control returns to the combinator's synchronous call frame, any worker error has
already been re-raised into the combinator's own thread's slot — so the bracket observes
the error correctly, with **zero combinator special-casing**. The combinator stays a
plain intrinsic that reads its own thread's slot; the ferry lives entirely in the
join paths (intrinsics-owned), not in the combinator.

**Purity note.** `a` may instantiate to `(IO x)` — the bracket then covers only the pure
**construction** of the IO value; effects run later, outside the bracket (effects escape
by construction — a property, not a problem). Test fns are `(Fn [] (Option String))`, so
this is moot for the runner.

---

## 3. The requirement

**Tests are ordinary functions.** A test is any zero-argument fn whose name begins
`test-` and whose return type is `(Option String)` — `None` for pass, `Some reason`
for fail (`repl/spec.md` §16.1). There is no test-registration construct, no
test-naming requirement beyond the prefix; eligibility additionally requires the exact
signature `(Fn [] (Option String))` (q-eligibility, §2); no module restriction.

**Composition belongs in the language.** The deliberate intent — recorded in
`repl/spec.md` §16.5 ("selection and result presentation composed using the
language") — is that discovering tests, selecting a subset, running them, and
presenting results are all expressible *as user code*. The `/run-tests` slash command
is a convenience over the same capability, not the capability itself. Composability is
the load-bearing word (ruling 1): a composition built on discovery must stay aware of
tests defined after the composition's helpers were written — which is why discovery
returns **late-bound callables**, not frozen names.

**The Decision-30 deadlock workaround.** This is why discovery exists as a *language*
form and is a spec obligation. `spec/08-modules.md` line 239 points users at it:

> Test submodules that need to enumerate their parent's symbols SHOULD use the
> `discover-tests` … builtin … these observe the parent's symbol table at runtime
> without requiring a `super` import, avoiding the deadlock entirely.

Decision 0030 records that the form-by-form scheduler deadlocks on parent↔child
mutual imports. `discover-tests` sidesteps it by reading the symbol table **at
runtime** rather than importing it. The fn-value return shape *strengthens* this: the
returned wrappers are late-bound through the live GOT, so they observe the parent's
current compiled bodies with no import at all.

**The spec promises.** `spec/appendix-a-builtins.md` §A.4 carries rows for
`discover-tests` and `run-test` (and §A.1/§A.2 the `TestResult`/`Trace` ADTs), all
marked `[R4]`. Under this design `run-test` is subsumed (running a discovered wrapper
*is* `run-test`), `TestResult` retires (§5), and `catch-runtime-error` is added as a
combinator; the appendix re-frames accordingly (§6).

**Minimal language surface, maximal in-language composition (the center of gravity,
§3.7).** All test *filtering* and *result formatting* are stdlib concerns. The language
surface is exactly: `discover-tests` (name+callable pairs) + `catch-runtime-error`
(protected-call combinator) + the existing macro system. Nothing more is owed by the
compiler. Every richer concept (a `TestCase` carrier, pass/fail tallies, progress dots,
timing reports, name-substring selection) is ordinary stdlib code over those pieces.

---

## 4. The user experience

### 4.1 Defining tests

```clojure
(defn test-add []
  (if (= (+ 1 2) 3) None (Some "addition broke")))

(defn test-div-zero []
  (match (catch-runtime-error (fn [] (/ 1 0)))   ; protected call — see §4.4
    [(Ok _)   (Some "expected an error")]
    [(Err _)  None]))
```

Nothing marks these as tests beyond the `test-` prefix and the `(Option String)`
return type.

### 4.2 Discovering and running from the REPL

```
user> /run-tests
  test-add ................................ ok
  test-div-zero .......................... ok

2 passed, 0 failed in 2.34ms
```

`/run-tests [module]` runs the current (or named) module; `/run-all-tests` runs every
project-root module (`repl/spec.md` §16.2.2). These remain fast Rust paths (int's call;
not a spec concern).

### 4.3 The in-language runner over discovered pairs (the showcase)

This is what the two rulings compose into. `discover-tests` returns pairs of
**(name, callable)**; `catch-runtime-error` brackets each callable; the runner folds a
three-way outcome per test — and it is **ordinary in-language code**, no macro:

```clojure
(import [primitives [discover-tests catch-runtime-error]])

;; Run one discovered test: returns a human-readable line.
;; (catch-runtime-error run) :: (Result (Option String) String)
;;   (Err msg)        — the test panicked (match non-exhaustion, div-by-zero, …)
;;   (Ok None)        — the test passed
;;   (Ok (Some why))  — the test ran and reported an assertion failure
(defn run-one [pair]
  (match pair
    [(Pair name run)
     (match (catch-runtime-error run)
       [(Err msg)        (str-concat name " PANIC: " msg)]
       [(Ok None)        (str-concat name " ok")]
       [(Ok (Some why))  (str-concat name " FAIL: " why)])]))

;; Run every test in the current module.
(defn run-all []
  (map run-one (discover-tests)))

;; Run only the tests whose name contains a substring — selection is in-language,
;; over the SAME pairs, and stays fresh because the callables are late-bound.
(defn run-matching [substr]
  (map run-one
       (filter (fn [p] (match p [(Pair nm _) (contains? nm substr)]))
               (discover-tests))))
```

The three-way `(Result (Option String) String)` fold is the genuinely nice payoff of
the user's two rulings composing: ruling 2 turns "did it panic?" into the outer
`Result`, and the test's own `(Option String)` is the inner pass/fail — so a single
nested `match` distinguishes **panic / pass / assertion-fail** with no special compiler
support. Selection (`run-matching`) is plain `filter` over the pairs; because each
callable is late-bound through the live GOT, a `discover-tests` call evaluated after a
new `test-*` is defined includes it, and a redefined test runs its new body — the
composability ruling 1 demands.

### 4.4 The `catch-runtime-error` combinator, directly

`catch-runtime-error` is usable by any code, not just tests — it is the language's only
way to turn a runtime panic into a value:

```clojure
(import [primitives [catch-runtime-error]])

;; Try a risky computation; recover with a default on panic.
(defn safe-div [a b]
  (match (catch-runtime-error (fn [] (/ a b)))
    [(Ok q)   q]
    [(Err _)  0]))           ; division by zero panicked — recover with 0
```

The combinator invokes the thunk on the calling thread, reads-and-clears the
thread-local error slot, and returns `(Err msg)` on panic or `(Ok result)` on success.
A passing thunk leaves the slot clear (`Ok`); a thunk that hit a lowered
`runtime_panic` (match non-exhaustion, div-by-zero, vec out-of-bounds) yields `(Err
"runtime panic: …")` instead of aborting the run.

### 4.5 What `--link` users see

```
$ cranelisp --link mytests.cl -o mytests
... links with no diagnostic for discover-tests ...
$ ./mytests
dyld: Symbol not found: discover-tests
```

**No friendly rejection (settled).** A `--link` build of a program that calls
`discover-tests` is **accepted at compile time**; the missing host symbol surfaces as
an unresolved-symbol failure at link/load, because the standalone executable has no live
session to scan and int's `define_symbol` is never called. This is the documented
**interim behaviour**; a future sprint may add a friendly diagnostic.

`catch-runtime-error`, by contrast, **works in `--link`**: it is a self-contained
intrinsic (it calls a closure already present in the linked program and constructs a
`Result` heap value — no live session needed). This is the right asymmetry: *error
capture / protection* is a pure runtime capability available everywhere; *discovery* is
a dev-session capability.

**S86 D5a ruling (2026-06-17, /arch — interim REAFFIRMED).** Sprint-86 isolation
(D5a) reduced an in-language-runner self-test blocker to this exact interim: a
`--link` build of a module that references `discover-tests` fails at the `cc` step with
a raw `undefined reference to discover-tests`, exit 1, no exe. `/qa` filed a repro
(`tests/link.rs::link_module_referencing_discover_tests_extern_resolves_at_aot_link`)
that asserted `assert_exit(0)` — i.e. that the linked build SHOULD resolve the extern
and exit 0. **That expectation contradicts the settled fourth-convergence design above
and is rejected.** Three dispositions were weighed:

- **(a) resolve `discover-tests` under `--link`** (AOT stub / elide) — reopens the
  settled "dev-session-only" ruling and erases the deliberate capture/discovery
  asymmetry. **Off-limits without a user re-convergence.**
- **(b) friendly compile-time rejection now** — the right long-term answer (it realizes
  the "future sprint may add a friendly diagnostic" path and honors the project
  no-opaque-error principle). **Deferred** — S86 is a user-facing-consolidation sprint
  already carrying heavy defect-fix load; a new compile-time gate at the int/frontend
  seam is out of proportion to the sprint. **Filed as FIXME 0406 (`target: /int`).**
- **(c) interim raw-error STANDS for S86 — SELECTED.** The current behaviour is exactly
  what §4.5 documents; the as-built (`apply.rs` `compile_extern_call` /
  `compile_apply`, the `Linkage::Import` arm — "or surfaces as an unresolved-symbol link
  error in `--link` (no friendly rejection)") is faithful. The `/qa` repro's
  `assert_exit(0)` is the wrong oracle.

**Corrected test expectation (`/qa` to encode).** The repro must assert the *documented*
behaviour: a non-zero exit (link failure), with stderr/output naming the unresolved
`discover-tests` symbol — e.g. `.assert_failure()` (non-zero exit) **and** an output
substring assertion on `discover-tests` (the linker's `undefined reference to` /
`Symbol not found` message naming the symbol). This flips the RED guard
green-against-reality and pins the interim as a regression guard. When FIXME 0406 lands
the friendly diagnostic, `/qa` retargets the same repro to assert the *friendly*
compile-time message instead of the raw linker error (the assertion that the failure
names `discover-tests` carries forward; only the channel + phrasing change). The raw
`undefined reference` is the interim; the friendly message is the destination — both are
non-zero-exit, so the `assert_failure` half is stable across the transition.

(Note: the SECOND S86 D5 repro at `tests/link.rs` — the cross-mode cache-reuse
`__cranelisp_got_<module>` drop — is a genuine backend cache defect, NOT this interim,
and its `assert_exit(0)` expectation is CORRECT. This ruling concerns only the
`discover-tests`-extern repro.)

---

## 5. The language constructs

### `discover-tests`

```
discover-tests              :: (IO (Vec (Pair String (Fn [] (Option String)))))   ; current module (q-scope)
discover-tests "mod.path"   :: (IO (Vec (Pair String (Fn [] (Option String)))))   ; named module, String arg
discover-tests ["a" "b"]    :: (IO (Vec (Pair String (Fn [] (Option String)))))   ; union over a Vec of module paths
```

Returns one `(Pair name callable)` per eligible `test-*` function:

- **`name`** — the fully-qualified test name `"module/test-name"` as a `String`, for
  selection, sorting, and reporting.
- **`callable`** — a language fn value of type `(Fn [] (Option String))` that, when
  invoked, performs a **GOT-slot-indirect call** to the test (§6 — the wrapper closes
  over the test's GOT slot, not a baked code pointer), so a *redefined* test runs its
  current body. This is the freshness ruling 1 requires.

**The Pair tradeoff (accepted by the user).** A returned pair needs a product type. The
honest accounting: `primitives/Pair` does **not** exist as-built anywhere — it lives
only in `stdlib/collections/pair.cl` (`(deftype (Pair a b) (Pair [:a first :b
second]))`), is **not** in any test fixture, and is **not** seeded by bootstrap. So
`Pair` must **join the primitives bootstrap seeds** (§6 seeding delta). The alternative
(a bespoke `TestCase { name run }` carrier) was rejected in §8c on the same grounds as
this convergence's center of gravity: a richer carrier is stdlib code, and `Pair` is the
minimum product the two-field return needs.

**Overloads (q-overload, settled).** The three call shapes are **one extern
taking `(Vec String)`**, with the no-arg and single-`String` shapes as stdlib-macro
sugar normalising to the `Vec` form:

- `(discover-tests)` → sugar → `(discover-tests [<caller-module-path>])`. Codegen can
  bake the caller's module path as a literal `String` arg; "current module" needs no
  ambient runtime lookup, and this bake is **about which table to scan**, unaffected by
  the fn-value return shape (q-scope re-verified).
- `(discover-tests "user.math")` → sugar → `(discover-tests ["user.math"])`.
- `(discover-tests ["a" "b"])` → the canonical form; the extern scans each named module
  and unions the results.

`DefKind::Overloaded` (the in-language multi-sig machinery, §9) is **not** the right
mechanism here: it is built for typed user fns with in-language bodies, the three shapes
share one return type, and a host extern has no body to mangle. One extern + one
normalising arg is the minimum mechanism (Principle 6). *(Settled by the fourth
convergence.)*

**Eligibility (q-eligibility, settled).** A `test-*` fn contributes a pair only if its scheme is
exactly `(Fn [] (Option String))` — zero-arg, returning `(Option String)`. A mis-typed
`test-*` is **excluded and warned at discovery time**, so a silently-skipped test cannot
masquerade as "no failures." The wrapper's own type is `(Fn [] (Option String))`, so the
eligibility contract and the returned callable type coincide. Rejected alternatives:
registration-time rejection at `defn` (too aggressive — a legitimately-non-test
`test-`-prefixed helper would error); widening to a return-type union (heavier; changes
the authoring convention).

**Module argument.** With ordinary apply semantics there is no special builder to lower
a bare module *path*, so the argument is an ordinary value: a `String`, a `(Vec
String)`, or absent for the current module. The old bare-path import-syntax sugar
`(discover-tests user.math)` is a casualty of dropping the special builder.

### `catch-runtime-error` (protected-call combinator)

```
catch-runtime-error :: (Fn [(Fn [] a)] (Result a String))
```

The **language-level** name is `catch-runtime-error` (q-rte-name, settled). Its internal
mechanism is the Rust slot-reader `take_runtime_error()` (`panic.rs:43`), which keeps its
name — the two-layer naming is §6.

Promoted out of the test feature to a **standalone `primitives` entry** usable by any
user code and by the stdlib, and reshaped from a slot-reader into a **bracket
combinator** (ruling 2). It invokes the thunk; if the thunk left a language-level
runtime error in the runtime's thread-local error slot, it **clears the slot** and
returns `(Err message)`; otherwise it returns `(Ok result)`.

**Polymorphism — one body serves all `a`.** The scheme is `forall a. (Fn [(Fn [] a)]
(Result a String))` — a **plain forall scheme with empty `constraints`**, exactly like
the as-built `bind` primitive (`bootstrap.rs:577`, which is also higher-order, taking a
`(Fn …)` continuation and quantifying two fresh vars with no constraints). It is **not**
a constrained-fn: there are no trait bounds on `a`, so the constrained-fn
monomorphisation machinery is not engaged. Because every Cranelisp value is a uniform
i64 at the ABI, **one runtime body serves every `a`** — no per-`a` specialisation of the
intrinsic is needed; the typechecker instantiates the forall at each call site as it
does for `bind`.

**Purity / typing (q-rte-purity).** The user's sketch matches directly on the result
with no IO unwrap, so the combinator **types pure** (`Fn`, not `IO`). This is sound
because the bracket is **self-contained and observationally deterministic relative to
its thunk**: it reads the error slot only to *consume* the error its own thunk produced,
clears it, and returns it as a value — slot state after the call equals slot state
before, unless the thunk panicked, in which case the combinator captures-and-clears so
the panic does not escape as ambient state. There is no observable side effect on the
caller's world beyond running the thunk the caller handed it. *(Purity note: `a` may
instantiate to `(IO x)` — the bracket then covers only the pure CONSTRUCTION of the IO
value; the effects run later, outside the bracket. Effects escaping by construction is a
property, not a problem; test fns are `(Fn [] (Option String))`, so this is moot for the
runner.)*

**Lenient/Par soundness — the fork-join ferry obligation (q-rte-purity, ANSWERED).**
The error slot is a `thread_local!` (`panic.rs:11`). Lenient evaluation is **LIVE**:
`compile_let` routes sparkable lets through `compile_let_lenient`
(`control_flow.rs:34/55/122`), which sparks pure work onto rayon workers via IVars
(`cranelisp_ivar_spark` → `rayon::spawn`, `ivar.rs:84`). Par branches likewise run on
rayon workers (`io.rs:406`). So a pure thunk's body genuinely **can** fork work onto
worker threads whose panics land in a *different* thread-local slot than the one the
combinator reads. (The doc's previous claim that lenient `let` "does not move work
off-thread" was WRONG and is struck.)

*Pre-S76, no fork-join boundary ferried the error slot — a pre-existing defect (§2),
since fixed: both join paths ferry as of S76 (BC §4b invariant 13, closed).* At the time
of the design pass, `ivar_spark`/`ivar_force` (`ivar.rs:84/115/137`) and
`dispatch_par_branches_with_trace` (`io.rs:405–484`, the rayon map at :456–473) both ran
the work item and returned a bare `i64` with **no `take_runtime_error()` check on the
worker** — so a panic in a sparked binding or a Par branch set the worker's slot,
returned sentinel `0`, and the join collected `0` with no slot check: the error was
silently swallowed on the caller's thread and the worker's slot left polluted. This
violated spec §12.4.3 (lenient evaluation MUST be observationally equivalent to
sequential — "the non-determinism in evaluation order is not observable"; sequential
would panic the whole expression, parallel silently yielded a sentinel). **Resolved in
S76 by landing the ferry on both join paths** (BC §4b invariant 13); the only residual is
the Par-boundary e2e witness, gated on the S85 0367 wiring (FIXME 0398).

*The obligation that makes `catch-runtime-error` sound.* Every fork-join boundary MUST
ferry the slot:

- **worker-side** — after running a work item, `take_runtime_error()` on the worker and
  return `(result, Option<err>)`.
- **join-side** — the **first** error (first-error-wins matches sequential semantics
  where the first panic aborts; aggregation rejected) is re-raised into the **joining**
  thread's slot via `set_runtime_error`, and the joined expression yields the sentinel.

*Soundness argument.* Both parallelism forms are **structured** fork-join — §12.4.3 pure
lets and §10.12 Par both guarantee the expression does not return until all branches
complete. So every spark joins back **inside the dynamic extent** of any enclosing
`catch-runtime-error` bracket. With ferrying in place, by the time control returns to the
combinator's synchronous frame any worker error has already been re-raised into the
combinator's own slot — so the bracket observes it correctly with **zero combinator
special-casing**. The combinator stays a plain intrinsic reading its own thread's slot;
the ferry lives entirely in the join paths (intrinsics-owned, §6), not in the combinator.

**What it captures.** Language-level runtime errors the compiler lowers to a
`runtime/panic` call (`cranelisp-intrinsics::panic::runtime_panic`): **match
non-exhaustion** (the canonical case), division by zero, vec out-of-bounds — anywhere
the backend emits a panic call. The mechanism: `runtime_panic` stores the message in the
thread-local and the JIT fn returns the sentinel `0`; the combinator reads the slot
after its synchronous call.

**What it CANNOT capture (state honestly).** Hard signals — `SIGSEGV`, `SIGBUS`,
`SIGILL`, `SIGFPE` — are **not** captured. The thread-local is set only by an explicit
`runtime_panic` call. Recovery from hardware traps requires the
`sigsetjmp`/`siglongjmp` signal-protection bracket that int installs **only** around
macro-clause JIT invocation (`src/expander.rs::invoke_jit_protected`). The combinator
sees what `runtime_panic` recorded; it does not see raw signals. (Signal-protected user
invocation, if ever wanted, is a *separate* host primitive — not in scope here.)

**The RC / partial-value caveat (carried forward).** When `runtime_panic` fires
mid-expression, the in-flight result is the sentinel `0` and any heap values allocated
earlier in the aborted expression are in an **indeterminate RC state** — drop glue for
the half-built value did not run. The combinator recovers the *error message* (the `Err`
payload), not a consistent heap. A `(Err msg)` outcome means "this evaluation is void; do
not trust any value it appeared to produce." This is inherent to returning control after
a panic without unwinding; it is documented, not fixed.

### Visibility, import, and shadowing

The visibility taxonomy is **binary** — a symbol is either *visible-without-import*
(special forms, e.g. `if`, recognised by the parser before resolution) or *requires
import / FQ reference*. `discover-tests` and `catch-runtime-error` are **primitives**, so
they **require import or FQ reference**: `(import [primitives [discover-tests
catch-runtime-error]])` or `(primitives/discover-tests …)`. FQ reference composes with
the S76 FIXME 0268 auto-loading work. Whether the stdlib's prelude re-exports these
names for bare-name convenience is a **stdlib packaging choice, not a language-design
question.** They **shadow like any imported name**; there is **no reserved-binder
enforcement** — `RESERVED_BINDER_NAMES` stays `["trace"]` (`ast_builder.rs:61`).

### The §4.12.3 untraceability note

A `PrimitiveExtern` entry (`discover-tests`) has no GOT slot, so a call to it has no
GOT-indirect callee to redirect — it is **structurally untraceable**, the same status as
an inline primitive. `catch-runtime-error`, published over an intrinsic (§6), is likewise
untraceable. (Note: the *callables `discover-tests` returns* ARE GOT-indirect and so
traceable — it is only the discovery/combinator entries themselves that are untraceable.)
The spec's §4.12.3 trace-exclusion list gains a line for these host-promised /
intrinsic-backed `primitives` entries.

### What retires

- **`run-test` as a separate primitive** (q2). Subsumed: running a test is *invoking a
  discovered callable*; the wrapper is the invoke capability, late-bound, and
  `catch-runtime-error` supplies protection. No language-level invoke-a-test-by-name
  primitive survives.
- **`TestResult` / `TestPass` / `TestFail`.** Results are bare `(Option String)` (the
  inner pass/fail) wrapped by the combinator's `Result` (panic vs not); the name lives in
  the discovered `Pair`; timing lives in trace's `Trace.nanos`. Nothing constructs
  `TestResult` — retire the §3.2.5 type, the §A.2 row, the §A.4 references, and the
  bootstrap seeding (`bootstrap.rs:766–844` step 8).
- **The grammar reserved-word + keyword-dispatch rows** for `discover-tests`/`run-test`
  (the names are not reserved; `trace` stays).
- **The friendly `--link` compile-time rejection.** Missing symbols are accepted;
  unresolved at link (§4.5).

---

## 6. The implementation

### Mechanism: two publication kinds, not one

The two primitives are published differently because their bodies live in different
places:

- **`discover-tests`** reads int's **live typed session state** (the per-module
  `SessionSymbolTable` + GOT) and constructs language `Pair` + closure values. Its body
  is irreducibly an int concern — `cranelisp-intrinsics` cannot name `Code` (Principle 18
  / Decision 0048). So it is a host-promised extern: kind **`DefKind::PrimitiveExtern`**
  (working name; reads alongside `DefKind::Primitive` and `DefKind::PlatformEffect`,
  `module.rs:1341/1355`), body promised by int at JIT-finalize via `Jit::define_symbol`.
- **`catch-runtime-error`** is a **self-contained intrinsic** — it invokes the closure it
  is handed, reads the existing `panic::take_runtime_error()` thread-local **(the internal
  mechanism — the slot-reader keeps its Rust name; only the language-facing combinator is
  `catch-runtime-error`)**, and constructs a `Result` heap value. It needs no live session
  and no int promise, so it is published like any intrinsic-backed primitive (below). The
  combinator logic is new Rust in `cranelisp-intrinsics`, but it is plain runtime code (no
  codegen change).

#### Calling a language fn value from an intrinsic — the load-bearing precedent

The user asked: "This does need backend support probably unless overloaded works." **It
does not need backend support.** Calling a language closure from intrinsic/runtime code
is an established as-built capability, with three precedents:

1. **IO Bind continuations** — `cranelisp-intrinsics::io::call_continuation`
   (`io.rs:351`) loads `code_ptr` from offset `CLOSURE_CODE_PTR_OFFSET` (16) of a
   continuation closure and calls `extern "C" fn(env_ptr: i64, val: i64) -> i64`,
   passing the closure pointer itself as `env_ptr`. This is the runtime invoking a
   language fn value from inside an intrinsic — exactly what the combinator needs.
2. **IVar thunks** — `cranelisp-intrinsics::ivar` (`ivar.rs:135`) loads a zero-arg
   thunk's code_ptr and calls `extern "C" fn(i64) -> i64` (env only). This is the
   *zero-arg* shape the combinator's thunk has.
3. **`run_test_by_name`** — `session_v4.rs:4778` transmutes a GOT code ptr to `extern
   "C" fn() -> i64` and calls it, bracketed by `take_runtime_error()` clear/read
   (`:4778`/`:4785`). This is *already the combinator's exact logic*, written in Rust on
   the host side — the convergence promotes it into a language-callable intrinsic.

So the combinator is a **plain intrinsic**: load `code_ptr` from the thunk closure
(offset 16), call `extern "C" fn(env_ptr) -> i64` with the closure pointer as `env_ptr`,
read-and-clear the slot, construct `Ok`/`Err`.

**Are thunks always closures?** Yes. `compile_lambda` (`control_flow.rs:679`) compiles a
literal `(fn [] …)` to a heap closure `[header(16) | code_ptr(8) | drop_glue_ptr(8) |
captures…]` with signature `extern "C" fn(env_ptr, params…) -> i64` — **even with zero
captures** (the capture list is simply empty; `payload_size(0)`; drop_glue_ptr 0). There
is no bare-fn-ptr representation for a literal lambda. A *named* fn referenced as a value
goes through `compile_fn_as_value` (`control_flow.rs:1152`), which also produces a
closure layout `[header | code_ptr | 0 | ]`. **Both cases are closures**, so the
combinator's "load code_ptr at offset 16, call with the closure as env" handles every
thunk it can receive — no normalisation needed. (The discovered test wrappers `§6` are
also closures of this shape, so the same combinator brackets them.)

#### `DefKind::PrimitiveExtern` (for `discover-tests`)

A `ModuleEntry::Def` in the `primitives` table with `kind: DefKind::PrimitiveExtern`, an
ordinary `scheme`, `got_slot: None`, `code: None`, key = ABI name (`discover-tests`).
Contract:

- **No GOT slot** — joins the slot-less classes in the `got_slot` rustdoc
  (`module.rs:725–727`).
- **The symbol-table key IS the ABI name** (`src/CLAUDE.md` §"JIT Symbol Names"); no
  separate `jit_name`. Backend lowers a call as a `Linkage::Import` against the key.
- **The publisher (int) promises the body** via `Jit::define_symbol`.

`DefKind::PlatformEffect` is the direct structural precedent: a host-promised callable
whose body lives outside `cranelisp-primitives`, registered by walking the kind
(`jit.rs:124–141`). `PrimitiveExtern` is the same shape with the body promised by int
rather than loaded from a DLL.

#### The discovery extern — building Pair + closure values

`discover_tests_extern` reads the live `TEST_RUNNER` state (`*const TestRunnerState`),
scans the per-module `SessionSymbolTable`(s) + GOT for eligible `test-*` fns (prefix +
zero-arg + non-null slot + exact `(Fn [] (Option String))` scheme, q-eligibility), and
for each builds a `(Pair name callable)`:

- **`name`** — heap `String` of the FQ name (the scan already produces `"module/name"`
  strings, `session_v4.rs:4700–4727`).
- **`callable`** — a heap closure of the discovered-wrapper shape. The closure's
  `code_ptr` points at a small **wrapper fn** whose body performs a GOT-slot-indirect
  call to the test (load the slot pointer from the module's `GotTable` at the test's
  `got_slot`, call `extern "C" fn() -> i64`, return the result). The wrapper closes over
  *the GOT slot identity* (module + slot index, or a pointer to the slot), not a baked
  code pointer — so a redefined test (whose new body the JIT writes into the same slot)
  runs through the same wrapper. This is the closure-construction machinery restored from
  §8c, grounded in the Decision 0010/0011 base-pointer ABI + embedded `drop_glue_ptr`
  closure repr: the extern allocates `[header | code_ptr=wrapper | drop_glue_ptr | slot
  captures]` via the heap-closure intrinsic, identical in layout to a `compile_lambda`
  closure, so the language sees an ordinary `(Fn [] (Option String))` value.
- The pairs are collected into a heap `(Vec …)`. For the `(Vec String)` argument the
  extern unions across named modules; for the sugar shapes the stdlib macro normalises
  before the call (§5).

The extern is more work than the names-only scan (it constructs closures, not just
strings) but it is the as-built §8c machinery, not new ground — and it is what delivers
ruling 1's freshness.

#### Publishing `catch-runtime-error` (combinator intrinsic) — the two-layer naming

**The layering, made explicit.** Two named things, deliberately distinct:

- **`catch-runtime-error`** — the **language-level** combinator. This is the
  `#[export_name]` the new C-ABI wrapper carries (language name = ABI name, per the
  JIT-symbol-name convention), the `intrinsics_table()` entry name, and the `primitives`
  symbol-table key user code imports.
- **`take_runtime_error()`** — the **internal Rust mechanism** (`panic.rs:43`), a plain
  `pub fn -> Option<String>` take-and-clear over the thread-local. It keeps its name; the
  combinator's body calls it to read-and-clear the slot. It is NOT a C-ABI export and NOT
  the language name.

**Source finding.** As built, `take_runtime_error` (`panic.rs:43`) is a **plain Rust
`pub fn -> Option<String>`** — a slot reader, not a combinator, **not** a C-ABI export,
**not** in `intrinsics_table()`. The convergence's combinator is **new Rust** layered
over it:

- Add an `extern "C"` combinator in `cranelisp-intrinsics::panic` — `#[export_name =
  "catch-runtime-error"]` (kebab-case, per the JIT-symbol-name convention) — taking the
  thunk closure pointer (`i64`) and returning the marshalled `(Result a String)` heap
  value (`i64`). Its body:
  1. clear any stale error (`take_runtime_error()` discard — the internal slot-reader);
  2. load `code_ptr` from the thunk closure (offset `CLOSURE_CODE_PTR_OFFSET` = 16) and
     call `extern "C" fn(env_ptr) -> i64` with the closure pointer as `env_ptr` (the
     `call_continuation` / `ivar` precedent);
  3. read the slot via `take_runtime_error()` (the internal slot-reader);
  4. if `Some(msg)`: marshal a `(Err msg)` — a heap ADT `[header | tag=1 | string]`,
     allocating the message via the heap-string intrinsic;
     if `None`: marshal `(Ok result)` — a heap ADT `[header | tag=0 | result]`.
     Both `Result` variants carry data, so both are heap allocations (neither is a
     nullary tag below `NULLARY_TAG_THRESHOLD`).
- Register the combinator in **`intrinsics_table()`** (`catalog.rs`) as an
  `IntrinsicEntry { name: "catch-runtime-error", ptr: …, param_count: 1, has_return:
  true, is_runtime: false }`. `Jit::new(symbol_tables)` then registers it for free via
  the existing intrinsics walk — and it resolves in **all three registration paths** (JIT
  setup, cache-hit `Linker::register_symbol`, `--link` object names) like every other
  intrinsic.
- Seed the `primitives` entry in `src/bootstrap.rs` with scheme `forall a. (Fn [(Fn []
  a)] (Result a String))` (plain forall, empty constraints — modelled on
  `register_bind_primitive`) and `kind: DefKind::Primitive`.

**Consequence: `catch-runtime-error` works in `--link` too** (unlike `discover-tests`) —
self-contained intrinsic, no live session. The combinator needs **nothing
session-side**: it calls a closure already in the linked program and constructs a heap
value, so all modes (Run / REPL / `--link`) are covered.

#### The fork-join error-slot ferry requirement (intrinsics-owned; landed S76, closed)

This is the mechanism that makes `catch-runtime-error` sound under live lenient/Par
evaluation (the soundness argument is §2 / §5). It lives on the **join paths**, NOT on
the combinator (which stays a plain slot-reader on its own thread). **It landed in S76
and is recorded closed in `bounded-contexts.md` §4b invariant 13** — both shapes below
now ferry; the description is retained as the design record of how the mechanism is
shaped:

- **Lenient-let spark/join (IVars).** `ivar_spark` (`ivar.rs:84`, `rayon::spawn` →
  `ivar_force`) and `ivar_force` (`ivar.rs:115`, calls thunk `code_ptr` at :137, stores
  bare i64) are extended so the worker calls `take_runtime_error()` after running the
  thunk and ferries any `Some(err)` back to the joining thread; the joining
  `ivar_force`/spin-wait re-raises the **first** error via `set_runtime_error` and yields
  the sentinel.
- **Par fork-join.** `dispatch_par_branches_with_trace` (`io.rs:405–484`; rayon map at
  :456–473 returns bare i64 from `run_io_trampoline`) ferries likewise: worker-side
  `take_runtime_error()` → `(result, Option<err>)`; join-side first-error re-raise via
  `set_runtime_error`.
- **Internal mechanism.** `panic.rs` carries the `set_runtime_error(msg)` companion
  to the existing `take_runtime_error()` slot-reader (the join-side re-raise primitive).
  Both are internal Rust, not C-ABI exports, not language names.

The pre-S76 as-built (neither path ferried — the pre-existing defect, §2) is now closed.
**First-error-wins** matches sequential semantics (the first panic aborts the whole
expression); aggregation is rejected. Because both forms are structured fork-join, the
ferry guarantees any worker error is back in the joining thread's slot before control
leaves the spark's dynamic extent — so an enclosing `catch-runtime-error` observes it
with zero combinator special-casing. The only residual is the Par-boundary e2e witness,
gated on the S85 0367 wiring (FIXME 0398).

#### Pair + Result seeding delta (ruling 1's accepted tradeoff + the combinator's return)

The fn-value return shape and the combinator return between them require **two ADTs that
are not currently seeded** in `primitives`:

| ADT | As-built location | Seeded in bootstrap? | Needed by | Delta |
|---|---|---|---|---|
| `Option` | `register_option_type` (`bootstrap.rs:485`, step 4) | **Yes** | wrapper return `(Option String)`; `Result` payload | none |
| `Pair`  | `stdlib/collections/pair.cl` only (`(deftype (Pair a b) (Pair […]))`); not in fixtures; not seeded | **No** | `discover-tests` pair return | **add a `register_pair_type` bootstrap step** seeding `(Pair a b)` with a single 2-field `Pair` data ctor (mirroring `register_option_type`'s shape) into the `primitives` module |
| `Result` | `stdlib/fn/result.cl` + `tests/fixtures/prelude.cl` + `tests/fixtures/preludes/test-standard.cl` (`(deftype (Result a b) (Ok [:a val]) (Err [:b err]))`); not seeded | **No** | combinator return `(Result a String)` | **add a `register_result_type` bootstrap step** seeding `(Result a b)` with `Ok`/`Err` data ctors into `primitives` |

Both new seeds follow the existing `register_option_type` pattern exactly: allocate
fresh type-var ids from `next_id`, build the `TypeDef` entry, and add per-ctor `Def {
kind: DefKind::Constructor }` entries with `forall [vars]. (Fn [field-tys] ADT)`
schemes. `Pair` has one data ctor (2 fields); `Result` has two data ctors (1 field
each). No nullary ctors are involved (contrast `Option`'s `None`), so all of `Pair`,
`Ok`, `Err` are heap-allocated — which is exactly what the discovery extern and the
combinator intrinsic construct.

Net: **Pair joins primitives (new); Result joins primitives (new); Option already
there.** The stdlib `Pair`/`Result` definitions become re-statements the prelude may
re-export for bare-name convenience (a stdlib packaging choice) or the stdlib may import
the `primitives` ones — `/stdlib`'s call, not a language question.

### Frontend — nothing (zero special-casing)

Both forms parse as plain `Expr::Apply` to an `Expr::Var`. The bespoke head-position
dispatch arms `build_discover_tests` (`ast_builder.rs:1080`) and the `run-test` half of
`build_run_or_trace_test` (:1115), plus their keyword-match rows (:1021–1022),
**delete**. The `trace` half of `build_run_or_trace_test` is preserved. No new `Expr`
variant, no reserved-word status, no reserved-binder change.

### Typecheck — nothing (zero special-casing)

The `Expr::Var` callee resolves like any symbol — found in the `primitives` symbol table,
scheme read from the entry. The combinator's higher-order forall scheme instantiates at
each call site exactly as `bind`'s does. No dedicated infer rule.

### Backend — one kind-dispatched call arm (for `PrimitiveExtern`); intrinsics for the rest

A `PrimitiveExtern` callee (`discover-tests`) adds a **kind-driven arm** emitting a
`Linkage::Import` against the entry key — identical in shape to the platform-effect /
intrinsic import path. `catch-runtime-error` needs **no new arm**: it is an ordinary
intrinsic-catalog import, resolved by the same path the existing intrinsics use. **No
codegen change for the combinator** — the closure-call is inside the intrinsic body
(Rust), not emitted CLIF. This is the direct answer to the user's "needs backend
support?": discovery needs one import arm (it already would for any PrimitiveExtern); the
combinator needs none.

**No friendly `--link` rejection.** In `--link`, a `discover-tests` call emits its
`Linkage::Import` and the missing host symbol surfaces as an unresolved-symbol link/load
error (§4.5). `catch-runtime-error` resolves normally in `--link`.

### Backend — `Jit::define_symbol` (for `discover-tests` only)

`Jit` installs a Cranelift `symbol_lookup_fn` at `Jit::new` (`jit.rs:297`) over an
internal `Mutex<HashMap<String, *const u8>>`. A new `Jit::define_symbol(name: &str, ptr:
*const u8)` inserts post-construction; the `symbol_lookup_fn` consults it at module
finalization when an unresolved `Linkage::Import` relocation is settled. This is the
additive host-symbol escape hatch (closes FIXME 0261) — no forked constructor (Principle
11), no callback indirection, no registry. (`catch-runtime-error` does NOT use this path —
it is in `intrinsics_table()`.)

### Int — bootstrap publication + the live-scan discovery extern

int's synthetic-module mount (`src/bootstrap.rs`) publishes:

- `discover-tests` with an ordinary scheme under `DefKind::PrimitiveExtern`; at session
  init int calls `Jit::define_symbol("discover-tests", discover_tests_extern as *const
  u8)`.
- `catch-runtime-error` with scheme `forall a. (Fn [(Fn [] a)] (Result a String))` under
  `DefKind::Primitive` (the body is the new combinator intrinsic — no `define_symbol`).
- the new `register_pair_type` and `register_result_type` seeds (above).

The discovery extern reads the **typed** symbol tables via int's `TestRunnerState`, scans
for eligible `test-*` entries (prefix + zero-arg + non-null GOT slot + exact `(Fn []
(Option String))` scheme), and returns a heap `(Vec (Pair String (Fn [] (Option
String))))` of name+wrapper pairs.

### Stdlib / REPL — the runner and the slash command

The in-language runner lives in `stdlib/testing/runner.cl` as **ordinary functions over
the discovered pairs** (§4.3) — `map`/`filter` over `(Vec (Pair String (Fn [] (Option
String))))`, each callable bracketed by `catch-runtime-error`, folded three-way. It is the
home of selection / iteration / reporting / tracing — **no macro is needed** (the
fn-value return makes the name→callable step unnecessary; that is the whole point of
ruling 1). The `/run-tests` slash command stays a fast Rust path or is re-pointed at the
in-language runner — int's call; not a spec concern.

### Spec — the cascade (q-cascade, FINAL; filed as FIXMEs only after green-light)

- **§2.9** — retract `discover-tests`/`run-test` from the `reserved_word` EBNF
  (`spec/02-grammar.md:911`); `trace` stays.
- **Grammar §2 keyword-dispatch rows** (`02-grammar.md:546`) — retract the two names;
  `trace` stays.
- **appendix-A §A.4** — re-type **both rows**: re-frame `discover-tests` from "special
  form, always in scope" to an import-required `primitives` entry returning `(Vec (Pair
  String (Fn [] (Option String))))`, overloaded over none/`String`/`(Vec String)`;
  re-frame the `run-test` capability as subsumed (running = invoking a discovered
  wrapper) and **add a `catch-runtime-error` row** (`forall a. (Fn [(Fn [] a)] (Result a
  String))`, import-required, all modes).
- **§4.12.3** — add the untraceability exclusion line for `PrimitiveExtern` +
  intrinsic-backed `primitives` entries (the *entries*; the discovered wrappers stay
  traceable).
- **§3.2.5 `TestResult`** — retire; §A.2 row removed.
- **`Result` + `Pair` join the `primitives` builtins documentation** — appendix-A (or
  the relevant builtin-types section) gains rows for the now-seeded `primitives/Pair` and
  `primitives/Result`, alongside the existing `primitives/Option`.
- **§16 (repl-spec)** — update the "selection and result presentation composed using the
  language" narrative to the pairs-and-combinator shape (discovery returns name+callable
  pairs; the runner folds three-way over `Result`); record the freshness property
  (late-bound wrappers) and the `--link` interim behaviour.
- **§12.4.3 (Lenient Evaluation) — NEW (fourth convergence).** The section currently
  promises "the non-determinism in evaluation order is not observable" and "Lenient
  evaluation is semantically transparent" (`spec/12-runtime.md:147/151`) but says nothing
  about how a runtime panic inside a parallelised binding propagates. Add a sentence
  pinning error propagation across fork-join boundaries so the transparency promise covers
  panics, e.g.:
  > A runtime error (§12.7) raised while evaluating any binding — whether evaluated
  > sequentially or in parallel — MUST propagate as if the bindings were evaluated
  > sequentially: the first such error aborts the whole `let` expression. An
  > implementation that evaluates bindings on separate threads MUST therefore convey a
  > worker-thread error back to the joining thread; a parallelised binding's panic MUST
  > NOT be silently discarded.
  This is the spec-side counterpart of the §6 ferry requirement; it pins as a §12.4.3
  conformance rule the property the S76 ferry now upholds (the swallowed-error defect of
  §2, since closed — BC §4b invariant 13). (The same property already
  holds structurally for §10.12 Par, which §10 may want to cross-reference, but the
  observational-equivalence claim that this sentence repairs lives in §12.4.3.)
- **FIXME 0266 stays trace-only** — it does not widen to the test names.

---

## 7. Data structures, functions & sequence

### The two entry shapes

- `discover-tests`: `ModuleEntry::Def` in `primitives`, `kind:
  DefKind::PrimitiveExtern`, ordinary `scheme` `(IO (Vec (Pair String (Fn [] (Option
  String)))))` (over its arg shapes), `got_slot: None`, `code: None`, key =
  `discover-tests`.
- `catch-runtime-error`: `ModuleEntry::Def` in `primitives`, `kind: DefKind::Primitive`,
  scheme `forall a. (Fn [(Fn [] a)] (Result a String))`, key = `catch-runtime-error`
  (matching the new intrinsic `#[export_name]`). Internal mechanism: the existing Rust
  slot-reader `take_runtime_error()` (`panic.rs:43`, keeps its name) + a new
  `set_runtime_error` companion for the fork-join ferry join-side.

Plus two new bootstrap-seeded ADTs in `primitives`: `(Pair a b)` (one 2-field data ctor)
and `(Result a b)` (`Ok`/`Err` data ctors).

### The discovery extern

`discover_tests_extern` reads the live `TEST_RUNNER` state, scans the per-module
`SessionSymbolTable`(s) + GOT for eligible `test-*` fns (prefix + zero-arg + non-null
slot + exact `(Fn [] (Option String))` scheme, q-eligibility), and assembles a heap
`(Vec (Pair String (Fn [] (Option String))))`. For each test it builds: a heap `String`
name, and a heap closure `[header | code_ptr=wrapper | drop_glue_ptr | slot-capture]`
whose wrapper does a GOT-slot-indirect call to the test (late-bound).

### The `catch-runtime-error` combinator intrinsic

The new `extern "C"` combinator (`#[export_name = "catch-runtime-error"]`, signature
`fn(thunk_closure: i64) -> i64`): clear the slot; load `code_ptr` from the thunk at offset
16 and call `extern "C" fn(env_ptr) -> i64` with the closure as `env_ptr` (the
`call_continuation`/`ivar` precedent); read the slot via the internal `take_runtime_error()`
slot-reader; marshal `Some(msg)` → `(Err msg)` heap ADT or `None` → `(Ok result)` heap ADT.
One body serves all `a` (uniform i64). The combinator itself reads only its own thread's
slot; cross-thread soundness comes from the fork-join ferry on the join paths (§6), not
from the combinator.

### The stdlib runner (end-to-end, in-language)

```clojure
;; stdlib/testing/runner.cl
(import [primitives [discover-tests catch-runtime-error]])

(defn run-one [pair]
  (match pair
    [(Pair name run)
     (match (catch-runtime-error run)
       [(Err msg)        (str-concat name " PANIC: " msg)]
       [(Ok None)        (str-concat name " ok")]
       [(Ok (Some why))  (str-concat name " FAIL: " why)])]))

(defn run-all []         (map run-one (discover-tests)))
(defn run-matching [s]   (map run-one
                              (filter (fn [p] (match p [(Pair nm _) (contains? nm s)]))
                                      (discover-tests))))
```

No macro: `discover-tests` hands back callables, so the runner is ordinary `map`/`filter`
over the pairs, fresh on every call.

### Sequence walk (the in-language runner path)

```mermaid
sequenceDiagram
    participant SRC as User code (run-all)
    participant DT as discover-tests extern (PrimitiveExtern, via define_symbol)
    participant ST as Live SessionSymbolTable + GOT
    participant TRE as catch-runtime-error combinator (intrinsic)
    participant W as Discovered wrapper closure (late-bound)
    participant T as Compiled test fn (current GOT body)

    SRC->>DT: (discover-tests)            [import-required primitives entry]
    DT->>ST: scan eligible test-* fns (prefix + (Fn [] (Option String)))
    ST-->>DT: slots + FQ names
    DT-->>SRC: (Vec (Pair name wrapper))  [wrappers late-bound through GOT]
    loop per pair
        SRC->>TRE: (catch-runtime-error wrapper)
        Note over TRE: clear slot; call closure code_ptr(env)
        TRE->>W: call wrapper()  (extern "C" fn(env)->i64)
        W->>T: GOT-slot-indirect call (current body)
        T-->>W: (Option String)  (or panic -> sentinel 0 + slot set)
        W-->>TRE: i64 result
        Note over TRE: read slot -> Ok(result) | Err(msg)
        TRE-->>SRC: (Result (Option String) String)
    end
```

Freshness lives in the **wrapper** (late-bound through the live GOT) and in
**re-calling `discover-tests`** (re-scans the current table) — not in any expansion-time
freeze (contrast §8d).

---

## 8. Appendix: superseded explorations

### 8a. The five-option analysis A–E (superseded 2026-06-05)

The options shared a framing later discarded — that the problem was choosing a
*registration edifice*: **A** `io_observer`-pattern shells (callback indirection;
REPL/`--run` only); **B** codegen-baked static discovered-set blob (stale for indirect
calls — false trace analogy; rejected); **C** late-bound per-module test registry (closed
all tensions at highest cost; superseded by the live scan); **D** recompile-on-change
(solves a non-problem; rejected); **E** `Jit::new_with_extras` (minimal fix; superseded
by `Jit::define_symbol`). Disproof worth keeping: **B's staleness** (live binding is the
right model) and that the live defect was always *symbol resolution*, never *binding
time*.

### 8b. The root-special-form layer (2026-06-05, superseded 2026-06-06 AM)

Ruled the two forms **root special forms parsed to dedicated `Expr` nodes**
(`Expr::DiscoverTests` / `Expr::RunTest`) with dedicated infer rules and reserved-word
status. Fell because it forced *both* frontend special-casing (two `Expr` variants +
builders + reserved-set widening) and typecheck special-casing (two infer rules) for two
host-promised callables, and added a third form/ADT asymmetry instance. The
PrimitiveExtern / ordinary-primitive treatment removes all of that. Kept
`Jit::define_symbol` (carried forward).

### 8c. The first-PM convergence — fn-value + pairs + `run-test`-keep (2026-06-06 AM, partially RESTORED by the third convergence)

Introduced `DefKind::PrimitiveExtern` (carried forward) and ruled the forms ordinary
import-required `primitives` entries with zero special-casing (carried forward). It
recommended `discover-tests` return **name-carrying pairs `(Pair String (Fn [] (Option
String)))`** and kept **`run-test`** reshaped to take a fn value and invoke it under
`take_runtime_error` protection. The PM (§8d) reversed both to names-only + a macro
runner; **the third convergence (current §TARGET) restores the fn-value/pairs return**
(ruling 1) — so 8c's return shape is the target again — while **subsuming `run-test`**
(running = invoking a discovered wrapper) rather than keeping it as a separate primitive,
and reshaping `take_runtime_error` from a slot-reader into the bracket combinator (ruling
2). The closure-construction analysis here (how the extern builds a `(Fn [] (Option
String))` value wrapping a GOT slot) is **refreshed and promoted into §6** as the live
design.

### 8d. The names-only / macro-runner convergence (2026-06-06 PM, superseded by the third convergence)

Drove the surface to names-only: `discover-tests` returned `(Vec String)`, `run-test`
was removed, `take_runtime_error` was a slot-reader `(Fn [] (Option String))`, and the
name→callable step moved into a **stdlib macro** that called `(discover-tests …)` at
expansion time and emitted FQ test calls — freezing the test set at the runner's
macro-expansion. `Pair` was eliminated.

**Why it fell — the one-line composability disproof (ruling 1).** Wrapping the discovery
call in a stdlib helper (the macro) freezes the test set at the *helper's* expansion
time, so any composition over the helper stops being aware of tests defined later —
"it needs to be composable." Freshness must live in the returned **values**, not in
expansion timing; a `(Vec String)` of non-callable names cannot carry freshness, so
fn-value pairs return (§8c restored) and the macro runner is retired. The
freezing-at-expansion analysis, the macro sketch, and the runtime-dispatch escape-hatch
discussion that this layer contained are not carried forward — the fn-value design makes
the name→callable step unnecessary, and the runner is ordinary in-language code (§4.3).

---

## 9. Appendix: as-built archaeology

The as-built mechanics, compressed to what still informs the design.

**Parse.** `build_list_expr` matches `"discover-tests"`/`"run-test"`
(`ast_builder.rs:1021–1022`) and dispatches to bespoke builders that emit `Expr::Apply`
to an `Expr::Var`, **not** dedicated AST nodes (contrast `build_trace` → `Expr::Trace`).
The design's "parse as ordinary apply" is the existing shape minus the head-position
recognition.

**Typecheck.** No special dispatch — `crates/cranelisp-typecheck/` has zero handling of
either name outside a unit-test assertion (`checker/tests.rs` asserts
`get("discover-tests").is_none()`, "needs import").

**Discovery scan.** `discover_test_names` (`session_v4.rs:4700–4727`) checks **name
prefix only** (`starts_with("test-")`), then `ModuleEntry::Def` + `code: Some` +
populated `got_slot` + empty `param_names` + non-null GOT slot. It does **not** check the
return type. The design tightens this to an exact scheme match (q-eligibility) and, for
each match, builds a name+wrapper `Pair` (the scan already locates the GOT slot the
wrapper closes over).

**Protected execution — the combinator's exact precedent.** `run_test_by_name`
(`session_v4.rs:4735–4811`) loads a test's code ptr from its GOT slot
(`:4750–4765` — "GOT is the single source of callable addresses; no `Code::ptr`"),
transmutes to `extern "C" fn() -> i64`, brackets the call with `take_runtime_error()`
clear (`:4778`) and read (`:4785`), and interprets the `(Option String)` result
(`:4792–4810`). **This is the combinator's logic, written in Rust on the host side.** It
installs NO signal protection — only the thread-local bracket — which is the basis of §5's
"what `take_runtime_error` cannot capture" honesty (signal protection — `catch_unwind` +
sigsetjmp — exists ONLY around macro-clause invocation,
`src/expander.rs::invoke_jit_protected`).

**Calling a closure from intrinsic code — the precedents.** `io::call_continuation`
(`io.rs:351`) loads `code_ptr` at `CLOSURE_CODE_PTR_OFFSET` (16) and calls `extern "C"
fn(env_ptr, val) -> i64`, passing the closure pointer as `env_ptr`; `ivar` (`ivar.rs:135`)
does the zero-arg `extern "C" fn(i64) -> i64` thunk call. These are the as-built proof
that an intrinsic can invoke a language fn value — so the combinator needs **no backend
support**.

**Lambda repr — always a closure.** `compile_lambda` (`control_flow.rs:679`) compiles a
literal `(fn [] …)` to a heap closure `[header(16) | code_ptr(8) | drop_glue_ptr(8) |
captures…]` with signature `extern "C" fn(env_ptr, params…) -> i64`, **even with zero
captures** (`payload_size(0)`; drop_glue_ptr 0 at :1220). A *named* fn as a value goes
through `compile_fn_as_value` (`control_flow.rs:1152`), also a closure. **There is no
bare-fn-ptr case** for either — the combinator's "load code_ptr at 16, call with closure
as env" handles every thunk.

**`take_runtime_error` as built.** `panic::take_runtime_error()` (`panic.rs:43`) is a
plain Rust `pub fn -> Option<String>`, take-and-clear over a `thread_local!`
`RUNTIME_ERROR: RefCell<Option<String>>` (`panic.rs:11`). The setter `runtime_panic`
(`panic.rs:27`) is the only C-ABI export (`#[export_name = "runtime/panic"]`), in
`intrinsics_table()`. `take_runtime_error` is **not** exported and **not** in the
catalog — hence the §6 finding that publishing the combinator needs a new C-ABI shim
(the combinator wrapper) + heap `Result` marshalling + a catalog entry.

**Polymorphic-scheme primitive precedent.** `register_bind_primitive` (`bootstrap.rs:572`)
seeds `bind` as a `Scheme { type_vars: [a, b], constraints: {} , ty: Fn([…], …) }` — a
plain forall, higher-order (its `cont` param is itself a `(Fn …)`), no constrained-fn
machinery. The combinator's `forall a. (Fn [(Fn [] a)] (Result a String))` is the same
shape; one body serves all `a`.

**Par threading.** Par branches dispatch through **rayon** (`io.rs:406`,
`use rayon::prelude::*`) onto worker threads; the error slot is `thread_local!`. This is
the basis of §5's Par-soundness boundary: a Par-internal branch panic lands on a worker's
slot, not the combinator's. The combinator runs its thunk synchronously on its own thread.

**ADT seeding.** `register_option_type` (`bootstrap.rs:485–522`, step 4) seeds `Option`
(with nullary `None` + data `Some`) into `primitives` via int's
`mount_synthetic_modules`. **`Pair` and `Result` are NOT seeded** — `Pair` exists only in
`stdlib/collections/pair.cl`, `Result` in `stdlib/fn/result.cl` + two test fixtures
(`tests/fixtures/prelude.cl`, `tests/fixtures/preludes/test-standard.cl`). Both must gain
bootstrap seeds (§6 seeding delta), each modelled on `register_option_type`.

**The JIT gap (FIXME 0261).** `Jit::new(symbol_tables)` derives the symbol set with no
extension point; the test externs are not in `intrinsics_table()`. A literal
`(discover-tests)` emits an unresolved `Linkage::Import` and fails at JIT-finalize;
`Jit::define_symbol` (§6) closes this for `discover-tests`; the intrinsic-catalog route
closes it for `catch-runtime-error`.

**Exemplar / stdlib / tests usage.** `discover-tests`/`run-test` appear in `exemplar/*.cl`
only in comments. `stdlib/testing/runner.cl` is sketch-era dormant — it becomes the home
of the new in-language runner (functions, not a macro). In `tests/`, the `/run-tests`
slash command dominates; literal forms appear at `tests/regression.rs:782` (`(run-test
"html/test-wrap-tag")` — rewrite over discovered pairs + the combinator) and
`tests/spec_12_runtime.rs:369/374` (re-target to pairs discovery + a `catch-runtime-error`
bracket). Net executable blast radius: compiler crates + bootstrap (incl. the two new ADT
seeds) + the new combinator intrinsic + spec + the stdlib runner + two test rewrites.

---

## 10. Change history

- **2026-06-05 — initial five-option analysis.** A–E registration-edifice analysis,
  E-now / C-target recommendation. (Now §8a.)
- **2026-06-05 — root-special-form convergence.** Pinned `Jit::define_symbol`, kept the
  live scan, name-stamped GOT-indirect wrapper closures, retired `run-test` into the
  wrappers, ruled the forms root special forms. (Now §8b.)
- **2026-06-06 (AM) — first PrimitiveExtern convergence.** New `DefKind::PrimitiveExtern`;
  forms become ordinary import-required `primitives` entries with zero
  frontend/typecheck special-casing; `discover-tests` returns raw test fns (recommend
  name-carrying pairs); `run-test` kept (fn-value, protected invoke); `TestResult` may
  retire. (Now §8c — its fn-value/pairs return is RESTORED by the third convergence.)
- **2026-06-06 (PM) — names-only / macro-runner convergence.** Drove the surface to
  names-only `(Vec String)`; removed `run-test`; `take_runtime_error` a slot-reader; the
  name→callable step in a stdlib macro freezing the test set at expansion. (Now §8d —
  superseded.)
- **2026-06-06 (third convergence — superseded by the fourth, below).** The user
  overturned two PM
  pillars. **Ruling 1 (composability):** wrapping the discovery call in a stdlib helper
  freezes the test set at the helper's expansion; freshness must live in the returned
  values, so `discover-tests` returns **fn-value pairs** `(Vec (Pair String (Fn []
  (Option String))))` — late-bound GOT-slot wrappers — restoring §8c's return shape and
  retiring the macro runner. `Pair` and `Result` are NOT seeded as-built (Pair: stdlib
  only; Result: stdlib + 2 fixtures) — both **join the primitives bootstrap seeds**
  (Option already seeded). **Ruling 2 (combinator):** `take_runtime_error` is reshaped
  from a slot-reader into a **protected-call combinator** `forall a. (Fn [(Fn [] a)]
  (Result a String))` — invoke the thunk, clear+capture the slot, return `Ok`/`Err`. It
  is a **plain intrinsic, no backend codegen change**: calling a language closure from
  intrinsic code is an established as-built capability (`io::call_continuation`,
  `ivar`, `run_test_by_name`); literal `(fn [] …)` thunks are always closures
  (`compile_lambda`), so one body handles every thunk; the forall scheme is a plain
  `bind`-style primitive (no constrained-fn). Purity holds (self-contained bracket on the
  calling thread); the Par/thread-local boundary is documented (a Par-internal branch
  panic lands on a rayon worker's slot, not the combinator's — that is the IO trampoline's
  boundary). `take_runtime_error` works in **all modes incl. `--link`**; `discover-tests`
  is dev-session only (no friendly `--link` rejection — interim). `run-test` is subsumed
  (running = invoking a discovered wrapper). Zero frontend + zero typecheck special-casing
  stands. The four prior layers retained as §8a–§8d.
- **2026-06-06 (fourth convergence — current §TARGET, settle-and-record).** The user
  answered every open question of the third convergence, so the design is now SETTLED and
  the open-questions list collapses to **decided rulings + one owed-implementation item**
  (§2): **q-scope** — no-arg `(discover-tests)` = the **current** module; **q-overload** —
  **ONE** extern taking `(Vec String)`, with no-arg + single-`String` as sugar normalising
  to it; **q-rte-name** — the combinator is renamed **`catch-runtime-error`** (the
  language/ABI name) while the intrinsics-internal Rust slot-reader keeps its name
  `take_runtime_error` (two-layer naming, §6); **q-eligibility** — discovery returns
  wrappers for fns matching BOTH the `test-` prefix AND the exact signature
  `(Fn [] (Option String))`; **q-cascade** — agreed and now FINAL, with one ADDED cascade
  item (spec §12.4.3 gains a sentence pinning error propagation across fork-join
  boundaries — proposed wording in §6). **q-rte-purity ANSWERED — the lenient-eval
  question.** Lenient eval is LIVE (`compile_let`→`compile_let_lenient`,
  `control_flow.rs:34/55/122`; sparks over IVars `ivar_spark`→`rayon::spawn` `ivar.rs:84`),
  so the doc's prior "lenient let does not move work off-thread" claim was WRONG and is
  struck. As-built, NEITHER fork-join boundary ferries the error slot (IVars
  `ivar_force` `ivar.rs:137`; Par `dispatch_par_branches_with_trace` `io.rs:456–473` —
  both return bare i64 with no worker-side `take_runtime_error()` check) → a worker panic
  is silently swallowed on the joining thread and pollutes the worker's slot; this is a
  PRE-EXISTING defect violating spec §12.4.3's observational-equivalence promise — **flag
  to file when actioned** (not filed from the design pass). The design obligation that
  makes `catch-runtime-error` sound: every fork-join boundary MUST ferry the slot
  (worker-side `take_runtime_error()`→`(result, Option<err>)`; join-side first-error
  re-raise via a new `set_runtime_error` companion + sentinel yield); first-error-wins
  matches sequential semantics. Because both forms are STRUCTURED fork-join (§12.4.3 +
  §10.12 — the expression does not return until all branches join), every spark joins
  back inside the dynamic extent of any enclosing `catch-runtime-error`, so with ferrying
  the combinator stays a plain own-thread slot-reader with ZERO special-casing — the
  earlier "Par-internal panic is the trampoline's boundary, leave it" position is
  superseded. The ferry is a named §6 implementation requirement on the Par/lenient join
  paths (intrinsics-owned). Everything else from the third convergence stands.
  *(Status update, not part of the dated record: the ferry obligation decided here
  **landed in S76** and is recorded **closed** in `bounded-contexts.md` §4b invariant 13
  — both join paths ferry; the §2 "pre-existing defect" is closed. The only residual is
  the Par-boundary e2e witness, gated on S85 0367 wiring, FIXME 0398. The "flag to file
  when actioned" above is satisfied.)*
- **2026-06-06 — editorial restructure preserved.** Keeps the solution-first house shape
  (overview + doc map + settled rulings; requirement → UX → constructs → implementation →
  data/sequence; appendices + change history) and updates content to the fourth
  convergence.
