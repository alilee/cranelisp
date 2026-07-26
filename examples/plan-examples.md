# Examples Plan — Learning Sequence Design

**Skill**: `/examples`
**Rebaselined**: Sprint 86 (Phase 6b)

This document describes the learning sequence in `examples/` — what each
example teaches, the design principles that govern the sequence, and how to
keep every example runnable. It is the working reference for the `/examples`
skill; the authoritative inventory is the on-disk file set itself.

> **Ring framing retired.** Earlier revisions of this plan organised
> examples by "ring" (R0 core → R4 effects), the project-wide scheduling
> axis that was retired in Sprint 64. Rings no longer appear here. Each
> example is now described by the **language capability it teaches**, not by
> a ring number. Where ordering matters it is a pedagogical dependency
> ("uses closures from 12"), not a ring gate.

## 1. Design Principles

1. **One new capability per example.** Each example introduces exactly one
   language concept and is the simplest program that makes it clear.
2. **Cumulative.** An example may use any capability taught by an earlier
   example, and nothing else. The sequence reads as a deliberate arc.
3. **Free-standing — zero stdlib dependency.** Examples MUST NOT import
   `stdlib/`. Everything they use is built from compiler primitives and
   special forms. This validates the *language*, not the library, and is a
   hard rule from the root `CLAUDE.md` §"Stdlib separation".
4. **Shared helpers live in the examples-local library, not inline.**
   Per the S115 user ruling (§2d), repeated helpers belong in
   `examples/lib/`, governed by the rule that **a definition may enter the
   library only after the example that teaches its mechanism**. The library
   is built from primitives and special forms only, so principle 3 is
   untouched. (Root `CLAUDE.md`'s "define any needed helpers inline" clause
   is being amended for `examples/` — FIXME 0823 → `/arch`. `tests/` keeps
   the inline rule.)
5. **Every example is runnable at all times.** A broken example teaches that
   the language is broken. Examples are sentinels: they catch real
   regressions by exercising the language end-to-end in compact form.
6. **Verifiable via exit code.** Every example defines `main` returning an
   Int (wrapped in `Pure`/`IO` where the IO model is in play). The return
   value is the sum of sub-test pass counts (1 per passing sub-test). A
   non-zero, *expected* exit code means every sub-test passed; a drop below
   the expected total signals a regression. The e2e guard
   `tests/examples.rs` pins each file's expected exit code.
7. **Comments explain the capability**, not the syntax — the code and its
   results teach the syntax.

## 2. The Learning Sequence (current on-disk set)

35 top-level `.cl` files plus two multi-file projects (`16-modules/`,
`37-method-import/`). Each row is the **capability taught**. Exit code is the
documented `main` return (sum of sub-test passes); it is the value
`tests/examples.rs` asserts.

| # | File | Capability taught | Exit |
|---|------|-------------------|------|
| 01 | `01-integers.cl` | Integer literals and the four arithmetic operators | 69 |
| 02 | `02-booleans.cl` | Boolean literals and comparison operators | 5 |
| 03 | `03-let-bindings.cl` | Local names with `let`; sequential and nested bindings | 97 |
| 04 | `04-functions.cl` | Named functions with `defn`; `if` as an expression | 135 |
| 05 | `05-recursion.cl` | Self-recursion and tail-call optimisation | 111 |
| 06 | `06-enums.cl` | Nullary ADTs (`deftype` enums) and `match` | 104 |
| 07 | `07-polymorphism.cl` | Let-polymorphism and type variables — **incl. one definition instantiated at three different types in one batch program** (S115 6b: the header previously asserted the opposite) | 120 |
| 08 | `08-floats.cl` | Float literals and the monomorphic `*-f64` primitives | 10 |
| 09 | `09-strings.cl` | The `String` type and string operations | 55 |
| 10 | `10-adts.cl` | Product and sum types with typed fields | 9 |
| 11 | `11-destructuring.cl` | Pattern matching that binds constructor fields | 69 |
| 12 | `12-closures.cl` | Anonymous functions (`fn`) and variable capture | 7 |
| 13 | `13-higher-order.cl` | Functions as arguments and return values; composition | 203 |
| 14 | `14-vecs.cl` | `Vec` literals and operations; vec primitives as first-class values | 81 |
| 15 | `15-traits.cl` | Trait-based operator dispatch (`Num`/`Eq`/`Ord`) + constrained polymorphism | 58 |
| 16 | `16-modules/` | Multi-file programs: `mod` (nested-child resolution), specific-name `import`, module-qualified references. **Corrected S115**: this row previously claimed `export` and `defn-`; it teaches **neither** — no numbered example uses either form (§2c.1 A4) | 47 |
| 17 | `17-display.cl` | User-defined traits and the `Display` trait | 176 |
| 18 | `18-macros.cl` | `defmacro`, quasiquote/unquote, multi-clause macros | 89 |
| 19 | `19-threading.cl` | Data pipelines with `->`, `->>` and friends | 130 |
| 20 | `20-adt-traits.cl` | Implementing traits (`Eq`, `Display`) for user ADTs | 39 |
| 21 | `21-hello-io.cl` | The IO model: `Pure`, `bind`, combinators, platform IO | 243 — **RED at HEAD, FIXME 0907** (§2f) |
| 22 | `22-io-hello.cl` | Testable IO via the `test-capture` platform | 99 |
| 23 | `23-io-sequence.cl` | IO sequencing patterns with explicit `bind` chains | 178 — **RED at HEAD, FIXME 0907** (§2f) |
| 24 | `24-io-echo.cl` | Input with `read-line`; read-then-process | 20 |
| 25 | `25-curry.cl` | Auto-currying and partial application — of a named `defn`, of a local **closure value**, and of a **trait operator** (S115 6b). First example to import the examples-local library (`operators`) | 139 |
| 26 | `26-functor.cl` | The `Functor` trait (higher-kinded `fmap`) | 91 |
| 27 | `27-lazy-seq.cl` | Lazy sequences (`take`, `filter`, `iterate`) | 183 |
| 28 | `28-parallel.cl` | Parallel evaluation: automatic sparking of independent `let` bindings (lenient eval) | 67 |
| 29 | `29-annotations.cl` | The `:Type` annotation model (capstone): constraining function typing + disambiguating expressions; `:` is a `^`-style reader macro so `: Int` == `:Int` (whitespace-tolerant) | 120 |
| 30 | `30-parallel-map-reduce.cl` | A general parallel `par-map` over a Functor: apply-argument sparking makes recursive divide-and-conquer and `fmap` of an expensive function parallelise automatically | 56 |
| 31 | `31-bitwise.cl` | Bitwise integer primitives (`bit-and`/`bit-or`/`bit-xor`/`bit-not`/`shl`/`shr`/`popcount`) as bitmask set operations; inline single-bit helpers (`bit-test`/`bit-set`/`bit-clear`/`bit-flip`) and a permission bitmask | 19 |
| 32 | `32-concurrency-combinators.cl` | Explicit-control concurrency (the CONTROL peer to 28/30's inferred half): `sleep` timer leaf, `race` (first-to-complete wins, loser cancelled), `select` (n-ary race over a Vec), and the `timeout` pattern expressed inline as `race`-against-a-deadline (stdlib `timeout` is off-limits to free-standing examples) | 6 |
| 33 | `33-redefinition.cl` | Definitions are live: a later `defn` replaces the earlier one, existing dependents rebind, and rebinding cascades transitively — **and the same three claims hold for trait `impl` blocks** (S115 6b) | 139 |
| 34 | `34-async-io-leaf.cl` | Poll-shape platform IO leaf: an async effect (`async-read`) that SUSPENDS on the host reactor and RESUMES with its result, vs. the blocking effects of 21–24; independent poll-shape leaves overlap on one reactor thread. Teaches the poll-shape leaf MECHANISM the network "server-with-no-spawn" shape is built on | 4 |
| 35 | `35-ctor-disambiguation.cl` | Same-named constructors across two in-scope types: the bare ctor name is ambiguous, the dotted `Type.Ctor` form disambiguates in VALUE position, and the dotted prefix in PATTERN position pins the scrutinee type (a cross-type dotted pattern is a compile-time type error). **Plus (S115 6b) the binder-vs-reference boundary: `.` is never part of a BINDER — rejected uniformly at all four binder positions, message quoted.** Builds on 06/10 | 100 |
| 36 | `36-multi-arity.cl` | Multi-signature `defn` dispatch (§5.1.2): ARITY dispatch (clauses differ by parameter count), TYPE dispatch (same arity, different concrete param types `:Int`/`:Blob`/`:(Vec Int)`), and the arity-overload-for-defaults idiom (a shorter clause supplies a default and delegates to a longer one). The function-level counterpart to the multi-clause `defmacro` of 18/19; distinct from currying (25). Builds on 05/06/10/14/25 | 8 |
| 37 | `37-method-import/` | Method-import dispatch (§7.11.2): to CALL a trait method you only need the METHOD in scope — the trait itself need not be imported. A submodule declares a trait `Describe` (a unary arg-dispatched `describe` and a nullary return-dispatched `blank`) with impls for two types; the entry module imports the METHODS ONLY (not the trait) and dispatches — unary by argument type, nullary by `:Type` annotation (let-binding and inline forms), same method name reaching two impls. Builds on 15/16. Multi-file. | 4 |

### Notes on specific entries

- **08-floats** — every sub-test asserts a *true* proposition (each correct
  result contributes 1), so a regression in any float op or comparison
  lowers the exit code below the expected total. (An earlier revision had a
  `test-ge` constructed to return 0 on success — a `1+…+0+…` total of 9 —
  which inverted the regression signal. Rewritten in S86 so the pass=1
  invariant holds uniformly; exit code moved 9 → 10.)
- **21 vs 22** — 21 is the full IO-model introduction (`Pure`, `bind`,
  combinators, recursion, then real `stdio` side effects). 22 deliberately
  does **not** re-teach those primitives; its single new idea is the
  *test-capture platform* — a platform that captures `print` output in
  memory, which is how the IO examples stay verifiable in CI. (S86 trimmed
  22 from a near-duplicate of 21's first parts down to this distinct
  content; exit code moved 11 → 99.)
- **29-annotations** — positioned as a **capstone**, not a feature
  introduction. `:Type` has appeared since example 04 (defn params), 10
  (deftype fields), and in every REPL result line; 29 names the single
  unifying model (`:Type` binds the immediately-following form and unifies
  its inferred type) that all those appearances share — and then shows the
  annotation doing REAL inference work via the two purposes the user called
  out (S87 rework): **constraining function typing** (pin a polymorphic body
  to a concrete type / trait instance via an annotation on a param, the
  return, or a sub-expression) and **disambiguating an expression** (a
  nullary trait method whose only type clue is its return type is ambiguous
  and rejected; the annotation selects the instance). The earlier
  annotate-a-bare-literal framing is demoted to a single "simplest form"
  line, since it does no inference work.
  - **S114 Phase 6b — whitespace tolerance + the located dangling-qualifier
    error beat.** The rule prose was corrected from the stale "binds the
    immediately-following form (no space)" to the S114 §1.4.5 truth: `:` is a
    reader macro in the manner of Clojure's `^` type hint, so **whitespace
    between `:` and the type form is permitted** — `: Int` reads identically
    to `:Int` in every position. The no-space form remains the idiom the
    example uses everywhere; a new runnable sub-test `space-form` proves the
    spaced spelling is the SAME annotation by pinning the ambiguous
    `(default)` with `: Int` (selects `Default Int` = 7 → contributes 1;
    ambiguous and non-compiling if the annotation were inert). Exit code moved
    **119 → 120** (`tests/examples.rs:151` expectation lands via /testing in
    the same phase commit). The error-cases comment block gained a "what the
    compiler tells you" beat: the empty-MODULE-half `/bar` located reject is
    quoted verbatim (stable message — "`/` here has no module name before
    it…"); the symmetric empty-LOCAL-half `foo/`/`:foo/` located-reject
    *contract* is DESCRIBED (located reject at the `/`, never a degradation to
    the module-less name) without pinning the terse string, since that wording
    is still being refined (0710 in flight).

- **30-parallel-map-reduce** — reworked (S92 Phase 6b) for the post-slice-1
  world: lenient evaluation now sparks independent, individually-expensive
  **apply-arguments**, not just `let` bindings (`design/backend/lenient-eval.md`
  §2.5; FIXME 0424 option (i) shipped). That widening is enough to make a
  fully general parallel `par-map` expressible with no per-shape workaround.
  Stage 1 is a recursive divide-and-conquer map-reduce over a `Vec` whose
  obvious form `(add-i64 (recur left) (recur right))` parallelises directly —
  the two recursive halves are independent apply-arguments, so both spark; the
  earlier `let`-lifting workaround is gone. Stage 2 defines a `Functor`
  (`Pair`) inline and shows that a general `par-map` is simply `fmap` of an
  expensive function: the `fmap` body `(Pair (func a) (func b))` has two
  independent apply-arguments, so both applications spark and run in parallel.
  The per-element leaf is a tail-recursive accumulator `work` (single tail
  self-call, gated off sparking by TCO) wrapped as an expensive identity
  `heavy`, so the only parallelism is the top-level divide-and-conquer — the
  teaching signal — and there is no internal over-spark. The A/B comments
  reference `CRANELISP_NO_LENIENT=1` (codegen escape hatch) and
  `CRANELISP_SPARK_BUDGET` (runtime in-flight cap). Exit 56 unchanged
  (`main` returns 312 = 8 × 39, cross-checked between the two stages).

- **32-concurrency-combinators** (S96 Phase 6) — the **control** peer to 28/30's
  inferred half. Teaches the S96 explicit-control combinators: `sleep` (the timer
  leaf, parks d ms then resumes with 0), `race` (first-to-complete wins, loser
  CANCELLED so the race completes in ≈ the winner's wall-clock), `select` (n-ary
  race over a **Vec** `[...]`, never a List — FIXME 0480), and the `timeout`
  PATTERN. All three are `primitives` builtins (no platform DLL, no env var).
  Free-standing: stdlib `timeout` is off-limits, so the timeout pattern is
  expressed INLINE as `(race work deadline)` where the deadline branch is built
  from `sleep` and yields a sentinel (99) on firing — exactly the stdlib
  derivation `timeout d io ≡ race io (sleep d)`, written out. Six sub-tests, each
  contributing 1 to a pass count → exit 6. Determinism: a Pure / a 50 ms branch
  always beats a 300 ms branch (6× gap; the loser is cancelled so wall-clock is
  ≈ the winner), verified exit-6-stable over 5 runs (~0.32 s each).
  - **Defect dodged by idiom (handed to /qa):** under lenient eval (default),
    `race` with an **inline `bind`-lambda argument** miscompiles —
    `(race (bind (Pure 0) (fn [_] (Pure 111))) (Pure 222))` errors with
    `failed to declare lambda function: … signature … incompatible with previous
    declaration` (a 2-param vs 1-param lambda-name collision from apply-argument
    sparking). `CRANELISP_NO_LENIENT=1` compiles it cleanly; `select` with the
    same inline shape is unaffected; lifting each `race` branch into a named
    helper avoids it. The example factors every `race`/`select` branch into a
    named helper — which is the clearer pedagogy anyway AND sidesteps the bug.
    Handoff repro in the S96 Phase-6 /examples report (for the consolidated /qa
    narrow-test pass).

- **14-vecs** (extended S101 Phase 6b) — added a "vec operations as
  ordinary values" section: `vec-get`/`vec-set`/`vec-push` each passed as a
  first-class value through a HOF (the S101 fn-as-value fix made this work;
  previously it SIGSEGV'd through NULL GOT slots — the S100 failing-guard
  defect). **Deliberate shape constraint: each generic HOF is instantiated
  with exactly ONE vec primitive** — using one generic HOF at TWO vec-trio
  instantiations SIGBUSes (open defect, FIXME 0483). Three helpers
  (`call-get`/`call-set`/`call-push`), one op each. Sub-test contributions
  8 + 40 + 4; sum moved 541 → 593, exit code moved 29 → **81** (593 mod
  256 — first example whose sum exceeds the exit-code byte).

- **33-redefinition** (S101 Phase 6b) — teaches "definitions are live": a
  later `defn` REPLACES the earlier one, existing dependents rebind, and
  rebinding cascades transitively through a dependency chain (the S101
  redefinition-machinery R3 transaction made this sound; previously the
  latent unsound hole). Batch-observable green path only — the interactive
  half of the surface (cascade `; broken:` reports, trap stubs with
  provenance, `/info` broken-status, recovery loop) is REPL-only UX owned
  by `/repl` scripts + `/docs` guide. Three sub-tests: direct call sees
  the later defn (6), dependent rebinds (18), transitive cascade (112) —
  exit **136**.

- **34-async-io-leaf** (S106 Phase 6, FIXME 0463 partial) — the first
  learning-sequence example of a **poll-shape (async) platform leaf**. Examples
  21–24 use BLOCKING platform effects (`print`/`read-line` run to completion on
  the calling turn); 34 introduces the other shape — an effect that does NOT
  block but SUSPENDS on the host reactor and RESUMES when its event is ready
  (the "server-with-no-spawn" mechanism: one reactor drives many suspended
  effects, no thread-per-connection). The leaf is `async-read` from the in-tree
  `async-demo` platform (`platforms/async-demo`, owned by `/platform`; a real
  `declare_platform!` poll-shape `PollFn`, `blocking = 0`): `(async-read N)`
  suspends ~N ms on the reactor's timer then produces N. Four sub-tests, each
  pass=1 → exit **4**: single suspend/resume, continuation-runs-after-resume,
  a data dependency threaded through two suspensions, and two INDEPENDENT leaves
  that overlap on one reactor thread (asserted on RESULT values; the wall-clock
  overlap is a runtime property covered by `tests/concurrency_reactor.rs`, not
  an exit-code check — an exit-code timing assertion would be flaky).

  - **Why a timer leaf, not a socket.** FIXME 0463 asks for the NETWORK
    accept→read→send shape. That is still **not** free-standing-expressible: no
    shared (non-exemplar) platform binds a socket, and there is no client-connect
    leaf, so a single `--run` cannot self-drive a socket without hanging (the
    S98 idle-armed-server caveat) or an external client. `async-read` is a
    self-driving **timer** poll leaf — deterministic, no external client, no
    hang — so it teaches the poll-shape leaf *mechanism* (declare / import /
    bind / reactor-drive / suspend / resume / overlap) that the network shape is
    built on, without the socket infrastructure that remains missing. The
    network-socket showcase stays exemplar-only; **0463 is NOT closed by this
    example** — it narrows to "a free-standing shared **socket** platform
    (accept/read/send + a client-connect leaf) so the network shape can
    self-drive." See §"Next skills".
  - **Why it is now feasible (changed since the S101 re-check).** The S96
    single-ABI + single-trampoline cutover (`platform-interface.md` §6.8.0)
    RETIRED the off-by-default `concurrency`/`concurrency-runtime` features: the
    host reactor + unified-ABI loader are now UNCONDITIONAL in every build, so
    the DEFAULT `--run` binary drives a poll-shape leaf (verified: the probe
    `(bind (async-read 55) (fn [r] (Pure r)))` exits 55). The `async-demo` DLL
    is built suite-wide by the nextest setup script
    (`tests/scripts/build-link-prereqs.sh`), and `tests/examples.rs` already
    sets `CRANELISP_PLATFORM_PATH=target/debug` for every example — so 34
    resolves in the harness with **no new symlink and no platform-wiring
    change**, only a new expected-exit row.
  - **Free-standing.** Uses only the `async-demo` platform DLL (a platform, not
    `stdlib/` — consistent with 21–24 using `stdio`/`test-capture`) plus
    `primitives` (`Pure`/`bind`/`add-i64`/`eq-i64`). Zero stdlib, zero exemplar
    dependency. Exit **4** verified stable over 5 consecutive `--run` invocations
    (2026-07-10) via the exact harness invocation
    (`CRANELISP_PLATFORM_PATH=target/debug ./target/debug/cranelisp --run`).

- **36-multi-arity** (S110 Phase 6b) — the first learning-sequence example of
  multi-signature `defn` dispatch (spec §5.1.2). Unblocked by the S110 C-4 fix
  (`303df28a`): an entry `main` whose body calls an overloaded fn previously
  failed `--run`/`--link` with "entry module has no `main` function" (the
  caller was generalized over the deferred overload-return var → slot-less
  `Polymorphic` `(Fn [] (IO a))` → backend correctly declined codegen). With
  the scoped re-generalize+reslot fix, that exact shape — which *every* example
  uses — now dispatches and returns cleanly, mode-uniform. The example teaches
  three facets, each verified `--run` == `--link`: ARITY dispatch (a `scale`
  with 1/2/3-arg clauses; arity dispatch takes precedence over currying —
  `(scale 5)` runs the 1-arg clause, does NOT curry the 2-arg one), TYPE
  dispatch (a `measure` with `:Int`/`:Blob`/`:(Vec Int)` clauses, same arity),
  and arity-overload-for-defaults (a `between` whose 2-arg clause defaults the
  step and delegates to its 3-arg sibling). Eight pass=1 sub-tests → exit **8**,
  stable over 5 `--run` invocations. **Prelude-surface note:** the `:(Vec Int)`
  clause annotates a parameter with the `Vec` *type*, so the example adds
  `(import [primitives [Vec]])` — the examples prelude re-exports the vec-*
  *functions* but not the type. The `measure` clauses are same-arity
  type-dispatch, so each annotates its parameter (the annotation both
  distinguishes the clause and supplies the type its body does not pin); the
  element type must be concrete because nothing else pins it (§3.11 ambiguity,
  not any clause-independence barrier — §5.1.2 back-flow now flows types
  across clauses via sibling self-calls): bare `:Vec` is rejected ("type
  argument count mismatch") and `:(Vec a)` is rejected (parameter unpinned) —
  only `:(Vec Int)` pins.

- **37-method-import** (S113 Phase 6b) — the first learning-sequence example of
  **method-import dispatch** (spec §7.11.2, settled S113 D2). Unblocked by the
  S113 W2 accept-side fix: importing a trait *method* without its *trait* now
  suffices to dispatch it (the method's fully-qualified identity names its trait's
  home module, where the impl is found by keyed lookup — "reaching the method
  reaches everything dispatch needs"). Multi-file so the trait can live in a
  *different* module (`main/traits.cl`, module `main.traits`) from the dispatch
  site: the entry `main.cl` imports the methods `describe`/`blank` and the two
  types `Shape`/`Circle` but **never** the trait `Describe`, and every call still
  dispatches. Four pass=1 sub-tests → exit **4** (verified `--run` == `--link`,
  fresh cache): unary arg-dispatch (Shape), same-method-name multi-impl dispatch
  (Circle), nullary return-dispatch driven by a let-binding `:Shape` annotation,
  and nullary return-dispatch driven by an inline `:Circle` annotation on the
  call. Teaches BOTH `:Type` annotation positions for return dispatch. Declaring
  the impls needs the trait head in scope (§7.11.2 edge (d)) — that is why the
  impls sit in `main/traits.cl` where `Describe` is declared, and the example
  comment states this. **No no-impl teaching comment** is included: the
  nullary-no-impl diagnostic currently leaks `undefined function` at codegen
  (open defect 0672, /dev), so the example teaches only impl-present behavior;
  every dispatched type has an impl. Free-standing (zero stdlib, zero exemplar):
  `primitives` only (`Pure`/`add-i64`/`eq-i64`/`mul-i64`/`Int`). Builds on 15
  (traits) + 16 (multi-file modules). Multi-file, so `tests/examples.rs` drives
  `37-method-import/main.cl` (like `16-modules/main.cl`), not a bare top-level file.

## 2f. S118 Phase-6 assessment record (2026-07-26) — two examples dark, attributed

> **Standing exception to Design Principle 5** ("every example is runnable at
> all times"). Two examples are red at HEAD and are shipped red on purpose.
> This section is the record; it stands until FIXME 0907 is ruled.

### 2f.1 The matrix — 35 of 37, all four cells agreeing

Full replay at HEAD `a1f5b2b7`: 35 top-level `.cl` files + `16-modules/` +
`37-method-import/`, each in four cells — cold `--run`, warm `--run`, cold
`--link`+execute, warm `--link`+execute. Cold = `examples/.cranelisp-cache`
removed (`--link` rejects `--no-cache`, so the cache directory is the cold
axis for the link cells; the run cells used `--no-cache` and were confirmed
identical against a removed-cache run).

**Result: 35 green at their documented exit codes in every cell.**
`21-hello-io.cl` and `23-io-sequence.cl` red in every cell. No third example
affected, no `--run`/`--link` divergence, no cold/warm divergence. This
reconciles name-for-name with the `/qa` attribution on FIXME 0907
(`examples ×1` cell = two programs).

Two harness facts worth writing down, because both cost time this pass and
neither is a defect:

- **`34-async-io-leaf.cl` requires `CRANELISP_PLATFORM_PATH=target/debug`.**
  `examples/lib/platforms/` carries committed symlinks for `stdio` and
  `test-capture` only; there is no `async-demo` symlink, so a bare
  `--run examples/34-async-io-leaf.cl` fails with `platform 'async-demo' not
  found`. `tests/examples.rs` sets the variable, so the suite is green and the
  §5 recipe below now sets it too.
- **The `--link` cells need `bash tests/scripts/build-link-prereqs.sh` first**
  (it builds the platform rlibs the `--link` path resolves by scanning
  `target/debug/`). Without it the three platform-linking examples fail inside
  `cc` with undefined Rust `std` symbols — a missing-prerequisite failure, not
  a compiler failure.

### 2f.2 What is actually dark — three sub-tests, one beat

Measured by deleting only the refusing definitions in scratch copies (never
committed):

| File | Refusing definitions | Rest of the file |
|---|---|---|
| `21-hello-io.cl` | `then`, `map-io` (Part 4) | 13 of 15 sub-tests run; exit 167; all five stdout side effects appear |
| `23-io-sequence.cl` | `map-io` (Part 4) | 7 of 8 sub-tests run; exit 136 |

Three sub-tests out of 23 carry the whole refusal, and all three are the same
beat: **a user-written combinator that takes an `(IO a)` as a parameter.**
Everything else in both files works today.

### 2f.3 Does the learning sequence survive?

**Degraded, not holed — but the damage is at the worst address in the arc.**
`21` is the *opening* file of the IO chapter and `22`, `23`, `24` all name it
in their headers. A reader walking the sequence in order meets their first
broken program exactly where effects are introduced.

Concepts with **no surviving carrier** anywhere in the sequence while 21/23
are dark:

| Lost | Why nothing else carries it |
|---|---|
| `if` selecting between two IO branches | 21 Part 3 / 23 Part 3 only; 30's `(if … (Pure a) (Pure b))` is a `main` tail, not a taught beat |
| Recursive IO construction (`sum-io`, `print-countdown`) | 32/34 bind but never recurse |
| User-written IO combinators (`then`, `map-io`) | the refused capability itself — unteachable until ruled |
| **Real console output** | `21` is the ONLY example that loads `(platform stdio)`; 22/23/24 use `test-capture`, 34 uses `async-demo`. With 21 dark, nothing in the corpus prints to a terminal |

Concepts that **survive elsewhere**: `Pure`/`bind` basics and
effect-then-pure-result (`22`), `read-line` and read-then-process (`24`),
IO-returning `defn` plus nested dependent binds (`34`), IO values passed to
the `race`/`select` primitives (`32`).

**No bridging example is being added.** The two files flip green as whole
units the day 0907 is ruled; a stand-in teaching the survivable subset would
be a second IO chapter to delete, and the lost `stdio` beat cannot be restored
without re-spelling the very combinators that refuse.

### 2f.4 Latent use of the refused shape elsewhere — none, with one caveat

Surveyed every `.cl` in `examples/` and `examples/lib/`. No other file defines
a function taking an `(IO a)` parameter, so no other example is compiling only
because it never instantiates the shape. `examples/lib/prelude.cl` re-exports
`Pure` and nothing else IO-related; the non-IO examples' `(Pure …)` wrap in
`main` is a freshly constructed value returned, which transfers rather than
releasing, and all 35 are green in all four cells.

The caveat is a **blocked next lesson, not a latent break**: `26-functor.cl`
teaches the higher-kinded `Functor` trait over `Option`, and "IO is a Functor"
is the standard follow-on. That instance is reachable — it compiles and runs
— but it **leaks** (measured ~68 bytes per call, linear over 800k iterations,
against a flat inline-`bind` control; recorded on FIXME 0907 §3). So the
natural extension of 26 must not be written until 0907 is ruled, and the
trait-method spelling must not be offered to readers as a way around the
refusal.

### 2f.5 What Sprint 118's result-owner work changed at this surface

The unified program-result owner (FIXME 0745) fixed a `--run`/`--link`
divergence where the linked stub `ireduce`d every result unconditionally, so a
non-Int program result exited with the low bits of a heap pointer. **No example
exercised that divergence** — Design Principle 6 requires every `main` to
return `(Pure <Int>)`, so the corpus has only Int results, and this is why the
link column matched the run column both before and after. Verified out of tree
that `(defn main [] (Pure "hi"))` now exits `0` under both `--run` and
`--link`. That is a real improvement and a candidate future beat ("a program
result that is not an Int is legal and exits 0"), but it is deliberately not
added: Principle 6's exit-code verification depends on an Int result, so such
an example could not verify itself.

### 2f.6 What was actioned at 6b

1. Attribution headers on `21-hello-io.cl` and `23-io-sequence.cl` naming
   FIXME 0907, the measured dark region, why no re-spelling is shipped, and
   what each file teaches again when ruled — plus an inline marker on the
   refusing Part 4 in each. Neither file's code was changed.
2. This section, and the RED annotations on rows 21 and 23 of §2.
3. §5 updated with the four-cell matrix recipe and both harness prerequisites.
4. Evidence appended to FIXME 0907 (matrix, dark-region measurement, the
   trait-instance compile-and-leak finding, learner impact, acceptance rider).
5. **FIXME 0916 filed** (`target: /qa`) — a self tail call in a `match` arm
   SIGSEGVs at ~1,000 depth when the scrutinee is a trait-method call; the
   plain-function control survives 400,000. Found while building a non-IO
   control for 0907; unrelated to IO.

`tests/examples.rs` needs **no** change: the expected exits for 21 and 23 stay
243 and 178, and they are correct again the moment 0907 is ruled. Its rows
carry no `// defect:` attribution line for 0907 today; adding one is
`/testing`'s call, recommended below.

## 2d. The examples-local library (USER RULING, 2026-07-21 — answers 0821)

> **This section supersedes §2c.1 Tier C1 and the conditional S120 row of
> §2c.5.** FIXME 0821 asked whether `examples/` gets a stdlib-exemption arc
> or is re-scoped to "the core language, free-standing". The user answered
> with a third option that neither branch anticipated.

### 2d.1 The ruling

> examples should have its own minimal library which will allow the examples
> to concentrate their attention. its library should follow from earlier
> lessons. the intent isn't to teach how to write applications — just to
> teach the core components of the language so the whole stdlib doesn't need
> to be available. just needs to be suggestive of what can be done with the
> language. to learn the stdlib, a learner would go to the stdlib docs, not
> the language examples.

Four load-bearing constraints, in the order they bind:

1. **An examples-local library** — not `stdlib/`, and not per-file inline
   re-definition. The third thing.
2. **It follows from earlier lessons.** A helper enters the library only
   *after* the example that teaches its mechanism. The library is
   **cumulative and pedagogically ordered** — its contents are a *function
   of the sequence*. This is the constraint that makes it something other
   than "a small stdlib", and it is the one that will be under pressure
   every time a later example wants a convenience.
3. **Purpose is the core language, not application-writing.** It exists so
   an example can concentrate on the construct it is about, and is
   **suggestive** of what the language can do — deliberately not complete.
4. **Learner routing is explicit.** The stdlib is learned from the stdlib
   docs; `examples/` teaches the language. Said in writing where a learner
   looks: `examples/lib/README.md`.

### 2d.2 The mechanism already existed

`examples/Cranelisp.toml` has always set `lib-dirs = ["./lib"]`, and
`examples/lib/prelude.cl` has always been on that path — **60 lines
containing zero definitions**, re-exporting ~30 primitives and nothing
else. The inline cost recorded all through §2c.4 (three separate `Num`
declarations; 19 reimplementing `->`; 20 hand-writing 250 lines of derive
output) was being paid against a library slot that was already wired and
empty. The ruling turns the pass-through into the artifact it should have
been.

**Two tiers, and the split is load-bearing:**

- **`lib/prelude.cl` — implicit, and stays definition-free.** It is loaded
  for *every* example including `01-integers.cl`. Anything defined there is
  in scope before the lesson that teaches it, which breaks constraint 2 by
  construction. It remains a name surface: `primitives` re-exports only.
- **Every other library module — explicit import, by name.** The import
  line (`(import [operators [Num +]])`) is not overhead; it is the reader's
  cue that this example is standing on an earlier lesson, and it names
  which one. It also gives the sequence a *reason* to use the module system
  before §2c.1's A4 module arc lands.

Verified live: a second module in `examples/lib/` is importable by name
from any example, resolves through the existing `lib-dirs`, and is **not**
loaded unless imported (so `15-traits.cl` keeps declaring its own `Num`
with no conflict).

### 2d.3 Contents — and the lesson that earns each

The library grows in sequence order. A row may not land before its earning
lesson exists.

| Module | Provides | Earned by | Status |
|---|---|---|---|
| `prelude.cl` | `primitives` re-exports; **no definitions, ever** | — (name surface) | shipped |
| `operators.cl` | `Num` (`+ - * /`), `Eq` (`= !=`), `Ord` (`< > <= >=`), impls for `Int`/`Float`/`Bool`/`String` | **15-traits.cl** — declares all three from scratch, in front of the reader, from `deftrait`/`impl` + the primitives of 01/08 | **shipped S115 6b** |
| `show.cl` | `Display`/`show` for the primitive types | **17-display.cl** | S116 |
| `option.cl` | `(Option a)` + `Some`/`None`, and `maybe`-style eliminators written with `match` | **10-adts.cl** (polymorphic sum types) + **11-destructuring.cl** (match binds fields) | S116 |
| `hof.cl` | `compose`, `flip`, `apply-twice` — function-shaping helpers, written as one-liners | **13-higher-order.cl** | S117 |
| `thread.cl` | `->` / `->>` | **19-threading.cl** — which builds them from raw `Sexp` constructors and is the only place that mechanism is taught | S117 |
| `seq.cl` | `map`/`filter`/`fold` over `Vec`, written by explicit recursion | **13-higher-order.cl** + **14-vecs.cl** | S117 |
| `io.cl` | a `do`-style sequencing macro over `bind` | **18-macros.cl** (defmacro/quasiquote) + **23-io-sequence.cl** (explicit `bind` chains) | S118 |

Each module's header states its earning lesson in one line. Reading a
library module must always be a **recap**, never a prerequisite.

### 2d.4 What deliberately stays out — and where the line is

The library is **suggestive, not complete**. It must not become a small
standard library, because a learner who mastered it would have learned a
vocabulary nobody uses. Excluded, on principle:

- **Anything not yet earned by an example**, however useful. This is the
  hard line and the one that will be argued with. If a helper is wanted
  before its lesson exists, the answer is to write the lesson.
- **Anything justified only by "applications need it."** No config, no
  error-formatting, no argument parsing, no logging. The ruling is explicit
  that teaching application-writing is not the intent.
- **General-purpose collection, string, and formatting breadth.** One or
  two representative operations per family is the point — enough to be
  suggestive. `Map`, `Set`, the full `count/get/conj/assoc` verb family, and
  the eighteen-primitive string surface stay out. They are stdlib topics and
  the reader is routed to the stdlib docs for them.
- **Convenience layered on convenience.** A helper must be expressible in
  terms of a *taught mechanism*, not in terms of other library helpers. Two
  levels of library-on-library and the library has started teaching itself.
- **Anything that would hide the construct an example is about.** The
  library exists to clear away what an example is *not* about. If importing
  it would remove the very thing under study, write it inline instead.

**Rule of thumb for the boundary:** if a reader would have to read the
library module to understand the example, the module is on the wrong side
of the line.

### 2d.5 How the ruling changes S116–S119

Tier C1 **dissolves as a structural exclusion**. It was framed as "the
free-standing rule permanently excludes the prelude-macro surface"; the
answer is that the surface can be *rebuilt, in miniature, from lessons* —
so the damage §2c.4 diagnosed in 19, 20, 23 and 27 is **fixable rather than
structural**:

- **19-threading** spends ~120 of 224 lines building `->`/`->>` from raw
  `Sexp`. That stays — it is the lesson. What changes is that the result
  moves *into* `lib/thread.cl` afterward, so 19 is the last file that has to
  build it and later examples can thread.
- **20-adt-traits** hand-writes 250 lines of what `derive` would generate.
  With `operators` + `show` in the library, the trait *declarations* stop
  being re-declared and 20 shrinks to what it is actually about:
  implementing traits for user ADTs.
- **23-io-sequence** opens by apologising for the absence of `do`. Once 18
  has taught `defmacro`, a `do`-style sequencing macro is earned, and 23 can
  teach the *idiom* rather than the plumbing.
- **27-lazy-seq** is 161 lines of implementing a lazy-sequence library. Same
  shape as 19, same treatment.

Revised sequencing (replaces the S120 row of §2c.5):

| Sprint | Library work | Alongside |
|---|---|---|
| **S115 6b** | seed: `lib/README.md` + `lib/operators.cl`, first consumer `25-curry.cl` | corrections + capability beats (§2c.6) |
| **S116** | `show.cl`, `option.cl`; retire the duplicate `Num` declarations in 19/20 | A1 (errors), A2 (field accessors) |
| **S117** | `hof.cl`, `seq.cl`, `thread.cl`; shrink 19 and 27 to their lessons | A4 (modules), A5 (strings) |
| **S118** | `io.cl` (`do`-style sequencing); rework 23 to the idiom | the boundaries example |
| **S119** | freeze the library; the §2c.5 reorder | reorder + renumber, with `/testing` |

**Ordering constraint that binds all of this:** every retirement of an
inline re-declaration changes a file's exit code, so each lands with a
`/testing` reconciliation FIXME. Batch them per sprint; do not dribble.

### 2d.6 What was executed at S115 6b

Seeded, not half-built. Two files, one consumer:

- **`examples/lib/README.md`** — states the purpose, the earning rule, the
  exclusion line, the prelude-vs-imported-module split, and the learner
  routing ("to learn the standard library, read the stdlib docs").
- **`examples/lib/operators.cl`** — `Num`/`Eq`/`Ord` with the impls
  `15-traits.cl` builds. Header names the earning lesson.
- **`25-curry.cl`** imports it for the trait-operator-partial beat, which is
  a beat 6b owed anyway. That makes the seed *load-bearing on day one*
  rather than speculative: the example needed `+`, and the alternative was a
  fourth inline `Num` declaration in a file about currying.

Deliberately **not** done in 6b: retrofitting 15/17/19/20 to import the
library. That is a de-duplication pass with exit-code churn across four
files and belongs in S116 with its own reconciliation batch.

## 2e. S117 Phase-6a assessment record (2026-07-25) — conformance, not invention

Sprint 117 shipped one language-facing capability that belongs in the learning
sequence: an `impl` trait **reference** may be module-qualified and resolves to
the same canonical trait identity as the bare spelling. A qualified
`deftrait` head remains invalid because that position declares a binder rather
than referring to an existing trait.

The natural teaching home is the existing multi-file trait-resolution project,
`37-method-import/`. It already establishes that method dispatch carries
fully-qualified trait identity across a module boundary. Extending that project
with a sibling implementation module can now show the declaration-side
counterpart without adding another end-of-sequence file: the sibling imports
the target type but not the trait, writes
`(impl main.traits/Describe Target ...)`, and the entry module observes the
method through its existing method-only import. The lesson stays one concept:
trait identity, rather than local spelling, controls enrollment and dispatch.

### Actual shipped impact

| S117 delivery | Impact on `examples/` | Phase-6 disposition |
|---|---|---|
| Qualified conventional and HKT trait references in `impl` heads | **Teachable positive surface.** The conventional form fits example 37's existing module/trait-identity lesson. HKT resolution is the same rule and does not justify a second beat in the already dense generic examples | Extend 37 in 6b with one conventional cross-module qualified-`impl` case |
| Canonical constrained-type display and inverse `/info` enumeration | REPL introspection/display behavior, not observable in a free-standing batch example | Route to `/repl` and `/docs`; no numbered-example change |
| Failed-turn transaction recovery and exact failing-member attribution | Interactive/session recovery and diagnostics, not a batch language construct | No numbered-example change |
| Cached-macro executable-carrier repair from W7 | **Correctness protection, not a new concept.** Examples 18 and 19 already teach macro definition, composition, and repeated expansion; cache state and the six execution permutations are compiler lifecycle details | In 6b, replay the examples in fresh and warm-cache Run/Link modes; do not teach cache internals |
| Primitive inventory, ownership evidence, and runtime-owned `Vec String` boundary | Internal boundary cleanup. Existing `split`/`join` semantics and public Cranelisp spelling did not change | No example change |
| Native `Byte` + `(Vec Byte)` + `Utf8Literal` exploration | Design-only; no type, literal, primitive, or stdlib text API shipped | Add nothing until a later implementation sprint settles and implements the normative surface |
| Deferred zero-argument-macro presentation (FIXME 0863) and partial R-2 evidence (FIXME 0859) | No shipped positive surface suitable for a runnable example | Do not reopen or encode either deferred contract |

### S117 Phase-6b action plan

1. Extend `37-method-import/` with one sibling module whose implementation
   names `main.traits/Describe` directly and does not import `Describe`.
2. Add one entry-module assertion that dispatch reaches that implementation;
   update the example's comments so the distinction between a reference in
   `impl` and the bare binder in `deftrait` is explicit.
3. Keep the change within example 37's trait-identity lesson; do not add a new
   numbered example or add a separate HKT spelling exercise.
4. Reconcile example 37's changed exit code through `/testing` in the same 6b
   change-set, per the ownership rule for `tests/examples.rs`.
5. Validate every example at its documented result under Run and Link, with
   both fresh and warm caches. This is regression evidence for W7, not an
   example of cache behavior.
6. Add no `Byte`, `Utf8Literal`, compact-Vec, code-point, grapheme, or new text
   examples; revisit the text lesson only after those facilities ship.

No new usability FIXME is warranted from this assessment. The two unshipped
surfaces are already represented by FIXME 0863 and FIXME 0859, and the
examples-owned plan already records the broader learning-sequence gaps.

### S117 Phase-6b execution result

**Attempted, then deferred behind FIXME 0869.** The planned sibling module was
implemented exactly as above. A fresh Run compiled and exited **5**, proving
that the shipped qualified-reference semantics work. The immediate warm-cache
Run then failed with:

```text
no impl of trait main.traits/Describe for type main.impls/Square
```

`/testing` reduced the result further: qualification is not causal. Both the
qualified spelling and an imported-bare sibling impl succeed fresh and
disappear on the warm-cache twin. The permanent failing-not-ignored guard is
`tests/cache.rs::cache_restores_sibling_written_trait_impls_for_dispatch`;
FIXME 0869 records the `/dev` root cause and proposed fix.

Because every checked-in example must remain runnable, example 37 was restored
to its prior four-test shape and documented exit **4**. The qualified-impl
teaching beat remains the right design but cannot ship until 0869 is fixed and
the fresh/warm Run and Link matrix passes. No `tests/examples.rs` exit change
is therefore required in Sprint 117. The generated failing cache was preserved
under `target/s117-examples-37.wcl2P9/repro-cache` for local inspection; it is
derived evidence, not part of the examples corpus.

The restored example was then verified from separate clean caches: fresh Run
**4**, warm Run **4**, fresh Link executable **4**, and warm Link executable
**4**, with `TMPDIR` and all temporary outputs under the workspace `target/`
tree and no `CRANELISP_LIB` override. Its pre-existing cache was restored after
verification.

## 2b. S115 Phase-6a assessment record (2026-07-21) — regression replay + rulings

> **Superseded in part by §2c.** The "6b plan" table that closed this section
> was written against the narrow brief (verify exit codes, verify ruling
> impact). §2c is the standing assessment against the binding `/examples`
> quality question (METHOD §2.2) and is the authority where the two conflict.
> The regression-replay record and ruling-impact table below stand as fact.

**Full replay green, BOTH modes: 37/37.** Every top-level example plus both
directory projects run at their documented exit code under `--run` *and* under
`--link`-then-run — no divergence, no drift. Binary rebuilt in full first
(`cargo build --workspace`) so no piecemeal-build skew; invoked with
`cwd=examples/` (the harness's own invocation, so `lib-dirs = ["./lib"]` is
discovered and NO `CRANELISP_LIB` is set — examples resolve their own prelude,
zero stdlib). The four concurrency/parallel examples (28/30/32/34) were
additionally run 3× each: exit-stable.

The **S114 exit-code rider (119 → 120) is DISCHARGED**: `29-annotations.cl`
measures 120 in both modes and `tests/examples.rs:153` asserts `&[120]`. The
on-disk top-level file set (35 files) matches `expected_exits()` exactly, so
the umbrella's file-set cross-check is satisfied.

### Ruling impact — verified against the tree, not assumed

| S115 ruling | Impact on `examples/` | Evidence |
|---|---|---|
| Dotted binders reject (`.` illegal in ANY binder) | **None — clean.** Every dotted name in the tree is a REFERENCE: dotted module paths in `import` (21/22/23/24/34, 37's `main.traits`), module-qualified calls (16), dotted ctor heads in VALUE position (35: `Maybe.Some`) and in PATTERN position (35: `(Maybe.Some x)` — the head is dotted, the binder `x` is bare) | full-tree grep of every `ident.ident` occurrence |
| Trait-method occurrence rule at ANY arity | **None — clean.** All 12 declared methods across 15/17/19/20/30/37 mention the implementing type (bare param, HKT `:(f a)` param, or `self` return). `37`'s `(blank [] self)` is the nullary return-`self` case | every `deftrait` body read; live probe confirms the arity-1 reject fires |
| `:Type` in a trait method's RETURN slot (latent, S116 `:`-fold) | **None — clean.** No `deftrait` in the tree carries `:` in the trailing slot. The only `:` inside a method signature is on HKT *parameters* (`(fmap [:(Fn [a] b) func :(f a) x] (f b))` in 26/30), which is the legal position | `awk` extraction of all `deftrait` forms |
| Auto-curry over a local closure works; `def`-bound route blocked (0800) | **No risk, and the blocked route is unreachable here**: `def` is a *stdlib macro* (spec §5.7 — "there is no native `def` special form") and the examples prelude does not provide it, so no free-standing example can bind a function with `def` at all. `25-curry.cl` already uses the `let` form exclusively | `(def adder (fn …))` in a free-standing probe → `undefined variable: def` |
| Impl redefinition hot-reloads | **New capability, not yet taught** — see the 6b plan | probe below |

### New capability delivered this sprint that the sequence should teach

Two, both **in-sequence extensions of an existing example**, not a new file
bolted at the end:

1. **Impl redefinition is batch-observable → extend `33-redefinition.cl`.**
   33 already teaches "definitions are live"; the S115 hot-reload ruling makes
   the *same* claim true of `impl` blocks, and 33 sits after 15/17/20, so
   traits are already in the reader's vocabulary. Verified probes (`--run` ==
   `--link`):
   - **re-impl replaces**: a second `(impl Sized Box …)` supersedes the first
     method body;
   - **omitting a method reverts it to the trait default** (`tag` omitted from
     the re-impl → the `deftrait` default body is used again);
   - **dependents rebind**: a `defn` written *before* the re-impl dispatches to
     the *new* impl — the exact liveness claim 33's existing three sub-tests
     make for plain `defn`, now shown for methods.
   A type-changing re-impl is *rejected with the prior impl intact* — that half
   is interactive-recovery UX and stays with `/repl`/`/docs`, as the batch/REPL
   split already recorded for 33.
2. **Auto-curry over a LOCAL closure → extend `25-curry.cl`.** Every current
   sub-test curries a top-level `defn`. The S115 fix makes
   `(let [g (mk 10)] ((g 1) 2))` work — currying a closure *value* — and a
   **trait-operator partial** keeps its carrier (`(let [add5 (+ 5)] (add5 3))`
   → 8, verified). 25 builds on 12 (closures) and 13 (HOFs), so both beats are
   cumulative-legal exactly where they belong. Keep captures scalar (FIXME 0796:
   auto-curried partials reach the 0760 capture-stranding seam for heap captures
   — an Int capture is unaffected).

### 6b plan

| # | Item | File | Exit impact |
|---|---|---|---|
| 1 | Impl-redefinition section: re-impl replaces / omitted method reverts to trait default / dependent rebinds | `33-redefinition.cl` | 136 → +3 sub-tests (needs a trait with a default method — see item 3) |
| 2 | Curry-a-local-closure + trait-operator-partial sub-tests | `25-curry.cl` | 118 → +2 |
| 3 | Trait **default methods** (§7.1.5) — currently taught by NO example, though 15's `Ord` is the spec's own worked default-method example. Introduce as one beat in `15-traits.cl` (`<=`/`>=` synthesized from `<`/`>`), which item 1 then relies on | `15-traits.cl` | 58 → +1..2 |
| 4 | Dotted-binder rejection as a teaching beat: `.` is for type/trait qualification ONLY. `35-ctor-disambiguation.cl` is the sequence's dotted-name teacher, so the comment beat belongs there (comment-only, quoting the now-stable located message: "`'a.b' is a dotted name, but a binder must be a bare (unqualified) name — write 'b' ('.' is reserved for type/trait qualification)`") — uniform across all four binder positions (defn head, param, `let`, `match`) | `35-ctor-disambiguation.cl` | none |
| 5 | §4 spec-feature-coverage table: add rows for trait default methods, impl redefinition, and the dotted-binder/binder-vs-reference boundary | this file | — |
| 6 | Exit-code reconciliation FIXME to `/testing` for items 1–3 (one FIXME, all rows together), filed **with** the 6b change-set, in the same phase commit — `/examples` does not edit `tests/` | — | — |

Ordering: 3 → 1 → 2 → 4 → 5 → 6 (item 1's "reverts to the default" beat reads
as a payoff only once defaults have been introduced).

### Gap FIXMEs filed at 6a

- **0820 → /testing** — `examples/16-modules/main.cl` has no e2e row. The
  umbrella covers only top-level `*.cl`; `37-method-import/` got its own
  directory-project test at S113, 16 never did. The stated reason for not
  coupling to it (`tests/examples.rs:276` — "not yet relaid out to the nested
  shape") is **false at HEAD**: `16-modules/main.cl` + `main/math.cl` +
  `main/shapes.cl` IS the nested §8.2.5 shape. Ask: one row, exit **47**,
  modelled on the 37 test; verified both modes at 6a.

### Not defects

No example failed, in either mode, so no defect handoff is owed this phase.
Two housekeeping observations, neither actionable: (a) `examples/.cranelisp-cache/`
carries residue from other agents' probes (`_probe_sp.o`) and a stray stdlib-named
`control.o` — gitignored derived state, and `CRANELISP_MODULE_TRACE=1` confirms a
current example run resolves NO stdlib module, so free-standing isolation holds;
(b) FIXME 0463 (network poll shape) remains blocked on the same unmet
dependency, re-verified — no free-standing socket platform exists.

## 2c. STANDING ASSESSMENT (opened S115 Phase 6a, 2026-07-21)

> **This section is the durable one.** It answers the binding `/examples`
> quality question (METHOD §2.2): *is `examples/` a comprehensive learning
> sequence, and the best way to learn the full language and its nuances by
> reading code?* That question is never finished. Every `/examples` successor
> re-asks it **against the whole sequence**, not this sprint's delta, and
> updates the tiers below. "It compiles and exits N" is the floor, not the
> content.
>
> Method: worked **outside-in from `spec/` and `stdlib/`**, not from the
> example list. Every "buildable today" claim below was verified by a live
> free-standing probe (`cwd=examples/`, no `CRANELISP_LIB` — setting it breaks
> free-standing resolution; invoke exactly as `tests/examples.rs` does).

### 2c.0 Verdict, in one line

**No.** `examples/` is a *sound* sequence — 37/37 green in both modes, nothing
in it is wrong about what it demonstrates — but it is **not comprehensive**,
and it is not yet the best way to learn the language by reading code. Three
structural reasons, in order of severity:

1. **Whole first-order features are unteachable from it.** A reader who
   finishes example 37 has never seen an error handled, a field read without
   `match`, a private definition, a re-export, a glob import, a trait default
   method, or twelve of the eighteen string primitives.
2. **Examples 21–37 are an append log, not a sequence.** 01–20 were designed;
   everything after is ordered by the sprint that produced it.
3. **Boundaries are taught only as prose, in 5 files of 37, and never as a
   class.** A learner reading only happy paths learns a language that does not
   exist — and in four places the prose is now *wrong*, so they learn a
   language that never existed.

The gap is **several sprints of work**, sequenced in §2c.5. It does not
compress into a 6b bullet list, and §2c.6 deliberately keeps 6b small.

### 2c.1 Axis 1 — Coverage: what a reader cannot learn from the sequence

Ranked by how central the missing thing is to writing ordinary Cranelisp.
"Buildable" = verified by probe at HEAD, free-standing, this assessment.

#### Tier A — central; a reader is actively blocked or actively misled

| # | Gap | Spec | Buildable today? | Evidence |
|---|---|---|---|---|
| A1 | **The entire error model.** Runtime panics; the four panic sources (match non-exhaustion, div-by-zero, vec OOB, stack overflow); `catch-runtime-error` and its `Result`/`Ok`/`Err`; the temporal-bracket rule (effect-run-time panics are *not* catchable); the "no `throw` — encode errors in the type system" doctrine; wrapping-vs-checked arithmetic; float `Inf`/`NaN`. The word "panic" appears in **zero** example files. | §12.7, §12.7.2.1–2, §12.7.3, §12.7.7, App A.3 | **YES** — probe: `catch-runtime-error` over `(div-i64 1 0)` → `(Err …)`, exit 31; over `(vec-get [1 2 3] 9)` + div-by-zero → exit 2. Needs only `(import [primitives [catch-runtime-error Result Ok Err]])`, zero stdlib | live probe |
| A2 | **Generated field accessors `Type.field`.** `10-adts.cl` states, verbatim, *"Field access requires pattern matching (next example)"* — **false** since §5.2.6. Every example in the corpus reads a single field with a full `match`, which is not the idiomatic form. This is not one missing example; it is a **non-idiomatic style running through ~10 files**. | §5.2.6, §8.5.2 | **YES** — probe: `(Point.x (Point 3 4))` → 3 | live probe |
| A3 | **Trait default methods.** `15-traits.cl` hand-writes all four `Ord` methods — and `Ord`-with-defaults is the spec's **own worked example** of §7.1.5. The example even comments *"Each method has an explicit implementation."* Also the [NEG] half: defaults are forbidden on higher-kinded traits. | §7.1.5 | **YES** — probe: `(gte [a b] Bool (not (lt a b)))` default synthesized for an impl providing only `lt`, exit 41 | live probe |
| A4 | **Module visibility and the import/export surface.** `16-modules/` teaches exactly three things: `mod`, specific-name `import`, module-qualified call. Untaught: `defn-`/`deftype-`/`deftrait-`/`defmacro-`/`mod-` private forms; the private-import rejection; `export` and re-export; glob import `[*]`; member glob; alias import; renamed import; alias-only; null import; `super`; multiple-module import; §8.6 shadowing/conflict/ambiguity rules. **`export` occurs in no numbered example** (only in `lib/prelude.cl`). §2's row for 16 claims it teaches `export` and `defn-` — it teaches **neither**. | §8.3.2–8.3.9, §8.4, §8.6, §8.7 | **YES** — probes: `defn-` private + call-through works (42); importing the private name is rejected with a good located message (*"'helper' is not public in 'main.util'"*); `[*]` glob works (42); `(export [main.util [pub-double]])` re-export works (42) | live probes |
| A5 | **The string/text surface.** `09-strings.cl` teaches 6 primitives; `primitives` exposes 18. Untaught: `parse-int`, `substring`, `split`, `join`, `replace`, `trim`, `starts-with?`, `ends-with?`, `contains?`, `to-upper`, `to-lower`, and `char-at` (re-exported by the examples prelude but **never called**). `parse-int` returning `Option` is also the canonical fallible-input idiom (App B.4) and has no analogue anywhere. | App A.3, §12.1.2 | **YES** — probe: `substring`/`trim`/`to-upper`/`starts-with?` free-standing, exit 11 | live probe |

#### Tier B — important facets of features already present

| # | Gap | Spec | Buildable? |
|---|---|---|---|
| B1 | **Pattern-matching's negative space.** §6.6 forbids nested patterns, literal patterns, or-patterns, and guards — four things a reader arriving from Rust/Haskell/Clojure will *try first*. None is named in any example. Exhaustiveness checking is also untaught (and is a **compile-time** reject, not a panic — a teachable boundary in itself: probe shows `missing constructor(s) B` at typecheck) | §6.5, §6.6 | comment-only + one compile-reject beat |
| B2 | **Let-polymorphism at two instantiations.** `07-polymorphism.cl` — the example *named* polymorphism — never instantiates one function at two types, and asserts *"In batch mode, each polymorphic function is used at one concrete type per program."* **That is false**: probe uses `id` at both `Int` and `Bool` in one batch program, exit 5. The example teaches the opposite of the feature it names. | §3, §5.1.1 | **YES** — probe |
| B3 | **Macro hygiene / auto-gensym.** `18-macros.cl`'s `with-double` binds `doubled` and the *caller* refers to it — an anaphoric, capture-dependent macro presented with no comment, as if it were ordinary. §9.8 auto-gensym is untaught. The sequence currently teaches the trap as the technique. | §9.8 | YES |
| B4 | Byte-length vs char-length (`str-len` is bytes; no multibyte string appears anywhere in the corpus) | §12.1.2 | YES |
| B5 | Strict evaluation + observable left-to-right order — never *named*, even though 27 (laziness) and 28/30 (leniency) are both defined as contrasts against it | §12.4.1 | YES (prose beat) |
| B6 | Detached strands / launch-and-continue / supervision — the whole "server lives" half of the concurrency model. Zero coverage | §10.12.7, §12.7.9 | needs check |
| B7 | **Docstrings — zero coverage in all six positions** (`defn`, `deftype`, constructor, `deftrait`, trait method, `defmacro`). Not one string literal follows a definition head anywhere in the corpus, though the spec's own trait and type examples carry them | §5.2.5, §5.12, §7.1.2, §9.2.4 | YES |
| B7a | **The reader surface below the top level: zero coverage.** No string escape ever appears (`\n`, `\t`, `\\`, `\"` — there is not one backslash in 4432 lines); comma-as-whitespace; the single-`;` comment form; `?`/`!` in symbols; the quote reader macro `'form`; `#(…)` with `%`/`%1`–`%9`; the `x#` auto-gensym spelling | §1.2–1.5 | YES |
| B7b | **`trace` and the `Trace`/`TraceCall` ADT: zero coverage** — a user-facing special form with reserved-word rules, an ADT with accessors, and a nesting [NEG], taught nowhere | §2.3, §12.9.5, App A.4 | needs check |
| B8 | Sexp/macro surface beyond the basics: `~@` is *used* in 19 and never *explained*; nested quasiquote depth; `begin` multi-form expansion; bare-symbol (zero-arg) macros; bracket-destructuring macro params; the SList helpers (`sfold`/`sreverse`/`sempty?`/`shead`/`stail`); `quote-sexp` | §9.2.7, §9.5, §9.6, §9.7, §9.11 | YES |
| B9 | `const`; definition ordering + mutual forward references (§5.13) — the sequence relies on forward refs constantly and never states the rule | §5.6, §5.13 | YES |
| B10 | Operators as first-class values (§7.6); explicit trait constraints (§7.8.2) | §7.6, §7.8.2 | YES / partial |
| B11 | Constrained-impl heads `(impl Display (Option :Display a) …)` | §7.3.3 | **BLOCKED** — pre-existing wrong-reject on HEAD (S112 TB-24, owner `/dev` typecheck) |

#### Tier C — structurally excluded; needs a ruling, not an example

> **C1 IS ANSWERED AND DISSOLVED — see §2d.** The user ruled (2026-07-21)
> that `examples/` gets **its own minimal, lesson-derived library**: neither
> a stdlib exemption nor a bare re-scoping, but a third artifact whose
> contents are a function of the sequence. The exclusion below is therefore
> **not permanent** — the prelude vocabulary can be rebuilt in miniature
> from taught mechanisms — and the damage it caused in 19/20/23/27 is
> fixable rather than structural. The diagnosis below stands as the record
> of *why* the ruling was needed; the disposition is §2d, not the S120 row.

**C1 was the single biggest structural finding of this assessment.**

**C1 — the free-standing rule permanently excludes the surface a real user
writes.** Root `CLAUDE.md` §"Stdlib separation" forbids `examples/` from
depending on `stdlib/`. But `do`, `bind!`, `pure`, `->`, `->>`, `cond`, `case`,
`when`, `unless`, `str`, `def`, `def-`, `const`, `list`, `vec`, `show`,
`Option`/`Result` on the prelude surface, `List`, and **`derive`** are all
*stdlib* macros/modules. Probe: `(derive [Eq] (deftype Color …))` →
`undefined variable: derive`. Consequences visible in the corpus today:

- `19-threading.cl` spends ~120 of its 224 lines **reimplementing `->` and
  `->>` from raw `Sexp` constructors** before it can teach pipelines. It is a
  macro-metaprogramming example wearing a threading example's title.
- `23-io-sequence.cl` opens by apologising: *"Without a `do` macro (which
  lives in the standard library), we build sequences using explicit bind
  calls."* Every IO example teaches the plumbing, never the idiom.
- `20-adt-traits.cl` says *"these are the patterns that a derive macro would
  automate"* — then hand-writes 250 lines of them.
- Appendix B's thirteen worked examples are **all** written in the prelude
  vocabulary. The learning sequence shares a vocabulary with none of them.

So `examples/` cannot, under the current rule, be "the best way to learn the
full language". It can be the best way to learn the **core language**. That is
a legitimate and valuable thing to be — but it must be a **decision**, not an
accident, and the reader must be told which one they are reading. Filed as
**FIXME 0821 → /arch** (question, not a change request): does a designated
late-sequence arc get a stdlib exemption, or does the prelude-macro surface
belong wholly to `/docs` + `/port` (exemplar) with `examples/` explicitly
re-scoped to "the core language, free-standing"? `/examples` does not rule
this; it is a cross-skill scope boundary. **Answered 2026-07-21 — §2d.**

**C2** — network poll-shape leaf (FIXME 0463): blocked, unchanged, re-verified.
**C3** — collection idiom (`List`, `Map`, `Set`, the `count/get/conj/assoc`
verb family): same exclusion as C1.

### 2c.2 Axis 2 — Order and progression

**Verdict: examples 01–20 are a designed sequence; 21–37 are an append log.**

01–20 genuinely build — 11 needs 10, 13 needs 12, 17 needs 15, 20 needs 17.
Each earns its position. From 21 on, position is *chronological by sprint*:
31-bitwise depends on nothing after 02; 33-redefinition depends on nothing
after 05; 25/26/27 are pure-language topics stranded **inside** the IO arc
(21–24 … then 28/30/32/34 resume it). A reader cannot tell that 31 is easier
than 27, because nothing in the numbering says so.

Specific ordering defects, worst first:

1. **29-annotations is a capstone whose content is a prerequisite.** It is
   positioned at 29 and framed as "naming a model you have already seen". But
   `11-destructuring.cl` (position **11**) already *needs* `:(Option Int)` to
   disambiguate a bare `None` and explains §3.11.1 ambiguity inline; 26, 35,
   36, and 37 all depend on annotation-driven disambiguation. The capstone
   framing is right; the placement means five earlier examples teach fragments
   of it ad hoc. Split: a short "annotations pin types" beat right after 10
   (where `:Int` fields first appear), keeping 29 as the capstone that shows
   annotations doing *inference work*.
2. **15 and 17 overlap on the declaration half.** 15 is titled "trait-based
   operator dispatch" but *declares* `Num`/`Eq`/`Ord` from scratch; 17 is
   titled "user-defined traits" and declares `Display`. The reader meets
   `deftrait` twice with no acknowledgement. 19 declares `Num` a **third**
   time. (Free-standing forces re-declaration — but the comments should say so.)
3. **The tail should be re-grouped, not re-appended.** A defensible grouping:
   core (01–14) → traits (15,17,20) → modules (16, +A4) → macros (18,19) →
   functions-as-data (12,13,25,26,27) → IO (21–24,34) → concurrency
   (28,30,32) → language mechanics (29,33,35,36,37) → errors (A1).
4. **Renumbering is a breaking change.** `tests/examples.rs` pins the file set
   by name. Any reorder is its own phase, co-planned with `/testing`; it must
   not ride along with content work. Sequenced as S119 in §2c.5.

### 2c.3 Axis 3 — Nuance and negative space

**Verdict: the sequence teaches boundaries incidentally, never as a class —
and four of its boundary claims are now factually wrong.**

Boundary teaching exists in exactly **5 of 37 files**: 11 (§3.11.1 concreteness),
29 (a real "error cases / what the compiler tells you" block — *the best
boundary writing in the corpus*), 35 (cross-type dotted pattern is a type
error), 36 (bare `:Vec` and `:(Vec a)` rejected, only `:(Vec Int)` pins), and
32 (a defect dodged by idiom). Everywhere else the reader sees only happy paths.

Three structural problems:

1. **No example's *subject* is the boundary.** There is no "what the compiler
   rejects and why" example. Rejections are footnotes to positive examples.
2. **A runnable example cannot type-error**, so compile-time boundaries can
   only ever be *comments* — inert, unverified, and free to rot (see the four
   below). But **runtime** boundaries *can* be made observable, via
   `catch-runtime-error` (A1). That is the mechanism the sequence is missing,
   and it converts a whole class of prose into runnable, regression-guarded
   teaching. This is the strongest single argument for A1.
3. **Comment-only boundaries have already rotted.** **Six** wrong claims found
   — all six in prose a reader has no way to check:
   - `07-polymorphism.cl`: *"each polymorphic function is used at one concrete
     type per program"* — **false** (probe, exit 5).
   - `10-adts.cl`: *"Field access requires pattern matching"* — **false** since
     §5.2.6 accessors (probe).
   - `14-vecs.cl`: *"The same generic higher-order function can be instantiated
     at several different vec primitives"* — this **SIGBUSes** (open defect
     FIXME 0483). The comment invites the exact shape the code below it
     carefully avoids, and §"Notes on specific entries" records the avoidance.
     The comment is actively dangerous.
   - `32-concurrency-combinators.cl:118-119`: *"the empty `select []` never
     completes"* — **contradicts §10.12.8 at HEAD**, which pins a **fatal,
     non-catchable runtime raise** and states in terms that a hang is
     *non-conforming* ("a guaranteed deadlock is worse than a clean fault").
     The example teaches the behaviour the spec explicitly rejected.
   - `Cranelisp.toml`: *"lib-dirs fully replaces the env and default tiers when
     present, so this config isolates examples from `{project_root}/stdlib/`"*
     — **contradicts §8.11.4** (settled S91): the lib-dir set is an **additive
     union**; no source replaces or suppresses another. The isolation
     *guarantee* still holds, but for a different reason (project root is
     `examples/`, and `examples/stdlib/` does not exist) — the stated mechanism
     is wrong. This also explains the standing operational note that setting
     `CRANELISP_LIB` breaks free-standing examples: under union semantics it
     *adds* the real stdlib rather than being overridden by the toml.
   - Six files (`01`, `02`, `06`, `08`, `09`, `10`) — and `lib/prelude.cl` —
     still frame primitives as *"Ring 0"/"Ring 1"*, an axis retired in
     **Sprint 64**. This plan's own §2 preamble declares ring framing removed;
     it was removed from the plan, not from the examples.

   Filed as **FIXME 0822 → /examples** (self-targeted tracking row; the fixes
   land in 6b, see §2c.6).

   The lesson generalises past these six: **every boundary the sequence teaches
   only in a comment is unverified and will rot.** That is the second argument
   for A1 — a boundary expressed as a `catch-runtime-error` sub-test is
   regression-guarded by the same exit code that guards everything else.

This sprint's rulings supply three further boundaries worth teaching, all
comment-grade: dotted names qualify types/traits and are **never** binders; a
trait method must mention its implementing type at **any** arity; a `defn`'s
trailing `:Int` annotates a **body** while a method signature's trailing
element **is** a return type (the trap that fooled our own corpus for months —
and precisely the kind of thing that belongs in a boundaries example, not a
footnote).

### 2c.4 Axis 4 — The code as reading material

**Verdict: the corpus reads as a test suite that happens to teach, not as
prose that happens to compile.** One artefact dominates: the `main`
accumulator.

**The systemic problem — `main` is written for the harness, not the reader.**
Every example ends in a right-nested `add-i64` staircase. In `15-traits.cl` it
is **30 levels deep**, indented off the right margin; in `20-adt-traits.cl`,
22 levels. This is the last thing a reader sees in every file, and it teaches
nothing. It also breaks the plan's own §1.5 invariant three ways:

- **The stated invariant is "1 per passing sub-test".** Only 08, 31, 33, 36
  and 37 actually honour it. Most examples sum *values*, so the exit code is a
  **checksum**, not a pass count.
- **Sub-tests that contribute 0 on success.** 02's `test-ge` is `(ge-i64 4 5)`
  → 0; `20-adt-traits.cl` has **six** negative assertions each wired to
  contribute 0. The §"Notes" entry for 08-floats records this being fixed in
  S86 *for 08 only* — the same defect is still live in 02, 06, 10, 15, 18, 20.
  For 20 the signal is **inverted**: if a negative assertion silently flipped
  to true, the total would *rise*, and a rise is not checked.
- **Eight files state a total the reader can never observe.** 05 (3635055→111),
  10 (265→9), 12 (263→7), 15 (314→58), 18 (601→89), 25 (374→118), 26 (347→91),
  28 (9283→67) all wrap mod 256, unexplained. Only 14, 16 and 33 explain it —
  and 14's note claims it is *"the first example whose sum exceeds the
  exit-code byte"*, which **05** already did, twenty examples earlier.
- The 9-line `;; Wrap the sum-of-pass-counts in Pure …` comment is duplicated
  **verbatim in all 37 files**.

**Weakest examples as reading material** (not by exit code):

1. **`20-adt-traits.cl`** — 250 lines, 22 sub-tests, 22-level `main`, six
   sub-tests that pass by contributing 0, a hand-written listing of the exit
   arithmetic, and a header that names `derive` as the thing this all replaces
   without being able to show it. Worst in the corpus.
2. **`15-traits.cl`** — 270 lines, 30-level `main`, redeclares three traits
   that 19 redeclares again, and hand-writes the spec's own default-method
   showcase *with the defaults expanded out* and a comment asserting that is
   how it must be.
3. **`19-threading.cl`** — the title promises pipelines; over half the file is
   a from-scratch `->`/`->>` implementation in raw `Sexp` constructors, plus a
   third copy of `Num`. Its own header comment contains a worked example
   annotated *"NOTE: this is wrong for str-concat"* — teaching material that
   flags itself as wrong and leaves it in.
4. **`07-polymorphism.cl`** — states a falsehood, and never demonstrates the
   feature it is named for.
5. **`27-lazy-seq.cl`** — good content, but it is 161 lines of *implementing* a
   lazy-sequence library; the reader learns thunked tails, not how to use lazy
   sequences. Same shape as 19. (Both are consequences of C1.)

**Best examples, for calibration** — `29-annotations.cl` (a real model, real
inference work, and a genuine boundary section), `33-redefinition.cl` (68
lines, three sub-tests, honest pass-count exit, prose that argues), and
`37-method-import.cl` (states the rule as a slogan — *"Declaration reaches the
TRAIT; dispatch reaches the METHOD"* — then proves it four ways). These three
are the house style the rest should be brought to.

### 2c.5 What "comprehensive" would require — sequenced, honestly

Closing this is **four to five sprints** of `/examples` phase-6 work. It does
not fit in one 6b. Sequenced so each sprint is independently shippable and
green:

| Sprint | Scope | Size | Why here |
|---|---|---|---|
| **S115 6b** | §2c.6 — the in-flight capability beats (defaults, impl-redefinition, curry-a-closure) **plus the four factual corrections + ring-framing purge**. No new files. | small | The corrections are cheap, and a corpus that states falsehoods should not survive a sprint once they are known |
| **S116** | **A1 (errors)** — new example: panics, the four sources, `catch-runtime-error`, the temporal-bracket [NEG], errors-in-the-type-system. **A2 (field accessors)** — new beat + a **corpus-wide** pass converting single-field `match` reads to `Type.field` where that is the better reading. | **large** — A2 touches ~10 files and every touched file needs its exit re-verified in both modes | A1 unlocks *runnable* negative space (§2c.3), which every later boundary beat depends on. A2 is the biggest single idiom correction and gets cheaper the sooner it lands |
| **S117** | **A4 (modules)** — grow `16-modules/` into a real arc: visibility (`defn-` + the private-import reject), `export`/re-export, glob and alias import forms, §8.6 shadowing/conflict. **A5 (strings)** — extend 09 to the full primitive surface incl. `parse-int`→`Option` as the fallible-input idiom. | medium-large | Both are self-contained, both are Tier A, neither depends on S116 |
| **S118** | **The boundaries example** (§2c.3 problem 1) — an example whose *subject* is what the language rejects: §6.6's four pattern limitations, exhaustiveness-as-compile-error, the three S115 rulings, the annotation traps, ambiguity. Runtime half runnable via A1; compile half a curated, *verified* catalogue. Plus Tier B1–B5, B7. | medium | Needs A1's mechanism, so it follows S116 |
| **S119** | **Reorder + renumber** (§2c.2). Regroup the append-log tail; split 29's prerequisite half forward; retire the duplicated `main` boilerplate in favour of one referenced note; normalise every `main` to the honest pass-count invariant. **Co-planned with `/testing`** — this rewrites `expected_exits()` wholesale. | medium, high-coordination | Must be last: reordering before the content is complete means doing it twice |
| ~~S120?~~ | **RESOLVED before it was scheduled.** 0821 is answered: `examples/` gets its own minimal, lesson-derived library (§2d). The library build-out folds into S116–S119 rather than becoming a terminal arc, and the scope statement the "if not" branch asked for is shipped as `examples/lib/README.md`. | — | §2d |

Tier B6, B8–B10 fold into S117/S118 opportunistically. B11 stays blocked on
the S112 typecheck wrong-reject and is not schedulable.

**Anti-goal:** do not close these by appending files 38, 39, 40… That is the
failure mode §2c.2 diagnoses. A4 and A5 are *extensions*; A1 and the
boundaries example are new files that must land in a **regrouped** sequence,
which is why S119 exists.

### 2c.6 S115 Phase-6b — EXECUTED (2026-07-21)

Content beats (the S115-capability half, verified by probe at 6a):

| # | Item | File | Exit | Status |
|---|---|---|---|---|
| 1 | **Trait default methods (§7.1.5)** — `<=`/`>=` synthesized from `<`/`>` | `15-traits.cl` | — | **DEFERRED — blocked, see below** |
| 2 | **Impl redefinition** — re-impl replaces; a dependent dispatch site rebinds; the rebind cascades | `33-redefinition.cl` | 136 → **139** | **DONE** |
| 3 | **Auto-curry over a local closure** + trait-operator partial (captures kept scalar — FIXME 0796) | `25-curry.cl` | 118 → **139** | **DONE** |
| 4 | **Dotted-binder rejection** as a comment beat: `.` qualifies types/traits, never binds; message quoted; all four binder positions probed and uniform | `35-ctor-disambiguation.cl` | 100 (unchanged) | **DONE** |

#### Why item 1 was deferred, and what it cost item 2

**FIXME 0825 (→ `/spec`, Blocker, open) is a spec self-contradiction on the
default-method spelling**, and it is not safe to author a teaching beat
against an unsettled spelling. `spec/02-grammar.md:200` and §7.1.5 say a
default method's last element is the *body* (no return type); §7.1
"Disambiguation" says the element after the parameter bracket is *always*
the return type. The compiler follows Disambiguation, so **the spec's own
worked `Ord` example does not compile**. Confirmed live at 6b:

```
(deftrait Sized (size [x] Int) (tag [x] Int (add-i64 (size x) 1000)))
→ codegen error: undefined function: size
```

— i.e. even in the spelling the compiler *accepts*, a default body that
calls a sibling method does not reach it. So the two spellings a reader
would try are: one that fails at type resolution, one that fails at
codegen. Authoring either into the sequence would teach a form that is about
to change, and the direction is a pending user ruling.

Knock-on: item 2's planned third sub-test — *"omitting a method from a
re-impl reverts it to the trait default"* — needs a default method, so it
went with item 1. The impl-redefinition beat shipped with a different, and
arguably better-matched, third sub-test: the rebind **cascades** through a
second layer, which is the exact claim the file's plain-`defn` half already
makes. Item 2's three sub-tests are now the trait-`impl` mirror of the
file's first three, which reads more deliberately than the original mix.

**Both beats return when 0825 settles** — sequence them together, since
"reverts to the default" is only a payoff once defaults exist.

Correction beats (§2c.3 / §2c.4) — **all landed**:

| # | Correction | File(s) | Status |
|---|---|---|---|
| 5 | Deleted the false *"one concrete type per program"* claim; replaced with what let-polymorphism actually buys, and added a sub-test instantiating one `id` at Bool, String and Int in one body (plus `first-of` at two type pairs) | `07-polymorphism.cl` | **DONE** — exit 119 → **120** |
| 6 | Deleted *"Field access requires pattern matching"*; replaced with the §5.2.6 generated accessor `Type.field` (probe: `(Point.x (Point 3 4))` → 3) and when to prefer each | `10-adts.cl` | **DONE** |
| 7 | Deleted the two-instantiation invitation; the comment now states the one-instantiation constraint the code obeys, names FIXME 0483, and tells the reader not to "simplify" into the crash | `14-vecs.cl` | **DONE** |
| 7a | Corrected *"the empty `select []` never completes"* → §10.12.8/§12.7.2's fatal raise, **plus** the temporal-bracket [NEG] (it is not catchable; IO-wrapping only defers the raise past the bracket) | `32-concurrency-combinators.cl` | **DONE** |
| 7b | Corrected the lib-dirs rationale to §8.11.4 additive-union; stated the real reason isolation holds (project root is `examples/`; no `examples/stdlib/`) and that `CRANELISP_LIB` therefore *adds* the real stdlib **ahead of** `./lib` in search order and breaks free-standing runs | `Cranelisp.toml` | **DONE** |
| 8 | Purged retired **Ring 0/Ring 1** framing | `01`, `02`, `06`, `08`, `09`, `10`, `lib/prelude.cl` | **DONE** |
| 9 | Added the mod-256 exit-byte note wherever the stated total exceeds 255; corrected 14's *"first example whose sum exceeds the exit-code byte"* (05 is first) | `05`, `10`, `12`, `14`, `15`, `18`, `25`, `26`, `28` | **DONE** |
| 10 | §2 rows (07/25/33/35) and §4 updated; §4 now carries an explicit NOT-COVERED block | this file | **DONE** |
| 11 | Exit-code reconciliation FIXME to `/testing` | — | **FILED — 0824** |

**FIXME 0822 (self-targeted) is CLOSED by items 5–9** — all six false
comment-claims and the ring residue are gone.

Correction beats (§2c.3 / §2c.4 — cheap, and a corpus that states falsehoods
should not survive a sprint once they are known):

| # | Correction | File(s) |
|---|---|---|
| 5 | Delete the false *"one concrete type per program"* claim; add a two-instantiation sub-test so the example demonstrates let-polymorphism | `07-polymorphism.cl` |
| 6 | Delete *"Field access requires pattern matching"*; replace with a forward pointer to the accessor beat (full A2 work is S116) | `10-adts.cl` |
| 7 | Delete the two-instantiation invitation; state the one-instantiation constraint the code already obeys and why (FIXME 0483) | `14-vecs.cl` |
| 7a | Correct *"the empty `select []` never completes"* → §10.12.8's fatal, non-catchable raise (a hang is explicitly non-conforming) | `32-concurrency-combinators.cl` |
| 7b | Correct the lib-dirs rationale to §8.11.4 additive-union; state the *real* reason isolation holds (project root is `examples/`, no `examples/stdlib/`) and that `CRANELISP_LIB` therefore *adds* the real stdlib and breaks free-standing runs | `Cranelisp.toml` |
| 8 | Purge retired **Ring 0/Ring 1** framing | `01`, `02`, `06`, `08`, `09`, `10`, `lib/prelude.cl` |
| 9 | Add the mod-256 note wherever the stated total exceeds 255; correct 14's *"first example whose sum exceeds the exit-code byte"* (05 was first) | `05`, `10`, `12`, `14`, `15`, `18`, `25`, `26`, `28` |
| 10 | Update §2 (the row for 16 claims `export`/`defn-`, which it does not teach) and §4 (add rows: default methods, impl redefinition, binder-vs-reference boundary; mark the Tier-A gaps as **NOT COVERED** rather than leaving §4 reading as complete) | this file |
| 11 | One exit-code reconciliation FIXME to `/testing` covering items 1–3 together, filed **with** the 6b change-set in the same phase commit — `/examples` does not edit `tests/` | — |

### 2c.7 FIXMEs filed at S115 6a

- **0820 → /testing** — e2e row for `examples/16-modules/main.cl` => **47**
  (see §"Next skills"; the stale rationale at `tests/examples.rs:276` is false
  at HEAD).
- **0821 → /arch** — **ANSWERED by the user 2026-07-21 and CLOSED.** The
  disposition is neither branch the FIXME offered: `examples/` gets its own
  minimal, lesson-derived library. See §2d.
- **0822 → /examples** — **CLOSED at 6b.** All six false comment-claims and
  the ring-framing residue are corrected (§2c.6 items 5–9).
- **0823 → /arch** — filed by `/sprint` with the ruling: root `CLAUDE.md`
  §"Stdlib separation"'s "define any needed helpers inline" clause needs
  amending for `examples/`. The principle's *purpose* is untouched — the
  library is built only from compiler primitives and special forms, so the
  language is still validated independently of `stdlib/`. `tests/` keeps the
  inline rule. Open, `/arch`'s call.
- **0824 → /testing** — filed at 6b; the three exit-code changes below.

### 2c.8 Not defects

No example failed in either mode, so no defect handoff is owed this phase. The
four wrong comment-claims are `/examples`-owned documentation defects, closing
in 6b (0822) — not compiler defects. FIXME 0483 (two vec-primitive
instantiations of one generic HOF → SIGBUS) is an existing open compiler
defect, re-confirmed relevant here only because `14-vecs.cl`'s comment invites
the crashing shape; the comment fix does not close 0483.

## 2a. S101 Phase-6a assessment record (2026-07-03) — EXECUTED in 6b

> Both 6b candidates below were executed the same day: `33-redefinition.cl`
> shipped (exit 136) and `14-vecs.cl` gained the vec-ops-as-values
> sub-tests (exit 29 → 81). See §"Notes on specific entries" for the
> shipped shapes. `tests/examples.rs` reconciliation is with `/qa`.

Full replay green: 32/32 (31 top-level files at their documented exit codes
+ `16-modules/` at 47), pre-built binary, Linux `.so` symlinks resolving via
Tier 2. No regression from the S101 redefinition-machinery + vec fn-as-value
changes.

New-surface findings feeding the 6b plan:

- **Redefinition semantics ARE batch-observable.** A `--run` file that
  redefines a `defn` succeeds, and an ALREADY-DEFINED dependent rebinds to
  the new definition (verified: `f`/`g`-uses-`f`/redefine-`f` → `g` sees the
  new `f`). That is genuinely new, exit-code-verifiable language semantics
  (previously the latent unsound hole; now the R3 transaction). 6b candidate:
  `33-redefinition.cl` teaching "definitions are live — a later `defn`
  replaces the earlier one and existing dependents rebind". The *interactive*
  half of the surface (cascade `; broken:` reports, trap stubs with
  provenance, `/info` broken-status + definition source, recovery loop) is
  REPL-only UX and belongs to `/repl` scripts + `/docs` guide, not the batch
  learning sequence.
- **vec ops as values now work single-instantiation** (S101 fix): passing
  `vec-get`/`vec-set`/`vec-push` to a HOF returns correct results through the
  examples prelude re-export (verified `--run`). 6b candidate: one sub-test in
  `14-vecs.cl` ("vec ops are ordinary values") — exit-code bump needs the
  `tests/examples.rs` table updated in the same change-set (coordinate with
  `/qa`). **Constraint: keep to ONE instantiation per HOF** — a vec-trio op
  as a value at TWO instantiations of the same generic HOF SIGBUSes (new
  defect, filed as FIXME 0483 with the full repro matrix; `vec-len` and user
  fns are unaffected).

## 3. Platform / IO examples (21–24) — running without an env var

The IO examples load a platform DLL (`stdio` or `test-capture`). The
resolver (`src/platform.rs`) selects the host-native extension at compile
time (`.so` on Linux, `.dylib` on macOS, `.dll` on Windows) and searches:

1. `{project_root}/platforms/` — i.e. `examples/platforms/`
2. `{lib_dir}/platforms/` for each `lib-dirs` entry
3. directories in `CRANELISP_PLATFORM_PATH`

`examples/lib/platforms/` ships **host-correct symlinks for each platform**
— `stdio.so` / `test-capture.so` (Linux) and `stdio.dylib` /
`test-capture.dylib` (macOS) — each pointing at cargo's built
`target/debug/libcranelisp_{stdio,test_capture}.{so,dylib}`. Because
`Cranelisp.toml` puts `./lib` on `lib-dirs`, the resolver finds these via
**Tier 2** (`{lib_dir}/platforms/`), and because it looks for the native
extension first, the matching symlink resolves — so the IO examples run with
no environment variable:

```bash
./target/debug/cranelisp --run examples/21-hello-io.cl
```

> **Why `examples/lib/platforms/` and not `examples/platforms/`.**
> `examples/platforms/` is `.gitignore`d (`.gitignore:21`), so symlinks
> placed there cannot be committed — that is why the original macOS-only
> `.dylib` symlinks there were never in the repo, and why the IO examples
> failed on a fresh Linux checkout. `examples/lib/` is tracked, so the
> committable fix lives under `examples/lib/platforms/` and reaches the
> resolver via the existing `lib-dirs = ["./lib"]` (Tier 2). NOTE: a global
> `*.dylib` ignore (`.gitignore:22`) still prevents committing the macOS
> `.dylib` symlinks — only the `.so` symlinks are tracked. macOS users (or
> any host lacking a checked-in symlink) set the search path explicitly:
> `CRANELISP_PLATFORM_PATH=target/debug`.

> **Resolver note (S86).** No resolver change was needed: extension
> selection (`src/platform.rs`) is already host-correct, and
> `libcranelisp_{name}.{ext}` is already a recognised candidate. The
> residual wart — a checkout must carry one symlink per host, and the global
> `*.dylib` ignore blocks committing the macOS variant — was judged marginal
> and NOT worth a `/platform` FIXME: the `.so` symlinks resolve the
> reference (Linux) host, and macOS retains the documented env-var path.

## 4. Spec feature coverage

> **This table is a WHITELIST, not a coverage claim — read §2c.1 first, and
> §4a below for the standing NOT-COVERED list.**
> The line that stood here ("Every major language feature in the spec is
> exercised by at least one example") was **false**, and its being here is part
> of why the gaps in §2c.1 went unnoticed: the table only ever grew rows for
> things that *were* covered, so it could never show what was missing. The
> S115 outside-in sweep against `spec/` found whole first-order features with
> **no** row and no example — the error model (§12.7), field accessors
> (§5.2.6), trait default methods (§7.1.5), module visibility and the
> import/export surface (§8.3–8.7), twelve of eighteen string primitives,
> docstrings (all six positions), and `trace`/`Trace`. Restructuring this
> table so absence is visible is item 10 of the 6b plan (§2c.6).
>
> (Spec sections track the current `spec/` numbering; verify against the spec
> when annotating coverage.)

| Feature area | Example(s) |
|---|---|
| Literals (Int, Float, Bool) | 01, 02, 08 |
| `let` bindings | 03 |
| `if` expressions | 04 |
| Named functions (`defn`) | 04 |
| Recursion + TCO | 05 |
| ADTs (enums, products, sums, polymorphic) | 06, 10 |
| Pattern matching | 06, 11 |
| Let-polymorphism | 07 |
| Strings | 09 |
| Closures / lambdas / capture | 12 |
| Higher-order functions, composition | 13 |
| Vec (incl. vec primitives as first-class values) | 14 |
| Traits + operator dispatch + constrained poly | 15, 17, 20 |
| Modules / imports / exports | 16, 37 |
| Method-import dispatch (call a trait method with only the method in scope; §7.11.2) | 37 |
| Macros (defmacro, quasiquote, multi-clause) | 18 |
| Threading macros | 19 |
| Auto-currying + partial application | 25 |
| Multi-signature `defn` dispatch (arity + type + default-overload) | 36 |
| Higher-kinded traits (Functor) | 26 |
| Lazy sequences | 27 |
| IO model (`Pure`, `bind`, platform IO, `read-line`) | 21, 22, 23, 24 |
| Parallel evaluation (lenient eval: independent `let` bindings + apply-arguments) | 28, 30 |
| Explicit-control concurrency combinators (`sleep`/`race`/`select` + inline `timeout` pattern) | 32 |
| Poll-shape platform IO leaf (async effect suspends/resumes on the reactor; independent leaves overlap) | 34 |
| `:Type` annotation model (incl. `^`-style whitespace tolerance: `: Int` == `:Int`) | 29 |
| Redefinition (later `defn` replaces; dependents rebind) — **and impl redefinition: a later `impl` replaces, dispatch sites rebind, cascades** | 33 |
| Binder-vs-reference boundary (`.` qualifies a reference, never binds — all four binder positions) | 35 |
| Currying a function VALUE: a local closure, and a trait operator | 25 |
| Let-polymorphism at multiple instantiations in one batch program | 07 |
| Generated field accessors `Type.field` (§5.2.6) — **named, not yet demonstrated** | 10 (prose only; beat is S116/A2) |
| The examples-local library: importing a lesson-derived module by name | 25 (`operators`) |

### 4a. NOT COVERED — the standing gap list

This is the half the whitelist above cannot show. Every row is a
first-order spec feature with **no example**. Sourced from the §2c.1
outside-in sweep; kept here so absence is as visible as presence.

| Missing area | Spec | Tier | Scheduled |
|---|---|---|---|
| The entire error model — runtime panics, the four panic sources, `catch-runtime-error`/`Result`, the temporal-bracket [NEG], "no `throw`", wrapping-vs-checked arithmetic, `Inf`/`NaN` | §12.7, App A.3 | A1 | S116 |
| Field accessors `Type.field` as the idiomatic single-field read (a ~10-file style correction, not one example) | §5.2.6 | A2 | S116 |
| Trait **default methods** | §7.1.5 | A3 | **blocked on FIXME 0825** |
| Module visibility + the import/export surface: `defn-`/`deftype-`/`mod-`, the private-import reject, `export`/re-export, glob `[*]`, alias/renamed/null import, `super`, §8.6 shadowing & conflict | §8.3–8.7 | A4 | S117 |
| Twelve of eighteen string primitives, incl. `parse-int`→`Option` as the fallible-input idiom | App A.3, §12.1.2 | A5 | S117 |
| Pattern matching's negative space (§6.6's four prohibitions) + exhaustiveness as a compile error | §6.5–6.6 | B1 | S118 |
| Macro hygiene / auto-gensym (18 currently teaches the capture trap as the technique) | §9.8 | B3 | S118 |
| Docstrings — all six positions, zero occurrences in the corpus | §5.2.5, §5.12, §7.1.2, §9.2.4 | B7 | S118 |
| The reader surface below the top level: string escapes, comma-whitespace, `'form`, `#(… %1)`, `x#` | §1.2–1.5 | B7a | S118 |
| `trace` / the `Trace`/`TraceCall` ADT | §2.3, §12.9.5 | B7b | S118 |
| Detached strands, launch-and-continue, supervision | §10.12.7, §12.7.9 | B6 | unscheduled |
| Constrained-impl heads `(impl Display (Option :Display a) …)` | §7.3.3 | B11 | **blocked** — S112 TB-24 wrong-reject |
| Network poll-shape leaf (accept→read→send) | — | C2 | **blocked** — FIXME 0463, no free-standing socket platform |
| Bitwise integer primitives (`bit-and`/`bit-or`/`bit-xor`/`bit-not`/`shl`/`shr`/`popcount`) | 31 |

## 5. Verification

At the start and end of every sprint, run every example in **four cells** —
cold/warm × run/link — and confirm the documented exit code in each.

Two prerequisites, both easy to forget and both producing failures that look
like compiler defects (see §2f.1):

```bash
cargo build                                  # the compiler itself
bash tests/scripts/build-link-prereqs.sh     # platform rlibs the --link path scans
export CRANELISP_PLATFORM_PATH=$PWD/target/debug   # 34-async-io-leaf has no committed symlink
```

Then, with `EX="examples/[0-9]*.cl examples/16-modules/main.cl examples/37-method-import/main.cl"`:

```bash
# warm run                     (cold run: add --no-cache)
for f in $EX; do ./target/debug/cranelisp --run "$f" >/dev/null 2>&1; echo "$f => $?"; done

# warm link                    (cold link: rm -rf examples/.cranelisp-cache first —
#                               --link REJECTS --no-cache, so the cache dir is the cold axis)
for f in $EX; do o=target/ex-$(echo $f | tr / _); \
  ./target/debug/cranelisp --link "$f" -o "$o" >/dev/null 2>&1 && "$o" >/dev/null 2>&1; \
  echo "$f => $?"; done
```

A zero exit (or a value below the documented total) means a sub-test failed
— investigate before shipping. **Known exception:** `21-hello-io.cl` and
`23-io-sequence.cl` exit 1 in all four cells at HEAD, attributed to FIXME
0907 (§2f). Any other red is a regression.

The e2e guard `tests/examples.rs` (owned by `/qa`) enforces the on-disk file
set against an expected-exit table; any file add/remove/rename, or any
deliberate exit-code change, requires `/qa` to reconcile that table.

## Next skills

**S118 Phase 6 (2026-07-26) — added at the top; older entries below stand.**

- `/design`(backend) + `/arch` (S119) — rule **FIXME 0907**, co-ruled with
  0903. The examples-side evidence is appended to 0907: the two red programs,
  the three-sub-test dark region, and the finding that changes the class —
  the trait-method spelling of the same combinator **compiles and leaks**
  (~68 bytes/call, measured). A ruling that clears the refusal without
  discharging the trait-instance release would convert seven loud REDs into
  silent leaks. Acceptance for this surface: 21 exits 243 and 23 exits 178 in
  all four cells.
- `/qa` (S119) — attribute **FIXME 0916**: a self tail call in a `match` arm
  SIGSEGVs at ~1,000 depth when the scrutinee is a trait-method call; the
  plain-function control survives 400,000. Nine-line A/B repro in the FIXME.
  Two candidate loci (backend tail-call transform / typecheck trait
  resolution) with no evidence separating them.
- `/testing` (S119, optional but recommended) — add a `// defect:` line naming
  0907 to the `21-hello-io.cl` and `23-io-sequence.cl` rows of
  `tests/examples.rs`. The expected exits (243, 178) are correct and must NOT
  change; only the attribution comment is missing. `/examples` does not edit
  `tests/`.
- `/examples` (after 0907 is ruled) — delete the two attribution header blocks
  and the two Part-4 markers, replay the four-cell matrix, and only then
  consider the queued beats: `26-functor.cl`'s "IO is a Functor" extension
  (blocked today by the trait-instance leak) and §2e's `37-method-import/`
  extension (still blocked on 0869).

- `/dev` — resolve FIXME 0869, covered by
  `tests/cache.rs::cache_restores_sibling_written_trait_impls_for_dispatch`.
  The examples teaching beat stays deferred until both qualified and
  imported-bare sibling impls survive a warm-cache turn.
- `/examples` (after FIXME 0869) — retry §2e's bounded extension of
  `37-method-import/`, then replay the complete free-standing sequence in
  fresh/warm-cache Run and Link modes. Do not introduce the design-only
  Byte/text surface.
- `/testing` (with that later examples change) — reconcile only the resulting
  `37-method-import/main.cl` expected exit in `tests/examples.rs`.
- `/repl` + `/docs` (S117 Phase 6) — assess the shipped recovery,
  introspection, and canonical-display behavior; these are intentionally not
  batch-example beats.
- `/testing` (S115 Phase 6b) — **FIXME 0824**: three `expected_exits()` rows
  in `tests/examples.rs`, all verified `--run` == `--link` on 2026-07-21:
  `07-polymorphism.cl` **119 → 120**, `25-curry.cl` **118 → 139**,
  `33-redefinition.cl` **136 → 139**. Lands in the SAME phase commit as the
  example change-set; `/examples` does not edit `tests/`. No file-set change
  (no adds, no removes, no renames), so the umbrella's on-disk parity guard
  is unaffected. The `.cl` files added under `examples/lib/` are library
  modules, not sequence entries, and must NOT gain rows.
- `/spec` + user (S115) — **FIXME 0825** is the reason the trait-default-method
  beat is not in the sequence, and it will stay out until the spelling
  settles. Two beats are queued behind it (§2c.6): the `15-traits.cl`
  defaults introduction, and `33-redefinition.cl`'s "omitting a method from
  a re-impl reverts it to the trait default". A third data point for the
  ruling, found at 6b: even in the spelling the compiler *accepts*, a default
  body that calls a sibling trait method fails at codegen with `undefined
  function: <method>` — see FIXME 0832.
- `/arch` — **FIXME 0823** (filed by `/sprint`): amend root `CLAUDE.md`
  §"Stdlib separation"'s inline-helpers clause for `examples/`. §2d is the
  `/examples`-side record of what the ruling means in practice; the library
  is built from primitives and special forms only, so the principle's purpose
  is intact.
- ~~`/arch` (S115 Phase 6a) — FIXME 0821~~ — **ANSWERED and CLOSED**
  (user, 2026-07-21). Disposition: §2d.
- ~~`/examples` (self, S115 Phase 6b) — FIXME 0822~~ — **CLOSED at 6b.**
- `/sprint` — 6b is executed (§2c.6). One planned beat deferred on a Blocker
  (0825), one library seed landed (§2d.6), seven corrections landed, three
  exit codes moved. The substantive sequence work remains S116–S119 (§2c.5,
  now with the library build-out folded in per §2d.5).
- `/testing` (S115 Phase 6a) — **FIXME 0820**: add a directory-project e2e row
  for `examples/16-modules/main.cl` => **47** (verified `--run` == `--link`,
  fresh cache, 2026-07-21), modelled on the existing `37-method-import` test,
  and correct the stale "not yet relaid out to the nested shape" rationale at
  `tests/examples.rs:276`.
- ~~`/testing` (S114 Phase 6b)~~ — **DISCHARGED at S115 Phase 6a**: the
  `29-annotations.cl` expected exit **119 → 120** landed;
  `tests/examples.rs:153` asserts `&[120]` and the example measures 120 in both
  modes. Historical note retained below for the sub-test-tally discrepancy.
  The original ask was: the `tests/examples.rs:151` `29-annotations.cl`
  expected exit **119 → 120** (new `space-form` whitespace-tolerance sub-test,
  +1). Lands in the SAME phase commit as this example change (binding handoff);
  `/examples` does NOT edit `tests/`. Verified `--run` == `--link` == 120,
  2026-07-20. NOTE the file-internal sub-test breakdown comment there
  (`42 + 42 + 11 + 7 + 17 = 119`) is a different grouping than the example's own
  `7 + 1 + 42 + 5 + 64 (+1) = 120` tally; whichever `/testing` keeps, the total
  is now 120.
- `/qa` + `/testing` (S113 Phase 6b) — reconcile the `tests/examples.rs`
  expected-exit table: NEW multi-file project `37-method-import/main.cl` => **4**
  (verified `--run` == `--link`, fresh cache, 2026-07-19). It is driven the same
  way as `16-modules/main.cl` (a directory project, not a bare top-level file) —
  discovery via the existing `CRANELISP_PLATFORM_PATH=target/debug` the harness
  already sets; no platform wiring needed (pure `primitives` + local `deftype`s).
- `/qa` (S110 Phase 6b) — reconcile the `tests/examples.rs` expected-exit table:
  NEW file `36-multi-arity.cl` => **8** (verified stable over 5 `--run`
  invocations 2026-07-16; `--run` == `--link`). No platform wiring needed
  (pure primitives + a local `deftype`). Filed as FIXME 0629.
- `/qa` (S106 Phase 6) — reconcile the `tests/examples.rs` expected-exit table:
  NEW file `34-async-io-leaf.cl` => **4** (verified stable over 5 `--run`
  invocations 2026-07-10). **No platform-wiring change is needed**: the
  `async-demo` DLL is already built suite-wide by
  `tests/scripts/build-link-prereqs.sh` (`-p cranelisp-async-demo`), and the
  harness already exports `CRANELISP_PLATFORM_PATH=target/debug` for every
  example — only the `expected_exits()` row is owed.
- `/sprint` — FIXME 0463 is **NOT closed** by example 34. 34 delivers the
  poll-shape platform-leaf *mechanism* (suspend/resume/overlap via `async-read`,
  a timer leaf); the NETWORK accept→read→send shape 0463's title asks for
  remains blocked. **Narrow 0463** from "add a poll-shape network/platform leaf
  example" to its precise unmet dependency: *a free-standing shared **socket**
  platform under `platforms/` exposing poll-shape `accept`/`read`/`send` —
  ideally plus a client-`connect` leaf so a single `--run` can self-drive (bind
  ephemeral port → connect to self → accept → read → send → assert → exit N),
  sidestepping the external-client and hangs-forever problems.* Owner
  `/platform` (+ `/arch` for shared-vs-exemplar placement). Blocker #2
  (harness-cannot-drive-a-server) is also softened: a self-driving socket leaf
  needs no harness extension since 34 proves a self-driving poll leaf runs green
  under the plain exit-code umbrella. Until the socket leaf lands, the network
  showcase stays exemplar-only and 34 is the sequence's poll-shape-leaf teacher.
- `/platform` — awareness: example 34 now depends on `platforms/async-demo`'s
  `async-read` as a **taught, user-facing** surface (previously a reactor-e2e
  test fixture only). It is referenced, not modified. If `async-demo`'s effect
  name/signature/semantics change, example 34 and `tests/concurrency_reactor.rs`
  must move together.
- `/qa` (S101 Phase 6b) — reconcile the `tests/examples.rs` expected-exit
  table: `14-vecs.cl` **29 → 81** (new vec-ops-as-values sub-tests) and NEW
  file `33-redefinition.cl` => **136**. Both verified via
  `target/debug/cranelisp --run` on 2026-07-03.
- `/qa` — (1) The S96 `32-concurrency-combinators.cl => 6` row is already in the
  `tests/examples.rs` table (added with the example so the umbrella stays green —
  the test's own assertion instructs the file-adder to update `expected_exits()`);
  no reconciliation owed, just awareness. (2) Author the narrow failing repro for
  the **race-inline-bind-lambda lenient-eval codegen defect** surfaced by this
  example — minimal: `(import [primitives [Pure bind race]]) (defn main [] (race
  (bind (Pure 0) (fn [_] (Pure 111))) (Pure 222)))` errors under default lenient
  eval with `failed to declare lambda function … incompatible with previous
  declaration`, compiles+runs (exit 111) under `CRANELISP_NO_LENIENT=1`; `select`
  with the same shape is unaffected. Resolver: `/backend` (apply-argument
  sparking vs combinator-argument lambda naming).
- `/docs` — getting-started can lead with `01-integers` and reference the
  platform-symlink note here for the IO examples.
