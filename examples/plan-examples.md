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
   `stdlib/`. They define helpers inline from compiler primitives and
   special forms, and resolve names through the tiny, standalone
   `examples/lib/prelude.cl` (configured via `examples/Cranelisp.toml`
   `lib-dirs = ["./lib"]`). This validates the *language*, not the library.
   This is a hard rule from the root `CLAUDE.md` §"Stdlib separation".
4. **Every example is runnable at all times.** A broken example teaches that
   the language is broken. Examples are sentinels: they catch real
   regressions by exercising the language end-to-end in compact form.
5. **Verifiable via exit code.** Every example defines `main` returning an
   Int (wrapped in `Pure`/`IO` where the IO model is in play). The return
   value is the sum of sub-test pass counts (1 per passing sub-test). A
   non-zero, *expected* exit code means every sub-test passed; a drop below
   the expected total signals a regression. The e2e guard
   `tests/examples.rs` pins each file's expected exit code.
6. **Comments explain the capability**, not the syntax — the code and its
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
| 07 | `07-polymorphism.cl` | Let-polymorphism and type variables | 119 |
| 08 | `08-floats.cl` | Float literals and the monomorphic `*-f64` primitives | 10 |
| 09 | `09-strings.cl` | The `String` type and string operations | 55 |
| 10 | `10-adts.cl` | Product and sum types with typed fields | 9 |
| 11 | `11-destructuring.cl` | Pattern matching that binds constructor fields | 69 |
| 12 | `12-closures.cl` | Anonymous functions (`fn`) and variable capture | 7 |
| 13 | `13-higher-order.cl` | Functions as arguments and return values; composition | 203 |
| 14 | `14-vecs.cl` | `Vec` literals and operations; vec primitives as first-class values | 81 |
| 15 | `15-traits.cl` | Trait-based operator dispatch (`Num`/`Eq`/`Ord`) + constrained polymorphism | 58 |
| 16 | `16-modules/` | Multi-file programs: `mod`, `import`, `export`, `defn-` | 47 |
| 17 | `17-display.cl` | User-defined traits and the `Display` trait | 176 |
| 18 | `18-macros.cl` | `defmacro`, quasiquote/unquote, multi-clause macros | 89 |
| 19 | `19-threading.cl` | Data pipelines with `->`, `->>` and friends | 130 |
| 20 | `20-adt-traits.cl` | Implementing traits (`Eq`, `Display`) for user ADTs | 39 |
| 21 | `21-hello-io.cl` | The IO model: `Pure`, `bind`, combinators, platform IO | 243 |
| 22 | `22-io-hello.cl` | Testable IO via the `test-capture` platform | 99 |
| 23 | `23-io-sequence.cl` | IO sequencing patterns with explicit `bind` chains | 178 |
| 24 | `24-io-echo.cl` | Input with `read-line`; read-then-process | 20 |
| 25 | `25-curry.cl` | Multi-signature dispatch and auto-currying | 118 |
| 26 | `26-functor.cl` | The `Functor` trait (higher-kinded `fmap`) | 91 |
| 27 | `27-lazy-seq.cl` | Lazy sequences (`take`, `filter`, `iterate`) | 183 |
| 28 | `28-parallel.cl` | Parallel evaluation: automatic sparking of independent `let` bindings (lenient eval) | 67 |
| 29 | `29-annotations.cl` | The `:Type` annotation model (capstone): constraining function typing + disambiguating expressions | 119 |
| 30 | `30-parallel-map-reduce.cl` | A general parallel `par-map` over a Functor: apply-argument sparking makes recursive divide-and-conquer and `fmap` of an expensive function parallelise automatically | 56 |
| 31 | `31-bitwise.cl` | Bitwise integer primitives (`bit-and`/`bit-or`/`bit-xor`/`bit-not`/`shl`/`shr`/`popcount`) as bitmask set operations; inline single-bit helpers (`bit-test`/`bit-set`/`bit-clear`/`bit-flip`) and a permission bitmask | 19 |
| 32 | `32-concurrency-combinators.cl` | Explicit-control concurrency (the CONTROL peer to 28/30's inferred half): `sleep` timer leaf, `race` (first-to-complete wins, loser cancelled), `select` (n-ary race over a Vec), and the `timeout` pattern expressed inline as `race`-against-a-deadline (stdlib `timeout` is off-limits to free-standing examples) | 6 |
| 33 | `33-redefinition.cl` | Definitions are live: a later `defn` replaces the earlier one, existing dependents rebind, and rebinding cascades transitively | 136 |
| 34 | `34-async-io-leaf.cl` | Poll-shape platform IO leaf: an async effect (`async-read`) that SUSPENDS on the host reactor and RESUMES with its result, vs. the blocking effects of 21–24; independent poll-shape leaves overlap on one reactor thread. Teaches the poll-shape leaf MECHANISM the network "server-with-no-spawn" shape is built on | 4 |
| 35 | `35-ctor-disambiguation.cl` | Same-named constructors across two in-scope types: the bare ctor name is ambiguous, the dotted `Type.Ctor` form disambiguates in VALUE position, and the dotted prefix in PATTERN position pins the scrutinee type (a cross-type dotted pattern is a compile-time type error). Builds on 06/10 | 100 |
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

Every major language feature in the spec is exercised by at least one
example. (Spec sections track the current `spec/` numbering; verify against
the spec when annotating coverage.)

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
| `:Type` annotation model | 29 |
| Redefinition (later `defn` replaces; dependents rebind) | 33 |
| Bitwise integer primitives (`bit-and`/`bit-or`/`bit-xor`/`bit-not`/`shl`/`shr`/`popcount`) | 31 |

## 5. Verification

At the start and end of every sprint, run every example and confirm the
documented exit code:

```bash
for f in examples/[0-9]*.cl; do
  ./target/debug/cranelisp --run "$f" >/dev/null 2>&1; echo "$f => $?"
done
./target/debug/cranelisp --run examples/16-modules/main.cl
```

A zero exit (or a value below the documented total) means a sub-test failed
— investigate before shipping. The e2e guard `tests/examples.rs` (owned by
`/qa`) enforces the on-disk file set against an expected-exit table; any
file add/remove/rename, or any deliberate exit-code change, requires `/qa`
to reconcile that table.

## Next skills

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
