# Program-result ownership

**Owner:** `design` (int). **Status:** current contract, verified against source
on 2026-09-21. **Subordinate to:** [`int.md`](int.md).
**Scope:** `src/` and `crates/cranelisp-exe-bundle/`.

Governing inputs, not restated here:

- [Type-drop glue identity](../arch/interfaces.md#type-drop-glue-identity-and-address-boundary)
  — `drop_glue_symbol_name` and `ConcreteType::result_root`.
- [IO-node ownership on force](../arch/total-concreteness.md#ownership-on-force--io-values-are-reusable-user-ruling-2026-09-21)
  — what reference the program driver hands back for a `Pure` payload.
- [Typecheck's residual-parameter defaulting](../typecheck/non-concrete-producer-obligations.md#3-values-residual-parameter-defaulting)
  — why a result's codegen type can be concrete when its display type is not.
- `design/arch/safety-invariants.md` R15 and `design/arch/bounded-contexts.md` §6.

Section numbers are stable because source, tests and filings cite them. Retired
numbers (§0, §8–§11) are not reused.

---

## 1. Binding outcome: observe, then release

Every successful execution result crosses from generated code into exactly one
**program-result owner**. The owner carries `(value: i64, ty: Type)` from the
program driver through the result's final observation, then releases the value
exactly once through backend's canonical glue for its concrete type.

1. The driver returns a word with its static result type. For `IO a`, the
   driver forces the tree and hands over the `Pure` payload; the owned type is
   `a`. The unwrap happens once, at the driver boundary.
2. Int determines the **release key** once, from the producer's codegen type
   (§1.1.1), and classifies that key once (§1.1). A scalar or value-layout
   result needs no release. Failing to obtain a key is an invariant error,
   never permission to shallow-release or leak.
3. The owner observes the live value. The REPL formats it; `--run` and `--link`
   convert it to the process exit code (`Int` narrows to `i32`; every other type
   exits 0). `result_is_exit_code` is the one statement of that rule.
4. Only after observation completes, the owner calls the canonical
   `extern "C" fn(i64)` glue for `(emitting module, ConcreteType)`.
5. The owner relinquishes the word. No downstream carrier holds an owned copy.

- The order is unconditional for owning values. A display failure, a
  successful conversion and a non-`Int` exit all still release.
- Runtime-error and dispatch-fault outcomes carry no successful result, so they
  create no owner and call no glue.
- A glue failure is an internal safety failure. Int never retries it.
- Int never traverses the value. Backend's per-concrete glue owns transitive
  discharge, so `String`, `Vec String`, nested ADTs, closures and recursive
  values all use the same one-call protocol.

There is no JIT-only releaser, IO-only payload branch, display-owned release,
shallow fallback or private copy of backend glue behaviour (**Single pipeline,
mode parameters**).

### 1.1 Classification is a shared predicate, not an absence test

Backend emits no glue row for a `NeverHeap | Value` type, so absence of a row
alone cannot distinguish "needs no release" from "artifact missing". Int
therefore asks backend's own question before any keyed lookup:

1. obtain the release key (§1.1.1);
2. classify it with the public `cranelisp_backend::heap::HeapCategory::classify`;
3. `NeverHeap | Value` ⇒ the inert arm; no keyed lookup is attempted;
4. `AlwaysHeap | Mixed` ⇒ the owning arm; a keyed miss is a hard error (§5).

- `Mixed` (a nullary-or-boxed ADT) owns: its glue exists and handles the bare
  tag internally. Int does not replicate that guard.
- An int-side "is this a heap type" list is rejected (**Single source of
  truth**). If the predicate moves to `cranelisp-types`, int follows it.

### 1.1.1 The release key is the producer's key

> The release key is the result-producing entry's `codegen_view` body
> `ConcreteType` — the value backend used for its result root — projected
> through `ConcreteType::result_root()`. Narrowing the observed `Type` with
> `ConcreteType::from_type` is only the fallback for an entry that published no
> codegen view. A narrowing failure there is the §5 hard error, naming the type
> and the absent view.

- The observed type is not always concrete. An unannotated `(Err "boom")`
  displays as `(Result a String)`, which the REPL display rules require.
  Typecheck's codegen view defaults the residual parameter to
  `(Result Int String)`, and backend emits glue for that type. Keying on the
  observed type would either fail or demand glue backend never emitted.
- Taking the key from the same read that produced the code pointer (§4.3) makes
  int's classification agree with backend's by construction (**Resolve once**).
- Bare polymorphic values do not execute. An unpinned `[]` or nullary
  constructor such as `None` publishes a slot-less template; eval returns
  `EvalResult::DisplayValue`, rendered from the inferred type and syntax. No
  word, slot or owner is fabricated. Calls and annotations follow ordinary
  evaluation.
- The one-hop `IO a ⇒ a` projection has one home, `ConcreteType::result_root()`.
  Int and backend both call it; neither holds a private copy.

---

## 2. Representation and ownership states

`OwnedProgramResult` (`src/result_owner.rs`) is the int-private owner. Its
states:

```text
driver outcome
  ├─ error/trap ─────────────────────────────> no owner
  └─ clean + static Type
       -> OwnedProgramResult { value, type, release target or inert }
       -> observed (display or exit conversion)
       -> released or typed no-op
       -> consumed
```

- Construction consumes the clean outcome value and its carried type, and
  refuses an `IO a` type outright, so a second IO unwrap is unconstructable.
- The owning arm holds a `GlueTarget`: the address together with the `Code`
  that keeps it mapped. The inert arm holds no callable target.
- Observation borrows the value; finalization consumes or disarms the owner.
- There is one finalization chokepoint. Callers cannot copy the owned word or
  invoke the target independently.
- A `Drop` backstop releases an armed owner during unwinding through the same
  chokepoint and disarm state. It is not a second normal release path.

A raw function address without its `Arc<Jit>` or `Arc<Linker>` guard is not a
valid release target (**Published pointers have retention owners**).

---

## 3. One protocol, three target-resolution adapters

Target resolution varies only because compiled code is housed differently. The
owner and the observe-then-release order do not vary.

- The owner is constructed after a published turn's code has executed, at the
  execution seams. It never attaches inside the prepared transaction.
- The adapter is selected by the `Code` that owns the result-producing entry:
  `Code::Jit` selects §3.1, `Code::Linker` selects §3.2, and any other or absent
  housing is a hard error for an owning result. A new housing needs a new
  adapter, never a no-release fallback.
- The key's module is the **emitting** module — the module that owns `main` or
  `__expr` — never a source expression's module or the latest compiled function.

### 3.1 Fresh JIT (`--run`, REPL and post-cache-miss)

Backend emits exported glue for every concrete owning result root of a compiled
batch and projects it into `CompilationArtifacts.drop_glues` with a finalized
`jit_address`.

1. The ordinary prepared publication moves each row into
   `SharedState.fresh_jit_drop_glues`, keyed `(module, ConcreteType)` and
   paired with the batch's `Code::Jit` owner (`FreshJitDropGlue`).
2. At construction, int keys and classifies (§1.1), then performs one keyed
   read.
3. It clones the row whole — artifact and owner. The clone is the retention
   root; the address is never stored without it.
4. An absent row, a symbol that differs from `drop_glue_symbol_name(module,
   key)`, `jit_address: None`, or a zero address is a hard integration error
   before observation. There is no symbol scan and no late compilation.
5. Observe while the cloned owner is live; call the address; drop the clone
   after the call returns.

`--run` and the REPL share this construction and differ only in the observation.

#### 3.1.1 One publication seam, one paired row

The ordinary prepared publication is the only writer to `fresh_jit_drop_glues`,
for HM clusters and macro checkpoints alike. It inserts `{artifact, owner}` as
one value, so a row is replaced pair-atomically or not at all. A macro-specific
writer, or any update of artifact and owner separately, could pair an old
address with a new JIT and is rejected.

### 3.2 Cache-hit execution

A cache hit carries no process-local glue address. The loaded object already
exports the glue body. Int:

1. derives the canonical symbol with `cranelisp_types::drop_glue_symbol_name`;
2. resolves it once with `Linker::get_symbol`, rejecting a miss or a null
   address as a hard cache-load error;
3. takes the `Arc<Linker>` from the result-producing entry's own
   `Code::Linker`. **The release target's retention owner is the same `Code`
   that owns the code which produced the result** — the rule that also makes
   §3.1's row read safe. No session map is added; the cache loader tabulates
   only callable-slot symbols;
4. runs the identical owner.

- A missing symbol is never repaired by synthesizing private glue.
- No address or glue map is serialized, so this adds no cache-schema field.
- `BUILD_ID` invalidation already prevents an older binary's object from being
  read, so a missing glue symbol is a genuine defect signal.

#### 3.2.1 Reach in production

Cache-hit loading restores only dependency modules today, never the CLI target,
so `main` and `__expr` always carry `Code::Jit`. The adapter's production
caller is the test runner: a test defined in a cache-restored module releases
its result through this adapter
([test runner §6.2](test-runner.md#62-execute)). The §6 row-3 unit tier
covers it directly.

- Keep it. Without it the adapter selection would need a no-release or
  wrong-row fallback for `Code::Linker`, the two shapes §5 forbids. The day
  cache restoration widens to the CLI target, its absence would be a silent
  leak.
- Its unit rows are not end-to-end evidence. The change-set that widens cache
  restoration to the CLI target owes an e2e observing a cache-hit result
  released exactly once.

### 3.3 Linked startup

`link_by_name` already validates `main : (Fn [] (IO _))` and reads `main`'s
entry. From that same read it:

1. takes the inner result type and its release key (§1.1.1), and classifies it
   (§1.1);
2. for a `NeverHeap | Value` result, passes no release symbol, and the stub is
   unchanged;
3. for an owning result, passes `drop_glue_symbol_name(entry_module, key)` to
   `generate_startup_object`, which imports it with signature `(i64) -> ()`;
4. reports a result with no obtainable key as a located link-time error naming
   the module and type, never a silent skip.

The stub's clean block then:

1. retains the driver's result word;
2. computes the process exit code while the word is live;
3. calls the relocated glue once for an owning result;
4. calls `exit` with the computed code.

The error block calls no result glue: a non-zero `error_kind` carries no
successful result. The entry module's object exports the glue body, and the
system linker resolves the relocation. The startup object owns no Rust `Arc`;
executable text stays live until `exit`. The exe-bundle must keep the runtime
symbols the generated glue calls (`runtime/dealloc`, `runtime/vec_drop`)
force-linked, and it defines no wrapper releaser and interprets no result type.

---

## 4. Integration seams and data flow

### 4.1 Artifact routing and consumption discipline

The routing is `compile_to_module` → prepared compilation → prepared
publication → `SharedState.fresh_jit_drop_glues`, keyed
`(module, ConcreteType) → {artifact, owner}`. The owner consumes it:

- **Read once**, at construction, never at display time.
- **Clone the pair**, never the address alone.
- **Never re-derive** backend's encoding. The symbol comes from the artifact
  (fresh JIT) or from `drop_glue_symbol_name` (cache and link), the one
  types-owned grammar.

An armed owner holds its own `Code` clone, so a later row replacement cannot
unmap the code it will call.

Do not wire result ownership into `worker::inline_jit_codegen_for_names`. It
has no production caller and discards the drop-glue artifacts.

### 4.2 REPL value lifetime

The clean REPL result travels from `pipeline::program_outcome_to_result` as
`ExprOutcome::Value` and `EvalResult::Val` to the formatter. The owner stays
armed across that boundary.

- Formatting reads the value first. `EvalResult::release_program_result()` runs
  after the complete `StyledDoc` is built and before control returns to the
  prompt. The REPL turn, EOF flush and agent submit each call it.
- Definition, bare-symbol and `DisplayValue` displays did not come from an
  executed result and create no owner.
- No formatter has an `IO` branch. `OwnedProgramResult::new` refuses `IO a`, so
  a future direct caller cannot build a second IO owner.

#### 4.2.1 A command that measures its own turn drives the release itself

[`/mem`](../../repl/spec/03-slash-commands.md#37-mem--allocation-statistics-tested)
requires the delta for `/mem <expr>` to include the result release. A REPL command that measures its turn's memory effect:

```text
open the counter window
  -> eval
  -> observe: render the result text
  -> release: EvalResult::release_program_result()   (the one chokepoint)
close the counter window
  -> compose the measurement line
  -> return result text and measurement line as one document
```

- Observation still completes before release; the measurement line is not an
  observation of the value.
- This is not a second release site. The explicit call reaches the same
  exactly-once chokepoint the `Drop` backstop would otherwise reach later.
- `Ok(None)` and `Err` carry no owner and release nothing.
- A command measuring *time* closes its window where its meaning says. `/time`
  measures evaluation and excludes the release. Changing that is a REPL
  specification question for `spec`; do not align one instrument's window with another's
  for symmetry alone.
- Emitting the delta as a separate write after the release was rejected: it
  would split what the user sees into two documents.

### 4.3 Run lifetime

`CompilerSession::trampoline` returns the owner. The `--run` order is
**observe → release → object-wait and shutdown → trace flush → exit**.

- Releasing before `shutdown` is not load-bearing against a current hazard:
  `shutdown` drops no symbol table or `Code`, and `process::exit` bypasses
  `Drop`. The order is kept because it is free and stays correct if `shutdown`
  gains teardown duties. A reordering finding here is not a memory-safety
  blocker.
- **Same-read rule.** Each owner or startup exit takes its release key from the
  result-producing entry's `codegen_view` in the same read that produces the
  code pointer: `pipeline.rs` for REPL execution, `CompilerSession::trampoline`
  for `--run`, `link_by_name` for linking. The observed `Type` travels with the
  owner for formatting and `result_is_exit_code`; it is only the key's fallback.
  A future seam acquires the key the same way. The test runner's preparation
  read takes each test's code pointer, code owner and key together. It
  resolves the release target before the first test runs, through the
  crate-private `ReleasePlan`; `OwnedProgramResult::new` is itself
  plan-then-own, so classification still has one implementation
  ([test runner §6](test-runner.md#6-prepare-execute-and-report)).
- `--run` reads `main`'s code pointer, result type and code owner in one entry
  read (`read_main_entry`); no separate return-type lookup can fall back. The
  REPL's observed-type default (`Type::Int` when neither a display nor an
  inferred type exists) never decides release, because an executed `__expr` is
  a concrete body whose codegen view supplies the key.

### 4.4 `Pure` and non-IO results

The program driver forces the result's IO tree and hands int one owned
reference to the `Pure` payload, as the IO-node ownership contract defines. The
owner releases that reference with glue for `a` — never glue for `IO a`, and
never an intrinsics `consume_*` function; the IO node's own teardown is the
runtime's.

Non-IO expression execution enters the same constructor with its own type, so
REPL evaluation and entry `main` obey one rule.

---

## 5. Exact-once and error-path rules

| Event | Disposition |
|---|---|
| clean scalar/value result | observe; release is a typed no-op; no keyed lookup |
| clean owning result | observe completely; call the target once; disarm |
| display or exit conversion fails | release through the same target before propagating, or through the armed backstop on unwind |
| driver runtime trap or dispatch fault | no owner; no glue call |
| no release key: no codegen view **and** the observed type does not narrow | hard located invariant error naming the type and the absent view; never shallow release or silent leak. A non-concrete observed type alone is not this row (§1.1.1) |
| owning type absent from `fresh_jit_drop_glues` | hard integration error; no scan, no late compilation |
| `jit_address: None` on a fresh-JIT owning result | hard integration error (object-mode polarity in a JIT path) |
| zero fresh-JIT address, or null `Linker::get_symbol` result | hard error at that adapter's safe boundary, before a `GlueTarget` exists; never a skip |
| artifact symbol differs from `drop_glue_symbol_name(module, key)` | hard integration error naming both spellings |
| cache-hit `Linker::get_symbol` miss | hard cache-load error; never private glue |
| linked startup: no obtainable key | located link error naming module and type |
| glue call traps | propagate or abort as a safety failure; never retry |
| session shutdown, REPL redefinition or row replacement | cannot invalidate a target held by an armed owner's `Code` clone |

Once the release call begins, the caller must not inspect, format, convert or
release the word again.

**Non-null is each adapter's obligation.** The address is the sole input to the
module's one `transmute`, so each adapter rejects null at its own safe boundary
with a located diagnostic. The `debug_assert_ne!` in `GlueTarget::new` is a
debug-tier detector for a future adapter that forgets, not a gate: it is absent
from release builds. A null-address unit row must discriminate the adapter's
error, not the assertion.

---

## 6. Unit-test design

Unit tests sit beside the owner and use test doubles for observation and glue.
Linked relocation stays end-to-end, where it is the fact under test. Ordering
tests assert a recorded event sequence
(`observe-start → observe-read → observe-done → glue(value) → guard-drop`);
counter tests assert exactly one glue call; type tests assert the exact
`ConcreteType` key and module-qualified symbol. Source cites the rows by
position, row 1 to row 7.

| Submodule | Positive | Edge | Negative |
|---|---|---|---|
| owner constructor and classification (`src/result_owner.rs`) | `Int` no-op; `String` release; `IO String` selects `String`; nested ADT/Vec key; the codegen key wins over the observed type and its `IO` head is stripped | non-IO expression; value `0` as a valid owned word; `Mixed` nullary tag | non-concrete type with no codegen view; owning type with no keyed target; never `IO a` glue; inert arm performs zero map reads |
| fresh-JIT resolution | keyed rows pair with `Code::Jit`; owner clone outlives the call | two types in one batch; repeat key; recompilation replaces address and owner together | absent key; `jit_address: None`; zero address; symbol/key mismatch; no address stored without its guard |
| cache-hit resolution | canonical symbol resolves through the entry's `Code::Linker` | two module-qualified copies of one concrete type | missing or null symbol fails hard; no scan; no `Code::Jit` row consulted for a Linker result |
| REPL display (`src/eval.rs` → `src/repl/format.rs` → `src/display.rs`) | scalar, `String` and nested payload displayed before one release | formatter error or unwind; warnings; value `0`; bare `None` and `[]` use `DisplayValue` | no release before the last display read; no second release; definition and `DisplayValue` paths release nothing |
| run arm and lifecycle (`src/main.rs`, `CompilerSession::trampoline`) | `IO Int` converts then releases; `IO String` exits 0 then releases | nested payload; shutdown after release | trap or fault calls no glue; glue never retried; no observed-type default decides release |
| startup CLIF (`src/exe.rs`) | scalar emits no call; owning result converts, then calls the relocated glue, then `exit` | `Int` owning wrapper versus scalar `Int`; nested type; module-qualified symbol | error block emits no release; no call after `exit`; a missing relocation is a link failure; a result with no obtainable key errors at `link_by_name` |
| exe-bundle (`crates/cranelisp-exe-bundle`) | the glue's runtime dependencies stay force-linked | program without a platform DLL | no generic releaser or result-type switch in the bundle |

---

## 7. Quality attributes and review rejects

- **Simplicity:** one owner state machine and one release-target shape; three
  small adapters reflect real housing differences. No value traversal and no
  second heap predicate.
- **Observability:** resolution errors name module, concrete type, expected
  symbol and mode. No trace sink is added.
- **Concurrency safety:** rows are `{artifact, owner}` pairs written only by the
  prepared publication; owners are turn-local and hold a `Code` clone; the map
  is read only at owner construction.
- **Performance:** one keyed lookup and one glue call per owning result; scalar
  results are call-free and read no map. The map grows with distinct
  `(module, owning ConcreteType)` pairs, the same order as the retention pool.
- **Testability:** observation and release are separable behind the owner, so
  ordering, exact-once and error cleanup are unit-testable without a compiler.

`review` rejects any change here that introduces:

- a raw release address without its `Code` guard, or a null address reaching
  `GlueTarget::new` from an adapter;
- a second heap-type predicate, or a release key re-derived from the observed
  type;
- an observe/release ordering inversion, or an IO-only or JIT-only release;
- an `IO` branch in a formatter, or any private deep releaser;
- a second `fresh_jit_drop_glues` writer or a non-pair row update;
- result wiring into `inline_jit_codegen_for_names`.

No marshalled macro handle, result owner or release target enters macro
preparation, source retry or publication. The macro reader's cloned `Code` is a
code-lifetime guard for invocation, not another glue-registry writer
([macro-turn ownership §9](macro-turn-ownership.md#9-interaction-with-macro-checkpoints)).

## Open obligations

- **Cache-hit result e2e (conditional).** Owed by the change-set that widens
  cache restoration to the CLI target (§3.2.1). `qa` allocates it then.
