# Program-result ownership and typed-context exit

**Status:** DESIGN — authored S116 Phase 3, refreshed to implementation-ready
S118 Phase 3 against HEAD `d1c34699`, **and RATIFIED as-built at S118 W4+**
(implementation `fc3375f9..16a26408`; W4 gate PASS; **FIXME 0745 CLOSED**). The
one design deviation the implementation forced — the release key — is ruled in
**§1.1.1** (FIXME 0896); the doc-truthfulness re-count of the fresh-JIT
polarities is in §6/§8 (FIXME 0901); the two as-built notes W4 flagged are
§3.2.1 (cache-hit adapter production-unreached) and §4.2 (the second IO owner is
now unconstructable). **Subordinate to:** `int.md`.
**Scope:** the Binary/int surface (`src/` + `crates/cranelisp-exe-bundle/`) only.
**Architecture inputs:** `design/arch/safety-invariants.md` R15,
`design/arch/bounded-contexts.md` §4b invariant 16 and §6,
`design/arch/interfaces.md` §“Type-drop glue identity and address boundary”,
Sprint 116 architecture ruling 9, and S118 arch rulings 10 (the Principle-8
bridge closes this sprint) and 11 (0863 serializes AFTER this work).
**Backend counterpart:** `design/backend/transitive-drop-glue.md` (§3.3 the
artifact contract, §3.4 D1/D6 the as-built reshape, §7 the slice order).
This resolves the design obligation in FIXME 0745; the FIXME remains open
until implementation and verification.

---

## 0. What this refresh changes

The S116 semantics (§1–§5) are **re-verified at HEAD and stand unchanged**. What
moved is the ground underneath them: S117 landed the W3a prepared-turn
transaction, the W3b presentation readers, and the W7 cached-macro clause
repair in `src/` after this design was written. The corrections:

1. **§4.1 was written against a seam that no longer exists.** `worker::
   inline_jit_codegen_for_names` — the "int compilation record that currently
   installs `Code::Jit`" the S116 text names — has **no production caller at
   HEAD** (`src/worker.rs:1544`; four call sites, all in `src/worker/tests.rs`).
   Every mode now routes through `prepare → compile_prepared_turn →
   publish_prepared_turn`. §4.1 is rewritten onto that seam.
2. **The fresh-JIT artifact routing already landed** (S117 W3a). `SharedState.
   fresh_jit_drop_glues: DashMap<(ModuleFullPath, ConcreteType),
   FreshJitDropGlue>` (`src/session_v4.rs:352-358`) is populated by
   `publish_prepared_turn` (`src/worker.rs:1748-1758`) and by the macro-clause
   turn's `publish` (`src/process_form/macro_clause.rs:175-187`), always as an
   `{artifact, owner}` **pair**. 0745 no longer has to build the routing — it
   has to *consume* it. §3.1 and §4.1 are re-cut accordingly.
3. **§7's "no global address map is introduced" claim is STALE.** One was
   introduced, by S117, and it is the right shape. The invariant that carries
   the weight is restated in §7: rows are replaced *pair-atomically*, and an
   armed result owner holds its own `Code` clone, so a replacement can never
   invalidate it.
4. **§4.3's "session shutdown may remove the final retention root" claim is
   OVERSTATED at HEAD.** `CompilerSession::shutdown` (`src/session_v4/
   lifecycle.rs:1762-1800`) settles the index, stops the scheduler and joins the
   worker pool; it drops no symbol table and no `Code`. The ordering rule is
   *retained anyway* — it costs nothing and is robust to `shutdown` evolving —
   but it is no longer justified by a live hazard, and §4.3 says so.
5. **Backend D1 changes nothing this design consumes.** Moving `finish()` after
   body compilation (`transitive-drop-glue.md` §3.4 D1, §7.0 slice S0) enlarges
   the projected map with consumer-demanded types; the result-root pre-pass
   (D6) and the projection semantics at `lib.rs:736/749-766` are unchanged. The
   0745 keys are result roots, which are pre-requested either way.
6. **New material:** the as-built seam census (§3.0), the serial implementation
   order (§8), the refreshed unit matrix (§6), and the acceptance mapping
   including QA's armed-detector re-demonstration leg (§9).

**What the S118 W4+ ratification pass changed on top of that** (this pass; the
sprint's post-implementation design drain):

7. **§1.1 step 1 / §5's non-concrete row are superseded by §1.1.1.** The
   observed-type narrowing was falsified in implementation by spec-required
   displays carrying residual type vars; the release key is the producer's
   `codegen_view` key, with `from_type` as the fallback that keeps the hard
   error. §4.3 gains the same-read statement and the FIXME-0898 pointer.
8. **§6 row 2 and §8's I1 exit re-count the fresh-JIT polarities three → four**
   (the null-address polarity, FIXME 0897), and §5 gains its row; the
   `GlueTarget::new` `debug_assert` is recorded as a debug-tier detector, not a
   gate.
9. **Two as-built notes recorded:** §3.2.1 (the cache-hit adapter is
   design-mandated but production-unreached — *kept as specified*, with the
   obligation it creates) and §4.2 (the second IO owner is deleted and
   unconstructable, not merely unreachable).

Nothing here needs a public-API, `cranelisp-types`, cache-schema, or backend
entry-point change; §10 records the verification.

---

## 1. Binding outcome: observe, then release

Every successful execution result crosses from generated typed code into exactly
one **program-result owner**. That owner carries the pair `(value: i64, ty: Type)`
from the program driver through the result's final observation, then releases the
value exactly once through backend's named glue for its concrete owning type.

The semantic protocol is:

1. The driver returns a word and its caller preserves the static result type. If
   the source return type is `IO a`, the driver consumes the IO protocol tree and
   transfers the `Pure` payload; the owned result type is the inner `a`, not
   `IO a`.
2. Int determines the result's **release key** once — from the producer's own
   codegen view, never by re-deriving it from the observed display type
   (§1.1.1) — and classifies that key once. A scalar/value-layout result needs
   no release. Failure to obtain a key is a typed-context invariant error, never
   permission to shallow-dec or leak.
3. The owner observes the live value: REPL formats it, while run/link converts it
   to the process exit code (`Int` narrows to `i32`; every other type yields 0).
4. Only after that observation completes, the owner invokes the canonical
   `extern "C" fn(i64)` glue selected by `(emitting module, ConcreteType)`.
5. The owner then relinquishes the word and may exit or return. No downstream
   carrier contains an owned copy.

This ordering is unconditional for owning values. Display failure, conversion
success, and non-`Int` exit conversion do not waive release. Runtime-error and
dispatch-fault outcomes carry no successful result owner and therefore invoke no
result glue. A glue failure is an internal safety failure and is not recovered by
calling glue again.

The protocol applies to plain heap results and to arbitrarily nested payloads.
Int never traverses the value. Backend's per-concrete glue owns transitive
discharge, so `String`, `Vec String`, an ADT containing a Vec of ADTs, closures,
and recursive finite values all use the same one-call int protocol.

This is the int manifestation of **Single pipeline, mode parameters** and **No
interim implementations of later-ring capabilities**: there is no JIT-only
releaser, IO-only payload branch, display-owned dec, shallow fallback, or private
copy of backend's glue behavior.

### 1.1 Classification is a shared predicate, not an absence test

Backend's `request_if_owning` (`crates/cranelisp-backend/src/drop_glue.rs:69-80`)
returns `Ok(None)` — and therefore **emits no artifact row** — when
`HeapCategory::classify` says `NeverHeap | Value`. Absence from the projection is
consequently ambiguous on its face: it means either "this result needs no
release" or "the artifact is missing".

Int must therefore ask the *same* question **before** it demands a key, never
infer disposition from a keyed miss. `cranelisp_backend::heap::HeapCategory`
and its `classify` are already public (`crates/cranelisp-backend/public-api.txt:
397-403`), and int already depends on backend. The owner constructor:

1. obtains the **release key** — the `ConcreteType` the producer keyed on
   (§1.1.1), not a re-narrowing of the observed `Type`;
2. classifies **that key** with `HeapCategory::classify(&key,
   Some(symbol_tables))`;
3. `NeverHeap | Value` ⇒ the scalar/value arm; **no keyed lookup is attempted**;
4. `AlwaysHeap | Mixed` ⇒ the owning arm; a keyed miss is now unambiguously a
   hard error (§5).

`HeapCategory::Mixed` (a nullary-vs-boxed ADT) is an owning result: glue exists
for it and `guard_nullary` inside the glue body handles the bare-tag case. Int
does **not** replicate that guard.

Duplicating the predicate — an int-side "is this a heap type" list — is the
resolver-mirror class and is rejected (**Single source of truth**). If the
predicate's home ever moves to `cranelisp-types` (FIXME 0468's candidate), int
follows it; it does not fork it.

### 1.1.1 The release key is the producer's key — RATIFIED as-built (FIXME 0896)

**This subsection supersedes the S116 text's step-1 narrowing.** As authored,
§1.1 step 1 and §5's "missing/non-concrete type at typed exit" row required int
to narrow the **observed** static `Type` with `ConcreteType::from_type` and to
treat a narrowing failure as a hard invariant error. W4 implemented that
literally, and it was **falsified in implementation**. `/design` has verified
the as-built shape (`src/result_owner.rs::release_key` + `strip_io_head`) and
**ratifies it**; the rule below is the design of record.

> **The rule.** The release key is the **result-producing entry's `codegen_view`
> body `ConcreteType`** — the same value backend computed its `result_roots`
> from — with the `IO` head stripped by the same rule backend applies. Narrowing
> the observed `Type` with `ConcreteType::from_type` is the **fallback**, used
> only when the entry published no codegen view; a narrowing failure *there*
> keeps §5's hard located/invariant error, and its diagnostic names both the
> type and the absent codegen view.
>
> The invariant that carries the weight is **"int keys on what the producer
> keyed on"** — *not* "the observed display type is concrete".

**Why the literal rule was wrong — two independent grounds.**

1. **Its premise is falsified by spec-required displays, not by corner cases.**
   Not every clean typed-exit result type is concrete:

   | REPL input | observed `Type` | required display |
   |---|---|---|
   | `[]` | `(primitives/Vec t1)` | `:(Vec a) []` (`repl/spec.md` §1.5) |
   | `None` (prelude `Option`) | `(primitives/Option t2)` | `Option.None` (§4.1) |

   Under the literal rule both turned into `program result type ... is not
   concrete at the typed exit of module `user``, redding
   `repl_introspection::display_empty_vec_value` and
   `repl_introspection::prelude_option_none_value_display_neg_definition_metadata`.
   A rule that makes two spec-required displays into internal errors is not a
   safety rule; it is a wrong premise.

2. **It is a second derivation of a question backend already answered.** Backend
   keys the result-root pre-request off the compiled body's `MonoExpr` type
   (`compile_to_module`'s `result_roots`); for a body that is not strictly
   concrete that type comes from `MonoExpr::lenient_from_expr`, whose walk fills
   a non-concrete node with the `ConcreteType::Int` placeholder. So for `[]`
   backend's result root is `Int`, backend emits **no glue**, and an int-side
   re-narrowing of the observed type would either hard-error or demand a key
   backend never published. Either outcome is int reaching a **different verdict
   from the producer** — which is §4.1's "never re-derive backend's type
   encoding" rule applied to the *type* rather than only to the symbol spelling
   (**Resolve once**, **Single source of truth**).

Taking the key from the same read that produced the code pointer (§4.3) makes
int's classification agree with backend's `request_if_owning` **by
construction** instead of by agreement between two derivations.

**Recorded limitation — the lenient-view placeholder gap.** Under this rule an
unpinned `[]` (or a bare polymorphic `None`) at the REPL still **leaks its
allocation**: backend keyed that result root through the `lenient_from_expr`
`ConcreteType::Int` placeholder and therefore emitted no glue, and the owner
cannot release what was never emitted. Its status:

- it is **pre-existing** — exactly the pre-0745 behaviour for those inputs — so
  W4 introduces no regression, and it is not a result-owner defect;
- the owner is the **lenient view** (`MonoExpr::lenient_from_expr`, typecheck),
  not this design. Closing it is a separate row against the lenient view and
  wants `/qa` cover of its own; it is **out of int's bounded context** and
  outside this sprint's zero-delta fence (§10);
- the alternative — hard-erroring when the observed type is non-concrete, and
  making the producer emit glue for such roots — is **not adopted here** because
  it is a typecheck + backend change wearing an int-side error as its trigger.
  Int must not force a producer change by refusing to release what the producer
  published.

**Cross-reference — the strip rule's home is an open `/arch` question.** The
`IO a ⇒ a` strip this rule applies (`strip_io_head`) currently has **two literal
encodings**: int's and backend's inline map in `compile_to_module`. They agree
by text, not by shared derivation. **FIXME 0898 (`target: /arch`)** owns where
the single statement lives — the candidate home is `cranelisp-types` beside
`drop_glue_symbol_name`, which is a cross-crate/public-surface question this
design does not settle and must not pre-empt. Until 0898 rules, int's
`strip_io_head` is the int-side statement of a rule whose authority is
backend's; if 0898 lands a shared helper, int **calls** it and deletes its copy
— it does not keep a fork.

---

## 2. Representation and ownership states

The implementation should model the successful result as an int-private owner,
not continue passing a copyable `(i64, Type)` tuple through unrelated helpers.
The conceptual state machine is:

```text
DriverOutcome
  ├─ error/trap ───────────────────────────────> no result owner
  └─ clean + static Type
       -> OwnedProgramResult { value, concrete/value disposition, release target }
       -> observed (display or exit conversion)
       -> released/no-op
       -> consumed
```

`OwnedProgramResult` is an int-private representation; its exact Rust spelling is
for `/dev`, but these properties are binding:

- construction consumes the clean `ProgramOutcome` value and the carried source
  `Type`;
- `IO a` is unwrapped exactly once at construction, after the driver has
  transferred the `Pure` payload;
- the owning arm contains the resolved glue target and its code-lifetime guard;
  the scalar/value arm contains no callable target;
- observation borrows the value; finalization consumes the owner;
- there is one finalization chokepoint. Normal callers cannot copy the owned word
  or independently invoke the target;
- a defensive `Drop` backstop may release an armed owner during Rust unwinding,
  but it must share the same disarm-on-success state and call target. It is not a
  second normal release path.

This follows **Model invariants by representation** and **Published pointers have
retention owners**. A raw function address without its `Arc<Jit>`/`Arc<Linker>`
guard is not a valid release target.

---

## 3. One protocol, three target-resolution adapters

Target resolution varies only because the compiled code is housed differently.
The semantic owner and observe-then-release ordering do not vary.

### 3.0 The as-built turn lifecycle the owner attaches to (HEAD)

S117 W3a collapsed every mode onto one owned prepare→compile→publish
transaction. The seams, by name and line:

| Stage | Seam | Note |
|---|---|---|
| prepare | `worker::prepare_cluster_commit` (`src/worker.rs:399`), invoked from `process_form::finalize_cluster` (`src/process_form.rs:508`), carrier stored by `ProcessedCluster::set_prepared` (`:626`, `src/cluster.rs:114/223`) | pure w.r.t. live state |
| compile | `worker::compile_prepared_turn` (`src/worker.rs:1656`) → **one** `compile_to_module` for the whole batch (`:1702`); artifacts land on `PreparedCompilation` (`:36-44`, stored `:1728-1733`) | revalidates the slot cursor first (`:1661-1676`) |
| publish | `worker::publish_prepared_turn` (`src/worker.rs:1737`) — infallible; installs glue owners FIRST (`:1748-1758`), then cursor, retention, entries, products | no `Result` arm |
| drivers | eval: `src/eval.rs:384`; worker cadence: `src/worker.rs:2666`; redefinition transaction: `src/redefine.rs:1511`; all via `compile_and_publish_processed{,_without_notify}` (`src/worker.rs:1829/1844`) | one cadence, three callers |
| macro clause | `PreparedMacroTurn` (`src/process_form/macro_clause.rs:110`), `compile_batch` (`:126`), `publish` (`:175`) | a second, parallel prepared transaction — see §3.1.1 |

**The result owner attaches at neither prepare nor publish.** It is constructed
strictly *after* a published turn's code has been *executed* — at the two
execution seams (§3.1) — and it reads the already-published
`SharedState.fresh_jit_drop_glues` row. This is the load-bearing sequencing
fact: the S116 design's §4.1 worry ("the artifact projection must reach the int
compilation record and must not be discarded") is **already discharged by the
as-built publish gate**, so 0745 introduces no new coupling into the turn
transaction and cannot destabilise it.

> **Do not wire the owner into `worker::inline_jit_codegen_for_names`**
> (`src/worker.rs:1544`). It has no production caller at HEAD and it drops
> `CompilationArtifacts.drop_glues` on the floor (`:1636-1651` routes only
> `clif_ir`/`code_size`). Code wired there is dead. Its production-deadness is a
> Principle-7 cleanup candidate for `/dev`, tracked here as an observation, not
> as 0745 scope.

### 3.1 Fresh JIT (`--run`, REPL, and post-cache-miss)

Backend proactively emits exported glue for every concrete owning **result root**
of the compiled batch, including the inner `a` of `IO a`
(`crates/cranelisp-backend/src/lib.rs:672-699`), and projects the defined
registry into `CompilationArtifacts.drop_glues` with a finalized `jit_address`
(`:736`, `project_drop_glues` `:749-766`).

Int's consumption is already built; 0745 uses it:

1. `publish_prepared_turn` moves each `(ConcreteType → DropGlueArtifact)` row
   into `SharedState.fresh_jit_drop_glues` keyed `(module, ConcreteType)`,
   **paired with the batch's `Code::Jit` owner** (`FreshJitDropGlue`,
   `src/worker.rs:46-51`). Owner installation precedes every entry publication
   in the same gate (Principle 22).
2. At result-owner construction, int narrows and classifies (§1.1), then
   performs **one** `fresh_jit_drop_glues.get(&(module, key))`.
3. The row is cloned whole — artifact **and** owner. The clone is the retention
   root; the raw `jit_address` is never stored without it.
4. Absence, `artifact.symbol != drop_glue_symbol_name(&module, &key)`, or
   `jit_address: None` on a fresh-JIT result is a hard integration error before
   observation ownership can be lost. There is no symbol scan and no
   compile-after-the-fact fallback.
5. Display/convert while the cloned owner is live; call the address; drop the
   clone only after the call returns.

`--run` and REPL consume the same target construction. Their only difference is
the observation callback: exit conversion versus `result_value_doc` rendering.

The `(module, ConcreteType)` key is the **emitting** module — the module whose
`compile_to_module` produced the glue, which for a result root is the module that
owns `main` / `__expr`. Int never derives a key from a source expression or from
the most recently compiled function.

#### 3.1.1 Two writers, one map

Both `publish_prepared_turn` and `PreparedMacroTurn::publish` write
`fresh_jit_drop_glues`, each inserting `{artifact, owner}` as one value. That is
sufficient and must stay so: **a row is replaced pair-atomically or not at all.**
A shape that updated the artifact and the owner separately would let an old
address pair with a new JIT. `/review` rejects any third writer, and any writer
that does not carry its own owner.

### 3.2 Cache-hit execution

A cache hit obtains no process-local address from serialized metadata. The
object already contains the exported glue body — `Linkage::Export`
(`drop_glue.rs:86-92`) emitted through the same `compile_to_module` the object
path uses (`src/session_v4/nice_worker.rs:317-319`). Int:

1. derives the same canonical symbol using
   `cranelisp_types::drop_glue_symbol_name(&module, &concrete_type)` (public,
   `cranelisp-types/public-api.txt:1849`);
2. resolves it once with `Linker::get_symbol` (public,
   `cranelisp-backend/public-api.txt:30`);
3. obtains the `Arc<Linker>` from the **result-producing entry's own `Code`** —
   `Code::Linker(Arc<Linker>)` is a public tuple variant, installed on every
   cache-restored entry at `src/worker.rs:2274-2289`. This is the unifying rule
   across §3.1/§3.2: **the release target's retention owner is the same `Code`
   that owns the code which produced the result.** It needs no new session map;
   `cache::load_cached_object`'s `fn_addrs` deliberately contains only
   callable-slot symbols (`crates/cranelisp-backend/src/cache/mod.rs:590-598`),
   so glue is resolved on demand, not pre-tabulated;
4. runs the identical observe-then-release owner.

Missing symbols are cache-load failures, not cache misses repaired by generating
private glue. No address or drop-glue map is serialized, so this design adds no
cache-schema bump — consistent with S118's one-schema-window fence (arch ruling
1; the 23→24 window belongs to 0869).

**Cross-version safety is already structural**: `BUILD_ID` is stamped by
`build.rs` and a mismatch invalidates the cache
(`crates/cranelisp-backend/CLAUDE.md` §Cache), so an object produced by a binary
that predates the glue registry can never be read by one that expects the symbol.
"Missing glue symbol on cache hit" is therefore a genuine defect signal, not a
version-skew nuisance to be softened.

#### 3.2.1 As-built: design-mandated, production-unreached — KEEP AS SPECIFIED

W4 built this adapter as designed and then established that **no production path
reaches it at HEAD**: `try_cache_hit_load` only ever restores **dependency**
modules (every call site is in `src/process_form/dependency.rs`), never the CLI
target, so the result-producing entry — `main` or `__expr` — always carries
`Code::Jit`. The unit matrix's row-3 cells are currently the only tier that
exercises it.

**`/design`'s call (S118 W4+): keep it as specified, guarded by the §6 row-3
unit tier. It is not marked future-facing and it is not deleted.** Grounds:

1. **It is not speculative generality — it is the other half of a rule this
   design already states.** §3.2 step 3's unifying rule ("the release target's
   retention owner is the same `Code` that owns the code which produced the
   result") is what makes the fresh-JIT adapter's row read *safe*. With the
   `Code::Linker` arm removed, that rule would have exactly one implemented arm
   and the selector would need a no-release or wrong-row fallback for the other
   — the two failure shapes §5 forbids. **Enforce invariants structurally**: the
   selector is exhaustive over `Code` *because* every housing has an adapter.
2. **The reach is a scheduling fact, not a design fact, and it is expected to
   move.** Widening cache restoration to the CLI target is a live trajectory
   (`cache-hit-loading.md`); the day it lands, the adapter's absence would be a
   silent no-release on the entry module's result — a leak with no diagnostic.
   Building it later, under a defect, is the **No interim implementations**
   anti-pattern this project has paid for before.
3. **The cost is bounded and the tier is honest.** It is one keyed symbol
   resolution plus a null check, fully unit-covered. What the design owes is not
   deletion but *truthfulness*: it is recorded here as production-unreached so
   `/review` does not read the unreached path as drift, and so nobody mistakes
   the unit rows for e2e evidence — **no e2e exercises this adapter today**.

The obligation this creates: when cache restoration does widen to the CLI
target, the widening change-set owes an e2e that observes a cache-hit result
released exactly once (`/qa` row), because that is the moment the unit tier stops
being the whole story.

### 3.3 Linked startup

The generated startup stub knows `main`'s concrete result type at object
emission. `link_by_name` (`src/session_v4/lifecycle.rs:2069`) already holds the
entry table, already runs `validate_main` (`:2095`) — which guarantees
`main : (Fn [] (IO _))`, hence `main_returns_io = true` unconditionally
(`:2119`) — and already reads `main`'s scheme to derive the GOT slot (`:2114`).
The inner `a` comes from the same scheme by the same read.

`link_by_name` therefore:

1. projects `main`'s scheme to the inner result `Type`, narrows it with
   `ConcreteType::from_type`, and classifies it (§1.1);
2. for a `NeverHeap | Value` inner type, passes no release symbol — the stub is
   byte-identical to today's;
3. for an owning inner type, passes
   `drop_glue_symbol_name(entry_module, inner)` into
   `crate::exe::generate_startup_object` (`src/exe.rs:50`, called at
   `lifecycle.rs:2162`) as one new `Option<LinkerSymbol>` parameter. `exe.rs` is
   int-private and a binary has no `public-api.txt`, so this is a zero-boundary
   change;
4. a non-concrete inner type is a **located link-time error** naming the module
   and the type — never a silent skip.

`declare_runtime_imports` gains the conditional `Linkage::Import` declaration of
that symbol with signature `(i64) -> ()`. `build_startup_func`
(`src/exe.rs:371-478`) keeps its shape; the clean block's required order becomes:

1. retain the driver's `exit_code_i64` (`:447`) as the owned result word;
2. compute the process `i32` exit code while the word is live (`ireduce`,
   `:476`);
3. for an owning result, `call` the relocated `extern "C" fn(i64)` glue once with
   `exit_code_i64`;
4. `call exit(computed_code)` (`:477-478`).

The error block (`:453-467`, the `check_runtime_error` path) does **not** call
result glue: `ProgramOutcome` carries no successful result on `error_kind != 0`.
The defining module object supplies the exported body — the entry module's `.o`
carries it, because the object path runs the same result-root pre-request — and
the system linker resolves the relocation. The startup object owns no Rust
`Arc`; ordinary executable text lifetime keeps both caller and relocated glue
live until `exit`. The exe-bundle must continue force-linking the
intrinsic/runtime dependencies the generated glue calls (`runtime/dealloc`,
`runtime/vec_drop`), but it defines no wrapper releaser and does not interpret
the result type.

---

## 4. Integration seams and data flow

### 4.1 Compilation-artifact routing — already landed, do not rebuild

The S116 obligation ("the fresh-JIT artifact projection must reach the int
compilation record that installs `Code::Jit`; it must not be discarded") is
**satisfied at HEAD** by `compile_prepared_turn` → `PreparedCompilation.
drop_glues` → `publish_prepared_turn` → `SharedState.fresh_jit_drop_glues`. The
association is `(module, ConcreteType) → {artifact, owner}`, not a source
expression and not the most recently compiled function, exactly as §4 required.

What 0745 owes here is therefore **consumption discipline**, not plumbing:

- **read once**, at owner construction, never at display time;
- **clone the pair**, never the address alone;
- **never re-derive** backend's type encoding; the symbol comes from the
  artifact (fresh JIT) or from `drop_glue_symbol_name` (cache/link) — the ONE
  types-owned grammar.

This applies **Resolve once** and **Single source of truth**.

Repeated compilation replaces a row together with its owner (§3.1.1). An armed
owner is unaffected: it holds a clone of the `Code` it captured, so the old JIT
pages stay mapped until the owner is consumed even if the map row has since been
replaced. This is the concurrency-safety property that makes the session-global
map acceptable (§7).

### 4.2 REPL value lifetime

The as-built chain is:

```text
eval.rs:534  execute_compiled_expr
  -> pipeline.rs:146  cranelisp_run_program(got_addr, ty.is_io())
  -> pipeline.rs:181  program_outcome_to_result  --(clean)-->  ExprOutcome::Value { value, ty }   (:228)
  -> eval.rs:539      EvalResult::Val { value, ty, warnings }
  ~~~~ returns to the REPL driver ~~~~
  -> repl/format.rs:600  EvalResult::Val arm
  -> display.rs:73/78    result_value_doc(value, ty, symbol_tables)   [reads the value]
```

`ExprOutcome::Value` / `EvalResult::Val` separate execution from later
formatting. The owned result must therefore remain **armed across that
boundary**, or the formatting operation must move inside an owner-consuming
helper. Either shape is acceptable only if the type, target, and lifetime guard
travel together and `format_eval_result*` cannot silently copy the owned word.

Formatting reads the value first. The release occurs after the complete
`StyledDoc` has been built, before control returns to the prompt. Bare
symbol/definition displays and display-only values that did not come from a
clean executed result do not fabricate ownership.

**As-built (S118 W4) — the second IO owner is gone, not merely unreached
(P20).** The S116 text asked that `repl/format.rs`'s defensive `ty.is_io()`
branch "must not *become* a second IO/result owner" and rested on it being
documented-unreachable. That branch **already was one**: it re-drove
`cranelisp_run_io` on the displayed word and rendered the inner value. W4
**deleted** it, and the shape that replaces the prose guarantee is structural —
`OwnedProgramResult::new` **refuses** an `IO a` type outright, so the single
unwrap at the driver boundary (`pipeline::program_outcome_to_result`'s clean
arm) is the only one there can be. A second IO owner is now *unconstructable*
rather than unreachable-by-convention (**Model invariants by representation**),
and the formatter's replacement comment (`src/repl/format.rs`, the
`EvalResult::Val` arm) carries that statement at the site. Do not reintroduce an
`is_io` branch in any formatter; a future direct caller enters the same owner
constructor, which will reject an un-unwrapped `IO a` for it.

**S117 W3b does not touch this path.** W3b's changes are the scheme renderer and
the impl-drawer/definition-display leaves (`s117-conformance-recovery.md`
§4/§5 → `repl/format_type.rs`, `format_scheme_type`); the `EvalResult::Val` →
`result_value_doc` value path is untouched, so §4.2 needs no reconciliation
beyond the line citations above.

### 4.3 Run lifetime

`CompilerSession::trampoline` (`src/session_v4/lifecycle.rs:1535`) returns
`(i64, Type)` from its clean arm (`:1616-1623`) after `cranelisp_run_program`
(`:1576`). `main.rs`'s Run arm (`src/main.rs:323-337`) currently does:

```text
trampoline -> wait_object_complete -> shutdown -> compute exit code -> flush -> exit
```

The binding order becomes **observe → release → object-wait/shutdown → trace
flush → exit**: the exit-code conversion and the release both move *ahead* of
`s.shutdown()`. `trampoline` returns an owned result rather than a free-standing
tuple; `main` computes the exit code through its observation API and finalizes
the result before any teardown.

**Correction to S116.** The S116 text justified this ordering with "shutdown may
remove the final `Code::Jit`/`Code::Linker` retention root". At HEAD that is
false: `shutdown` (`lifecycle.rs:1762-1800`) settles the importable index, stops
the scheduler and joins the worker pool — it drops no symbol table and no
`Code`, and `process::exit` bypasses `Drop` anyway. The ordering rule is retained
because it is free and because it is the shape that stays correct if `shutdown`
ever acquires teardown responsibilities; it is **not** load-bearing against a
live hazard today, and `/review` should not treat a reordering finding here as a
memory-safety Blocker.

`lookup_main_return_type` (`lifecycle.rs:1659-1671`) falls back to `Type::Int`
when the entry is absent. That fallback must not reach the owner constructor as
an authoritative classification: `lookup_main_code_ptr` errors first on an absent
`main`, so the path is unreachable — but the owner constructor takes the type
from the same read that produced the code pointer, not from a second lookup.

**The same-read rule extends to the release key (§1.1.1, ratified).** The key is
read off the result-producing entry's `codegen_view` in the *same* pass that
produces the code pointer — as built, `entry.codegen_view().map(|view|
view.body.ty().clone())` at each of the three seams that construct an owner or a
startup exit (`src/pipeline.rs:105` for REPL/expression execution,
`src/session_v4/lifecycle.rs:1724` for `--run`, `:2183` for `link_by_name`). The
observed static `Type` still travels with the owner — it is what observation
formats and what `result_is_exit_code` reads — but it is **not** the release
key's authority, only its fallback. A future seam that acquires a result owner
acquires the key the same way; a second lookup keyed on anything else is the
drift this rule exists to prevent.

The `IO a ⇒ a` strip applied to that key is the same rule backend applies to its
result roots. **Where that rule's single statement should live is FIXME 0898's
open `/arch` question**, not this design's (§1.1.1, last paragraph).

### 4.4 `Pure` and non-IO results

`cranelisp_run_program` owns known IO protocol nodes. For `Pure payload`,
`drive_io` returns the payload and `consume_io_tree` frees the outer IO box
without freeing that opaque field; ownership transfers to the int result owner
(FIXME 0745's Evidence 2, re-verified: the intrinsics side is coherent and is
NOT the seam). The result owner therefore selects glue for `a`, never glue for
`IO a` and never an intrinsics `consume_*` function.

Non-IO expression execution enters the same clean-result constructor with its
own result type. This prevents an IO-only 0745 patch and makes REPL evaluation
and entry-main execution obey one typed-context rule.

---

## 5. Exact-once and error-path rules

| Event | Result ownership disposition |
|---|---|
| clean scalar/value result (§1.1 classification) | observe; release is a typed no-op; consume owner; **no keyed lookup attempted** |
| clean owning result | observe completely; invoke target once; disarm |
| display/exit conversion returns an error | finalize through the same target before propagating, or unwind through the armed backstop |
| driver runtime trap (`error_kind == 1`) / dispatch fault (`== 2`) | no successful result owner; no result glue call |
| no release key obtainable at typed exit — the entry published no `codegen_view` **and** the observed `Type` does not narrow (§1.1.1) | hard located/invariant error naming the type *and* the absent codegen view, while the owner remains armed; never shallow release or silent leak. A non-concrete **observed** type is by itself NOT this row: the key comes from the producer, and `(Vec t1)`/`(Option t2)` displays are spec-required |
| owning type absent from `fresh_jit_drop_glues` | hard integration error; no ambient scan, no late compilation |
| `jit_address: None` on a fresh-JIT owning result | hard integration error (object-mode polarity leaking into a JIT path) |
| `jit_address: Some(0)` on a fresh-JIT owning result, or a null `Linker::get_symbol` resolution on a cache-hit one | hard integration error at **each adapter's own safe boundary**, before a `GlueTarget` exists (FIXME 0897) — never a `None`/skip. This is what lets the sole `unsafe` block assert non-null |
| `artifact.symbol` disagrees with `drop_glue_symbol_name(module, key)` | hard integration error naming both spellings |
| cache-hit `Linker::get_symbol` miss | hard cache-load error; never private glue synthesis |
| link-time non-concrete inner result type | located link error naming module + type |
| glue call traps | propagate/abort as safety failure; never retry |
| session shutdown / REPL redefinition / map-row replacement | cannot invalidate a target held by an armed owner's cloned `Code` guard |

The release call owns its input. After it begins, the caller must not inspect,
format, convert, or release the word again.

---

## 6. Unit-test design: submodule × complexity/edge/negative matrix

Tests mirror module composition (**Tests mirror module composition**). `/dev`
places unit tests beside the owner and uses test doubles for observation and glue
invocation; exe-bundle/link correctness remains e2e where relocation is the fact.

| Submodule (home) | Complexity / positive | Edge | Negative |
|---|---|---|---|
| owner constructor + classification (`src/pipeline.rs` or a new `src/result_owner.rs`) | `Int` no-op; `String` release; `IO String` selects `String`; nested ADT/Vec key; **the `codegen_view` key wins over the observed type** and its `IO` head is stripped (§1.1.1) | non-IO expression; `Pure` inner typing; value `0` as a valid owned word; `HeapCategory::Mixed` nullary tag | non-concrete `Type` **with no codegen view** (the fallback's hard error); owning type with no keyed target; **never** select `IO a` glue; scalar arm performs zero map reads |
| fresh-JIT target resolution (`src/worker.rs` `FreshJitDropGlue` consumers) | keyed `String` and nested-type rows pair with `Code::Jit`; owner clone outlives the call | two types in one batch; repeat key; recompilation replaces address **and** owner together | the **four** hard-error polarities — absent key; `jit_address: None`; **null (`Some(0)`) address**; symbol/key mismatch — plus: raw address stored without its guard |
| cache-hit resolution (`src/worker.rs:2274` neighbourhood) | canonical symbol resolves via the result-entry's `Code::Linker(Arc<Linker>)` | warm cache; two module-qualified copies of the same concrete type | missing symbol fails hard; no scan; no serialized/process-local address fallback; no `Code::Jit` row consulted on a Linker result |
| REPL display (`src/eval.rs:539` → `src/repl/format.rs:600` → `src/display.rs:78`) | scalar, `String`, nested payload displayed before one release | formatter returns error / unwinds; warning envelope; result value `0` | no release before the final display read; no double release after formatting; display-only `Def`/bare-symbol path releases nothing; the `is_io` defensive branch constructs no second owner |
| run arm + lifecycle (`src/main.rs:323` / `lifecycle.rs:1535`) | `IO Int` converts then releases; `IO String` converts `0` then releases | nested payload; both JIT and cache-hit retention; shutdown after release | shutdown-before-release rejected; trap/fault invokes no result glue; glue never retried; `lookup_main_return_type`'s `Int` fallback never authoritative |
| startup CLIF (`src/exe.rs:50/371`) | scalar omits the call entirely (byte-identical stub); owning `IO a` — conversion precedes the relocated call, which precedes `exit` | `Int` owning wrapper vs scalar `Int`; nested concrete type; module qualification in the symbol | error block emits no release; no call after `exit`; missing relocation is a link failure; no JIT/private helper; non-concrete inner type errors at `link_by_name` |
| exe-bundle contract (`crates/cranelisp-exe-bundle`) | generated glue's intrinsic dependencies stay force-linked | no-platform program; release strictly before process exit | no exe-bundle generic releaser or result-type switch; missing dependency fails linked e2e |

Ordering tests use a recorded event sequence such as
`observe-start → observe-read → observe-done → glue(value) → guard-drop`; counter
tests assert glue is called exactly once. Type tests assert the exact
`ConcreteType` key and module-qualified `LinkerSymbol`, not merely that some
function pointer was called.

**Non-null is an adapter obligation; the constructor's assert is a detector, not
a gate.** Both runtime adapters reject a null address at their own **safe**
boundary with a located diagnostic — `fresh_jit_target`'s `Some(0)` polarity and
`resolve_cached`'s `is_null` check (FIXME 0897) — because the address is the
sole input to the module's one `transmute`, and a narrowing carries its check
(**Narrowing carries its check**; **Enforce invariants structurally**). The
`debug_assert_ne!` in `GlueTarget::new` is the **tier-3 backstop**: a debug-tier
detector for a future third adapter that forgets, matching the convention
already stated for `force_enroll` (`src/CLAUDE.md` §redefine invariants). It is
**not** a gate — in a `debug_assertions`-off build it is not evaluated, there is
no release fallback, and so it has no polarity to invert. A new adapter must
reject at its own boundary and must not lean on it; the negative unit row for a
null address must discriminate the *adapter's* located error, not the
`debug_assert`.

---

## 7. Quality attributes

- **Simplicity / maintainability:** one owner state machine and one release-target
  representation; three small resolution adapters reflect real code-housing
  differences. Int contains no value-layout traversal and no second heap-type
  predicate (§1.1).
- **Observability:** target-resolution errors name module, concrete type, expected
  symbol, and mode. Debug assertions and event-order unit tests make early
  release, lost ownership, and retention loss attributable at the seam. No new
  trace sink or ring buffer is introduced (`observability.md` unchanged).
- **Concurrency-safety — CORRECTED.** S116 claimed "no global address map is
  introduced". S117 introduced one, and it is the right shape. The binding
  invariants are now: (a) `fresh_jit_drop_glues` rows are `{artifact, owner}`
  pairs replaced atomically by exactly the two publish gates (§3.1.1); (b) result
  owners are turn-local and hold a **clone** of the retention `Code`, so
  recompilation cannot invalidate an armed owner; (c) no other writer exists, and
  the map is never read except at owner construction.
- **Performance:** one keyed lookup at owner construction and one glue call at
  final release. Scalar/value results remain call-free and perform zero map
  reads. No global registry walk, type scan, or depth-proportional int work. The
  map grows with distinct `(module, owning ConcreteType)` pairs compiled in the
  session — bounded by the same order as the existing retention pool.
- **Testability:** observation and release are separable callbacks behind an
  int-private owner, so ordering, exact-once behavior, and error cleanup are
  unit-testable without constructing the full compiler (**Testability is
  structural**).
- **Untouched this sprint:** int's compiler-internal concurrency architecture
  (`concurrency-architecture.md`), the scheduler/cadence model, and the
  observability sinks. 0745 changes result lifetime, target resolution, REPL
  display ownership, and linked-startup ordering only.

---

## 8. Serial implementation order

One `/dev` deployment, serial slices. Each slice is independently reviewable; no
slice leaves a partial release path reachable.

**Precondition — gated on backend slice S0 only.** `transitive-drop-glue.md`
§7.0's registry reshape moves `finish()` after body compilation. That change is
behaviour-neutral for result roots (they are pre-requested before bodies either
way, §0 item 5), so I0–I2 may proceed in parallel with backend S0–S1; **I3
onward should land after backend S0** so the acceptance runs against the final
projection shape. The Track-B wave order (`SPRINT.md` W3 backend → W4 int) already
provides this.

| # | Slice | Content | Exit |
|---|---|---|---|
| **I0** | Classification + owner skeleton | The int-private `OwnedProgramResult` with construction, observation-borrow, consuming finalize, disarm-on-success, and the `Drop` backstop. `HeapCategory`-based classification (§1.1). Scalar arm complete; owning arm's target resolution stubbed behind one private trait/enum. | Unit rows 1 of §6; zero behaviour change (every result is currently scalar-armed or unarmed) |
| **I1** | Fresh-JIT adapter | `fresh_jit_drop_glues` keyed read; pair clone; the **four** hard-error polarities (absent row; `jit_address: None`; null `Some(0)` address; symbol/key mismatch). | Unit rows 2; still no call site wired |
| **I2** | Cache-hit adapter | `drop_glue_symbol_name` + `Linker::get_symbol` off the result entry's `Code::Linker`, plus its null-resolution rejection. **Production-unreached at HEAD and kept as specified — §3.2.1.** | Unit rows 3 (the only tier that reaches it) |
| **I3** | Run arm | `trampoline` returns the owner; `main.rs` observes → releases → waits/shuts down → flushes → exits. | REDs #15, #16 flip (`--run`, both toggles) |
| **I4** | REPL arm | Owner armed across `EvalResult::Val`; release after the `StyledDoc` is built. | RED #18 flips |
| **I5** | Linked startup | `link_by_name` derives the inner concrete type + symbol; `generate_startup_object` gains the optional release symbol; `build_startup_func` emits convert → glue → exit. | RED #17 flips |

Slices I3/I4/I5 each carry their own armed-detector acceptance leg (§9).

**Rejected orderings.** Doing I5 first (the "smallest CLIF" instinct) is wrong:
the linked path is the only one with no unit tier and no keyed-miss diagnostics,
so a shared-classification bug surfaces there as a link error with no
attribution. Doing I3/I4/I5 as one change-set is rejected: three REDs flipping
together removes the per-mode attribution that `mode-divergence` defects need.

---

## 9. Acceptance mapping

### 9.1 The flip set

Four committed failing-not-ignored cells (`tests/plan/s118-test-plan.md` §2.1
rows 15–18):

| Cell | Mode | Flips at |
|---|---|---|
| `adt_drop_glue_underkey::entry_main_ioresult_heap_payload_toggle_off_leak_r2` (#15) | `--run`, `CRANELISP_NO_OWNERSHIP=1` | I3 |
| `program_result_owner_s116::run_nested_pure_payload_observed_then_released_both_toggles` (#16) | `--run`, both toggles | I3 |
| `program_result_owner_s116::linked_nested_pure_payload_converts_then_releases` (#17) | `--link` | I5 |
| `program_result_owner_s116::repl_nested_heap_value_displays_before_exact_release` (#18) | REPL | I4 |

Green control that must stay green:
`program_result_owner_s116::scalar_pure_result_exit_conversion_control_green`
(the scalar arm must remain call-free — §1.1 step 3).

**`/testing` rider — DISCHARGED at W4** (cell #15 was re-locused in the flipping
change-set, with the falsification below named). Retained as the record of why.
As authored, cell #15's `// defect:` line read
`locus=crates/cranelisp-backend compiler/rc_emission.rs::protect_return_value`
(`tests/adt_drop_glue_underkey.rs:258`). Both mechanisms at that locus are
falsified; the locus is the int result-value lifetime seam. Re-locusing is
`/testing`'s edit, owed with (not after) the flip — otherwise the `locus=`
hotspot analysis keeps mis-attributing this defect to backend.

### 9.2 Armed-detector re-demonstration (QA §4.1 — the acceptance leg)

Per `tests/plan/s118-test-plan.md` §4.1, each Track-B fix wave must demonstrate
its flips **under armed detectors**, not by symptom absence. For this wave:

- `/dev`'s acceptance run for **each** of I3, I4, I5 re-runs that slice's flipped
  cell's program in a **child process** with M1+M2+M3 armed and shows a clean
  exit;
- arming is **subprocess-scoped only** — child `Command` + `.env(…)`, never
  suite-scope export and never `std::env::set_var` (QA §1, structural; a
  suite-global M3 aborts every still-red leak guard). `/testing`'s W1 static gate
  greps for violations;
- this is an **acceptance-run obligation, not a new committed-cell family**. The
  four cells stay unarmed/deterministic;
- the armed legs may only be believed after Track A's detection proofs land
  (arch ruling 3 / FIXME 0768: an unproven detector is not evidence). Sequencing
  is already satisfied by W2 → W3 → W4.

### 9.3 Consequents and non-goals

- Cells #19–#21 (`conj` ×2, exemplar residue) are **backend** consequents
  (`transitive-drop-glue.md` §7.5); they are not this wave's flips and must not
  be patched here.
- A cell that goes green without its owning slice landing is treated with
  suspicion (QA §2.4, S98 rule): the flip must trace to the mechanism.
- No new e2e is owed (QA §4.1 typed-context-exits row: "cells #15–#18 …
  `/dev`(int/exe-bundle) unit matrix per `result-owner.md` §6; no new e2e
  owed"). The §6 matrix is the owed tier.
- FIXME 0875 (exemplar standalone-`--link` unresolved Rust symbols) is
  **adjacent but separate**: QA §8 sequences its symbol-inventory attribution
  into W5, *after* I5 lands, precisely because I5 changes the link path. `/dev`
  must not fold a speculative exe-bundle force-link change into I5 to chase it.

---

## 10. Interface and schema verification (HEAD)

Every input this design needs is already public; the change is int-private.

| Need | Home | Status |
|---|---|---|
| `CompilationArtifacts.drop_glues` / `DropGlueArtifact{symbol, jit_address}` | `cranelisp-backend` | public (`public-api.txt:544/552-554`) |
| `HeapCategory` + `classify` | `cranelisp-backend::heap` | public (`:397-403`) |
| `Linker::get_symbol` | `cranelisp-backend::cache::linker` | public (`:30`) |
| `Code::Jit(Arc<Jit>)` / `Code::Linker(Arc<Linker>)` | `cranelisp-backend` | public tuple variants |
| `drop_glue_symbol_name` | `cranelisp-types` | public (`:1849`) |
| `ConcreteType::from_type` | `cranelisp-types` | public |
| `SharedState.fresh_jit_drop_glues`, `FreshJitDropGlue` | `src/` | int-private, landed S117 |
| `generate_startup_object` | `src/exe.rs` | int-private; binary has no `public-api.txt` |

**Zero deltas:** no `cranelisp-types` change, no crate `public-api.txt` change,
no `CACHE_SCHEMA_VERSION` change (S118's single 23→24 window belongs to 0869 —
arch ruling 1 / QA §1), no new backend entry point, no ABI change, no
`cranelisp-exe-bundle` API change. If implementation discovers a needed public
change, that is a **STOP** and a FIXME `target: /arch`, not a widening.

---

## 11. Sequencing against FIXME 0863 (arch ruling 11)

0863 (the cluster-wide prepared macro-presentation transaction) reopens the same
`src/` publication seam this design attaches to. Arch ruling 11 serializes it as
a **later wave**, after 0745. The constraint, from this side:

- 0745 does **not** modify `prepare_cluster_commit`, `compile_prepared_turn`, or
  `publish_prepared_turn`; it reads the map those seams already populate (§3.0).
  It therefore leaves 0863's foundation exactly as 0863's design found it;
- 0863's wave rebases its reading of the turn transaction on the **post-0745**
  state, which for the transaction itself is unchanged;
- the one point of contact is `PreparedMacroTurn::publish`'s write to
  `fresh_jit_drop_glues` (`macro_clause.rs:182-187`). When 0863 makes the macro
  clause turn **absorbable** by the parent rather than self-publishing, those
  rows must move into the parent's publish gate **as pairs**, preserving §3.1.1.
  This is recorded as a delta note in `s117-conformance-recovery.md` §6.

---

## Next skills

**Implementation is complete** (§8's I0–I5 landed `fc3375f9..16a26408`; the four
§9.1 cells flipped; W4 gate PASS; FIXME 0745 CLOSED). What remains:

- `/arch` — FIXME 0898: rule where the `IO a ⇒ a` result-root strip rule's
  single statement lives (§1.1.1's last paragraph). Int calls the shared helper
  and deletes its copy the moment one exists; it does not keep a fork.
- `/dev` (int/exe-bundle) — stale-citation sweep: `src/result_owner.rs`'s
  `release_key` rustdoc and `src/CLAUDE.md` §"Program-result ownership" both
  cite the retired number **0892**; the ruling is **0896** and now lives in
  §1.1.1. `/design` does not edit source.
- `/design` (typecheck) — the recorded limitation in §1.1.1: the lenient view's
  `ConcreteType::Int` placeholder is why an unpinned `[]` / bare `None` result
  still leaks. It is a lenient-view row, not a result-owner row.
- `/qa` — cover for that lenient-view row when it is scheduled; and the §3.2.1
  obligation: an e2e for the cache-hit adapter is owed **by the change-set that
  widens cache restoration to the CLI target**, not before.
- `/review` (int/exe-bundle) — standing rejects for any future change here: raw
  unguarded addresses; a null address reaching `GlueTarget::new` from a new
  adapter; a second heap-type predicate; a re-narrowing of the observed type as
  the release key (§1.1.1); display-before/after ordering inversions; IO-only or
  JIT-only release; a reintroduced formatter `is_io` branch; any private deep
  releaser; a third `fresh_jit_drop_glues` writer or a non-pair row update; any
  wiring into the production-dead `inline_jit_codegen_for_names`.
- `/sprint` — 0863's wave stays sequenced after this one per arch ruling 11;
  0875's attribution is unblocked (I5 has landed).
