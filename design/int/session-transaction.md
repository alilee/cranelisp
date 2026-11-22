# Session transaction — guarded redefinition, slot versioning and retention

Owner: `design` (int). Subordinate to `int.md` §8.6. Normative surface:
`repl/spec/18-redefinition.md` §18 and, for reload,
`repl/spec/14-file-watching.md` §14. This document owns the slot, retention
and persistence mechanics and the whole-file rebuild of a reloaded module
([§7.3](#73-the-watcher-and-reload-path)). The REPL-turn instance
rematerialization cadence around them is `design/int/s122-closure.md` §2.
Section numbers are pinned by live source comments and tests; keep them
stable.

## §0. The model

Redefinition is a guarded publication inside the ordinary prepared transaction:

1. The proposed cluster checks into unpublished staging.
2. Before any live change, the guard rejects a structurally different
   redeclaration of a live nominal type (§2.6). `redefine::validate_guarded_redefinition`
   then rejects a declaration-class change, a visibility change and a callable
   language-type change with a blocking dependent (§3). Inferred ownership
   modes are not compared (§2.4).
3. An admitted generic base or overload family rematerializes its prior
   concrete instances into the same candidate (`design/int/s122-closure.md` §2).
4. The commit gate classifies each published callable (§2) and applies the slot
   policy (§7); every displaced compiled owner enters the retention pool (§6).

A rejected redefinition leaves the complete prior definition live and its
backing source unchanged. **No ordinary callable redefinition re-typechecks or
recompiles a dependent, marks a symbol broken or installs a trap stub.**

A reload of a saved file is not a redefinition. It rebuilds the module from a
fresh table and recompiles or locks its dependents (§7.3).

The S101–S103 dependent-recompilation transaction, its broken symbols and trap
stubs, its cascade and `stale:` reports and its end-of-turn module reload were
deleted from `src/` in S123 (§5.2). Git retains them.

---

## §1. Actors

| Actor | Function | Anchor |
|---|---|---|
| **REPL turn (eval thread)** | Sole driver of an interactive redefinition: submits the cluster, waits for publication, renders the result. The entry module never enters `TypecheckBlocked`. | `src/eval.rs` |
| **Redefinition guard** | Admission decision over staging versus live, before planning or codegen. | `redefine::validate_guarded_redefinition`, called from `worker::validate_guarded_staging` |
| **Blocking-dependent scan** | Derived on demand from committed `callees` (§3). | `redefine::blocking_dependents` |
| **Commit gate** | Classifies each published callable (`RedefKind`) and applies the one slot policy; returns displaced owners. The single slot-policy authority (§7.1). | `worker::commit_staging_to_live` and the prepared compiled publication |
| **Retention pool** | Session-lifetime owner of every displaced compiled `Code` (§6). | `SharedState.retained_code: redefine::RetentionPool` |
| **GOT** | Per-slot atomic commit substrate; slot identity carries ABI identity (§7). | types-owned mint; `got.store_slot` |
| **Persistence writers** | Backing-file regeneration and nice-worker `.o`/`.meta` writes (§8). | `session_v4::lifecycle::regenerate_backing_file`; `session_v4::nice_worker::compile_module_object` |
| **Heap and runtime cadence** | What publication cannot reach: heap closures holding code pointers, suspended IO continuations, detached strands, in-flight frames. §6 and §7 exist because of them. | — |

---

## §2. Classification at the commit gate

### 2.1 Where it runs

The staging→live commit classifies every staged callable against the prior live
binding under the same name:

| `RedefKind` | Meaning | Slot |
|---|---|---|
| `New` | No prior live callable, or a slot-less prior (a template replaced) | fresh mint |
| `AbiPreserving` | Prior exists with the same language type | reuse and patch in place |
| `AbiChanging` | Prior exists with a different language type | fresh mint; old slot frozen |

The gate runs at the commit because the slot decision must precede codegen that
embeds slot indices. The slot policy and the rematerialization check read
`classify_redefinition` directly. No classification leaves the commit: nothing
runs after publication on its account (§5.2).

### 2.2 The comparand

The comparand is the callable's **language type**: `redefine::LanguageType`, an
alpha-canonical rendering of the fully resolved scheme and its constraints,
compared across the complete signature set of an overload family. Raw schemes
must not be compared, because two checks of the same source assign different
type-variable ids. Documentation, parameter names and the body are not part of
it. Visibility and declaration class are checked by the guard, not the
comparand. Macro, gate-exempt internal and slot-less-prior shapes classify
without a language-type comparison.

### 2.3 Body-only cost

A same-language-type redefinition pays one comparison and the in-place slot
patch. Existing callers and captured callable values reach the new body at
their next call through the slot they already embed.

### 2.4 Ownership modes are not compared

A same-language-type replacement publishes in place whatever its inferred
ownership modes (REPL §18.1, user ruling 2026-11-16). Under uniform counting
every call position consumes its arguments whatever the callee's summary, so a
compiled slot's contract is the same for every mode summary
([ownership inference §5](../arch/ownership-inference.md#5-mode-summaries-module-caching-and-the-r3-redefinition-model-part-4),
"Modes are not slot ABI"). `RedefKind` is decided by the language type alone
(§2.1), and "ABI" in this document means the language type.

**As built (packet row D7, `7cceedc4`).** No binary site compares summaries.

- The guard in `redefine::validate_guarded_redefinition` has no same-type
  mode arm, diagnostic or summary formatter.
- The rematerialization decision in `worker.rs` reads `RedefKind` alone: a
  realization keeps its slot when its key is unchanged and its kind is not
  `AbiChanging`.
- `ModeSummary::{abi_eq, abi_eq_opt, is_abi_conservative}` left the types
  crate in the same change-set.
- Module rows:
  `redefine::tests::same_type_replacement_is_admitted_whatever_its_modes`
  and `worker::tests::same_type_mode_change_rematerializes_instance_in_its_slot`,
  both RED against the prior comparison;
  `worker::tests::ordinary_replacement_preparation_rematerializes_prior_instance`
  pins the kept slot.
- **Grade.** Asserted with a named falsifier until `qa`'s mode-change
  redefinition cell runs
  ([safety invariants](../arch/safety-invariants.md) row R12): a same-type
  redefinition that changes the inferred modes, with live callers and a
  captured callable value, must balance under the armed check in the REPL,
  and a restart on the saved source must agree. A backend emission read of a
  mode summary would refute the premise.
- **What stays.** Inference, the summaries on bindings and their persistence
  are untouched; only the comparison leaves. ACT-0953 is discharged with it.

### 2.5 Trait-implementation redefinition

A same-type re-`impl` takes effect (`spec/05-definitions.md` §5.4.5). It is an
ordinary callable redefinition of the implementation's method bodies and uses
the same guard, gate, slot policy and retention; there is no impl-specific
admission or commit path (Principles 7 and 11).

- Trait conformance, checked before anything publishes, fixes each method's
  language type for an unchanged trait. A conforming re-impl therefore
  classifies `AbiPreserving` and its bodies patch the existing slots. A non-conforming body is rejected with the
  prior implementation still live.
- **The codegen batch is the staged body set** (ACT-1035, as built S123).
  `worker::derive_codegen_batch` returns exactly the staging table's codegen
  targets: every staged concrete body and nothing else. Publication can own
  only staged bodies, because `SymbolTable::publish_compiled_staged` requires
  the owner keys to equal the staged `Concrete`/`Body` key set (its rustdoc).
  A compiled body that publication did not own would have its address
  written into its GOT slot while its JIT is freed at the end of the turn
  ([Principle 07](../arch/principles/07-single-source-of-truth.md),
  [Principle 22](../arch/principles/22-published-pointers-have-retention-owners.md)).
  - **The refusal.** Before codegen, `worker::refuse_unstaged_codegen_targets`
    rejects any batch member that staging does not hold, with a located
    invariant error. An unowned compile therefore cannot be written.
  - **Omitted defaults.** A re-impl that turns an explicit method into a
    default re-stages the trait's synthesised default body, so the staged set
    already contains it. A stale override cannot keep dispatching
    (`spec/07-traits.md` §7.1.5).
  - **Live siblings.** A live implementation of the same trait that the turn
    does not re-stage is not recompiled. A parametric impl, whose methods are
    templates, therefore compiles nothing at its own turn.
  - **Consequence for preloaded tables.** A live concrete body can be
    compiled only by a turn that stages it. A table installed without code
    for its bodies must therefore leave none of them live unless the next
    compile restages it under the same key (§8.2).
- **Guards.** At the `worker` seam:
  `derive_codegen_batch_enrolls_omitted_default_method_of_the_impl` (both
  the provided method and the re-staged default compile),
  `parametric_impl_turn_does_not_compile_live_sibling_impl` (the ACT-1035
  shape compiles nothing), and the detection proof
  `unstaged_codegen_target_is_refused_before_codegen` (a planted unstaged
  member is refused, and the staged set passes). End to end:
  `tests/impl_redefinition_dispatch.rs`, and in `tests/spec_07_traits.rs`
  `repl_concrete_impl_call_survives_parametric_impl_only_begin` with its control
  `w4_impl_begin_with_keep_retains_code_control`.

### 2.6 Type re-establishment (REPL §18.5, §14.8)

A live nominal type is re-established only with an identical structure. One
comparison serves live turns and watcher reloads (Principle 11); a reload
therefore never changes a live type's layout, and a changed structure takes
effect only at restart.

- **Site.** `worker::validate_guarded_staging_except` makes one type pass over
  the staged keys before its per-key `validate_guarded_redefinition` loop.
  The validator is the guard's only entry: prepare, plan (including macro
  checkpoints) and commit all call it, so no cadence can skip it.
- **Comparand table.** A live turn compares against the live table. A
  whole-file rebuild's live table starts empty, so its prepare step compares
  against the module's established reference instead (§7.3.2); the per-key
  loop still reads the live table and finds no prior binding.
- **Trigger.** A staged key whose staged binding and live binding both answer
  `Binding::type_def_info()`: a product constructor carrying its type facet,
  or a sum's `TypeRecord::Defined`. A class change between a type and a
  callable is outside this pass; it keeps its existing refusal.
- **Order.** The pass precedes every per-key check. A sum's visibility change
  must get this remedy, not the class/visibility refusal's "reload persisted
  source". Checking the type before any same-cluster callable also keeps the
  type-naming diagnostic deterministic.
- **Comparand.** The recorded determinants of the layout. The comparison
  derives no layout, so it does not mirror a types derivation (Principles 7
  and 24).

  | Facet | Read from |
  |---|---|
  | Visibility | the type key's binding |
  | Product or sum | which binding form answers `type_def_info()` |
  | Type-parameter count | `TypeDefInfo.type_params` |
  | Constructors, in order | `TypeDefInfo.constructors`; each sum constructor under the types-owned `member_key(Type, Ctor)` in the same table |
  | Per constructor: tag, payload count, `internal` | `CallableOrigin::Ctor` |
  | Per constructor: payload and result types, alpha-equivalent | the constructor's scheme under `LanguageType::of_scheme` (§2.2); the result type carries parameter order |
  | Product only: field and accessor names | the constructor arm's `param_names` |

  Docstrings and sum payload labels are excluded. The family is compared
  whole, from the live and staging tables the validator already holds: an
  added sum constructor has no prior key for a per-key check to see.
- **Refusal.** The pass returns an int-private value naming the type. It
  becomes one `CranelispError::TypeError` for both cadences, naming the type
  and stating that its structure differs from the live declaration. The
  remedy keeps the structure, uses a new name, or edits the saved source and
  restarts; the message must not offer reload as a remedy. The wording is
  `dev`'s.
- **Refusal record.** When the session scheduler is present, the validator
  records the refused type on the module's scheduler state before returning
  the error. Every registration or re-registration starts that record empty,
  and only a failed reload reads it
  ([REPL lifecycle §1.3.1](repl-lifecycle.md#131-session-lock)).
  A refused live turn also leaves a record. Nothing reads it, and the
  module's next registration clears it first. This record is the typed
  discriminator: nothing matches message text, and `CranelispError` gains no
  variant.
- **Types backstop.** The types-owned publication funnel
  (`validate_publication_collision`) refuses an in-place republication of a
  synthesized constructor or accessor whose scheme is not alpha-equal. On
  every int path, this pass fails first. The backstop cannot see a reorder of
  same-typed fields, which keeps every position's type and is memory-safe.
  This pass is the only refusal for that case.
- **Guards.** The pass's units are in `src/redefine/type_structure/tests.rs`.
  They cover changes to fields, constructors, payloads, type parameters and
  visibility, and they admit an identical redeclaration. End to end,
  `tests/repl_persist.rs::persist_live_deftype_changing_field_type_rejected_and_not_written_neg`
  checks the live-turn cadence. It covers the refusal, both value probes, the
  saved file and a cold restart.
  [REPL lifecycle §1.3.1](repl-lifecycle.md#131-session-lock)
  names the reload-cadence guards.
- **Rejected alternatives.**
  - A foreground comparison before re-registration would avoid the worker
    failure path. It would, however, re-derive resolved field types outside
    typecheck (Principle 7). It would also cover no live turn and no
    macro-produced `deftype`.
  - Threading a typed error from the guard would change the error type of the
    shared prepare, cluster and worker signatures, for a fact that only
    `reload_module` reads.

---

## §3. Reverse edges

### 3.1 The feed

Committed callable bindings carry forward `callees`: every statically resolved
reference from a checked body to a module-resident callable, in call position or
as a value. `cranelisp-types` settles them through its callable-arm settlement
(`canonical_callees`); typecheck owns their extraction
(`crates/cranelisp-typecheck/AGENTS.md`).

### 3.2 Why edges come from typecheck

Edges are recorded where resolution knowledge lives. Deriving them in `src/`
from stored ASTs would duplicate scope-aware resolution — shadowing, import
chains, module locality — outside the crate that owns it (Principles 7 and 17).
Call and value references are recorded uniformly, because a language-type change
invalidates both. A cache schema bump accompanied the enrichment, so every
restored table's edges are extraction-current.

### 3.3 Derivation on demand

Reverse edges are derived by scanning the live tables' `callees` when a
decision needs them — the blocking-dependent scan at admission, and
`ReverseIndex` for `/refs`. There is no maintained caller index:
a scan is correct by construction against current tables and costs nothing on a
body-only turn. REPL §18.2 makes the no-persisted-index rule normative.

The blocking-dependent scan normalizes a concrete realization to its owning
callable and a compiler-private macro clause to its owning macro parent,
deduplicates, sorts by canonical name and excludes only the target's self-edge.

---

## §4. No quiesce

Between a fresh-slot commit and any later use there is no unsound window: old
machine code embeds the **old** slot index, which is frozen and still points at
old code, so an old-ABI chain stays coherent. Each `store_slot` is independently
atomic. Publication never pauses the IO runtime, the watcher or the nice
workers.

---

## §5. No broken symbols

### 5.1 Why no redefinition can break a caller

- **The refusal is the redefinition's.** A language-type change is admitted
  only when the target has no blocking dependent (REPL §18.1). The scan (§3.3)
  reads every binding's recorded `callees`, which are recorded for template
  and concrete bodies and for macro clauses alike
  (`callee_edges::binding_callees`). Every symbol a type change could break is
  therefore a blocker, and the change is refused before publication with the
  §18.1 diagnostic.
- **The other paths.** A same-type replacement patches in place and breaks no
  caller (§2.3). A whole-file reload recompiles or locks its dependents
  (§7.3), and a locked session runs no code.
- **Nothing follows publication.** No classification, outcome or report
  leaves the commit (§2.1). A redefinition never re-typechecks or recompiles a
  dependent and never triggers a module reload (§10). The approved S121
  publication receipt
  ([S117 recovery §1.1.3](s117-conformance-recovery.md#113-post-publication-outcomes-retired))
  retired unbuilt with its subject
  ([arch §6](../arch/bounded-contexts.md#6-binary-int-src-cratescranelisp-exe-bundle)).

### 5.2 No symbol is left broken

The user ruled that a call to a symbol a redefinition would leave broken is
refused at compile time. The deleted trap stub raised through `runtime/panic`,
which ends the process, so a reachable trap would have ended the REPL.

- **Grade: structural.** A broken symbol cannot be represented. Packet row
  P13 removed `Life::Broken`, `BrokenProvenance`, `BrokenTransition`,
  `mark_broken` and `cranelisp_backend::compile_trap_stub`, with no
  cache-schema bump (§8.3; S123 packet row P13, retired and in Git at
  `d4e930a7`). It is built: `Life` in
  `crates/cranelisp-types/src/lifecycle.rs` has no `Broken` variant, and no
  name of the five occurs in a source file under `crates/` or `src/` (read
  2026-11-16). `src/worker.rs`'s slot reader matches only `Life::Concrete`.
  The S123 deletion had already removed every int construction site.
  The open question in `backend.md` §7 and the stub in `ownership-codegen.md`
  §8.1 are moot: no call to a broken symbol is compiled.
- **Guards.** `redefine.rs`'s
  `concrete_and_unrealised_template_callers_block_a_type_change`: a concrete
  caller and a template caller with no realisation both block a type change
  of `f`, and with no caller nothing blocks it. End to end:
  `tests/repl_redefinition.rs`.
- **Evidence still owed.** The unit rows for a macro-clause caller and the
  detection proof (a planted scan that skips template callees turns the
  template row red) were not found in `src/` on 2026-11-16. `qa` decides
  whether they are required before the grade is credited.

---

## §6. Retention

### 6.1 The pool

```rust
// SharedState
retained_code: Mutex<Vec<RetainedCode>>   // append-only, session-lifetime

struct RetainedCode {
    fq: FQSymbol,
    module: ModuleFullPath,
    slot: Option<usize>,  // the frozen or patched slot, when there is one
    code: Code,           // keeps the executable pages mapped
}
```

- **Every replaced or retired compiled body is pooled.** The publication record
  returns the displaced owner of every replaced body arm, whatever its
  `RedefKind`, and each retaining path pushes it under the same module write
  guard that performed the replacement. A whole-file rebuild pools every
  compiled owner of the table it displaces before that table can drop
  (§7.3.1). No live cell can name a displaced owner that is not yet pooled.
- **Retaining paths:** the staged commit gate (`worker::commit_staging_to_live`),
  the prepared compiled publication and its rejection restore
  (`worker::compile_and_publish_prepared_with`,
  `worker::retain_and_restore_rejected_compilation`) and the rebuild prologue
  in `session_v4::lifecycle::reload_module`.
- **Two paths do not pool:** cache-hit owner publication
  (`worker::load_cached_module_via_linker`) drops displaced owners, and a commit
  with no session `SharedState` (unit tests, dry runs) keeps the plain drop.
  The retention claim is therefore **asserted with a named falsifier**: a
  closure minted from a body one of those paths displaces, still reachable after
  the drop. Reachability is `qa`'s to measure.

### 6.2 Lifetime

The pool is append-only to session end. A same-ABI replacement cannot prove that
no detached strand is mid-call in the old body, so freeing on replacement would
trade a use-after-free for a few hundred bytes. The leak is bounded by the
session's pooled displacements, is visible as pool length and GOT-trace events
(§9.3), and restart reclaims it.

### 6.3 No clear-before-replace

No path clears compiled code ahead of recompilation. Compiled owners stay
attached until publication replaces them and the gate pools each displaced
owner before releasing the write guard. A `*code = None`-style clear would drop
what can be the last reference to pages an in-flight frame or heap closure still
executes.

---

## §7. Slot versioning

### 7.1 The commit gate is the single slot-policy authority

| Kind | Slot | Prior `Code` |
|---|---|---|
| `New` | fresh mint | — |
| `AbiPreserving` | reuse the prior slot; codegen patches it | pooled at publication |
| `AbiChanging` | fresh mint; the old slot is never written again and is recorded in the table's `retired_slots` | pooled at publication |

A whole-file rebuild publishes every callable as `New` into a fresh table; its
displaced owners are pooled by the rebuild prologue (§7.3.1).

Typecheck's redefinition slot pin is the fast-path identity; on `AbiChanging`
the gate overrides it. A fresh slot is unconditional on a language-type change,
independent of recorded callers: a value captured by a transient REPL expression
has no `callees` edge but still loads the old slot.

### 7.2 Freezing is structural

Every slot writer derives its index from a live binding, and after an
`AbiChanging` commit no live binding carries the old index. The allocator scans
live claims together with `retired_slots`, so a retired index is never reissued
by that table (Principle 20). Retirement is per table: a whole-file rebuild's
fresh table starts with no claims and no retired slots, and its safety rests on
the plan invariant instead (§7.3.3). A retention entry's `(module, slot)` is
for observation, not a gate.

### 7.3 The watcher and reload path

A reload of a saved file is a **whole-file rebuild**. The module's new
generation is exactly what the saved source establishes, compiled into a fresh
table (REPL §14.2 steps 2–3; §14.5 items 1–2). An interactive turn is an
**increment**: it merges into the live table under the guard (§§2, 7.1). One
seam separates the two (Principle 11): whole-source provenance, which only
`reload_module` establishes (§7.3.1). REPL §14.8's restart boundary for types
is the only redefinition check a rebuild applies (§7.3.2). Plan selection,
ordering, the one reload executor, waiting dependents and the session lock
are [REPL lifecycle §1.2–§1.3](repl-lifecycle.md#12-poll-and-reload).

#### 7.3.1 The whole-file rebuild

- **Where.** In `reload_module`, after `wait_module_typecheck_settled` and
  before anything that can fail: before the saved file is read and parsed,
  and before the module preamble is captured and the source re-registered.
  It runs once per attempt, on the eval thread, inside a reload plan between
  turns, so no user code is in flight. The `ClearModuleState` trace event is
  recorded here, where the clear happens. A waiting member that the executor
  does not attempt runs this prologue and nothing after it
  ([REPL lifecycle §1.2](repl-lifecycle.md#12-poll-and-reload), Waiting).
  - **Why first.** A read or parse failure that returned before the swap
    kept the previous generation: its names stayed resolvable and its
    dependents compiled against it unlocked (ACT-1044). With the prologue
    first, every failure cause leaves the same state.
- **Swap.** Under the module's write guard, replace its table with
  `SymbolTable::new_with_params(module)` whose `got` is the displaced table's
  `Arc<GotTable>`, then release the guard. The GOT base address baked into
  compiled code therefore stays fixed for the module's lifetime (§7.4). Hold
  at most one `DashMap` guard at a time.
- **Nothing is copied.** Definitions of every class, candidates, the `import`,
  `export`, `mod` and `platform` records, written impls, lookup dependencies,
  retired slots and the preamble of the prior generation are all absent from
  the fresh table. There is no removal list, so the rebuilt namespace cannot
  hold anything the saved source did not establish.
- **Session-side state keyed by the module** is reset from the displaced
  table, each under its own guard:

  | State | Reset |
  |---|---|
  | Import-alias and submodule-alias keys in `module_aliases` | Remove `module_alias_key(module, alias)` for each alias the displaced `imports` and `submodules` declared. Pass 0 reinstalls the ones the saved source declares ([int §6.10](int.md#610-the-import-generation)) |
  | `declared_exports[module]` | Remove; Pass 0's `install_exports` records the new set |
  | `prelude_fallback[module]` | Remove; the `Replace` prologue's fresh recompute then sets it exactly from the saved source |
  | Implementation shells in another trait home | For each displaced `written_trait_impls` entry whose trait home is another module, remove the shell at `trait_impl_key(impl_type, trait_name)` in that home with `remove_non_callable`. An absent shell is a no-op. The rebuild restages each impl it still declares. Shells other modules wrote into this module are absent from the fresh table; their writers are dependents and restage them |
  | Introspection records | Remove the record of each displaced definition. The rebuild's publication installs the new records ([session persistence §2.4.1](session-persistence.md#241-who-writes-a-record)) |

  The typecheck product (which `reload_module` replaces), the watcher map,
  the scheduler state (which re-registration resets), the cache hash stash
  and the `/search` rows are not reset here.
- **Retention.** Every compiled owner the displaced table holds, including
  overload arms, instances and macro clauses, enters the retention pool as a
  frozen entry before that table can drop (§6.1). The displaced table then
  becomes the module's reference or drops (§7.3.2).
- **Order.** Swap, pool the displaced owners, hold the reference, and only
  then run the fallible session-state reset. An early return from the reset
  then cannot drop an unpooled `Code` or lose the reference (review A1). The
  reset's one refusal is precluded today, since it removes only an
  implementation shell; the order makes that irrelevant.
- **Then the ordinary path.** Pass 0, macro checkpoints, the final cluster,
  codegen and publication run as a first registration on the fresh table.
  - The per-key guard finds no prior binding and passes. A rebuild may
    change a callable's type, ABI, declaration class or visibility, change a
    trait's interface, or drop any definition; its dependents recompile or
    lock.
  - A body that names an omitted definition, import or macro fails as an
    ordinary unresolved name.
  - A gap keeps the attempt's provenance and retries against the same fresh
    table. Nothing swaps a second time.
  - Lookup dependencies are exact for each generation, because only the
    rebuild's own compile records them.
- **Failure.** The module keeps its partial fresh table: normally only Pass 0
  records and checkpoint-published macros. That is the specified failure
  state (cleared, unavailable), so there is no rollback. A read or parse
  failure registers nothing, so `reload_module` records the module `Failed`
  in the scheduler with that error, as a failed registration would have.
  Every cause therefore leaves the same table, scheduler and session state,
  and a later load that reaches the module is refused by the fail-fast. The
  module stands failed, or waits when a dependency refused it, and the
  session locks
  ([REPL lifecycle §1.3.1](repl-lifecycle.md#131-session-lock)).
- **Increments never rebuild.** Only `reload_module` swaps, and only its
  registration of the re-read saved source carries whole-source provenance,
  including the first-seed fallback for a module the scheduler no longer
  tracks. Everything else merges into the live table:
  - a first registration at startup, through the dependency drive or as a
    cache-restore dependency;
  - a REPL turn (`Additive`), a macro checkpoint and clause staging;
  - the retry after a submodule gap, which stores an increment with no source
    once the final cluster has published;
  - a dispatch with no stored continuation, and startup recovery's empty
    re-registration of the entry module.

#### 7.3.2 The established reference

- **What it is.** The table displaced by the first whole-source attempt since
  the module's last successful one. It is the last successful generation,
  including every increment merged into it since.
- **Where it is held.** The session holds it beside the failed set, keyed by
  module. An attempt that finds one held keeps it and lets its own displaced
  (partial) table drop after pooling its owners. Only `reload_module`'s
  success branch drops it, together with the failed-set and
  failure-dependency clears. Every failed or waiting attempt therefore
  leaves one held.
- **How it travels.** `SourceProvenance::WholeSource` carries it, in place of
  the retired instantiation-demand packet. The continuation keeps it across
  gaps into the final cluster's prepare step. An increment has no variant that
  could carry one.
- **§14.8 comparand.** The prepare step's type pass (§2.6) compares staged
  types against the reference. A changed structure refuses with the restart
  remedy and records the refused type; a repeated structural save meets the
  same reference and fails again. Success drops the reference, so a type that
  a successful rebuild removed may return later with any structure.
- **Retained edges.** Reload selection and ordering read the reference's
  edges beside the partial table's
  ([REPL lifecycle §1.2](repl-lifecycle.md#12-poll-and-reload)). A failed
  compile records no callee edge and no lookup dependency, so without the
  reference a module that failed on `lib/h` would lose its edge to `lib`, and
  repairing `lib` would never release it (REPL §14.6; FQR-1, FQR-2, FL-3).
- A module with no table at reload takes an empty reference. Production
  reaches this for a startup-failed dependency whose never-compiled table
  recovery purged
  ([REPL lifecycle §1.3.1](repl-lifecycle.md#131-session-lock)); it never
  compiled, so there is no generation to compare against or to take edges
  from. Its failure dependencies select it instead
  ([§1.2.1](repl-lifecycle.md#121-failure-dependencies)).
- **Grade: structural.** Only whole-source provenance can carry a reference,
  and only the success branch drops one.

#### 7.3.3 Slot reuse and the plan invariant

- The fresh table mints GOT slots from zero, so a rebuild reuses slot indices
  and consumes no capacity (§7.5). Increments keep per-table tombstones
  (§7.1–§7.2).
- **Invariant.** Every module whose compiled code references a rebuilt
  module's GOT is rebuilt, failed or waiting after it in the same plan,
  each of which displaces its previous generation, before any of its code
  can run. A caller left behind would call through a reused slot into a
  different function, possibly of a different ABI. Macro expansion stays
  available while the session is locked, so "evaluation is refused" alone
  does not protect a generation left in place.
- **Realization.** The selection predicate, plan order from the same
  predicate, the post-plan order check and the one executor
  ([REPL lifecycle §1.2](repl-lifecycle.md#12-poll-and-reload)); every
  outcome runs the prologue, and a failure, which every wait depends on,
  locks the session ([§1.3.1](repl-lifecycle.md#131-session-lock)).
- **Grade: asserted with a named falsifier.** Falsifier: after a completed
  plan, code runs in a module that references a rebuilt module's GOT and was
  neither rebuilt, failed nor waiting after it in that plan. Possible
  sources are an edge kind outside loading imports, exports, the prelude
  fallback, callees and lookup dependencies, and a dependent with no mapped
  file (below). A null import is no edge; a use
  through it is a recorded callee or lookup edge.
  A module cycle whose members all compile is no longer a source: the
  publication check rejects the attempt that closes it
  ([int §6.11](int.md#611-module-cycles-at-publication)), and a follow-on
  root set that recurs anyway fails its modules
  ([REPL lifecycle §1.2](repl-lifecycle.md#12-poll-and-reload)). Controls:
  FQR-1, FQR-2 and the lookup-dependency cells for edge kinds; the order,
  order-check and recurrence units (§1.2); the executor for callers.
- **Residuals.**
  - A dependent with compiled definitions and no mapped backing file is not
    rebuilt. Regeneration maps every file it writes, so this needs a module
    that started without a file and whose regeneration never wrote one: one
    that declares an inline `(mod name body…)` in the REPL, which FIXME 0343's
    guard exempts from regeneration. Unmeasured.
  - A dependent whose file is still recorded absent is not rebuilt either
    ([REPL lifecycle §1.2](repl-lifecycle.md#12-poll-and-reload), Reload
    set). It is safe only while that module holds no compiled definition.
    A defining turn's regeneration replaces the absent record, so the
    falsifier is a module with compiled definitions whose regeneration
    failed to write: a write error or the FIXME 0343 exemption above.
    Unmeasured.
  - The pool grows by one displaced table's owners per rebuild, the same
    order as its growth under redefinition (§6.2).
  - `/search` rows for a failed module stay at their last publication.

#### 7.3.4 Module tests (`dev`)

Arm each positive row RED on the pre-fix source where its seam exists.

| Row | Expected |
|---|---|
| Prologue | A module holds a function, an overload family, a template with a same-module instance, a type, a trait, an impl of a foreign trait, a macro, `(import [lib [id]])`, an aliased import, `(mod child)` and a preamble. A successful rebuild from a source omitting each leaves every one absent: `id` is unresolved and not in `explicit_import_sources`, the alias and submodule-alias keys are gone, the foreign trait home holds no shell, the preamble is `None` and `retired_slots` is empty. The new `got` is `Arc::ptr_eq` to the prior one, and the pool holds every displaced compiled owner. A rebuild keeping each item records it once |
| Prelude bit | A rebuild adding `(import [prelude [...]])` leaves the fallback bit off; removing it again turns the bit on |
| Increments | No module test; the grade is structural. Whole-source provenance has one caller, `rebuild_from_file`, reached only from `reload_module`, whose one production caller is `run_reload_plan`. The swap (`install_fresh_generation`, private) has that caller and two more that replace a whole generation without registering source: the executor's waiting member and startup recovery's entry that did not compile ([REPL lifecycle §1.2, §1.3.1](repl-lifecycle.md#131-session-lock)). A REPL turn, a dispatch with no stored continuation and the retry after a submodule gap therefore cannot reach the swap |
| Unresolved omission | A rebuild whose remaining body names an omitted function, and separately an omitted import, fails as unresolved and leaves the module standing failed |
| Empty source | A rebuild from a source with no checkable form succeeds with an empty table |
| Reference | A first failing rebuild holds the established table. A second failing rebuild keeps it, so a structural type change refuses both times, also when the attempt resumes after a dependency gap. Success drops it. After a successful rebuild that removed type `T`, a rebuild re-adding `T` with another structure succeeds |
| GOT reuse | `N` rebuilds of a module with `k` callables, `N·k > GOT_TABLE_SIZE` (for example `k = 128`, `N = 9`), all succeed; `got` stays pointer-equal and `retired_slots` stays empty. Negative leg: an increment's ABI-changing redefinition records the old slot in `retired_slots`, and the next mint does not reissue it |

Selection, ordering and lock rows are listed in
[REPL lifecycle §1.2 and §1.3.1](repl-lifecycle.md#12-poll-and-reload). End to
end: C2 and C3, RM-1 to RM-5, FL-1 to FL-3, FQR-1 and FQR-2, M1, the §14.8
cells and the watcher cascade cells.

#### 7.3.5 Rejected shapes

- **Clear in place and tombstone every slot.** It needs a types funnel, and a
  module with `k` callables would use up the GOT after about
  `GOT_TABLE_SIZE / k` saves, with the tombstones persisted in `.meta.json`.
- **A fresh GOT per generation.** Other modules' relocations and the JIT data
  symbol would need backend work.
- **An attempt-private table published on success.** The specified failure
  state is already cleared, and the reference keeps what a failure needs.
- **Per-definition removal and persisted demand replay.** Absent-key
  retirement of omitted definitions, the referer scan, candidate withdrawal
  and captured reload demands are superseded by the fresh table; Git retains
  them.

### 7.4 Slab stability

A module's GOT base address is baked into finalized code, so the slab never
moves while slots are minted. Fresh-slot redefinition adds allocation events,
not a new kind of growth.

### 7.5 GOT exhaustion

Each module GOT has `GOT_TABLE_SIZE` slots and a table never reuses its retired
slots, so repeated language-type-changing redefinition by increments consumes
capacity until the module's next whole-file rebuild. A rebuild starts a fresh
table on the same GOT and consumes none (§7.3.3).

A restart returns capacity only when the module's cache entry does not
restore. Retired slots serialize (§8.1, §8.4). An entry whose cache stays
valid is preloaded with its persisted tombstones (§8.2), and a cache-restored
dependency installs its persisted table. As built, the entry preload adds
`k + 1` tombstones per launch, which is a confirmed defect (§8.2). The
persisted tombstones of ABI-changing redefinitions are backlog item 0466,
which the user deferred.

The types-owned mint refuses an index at or beyond the table size with a
diagnosed "GOT slot table exhausted" error rather than writing past the slab
(`redefine.rs` unit `got_exhaustion_surfaces_error_not_ub`).

---

## §8. Persistence

### 8.1 Slot assignments serialize

Each callable's slot and the table's `retired_slots` serialize with the symbol
table into `.meta.json`. Slot numbers are load-bearing against cached `.o` code,
so no path renumbers or compacts them.

### 8.2 Faithful writes

`regenerate_backing_file` runs after every successful defining turn; a rejected
redefinition is never written (REPL §18.8).

**The entry slot preload.** At registration, every mode pre-seeds the entry
module's table from a `.meta.json` that the manifest validates against the
current source, then recompiles the module from source onto it
(`session_v4::lifecycle::preload_entry_slot_assignments`). Each authored
definition keeps its persisted slot, and new definitions mint above them.

- **What the preload releases** (packet row P15, built in the S123 W4 tree,
  not yet committed; read 2026-11-16). `release_bodies_the_recompile_restages`
  releases the synthetic `__expr` wrapper and each `minted_from: Some(_)`
  instance on the decoded table, before `into_concrete`, through the
  types-owned `SymbolTable<(), ()>::release_callable`. That call removes one
  callable from a decoded, code-free table and drops its slot claim without a
  tombstone; a refusal leaves the table unchanged, and the preload then
  installs nothing. The recompile restages each instance a definition demands
  under a fresh slot, rather than replacing it in place. A preloaded instance
  left live would hold a slot with no code, because the batch compiles only
  staged bodies (§2.5). Releasing it removes that state by construction.
  Which bodies to release is int's policy, recorded here; existing tombstones
  are kept. No cache-schema bump and no ABI effect
  (S123 packet row P15, retired and in Git at `d4e930a7`).
- **Defect P15 closes: the tombstones accumulated** (confirmed by `qa`,
  2026-11-16, [evidence plan](../../tests/plan/s123-evidence-delta.md) §3.6
  R-5). The earlier preload retired these bodies through
  `retire_abi_changing`, and each retirement recorded a tombstone in
  `retired_slots`, which serializes (§8.1). The nice worker rewrites the
  entry's `.meta.json` after the from-source compile, and an unchanged source
  keeps the cache valid, so every cached launch of an entry with `k`
  instances lost `k + 1` slots for good. With 128 generic identities, five
  cached launches persisted 645 tombstones and the seventh exhausted the GOT
  (§7.5). The release records none, so a cached restart consumes no GOT
  capacity. The guard is R-5's cell,
  `tests/cache.rs::cached_restarts_keep_generic_instance_slot_capacity_across_modes`;
  its flip to green awaits the suite run.
- **Why a release is safe** (`arch`'s ground, P15; it replaces the earlier
  "no module cycle" ground, which fails for a module `/mod` loads that
  imports the entry). A tombstone protects code that embeds the old index
  (§7.2). There are three possible holders:
  - *This process.* A decoded table holds no compiled owner, and its GOT is
    the fresh slab deserialization creates. Nothing has compiled against it.
    Grade: structural.
  - *Other modules' cached objects.* Instances are minted in the demanding
    module with their own slot
    ([monomorphisation §3.7](../typecheck/monomorphisation.md#37-cross-module-body-recheck-scoping)),
    and `__expr` is never referenced across modules, so such code embeds
    only authored slots, which the preload keeps. Grade: asserted with a
    named falsifier: another module's cached object that relocates against
    the entry's GOT at an index the entry's table holds for a minted
    instance or for `__expr`.
  - *The entry's own earlier object.* The entry is compiled from source, and
    one compile writes its new object and `.meta.json` together.

### 8.3 Broken modules are not persisted

No module can hold a `Life::Broken` entry, because `src/` constructs none
(§5.2). The nice worker therefore has no broken-module check, and no
`.meta.json` holds the variant. P13 relies on this to remove it without a
cache-schema bump.

### 8.4 High water across sessions

Retired indices survive in `.meta.json` as holes. A new session mints strictly
above every index a cache references; the retained code of frozen slots dies
with the old session.

### 8.5 The backing file holds definitions only

`save.rs` omits `$`-mangled instances and the synthetic `__expr` wrapper. Mono
instances travel through the compiled channel. A whole-file rebuild keeps none:
the definitions that use an instance demand it again when they recompile.

---

## §9. Surfacing

### 9.1 What the user sees

An ordinary redefinition surfaces only as the definition confirmation or the
rejection diagnostic (REPL §18). There is no cascade, `stale:` or downgrade
report.

### 9.2 Introspection

`/sig`, `/info` and bare lookup show only live definitions. No entry carries
broken provenance (§5.2).

### 9.3 Observability

`got_trace` records redefinition and slot-freeze events (`src/got_trace.rs`).
Pool length is the retention leak metric.

---

## §10. No reload follows a redefinition

A redefinition turn never runs a reload plan. The reload executor's callers
are the watcher poll and `/mod`'s recompile of a cache-installed module
([REPL lifecycle §1.2](repl-lifecycle.md#12-poll-and-reload)). A same-type
edit of a generic definition rematerializes its prior instances in the turn's
own candidate, so a compiled caller reaches the new body without being
re-typechecked (REPL §18.1; `design/int/s122-closure.md` §2).

---

## §13. Implementation map (`src/`)

| Concern | Site |
|---|---|
| Admission guard, blocking dependents, rematerialization policy, overload-arm correspondence | `src/redefine.rs` (`validate_guarded_redefinition`, `blocking_dependents`, `instance_rematerialization_policy`, `match_replacement_overload_arm`) |
| Guard invocation, type re-establishment pass (§2.6) and prepared candidate | `src/worker.rs` (`prepare_cluster_commit`, `validate_guarded_staging_except`); the refusal record on `scheduler::ModuleState` |
| Classification, slot policy and pooling | `redefine::classify_redefinition`; `worker::commit_staging_to_live`; the prepared compiled publication |
| Codegen batch and its refusal (§2.5) | `worker::derive_codegen_batch`, `worker::refuse_unstaged_codegen_targets` |
| Whole-file rebuild (§7.3) | prologue and reference hold: `session_v4::lifecycle::reload_module`; whole-source provenance and the reference it carries: `scheduler::SourceContinuation`, read by `process_form::process_cluster_once` and handed to the prepare step by `process_form::finalize_cluster`; plan, order check and executor: `session_v4::lifecycle` ([REPL lifecycle §1.2](repl-lifecycle.md#12-poll-and-reload)) |
| Retention pool | `redefine::RetainedCode`, `RetentionPool`; `SharedState.retained_code` |
| Persistence | `session_v4::lifecycle::regenerate_backing_file`, `reload_module`, `preload_entry_slot_assignments` (§8.2); `session_v4::nice_worker::compile_module_object` |
| Reverse index for `/refs` (§3.3) | `redefine::ReverseIndex`, `redefine::base_fq_from_tables` |
