# Session transaction — guarded redefinition, slot versioning and retention

Owner: `design` (int). Subordinate to `int.md` §8.6. Normative surface:
`repl/spec/18-redefinition.md` §18. The S122 reload and instance
rematerialization cadence is `design/int/s122-closure.md` §2; this document owns the
slot, retention and persistence mechanics around it. Section numbers are pinned
by live source comments and tests; keep them stable.

## §0. The current model, and what it superseded

Redefinition is a guarded publication inside the ordinary prepared transaction:

1. The proposed cluster checks into unpublished staging.
2. `redefine::validate_guarded_redefinition` rejects, before any live change,
   a declaration-class change, a visibility change, a callable language-type
   change with a blocking dependent (§3) and a same-language-type replacement
   whose ABI-bearing `ModeSummary` differs.
3. An admitted generic base or overload family rematerializes its prior
   concrete instances into the same candidate (`design/int/s122-closure.md` §2).
4. The commit gate classifies each published callable (§2) and applies the slot
   policy (§7); every displaced compiled owner enters the retention pool (§6).

A rejected redefinition leaves the complete prior definition live and its
backing source unchanged. **No ordinary callable redefinition re-typechecks or
recompiles a dependent, marks a symbol broken or installs a trap stub.**

The S101–S103 design this document formerly carried — an affected-set
dependent-recompilation transaction, BROKEN symbols with trap-stub slots, the
`stale:` downgrade report and the T1 end-of-turn module reload — is superseded
by that rule. Its code remains in `src/redefine.rs`; §§4, 5, 9.1–9.2 and 10
describe the residue only so source comments that cite them resolve, and
`int.md` §16.0 records its removal and the one leg whose reachability is
suspect. Do not extend it.

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
embeds slot indices. Each classification rides the processed cluster back to
eval as a `RedefinitionOutcome` (§13).

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

### 2.4 The ownership-ABI half

`ModeSummary`'s ABI-bearing modes are not part of the language type, but they are
the ABI of an existing live slot. The guard therefore rejects a same-type
replacement whose ABI-bearing modes differ (`ModeSummary::abi_eq_opt`;
REPL §18.1.2). A caller-free language-type change takes a fresh slot and may
change modes. ACT-0953 carries the future decoupling of slot ABI from ownership
inference.

### 2.5 Trait-implementation redefinition

A same-type re-`impl` takes effect (`spec/05-definitions.md` §5.4.5). It is an
ordinary callable redefinition of the implementation's method bodies and uses
the same guard, gate, slot policy and retention; there is no impl-specific
admission or commit path (Principles 7 and 11).

- Trait conformance, checked before anything publishes, fixes each method's
  language type for an unchanged trait. A conforming re-impl therefore
  classifies `AbiPreserving`, subject to the §2.4 ownership-ABI check, and its
  bodies patch the existing slots. A non-conforming body is rejected with the
  prior implementation still live.
- The codegen batch must recompile every re-staged method body even though
  publication retained a prior owner. `worker::derive_codegen_batch` forces
  every concrete implementation body of the authored trait into the batch.
  It selects them from the table, not from the impl form's written methods.
- Deriving the set from the form under-approximates it. When a method changes
  from explicit to default, the synthesised default body never appears in the
  form, and the stale override would keep dispatching (`spec/07-traits.md`
  §7.1.5). Recompiling a sibling implementation of the same trait costs a
  compile and changes nothing observable.
- The discriminating unit cell is
  `derive_codegen_batch_enrolls_omitted_default_method_of_the_impl`; an
  explicit-method cell passes under either derivation. End-to-end behaviour
  is `tests/impl_redefinition_dispatch.rs`.

---

## §3. Reverse edges

### 3.1 The feed

Committed callable bindings carry forward `callees`: every statically resolved
reference from a checked body to a module-resident callable, in call position or
as a value. `cranelisp-types` settles them through its callable-arm settlement
(`canonical_callees`); typecheck owns their extraction
(`crates/cranelisp-typecheck/CLAUDE.md`).

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
`ReverseIndex` for the superseded residue. There is no maintained caller index:
a scan is correct by construction against current tables and costs nothing on a
body-only turn. REPL §18.2 makes the no-persisted-index rule normative.

The blocking-dependent scan normalizes a concrete realization to its owning
callable and a compiler-private macro clause to its owning macro parent,
deduplicates, sorts by canonical name and excludes only the target's self-edge.

---

## §4. Affected-set closure (superseded residue)

`redefine::affected_closure`, `condense_reverse_topo`, `scc_should_visit`,
`member_propagates` and `run_transaction` implement the former transaction:
transitive reverse closure, SCC condensation, a callee-first walk with a
propagation skip test and slot-less pass-through. `apply_redefinition_outcomes`
runs it for a per-symbol `AbiChanging` outcome. The guard admits such an outcome
only when no blocking dependent exists, so the closure should be empty; no
current requirement relies on it.

### 4.1 Closure and ordering

Superseded as above. The frozen-world argument of §4.3 is the part that remains
load-bearing, for slot versioning.

### 4.2 Per-symbol re-typecheck

Superseded. The residue re-checks from stored introspection sexps and falls back
to module-grain reload when a sexp is unavailable.

### 4.3 No quiesce

Between a fresh-slot commit and any later use there is no unsound window: old
machine code embeds the **old** slot index, which is frozen and still points at
old code, so an old-ABI chain stays coherent. Each `store_slot` is independently
atomic. Publication never pauses the IO runtime, the watcher or the nice
workers.

---

## §5. BROKEN state (superseded residue)

### 5.1 Marking

`redefine::mark_broken` transitions a slotted entry through the types-owned
`Life::Broken` funnel, retains its displaced code and a paired trap stub in the
pool, and patches the slot in place. A slot-less entry is left unchanged.
`broken_status_line` renders a `Life::Broken` entry's provenance at `/sig`,
`/info` and bare lookup. REPL §18 forbids creating broken symbols on ordinary
redefinition; reload and restart never restore broken state (§18.8).

---

## §6. Retention

### 6.1 The pool

```rust
// SharedState
retained_code: Mutex<Vec<RetainedCode>>   // append-only, session-lifetime

struct RetainedCode {
    fq: FQSymbol,
    module: ModuleFullPath,
    slot: Option<usize>,        // the frozen or patched slot, when there is one
    code: Code,                 // keeps the executable pages mapped
    trap_msg: Option<Box<str>>, // Some only for a trap stub's baked message
}
```

- **Every replaced compiled body is pooled.** The publication record returns the
  displaced owner of every replaced body arm, whatever its `RedefKind`, and each
  retaining path pushes it under the same module write guard that performed the
  replacement. No live cell can name a displaced owner that is not yet pooled.
- **Retaining paths:** the staged commit gate (`worker::commit_staging_to_live`),
  the prepared compiled publication and its rejection restore
  (`worker::compile_and_publish_prepared_with`,
  `worker::retain_and_restore_rejected_compilation`), and the residue's
  `mark_broken`.
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
(§9.3), and restart reclaims it. A trap stub's message buffer rides the same
entry as its `Code`, so neither can outlive the other (Principle 18).

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

Typecheck's redefinition slot pin is the fast-path identity; on `AbiChanging`
the gate overrides it. A fresh slot is unconditional on a language-type change,
independent of recorded callers: a value captured by a transient REPL expression
has no `callees` edge but still loads the old slot.

### 7.2 Freezing is structural

Every slot writer derives its index from a live binding, and after an
`AbiChanging` commit no live binding carries the old index. The allocator scans
live claims together with `retired_slots`, so a retired index is never reissued
(Principle 20). A retention entry's `(module, slot)` is for observation, not a
gate.

### 7.3 The watcher and reload path

Persisted-source reload and the watcher's dependent-module recompilation commit
through the same gate and slot policy at module grain:

- no slot is zeroed; old pointers stay live until each new pointer lands;
- each recommitted callable classifies against its prior binding;
- demands for the module's prior instances travel with the reload as data
  (`design/int/s122-closure.md` §2); no source form is replayed.

What happens to a callable absent from reloaded source is not designed here.
The S101 design left it resolvable until restart as a recorded gap; that has not
been re-verified against the current Replace generation, so confirm the
behaviour in `reload_module` before relying on either outcome.

### 7.4 Slab stability

A module's GOT base address is baked into finalized code, so the slab never
moves while slots are minted. Fresh-slot redefinition adds allocation events,
not a new kind of growth.

### 7.5 GOT exhaustion

Each module GOT has `GOT_TABLE_SIZE` slots and retired slots are never reused, so
repeated language-type-changing redefinition consumes capacity until restart.
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
redefinition is never written (REPL §18.8). Startup pre-seeds the entry
module's slot assignments from a still-valid `.meta.json` before recompiling
from source, so persisted slots are reused and new definitions mint above them.

### 8.3 Broken modules are not persisted

A module holding a `Life::Broken` entry at write time persists no `.o`/`.meta`,
because a snapshot would record a trap stub as compiled truth. Broken state is
never persisted; restart recompiles current source.

### 8.4 High water across sessions

Retired indices survive in `.meta.json` as holes. A new session mints strictly
above every index a cache references; the retained code of frozen slots dies
with the old session.

### 8.5 The backing file holds definitions only

`save.rs` omits `$`-mangled instances and the synthetic `__expr` wrapper. Mono
instances travel through the compiled channel and, on reload, as captured
demands.

---

## §9. Surfacing

### 9.1 The cascade report (superseded residue)

`TransactionReport` renders the residue's `recompiled:`, `broken:`, `recovered:`
and `stale:` sections. Current §18 surfaces an ordinary redefinition only
through the definition confirmation or the rejection diagnostic.

#### 9.1.1 The downgrade (`stale:`) section (superseded residue)

`is_t1_downgrade` selects a redefinition of a prior callable outside per-symbol
precision where either the prior or the staged entry is slot-less — including a
template-to-template body edit, which changes no slot shape; `stale_callers` names the compiled direct
callers of the target and its instances, folding a macro clause to its owning
macro. REPL §18 no longer defines this section. The reachability of this leg is
the open question in `int.md` §16.0.

### 9.2 Broken status at `/sig` and `/info` (superseded residue)

See §5.1.

### 9.3 Observability

`got_trace` records redefinition, slot-freeze and trap-patch events
(`src/got_trace.rs`). Pool length is the retention leak metric. The rejection
diagnostic and definition confirmation are the user-visible record.

---

## §10. T1 and module-grain reload (superseded residue)

- **T1 — target outside per-symbol precision.** Such a redefinition classifies
  without the per-symbol transaction. The residue then drives
  `drive_t1_full_cure` from `apply_redefinition_outcomes`:
  - **CS-1:** when compiled stale callers exist and the module may regenerate,
    regenerate the backing file, reload the target module and reload its
    dependents;
  - **CS-2:** a successful reload pushes no `stale:` report;
  - **CS-3:** a reload failure enters the REPL §14.4 error-blocked state
    (liftable by repairing the recorded failed forms); a suppressed module
    keeps the `stale:` report.
  REPL §18.1 now requires same-language-type generic edits to rematerialize
  their instances in the original candidate without re-typechecking callers
  (`design/int/s122-closure.md` §2), so this reload is not the cure. Its reachability is
  the suspected defect recorded in `int.md` §16.0.
- **T2 — unrecoverable re-check input** and **T3 — untrusted edge feed** belong to
  the residue's module-grain fallback and have no current requirement.

---

## §13. Implementation map (`src/`)

| Concern | Site |
|---|---|
| Admission guard, blocking dependents, rematerialization policy, overload-arm correspondence | `src/redefine.rs` (`validate_guarded_redefinition`, `blocking_dependents`, `instance_rematerialization_policy`, `match_replacement_overload_arm`) |
| Guard invocation and prepared candidate | `src/worker.rs` (`prepare_cluster_commit`, `validate_guarded_staging`, `capture_reload_instantiation_demands`) |
| Classification, slot policy and pooling | `redefine::classify_redefinition`; `worker::commit_staging_to_live`; the prepared compiled publication |
| Outcomes to eval | `RedefinitionOutcome` on the processed cluster (`src/cluster.rs`), consumed after codegen in `src/eval.rs` |
| Retention pool | `redefine::RetainedCode`, `RetentionPool`; `SharedState.retained_code` |
| Persistence | `session_v4::lifecycle::regenerate_backing_file`, `reload_module`; `session_v4::nice_worker::compile_module_object` |
| Superseded residue | `run_transaction`, `mark_broken`, `ReverseIndex`, `stale_callers`, `TransactionReport`, `apply_redefinition_outcomes`, `drive_t1_full_cure` |
