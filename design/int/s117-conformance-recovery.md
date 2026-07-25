# Sprint 117 — REPL conformance and failed-turn recovery

This subordinate design elaborates the Binary/int master for Sprint 117 Tracks
A and B. It covers FIXME 0816 (macro-expanded declaration staging), 0817
(failed-codegen recovery and diagnostic attribution), 0839 (`/info <Type>`
inverse impl enumeration), 0802 (constraint rendering), and FIXME 0800 faces
DF-1/DF-2 only. `def` remains the zero-argument stdlib macro specified in
`stdlib/defs.cl`; function-valued `def` behaviour (DF-3) is a later
stdlib/REPL API choice, not a core-form or language-spec decision.

The design stays inside the one v4 pipeline (Principle 11 — Single pipeline,
mode parameters), adds no instrumentation or memory mechanism, and changes no
public crate interface.

## 0. Phase-5 refinement against the W1 guards

The W1 results narrow W3:

- **MB-1 through MB-4 are green.** The existing expansion → structural peel →
  one `check_forms` path already satisfies §2. W3 must preserve it and must not
  add a macro-staging implementation.
- **IN-1 and IN-2 are green; IN-3 is red.** The inverse relation is already
  complete enough for local/re-impl and inverse-twin coverage. The remaining
  defect is mixed local/imported presentation order, not a missing canonical
  impl index.
- **TX-1 through TX-4 are red.** Typecheck commits staging before the REPL's
  codegen boundary, so a backend failure leaves live residue.
- **TD-1 and TD-2 are red.** The scheme renderer discards the module component
  of each `FQTraitName`.
- **DF-1 and DF-2 are red.** The expanded-program `Defn` heuristic selects the
  generated helper because no entered-form presentation subject survives.

Use three serial dev/review sub-rounds:

1. **W3a — transaction and diagnostic identity (TX-1..TX-4).**
2. **W3b — scheme and impl-drawer presentation (TD-1, TD-2, IN-3, with IN-1
   and IN-2 as controls).**
3. **W3c — generic zero-argument-macro presentation (DF-1, DF-2).**

W3a is the stateful/high-risk change and establishes the prepared-turn carrier.
W3b is pure/read-only formatting. W3c consumes origin/prepared-turn metadata
but changes no compilation semantics. Each sub-round receives its own
`/review`; combining them would obscure attribution (Principles 5 and 6).

## 1. One entered turn, one transaction

The REPL actor submits one source cluster. The compilation actor expands,
builds, typechecks, derives the exact codegen batch, compiles it, and returns a
terminal result. The REPL displays only after that terminal result.

```text
entered cluster
  -> expand to fixpoint
  -> flatten structural `begin`
  -> build one ordered ParsedEntry sequence
  -> typecheck into fresh staging
  -> prepare live commit + exact codegen batch
  -> codegen
       success -> publish turn + dependent-redefinition handling + display
       failure -> discard turn products + display the located failure
```

The transaction owns all products created for the turn:

- staged symbol-table entries and their staged slots;
- the exact codegen enrollment derived from the turn's finalised program;
- turn-local typecheck-product and introspection updates;
- redefinition outcomes, which remain pending until codegen succeeds.

An error before publication drops these products. Earlier live definitions,
compiled code, introspection, and scheduler terminal state remain unchanged.
The next prompt therefore starts from the last successful turn. This extends
the existing type-error discard rule through codegen; it does not introduce a
second transaction system.

### 1.1 Implementation shape

`process_cluster_with_staging` must stop treating successful `check_forms` as
the publication point. It returns an int-private `PreparedTurn`; it does not
drain staging, replace the caller's `CheckState`, update
`typecheck_products`, or write introspection. The carrier owns:

- the fresh staging table and the post-check `CheckState`;
- warnings, unresolved-dispatch sites, source/introspection records, and the
  source-ordered final program;
- the exact, already-derived codegen name batch;
- an ordered `CommitPlan`, one row per staged entry, containing its final live
  slot, redefinition classification, retained-code action, terminal-closure
  verdict, and final entry shape;
- the precomputed typecheck-product and presentation updates.

Preparation is a pure planning phase with respect to live state. Under the
existing single-owner-per-module cadence, it snapshots the live module's
`next_got_slot`, classifies every entry against the prior live entry, assigns
fresh indices arithmetically from that snapshot, and proves the complete plan
fits `GOT_TABLE_SIZE`. It does **not** call `allocate_got_slot`, advance
`next_got_slot`, push retention owners, patch a GOT cell, or install an entry.
It also runs `check_terminal_closure`, computes slot-less displacement
retention, derives the dependent-redefinition outcomes, and checks that every
batch member has a callable prepared entry. No `Result`-returning validation
is allowed after this phase.

The module cadence is the isolation lock for this optimistic plan: no second
turn for the same module may prepare or publish between snapshot and commit.
Immediately before codegen, the driver revalidates that the module and its
`next_got_slot` still equal the prepared snapshot; a mismatch discards the
turn before any backend/GOT action. The cadence owner is then held through
codegen and publish, making a post-codegen mismatch unrepresentable. Other
modules may progress concurrently because their tables and GOT slabs are
disjoint.

`process_form::finalize_cluster` and `ClusterOnce::Done` carry the owned
`PreparedTurn`; they do not first manufacture a committed
`ProcessedCluster`. Both the eval driver and the worker/batch cadence invoke
the same three operations:

1. `prepare` — typecheck into staging, derive the exact batch, and construct
   the complete commit plan without live mutation;
2. `compile_prepared` — codegen that exact batch against the prepared view;
3. `publish` — consume prepared+compiled state through the infallible commit
   gate, then issue cadence notifications.

On any error from steps 1 or 2, dropping the carrier drops its staging table,
candidate `Code` owners, and pending metadata. The caller retains its prior
`CheckState`; live entries, `next_got_slot`, GOT cells, retention pools,
typecheck products, introspection, and redefinition state are byte-for-byte
unchanged. The dependent-redefinition transaction is invoked only after
publication.

The batch is explicit and closed over the prepared turn. A later prompt must
never discover an earlier failed definition through a module-wide
`code: None` sweep. `derive_codegen_batch` remains the single enrollment
authority, but it reads the staging-first prepared view once and stores the
result on `PreparedTurn`. `compile_prepared` accepts that stored slice; it
neither re-derives nor widens it. This is Principle 7 (Single source of truth)
and Principle 26 (Record from settled state): enrollment is recorded from the
fully expanded, fully typechecked program.

#### 1.1.1 Prepared module view and GOT isolation

The backend's table parameter consumes a `DashMap`, so int materialises an
int-private map for codegen. Unchanged modules are cloned as ordinary read
views. The target module is a staging-over-live overlay whose entries have
already been rewritten to their final planned live slots. Its `got` is
`Arc::clone` of the canonical live `GotTable`, not staging's short-lived slab:
generated calls and `Jit::new`'s `__cranelisp_got_{module}` data symbol must
embed the session's long-lived slab base.

Sharing that slab is safe only because the existing backend call has a
transactional tail:

1. `compile_to_module(module, exact_names, prepared_map, jit, ...)` collects
   and compiles **all** names in the supplied slice;
2. it finalises the whole JIT;
3. only after both operations succeed does
   `write_finalized_got_slots` perform the infallible per-symbol stores.

Therefore a body-compile or JIT-finalise error occurs before the first shared
GOT write. W3a must preserve one `compile_to_module` call for the entire exact
batch. A loop of per-name calls is a transaction violation: an early name
could patch the shared slab before a later name fails.

There is no existing isolated GOT that can replace this arrangement. A fresh
table would make final machine code embed the wrong slab base; copying its
pointers later would not repair baked indirect-call addresses and would
disconnect future hot reloads. Likewise, save-and-restore of live cells would
be transient publication visible to concurrent callers. Both shapes are
rejected.

The shared-GOT call establishes the commit point: after it succeeds, planned
slots contain the new pointers. Everything following it must therefore be
infallible and ownership-only. `compile_prepared` retains the `Arc<Jit>` and
attaches `Code::Jit` plus returned artifacts to the **owned prepared entries**,
not the live map; every lookup it needs was proven during preparation. Then
`publish`:

1. advances `next_got_slot` directly to the precomputed final value;
2. moves (does not recompute) frozen-code owners into `retained_code`;
3. moves the exact prepared entries into live;
4. installs the prepared typecheck product and introspection records;
5. returns the already-computed redefinition outcomes and scheduler products.

These operations use pre-owned values and infallible map replacement under the
module guard. No allocation, slot classification, closure check, batch
derivation, symbol lookup, or backend call occurs in this gate. Retention
owners are placed before the corresponding old live entries are dropped
(Principle 22 — Published pointers have retention owners).

An ABI-preserving redefinition deliberately compiles against its existing live
slot, so backend success patches that slot immediately before the prepared
entry is installed. This is sound precisely because success has crossed the
infallible commit gate. An ABI-changing or new definition writes its
precomputed fresh slot, which is not reachable by a live entry until publish.

This needs only int-private carriers and refactoring of the existing
`commit_staging_to_live` / `inline_jit_codegen_for_names` internals. It adds no
backend entry point, `cranelisp-types` carrier, cache schema, or public API
(Principles 1, 2, and 6).

Batch `--run`/`--link` and worker compilation use these same operations at
their existing cadence boundary. Their notification timing changes to
post-publish; there is no REPL-only typecheck or codegen path (Principle 11).

#### 1.1.2 Macro registration belongs to the prepared world

The current `process_form::form_dispatch::register_macro_in_module` is an
additional pre-commit writer: Pass 1 and
`process_form::process_regular_form` insert macro parents directly into
`ctx.symbol_tables` and write `ctx.introspection` immediately. Such a macro is
absent from typecheck's later staging table and therefore absent from
`PreparedCommit.published_names`. W3c cannot be repaired by carrying
provenance alone; macro registration itself must join the W3a transaction.

The existing int-owned `TurnCheckWorld` from §2.1 is therefore the one
candidate world for the whole entered cluster, not a macro-clause-only
adapter. It is created at the beginning of `process_cluster_once` under the
module's existing cadence ownership:

- `baseline` is the immutable live-table snapshot used for final delta and
  redefinition classification;
- `settled` is the mutable candidate table map used by Pass 0/1/2 macro
  recognition, registration, clause compilation, and final typecheck;
- `pending_introspection` is an FQ-keyed map of complete candidate
  `Introspection` records;
- reserved-slot/JIT owners and cleanup guards hold compiler-time macro clauses
  made executable during the turn.

`process_cluster_once` builds its working `ModuleCompiler` over
`TurnCheckWorld.settled` and `pending_introspection`; scheduler/dependency
readiness remains connected to `SharedState`. A dependency gap discards this
world and retry-from-top creates a fresh one after the dependency is live,
preserving the existing cadence and avoiding parked in-progress state.

`register_macro_in_module` remains the single macro-entry constructor, but its
write target becomes this candidate world. Its binding-conflict query,
`assert_prelude_closure`, and `check_terminal_closure` all read the same
candidate view. It inserts the macro parent and complete authored
introspection record immediately. Existing macro availability order is
therefore preserved: macros registered in Pass 1 remain visible to Pass 2
exactly as today, and an expansion-emitted macro becomes visible to subsequent
forms after its registration point; no earlier form can observe it, and no
same-module non-macro definition becomes newly available during macro
execution.

When subsequent expansion needs clause code, `compile_macro_if_needed` calls
the **same** `process_form::macro_clause::prepare_macro_clause_turn` mechanism
defined in §2.1. In a parent turn it consumes the candidate world, returns the
one `OwnedCompiledMacroTurn`, and **absorbs** its settled entries, exact
closure, JIT/drop-glue owners, and reserved-slot cleanup guard into the parent
prepared turn. It does not publish to `SharedState`, notify the scheduler, or
invoke a second clause compiler. The candidate macro entry therefore sees its
compiled clause through its reserved canonical GOT slot and can be invoked by
later expansion in this cluster.

Those reserved cells are not live publication: the live slot cursor does not
include them and no live entry names them. The parent cadence token prevents a
competing turn from allocating across the reservation. On any later
expansion, projection, typecheck, or backend failure, the parent guard clears
every written reserved cell while its owner is still retained, then drops the
candidate world. No reachable live entry, live cursor, introspection record,
typecheck product, or scheduler state changed. On success,
`publish_prepared_turn` installs owners first, moves candidate macro entries
and introspection, advances the cursor, and only then exposes the cells.

Final preparation computes one canonical `TurnDelta` from `baseline` to the
settled candidate overlay, including typecheck staging. Macro parents and
their synthesized clauses therefore enter `PreparedCommit.published_names`,
the exact codegen/retention plan, and W3c's emitted-subject intersection by
the same canonical FQ keys as ordinary definitions. There is no
macro-specific live commit, before/after scan, or second source of published
names.

This is an int-only refactor of existing `SessionSymbolTable`,
`Introspection`, `TurnCheckWorld`, `PreparedCommit`, and macro-clause
preparation. It requires no frontend/typecheck/backend public API or cache
change. The result is technically **READY**, not blocked on `/arch`.

### 1.2 Recovery scenario matrix

The implementation-strategy unit matrix is:

| Prior live state | Failed turn | Required post-failure state |
|---|---|---|
| no same-named entry | new def fails codegen | name absent; independent literal succeeds |
| compiled same-named entry | ABI-preserving redefinition fails | prior entry, slot, code, and display remain |
| compiled same-named entry | ABI-changing redefinition fails | prior entry remains current; no dependent transaction runs |
| several generated entries | one generated unit fails | none of that entered cluster publishes |
| no generated code | type/build failure | existing typecheck discard behaviour is unchanged |
| near-full live GOT | plan needs too many fresh slots | preparation fails; `next_got_slot` and all cells are unchanged |
| compiled batch | second name fails before finalise | first name has not patched its prior live slot |
| successful ABI-preserving redefinition | backend returns success | GOT patch, entry replacement, `Code` owner, metadata, and outcome all publish as one terminal transition |
| successful ABI-changing redefinition | backend returns success | fresh slot publishes; old slot and code owner remain frozen before prior entry drops |
| cadence interference (unit seam) | live slot cursor differs before codegen | preparation is discarded before any GOT write |
| expansion emits macro, later form invokes it, final projection fails | candidate clause was usable inside turn; macro parent, clause, reserved cell, owner, and introspection all roll back |
| expansion emits macro, later form invokes it, turn succeeds | macro parent and clause publish through one prepared commit; no second compilation or notification path |

Unit strategy splits by seam:

- **prepare:** classification matrix (`New`, ABI-preserving, ABI-changing,
  slot-less displacement), deterministic final slots, closure rejection, exact
  enrollment, capacity exhaustion, and no mutation of live/check/product
  snapshots;
- **ownership:** a changed slot cursor fails the pre-codegen revalidation; a
  held module-cadence token admits no second same-module prepare/publish;
- **compile:** a two-name batch whose second member fails proves zero GOT
  writes and zero `Code`/introspection installation; success returns owned
  compiled entries without installing them;
- **publish:** success moves exactly the planned entries, advances the cursor
  once, retains old owners before replacement, installs products, and returns
  the prepared outcomes; no branch returns `Err`;
- **candidate macro registration:** Pass-1 and expansion-emitted macros write
  only `TurnCheckWorld`; candidate recognition sees them in the established
  order while live symbol/introspection maps remain unchanged;
- **candidate clause absorption:** a later form can invoke the emitted macro
  from its one compiled clause; an injected later failure clears its reserved
  cell and drops all owners, while success publishes without recompilation;
- **cadence parity:** eval and worker drivers both call the same
  prepare/compile/publish helpers and notify only after publish.

The sprint QA plan owns the e2e recovery and subsequent-literal guards.

## 2. Macro-expanded declaration staging (0816)

Macro output is not a special registration class. After Pass 1 reaches its
expansion fixpoint, int flattens structural `begin` exactly once, preserves
the emitted order, builds the whole result, and submits one `ParsedEntry`
sequence to the ordinary `check_forms` Passes 2/3.

Pass 2 registers every declaration head in that sequence before Pass 3 checks
dependent bodies and impl conformance. Consequently, in:

```lisp
(begin
  (deftype T ...)
  (impl Trait T ...))
```

the `impl` resolves the staged `T` regardless of which trait is named or which
macro emitted the forms. `Display`, `Eq`, user traits, and qualified trait
references share the same staging-first lookup. A trait-specific registrar,
derive-macro whitelist, pre-registration scan, or retry after `unknown type`
is rejected (Principles 7, 12, 17, and 24).

The implementation seam is the existing `process_cluster_once` expansion →
structural peel → build → `check_forms` chain. The fix must remove any
per-form call that checks an expanded `impl` before the complete flattened
cluster has entered staging. It must not alter defmacro-before-use or make
same-module non-macro definitions available during macro execution; this
ordering applies after expansion has completed.

### 2.1 On-demand macro clauses: owned check world and exact provenance

The on-demand clause compiler is a smaller transaction with a harder
provenance requirement. Checking a clause can mint concrete `$`
specialisations in dependency modules. The live implementation currently
lets those foreign-module writes escape through `TypeCheckEnv.modules`, then
tries to discover them with a before/after scan of every live `$` name. That
scan is rejected: its answer can include an unrelated worker's concurrent
mint, and filtering the observed names afterwards does not repair the missing
ownership boundary (Principles 18, 24, and 26).

`check_program_compat_no_gap` therefore splits internally into the existing
general compatibility adapter and a macro-only preparation path:

```text
prepare_macro_clause_turn
  -> snapshot live tables into an int-owned TurnCheckWorld
  -> check_forms(target staging, TurnCheckWorld.modules)
  -> freeze the settled world
  -> derive TurnDelta by canonical-key comparison with the owned baseline
  -> derive the closed callee set by keyed reads only
  -> plan slots, retention, codegen, and publication
  -> PreparedMacroTurn
```

`TurnCheckWorld` owns two int-private views:

- `baseline`, an immutable snapshot of the live tables at the cadence point;
- `settled`, a separate table map initially cloned from that snapshot and
  passed as `check_forms`'s `modules`, plus the ordinary target-module staging
  table passed through `SymbolTableAccess::cluster`.

This use of the existing public `check_forms` surface is deliberate.
Current-module writes land in the owned staging table; writes that typecheck
retargets to a dependency or trait-home module land in `settled`, not in the
session's live map. No typecheck public type, `CheckResult` field, shared
carrier, or cache schema changes. The snapshot is a complete read used to
construct an isolated execution world, not a search for an identity.

After successful typecheck, int freezes both owned views. `TurnDelta` compares
the complete canonical-keyed rows of `baseline` and the frozen products and
records every definition that is new or semantically changed by this check.
The target staging rows participate as the target module's settled overlay.
Comparison excludes runtime-only `Code` ownership inherited unchanged from
the baseline; a row is changed when its settled definition payload, slot
eligibility, scheme, AST/view, callees, or other codegen-relevant fields
changed. Because both sides are owned by one turn and no writer can enter
either side after settlement, this is provenance, not a temporal scan of
ambient state. `TurnDelta` is the exact set of definitions minted or changed
by the check, keyed by `FQSymbol`.

The codegen closure is then derived once from settled **codegen views**.
`Def.callees` is not the enrollment carrier: for a polymorphic call it
deliberately records the source/template identity (`helper/bump`), while the
post-monomorphisation `MonoExpr::Apply.dispatch` records the selected
executable storage identity (`helper/bump$Int`). Enrolling from `callees`
would therefore select the slot-less `UserFnState::Polymorphic` template and
miss the concrete row. `callees` remains the redefinition/reporting relation;
macro codegen enrollment consumes the same typed carrier the backend consumes
(Principles 7 and 24).

Exact algorithm:

1. Seed the worklist with the synthesized clause's canonical `FQSymbol`.
2. Fetch that row directly from the settled target staging table and require
   its `ModuleEntry::Def.codegen_view`.
3. Walk the complete `MonoDefnVariant`/`MonoExpr` tree. At each
   `MonoExpr::Apply`:
   - `ApplyRef::Dispatch(fq)` is the selected executable target; enqueue that
     exact `FQSymbol`;
   - `ApplyRef::ViaCallee` contributes no parallel identity. Walk its callee
     expression normally: a `MonoExpr::Var { resolution:
     VarRef::Global(fq), .. }` enqueues that storage identity, while
     `VarRef::Local` and computed closure values add no table dependency.
   Standalone function-valued `MonoExpr::Var::Global` sites are handled by the
   same Var rule. Nested lambdas, branches, bindings, match arms, constructors,
   vectors, tracing, parallel binds, and launch continuations are all visited;
   no expression position is skipped.
4. For each enqueued FQ, perform one keyed fetch from `TurnDelta`. If it is a
   turn-minted/changed concrete callable, enroll it and walk its settled
   `codegen_view` recursively.
5. Otherwise perform one keyed fetch from `baseline`. Record an already
   executable row as an explicitly referenced live dependency lease. A
   baseline row that is not executable is an error; int never derives a `$`
   spelling from the template name.
6. A missing canonical key, a selected template/non-callable row, a required
   row without `codegen_view`, or an absent typed `ApplyRef`/`VarRef` is a
   located preparation error. There is no `ResolvedCall`-string
   reconstruction, `Def.callees` fallback, mangle synthesis, or keyed-miss
   scan.

#### 2.1.1 Cache-restored clause: semantic equality is not executable equality

The W7 mode-equivalence guard exposes one refinement to step 4. A cache
sidecar intentionally restores the settled definition payload but cannot
restore either runtime carrier: `SymbolTable::into_concrete` leaves
`Def.code = None`, and the serde-skipped GOT slab begins with null cells. If
the same authored macro clause is then synthesised and typechecked, its fresh
candidate row is semantically identical to that restored row.
`entry_fingerprint` correctly ignores `Code`, so the ordinary semantic
comparison omits the clause from `TurnDelta`. The closure then treats the
explicit seed as a baseline dependency and rejects it because the cached
object has not yet supplied live Code/GOT.

The error is in enrollment, not in cache restoration and not in semantic
fingerprinting. Runtime carriers are deliberately absent from the persisted
schema, while the freshly checked clause is a settled codegen product. The
smallest repair is therefore an **explicit-seed executable-carrier
classification** after the ordinary semantic delta is frozen and before
`derive_macro_turn_closure` runs:

```text
seed = FQ(target_module, clause_name)
if seed is already in TurnDelta:
    keep it
else if the keyed baseline seed is executable:
    keep it as a leased baseline dependency
else:
    fetch the keyed seed from the fresh target staging overlay
    require a concrete callable with a settled codegen_view
    insert that candidate row into TurnDelta
```

`prepare_macro_clause_turn` remains the actor. It constructs `seed` before
closure derivation and calls one int-private helper (for example,
`enroll_non_executable_seed`) that performs the three keyed reads above.
`entry_fingerprint` remains the semantic comparison authority; it must not
start comparing `Code`, pointer values, or GOT contents. The helper uses the
same executable predicate as `derive_macro_turn_closure`: a supported backend
leaf is executable by construction; an ordinary callable requires both its
canonical slot and a non-null cell in that module's table. That predicate
should be one private function shared by seed classification and the baseline
closure arm, so the two sites cannot disagree.

This is deliberately seed-narrow. The freshly synthesised clause is known to
be a product of this check and its canonical identity is already carried as
`clause_name`. It is therefore valid to prefer that settled candidate when
the old runtime carrier is absent. The helper must not enumerate all
non-executable baseline rows, consult scheduler/cache-origin state, infer a
`$` name, or promote an unrelated row. Reachable dependencies continue
through the typed `MonoExpr` carrier and the existing keyed closure rules.
Thus an unrelated cache-restored non-executable definition remains outside
the batch.

Once promoted, the clause follows the unchanged W3a transaction: slot
planning gives it a fresh reserved canonical cell; the exact whole batch is
compiled; `Code` ownership is attached to the owned candidate; and only the
infallible publish gate moves the entry and advances the cursor. Any
preparation/backend failure clears reserved cells and drops owners without
altering the restored baseline. No cache-load retry, eager object load,
post-publication repair, or second compilation path is introduced.

The required focused matrix is:

| Baseline seed | Fresh candidate | Required result |
|---|---|---|
| same semantic row; `Code = None`; canonical cell null | concrete callable with `codegen_view` | seed enters the exact batch and publishes only after whole-batch success |
| same semantic row; owned `Code`; canonical cell non-null | same candidate | seed remains a leased baseline dependency and is not recompiled |
| semantically changed row, whether baseline executable or not | concrete callable with `codegen_view` | ordinary `TurnDelta` enrollment remains authoritative |
| non-executable same row | template, non-callable, or missing `codegen_view` | located preparation error; no live mutation |
| unrelated non-executable same-semantic row | any settled clone | excluded unless reached independently by an exact typed carrier |

Unit tests belong beside `prepare_macro_clause_turn` and
`derive_macro_turn_closure`; they assert batch membership, lease membership,
fresh-slot planning, exclusion, and byte-for-byte live-table/GOT preservation
before publish and after a discarded turn. The existing
`build_confidence::mode_equiv_macro_user_defined` guard is the production e2e:
all six mode×cache permutations must return 42, with the cached permutations
proving the repaired carrier path and the fresh permutations controlling
semantic behavior.

Existing interfaces suffice. The repair is private to Binary/int and changes
neither a public crate API nor `cranelisp-types`, frontend, typecheck, backend,
cache schema/version, object format, or introspection. It also adds no
presentation metadata from deferred W3c, parallel carrier map,
post-publication failure point, instrumentation, or memory mechanism
(Principles 2, 6, 7, 20, 22, 24, and 26).

The source seam is int-private:
`process_form::macro_clause::prepare_macro_clause_turn` invokes a dedicated
`collect_codegen_dependencies(&MonoDefnVariant, &mut FqWorklist)` visitor.
The visitor pattern-matches the already-public `cranelisp_types::{
MonoExpr, ApplyRef, VarRef}` fields on each settled entry's existing
`codegen_view`; no typecheck API or carrier changes are required.

The resulting `MacroTurnClosure` is a canonical `FQSymbol` keyed set,
topologically grouped by module (SCCs allowed and deterministically ordered).
It contains the clause, every reachable turn-minted/changed dependency, and
only explicitly referenced already-live dependencies. An unrelated `$`
definition cannot enter merely because it exists, was minted concurrently, or
sorts near a member. This applies Principle 7 (Single source of truth),
Principle 24 (Resolve once), and Principle 26 (Record from settled state).

The private `PreparedMacroTurn` owns:

- the frozen target staging and every `TurnDelta` entry selected by the
  closure;
- the exact FQ-keyed closure and per-module backend batches;
- the unchanged live dependency leases needed through codegen;
- the `CheckResult` diagnostics;
- a prevalidated per-module slot and entry replacement plan;
- the old-code retention moves and pending introspection/typecheck-product
  updates.

Preparation acquires the existing cadence ownership for every module whose
row or slot can change, in canonical module order, and snapshots every affected
slot cursor. Before backend entry it revalidates all snapshots and retains
those cadence tokens through compilation and publication. It resolves every
batch member, validates capacity and callable shape, assigns final live slots,
checks terminal closure, and allocates all fallible metadata containers before
backend entry. A failure drops `PreparedMacroTurn`; neither live tables nor
GOT cells have changed.

Backend compilation consumes the stored per-module batches in dependency
order and returns owned JITs, entry pointers, artifacts, and generated
drop-glue artifacts. The compilation phase does not publish an entry as soon
as an individual module succeeds. Its result is an
`OwnedCompiledMacroTurn`; on any later backend failure, all candidate owners
drop together and the session remains at the baseline state.

Generated code must embed the session's canonical long-lived GOT slab; a
scratch slab would bake the wrong address and break later hot reload. Every
turn-minted/changed macro dependency therefore receives a prevalidated **fresh
reserved slot**, even when it supersedes a live definition. The backend may
write finalized pointers into those reserved canonical cells while the
candidate JIT owners remain held by `OwnedCompiledMacroTurn`, but the cells are
not yet published: the live slot cursor does not include them and no live
entry names them. Existing callers continue to use the prior entry and slot.
An unwind/error guard clears every written reserved cell while its JIT owner is
still alive, then releases the owners; cursor, entries, and all reachable GOT
cells remain at baseline. Reusing or patching an existing live slot during
macro-turn compilation is forbidden. This preserves the existing backend
public API and the canonical-GOT requirement while making whole-closure
rollback internal to int.

Publication consumes `OwnedCompiledMacroTurn` and has no `Result`-returning
operation:

1. move the JIT owner and every generated drop-glue owner into their
   session retention homes;
2. move every displaced, still-published prior `Code` owner into
   `retained_code`;
3. move the prepared entries into live tables, making their already-written
   reserved cells reachable for the first time;
4. advance slot cursors and install typecheck/introspection products;
5. emit scheduler completion notifications.

Owners precede pointers, and displaced owners precede entry replacement
(Principle 22 — Published pointers have retention owners). All allocation,
lookup, validation, and notification payload construction happened during
preparation or compilation; publication consists only of moves, atomic stores,
and infallible replacements under the retained cadence tokens.

### 2.2 Descriptor and executable clause are distinct states

The pre-codegen clause descriptor carries syntax and matching data only:

```rust
struct MacroClauseDescriptor {
    params: Vec<MacroParam>,
    rest_param: Option<Symbol>,
    clause: FQSymbol,
}
```

It has no callable pointer and cannot be invoked. Successful publication
constructs the separate execution state:

```rust
struct ExecutableMacroClause {
    entry: NonNull<u8>,
    owner: Code,
    abi: MacroClauseAbi,
    params: Vec<MacroParam>,
    rest_param: Option<Symbol>,
}

enum MacroClauseAbi {
    SexpListToSexpI64V1,
}
```

`Code` is non-optional. `NonNull<u8>` makes a null callable unrepresentable,
and `MacroClauseAbi` records the exact witness required before the cast. The
only unsafe seam converts `entry` under
`SexpListToSexpI64V1` to `extern "C" fn(i64) -> i64`. Its caller must hold the
`ExecutableMacroClause` (therefore its `Code` owner) across argument
marshalling, the signal-protected call, result unmarshalling, and span
rewriting; the input word is a live runtime `(SList Sexp)` allocation and the
returned word is interpreted under the same ABI. No `Option<Code>`, raw
pointer plus separately looked-up lease, or descriptor-with-late-pointer state
survives this split (Principles 20 and 22).

### 2.3 Macro-turn test strategy

The strategy-bearing seams live with focused unit scenarios:

- **owned-world isolation:** a check that mints a dependency `$` writes only
  the turn world; live tables, live slots, and typecheck products are unchanged
  before publish;
- **concurrent unrelated exclusion:** after the turn snapshot, another worker
  publishes an unrelated `$` definition in the same or another module; the
  prepared closure is byte-for-byte unchanged and excludes it;
- **reachable typed-carrier closure:** a clause calling polymorphic
  `helper/bump` carries `ApplyRef::Dispatch(helper/bump$Int)`; the concrete
  delta row is enrolled, the slot-less `helper/bump` template is not.
  Direct, transitive, function-valued, duplicate, and cyclic typed references
  include exactly the canonical reachable changed rows;
- **already-live dependency:** an explicitly referenced callable live callee is
  leased but not recompiled; a referenced concrete `TurnDelta` row joins the
  prepared batch; an explicitly selected baseline template is rejected; an
  unreferenced live row never joins;
- **keyed-miss negative:** a missing dispatch/global key, selected template,
  or absent typed carrier fails preparation at the recorded call site and
  never falls back to `callees`, mangle reconstruction, or enumeration;
- **all-or-nothing backend:** a later module/member failure publishes no
  earlier compiled pointer or owner;
- **owner-before-pointer:** executable publication installs JIT/drop-glue and
  displaced-code owners before any pointer/entry replacement;
- **state split:** a `MacroClauseDescriptor` cannot enter invocation;
  `ExecutableMacroClause` construction rejects null/missing-owner/wrong-ABI
  inputs, and invocation retains the owner for the complete unsafe call
  window.

The production-path e2e guard uses two independently scheduled modules: one
macro clause forces a concrete specialization while another turn mints an
unrelated `$` specialization. Repeated runs must invoke the macro correctly,
must never compile or publish the unrelated symbol as part of the macro turn,
and must leave the unrelated turn under its own scheduler notification. This
is an ordinary behavior/production-path guard; it requires no allocator,
fault-injection, or cyber-sensitive instrumentation.

## 3. Failed-unit diagnostic attribution (0817, separate cell)

Rollback and naming are independent obligations. The codegen error wrapper
must receive the exact `FQSymbol` currently being compiled from the explicit
batch iterator. It must not infer an owner from the failing AST's callee,
ambient module cursor, punctuation spelling, a last-seen symbol, or iteration
order.

The resulting diagnostic identifies:

- the module-qualified compilation unit (`collections.vec/vec-flatten`, or its
  actual generated unit);
- the original located backend error and source file/span when available.

`codegen failed for /` in an error about `vec-concat` is therefore a
wrong-unit-attribution defect even when recovery works. The wrapper is a pure
formatting carrier over the batch identity; it neither controls rollback nor
retries. This follows Principle 24 (Resolve once): the batch already contains
the identity, so the diagnostic consumes it.

Where the backend reports only a batch-level error, int names the batch member
it deliberately asked the backend to compile at that call boundary. It must
not parse the backend message to rediscover a name.

## 4. `/info <Type>` inverse impl enumeration (0839)

The REPL already has the canonical impl relation used by `/info <Trait>`.
`/info <Type>` must read the inverse projection of that same relation:

```text
canonical impl rows: (FQTraitName, FQTypeName)
       trait query -> filter by trait, display target types
       type query  -> filter by target type, display traits
```

This is complete-set enumeration, not name resolution (Principle 24's
enumeration carve-out). The existing `impls_for_type_in_view` relation reader
is retained; IN-1 and IN-2 prove that it already supplies the required local
and inverse-twin pairs. W3 must not replace it with a second global scanner or
mutable reverse index.

The type branch compares the queried type's canonical `FQTypeName`, including
an imported or qualified query resolved to its home. Its `; impl:` rows render
through the existing normative related-symbol layout: **unqualified names,
locally-defined traits first, then imported traits**, with deterministic order
within each partition. Canonical identity is retained until that final display
projection; it is not reconstructed from the rendered bare name. Re-entering
the same `(trait, type)` impl replaces methods but does not add a row. Name
poisoning upstream makes two distinct visible same-bare-name traits illegal,
so the final bare-name projection does not conflate two live candidates.

The implementation refinement is narrow: retain enough provenance to partition
each candidate as local versus imported before projecting to `TraitName`. A
single lexical sort of bare names is wrong because it can put an imported
trait before a local trait; sorting by fully-qualified identity is also wrong
because this drawer's normative order is scope-relative.

The reader is REPL-only and int-private. It adds no compile-necessary index and
no cross-crate API. Complexity remains linear in the visible impl set on an
explicit `/info` request (Principles 6 and 7).

## 5. Canonical constrained-type rendering (0802)

`Scheme.constraints` already carries `FQTraitName`; the renderer currently
throws away the module by mapping each item to `t.name`. `format_scheme_type`
must instead carry the full identity into
`format_type_with_inline_constraints` and render `:{module}/{trait} var`.

There is one scheme renderer for definition echoes, bare lookup, `/sig`,
`/info`, `/list`, overloaded-variant rows, and search envelopes. Callers must
not add qualification after rendering. Constraints sort by canonical
fully-qualified text for deterministic output. Primitive/ADT type rendering
and unconstrained schemes are unchanged.

This is an int-local formatting correction: no stored type or public API
changes. It applies Principle 7 and preserves the typecheck-produced settled
constraint identity (Principle 26).

## 6. `def` presentation, faces DF-1 and DF-2 (0800)

`def` is not recognised by the parser or compiler as a core form. Int must not
branch on the literal spelling `def`, on `-def`, or on the stdlib module
(Principles 10 and 19).

### 6.1 Carriers and single record

Expansion returns int-private provenance with the expanded form:

```rust
struct EnteredMacroProvenance {
    origin: Sexp,
    macro_id: FQSymbol,
    emitted_public_subjects: Vec<FQSymbol>,
}

struct PreparedPresentation {
    subject: FQSymbol,
    scheme: Scheme,
    source: String,
}
```

`macro_id` is the exact identity returned by
`cranelisp_types::resolve_macro_head` at the outer entered form's recognition
site. It is not reconstructed from the written head and is not recovered by
scanning introspection after expansion. `emitted_public_subjects` is collected
from the definitions emitted by that invocation and accepted by the ordinary
Pass-1/build path. It is an ordered, canonical-FQ set; visibility is read from
those emitted definitions, so private definitions and generated helpers never
enter it. Nested expansion may add emitted forms, but it does not replace the
outer entered form's `macro_id`.

`PreparedCommit` gains
`presentation: Option<PreparedPresentation>`. The surviving canonical record
is the selected subject's existing `Introspection`, with one crate-private
`presentation_scheme: Option<Scheme>`. Its existing `source` remains the only
authored-source field. There is no `SharedState.presentation_schemes`, no
second source field, and no reader-side inference. The accidental public
exposure of `Introspection` is narrowed as directed by BC §6; the established
public read views `SymbolInfo` and `SymbolDescription` are unchanged.

### 6.2 Selection is total and structural

Selection runs only when the entered outer form was actually recognised and
expanded as a macro. The exact cases are:

| Expansion result | Presentation result |
|---|---|
| no emitted PUBLIC subject | `None`; the turn follows its ordinary expression/side-effect display |
| exactly one emitted PUBLIC subject, and it is a zero-argument macro in the settled candidate table | project it and store `Some(PreparedPresentation)` |
| exactly one emitted PUBLIC subject of any other kind, including a non-zero-argument macro | `None`; retain its ordinary symbol-table classification and display |
| more than one emitted PUBLIC subject | located pre-commit error; do not guess which subject represents the entered form |
| any number of PRIVATE emitted definitions, with zero/one public subject | private definitions are excluded; apply the corresponding public-subject row |
| arbitrary expression output with no public definition | no subject and no projection; ordinary expression handling |
| direct `defmacro` or another ordinary non-invocation definition | no `EnteredMacroProvenance`; ordinary `defmacro` presentation |

The zero-argument test reads the selected candidate `ModuleEntry::Def {
kind: DefKind::Macro { clauses_meta, .. } }` and requires a clause with no
fixed or rest parameters. It does not test the names `def`, `-def`, a generated
`*-def` suffix, or any module identity. A multiple-public-subject expansion is
an error even if only one member happens to be a zero-argument macro: the
language-visible subject relationship would otherwise depend on a
presentation-specific heuristic.

### 6.3 READY source sequence

The exact implementation sequence is:

1. `process_form::macro_resolution::SymbolTableMacroResolver::recognize`
   already receives the canonical `FQSymbol`; the outermost call through
   `try_expand_sexp` must return that identity alongside its expanded `Sexp`.
   `process_cluster_once` retains it with the entered origin. Ordinary nested
   recognition continues to drive expansion but cannot overwrite it.
2. `process_form::form_dispatch` / Pass 1 inserts definitions built from that
   expansion into the cluster's `TurnCheckWorld`, never the live map.
   `register_macro_in_module` returns the emitted macro's FQ name and declared
   visibility while using the same candidate table as recognition. The
   cluster spine records only PUBLIC names attributable to this entered
   expansion on `EnteredMacroProvenance`; it does not diff or enumerate the
   ambient table. Any clause compiled for later same-cluster expansion is
   absorbed into the parent turn per §1.1.2.
3. `finalize_cluster` passes the world and provenance into
   `worker::prepare_cluster_commit`. After `check_cluster_to_staging` has
   settled into the candidate overlay and the canonical `TurnDelta`,
   `PreparedCommit.tables`, `published_names`, and final slots are complete,
   preparation intersects the carried subject set with the exact prepared
   publication plan and applies §6.2. A mismatch is an invariant error, never
   a fallback scan.
4. For the one eligible subject, construct its nullary subject `Sexp` and call
   the existing `process_form::macro_resolution::try_expand_sexp` through a
   `ModuleCompiler` whose `symbol_tables` is `PreparedCommit.tables`. Then call
   `worker::infer_presentation_scheme` with those same candidate tables. This
   is the ordinary depth-one expansion plus build/`__expr` dry-typecheck path:
   no runtime value is invoked, no codegen runs, and the dry staging is
   discarded.
5. Store the settled `Scheme`, selected `FQSymbol`, and authored source in
   `PreparedPresentation`. Expansion, build, dependency, or typecheck failure
   returns from preparation; dropping the prepared turn leaves live symbol
   tables, GOT reachability, introspection, scheduler state, and prior
   presentation unchanged. Only after this step may
   `worker::compile_prepared_turn` enter the backend.
6. `worker::publish_prepared_turn` consumes the prepared presentation at the
   existing eval-cadence publication gate. For each published subject it
   installs one complete `Introspection` record: the turn's normal
   source/sexp/expanded/AST/CLIF fields plus
   `presentation_scheme = Some(scheme)` only for the selected subject and
   `None` otherwise. Record replacement is the atomic publication unit; a
   successful direct redefinition therefore clears a stale projection by
   replacement with `None`, and symbol removal removes its introspection
   record. No fallible projection work occurs here.
7. `eval.rs` chooses the definition echo from the carried selected subject,
   not from an expanded-program helper heuristic.
   `repl::format::format_def_entry_doc`, `/sig`, and `/info` all call one
   crate-private accessor over the subject's `Introspection`: projected
   scheme when present, ordinary `ModuleEntry` scheme otherwise. `/source`
   and `/info` read that same record's existing authored `source`.

For today's stdlib expansion this projects `n` through the emitted public
zero-argument macro `n` to `Int`, yielding an `n` definition echo and
value-shaped `/sig`/`/info`; generated `n-def` remains ordinarily
introspectable when named directly. Supporting application/currying of a
function-valued `def` is DF-3 and remains out of scope.

This sequence applies Principle 7 (Single source of truth), Principle 24
(Resolve once), and Principle 26 (Record from settled state). The projection
is REPL metadata only: it never changes resolution, macro arity, runtime
invocation, codegen enrollment, or symbol-table classification.

### 6.4 Production-test contract

`/dev` must add private unit tests for the carrier/selection/publish seams and
`/testing` must retain production REPL tests for user-visible behavior:

- resolved alias/import/re-export macro identity survives expansion; a same
  spelling in another module cannot capture attribution;
- zero public subject and arbitrary-expression output take the ordinary path;
- one public zero-argument macro projects, while one public non-zero-argument
  macro remains `defmacro`;
- private helpers are excluded, including private-helper plus one-public-subject;
- an expansion-emitted macro is visible to the next form in the same cluster
  at the established availability point, while an earlier form cannot see it;
- before final commit, emitted macro parents and their introspection exist only
  in `TurnCheckWorld`; `PreparedCommit.published_names` nevertheless includes
  them by canonical FQ identity;
- later-form invocation uses one absorbed clause compilation; owner/closure
  assertions prove there is no compile-again publication path;
- two public subjects fail before backend entry and publish no symbol,
  introspection, GOT reachability, or scheduler completion;
- projection expansion failure and dry-typecheck failure preserve the prior
  live definition and prior canonical introspection record, and clear any
  reserved clause cells created for same-cluster expansion;
- a successful projected definition makes echo, `/sig`, and `/info` render the
  identical projected scheme, while `/source` and `/info` retain the authored
  origin;
- a generated helper queried explicitly keeps its ordinary definition scheme;
- direct successful redefinition clears `presentation_scheme`; removal removes
  the record; redefining with another projection replaces it rather than
  retaining the old one;
- a direct ordinary `defmacro` remains a macro and never acquires projection;
- the test macro uses an unrelated name and module so no implementation can
  pass by recognising `def`, `-def`, `stdlib`, or a `*-def` helper convention;
- Run/Link controls compile the same macro expansion without allocating or
  consulting REPL introspection, and no test executes the projected runtime
  value merely to learn its scheme.

### 6.5 S118 delta note — preconditions re-verified at HEAD (`d1c34699`)

FIXME 0863 carries this §6 (with §1.1.2) into Sprint 118 as the deferred `/dev`
handoff. `/arch` confirmed it **READY** (S118 ruling 11) and serialized it as a
late wave **after** FIXME 0745, because both touch the `src/` publication /
result-owner seams and must not interleave. This design predates the W7
cached-macro clause repair (§2.1.1), so its preconditions were re-read at HEAD.
**No redesign follows; this is a reconciliation record.**

**Unchanged — the §6/§1.1.2 premises all still hold, unmet, at HEAD:**

- `TurnCheckWorld` is still constructed *inside* `prepare_macro_clause_turn`
  (`src/process_form/macro_clause.rs:479`), not at `process_cluster_once`. §1.1.2
  step 1 (move the ownership boundary before Pass 1) is untouched work.
- `prepare_macro_clause_turn` still **self-publishes**: `compile_macro_clause_core`
  calls `turn.publish(env)` directly (`macro_clause.rs:105`, `:175`). §1.1.2 step 3
  (return an owned prepared result the parent absorbs) is untouched work.
- `register_macro_in_module` is still an additional pre-commit writer — it writes
  `env.introspection` (`src/process_form/form_dispatch.rs:348-368`) and the live
  `env.symbol_tables` (`:369+`) immediately. §1.1.2's diagnosis is exact.
- No `EnteredMacroProvenance`, `PreparedPresentation`, or `presentation_scheme`
  exists anywhere in `src/` or `crates/`, and `worker::PreparedCommit`
  (`src/worker.rs:21-34`) has no `presentation` field. The W3c removal was clean;
  nothing half-landed.
- `Introspection` is int-private (`src/session_v4/types.rs:311`), so §6.1's
  "one crate-private `presentation_scheme`" remains a zero-public-API,
  zero-cache-schema change — consistent with S118's single-schema-window fence.

**Two deltas the implementing wave must absorb:**

1. **The W7 seed classification must follow the ownership boundary.** §2.1.1
   landed `enroll_non_executable_seed` + the shared `baseline_entry_is_executable`
   predicate (`macro_clause.rs:376-443`), which classify the clause seed against
   `TurnCheckWorld.baseline` — a snapshot of the **live** tables. Once §1.1.2
   makes the clause turn absorbable, the parent's candidate world becomes the
   relevant prior state, and both the seed classification and the shared
   executable predicate must read it. In particular, a clause already compiled
   into a **reserved-but-unpublished** cell by an earlier absorbed clause turn in
   the same cluster must classify as *executable*, or a second expansion in that
   cluster re-enrolls and recompiles it — contradicting §6.4's "later-form
   invocation uses one absorbed clause compilation … no compile-again publication
   path". The §2.1.1 five-row matrix keeps its rows; its "baseline" column is
   re-read as "the world the parent turn owns".
2. **Absorbed drop-glue rows move as pairs.** `PreparedMacroTurn` accumulates
   `compiled_drop_glues` (`macro_clause.rs:117-122`, `:158-163`) and its `publish`
   installs them into `SharedState.fresh_jit_drop_glues` as `{artifact, owner}`
   values (`:182-187`). When absorption folds that publish into the parent gate,
   those rows must move **as pairs**, preserving the invariant
   `design/int/result-owner.md` §3.1.1 pins: a row is replaced atomically with its
   retention owner, and no third writer of that map exists. This is a coupling
   0745 introduces on the consumption side and 0863 must not break.

**Handoff order (binding, arch ruling 11).** 0745 lands *and reviews* first. The
0863 wave then rebases its reading of the turn transaction on the post-0745
state — which, for the transaction itself, is unchanged: 0745 modifies neither
`prepare_cluster_commit`, `compile_prepared_turn`, nor `publish_prepared_turn`
(`result-owner.md` §3.0/§11); it only consumes the map those seams populate.

## 7. Quality attributes and interface assessment

- **Simplicity / maintainability:** one prepared-turn boundary, one existing
  impl-view reader, one scheme renderer; no trait-specific macro path or reverse
  index.
- **Observability:** ordinary located compiler errors remain; only their owner
  identity is corrected. No new trace, allocator/RC diagnostic, fault
  injection, or cyber-sensitive instrumentation is introduced.
- **Concurrency:** a prepared turn remains owned by its existing cadence
  driver and is not parked in shared maps. Publication remains at the existing
  commit gate.
- **Performance:** only explicit `/info` performs complete impl enumeration.
  Codegen batch derivation is bounded to the entered turn.
- **Testability:** prepared-turn commit/discard, provenance selection,
  complete-record replacement, and impl-pair collection are int-private
  pure/owned seams with the matrices above; production REPL tests pin the
  shared reader and stale-metadata lifecycle. W7 additionally pins the
  semantic-equal/cache-restored macro-clause carrier at the private seed
  enrollment seam and through the six-permutation production guard.
- **Public API:** none. `src/` gains only private types/helpers;
  `cranelisp-exe-bundle` is untouched; no `public-api.txt`,
  `cranelisp-types`, frontend, typecheck, or backend public change is required.
  BC §6 explicitly narrows the accidental `Introspection` exposure; no new
  public DTO or cache-schema field is introduced.

## Next skills

- `/dev` — narrow to Binary/int for the W7 seed-enrollment helper, shared
  executable predicate, and focused unit matrix in §2.1.1.
- `/testing` — retain
  `build_confidence::mode_equiv_macro_user_defined` as the production
  mode×cache defect guard; no new e2e mechanism is required.
- `/review` — verify seed-narrow enrollment, unchanged W3a
  prepare→whole-batch-codegen→publish atomicity, and zero interface/cache
  schema drift.
- `/sprint` — record the W7 regression disposition after `/dev` and `/review`
  complete; W3c presentation expansion remains deferred and untouched.
