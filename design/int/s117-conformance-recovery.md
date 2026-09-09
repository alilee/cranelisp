# Sprint 117 — REPL conformance and failed-turn recovery

This subordinate design elaborates the Binary/int master for Sprint 117 Tracks
A and B. It covers FIXME 0816 (macro-expanded declaration staging), 0817
(failed-codegen recovery and diagnostic attribution), 0839 (`/info <Type>`
inverse impl enumeration), 0802 (constraint rendering), and FIXME 0800's
multi-definition REPL result. `def` remains the zero-argument stdlib macro
specified in `stdlib/defs.cl`; function-valued `def` behaviour (DF-3) is a later
stdlib/REPL API choice, not a core-form or language-spec decision.

The design stays inside the one v4 pipeline (Principle 11 — Single pipeline,
mode parameters) and adds no instrumentation or memory mechanism. S117 changed
no public crate interface; the S121 amendment consumes the separately approved
and baseline-confirmed `publish_compiled_staged` types boundary plus the
separately user-approved absent-key `ChangeAbi` semantic extension. The latter
changes no generated Rust surface line; int adds no further public delta.

> **S121 macro-checkpoint amendment (user-approved 2026-09-03).** The original
> cluster-wide macro staging in §§1.1.2 and 2.1 is superseded. A complete
> authored or expansion-produced `defmacro` is an immediate, one-module
> publication checkpoint. A later form failure retains that macro. Ordinary
> definitions still form one HM binding cluster and retain the prepared
> all-or-nothing publication described by §1. `PreparedMacroTurn`,
> `TurnCheckWorld`, `TurnDelta`, candidate invocation, reserved unpublished GOT
> cells, and cross-module rollback are deleted rather than adapted. The current
> design is stated in the amended sections below.

## 0. Phase-5 refinement against the W1 guards

The W1 results narrow W3:

- **MB-1 through MB-4 are green.** The existing expansion → structural peel →
  one `check_forms` path already satisfies §2. W3 must preserve it and must not
  add a trait-specific or per-expanded-form staging path. S121's macro-local
  owner-free staging is the executable `defmacro` checkpoint, not an alternate
  route for the ordinary declarations emitted by expansion.
- **IN-1 and IN-2 are green; IN-3 is red.** The inverse relation is already
  complete enough for local/re-impl and inverse-twin coverage. The remaining
  defect is mixed local/imported presentation order, not a missing canonical
  impl index.
- **TX-1 through TX-4 are red.** Typecheck commits staging before the REPL's
  codegen boundary, so a backend failure leaves live residue.
- **TD-1 and TD-2 are red.** The scheme renderer discards the module component
  of each `FQTraitName`.
- **DF-1 and DF-2 are red.** The singular definition result selects one emitted
  definition and cannot report a statement's complete definition set.

Use three serial dev/review sub-rounds:

1. **W3a — transaction and diagnostic identity (TX-1..TX-4).**
2. **W3b — scheme and impl-drawer presentation (TD-1, TD-2, IN-3, with IN-1
   and IN-2 as controls).**
3. **W3c — ordered multi-definition result presentation (DF-1, DF-2).**

W3a is the stateful/high-risk change and establishes the ordinary prepared
carrier. W3b is pure/read-only formatting. W3c consumes exact publication
identities; S121 records macros at their checkpoint while ordinary definitions
remain pending until W3a publication. Each sub-round receives its own
`/review`; combining them would obscure attribution (Principles 5 and 6).

## 1. One ordinary HM cluster, with source-ordered macro checkpoints

The REPL actor submits one source cluster. Int walks it in source order,
committing each complete `defmacro` as a checkpoint while accumulating the
expanded non-macro forms into one ordinary HM binding cluster. The REPL reports
the terminal result after processing stops, but publication may already have
crossed one or more macro checkpoints.

```text
entered cluster
  -> walk authored and emitted forms in source order
       defmacro -> check all clauses and expansion-time closure
                -> codegen all clauses
                -> publish parent + clauses in one module transaction
                -> checkpoint the remaining work
       ordinary -> expand and accumulate
  -> typecheck the complete ordinary HM binding cluster into fresh staging
  -> prepare exact codegen batch
  -> codegen
       success -> publish ordinary cluster + dependent-redefinition handling
       failure -> discard ordinary products; keep earlier macro checkpoints
```

The ordinary-cluster transaction owns all non-macro products created after
expansion:

- staged symbol-table entries and their staged slots;
- the exact codegen enrollment derived from the turn's finalised program;
- turn-local typecheck-product and introspection updates;
- redefinition outcomes, which remain pending until codegen succeeds.

An error before ordinary publication drops these products. Earlier live
definitions and every successful macro checkpoint remain unchanged. The next
prompt therefore starts from the last successful publication boundary. This
extends the existing type-error discard rule through ordinary codegen while
making macro availability match its source-ordered compile-time semantics.

### 1.1 Implementation shape

For the accumulated ordinary HM cluster, `process_cluster_with_staging` must
stop treating successful `check_forms` as
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
batch member has a callable prepared entry. The final types-owned publication
still revalidates the submitted staging and owner set against the live table;
its refusal is an expected internal error path, not an unreachable state.

The module cadence is the isolation lock for this optimistic plan: no second
turn for the same module may prepare or publish between snapshot and commit.
Immediately before codegen, the driver revalidates that the module and its
`next_got_slot` still equal the prepared snapshot; a mismatch discards the
turn before any backend/GOT action. The cadence owner is then held through
codegen and publish, making a post-codegen mismatch unrepresentable. Other
modules may progress concurrently because their tables and GOT slabs are
disjoint.

`process_form::finalize_cluster` carries the owned `PreparedTurn`; it does not
first manufacture a committed `ProcessedCluster`. Both the eval driver and the
worker/batch cadence invoke the same three operations:

1. `prepare` — typecheck into staging, derive the exact batch, and construct
   the complete commit plan without live mutation;
2. `compile_prepared` — codegen that exact batch against the prepared view;
3. `publish` — consume prepared+compiled state through
   `publish_compiled_staged`, then issue cadence notifications.

On any error from steps 1 or 2, dropping the carrier drops its staging table,
candidate `Code` owners, and pending metadata. A step-3 refusal returns every
submitted owner; int keeps those owners alive while restoring every touched
GOT cell, then releases them. The caller retains its prior `CheckState`; live
entries, slot authority, retention pools, typecheck products, introspection,
and redefinition state remain unchanged. The dependent-redefinition
transaction is invoked only after publication.

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

The existing backend call has a batch-finalization tail:

1. `compile_to_module(module, exact_names, prepared_map, jit, ...)` collects
   and compiles **all** names in the supplied slice;
2. it finalises the whole JIT;
3. only after both operations succeed does
   `write_finalized_got_slots` perform the infallible per-symbol stores.

Therefore a body-compile or JIT-finalise error occurs before the first shared
GOT write. W3a preserves one `compile_to_module` call for the entire exact
batch. A loop of per-name calls is a transaction violation: an early name
could patch the shared slab before a later name fails.

There is no existing isolated GOT that can replace this arrangement. A fresh
table would make final machine code embed the wrong slab base; copying its
pointers later would not repair baked indirect-call addresses and would
disconnect future hot reloads. The canonical cells are therefore used, but
the module writer guard is acquired before backend finalization can touch them
and retained through publication or restoration. A reader cannot observe the
intermediate cell values.

The shared-GOT call is not the live table commit point. `compile_prepared`
retains the returned owners and snapshots every touched cell before backend
entry. It then submits the original owner-free staging, decisions and exact
per-symbol owner map to `publish_compiled_staged`. Success atomically installs
the final lifecycle bindings and owners and returns displaced owners for int to
retain before release. Refusal leaves the table unchanged and returns all
candidate owners; int restores reused cells to their prior pointers and fresh
cells to null while those owners are still alive. No ownerless body becomes
visible and no pointer outlives its owner.

An ABI-preserving redefinition deliberately compiles against its existing live
slot. The module writer guard prevents readers from pairing that temporary new
pointer with the old binding; publication installs the new binding and owner,
while refusal restores the old pointer before releasing the guard. An
ABI-changing or new definition writes its precomputed fresh slot, which is not
reachable by a live entry until publication.

This consumes the approved `publish_compiled_staged` types boundary and needs
only int-private orchestration around it. It adds no further backend entry
point, types carrier, cache schema, or public API (Principles 1, 2, and 6).

Batch `--run`/`--link` and worker compilation use these same operations at
their existing cadence boundary. Their notification timing changes to
post-publish; there is no REPL-only typecheck or codegen path (Principle 11).

#### 1.1.2 A complete `defmacro` is its own publication checkpoint

Macro registration does not join the later ordinary `PreparedCommit`. Int
processes direct and expansion-produced `defmacro` forms at their source-order
position. For one macro it constructs an owner-free staging table containing
the parent group and every active synthesized clause, checks all clauses as one
definition unit, compiles the complete clause batch, and publishes that table
through the ordinary one-module `publish_compiled_staged` path. A failed
clause check, dependency resolution, codegen, or publication publishes neither
the parent nor any clause. Once publication succeeds, a later form cannot roll
it back.

This ordering is the availability rule:

```text
ordinary form before macro -> expands without seeing that macro
defmacro                  -> complete check + codegen + publication
ordinary form after macro -> may invoke the committed macro
```

Ordinary forms on either side remain members of the same eventual HM binding
cluster. They are accumulated, not published at the macro boundary, and cannot
be expansion-time helpers for the macro. A macro may use only already-committed
same-module macros and already-available dependency-module functions or
realizations. This is why a macro checkpoint is independently valid while an
arbitrary locally successful ordinary form is not.

The source-order driver checkpoints its **remaining work**, not compiled
candidate state. The retry carrier retains the already-expanded ordinary forms
that precede the checkpoint, the unprocessed source/emitted suffix, and the
entered-form provenance needed for presentation. After a `ResolutionGap`:

- a gap before or during a macro leaves that macro uncommitted and retries it;
- a gap after a committed macro retries only the uncommitted suffix;
- ordinary forms accumulated before the macro remain in the eventual HM
  cluster; and
- a generated macro is never recreated by re-expanding its originating form.

Thus retry does not interpret a committed checkpoint as a duplicate source
definition. A second same-named `defmacro` occurrence in the original work
packet is still an illegal same-cluster redefinition; only a later REPL turn or
reload generation may request redefinition. The scheduler continues to own the
sole `ResolutionGap` wait/requeue crossing. The retained continuation is source
work, not a typecheck world, compiled-owner stack, or reserved-GOT rollback
carrier.

An allowed dependency gap is handled independently: the macro transaction is
discarded, the dependency module finishes its ordinary publication, and the
same macro is retried against that larger live world. A successfully published
dependency remains even if the macro or a later form fails. Any concrete
realization required from a dependency follows that module's normal scheduler
and publication path; it is not copied into or rolled back with the macro.

Macro redefinition and reload use the same checkpoint. The prior macro remains
fully executable until all replacement clauses have checked and compiled. The
module writer guard then publishes the new parent metadata and every active
clause owner together. Shared clause indices preserve their ABI-compatible
slots; new indices receive new slots. When a prior parent has `N` clauses and
its replacement has `M < N`, int derives the exact surplus keys for the
half-open index range `M..N` from that prior parent's clause metadata. It does
not scan the symbol table by spelling or prefix. Every selected live row must
be private and have `CallableOrigin::MacroClause { group }` naming that same
parent; a missing row, a foreign group, or any other origin is a transaction
refusal.

The replacement staging deliberately omits those surplus keys and supplies one
explicit absent-key `StagedPublicationDecision::ChangeAbi` for each of them in
both the isolated plan and the final `publish_compiled_staged` call. This uses
the approved absent-key meaning of `ChangeAbi`: retire this exact prior
callable, retain its slot as an `AbiChanging` tombstone, and publish no binding
at the key. Int never emits an absent-key decision for `Plain`, `Clause`,
trait-method, platform, primitive, constructor, accessor, or any other
ordinary callable removal; only the validated surplus `MacroClause` set is
eligible. The decision list for plan and final publication is identical.

The publication record for each retired clause returns its displaced owner.
Int moves all such owners into session retention before releasing the writer
guard. Their old GOT slots remain frozen at the old pointer and permanently
unallocatable through the table's tombstones; neither publication nor rollback
clears or reuses them. Thus a 3-clause macro redefined to 1 preserves index 0
and retires indices 1 and 2, while a later 1-to-3 redefinition preserves the
current index 0 and mints fresh slots for new indices 1 and 2 rather than
reclaiming either tombstoned slot. A successful replacement remains after a
later reload form fails. A failed replacement leaves the prior parent,
clauses, pointers, owners, tombstones, and introspection unchanged.

Dependent-recompilation handling begins only after the checkpoint has
published. It is not part of macro success and must not keep a checked macro in
candidate state. If the §18 redefinition/reload cure later reports or blocks,
its own rules govern dependants, but it does not roll the committed macro back.

A Replace/reload continuation also records that generation setup has already
run. Retrying after a gap must not clear or reconstruct the module a second
time, because that would erase the macro checkpoint just committed by the same
reload. A new watcher event or explicit reload starts a new generation against
the then-current live table and may redefine the macro normally. Consequently,
a successful macro replacement followed by an ordinary-form failure leaves the
new macro alongside the last successfully published ordinary definitions; the
reload still reports the later error.

This deletes `TurnCheckWorld`, `TurnDelta`, `PreparedMacroTurn`, candidate
invocation, reserved unpublished slots, and cross-module rollback. It changes
no public crate interface, cache schema, platform contract, backend contract,
or trait-implementation behavior.

#### 1.1.3 Post-publication outcomes are stack-owned receipts

A successful publication returns one int-private, move-only
`PublicationReceipt` containing its already-committed
`RedefinitionOutcome`s. It contains no staging table, `CheckState`, generated
program, code owner, GOT reservation, or resume position. `ProcessedCluster`
does not own or copy these outcomes.

`process_cluster_once` is an outer `ProcessAttempt` wrapper around a fallible
core. The wrapper owns the receipt while the core receives a mutable sink. A
successful macro or ordinary publication moves its outcomes into that sink;
Rust `?` may leave the core, but the wrapper still returns both the terminal
`Result` and the receipt. Thus a later error cannot discard a successful
checkpoint's §18 work.

```text
process attempt
  core publishes -> append committed outcomes to route receipt
  core then returns Done, Gap, or Err
  wrapper returns { terminal result, receipt }
  cadence consumes receipt once before handling the terminal result
```

The route owner settles the receipt as follows:

- REPL eval applies §18 after `Done`, before waiting on `Gap`, and before
  returning a later `Err`;
- dependent recheck retains one receipt across source retries and settles it
  before interpreting either terminal success or failure; and
- a pool worker consumes the receipt on its own stack on `Done`, `Gap`, and
  `Err`. Pool work uses a complete `Replace` generation: success has recompiled
  the module and watcher/T1 orchestration already owns dependent reload;
  failure is handled by the existing module error block. Its decision does not
  depend on the individual outcome rows; and
- the retained `New`-only batch compatibility route consumes an empty receipt
  and treats an effectful one as an internal contract failure.

No receipt is stored in `SharedState`, `ModuleState`, the scheduler, a parking
map, or a source continuation. In particular, a scheduler receipt mailbox is
rejected: it would duplicate an already-settled fact, add reset/drain ordering,
and buy no observable behavior. Retry continues to store only the uncommitted
source/emitted suffix and the generation-started bit.

### 1.2 Recovery scenario matrix

The implementation-strategy unit matrix is:

| Prior live state | Failed turn | Required post-failure state |
|---|---|---|
| no same-named entry | new def fails codegen | name absent; independent literal succeeds |
| compiled same-named entry | ABI-preserving redefinition fails | prior entry, slot, code, and display remain |
| compiled same-named entry | ABI-changing redefinition fails | prior entry remains current; no dependent transaction runs |
| several ordinary generated entries | one generated unit fails | none of the ordinary HM cluster publishes; earlier macro checkpoints remain |
| no generated code | type/build failure | existing typecheck discard behaviour is unchanged |
| near-full live GOT | plan needs too many fresh slots | preparation fails; `next_got_slot` and all cells are unchanged |
| compiled batch | second name fails before finalise | first name has not patched its prior live slot |
| successful ABI-preserving redefinition | backend returns success | GOT patch, entry replacement, `Code` owner, metadata, and outcome all publish as one terminal transition |
| successful ABI-changing redefinition | backend returns success | fresh slot publishes; old slot and code owner remain frozen before prior entry drops |
| cadence interference (unit seam) | live slot cursor differs before codegen | preparation is discarded before any GOT write |
| expansion emits macro, macro compilation fails | no parent, active clause, owner, GOT pointer, or introspection from that macro publishes |
| expansion emits macro, later form invokes it, later typecheck/codegen fails | the committed parent, all active clauses, owners, and introspection remain; the later ordinary cluster does not publish |
| macro replacement succeeds, later reload form fails | the new macro generation remains current; the prior macro is not restored |
| gap after a committed macro | retry begins from the retained uncommitted continuation; the macro is neither rebuilt nor diagnosed as a duplicate |
| 3-clause macro successfully becomes 1 clause | exact old indices `1..3` are absent-key `ChangeAbi` retirements; both old slots remain frozen and tombstoned; no surplus binding remains |
| 3→1 macro later becomes 3 clauses | active index 0 preserves its current slot; indices 1 and 2 receive fresh slots distinct from both retired slots |
| macro shrink plan/publication refuses | prior parent, all prior clauses, pointers, owners, tombstones, candidates, and source continuation remain unchanged; no partial retirement occurs |

Unit strategy splits by seam:

- **prepare:** classification matrix (`New`, ABI-preserving, ABI-changing,
  slot-less displacement), deterministic final slots, closure rejection, exact
  enrollment, capacity exhaustion, and no mutation of live/check/product
  snapshots;
- **ownership:** a changed slot cursor fails the pre-codegen revalidation; a
  held module-cadence token admits no second same-module prepare/publish;
- **compile:** a two-name batch whose second member fails proves zero GOT
  writes and zero `Code`/introspection installation; success returns owned
- **publish:** success moves exactly the planned entries, advances the cursor
  once, retains old owners before replacement, installs products, and returns
  the prepared outcomes; no branch returns `Err`;
- **macro checkpoint:** direct and expansion-emitted macros remain invisible
  until every clause has checked and compiled, then parent, active clauses,
  owners, metadata and introspection publish through one module gate;
- **checkpoint continuation:** a later invocation sees the committed macro; an
  injected later failure retains it, and a gap retry resumes the uncommitted
  source/emitted suffix without rebuilding or duplicate-registering it;
- **clause-set replacement:** 3→1 derives only exact prior indices `1..3`,
  publishes their absent-key `ChangeAbi` decisions with the parent and active
  clause, retains displaced owners before guard release, and leaves their old
  slots frozen and tombstoned; the following 1→3 mints fresh slots for indices
  1 and 2; an injected late refusal leaves the complete prior generation and
  tombstone set byte-identical;
- **cache bijection:** restore accepts exactly one private same-group
  `MacroClause` row per active parent index and no surplus owned row; both
  missing and surplus directions regenerate;
- **cadence parity:** eval and worker drivers both call the same
  prepare/compile/publish helpers and notify only after publish.

The sprint QA plan owns the e2e recovery and subsequent-literal guards.

## 2. Macro-expanded declaration staging (0816)

Macro output is not a special ordinary-declaration registration class. Int
flattens structural `begin` once at the expansion site and preserves emitted
order. Expansion-produced `defmacro` forms cross the checkpoint in §1.1.2 at
their emitted position; all remaining declarations accumulate into one
`ParsedEntry` sequence for the ordinary `check_forms` Passes 2/3.

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

### 2.1 Macro checkpoint: exact clause identity and one-module publication

Int prepares one macro from its parsed `DefmacroInfo`; it never discovers a
macro or its clauses by scanning live names. For every clause index it derives
the exact synthesized FQ identity from the parent macro identity and index.
Before `check_forms`, the private target staging table declares that exact key
as `Private` with `CallableOrigin::MacroClause { group }` and the canonical
one-argument macro ABI scheme:

```text
(Fn [(macros/SList macros/Sexp)] macros/Sexp)
```

This prebirth is the authority for clause identity. A matching existing live
`MacroClause` may be replaced across turns; a `Plain` callable or clause owned
by another macro at that exact key is a collision. A name prefix is never
evidence of clause origin. Typecheck may preserve `MacroClause` only from this
exact staging-local prebirth; it must not inherit the origin from the live
table during an ordinary user definition or redefinition.

After the single macro-unit check returns, int validates every active clause:
exact FQ and parent group, private visibility, the synthesized one-parameter
shape, canonical ABI scheme, and concrete body state. It also validates that
the staging table contains no trait-implementation mutation. This is a
defn-only path; existing `TraitImpl` registration, conformance, publication,
and cache behavior do not change.

The macro unit then uses the ordinary one-module prepared path:

```text
parent + every active clause in owner-free staging
  -> derive one module slot/redefinition plan
  -> compile all active clauses in one backend batch
  -> retain every returned owner and drop-glue pair
  -> publish_compiled_staged under the module writer guard
```

All lookups, capacity checks, lifecycle validation, owner-key validation, and
introspection construction occur before backend entry. Backend failure leaves
the live table untouched. Compiled-publication refusal returns every owner;
int restores all touched canonical GOT cells while those owners remain alive,
then releases them. On success every active clause has an owner at the same
publication that exposes its parent metadata. `PreparedCommit` is the only
prepared publication carrier; it may carry several exact per-symbol owners
from the one macro batch but does not acquire a cross-module form.

The macro reader and replacement writer use the same module-table guard. A
reader snapshots parent clause metadata and, for the selected clause, its
validated `MacroClause` origin, ABI, GOT pointer, and cloned `Code` owner while
holding one read guard. It releases the guard before invoking JIT code; the
owner clone keeps the pointer alive. A replacement holds the write guard from
before backend finalization first touches a reusable canonical GOT slot through
the table publication. Thus a reader sees the complete old generation or the
complete new generation, never old metadata with a new pointer.

Macro parents and generated clauses are not language values. Typecheck's
language-value candidate projection and unique-scheme extraction exclude
`CallableOrigin::MacroClause`; the backend's private checked carrier rejects an
ordinary value/call reference to one before emission. The macro executor still
uses the exact internal binding directly. `Binding::is_callable_target` and
module codegen enumeration remain broad enough to compile that internal
binding.

Cache restoration validates each active parent-metadata index against the
exact expected clause key, `MacroClause` origin and group, private visibility,
canonical ABI and concrete body state. It also validates the converse: every
persisted `MacroClause` row owned by that parent is named by exactly one active
parent-metadata index. Parent metadata and its active clause rows therefore
form a bijection; an orphan, duplicate, missing, surplus, wrong-group, or
formerly-`Plain` clause makes the cache stale and triggers regeneration rather
than repair or retagging. Runtime owners and GOT pointers remain non-persisted
and follow the ordinary cache load path.

Dependency work is not part of this staging table. A missing dependency or
generated realization produces the ordinary `ResolutionGap`; the dependency
module publishes independently and the macro retries. Only when the complete
expansion-time closure is live and codegenable does the target macro batch
compile and publish. This is the exact provenance boundary without an owned
clone of every module.

<details>
<summary>Superseded S117 owned-world design (retained as decision history)</summary>

The following S117 design is not an implementation instruction. S121 rejected
the temporary cross-module check world and rollback mechanism in favor of the
checkpoint above.

### Retired: on-demand macro clauses through an owned check world

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

</details>

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

### 2.3 Macro-checkpoint test strategy

The strategy-bearing seams live with focused unit scenarios:

- **checkpoint isolation:** parent and all active clauses remain absent until
  the one macro batch has checked, compiled and published; any failure retains
  the complete prior macro generation;
- **dependency independence:** a required dependency realization publishes
  through its own module; later macro failure does not remove it, and unrelated
  concurrent realizations never enter the target macro staging table;
- **source-order visibility:** an earlier form cannot call a later macro, a
  later form can call a committed macro, and ordinary forms on both sides
  still typecheck as one HM binding cluster;
- **retry continuation:** gaps before/during a macro retry that macro, while a
  gap after it resumes the uncommitted suffix with the checkpoint present and
  without a duplicate-definition path; include an expansion-produced macro;
- **receipt settlement:** direct and expansion-produced redefinitions followed
  by `Done`, `Gap` then success, `Gap` then dependency failure, and a later
  internal error each apply every already-committed outcome exactly once;
  dependent recheck covers success and failure, while initial-load and
  watcher/reload workers acknowledge receipts on every terminal path without
  scheduler or session receipt state; the `New`-only batch route proves its
  receipt inert;
- **multi-clause atomicity:** a failure in any clause exposes neither parent nor
  siblings; success exposes the parent metadata and every active owner in one
  module publication;
- **origin authority:** fresh birth and replacement preserve exact
  `MacroClause` group identity; a same-spelling `Plain` callable collides, and
  bare, self-qualified and child-qualified user references to a real clause
  are rejected before backend emission;
- **reader generation:** concurrent replacement snapshots either all-old or
  all-new metadata/pointer/owner under one guard, and the cloned owner survives
  invocation after the guard is released;
- **owner-before-pointer:** executable publication installs JIT/drop-glue and
  displaced-code owners before any pointer/entry replacement;
- **state split:** a `MacroClauseDescriptor` cannot enter invocation;
  `ExecutableMacroClause` construction rejects null/missing-owner/wrong-ABI
  inputs, and invocation retains the owner for the complete unsafe call
  window.

The production path must cover fresh, cache-restored, redefinition and reload
faces. A later failing form must leave an earlier successful macro callable in
all modes; a failed replacement must leave the old macro callable. Cache rows
with `Plain` generated clauses must regenerate. These are ordinary production
guards and require no allocator, fault injection, or cross-module rollback
instrument.

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

## 6. Multi-definition REPL presentation (0800)

`def` is not recognised by the parser or compiler as a core form. Int must not
branch on the literal spelling `def`, on `-def`, or on the stdlib module
(Principles 10 and 19).

### 6.1 Binding identity remains visible

The REPL does not reinterpret a zero-argument macro as the type of the form it
would emit. A `defmacro` binding remains a `defmacro` in its definition echo,
bare-symbol introspection, `/info`, and `/sig`. Its expansion result is visible
only when the macro is invoked. This follows `spec/09-macros.md` §§9.5, 9.10.2,
9.13 and `repl/spec/11-macro-introspection.md` §11.2.

Consequently there is no `PreparedPresentation`, `presentation_scheme`, dry
typecheck of a nullary macro, selected presentation subject, or parallel
presentation store. The REPL reads each published binding's ordinary
`ModuleEntry` classification.

The result carrier is instead an ordered publication receipt:

```rust
EvalResult::Definitions {
    symbols: Vec<FQSymbol>,
    warnings: Vec<Warning>,
}
```

`TurnDefinitions` is int-private and stack-owned by one eval. It records each
definition's canonical `FQSymbol`, emitted position, and whether that
definition crossed its publication boundary. It is never stored in
`SharedState`, the scheduler, a symbol table, or introspection. Compiler-only
generated realizations are absent because rows arise from typed `TopLevel`
definitions and parsed `defmacro` checkpoints, not a table scan.

### 6.2 Collection is total and structural

Every definition emitted by the entered statement and successfully published
is listed, in emitted order. Visibility does not select a subject: a private
definition entered or emitted at the REPL is still a definition produced by
that statement. An arbitrary expression or structural form contributes no
definition row. A mixed definition-plus-expression statement retains its
ordinary value-result behavior; this section changes definition-only results.

Ordinary definitions enter the receipt as pending and become displayable only
after the complete HM/codegen publication succeeds. A `defmacro` enters as
published at its immediate checkpoint. On a dependency retry, exact canonical
identities already present in the stack receipt are reused, so neither an
earlier pending definition nor a durable macro checkpoint is duplicated or
reordered. A later error returns the error rather than a successful definition
result, while the macro checkpoint remains live under §1.1.2.

### 6.3 Source sequence

1. The source-order walk records each typed ordinary definition as pending and
   each successfully published macro checkpoint as published. Expansion
   products are consumed from their actual flattened order.
2. A gap returns only the established source continuation. The eval-owned
   receipt remains on its caller's stack; the retry merges repeated pending
   identities without rescanning live tables.
3. Successful ordinary codegen/publication marks the exact typed definition
   identities published. Structural forms leave the receipt unchanged.
4. A definition-only turn constructs one `EvalResult::Definitions` from every
   published row. `format_eval_result` renders each symbol through the existing
   single-symbol `ModuleEntry` formatter, separated by newlines. Warnings are
   attached once to the batch.
5. Persistence and failed-form repair consume the same complete symbol list;
   they do not infer a primary definition.

For the current stdlib expansion:

```clojure
(def n 42)
```

the definition result is:

```text
:(Fn [] primitives/Int) user/n-def ; defn
:user/n ; defmacro
; [] -> Sexp
```

`/info n` and `/sig n` continue to describe `user/n` as `defmacro`. Entering
bare `n` invokes the zero-argument macro, expands to `(n-def)`, and evaluates
to `:primitives/Int 42`. No binding changes classification between those
surfaces.

### 6.4 Production-test contract

`/dev` must add private unit tests for the carrier/publish seams and
`/testing` must retain production REPL tests for user-visible behavior:

- one and several direct definitions render in source order;
- an expansion emitting both an ordinary definition and `defmacro` lists both
  in emitted order, with their ordinary classifications;
- private emitted definitions are included without becoming public;
- arbitrary-expression and structural-only output take the ordinary path;
- an expansion-emitted macro is visible to the next form in the same cluster
  at the established availability point, while an earlier form cannot see it;
- before its checkpoint, an emitted macro parent, clauses and introspection
  exist only in that macro's owner-free staging; after it, a later-form
  invocation reads the live generation without compile-again publication;
- dependency retry neither duplicates nor reorders receipt rows;
- a failed ordinary cluster exposes no successful definition result, while an
  earlier successful macro checkpoint remains live;
- `/info` and `/sig` keep a zero-argument macro classified as `defmacro`, while
  entering its bare name exercises expansion and displays the evaluated type;
- Run/Link controls compile the same expansion without allocating a REPL
  receipt or consulting introspection for result selection.

### 6.5 S121 checkpoint reconciliation

The S118 plan to move `TurnCheckWorld` ahead of Pass 1 and absorb
`PreparedMacroTurn` into the ordinary cluster is retired. Result presentation
does not participate in macro publication: the macro checkpoint publishes its
ordinary binding and introspection, then records the canonical identity on the
eval-owned receipt. A later failure does not erase the checkpoint. Ordinary
emitted definitions remain pending until the ordinary HM cluster publishes.

No drop-glue row moves between prepared carriers: the macro checkpoint and the
ordinary cluster each publish their own `{artifact, owner}` pairs through the
same ordinary publication machinery. No candidate-world seed classification
survives. A cache-restored macro whose active clauses lack runtime owners is
recompiled as one macro checkpoint before use.

## 7. Quality attributes and interface assessment

- **Simplicity / maintainability:** one ordinary `PreparedCommit` shape serves
  both a macro checkpoint and the later HM cluster. The cloned multi-module
  world, semantic-delta scanner, candidate invocation and reserved-slot stack
  delete; there is no trait-specific macro path or reverse index.
- **Observability:** ordinary located compiler errors remain; only their owner
  identity is corrected. No new trace, allocator/RC diagnostic, fault
  injection, or cyber-sensitive instrumentation is introduced.
- **Concurrency:** source continuations may be requeued, but no partially
  checked or compiled world is parked. Macro readers and replacement writers
  share one module guard; publication remains at the existing module gate.
- **Performance:** only explicit `/info` performs complete impl enumeration.
  Codegen batch derivation is bounded to the entered turn.
- **Testability:** macro-checkpoint commit/discard, retry continuation,
  provenance selection, reader generation, complete-record replacement, and
  impl-pair collection are int-private seams with the matrices above;
  production REPL tests pin fresh/cache/redefinition/reload parity.
- **Public API:** the S121 implementation consumes the already approved and
  baseline-confirmed `publish_compiled_staged` types operation and the approved
  absent-key meaning of its existing `ChangeAbi` decision. `src/` gains only
  private types/helpers; `cranelisp-exe-bundle` is untouched; no further types,
  frontend, typecheck or backend public change is required. BC §6
  explicitly narrows the accidental `Introspection` exposure; no new public
  DTO or cache-schema field is introduced.

## Next skills

- `/dev` — narrow to Binary/int for §1.1.2 and §2.1: source continuations,
  one-module macro preparation/publication, exact `MacroClause` birth and
  language-value exclusion, then deletion of the retired temporary machinery.
- `/testing` — retain
  `build_confidence::mode_equiv_macro_user_defined` as the production
  mode×cache defect guard; no new e2e mechanism is required.
- `/review` — verify source-order checkpoint semantics, macro-local atomicity,
  ordinary HM-cluster atomicity, exact retry behavior, one-guard reader
  generation, and zero interface/cache-schema drift.
- `/sprint` — sequence the checkpoint implementation before the remaining C6
  reader migration and retain the independent public-API gate already closed.
