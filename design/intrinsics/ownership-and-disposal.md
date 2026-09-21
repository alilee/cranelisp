# Runtime heap ownership and disposal

Owner: `/design` (intrinsics). The interior design for how this crate holds,
mints and releases counted references to runtime heap values, and how it tears
the two tag-directed node families down.

Consumes without restating: [intrinsics bounded context](../arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics), invariants 2
(intrinsics owns the runtime heap layout) and 3 (the atomic-RC discipline and
its per-site ordering table); `design/runtime/s119-typed-consume-funnel.md` (the
cross-pair typed-handle contract); `design/runtime/s118-structural-embedding-ownership.md`
(the consume-owner contract the producer seams are written against);
`spec/12-runtime.md` §12.3 (reachability and teardown); `spec/appendix-c-nfr.md`
§C.4.1 (the RC-ordering floor); `design/arch/total-concreteness.md` §3.4 (the
approved `Effect` surface) and `design/platform/platform.md` §4.2 (the
repeatable-thunk interior this crate discharges).

Out of scope here: reactor scheduling and executor lifetime
([`reactor.md`](reactor.md)), the emitted counterpart
(`design/backend/io-trampoline.md`), the primitives producer seams
(`design/primitives/`), the diagnostic and fault-plant surface
([`diagnostic-modes.md`](diagnostic-modes.md)).

---

## 1. Invariants

1. Every live counted reference in this crate's Rust bodies is an `Owned`, a
   `Borrowed` read view, or a raw word at a seam the trusted-base enumeration
   names (§2).
2. RC increment has exactly one extern-Rust entry point (§3).
3. One teardown walk per node family. The tag decodes once into a closed enum;
   the walk over that enum is exhaustive with no catch-all; a field is read only
   under the arm whose tag declares it, and only after the zero-observing
   decrement (§4).
4. An IO node is deallocated in exactly one place (§6).
5. The trampoline never inspects a reference count to choose an ownership story
   (§7).
6. Forcing a published `Pure` or `Effect` node leaves it in the ownership
   state it had before: a `Pure` force *mints* the consumer's reference rather
   than moving the node's own (§6.1), and an `Effect` force *borrows* the thunk
   rather than consuming it (§6.2). Their words are written only while the node
   is fresh and unpublished. `Launch` and `EffectPoll` are outside this
   invariant: `Launch` writes its field-0 sentinel after publication, and both
   are separate intake (`total-concreteness.md` §3.4).

## 2. The typed handle vocabulary

`crates/cranelisp-intrinsics/src/handle.rs` publishes two types with closed
operation sets, which are not widened here:

- `Owned::{from_abi, into_raw, as_borrowed, raw_for_read, is_nullary_tag}` —
  transparent, `#[must_use]`, neither `Copy` nor `Clone`, with a debug-only,
  unwind-safe drop bomb. Discharge it by consuming it, by storing it into a
  structure whose glue will discharge it, or by returning it across an ABI shim.
  The move checker enforces *not twice*; the drop bomb reports *not never*.
- `Borrowed<'a>::{from_abi, to_owned, raw_for_read}` — the copyable read view,
  with no discharge operation.

Nine consuming entries take `Owned`: `rc::consume_shallow`;
`drop::{consume_slist, consume_sexp, consume_vec_with, consume_vec_of_string,
consume_io_tree, consume_closure, dec_shallow_io}`; `trace::consume_trace_call`.
`consume_vec_with` additionally takes a `fn(Owned)` element callback; its only
producers are `rc::consume_shallow` (Vec-of-String) and `drop::consume_io_tree`
(`Select`'s Vec-of-IO carrier), and no callback alias is published.

`free_io_node` stays raw. It sits *beneath* the handle abstraction with
`atomic_dec_rc`: its precondition is a count already at zero, while `Owned`
models a live counted reference.

`ResultDisposer` remains a compiler-provided raw `extern "C" fn(i64)` drop-glue
address, distinct from the Rust element callback. JIT closure calls, poll
functions and backend/platform emitted signatures likewise stay raw; the typed
vocabulary stops at this crate's Rust bodies.

**The trusted base is enumerated executably, not in prose.**
`crates/cranelisp-intrinsics/src/handle/tests.rs::typed_handle_trusted_base_matches_the_approved_intrinsics_allow_list`
holds the exact function-and-count allow-list for `Owned::from_abi`,
`Borrowed::from_abi`, the parent-borrow projection, `.to_owned()` and
`mem::forget` (the latter being exactly `Owned::into_raw` and
`OwnedCWaker::wake`). A new mint, projection or `mem::forget` is a `/review`
rejection unless the approved enumeration moves with it in the same change-set.
Adapt only at an existing source-stated ownership handoff; do not reshape the
trampoline, trace representation or callback ABIs to create one.

**The honest grade.** This is a lexical structural guard: it makes the unsafe
assertions enumerable and detects a moved adoption, but it does not prove the
provenance of the permitted raw words or semantic correctness inside an allowed
function.

The primitives half of the pair — its produced-owner adapter, its
parent-lifetime child borrow and its owner-into-raw-storage exits — is designed
in `design/primitives/` against the same cross-pair contract and is not
redefined here.

## 3. `rc_inc` — the blessed inc entry point

`rc::rc_inc(ptr: i64)` is the single extern-Rust RC-increment, the inc-half
mirror of `rc::consume_shallow`'s dec: the same `NULLARY_TAG_THRESHOLD` skip for
bare tags, the same RC field derived from `HeapHeader::RC_OFFSET`, an atomic
`fetch_add(1, Release)`, and `rc_trace("inc", ptr, new_count)`. Release is the
NFR §C.4.1 floor and is no weaker than the backend's inline SeqCst `atomic_rmw`
inc, so a value incremented on both paths sees one consistent discipline. Its
env-gated seam validation runs as a *precheck*, per
[`diagnostic-modes.md`](diagnostic-modes.md) §7.5.

`Borrowed::to_owned` is the single typed mint and delegates here; `io.rs` and
`trace.rs` retain direct raw calls (§9).

One deliberate, owned divergence: `ivar.rs`'s spark inc keeps SeqCst, because
the IVar cell's RC and state transitions share one uniform total order
(Decision 13). The canonical per-site ordering policy is
[intrinsics bounded context](../arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics), invariant 3; this document does not
re-rule it.

## 4. The structural discharge mechanism

Three collaborating pieces per family:

- **A closed tag enum with one fallible decode.** One `i64 → Tag` site per
  family. `Unknown(i64)` is a *named* variant handled by exactly one arm, not a
  fall-through. In an ordinary build it discharges no guessed fields and still
  deallocates the outer node; under the existing `CRANELISP_RC_DEC_CHECK` gate it
  raises the crate's located seam message and hard-fails before deallocation.
  There is deliberately no unconditional debug assertion: teardown may follow an
  already-supervised language error, and a second panic across an `extern "C"`
  boundary would abort an otherwise recoverable process.
- **A per-tag declared field list** — data, not control flow: for each tag, the
  fields it owns as `(offset, kind)`, where the kind names the discharge the
  field needs (shallow, `SList`, `Sexp`, closure, IO sub-tree, an IO branch
  block or vector, or scalar). `Par`'s variadic branch block and `Select`'s
  carrier `Vec` are two declared kinds, not two hand-rolled loops.
- **One dispatcher** that reads a declared field and performs its discharge. It
  owns the sole raw-to-`Owned` transfer on the teardown path (`drop.rs`'s
  `owned_field`); `consume_vec_with`'s element loop is the only other mint in
  the module, and recursive fields, SList tails, inline `Par` branches and the
  `Select` carrier all flow through those two sites.

**Grade.** Exhaustiveness *over the declared enum* is structural — a missing arm
does not compile. Completeness *of the enum against the published tag constants*
is measured, because Rust cannot make a `match` on `i64` exhaustive: a new
constructor added in `cranelisp-types` without a matching variant would decode
as `Unknown`. The falsifier is the per-family decode-coverage row beside the
constants' own cardinality pins.

**What this must not become.** Not a cross-crate table — the tag *constants* are
`cranelisp-types`' (`Sexp`) and `cranelisp-platform`'s (`IO`), while the
discharge shape is this crate's. Not a header type-word. Not a generic visitor:
two families, two tables, one dispatcher shape; a third family is the trigger to
generalise, not a reason to pre-generalise.

## 5. The `Sexp` family

`consume_sexp` is: nullary guard, decrement, fence, one exhaustive walk,
deallocate. There is no pre-decrement field snapshot, because the premise that
justified one — that every heap-allocated `Sexp` constructor is unary — is false
for `SexpAnnotated`.

| Tag | Constructor | Declared owned fields |
|---|---|---|
| 0/1/2 | `SexpInt` / `SexpFloat` / `SexpBool` | none — field 0 is a scalar |
| 3/4 | `SexpStr` / `SexpSym` | field 0: `HeapString`, shallow |
| 5/6 | `SexpList` / `SexpBracket` | field 0: `SList<Sexp>` |
| 7 | `SexpAnnotated` | field 0 (`stype`) **and** field 1 (`sform`), both `Sexp` |
| — | `Unknown(n)` | none; located, gated report (§4) |

Field 1 is readable only under the tag-7 arm: every other heap `Sexp` node is a
one-field, 32-byte allocation, so reading offset 32 on one is out of bounds.
Either `Annotated` half may itself be a bare nullary `Sexp` tag.

## 6. The IO family

`free_io_node(p)` is the single teardown tail: its precondition is that the
caller has decremented this node's count to zero and fenced; it discharges every
field the tag declares and deallocates. It is the only place an IO node's fields
are released and the only place an IO node is deallocated. Its callers are
`drop::consume_io_tree` (`Structural`), `drop::dec_shallow_io`
(`SpineTransferred`), and the backend-emitted `drop<IO T>` through the
`runtime/free_io_node` catalog row, which is fixed to `Structural`. The
disposition is an in-crate parameter and never crosses the ABI.

The disposition makes the caller's ownership story a value rather than a rustdoc
assertion. It differs in exactly one row — `Bind`'s, whose two fields are the
only fields a caller ever transfers out of a node before releasing it. Every
other row, `Pure` and `Effect` included, is a plain declared field list under
§4's mechanism:

| Tag | Owned fields | `Structural` | `SpineTransferred` |
|---|---|---|---|
| `Pure` (0) | payload@24, witness@32 | discharge an `Owned(glue)` witness | **identical** — the payload is never transferred |
| `Effect` (1) | thunk@24, token@32 | discharge the thunk through the platform (§6.2); the token is scalar | **identical** — the thunk is never transferred |
| `Bind` (2) | inner@24, cont@32 | discharge both | **none** — both transferred to `current` / `cont_stack` |
| `Par` (3) | count@24, branches@32.. | branch block | branch block |
| `EffectPoll` (4) | state closure@24 | closure | closure |
| `Launch` (5) | sub-tree@24 (`0` = detached) | sub-tree if non-zero | sub-tree if non-zero |
| `Select` (6) | carrier `Vec`@24 | branch vector | branch vector |

### 6.1 The `Pure` payload witness — retain on force

> **Status (2026-09-21).** Implemented in the working tree and reviewed with
> no blocking finding. QA accepted the correction evidence: IOR-2 balances,
> and the `Reserved` arm has executing evidence and a detection proof (§8).
> Integration remains pending. The rule replaces an atomic *claim* whose second force
> refused a reused IO value, against the reuse rule under "Task Tree
> Construction" in `spec/10-io.md`.

The ABI-10 `Pure` node carries a witness word at field 1 describing what field 0
owes: `Scalar` (`0`) — a scalar or value-flattened payload owing nothing — or
`Owned(glue)`, the canonical `drop<T>` address for the payload's concrete type,
the same glue every other release site calls. No IO-specific releaser symbol is
minted. `1` is reserved and emitted by nothing. It decodes to a *named*
`Reserved` variant so the word can never become a call target or an increment
target:

- **Teardown** is the single reporting point, on the §4 `Unknown` precedent:
  discharge nothing, located report under the existing gate.
- **Force** treats it as `Scalar`: it hands field 0 on with no RC operation and
  no report. A report here would duplicate teardown's for the same node and
  add a branch to the hot path. This is safe only while `1` stays unemitted: a
  `Reserved` word stamped over an owning payload would give each force an
  unminted reference, and a second force would under-count. The teardown
  report is therefore the detector for that fault, not decoration.

*Grade:* no emitter is asserted, with the falsifier "any construction or
adoption stamp that writes `1`". The teardown report is a gated instrument whose
detection is proven by the reserved-word mutation cells (§8).

**No writer after publication.** Both words are written only by the
construction emitters and the backend's platform-return adoption stamp, while
the node is fresh and unpublished. Nothing in this crate writes either word
afterwards, so both are ordinary field reads under the `Pure` arm, published to
every later reader by the same edge that already publishes field 0. There is no
post-publication modification order to linearise and no claim to arbitrate.

- **Run lane — force mints, it does not move.** The trampoline reads field 0 and
  the witness. For `Owned(glue)` it takes its own counted reference to the
  payload through the blessed inc entry point (§3) and hands *that* reference to
  the consumer; the node keeps its own. For `Scalar` it hands the word on with
  no RC operation. Either way the consumer receives exactly what it received
  before — one reference it discharges through the edge disposer — so every
  downstream path (continuation call, terminal result, `ProducedValue`'s armed
  drop, `Select`-loser disposal) is unchanged. Forcing the same node again is an
  ordinary repeat of the same reads and the same mint.
- **Teardown, both dispositions.** The payload is a declared field in §4's table
  with a glue-witnessed discharge kind: read the witness, call `glue(payload)`
  for `Owned(glue)`, do nothing for `Scalar` or `Reserved`. Because the node
  never transfers the payload, the `Structural` and `SpineTransferred` cells are
  the same operation, and the teardown tail needs no `Pure` special case — the
  field returns to the declared-list mechanism invariant 3 states for every
  other field.

**Why removing the guard alone is not the correction.** Under the claim rule the
node *hands over* its single reference; delete the arbitration and two forces
each hand over the same one reference and teardown discharges a third time. The
mint is what makes the second force legitimate. Following Principle 20, the
node's representation has no claim state for a referee to arbitrate. The grades
below record that no rule stops a future writer from adding one.

**Ownership proof for the mint.** The forcing lane holds a live reference to the
node across the whole force: frame-owned for a fresh node, the caller's tree for
a non-fresh one, and the branch's caller-owned root for a `Par`/`Select` branch
under its structured join. A live `Pure` node holds one counted reference to an
`Owned(glue)` payload, so the payload's count is at least one when the inc runs
— the mint is on a live object, and it needs no ordering beyond the node
publication that already makes reading field 0 sound. **Named failure of the
precondition:** the pre-existing *severed join* residual (`total-concreteness.md`
§3.4; [`reactor.md`](reactor.md) §2.21), where a cancelled `Select` loser with
an in-flight rayon bridge detaches a worker that can read a node the root has
already torn down, then read and increment freed memory. This design neither
creates nor cures it; it stays `qa` intake.

**The mint is the exact inverse of the discharge.** Read at source, 2026-09-21.
`DropGlueRegistry::request_if_owning` declines exactly `NeverHeap` and `Value`,
so an `Owned(glue)` payload is `String`, a closure, a `Vec`, a nested IO node,
or an `AlwaysHeap`/`Mixed` ADT. All five emitted glue shapes share one skeleton:
an optional nullary-tag skip, one atomic decrement at `HeapHeader::RC_OFFSET`,
and *every* structural act — element decs, capture decs, field decs, the IO
teardown tail, `dealloc` — strictly inside the `old_rc == 1` branch. `rc_inc`'s
threshold skip has the same polarity as the glue's, and the glue emits its skip
exactly for the `Mixed` types whose payload can be a bare tag. So one `rc_inc`
adds one reference at `+8` and one `drop<T>` removes one, for every payload
category that can carry a witness. This is not a new balance premise: it is the
same inc/dec pairing every `let`-bound heap value already uses, and adopting it
here *removes* a distinct ownership story rather than adding one.

Two categories that might look like exceptions are not. An **IVar** cell can
never be a `Pure` payload — `ConcreteType` has no IVar variant, so classification
never sees one and no glue is ever minted for one — which is why §3's deliberate
SeqCst divergence does not reach this path. A **`Value`-flattened** ADT is
classified `NeverHeap`-equivalent, stamps `Scalar`, and is handed on untouched.

**Grades.**

| Property | Grade |
|---|---|
| A force mints the consumer's reference and the node keeps its own | *Measured*: the retain cells of §8 were observed failing on a force without the mint |
| Teardown discharges the payload once under both dispositions | *Measured*: §8 |
| No write to a published node's words | *Asserted, with a named falsifier.* It is an as-built fact: the claim writer was deleted and `review` confirmed its absence at source once. Nothing enforces it against re-introduction, so it is **not** structural. Falsifier: any new write to a published `Pure` node's field 1 |
| One `rc_inc` inverts one `drop<T>` | *Asserted, with a named falsifier*: a `GlueShape` whose emitted body discharges owned substructure or deallocates outside its `old_rc == 1` branch. That observation belongs to the backend's own glue evidence; this crate depends on the property no more than every inline release site already does |

**Cost, derived rather than measured.** Counting atomic read-modify-writes over
a node's life, this rule is never worse than the claim rule and is strictly
cheaper for two of the three cases, so no corpus benchmark is warranted:

| Case | Claim rule | This rule |
|---|---|---|
| heap payload, forced once | swap at force, swap at teardown, consumer dec — **3** | inc at force, glue dec at teardown, consumer dec — **3** |
| scalar payload | swap at force, swap at teardown — **2** | two plain loads — **0** |
| unforced node (`Select` loser, unrun `Bind` sub-tree) | swap at teardown, glue dec — **2** | glue dec — **1** |

Reuse adds one inc and one dec per extra force, which is new capability rather
than a regression on an existing path. The trigger that would justify measuring
is a `Pure`-dense corpus regression attributable to this seam; none is predicted
by the table. The trampoline must not recover the old move by testing the node's
count — invariant 5.

**Nothing observes a claim.** The claim state, its refusal and the detectors
that observed it — including the former A6 seam check — are gone, because the
condition each observed has no representation: no payload transfer for a
shallow release to catch, no duplicate claim to record. `dec_shallow_io`'s
safety precondition covers only *transferred* fields; a `Pure` payload is never
transferred and is discharged by the same declared field as the structural
walk.

### 6.2 The `Effect` thunk — borrowed on force, discharged at teardown

> **Status (2026-09-21).** Implemented and independently reviewed against the
> approved ABI-11 surface (`total-concreteness.md` §3.4). Module lifetime tests
> and public Effect reuse pass; QA accepted the evidence. The user confirmed
> the generated baseline on 2026-09-21. Integration remains pending.

The platform owns the thunk's representation, its per-force wrapper and its
destructor containment (`design/platform/platform.md` §4.2). This crate decides
when the thunk is called and when it is discharged. It never names the stored
type.

**The node owns the thunk; the node's count is the thunk's count.** The
thunk word is a declared field of the `Effect` row with its own discharge kind,
under both dispositions (§6 table). Teardown reads the word under the `Effect`
arm, after the zero-observing decrement and fence, and calls
`drop_effect_thunk` on it exactly once before the node is deallocated
(invariants 3 and 4). The word is never transferred, so `Structural` and
`SpineTransferred` perform the same operation. The token word is scalar and
owes nothing. `Unknown(_)` stays field-less.

A null thunk word is not a state: every constructor writes a live pointer, and
the design adds no null skip for one. The `Launch` row's `0` is a documented
sentinel. `Effect` has none.

**Lifetime during a force.** A forcing lane calls the thunk only while it holds
a counted reference to the node, as it does for `Pure` (§6.1): frame-owned for a
fresh node, the caller's tree for a non-fresh one, and the branch's caller-owned
root under the structured join for a `Par` or `Select` branch, including a
blocking branch on a rayon worker. So a force never overlaps discharge. The
node's count cannot reach zero while any lane can still call. Concurrent forces
of one node from two branches each hold their own reference. The platform's
`Send + Sync` bound, not a lock here, makes the shared call sound.

Each lane's last use of the node comes before its decrement, and the teardown
fence acquires every such decrement. Teardown also runs only after the bridge
join has ordered a worker's exit ([`reactor.md`](reactor.md) §2.21). Together
these order every force's effect on the captures before the capture destructors
run, on whichever thread releases the node. The named failure is the same
severed-join residual as §6.1: a detached worker could call a thunk that root
teardown has already discharged. This design neither creates nor cures it; it
stays `qa` intake.

**The guard handoff.** `io_guard`'s protected force keeps its call and its
signal guard unchanged. Its safety precondition changes from "a thunk not yet
forced" to "a live thunk, borrowed for this call, whose node the caller holds".
The trampoline's force comment changes the same way. After a recovered trap or
a caught panic, the thunk is intact and still owned by the node. Only teardown
discharges it.

**Failure behaviour.**

- A capture destructor that panics is contained DLL-side by the platform. Teardown
  sees an ordinary return and deallocates the node.
- A hardware trap inside a capture destructor is **consciously unprotected**.
  Teardown runs outside the signal guard, and guarding every `Effect` teardown
  would put a `sigsetjmp` on a release path to protect captures that are today
  only `i64`s and `CLOwned` host references. *Trigger:* a platform capture that
  owns a foreign resource whose destructor can trap.
- On the abort path of §7 the unreleased fresh node leaks its thunk and its
  captures with it. The direction stays leak-only. The repair belongs to that
  path, not here.

**Grade.** The one-discharge rule is structural where §4's mechanism is: one
declared field, one dispatcher, one teardown tail. That no force overlaps
discharge is *asserted*, inheriting §6.1's lane-lifetime argument and its named
failure. The module evidence is listed in §8.

## 7. Trampoline ownership transitions

`current_is_fresh` means the trampoline owns one continuation-produced
reference. It does **not** mean the node has only one reference.

**Fresh `Bind` descent.** Before descending through a fresh `Bind`, the
trampoline establishes its own references to the inner IO node and to the
continuation while its parent reference is still live, then releases that parent
with structural `consume_io_tree`. The inner owner becomes `frame.current`; the
continuation owner enters `frame.cont_stack`; the disposer word stays scalar
metadata. Acquiring both field references before the structural parent release
is the single rule for RC=1 and RC>1 — with RC=1 the teardown releases the
parent's two field references while the newly acquired ones carry the traversal;
with RC>1 the retained parent keeps its field references and the traversal later
releases only what it acquired. Anything that reads the count to pick between
two stories is a normal-completion breach of `spec/12-runtime.md` §12.3.1.

`io.rs::read_bind_transition` applies this once for both the synchronous and the
asynchronous dispatcher. It materialises the frame-owned parent as `Owned` and
uses one private parent-borrow projection — the sole `Borrowed::from_abi`
assertion in the crate — narrowed to the live parent and immediately discharged
through `Borrowed::to_owned`. The `SpineTransferred` release remains correct for
fresh nodes whose fields have already transferred under their own rules, but it
is not the fresh-`Bind` descent operation.

**Non-fresh caller-tree `Bind`** retains the borrowed descent: no child
increment, no parent release; the caller's final structural walk remains the
owner.

**Cancellation needs no second rule.** After fresh-`Bind` descent the frame owns
the current node and every fresh continuation independently, so `TrampolineFrame`'s
drop guard can discharge them if the future is cancelled, and normal completion
discharges the same owners through `feed_continuation`.

**A forced node needs no second rule either**, which is the trampoline-side
consequence of §6.1 and §6.2. A node the loop has already forced is in the same ownership
state as one it has not: the frame's reference still carries every obligation
the node holds. So the three release seams reached after a force — the shallow
release in `feed_continuation`, the drop guard's structural release of a
cancelled frame's fresh current, and the caller's terminal tree walk — each stay
one plain release of one reference, and a value already handed to a consumer is
balanced by that consumer's own disposer. The pairing is symmetric on the
cancelled path too: the frame's release discharges the node's reference while
`ProducedValue`'s armed drop discharges the minted one.

**One path is not balanced, and this design does not cure it.** When an arm
raises a runtime error or a dispatch fault, the loop disarms the frame *and*
returns without releasing the fresh `current` node or the un-popped fresh
continuations, so they leak. That is a pre-existing defect of the abort path,
independent of the `Pure` rule and reachable through any node kind. Its only
interaction with §6.1 is magnitude: a forced `Pure` leaked there now leaks one
payload reference with its node, where under the claim rule the payload had
already moved to the consumer. The direction stays monotone-safe — a leak, never
a second owner or a use-after-free — and the repair (release the frame's owners
before the abort return, rather than disarming) is `qa` intake, not part of this
correction.

**Result-handoff disposal authority.** A tree does not own a value already
returned by an entered foreign call, so the disposal authority rides the
handoff edges rather than platform `Effect` nodes: `Bind` carries the disposer
for the value its inner `IO a` hands to the continuation; `Par` carries one
disposer beside each branch pointer, and its result buffer owns every
initialized slot until the buffer is transferred; `Select` carries the common
branch-result disposer, used only for cancelled losers; `Launch` carries the
detached sub-tree's result disposer, because the supervisor discards that
result. `ProducedValue` represents only the two valid states — armed ownership
after production, and explicit transfer — and invokes the carried disposer
exactly once if dropped while armed. `TrampolineOutcome` keeps `Completed(value)`
distinct from `Stopped`, so cancellation and fault sentinels cannot acquire
disposal authority. The disposer words are non-owning function addresses, so the
teardown walk skips them while still reclaiming each node's authored heap
fields.

## 8. Evidence

Module-tier evidence and its detection limits:

- the handle drop-bomb triplet in `handle/tests.rs` — a deliberate leak fires
  with the located prefix, the same fixture consumed through `consume_shallow`
  is silent and balanced, and an unrelated unwind stays survivable;
- the trusted-base allow-list guard (§2), armed by a same-count move of an
  approved adoption into an unauthorized helper;
- the `Sexp` decode-coverage, declared-field, `Annotated`, nullary-half,
  scalar-tag and unknown-tag rows in `drop/tests.rs`, with the balance walk in
  `drop/rc_balance.rs`;
- the `Pure` witness and `free_io_node` disposal rows in `drop/tests.rs`,
  covering the scalar and `Owned(glue)` teardown arms and the shared-reference
  release (`dec_shallow_io_preserves_shared_reference`);
- the `Pure` retain-on-force cells in `io/tests.rs`: a forced node keeps its
  payload and its shallow release discharges it; unforced and forced nodes
  balance under structural release; a shared node forced twice yields its
  payload each time and balances; the scalar twin makes no RC operation; and
  glue over a bare nullary tag touches no count. The first two were observed
  failing on a force without the mint. They live beside the force seam rather
  than in `drop/rc_balance.rs`, because each pair spans the module-private
  force and the teardown, and reuses the same allocation ledger;
- the `Reserved` teardown cell in `drop/tests.rs` and the `reserved-pure`
  leg of the gated unknown-tag harness: the unowned payload remains live, only
  the node is freed, and the located report fires when armed. Removing the
  reserved decode arm made both checks fail; the arm was restored;
- the four `Effect` lifetime cells in `io/tests.rs`: unforced structural
  release, two forces followed by final release, shallow final release, and
  release of one of two references. Capture-destructor counters observe exactly
  one final discharge; all four failed on the old field-less teardown row;
- `Effect` fixtures in `io/tests.rs` and `reactor/tests.rs` construct through
  `CLIO::effect*` using the shared `test_effect_node` helper and the host
  allocation callback. Fault fixtures use panicking closures. Nodes are freed
  through the teardown tail, without restating the private thunk type;
- the deterministic `Select`-loser release test in `io/tests.rs`, which holds a
  worker at a test-only post-send barrier, drops the loser future without
  re-polling the ready receiver, and proves the queued nonzero-disposer payload
  was released once with its exact value, against a winner control; and
- the unique-parent and shared-parent fresh-`Bind` pair in `io/tests.rs`, which
  must return `73`, free the unique parent and its fields, observe the retained
  parent and both fields live before final release, and balance.

Module attribution and public acceptance are distinct, and both belong to
[`qa`'s plan](../../tests/plan/s122-evidence-delta.md). That plan records the
typed-funnel runtime checkpoint closed on 2026-09-11 with its stated limits.
For IO reuse:

- IOR-1 (a reused `Pure` yields its value on each force) is green.
- IOR-2 now passes with zero marginal residual after the backend scope-result
  retain correction; its mechanism was observed in pre-fix CLIF.
- Effect reuse passes. The corrected unforced-capture safety fence keeps a
  host owner so the final free is visible to host counters; it passes restored
  and fails with teardown deliberately omitted. The old counter reading did
  not discriminate release from leak.
- The abort-path leak (§7) and the severed-join residual (§6.1) remain `qa`
  intake.

## 9. Potential extensions, with triggers

- **A callback-scoped borrow.** `Borrowed::from_abi` is `'static`-branded and so
  unbranded in practice; only the `as_borrowed`-derived form carries the escape
  check. The extension, on the `with_vec_strings` precedent, is triggered by a
  real storing hazard appearing — none has.
- **Deriving the hand-written extern shims.** The crate's extern shims carry
  their ownership facts as rustdoc rather than deriving them; the natural
  derivation home is `intrinsics_table()`
  ([`intrinsics-table.md`](intrinsics-table.md)). Trigger: a second hand-mirror
  defect between a shim and its declared facts.
- **Narrowing `rc_inc` to `pub(crate)`.** Possible once `io.rs` and `trace.rs`
  stop calling it raw; it is a published item, so it moves through `arch` and the
  baseline gate.

## 10. Cross-references

- `design/arch/bounded-contexts.md` §4b — the bounded context, the heap-layout
  and RC invariants, and the per-site ordering table.
- `design/runtime/s119-typed-consume-funnel.md`,
  `design/runtime/s118-structural-embedding-ownership.md` — the cross-pair
  contracts this interior implements.
- `design/backend/io-trampoline.md` — the emitted counterpart: the reified IO
  data and the RC/drop discipline this crate interprets.
- [`reactor.md`](reactor.md) — executor lifetime, cancellation and the bridge
  join that orders a worker's last use of a branch node before teardown.
- `design/platform/platform.md` §4.2 — the `Effect` thunk's representation,
  wrapper and destructor containment.
- [`diagnostic-modes.md`](diagnostic-modes.md) — the RC/alloc seam checks, their
  precheck ordering and the fault-plant protocol.
