# Sprint 121 — the C7 platform visit

**Status:** DESIGN, Sprint 121 Phase 3. `design` narrow-deployed to
`cranelisp-platform` and the platform fixtures. Design-only: no product source,
test source, fixture, spec, architecture, QA plan or filing is edited by this
pass.

**Stream:** C7, the last compiler-side stream (`sprints/SPRINT.md` §"Coherent
work inside each stream"). Its exit condition is *"public platform surface and
consumer fixture green"*, and its instruction is *"reconcile the platform design
and facade once, then implement marker/schema/shared-heap evidence against
settled C5/C6 contracts. If 0934 changes the IO-node layout, bump `ABI_VERSION`
and rebuild fixtures in this visit."*

**Filings verified and disposed here:** 0463, 0870, 0871, 0873, 0874 (C7's
primary allocations), plus the C5→C7 ABI handoff from 0934 and the C6→C7
facade-documentation consequence of 0933.

---

## Document map

`design/platform/` after this pass carries **four live records and one archive**:

| Document | Role |
|---|---|
| `platform.md` | The master design: what the crate is, its invariants, its ABI and node layouts, its state. Rewritten by this pass (0871). |
| `platform-dlls.md` | DLL authoring and loading mechanics — the manifest, the wrappers, the capture-RC protocol, the search path, the reference platforms. |
| `poll-leaf-authoring.md` | The v9 ctx-vtable poll-leaf contract and the `poll_support` scaffolds — the right-sized successor to the 1,414-line `poll-support.md` (0871). |
| `adt-marker-binding.md` | The marker-binding mechanism decision (0873), `arch`-approved. |
| `s121-c7-platform-visit.md` | This document: the one S121 C7 stream design. |
| `archive/` | `poll-support-s96.md`, `sprint71-redesign.md`, `host-wiring-s76.md`, `implementation-slice-s66.md`, `platform-registry-removal.md`. |

This document is the *visit* record — what C7 does this sprint and why. It
retires when the sprint closes; the durable content it settles lands in
`platform.md`.

---

## 1. What this visit settles

**One sentence.** The platform edge takes the settled runtime and lifecycle
contracts once: the `Pure` node's payload-glue word bumps `ABI_VERSION` 9→10 and
every fixture rebuilds against it in the same change-set, the DLL's sentinel and
the backend's tag-dispatched adoption stamp meet at the independently pinned
absolute byte 32, the marker-binding mechanism `arch` approved at S118 is
implemented on that same
rebuild, the crate's rustdoc stops describing three retired architectures, and
the shared-heap integration fixture converges — with the generic
platform-extension seam left demonstrably untouched so the deferred network
lesson costs the interface nothing.

**Five bundles**, ordered in §10:

| Bundle | Content | Filings |
|---|---|---|
| **P0** | The ABI 9→10 window: `Pure` widen, the new payload-glue constant, the platform compile-time offset pin, the four text-level version pins, the `Pure`-returning fixture the C4 B5 adoption stamp is measured on, refusal and compatibility evidence, every fixture rebuild | 0934 handoff; the `total-concreteness.md` §3.4 platform-return ruling |
| **P1** | Marker binding: `schema_declares_type`, the `adts:` arm, five call-site migrations, the `resolve_field` type-key diagnostic | 0873 |
| **P2** | The facade wash: crate-root, `concurrency.rs`, `poll_support.rs`, `declare.rs`, `HostCallbacks` and `CLIO` rustdoc to one current contract; the manifest-sig concreteness fact; crate `CLAUDE.md` current state | 0870, 0933 consequence |
| **P3** | The shared heap-ADT integration fixture | 0874 |
| **P4** | Design canon and extension-seam record | 0871, 0463 |

P4 is delivered by **this pass** (it is design work). P0–P3 are one `dev`
change-set in the C7 wave; they are separated as bundles because their evidence
differs, not because they land separately — §10 states why one change-set is
required rather than convenient.

---

## 2. Consumed contracts, and the three source facts that bind this design

### 2.1 Consumed, not restated, not reopened

| Contract | Owner and record |
|---|---|
| `Pure` = `[header \| tag@16 \| payload@24 \| payload_glue@32]`; every other IO node byte-identical; after publication the word is the one three-state atomic witness (`0 = Scalar`, `1 = Claimed`, otherwise `Owned(glue)`), and force and teardown both claim through it before payload access or discharge | `arch` — `total-concreteness.md` §3.4; `interfaces.md` §"IO Tag Constants"; `safety-invariants.md` §4 row R20 |
| `ABI_VERSION` 9→10 and the fixture rebuilds are C7's, once; no new versioning mechanism is invented | `arch` — `total-concreteness.md` §3.4 "ABI + fixtures (C7)"; `sprint` — `SPRINT.md` §"Coherent work"/0934 row |
| **The platform-return stamp is tag-dispatched at the backend's one platform-call chokepoint** — `IO_TAG_EFFECT` ⇒ fn-name @40, `IO_TAG_PURE` ⇒ canonical `drop<T>` or `0` @32 (ABI ≥ 10), any other tag ⇒ no write. Allocated to **C4 bundle B5** in its existing backend visit; the C7 platform-local footprint-absorber fallback is **REJECTED**; the C4 design visit is not re-opened | `arch` — `total-concreteness.md` §3.4 "the platform-return seam"; `interfaces.md` §"IO Tag Constants"; `safety-invariants.md` §4 row **R19** |
| **The authority split at the crossing**: the DLL initialises only the `0` sentinel while the node is fresh and unpublished; C4's backend adoption stamp writes `0` or the canonical glue while it remains exclusive and unpublished; after publication C5 alone owns state access, and both force and teardown atomically exchange the word to `Claimed` | `arch` — `total-concreteness.md` §3.4; `interfaces.md` §"IO Tag Constants"; `safety-invariants.md` §4 row R20 |
| C7 stays the **only** ABI 9→10 owner, and supplies the independent compile-time assertion `HEAP_HEADER_SIZE + IO_PURE_GLUE_OFFSET == 32` plus the `Pure`-returning fixture and acceptance leg the adoption stamp is measured on | `arch` — `total-concreteness.md` §3.4 "Offset detector packaging" / "Evidence (C4 tier)" |
| `CACHE_SCHEMA_VERSION` 24→25 is C1's single window; C7 creates no second cache version and captures no acceptance cache baseline between C1's bump and C4's layout flip | `arch` — `symbol-table-lifecycle.md` §9 |
| `free_io_node` is C5's to land (it does not exist at HEAD), and C5's I0b is *gated on* this bump — a landing order, not a code dependency | C5 §14, handoff H6 |
| A platform effect is born `Life::Concrete { slot: manifest-order mint, realization: Dll }`; `src/platform.rs:351`'s cursor write deletes; slot *i* = descriptor *i* becomes a mint-order invariant surfaced by the load-boundary uniqueness scan | `arch` — `symbol-table-lifecycle.md` §4.4/§5.6; C6 §8.1 |
| A manifest sig with a residual `Type::Var` is refused with a located diagnosed load error at `parse_and_check_platform_type_sig`; the structural refusal is C1's settlement funnel and the located frame is C6's. **C7 adds no second predicate.** | C6 §8.2; `arch` — `total-concreteness.md` §3.5 |
| `HostCallbacks` is permanently two fields; the boundary is poll-in / wake-out; there is no closure-callback capability and Decision 0031's forward commitment is retired | `arch` — `bounded-contexts.md` §5 "Host callbacks" (S98 user ruling) |
| Typed handles do not wrap `free_io_node`; public platform crossings keep the established `CLOwned` / borrowed contracts unchanged | C5 §4.1, §14 |
| The narrowed network lesson is deferred and **must not change the platform interface** | user, 2026-09-01 (`SPRINT.md` Phase-2 decision table, 0463 row) |
| `adts:` + `schema_declares_type` is the approved marker mechanism, with three named conditions on the implementing change-set | `arch` gate, 2026-07-25 (recorded on FIXME 0873) |

### 2.2 Three source facts that bind this design and are in no prior record

Each was established against live source in this pass. Each changes what the
visit must do.

**Fact 1 — the crate memory states the rule that would skip this bump, and the
rule is false for the node this bump changes.**
`crates/cranelisp-platform/CLAUDE.md` (§"Effect-node layout is append-only")
says: *"Node layout is an **in-process** backend↔intrinsics convention —
widening it is NOT an `ABI_VERSION` bump (host + DLLs rebuild together)."* That
is true for `IO_TAG_EFFECT_POLL`/`LAUNCH`/`SELECT`, which no DLL constructs
(the same memory says so two sections later). It is **false for `Pure` and
`Effect`**, which `CLIO::pure` and `CLIO::effect*` construct inside the DLL. A
`dev` reading that sentence would conclude no bump is owed. The sentence is
corrected in P2, and the correction is load-bearing, not cosmetic.

**Fact 2 — the `ABI_VERSION` number is pinned as literal text at four sites, three
of them outside this stream's surface.**
`crates/cranelisp-platform/tests/baseline.rs:68` greps `src/lib.rs` for the exact
string `"pub const ABI_VERSION: u32 = 9;"`;
`crates/cranelisp-platform/tests/macro_expansion.rs:90` asserts the literal `9`
rather than the const; `tests/concurrency_poll_edge_guards.rs:66,134` repeat the
source-text grep; `tests/facade_pif_rows.rs:759` still names `ABI_VERSION = 8` in
its frozen-table comment. The first two are C7's; **the last two are project-root
`tests/`, owned by `test`.** The bump therefore has a mandatory cross-stream
edit, named as a handoff in §16 rather than discovered when the suite goes red.

**Fact 3 — the backend's platform fn-name stamp was guarded on the call target's
kind, not on the returned node's tag, and wrote eight bytes past the end of a
`Pure` node at both v9 and v10. CONFIRMED at source by `arch` and RULED; the
cure is allocated to C4 B5.**
`compiler/apply.rs:1546-1549` stamps whenever `is_platform_effect` holds;
`:1636-1641` stores at `EFFECT_FN_NAME_ABS_OFFSET` (`:39-40` =
`HeapHeader::SIZE + IO_EFFECT_FN_NAME_OFFSET` = 40 from the node base).
`CLIO::pure` (`lib.rs:908-920`) calls `alloc(16)`, so a `Pure` node is 32 bytes
today and 40 bytes after this bump; an 8-byte store at base+40 is out of bounds
in both. It has never fired because **no shipped platform fn returns a `Pure`
node** — all nine in-tree fixtures return `CLIO::effect*` — but `CLIO::pure` is
published author surface, with a family of `From` conveniences routing into it
(`lib.rs:1066-1105`).

`arch` ruled the disposition on 2026-09-01 (`total-concreteness.md` §3.4, "the
platform-return seam"): the stamp dispatches on the **returned node's tag** at
the one existing chokepoint, in C4's bundle B5 and its existing backend visit.
The fact stays recorded here because it is what this stream's evidence and
window discipline are built on — §4 now designs C7's half of that ruling (the
sentinel, the platform offset pin, the fixture and the acceptance leg), not an
escalation.

---

## 3. Bundle P0 — the ABI 9→10 window

### 3.1 What changes, exactly

One node grows one word.

| Node | v9 (payload bytes) | v10 (payload bytes) | Delta |
|---|---:|---:|---|
| `Pure` (0) | 16 — `[tag, payload]` | **24** — `[tag, payload, payload_glue]` | one word appended |
| `Effect` (1) | 40 | 40 | none |
| `Bind` (2), `Par` (3), `EffectPoll` (4), `Launch` (5), `Select` (6) | — | — | none |

One new public constant, in the established family (payload-relative, like
`IO_EFFECT_RESOURCE_OFFSET`/`_FN_NAME_OFFSET`/`_CAPACITY_OFFSET`):

```
IO_PURE_GLUE_OFFSET: i64 = 16     // payload+16 == node base+32
```

The name says `PURE` because the word is `Pure`-only. It is deliberately *not*
called an "IO header" or "IO node" offset: naming it generally would invite the
uniform-header shape `arch` explicitly rejected (R15 stands).

`CLIO::pure` allocates three words instead of two and writes the sentinel `0` at
the new offset. §4 is why `0` and not something else.

**The platform offset pin (§4.4).** This crate composes the word's absolute
location as `HEAP_HEADER_SIZE + IO_PURE_GLUE_OFFSET` and asserts at compile time
that it equals 32. C4 independently pins the backend composition in its own
vocabulary. Each owner therefore detects drift while compiling its own crate,
without a cross-crate assertion or a second visit.

### 3.2 Why this is an `ABI_VERSION` bump

Against the bump rules in `ABI_VERSION`'s own rustdoc (`lib.rs:190-201`), rule
(ii) — *"any change to `HEAP_HEADER_SIZE`, `STRING_HEADER_BYTES`, `IO_TAG_*`,
`IO_EFFECT_RESOURCE_OFFSET`: BUMP"* — is the governing clause, but it enumerates
constants rather than stating the property. The property is:

> A node layout is ABI-governed **iff a DLL constructs or reads that node.**

`Pure` qualifies: `CLIO::pure` is in the DLL. The failure a mismatch produces is
not a leak. A v9-built DLL returns a 32-byte `Pure`; a v10 host's teardown walker
reads `[base+32]` — past the allocation — and, if the word is non-zero, **calls
it as a function pointer**. That is arbitrary control transfer from adjacent heap
bytes, and it is exactly what the version gate exists to make impossible. The
refusal is therefore the safety property of this bundle, not paperwork.

Rule (ii)'s enumeration is repaired in P2 to state the property and cite
`IO_PURE_GLUE_OFFSET` alongside the existing constants, so the next node change
does not have to re-derive this.

### 3.3 Refusal evidence

`platforms/shapes-badabi` is the standing load-refusal fixture: it hand-rolls its
manifest (no macro) precisely so it can bake a stale version, and
`tests/platform_errors.rs::platform_abi_version_mismatch_e2e` drives it.

At HEAD it bakes `STALE_ABI_VERSION = 2` (`shapes-badabi/src/lib.rs:57`) — a
version seven generations old. That proves the comparison is `!=`; it does not
prove the deployment case anyone will actually hit, which is **the immediately
preceding version**. This visit repoints it to `9` and states the rule in its
rustdoc:

> `STALE_ABI_VERSION` is always `ABI_VERSION - 1` at the time of the last bump.
> It is a literal, not a computed expression, because computing it from the const
> would make the fixture track the host and stop being a mismatch.

Re-pointing it is therefore a **standing obligation of every future bump**, and
saying so in the fixture is what makes it survive. Its two contradictory
rustdoc claims (`:50` says the host is 8, `:96` says 6) are corrected in the same
edit.

**Detection proof.** The refusal fixture is an instrument, so it is proven to
detect in this change-set, both legs: with `STALE_ABI_VERSION = 9` the e2e
refuses with `PlatformError::AbiVersionMismatch`; with it temporarily set to
`ABI_VERSION` the same e2e loads. The negative leg is the one that has to be
demonstrated, because a refusal that fires for the wrong reason (a missing
export, a parse failure) is indistinguishable from a working gate until someone
reads the stderr.

### 3.4 Compatibility evidence

Every in-tree platform rebuilds in this change-set; there are no out-of-tree
DLLs, which is the same latitude the v8 and v9 cutovers used. The nine fixtures
and what each proves after the rebuild:

| Fixture | Shape | Post-bump obligation |
|---|---|---|
| `platforms/stdio` | blocking `print` + poll `read-line` (`role: Consume`, manifest-static serial token) | rebuild; its e2e lane green |
| `platforms/test-capture` | 7 blocking effects across all three scheduling classes | rebuild; the capture lanes green; **gains the two `Pure`-returning fns** (§4.5) — the only fixture whose source the widen itself changes |
| `platforms/shapes` | ADT marshaling, one marker, embedded schema | rebuild; **marker migrates to `adts:`** (P1); stale "ABI v3" header line corrected |
| `platforms/shapes-badabi` | hand-rolled stale manifest | `STALE_ABI_VERSION` → 9; rustdoc corrected; refusal e2e green |
| `platforms/boom` | faulting thunk, no schema | rebuild; dispatch-fault e2e green |
| `platforms/async-demo` | one poll leaf, `role: None` | rebuild; reactor lane green |
| `platforms/pool-demo` | 3 blocking `ResourceSerial` with `(token, capacity)` | rebuild; capacity lane green |
| `platforms/poll-pool` | 8 poll leaves incl. `Produce`/`Consume` roles, self-`acquire` | rebuild; fan-out/capacity/reactor lanes green |
| `exemplar/platforms/web` | 4 markers, 1 blocking + 3 poll leaves, embedded schema | rebuild; **4 markers migrate to `adts:`** (P1); the retired v8 leading-pair paragraph at `:34-36` deleted |

No fixture constructs a `Pure` node **at HEAD**, so the widen changes no existing
fixture body — the rebuild is what makes them v10. The one deliberate addition is
§4.5's `Pure`-returning pair in `test-capture`, which exists precisely because
the seam had no traffic and therefore no evidence; it lands **after** the widen
inside the same change-set (§10), never before it. Otherwise the fixture work in
this bundle is the version pins, the refusal fixture and the two stale headers.

### 3.5 What this bundle must not do

- It does not touch `CACHE_SCHEMA_VERSION`. C1 owns the one window.
- It does not add a second gate, a "v9 compatibility mode", or a per-node version
  byte. One number, one refusal.
- It does not re-time itself relative to C5. C5's I0b is gated on this bump
  landing; the gate is a landing order that `sprint` sequences, and C7 does not
  land the bump before C4's construction sites stamp, or the tree spends a wave
  with a widened node nothing writes.

---

## 4. The platform-constructed `Pure` node — the sentinel, the adoption stamp, and C7's half

The disposition of this seam is **ruled** (`total-concreteness.md` §3.4, "the
platform-return seam", 2026-09-01). What was C7's open escalation is now a
consumed contract with C7 holding three obligations: the sentinel, the offset
pin, and the fixture the stamp is measured on. This section states them and
records what the ruling closed.

### 4.1 What `CLIO::pure` writes: the sentinel `0`, necessarily

The glue word is *the canonical `drop<T>` address for the payload's concrete
cranelisp type*. Those addresses are JIT-emitted (or link-resolved) per concrete
type in the host process. A platform DLL is compiled independently, cannot name
one, and **has no channel to fetch one**: `HostCallbacks` carries exactly `alloc`
and `alloc_with_tag` and will not widen (`bounded-contexts.md` §5, S98 ruling).
Adding a third callback to serve this would reopen a settled architecture
decision to serve a convenience.

So `CLIO::pure` writes `0`, and that is forced, not chosen. Before adoption this
is only an unpublished sentinel, not the final `Scalar` classification. It is
also the DLL's **only legal write to this word**: C4's backend adoption stamp
replaces it with `0` or the canonical glue while the node remains exclusive and
unpublished; after publication C5 alone may touch the word, with force and
teardown both atomically exchanging it to `Claimed`. A DLL-side write of
anything else — a fabricated address, the reserved claim state `1`, a class tag,
or a value obtained through a widened `HostCallbacks` — is a second ownership
mechanism, and is a `review` reject (§15).

### 4.2 What the sentinel costs after the ruling: nothing that survives the crossing

The sentinel would under-claim if it were published as the final state: for a
`CLString` or `CLAdt<T>` payload, interpreting `0` as `Scalar` would erase the
node's heap obligation. Before the adoption ruling that was a live residual at
the platform edge, graded *asserted with a named falsifier*.

The ruling closes it **at the seam the node must cross**. Every DLL-minted `Pure`
node reaches the host as the return value of a platform call, and the backend's
B5 arm overwrites the sentinel there with the canonical `drop<T>` for the payload
type it knows concretely from the entry's `(Fn […] (IO T))` scheme — or leaves
`0` when the payload is non-heap. The DLL's `0` is therefore not a claim about
ownership at all; it is an **initial value the ABI crossing replaces**, exactly as
the `Effect` node's null `fn_name` already is.

That closure is complete only if no DLL-minted `Pure` can reach the host by any
other route, and the facade makes that structural:

- `CLIO::pure` takes `val: CL where CL: CLType`, and **`CLIO<T>` does not
  implement `CLType`** (the trait's implementors are `CLInt`/`CLBool`/`CLFloat`/
  `CLString` and `CLAdt<T>` — `crates/cranelisp-platform/src/lib.rs:816-834`,
  `adt.rs:142`). A nested `pure(pure(…))` is unconstructable, so no `Pure` node
  can be hidden inside another node's payload.
- An effect thunk returns `CL: CLType` too, so a `Pure` node cannot be produced
  by forcing an `Effect` either.
- The `From` conveniences that lift a natural value into `CLIO`
  (`lib.rs:1066-1105`) all route into `CLIO::pure`, so they are covered by the
  same argument rather than being a second mint.

**Grade after the ruling: structural for the reachability half** (no DLL-minted
`Pure` escapes the return seam — the falsifier is a `CLType` implementation added
for `CLIO<T>`, which is also a public-API delta), **measured for the discharge
half** (§4.5's acceptance leg, which executes the stamped node on both paths).
The old F4 leak cell inverts accordingly: it was "exactly one leaked string, and
nothing worse"; it is now "zero leaked, zero double-freed" (§14 F4).

One honest boundary: the closure is over nodes **this facade** can mint. A DLL
that bypasses `CLIO::pure` and hand-rolls a node through `alloc` is outside every
guarantee in this crate, as it already was for every other layout invariant.

### 4.3 The adoption stamp — what C4 B5 does, and what C7 must not do

The ruled lowering, quoted for the reader who arrives here first
(`total-concreteness.md` §3.4 is authoritative):

```
node = <GOT-indirect platform call>          # non-poll; the poll arm returns earlier
tag  = load.i64 [node + 16]
tag == IO_TAG_EFFECT ⇒ store fn_name_ptr → [node + 40]   # value-identical to today
tag == IO_TAG_PURE   ⇒ store drop<T> | 0  → [node + 32]  # in-bounds at ABI ≥ 10 only
otherwise            ⇒ no write
```

It lands in **C4 bundle B5, in its existing backend visit** — the seam is inside
C4's reserved surface, the ruling leaves no interior design freedom, and the C4
design visit is not re-opened. C7 therefore:

- **adds no stamp, no guard and no second predicate of its own.** The crate's
  contribution to the correctness of that store is the layout, the constant, the
  pin and the version gate — nothing executable;
- **does not re-time C4.** The Pure arm's store is in-bounds only against the
  two-field node, so the C4→C7 window carries the ruling's named residual: zero
  traffic, because no in-tree platform fn returns `Pure` and C7 adds none before
  P0 (§10, §15 reject 14);
- **keeps the ABI act singular.** The 9→10 bump and its refusal remain C7's and
  only C7's; B5 consumes the layout, it does not version it.

### 4.4 The platform offset pin — one vocabulary, one absolute byte

The architectural crossing datum is the absolute byte offset **32**. C7 owns
this crate's composition of that datum and lands, beside the public constant:

```rust
const _: () = assert!(HEAP_HEADER_SIZE + IO_PURE_GLUE_OFFSET == 32);
```

The assertion is compile-time, adds no dependency, and pins
`cranelisp_types::HeapHeader::SIZE` on the way through because
`HEAP_HEADER_SIZE` derives from it. Any drift in the platform composition fails
constant evaluation while compiling `cranelisp-platform`.

C4 independently owns and pins the backend composition of absolute offset 32.
C7 writes and reserves no backend source. The fixture pair in §4.5 exercises
correct use of the pinned crossing without redefining either crate's offset
authority.

### 4.5 The `Pure`-returning fixture and the acceptance leg — C7's evidence obligation

The seam has never had traffic, which is exactly why it has never had evidence.
C7 supplies both, and it is deliberately the smallest fixture that discriminates:

**`platforms/test-capture` gains two functions**, appended (so no existing
manifest index moves):

| Fn | Signature | Body | Discriminates |
|---|---|---|---|
| `pure-int` | `(Fn [] (primitives/IO primitives/Int))` | `CLIO::pure(CLInt)` | the non-heap leg — the stamp writes `0`; teardown claims `Scalar` and discharges nothing |
| `pure-string` | `(Fn [] (primitives/IO primitives/String))` | `CLIO::pure(CLString)` | the heap leg — the stamp writes the canonical `drop<String>`, and the payload is discharged exactly once |

`test-capture` is chosen because it is the general-purpose behavioural fixture:
its lanes already assert forced values, and it carries no schema or marker
coupling that a `Pure` return would drag into the evidence. The pair is
**appended after** the widen inside the same change-set (§10 order), never before
it.

The acceptance leg (`qa`'s to place — H3) runs in the C4/B5 crossing subwave
after C5 I0b; it needs C4's stamp, C7's rebuild and C5's claim/teardown together:

| Leg | Program shape | Expected |
|---|---|---|
| **unrun heap** | call `pure-string`, bind the `IO` value, never force it | zero un-discharged strings — the F4 inversion. Anything else means the stamp did not land or is not read as an obligation |
| **forced heap (the control)** | force the same node on the run lane | exactly one successful claim hands one live string to the program; teardown observes `Claimed`, performs no payload discharge, and nothing is double-freed |
| **non-heap** | call `pure-int`, unrun | nothing discharged, no write through a zero word |

**Why no `CLAdt<T>` leg.** `CLAdt<T>` is the other `CLHeap` payload category, and
its stamp is the same `DropGlueRegistry` request for a different `T`; the seam
does not inspect payload shape, so there is no observation the ADT leg makes that
the `String` leg does not. Recorded as an extension with a trigger: **a reported
or observed defect in which the payload category, not the heap/non-heap split,
changes the stamped value.**

### 4.6 The platform-local fallback — REJECTED

The alternative this design carried before the ruling was to have `CLIO::pure`
allocate the `Effect` node's five-word footprint so that base+40 landed inside
the allocation on a reserved absorber word, making the out-of-bounds store
impossible without leaving this crate.

`arch` **rejected it** (`total-concreteness.md` §3.4): it removes the symptom and
preserves the mechanism — a fixed-offset store into a node whose shape varies by
tag, with the store's correctness resting on an allocation size chosen elsewhere
to absorb it. It also does nothing for the under-claiming residual, since an
absorber word is not a glue address. It is recorded here so a later reader finds
the option already disposed of rather than re-deriving it, and re-proposing it is
a `review` reject (§15 reject 15).

---

## 5. Bundle P1 — marker binding (0873)

The mechanism decision is **complete and `arch`-approved**; this visit
implements it. `adt-marker-binding.md` carries the comparison, the selection and
the rejected options, and this pass flips its status from PROVISIONAL to
APPROVED and transcribes the gate's three conditions. Nothing about the selection
is reopened here.

What the implementation owes, beyond the design's own §5:

1. **`schema_declares_type(artifact, type_key) -> bool`**, a `pub const fn` in
   `declare.rs` beside `extract_layout_hash`, paren-depth-tracking, `;;`-comment
   skipping, bare-FQ-keys only. It is a pure total function over `&str` and is
   unit-testable to its boundaries directly (Principle 5), in the idiom
   `extract_layout_hash`'s scanner tests already use.
2. **The `adts:` key on `declare_platform!` arm 1 only** — supplying `adts:`
   without `schema:` is a macro match failure, so a platform that embeds no
   schema structurally cannot declare markers. Per entry the fragment preserves
   author rustdoc (`$(#[$attr:meta])*`); the four web markers carry load-bearing
   documentation that a silently-discarding mechanism would not survive.
3. **Five call-site migrations**: `platforms/shapes` ×1,
   `exemplar/platforms/web` ×4. `shapes-badabi`'s marker and the crate's own test
   fixtures keep hand-written `impl CLAdtType` — correctly, since neither embeds
   an artifact — and `CLAdtType` stays a public, hand-implementable trait with an
   unchanged contract, so no out-of-tree DLL breaks.
4. **The `resolve_field` type-key diagnostic** (`adt.rs:334-372`): probe
   `lookup_type(type_key)` before reporting a field miss, so an absent type key
   reports as an absent *type* rather than as `constructors:[]` blaming the field
   name. Crate-internal, no gate; it rides here because it is the message an
   author debugging exactly this class would read.
5. **`arch` gate condition 1 — the grammar coupling is named at both sites.**
   `schema_declares_type` is a second reader of the artifact text beside the
   runtime parser. Its rustdoc and `schema.rs`'s grammar home each cite the
   other, so an artifact-grammar change is a named two-site change rather than
   silent drift. This is a condition on the change-set, not a nicety.

**Detection proof (gate condition, and the audit's stated bar).** The const
assertion is an instrument. The change-set demonstrates both legs: a deliberately
misspelled `adts:` key fails the build with the intended message naming the
marker and the key; the correct spelling builds. The audit was explicit that
"merely adding another positive test does not cure the mismatch risk" — the
negative leg is the deliverable, relocated from runtime (where on the poll path
it is an unattributable process abort) to build time, where it is deterministic.

**Why P1 rides P0.** The five migrated call sites are in fixtures that P0
rebuilds anyway, and the macro arm they migrate into is in the same file whose
ABI rustdoc P2 corrects. Splitting them costs two visits to the same three files
for no evidence gain.

---

## 6. Bundle P2 — the facade wash (0870), and the manifest-sig fact (0933)

### 6.1 Verified stale sites

Every evidence row in the audit's R1 was re-verified against live source in this
pass. All hold:

| Site | Says | Source says |
|---|---|---|
| `concurrency.rs:4`, `:21` | `ABI_VERSION` = 8 | 9 (`lib.rs:298`) — and the file's own test is named `host_ctx_v9_vtable_layout_is_stable` (`:161`) |
| `declare.rs:130-145` | "ABI v8 … the crate stamps `abi_version: 8`" | `:436` stamps `$crate::ABI_VERSION` |
| `poll_support.rs:1` | "the `concurrency`-gated ergonomics suite" | the feature is retired; `Cargo.toml` has no `[features]`; `lib.rs:159-166` says core |
| `lib.rs:16-19` | host services include "validation" through `HostCallbacks` | validation is the layout-hash gate; the callback was removed |
| `lib.rs:575` | "Current shape (ABI v3)" | the struct is right, the frame is six versions old |
| `lib.rs:586-596` | `HostCallbacks` "widens further with `rc_inc`, `rc_dec`, `invoke_closure`" | retired by the S98 ruling; `bounded-contexts.md` §5 says two fields, permanently |
| `lib.rs:893-898` (`CLIO`) | `Fn a b` "reserved for future callback support" | same retirement |
| `platforms/shapes/src/lib.rs:16` | "ABI v3" | — |
| `platforms/shapes-badabi/src/lib.rs:50`, `:96` | host ABI is 8; and 6 | in the same file |
| `exemplar/platforms/web/src/lib.rs:34-36` | the v8 leading-pair node shape | `:93-98` in the same file declares it dead |
| `CLAUDE.md` §"Known asymmetries" | records `poll_support.rs:1` as a known-stale phrasing to tolerate | the repair is the point |

### 6.2 The wash, and the two things it is not

The wash is **documentation only; no semantic API delta is authorized** (0870's
own terms). Each site above moves to one contract: ABI v10, core/ungated poll
support, layout-hash validation, a permanently two-field `HostCallbacks`, and no
closure-callback promise anywhere.

Two additions the wash carries beyond the audit's list, both established in §2.2:

- **The bump rule states its property.** `ABI_VERSION`'s rule (ii) currently
  enumerates constants. It gains the property — *a node layout is ABI-governed
  iff a DLL constructs or reads that node* — and `IO_PURE_GLUE_OFFSET` joins the
  enumeration.
- **The crate memory's false rule is corrected** (Fact 1). "Widening a node
  layout is not a bump" becomes "widening `EffectPoll`/`Launch`/`Select` is not a
  bump because no DLL constructs them; widening `Pure` or `Effect` is, because
  `CLIO::*` does." The memory also drops its "known stale phrasing" warning,
  which the wash makes untrue, and its two citation drifts
  (`concurrency.rs:133` → `:128`; the `poll_support.rs:254` row).

The wash is **not** a re-derived surface inventory. The audit was explicit: *"do
not add another manually maintained surface inventory."* Per-item public-API
truth stays the source rustdoc plus `public-api.txt`; `platform.md` carries the
shape, never a census.

### 6.2a Inbound references to the archived records

P4 archives four design records, and source comments cite them. Rust doc
comments are **not** covered by `scripts/verify-citations.py`, which scans
documents — so this drift is real and silent, and it is enumerated here rather
than left to be discovered. Inside C7's surface, the repointing rides P2:

| Site | Cites | Repoint to |
|---|---|---|
| `crates/cranelisp-platform/src/poll_support.rs` (module rustdoc and four in-body design comments) | the archived poll-support record | `poll-leaf-authoring.md` |
| `crates/cranelisp-platform/src/lib.rs:132` | the archived S71 redesign | `platform.md` |
| `crates/cranelisp-platform/src/lib.rs:190` | the archived S71 redesign, for the bump rules | `platform.md` §4.3 — the same line P2 rewrites to state the property, so this is one edit, not two |
| `crates/cranelisp-platform/tests/baseline.rs:101` | the archived S71 redesign | `platform.md` §4.3 |
| `platforms/poll-pool/src/lib.rs:7`, `:80` | the archived poll-support record | `poll-leaf-authoring.md` §2, §3 |

Four more sites are outside this stream and are routed in §16.1 (H6).

### 6.3 The manifest-sig concreteness fact (0933's platform half)

C6 owns the located refusal at `parse_and_check_platform_type_sig`, over C1's
structural funnel. **C7 adds no check.** What C7 owes is the *facade
documentation* of the resulting author-visible rule, on `PlatformFn.type_sig`'s
rustdoc and `declare_platform!`'s `sig:` key:

> A manifest type signature is fully qualified and **fully concrete**. A bare
> lowercase leaf parses as a type variable and the load refuses with a located
> error naming the leaf and the function. A platform fn is a hand-written C-ABI
> body; a polymorphic platform signature is a declared contract nothing can
> check.

**A build-time check for this was considered and rejected.** The same const
byte-scanner idiom that makes `adts:` structural could reject a lowercase leaf in
`sig:` at compile time, which would be Principle 18's grade-1 form and cheaper
for the author than a load refusal. It is not built, because the type-signature
grammar is materially richer than the schema artifact's (arrows, application,
nesting), a const scanner over it would be a third reader of a grammar that
already has two, and C6's located load refusal is the settled mechanism at the
right layer. **Trigger for reconsideration:** a second class of manifest-sig
error that only surfaces at load, or an author report that the load-time
refusal's distance from the declaration site is the actual cost.

---

## 7. Bundle P3 — the shared heap-ADT fixture (0874)

`crates/cranelisp-platform/tests/cl_adt_products.rs:51-71`,
`crates/cranelisp-platform/tests/cl_adt_sums.rs:39-63` and
`crates/cranelisp-platform/tests/worked_examples.rs:33-58` each carry a
character-for-character identical `alloc_full_heap_adt`, two carry an identical
`dealloc_heap_adt`, and all three duplicate the `static INSTALL: Once`
schema-installation preamble. No `tests/common/` directory exists today.

The shape:

- **The three binaries stay separate.** Each owns a write-once `GLOBAL_SCHEMA`;
  merging them would make schema lifetimes interfere, and the isolation is the
  reason the split exists. 0874's own terms say so.
- **One private `common` module** is proposed under the crate's `tests/`,
  imported by all three, carrying
  `alloc_full_heap_adt`, `dealloc_heap_adt` and `read_rc` with **one explicit
  layout contract in its rustdoc** — `[total_size@0][rc@8][tag@16(u32)][pad@20][field_i@24+8i]` —
  cited to `HeapHeader` and `alloc_with_tag`'s five-step contract rather than
  restating the numbers as folklore.
- **The schema-installation preamble is not shared.** Each binary's synthetic
  schema is that binary's subject; sharing it would couple the three tests'
  fixtures to each other and hide which schema a failure is about.
- **No new public test-support API.** `tests/common/` is a private module of the
  integration binaries; nothing is added to `public-api.txt`.
- Every existing production API assertion is preserved verbatim. This is a
  fixture extraction, not a test rewrite: if any assertion changes, the bundle
  has exceeded its remit.

**Why P3 rides P0.** The fixture encodes the heap layout at the byte level, which
is the seam this sprint moves. Extracting the helper before the bump means
writing the contract twice; after it, twice again. One touch, on the most
dangerous byte-layout seam in the crate, is the whole point of the stream model.

---

## 8. The extension seam, and why the 0463 deferral is safe

The user deferred the narrowed network lesson and bound the deferral: *"It must
not change the platform interface: future platform developers define socket
operations using the existing mechanism."* C7's obligation is to state the exact
interface facts that make that true, and to say what would falsify them.

### 8.1 The claim

**The platform crate has no capability vocabulary.** It does not enumerate,
match on, allow-list or otherwise know any effect name, syscall, or resource
kind. Effect names are *data* the DLL's manifest supplies and
`manifest_to_descriptors` copies; nothing in the crate branches on one. There is
consequently no list from which "network" could be omitted, and therefore nothing
for the deferral to narrow.

This is a **structural** property — a property of the data flow, not of a test
that probes it. That is what makes deferring the lesson costless to the
interface: the seam's guarantee does not depend on how many capability examples
exist.

### 8.2 The six facts, each verified against live source in this pass

| # | Fact | Source |
|---|---|---|
| 1 | `PollFn` is `unsafe extern "C" fn(state, *const HostCtx, *const Waker) -> Poll` — an opaque state pointer and two host handles. It carries no operation vocabulary; any non-blocking syscall shape fits. | `concurrency.rs:96-101` |
| 2 | `HostCtx` is a six-slot vtable: `register_readable`, `register_writable`, `register_timer`, `acquire`, `retire`, `host`. Readiness registration is **fd-generic** — a socket, a pipe, an inotify fd and a timerfd register identically. | `concurrency.rs:63-94` |
| 3 | `ConcurrencyDescriptor` + `ResourceRole {None, Produce, Consume, Retire}` express a resource lifecycle abstractly. `accept` is a `Produce`; `read`/`send` are `Consume`; a close is `Retire`. No network naming appears in the vocabulary. | `concurrency.rs`, `cranelisp-types::scheduling` |
| 4 | `declare_platform!`'s `descriptor:` key admits any poll leaf and its `schema:`/`adts:` arm binds any ADT the compiler generates. A future socket platform declares `Socket`/`Listener` as ordinary `.cl` types and needs no platform-crate change. | `declare.rs:194-285` |
| 5 | The existence proof already exists: `exemplar/platforms/web` implements `bind-listener`/`accept-conn`/`read-conn`/`send-conn` — a real `TcpListener`, real `accept`, real `read`, real `send` — **entirely through the published facade, with no platform-crate extension.** | `exemplar/platforms/web/src/lib.rs` |
| 6 | Two structurally different leaf families already ride the one carrier in-tree: `poll-pool`'s eight leaves (including `Produce`/`Consume` roles and self-`acquire` through the ctx vtable) and `stdio`'s mixed blocking-`print` / poll-`read-line` singleton-resource shape. Extension is exercised, not merely permitted. | `platforms/poll-pool`, `platforms/stdio` |

### 8.3 What is actually deferred, and what remains true

Deferred: a *free-standing* socket platform under `platforms/`, a client-connect
driver, and a deterministic server-driving harness — the three blockers 0463
itself names, re-verified as standing (no `platforms/` fixture binds a socket).
None of these is an interface capability. All three are **fixtures and
harness**, which is why deferring them changes nothing an author can or cannot
express.

**C7 performs no platform work for 0463.** Its disposition is verification plus
the record above. The reconsideration trigger is the one the user set: a reusable
network platform or a deterministic server-driving lesson being independently
scheduled.

### 8.4 One repair this pass makes on 0463's behalf

`poll-support.md` cited "FIXME 0463" four times (`:463`, `:511`, `:541`,
`:1374`) meaning an entirely different, long-resolved platform-internal question
about the v8 poll leading-pair injection point — a mechanism that v9 itself
retired. A disposition of the live 0463 that opened that document would read
"resolves FIXME 0463" against a heading describing retired machinery and be
actively misled. The document moves to `archive/poll-support-s96.md` in this
pass with a banner naming the collision, and its live successor
(`poll-leaf-authoring.md`) carries no such citation. This is the "records are
claims too" failure mode caught before it cost a disposition.

---

## 9. Per-filing disposition

Grouped as the brief requires — implementation, current-state wash, evidence, or
retirement — rather than four separate passes.

| Filing | Central claim verified against source? | Class | Disposition |
|---|---|---|---|
| **0463** — network poll-shape lesson | **Yes.** `platforms/` still binds no socket; no client-connect leaf exists; the examples harness is still the bare exit-code umbrella. | **evidence / retirement** | **No platform work.** Deferred per the user's 2026-09-01 ruling, with §8's six interface facts as the record that the deferral narrows nothing. `sprint` annotates the filing; it stays open under the user's stated trigger. |
| **0870** — facade describes retired ABI | **Yes.** All eleven cited sites re-verified stale (§6.1). | **current-state wash** | Bundle P2, riding P0. Documentation only; no semantic API delta. Two additions established here: the bump rule states its property, and the crate memory's false node-layout rule is corrected. Resolvable at wave exit. |
| **0871** — design canon collapse | **Yes.** Five live records ≈3,900 lines; `poll-support.md` 1,414 with a landed implementation order; three live historical files; a stale manual census at `platform.md:97-107`. | **retirement** | **Resolved by this pass.** Four superseded records archived, `platform.md` rewritten without the census, the per-sprint pass log or the retired callback commitment, and `poll-leaf-authoring.md` authored as the right-sized poll design. `sprint` deletes the filing. |
| **0873** — marker binding | **Yes.** Five hand-written production markers; `resolve_field`'s type-key/field-miss conflation confirmed at `adt.rs:334-372`. | **implementation** | Bundle P1. Design complete and `arch`-approved; this pass flips the design's status and transcribes the three gate conditions. `dev` implements; the filing resolves when the detection proof lands. |
| **0874** — shared heap fixture | **Yes.** Three character-identical `alloc_full_heap_adt` copies; no `tests/common/` exists. | **evidence** (test support) | Bundle P3, riding P0. Three binaries stay separate; one private layout fixture; no new public test-support API; every production assertion preserved. |
| **0934** (C5's; C7 handoff) | Consumed. | **implementation** | Bundle P0 — the 9→10 bump and the fixture rebuilds, C7's only ABI act. The platform-edge residual §4.2 named is **closed by the `arch` platform-return ruling**, not carried: C7's remaining work is the sentinel, the independent platform offset pin (§4.4) and the `Pure`-returning fixture plus acceptance leg (§4.5) the stamp is measured on. |
| **0933** (C6's; C7 consequence) | Consumed. | **current-state wash** | The facade sentence in §6.3. No check, no predicate, no second reader of the sig grammar. |

**Retirements this stream can claim: 0871 (this pass) and, at wave exit, 0870,
0873 and 0874.** 0463 remains open by user ruling, not by omission.

---

## 10. Bundles in order

```
P4 (this pass, design)  →  P0 ⊕ P1 ⊕ P2 ⊕ P3 (one dev change-set)  →  review  →  wave exit
```

**Why P0–P3 are one change-set and not four.** They collide on the same files by
construction, not by coincidence:

- `lib.rs` carries `ABI_VERSION` (P0), the `CLIO::pure` widen (P0) and the
  crate-root and `HostCallbacks`/`CLIO` rustdoc (P2).
- `declare.rs` carries the ABI-v8 macro rustdoc (P2) and gains
  `schema_declares_type` plus the `adts:` arm (P1).
- `platforms/shapes` and `exemplar/platforms/web` rebuild for the bump (P0),
  migrate their markers (P1) and lose their stale headers (P2).
- The integration fixtures encode the heap layout the bump moves (P3 ⊕ P0).

Splitting them means three extra visits to five files and a window in which the
tree carries a widened node, a half-migrated marker set and rustdoc describing a
version that exists in neither. The stream model's whole claim is that this is
one visit.

**Ordering inside the change-set**, which does matter:

1. `ABI_VERSION` 9→10 and the `Pure` widen with its constant and the platform
   offset pin (P0, §4.4), because every other edit's text depends on the number
   and every later step in this list depends on the three-word node existing.
2. The four version pins (P0, two of them `test`-owned — handoff H1).
3. `schema_declares_type` and the `adts:` arm with their detection proof (P1).
4. Fixture rebuilds, marker migrations, `shapes-badabi` repoint and its detection
   proof (P0 ⊕ P1).
5. **The two `Pure`-returning `test-capture` fns (P0, §4.5)** — strictly after
   step 1, because a `Pure`-returning platform fn against a v9 two-word node is
   the ruling's own window falsifier (an out-of-bounds store at base+32). This is
   an ordering *requirement*, not a preference, and §15 reject 14 states it.
6. The rustdoc and memory wash (P2) — after the source edits, so it describes
   what landed.
7. `tests/common/` extraction (P3) — independent of 1–6, placed last so a
   fixture failure during 1–5 is attributable to the layout, not the extraction.

**Position in the W3 braid.** C7 is one retained visit, paused once rather than
closed and redispatched. After C5 I0a exists, C7 stages only P0's ABI-10 node,
constant and independent offset pin, with no `Pure`-returning fixture. C4 then
lands its construction stamps and B5 adoption arm against that widened layout.
The same C7 visit resumes, adds the `Pure` fixtures only now, completes P1–P3 and
closes. C5 I0b then lands the atomic claim and discharge together before R4
E1–E3 or the wider IO acceptance set executes. Thus no runnable intermediate
tree contains a platform-returning `Pure` without all of the tag dispatch,
three-word node and post-publication claim/discharge mechanism. C6 remains
outside this crossing; `sprint` owns the retained reservations and pause.

---

## 11. Source, fixture and module-test reservations

Exact writable paths this stream claims. Every path appears once across the
sprint's streams, or is flagged in §16.

### 11.1 Crate source

| Path | What changes | Bundle |
|---|---|---|
| `crates/cranelisp-platform/src/lib.rs` | `ABI_VERSION` 9→10 + its rustdoc rule (ii) and history entry; new `IO_PURE_GLUE_OFFSET` + the independent compile-time platform offset pin (§4.4); `CLIO::pure` widen + sentinel write + the authority-split rustdoc (DLL writes `0`, the crossing adopts); crate-root `//!`; `HostCallbacks` rustdoc; `CLIO` rustdoc; `CLType` sealed-set rustdoc (the nested-`Pure` unconstructability §4.2 rests on); `PlatformFn.type_sig` rustdoc | P0, P2 |
| `crates/cranelisp-platform/src/declare.rs` | `schema_declares_type`; `adts:` arm on arm 1; the "ABI v8" macro rustdoc block | P1, P2 |
| `crates/cranelisp-platform/src/adt.rs` | `resolve_field` type-key-miss diagnostic | P1 |
| `crates/cranelisp-platform/src/concurrency.rs` | module rustdoc `:4`, `:21` → v10 | P2 |
| `crates/cranelisp-platform/src/poll_support.rs` | module rustdoc `:1` → core/ungated; five design-comment repoints (§6.2a) | P2 |
| `crates/cranelisp-platform/CLAUDE.md` | the node-layout bump rule (Fact 1); ABI 10 + `Pure` layout; drop the stale-phrasing asymmetry; two citation repairs | P0, P2 |
| `crates/cranelisp-platform/public-api.txt` | regenerated | P0, P1 |

### 11.2 Module tests (this crate's own tiers)

| Path | Rows |
|---|---|
| `crates/cranelisp-platform/src/tests.rs` | `abi_version_is_9` → `_is_10`; `CLIO::pure` footprint and sentinel cells (§12 A1, A2) |
| `crates/cranelisp-platform/src/declare/` inline `mod tests` | `schema_declares_type` cells (§12 B1–B6); the `adts:` expansion cell |
| `crates/cranelisp-platform/src/adt/tests.rs` | the type-key-miss diagnostic cell (§12 C1) |
| `crates/cranelisp-platform/src/schema/tests.rs` | unchanged |
| `crates/cranelisp-platform/src/concurrency.rs` inline `mod tests` | unchanged (layout pins hold; the file's rustdoc is what moves) |

### 11.3 Crate integration tests

All under `crates/cranelisp-platform/tests/`.

| Path | What changes |
|---|---|
| `common/mod.rs` | **proposed new** — the shared layout fixture (P3) |
| `crates/cranelisp-platform/tests/cl_adt_products.rs`, `crates/cranelisp-platform/tests/cl_adt_sums.rs`, `crates/cranelisp-platform/tests/worked_examples.rs` | import `common`; delete the local copies; assertions untouched (P3) |
| `crates/cranelisp-platform/tests/baseline.rs` | the `= 9;` source-text pin → `= 10;` (P0) |
| `crates/cranelisp-platform/tests/macro_expansion.rs` | the literal `9` → `ABI_VERSION` (P0) — pin the const, not the number, so the next bump costs one site fewer |
| `crates/cranelisp-platform/tests/macro_full_arm_compile.rs` | gains the `adts:` arm so the all-arms compile fixture stays complete (P1) |

### 11.4 Platform fixtures

| Path | What changes |
|---|---|
| `platforms/shapes/src/lib.rs` | marker → `adts:`; stale "ABI v3" header |
| `platforms/shapes-badabi/src/lib.rs` | `STALE_ABI_VERSION` 2→9 + the standing rule in rustdoc; the two contradictory ABI claims |
| `platforms/poll-pool/src/lib.rs` | rebuild; two design-comment repoints (§6.2a) |
| `platforms/test-capture/src/lib.rs` | rebuild; **append the two `Pure`-returning fns** (§4.5) after the widen |
| `platforms/{stdio,boom,async-demo,pool-demo}` | rebuild only; no source change unless a stale ABI claim is found in the same read |
| `exemplar/platforms/web/src/lib.rs` | four markers → `adts:`; delete the retired v8 leading-pair paragraph at `:34-36` |

**On the `test-capture` addition.** Appending keeps every existing manifest index
— and therefore every existing GOT slot — unchanged. No in-tree lane asserts that
platform's descriptor count or enumerates its exported names (verified in this
pass across `tests/spec_platforms.rs`, `tests/spec_10_io.rs`,
`tests/platform_errors.rs`, `tests/concurrency_capacity.rs`,
`tests/facade_pif_rows.rs`), so the two new names reach only the lanes that glob
`platform.test-capture`; the implementing change-set re-confirms that before
landing rather than trusting this sentence.

### 11.5 Not reserved, and deliberately

- `src/platform.rs` — C6's, for both the mint and 0933's refusal.
- `crates/cranelisp-intrinsics/src/{drop,io}.rs` — C5's.
- `crates/cranelisp-backend/src/compiler/apply.rs` and
  `crates/cranelisp-backend/src/heap.rs` — C4's. The tag dispatch is **B5's**
  under the ruling. C7 writes and reserves no backend line.
- `tests/concurrency_poll_edge_guards.rs` and `tests/facade_pif_rows.rs` —
  `test`'s; handoff H1.
- `exemplar/` outside `platforms/web/` — U8's; the split is settled in §16.3.

---

## 12. Unit-test design (platform tier)

Rows this design implies, per submodule × scenario class (Principle 23). `qa`
owns whether any becomes a plan row; these are the design's implications.

**A — `lib.rs`, the `Pure` footprint (P0)**

| # | Scenario | Cell |
|---|---|---|
| A1 | positive | `CLIO::pure(CLInt)` allocates a node whose `alloc_size` header is at least `HEAP_HEADER_SIZE + 24` |
| A2 | positive | the word at payload `IO_PURE_GLUE_OFFSET` reads `0` on a freshly constructed node — the sentinel is written, not merely left unallocated |
| A3 | negative | the `Effect` node's four payload offsets are unchanged from v9 (the widen is `Pure`-only, and this is the cell that catches a wrong-node edit) |
| A4 | **structural** | the §4.4 platform-side pin: `HEAP_HEADER_SIZE + IO_PURE_GLUE_OFFSET == 32` as a `const _: () = assert!(…)`. Not a test row — it is a compile failure, which is the point; it is listed here so a reader looking for the offset's protection finds it |

**B — `declare.rs`, `schema_declares_type` (P1)**

| # | Scenario | Cell |
|---|---|---|
| B1 | positive | a declared entry returns `true` |
| B2 | negative | an absent key returns `false` |
| B3 | **discriminating** | a key that occurs **only as a field type** returns `false` — the depth-tracking cell; a `strstr` implementation passes B1/B2 and fails here |
| B4 | negative | a near-miss inside a `;;` comment returns `false` |
| B5 | boundary | the empty artifact returns `false` |
| B6 | boundary | an applied-form key (containing `(` or whitespace) is rejected with the documented message |

**C — `adt.rs`, the miss diagnostic (P1)**

| # | Scenario | Cell |
|---|---|---|
| C1 | positive | a read against an unknown *type key* reports a type-key miss and lists the known keys |
| C2 | **control** | a read against a known type with an unknown *field* still reports a field miss — C1 must not swallow the case it is distinguishing from |

**D — the two detection proofs** (change-set obligations, not rows)

| # | Instrument | Positive leg | Negative leg |
|---|---|---|---|
| D1 | the `adts:` const assertion | a misspelled key fails the build with the intended message | the correct spelling builds |
| D2 | `shapes-badabi`'s refusal | `STALE_ABI_VERSION = 9` refuses with `AbiVersionMismatch` | temporarily set to `ABI_VERSION`, the same e2e loads |

**E — the platform-return acceptance leg** (`qa`'s placement, H3; C7 supplies the
fixture and the shapes, and the leg runs in the C4/B5 crossing subwave after C5
I0b because it needs C4's stamp, C7's rebuild and C5's claim/teardown together)

| # | Scenario | Cell |
|---|---|---|
| E1 | positive | `pure-string` called and **not** forced: zero un-discharged strings after teardown (the F4 inversion — under-claiming would show one) |
| E2 | **control** | the same node forced: exactly one successful claim transfers one live string to the program; teardown observes `Claimed`, performs no payload discharge, and nothing is double-freed (without the control, E1 is also satisfied by a double discharge) |
| E3 | negative | `pure-int` called and not forced: nothing discharged, no call through a zero word |

The negative legs are the load-bearing halves. A refusal that fires for the
wrong reason — a missing export, a parse failure — is indistinguishable from a
working gate until someone reads the stderr, and this repository has paid for
that twice.

---

## 13. Public API, schema and ABI effects

| Surface | Effect | Owner |
|---|---|---|
| `cranelisp-platform/public-api.txt` | **+2 lines**: `pub const fn schema_declares_type` (approved at the S118 `arch` gate) and `pub const IO_PURE_GLUE_OFFSET`. No removals. The exact diff is enumerated at implementation and regenerated with the one canonical command G0 settles (FIXME 0945); no baseline is regenerated before that procedure repair lands. | C7 |
| `declare_platform!` | **+1 optional key** (`adts:`) on arm 1. Macros are not in the baseline, but this is external-author surface under Principle 15 and is recorded as such. Arm 2 (no `schema:`) is unchanged, and `adts:` without `schema:` is a match failure. | C7 |
| `ABI_VERSION` | **9 → 10.** C7's only ABI act; one bump, one refusal, no compatibility mode. | C7 |
| IO node layout | `Pure` 16 → 24 payload bytes. Every other tag byte-identical. | `arch` ruled; C7 executes the version half |
| Glue-word state authority at the crossing | **Contract change, no public delta.** The DLL writes only the unpublished `0` sentinel; C4's B5 tag arm adopts with `0` or canonical glue before publication; after publication C5 force and teardown are the only accessors and both atomically exchange to `Claimed`. `CLIO::pure`'s rustdoc states the platform half; platform implements no claim. R1 adds no tag, field, public constant, schema change or ABI bump beyond P0's already-planned 9→10 | `arch` ruled; C7 documents |
| Platform absolute offset 32 | C7 lands `HEAP_HEADER_SIZE + IO_PURE_GLUE_OFFSET == 32` as an independent compile-time assertion beside the platform constant. C4 independently owns the backend pin (§4.4). | C7 |
| `platforms/test-capture` manifest | **+2 appended fns** (`pure-int`, `pure-string`, §4.5). Fixture surface, not published API; appended so no existing manifest index or GOT slot moves | C7 |
| `CACHE_SCHEMA_VERSION` | **untouched.** C1 owns 24→25. C7 creates no second cache version and captures no acceptance cache baseline inside C1's window. | C1 |
| `CLAdtType`, `CLAdt`, `Schema`, `CLType`, `CLHeap`, `CLOwned` | **unchanged contracts.** `CLAdtType` stays hand-implementable; no typed handle wraps a raw teardown entry point; owned/borrowed crossings are as established. | — |
| Schema artifact grammar | **unchanged.** `schema_declares_type` is a second *reader*, named at both sites per the `arch` gate's condition 1. | — |
| `cranelisp-types` | **zero.** | C1 |
| Host load path | **unchanged** in mechanism. The mint's authority moves under C1/C6; the DLL slab still wraps in place and `got_slot = manifest index = mint slot`. | C6 |

---

## 14. Falsifiers

Each names an observation that would refute a claim this design makes, and where
it would come from.

| # | Claim | Falsifier |
|---|---|---|
| **F1** | The 9→10 gate refuses a prior-version DLL. | `shapes-badabi` at `STALE_ABI_VERSION = 9` loads, or refuses for a reason other than `AbiVersionMismatch` (D2's negative leg is what distinguishes these). |
| **F2** | `schema_declares_type` matches declarations, not occurrences. | B3 passes with a byte-scanner that ignores paren depth — i.e. a key present only as a field type returns `true`. |
| **F3** | The widen is `Pure`-only. | A3 reds: any `Effect` payload offset moves, or any other tag's size changes. |
| **F4** | The ruling closes the platform-edge residual: a DLL-constructed `Pure` over a heap payload, adopted at the crossing, is discharged or transferred exactly once. | E1/E2 (§12): `pure-string` unrun shows any un-discharged string (the stamp did not land, or teardown did not win the claim), **or** forced shows a double free or more than one successful claim. Either result reopens the residual this design records as closed. |
| **F4′** | No DLL-minted `Pure` reaches the host except as a platform call's return value, so the crossing sees all of them. | A `CLType` implementation for `CLIO<T>` (which would make `pure(pure(…))` constructable and hide a node inside a payload), or any `CLIO`-returning position in the facade other than a platform fn's return. Both are public-API deltas, so the `public-api.txt` diff is where this is observed. |
| **F5** | The platform crate has no capability vocabulary, so the 0463 deferral narrows nothing. | Any `match`, comparison or table lookup on an effect name, syscall name or resource kind appearing inside `cranelisp-platform`. Today there is none; the falsifier is stated rather than instrumented, because instrumenting it would be the manually maintained inventory the audit forbade. Grade: **asserted with a named falsifier.** |
| **F6** | The `adts:` assertion is armed. | D1's positive leg does not fail the build, or fails with a message that names neither the marker nor the key. |
| **F7** | `Pure`'s widen does not move the run lane's reads. | Any trampoline field-0 read changes offset. (Cross-checks C5 §4.3's field-1/field-0 correction from the platform side: the payload stays at field 0.) |
| **F8** | The platform composition of the crossing offset remains absolute byte 32. | The compile-time assertion is removed or weakened, or `HEAP_HEADER_SIZE + IO_PURE_GLUE_OFFSET` differs from 32. Either change fails the `cranelisp-platform` build while the assertion stands; C4's separate emission evidence owns correct backend use of the same absolute offset. |
| **F9** | The DLL never writes a non-zero glue word. | Any write to `IO_PURE_GLUE_OFFSET` inside `cranelisp-platform` or a `platforms/*` fixture other than the `0` sentinel in `CLIO::pure`, or a third `HostCallbacks` field that could supply one. Grade: **asserted with a named falsifier** — a grep-shaped claim, not an instrumented one, because the write surface is this crate plus in-tree fixtures and the S98 two-field ruling already gates the callback half. |

---

## 15. `/review` reject criteria

The change-set is rejected if any of these holds.

1. **`ABI_VERSION` bumped without every fixture rebuilt**, or any fixture left
   asserting the old number. Four text pins exist (§2.2 Fact 2); a green suite
   with a stale pin means a pin is not checking what it claims.
2. **A second gate, mode or compatibility path** for v9 DLLs. One number, one
   refusal.
3. **`CACHE_SCHEMA_VERSION` touched**, or an acceptance cache baseline captured
   inside C1's window.
4. **The `Pure` widen applied to any other tag**, or the payload moved off field
   0.
5. **`CLIO::pure` writing anything but the unpublished `0` sentinel, or platform
   code implementing any post-publication claim** — in particular writing the
   reserved `1`, a fabricated glue address, a class tag, or a value obtained
   through a widened `HostCallbacks`. Any of these mints a second ownership
   mechanism or reopens the S98 two-field ruling. C5 owns the atomic claim; the
   sentinel is the DLL's only legal write to that word (§4.1).
6. **A second concreteness predicate for manifest signatures** anywhere in this
   crate. C6 owns the refusal; C7 owns the sentence.
7. **`adts:` accepted without `schema:`**, or the const assertion landing without
   its detection proof (both legs) in the same change-set.
8. **Author rustdoc lost in the marker migration.** The four web markers carry
   load-bearing documentation; a mechanism that discards it is not the approved
   mechanism.
9. **`schema_declares_type` and the runtime parser not citing each other** —
   `arch` gate condition 1, and the whole reason a second reader was acceptable.
10. **A new manually maintained surface or file census** in any platform design
    document or crate rustdoc. This is what 0871 exists to remove.
11. **The three integration binaries merged**, or `tests/common` exposed as
    public test-support API.
12. **Any production assertion changed in P3.** It is a fixture extraction.
13. **A "test owed" deferral.** Every fix in this change-set lands with its unit
    row; the e2e need was assessed here (the refusal and dispatch lanes already
    exist and are named in §3.4).
14. **A `Pure`-returning platform fn ordered before the widen**, in this
    change-set or any other. That is the ruling's own window falsifier: against a
    two-word v9 node the B5 Pure arm stores out of bounds at base+32.
15. **Any platform-local absorption of the stamp** — a `CLIO::pure` footprint
    chosen to make a fixed-offset store land inside the allocation, a reserved
    absorber word, or a tag-shaped guard added inside this crate. `arch` rejected
    the fallback (§4.6); the dispatch is the backend's, at one chokepoint.
16. **The §4.4 offset pin absent**, or expressed as a comment rather than a
    compile-time assertion. Two names for one byte with nothing holding them
    together is the drift this bundle exists to prevent.

---

## 16. Handoffs, collisions, and what is open

### 16.1 Handoffs out

| # | To | Content |
|---|---|---|
| **H1** | `test` | Two project-root `tests/` files pin the ABI number as literal text and must move with the bump: `tests/concurrency_poll_edge_guards.rs:66,134` (source-text grep for `= 9;`) and `tests/facade_pif_rows.rs:759` (frozen-table comment still naming `ABI_VERSION = 8` — already stale at HEAD, independently of this bump). Recommended shape: pin the const, not the number, wherever the assertion permits. |
| **H2** | — | **DISCHARGED** by the `arch` platform-return ruling (`total-concreteness.md` §3.4, 2026-09-01). The finding was confirmed at source, the tag dispatch is allocated to C4 bundle B5 in its existing backend visit, and the platform-local fallback is rejected. Retained as a row so a reader following the old handoff arrives at the ruling rather than at silence. C7's remaining halves are the sentinel (§4.1), the pin (§4.4) and the fixture and acceptance leg (§4.5). |
| **H3** | `qa` | (a) the §4.5 acceptance leg — E1/E2/E3 placement, and that **F4 is now an expected-GREEN cell rather than a leak allowance**: the platform-edge residual is closed by the ruling, so a hit is a defect, not an accepted debt; (b) R1's shared-node/duplicate-force evidence remains C5+`test` evidence and is not duplicated in C7; (c) the two detection proofs (D1, D2) as arming evidence rather than coverage rows; (d) the traceability consequence of the ABI bump for any spec row citing v9. |
| **H4** | `sprint` | Preserve the §16.3 reservations and QA's retained-visit W3 braid: C5 I0a; stage C7 P0 without a `Pure` fixture; land C4 including B5; resume and close C7 with the fixtures; land C5 I0b atomic claim+discharge; only then execute R4 E1–E3. No crate is released and redispatched across its pause. |
| **H8** | `sprint` → `design`(backend) | **A record-currency finding, not a design ask.** `design/backend/s121-c4-visit.md` §6.3 still describes the `Pure` stamp's construction sites as "a **closed set of three**", and §13 reject 10 rejects a write to the glue word "outside the closed set of three". The ruling makes the platform-return adoption stamp the **fourth sanctioned site** and says §13 reject 10 reads accordingly. The ruling also states the C4 design visit is not re-opened, so this is a one-line currency repair in a record C7 does not own — flagged rather than left for `dev`(backend) to hit as a contradiction between its contract and its reject list. |
| **H5** | `dev`(platform) | The crate `CLAUDE.md` current-state obligations named in §6.2 — the false node-layout bump rule, the retired stale-phrasing asymmetry, and the two citation drifts. These are memory, not design, and land in the implementing visit. |
| **H6** | `sprint` → `arch`, `design`(backend), `dev`(intrinsics) | Four references to records this pass archived, outside C7's surface. **`arch`**: `design/arch/platform-interface.md:13` (cites the archived S76 host-wiring seam map), `:1517` and `:1636` (both name the archived poll-support record as the re-cascade target — the cascade landed, and its live successor is `poll-leaf-authoring.md`). **`design`(backend)**: `design/backend/io-trampoline.md:2157`. **`dev`(intrinsics)**: `crates/cranelisp-intrinsics/src/alloc.rs:384` and `alloc/tests.rs:94,120` cite the archived S76 record in a `// spec:` annotation — a traceability annotation pointing at an archived plan, so `qa` may want it retargeted rather than merely repointed. None blocks C7; all are silent, because doc comments are outside the citation checker's corpus. |
| **H7** | `qa` | The citation-drift ratchet. `design/platform/` now verifies clean **without** the baseline: all ten platform rows in `scripts/citation-drift-baseline.txt` are repaired by this pass (five `platform.md` path rows and one line row by the rewrite, three `poll-support.md` rows by the archive move, one `adt-marker-binding.md` row by a citation repair). The baseline is `qa`-owned and this pass did not edit it; the rows are now deletable, which is the ratchet working as intended. |

### 16.2 Blockers

**None hard.** The retained-visit order and one procedural gate are `sprint`'s
to enforce:

- C7 stages the widen, constant and pin after C5 I0a, then pauses without a
  `Pure`-returning fixture. C4 lands its construction stamps and B5 adoption arm
  before the same C7 visit resumes and adds the fixture.
- C5 I0b lands the atomic claim and discharge after C7 closes. Until then the
  fixture exists but does not execute; a platform-returning `Pure` in a runnable
  intermediate tree is the ruling's window falsifier.
- The §4.5 acceptance leg executes only after C5 I0b, because it needs C4's
  stamp, C7's rebuilt fixture and C5's claim/teardown together. It is not a
  blocker on the C7 change-set; it is a statement of when the evidence exists.
- `public-api.txt` is not regenerated until G0 lands the canonical regeneration
  procedure (FIXME 0945).

### 16.3 Reservations settled at the boundary

1. **`exemplar/platforms/web/` — SETTLED, not open.** The stream table gives
   `exemplar/` to U8 and "platform fixtures" to C7, and 0873's `refers_to` names
   `exemplar/platforms/web/src/lib.rs` explicitly. The split is:
   **C7 reserves `exemplar/platforms/web/` — that DLL crate and nothing else —
   and U8 owns the whole of the rest of `exemplar/`, including every `*.cl`, the
   manifest, and the exemplar's own documentation.** The boundary is the crate
   directory, not a file list, so a new file inside `exemplar/platforms/web/` is
   C7's and a new file anywhere else under `exemplar/` is U8's. The reason it
   falls this way: the two edits web takes this sprint — the ABI rebuild and the
   mechanical marker migration — are the platform stream's own contracts applied
   uniformly across nine fixtures, and splitting the ninth off would mean two
   streams doing one migration. Nothing C7 writes in that directory is
   language-facing, so U8's acceptance pass reads it as it reads any other
   platform.
2. **`src/platform.rs` is C6's**, and 0933's refusal edits the same function this
   crate's facade documents. No overlap in writable paths — C7 writes only the
   platform crate's rustdoc — but the two sentences must agree, so C7's §6.3 text
   is written to C6 §8.2's wording rather than independently.
3. **`design/platform/CLAUDE.md` names subsystems that live in other crates**
   (`allocator.md`, `string-runtime.md`) as this directory's expected content.
   Corrected in this pass, since the file is in this stream's boundary.

### 16.4 Open, and owned elsewhere

- **The severed-join residual** — `qa` intake per the Phase-3 readiness gates.
  It is not a condition this design creates and not one C7 can close. R1 is
  settled: C5 owns the once-only atomic claim, and a DLL-constructed `Pure`
  participates in that same mechanism after C4 adopts it. C7 adds no
  platform-side claim or duplicate R1 evidence.
- **`PlatformFn.ptr`'s residual field** — the fn pointer is carried redundantly
  with the GOT. Not a contract violation, long recorded, and removing it is an
  ABI bump of its own. Deliberately not bundled here: this window's bump has one
  reason, and a second reason would make the refusal evidence ambiguous.
  **Trigger:** the next bump for any other cause.
- **Compile-time field-name checking** for `read_field("…")`. Out of budget
  (Principle 6) and recorded in `adt-marker-binding.md` §6. **Trigger:** a
  reported field-string mismatch, or a platform exceeding roughly a dozen
  distinct field names.
- **A build-time manifest-sig concreteness check** — considered and rejected in
  §6.3 with its trigger.
- **`inc_rc`/`dec_rc` naming** — a deliberate long-standing asymmetry; renaming
  cascades to consumers. Unchanged.

**No user-owned, spec or architecture decision remains implicit in this design,
and none is now outstanding.** Every contract it consumes was ruled before or
inside this window; the one item it could not decide — the platform-return stamp
— was ruled by `arch` on 2026-09-01 and is consumed here, not re-opened. What
leaves this stream is record currency (H8) and evidence siting (H3), neither of
which is a design question.

---

## 17. Quality attributes

| Attribute | This visit's effect |
|---|---|
| **Simplicity** | Net reduction. Four design records leave the live set; the master loses a stale census, a per-sprint pass log and a retired forward commitment. In source, one node grows one word and one duplicated fixture converges to one. |
| **Maintainability** | The bump rule gains its *property* rather than another constant in a list, so the next node change is decidable without re-deriving it. The crate memory stops carrying a rule that contradicts the crate. |
| **Security / safety** | The version gate's purpose is stated as what it prevents (a garbage word called as a function pointer), not as bookkeeping. The one material hazard at the public facade — a kind-selected store landing outside a `Pure` node — was escalated rather than absorbed, and is now closed at its mechanism by the ruled tag dispatch (register row R19); C7's contribution is the layout, the pinned offset, the version refusal and the first traffic the seam has ever had. The platform-edge under-claiming residual moves from *asserted with a falsifier* to structural-plus-measured (§4.2). |
| **Testability** (Principle 5) | `schema_declares_type` is a pure total function over `&str`, unit-testable to its boundaries with no host, no DLL and no schema install. Both new instruments carry two-leg detection proofs. |
| **Observability** | A marker/schema disagreement moves from a runtime panic — or, on the poll path, an unattributable process abort — to a build error naming the marker and the key. The `resolve_field` diagnostic stops misattributing a type-key miss as a field miss. |
| **Concurrency-safety** | The poll ABI, `HostCtx`, waker contract and reactor boundary are unchanged. For `Pure`, this crate writes only the sentinel while the node is exclusive and unpublished; C4 adopts before publication, and C5 owns every later atomic claim. The crate adds no thread or claim implementation and still holds only its three per-DLL write-once globals. |
| **Performance** | One extra word per DLL-constructed `Pure` node — a node no shipped platform builds. The `adts:` check is const-evaluated at zero runtime cost. |

---

## Next skills

- **`sprint`** — H1, H4 and H8, and the §16.3 reservation as settled. No
  decision this design owes is outstanding: H2 is discharged by the `arch`
  ruling, and §4.4's platform pin is wholly inside C7.
- **`qa`** — H3: the §4.5 acceptance leg (E1–E3), F4 re-read as an expected-GREEN
  cell rather than a leak allowance, and the two detection proofs as arming
  evidence.
- **`test`** — H1: the two project-root ABI text pins.
- **`dev`(platform)** — P0 ⊕ P1 ⊕ P2 ⊕ P3 as one change-set, in §10's internal
  order — including the two `Pure`-returning fns strictly after the widen — each
  bundle with its §12 rows and each instrument with both legs of its detection
  proof; plus H5's memory obligations.
- **`dev`(backend)** — no ask from C7. B5 consumes the ruling directly; C7's
  only backend-facing artifacts are the pinned offset and the fixture its stamp
  is measured on.

## Cross-references

- `design/platform/platform.md` — the master design this visit rewrites
- `design/platform/adt-marker-binding.md` — the approved marker mechanism (0873)
- `design/platform/poll-leaf-authoring.md` — the v9 poll-leaf contract
- `design/arch/total-concreteness.md` §3.4, §3.5 — the `Pure` layout, the
  platform-return stamp ruling and the platform-sig concreteness rulings
- `design/arch/safety-invariants.md` §4 rows R19–R20 — IO-node stamp writes are
  tag-licensed and a `Pure` payload transfers at most once
- `design/arch/interfaces.md` §"IO Tag Constants" — the layout of record
- `design/arch/bounded-contexts.md` §5 — the platform bounded context and the
  permanently two-field `HostCallbacks`
- `design/intrinsics/s121-c5-intrinsics-visit.md` §4, §14, H6 — `free_io_node`
  and the ABI gate on I0b
- `design/int/s121-c6-visit.md` §8 — the platform-manifest mint and 0933's frame
- `design/backend/s121-c4-visit.md` §6 — the construction-side stamp; bundle B5
  also carries the ruled platform-return tag dispatch (§4.3, H8)
- `audits/cranelisp-platform-s117.md` §R1–R5 — the findings this visit closes
