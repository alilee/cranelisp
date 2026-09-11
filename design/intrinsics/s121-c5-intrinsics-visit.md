# Sprint 121 — the C5 intrinsics visit

**Status:** DESIGN — pre-implementation. The single `cranelisp-intrinsics`
design delta for Sprint 121's C5 stream (`sprints/SPRINT.md` §"Coherent work
inside each stream"). One visit, four ordered bundles, one mechanism.

**Scope.** `crates/cranelisp-intrinsics/src` only. C5 is an ordered runtime
pair; the `cranelisp-primitives` half — the declaration table, the extern shim
generator, the `marshal`/`string`/`vec` implementation bodies — is the *next*
design invocation's and is named here only where this crate hands it something.

**Authority.** Elaborates `design/arch/bounded-contexts.md` §4b. Consumes,
without restating: the `Pure` ownership-witness contract
(`design/arch/total-concreteness.md` §3.4 as re-ruled 2026-09-01;
`design/arch/interfaces.md` §"IO Tag Constants"), the C4 emission contract
(`design/backend/s121-c4-visit.md` §6 and handoff H1), the unified symbol
lifecycle (`design/arch/symbol-table-lifecycle.md` §§4.6 and 5.5), the
historical C5 stream allocation in [the S121 lifecycle design at checkpoint
`dc78ddbe`](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/symbol-table-lifecycle.md)
§9, and the
cross-pair typed-handle contract (`design/runtime/s119-typed-consume-funnel.md`,
reconciled to S121 in the same change-set as this document).

**Verified against HEAD `18bca20d`** (working tree carries only `design/`,
`spec/` and `sprints/` edits; no source is modified). Every "landed" and
"absent" claim below was checked in source, and the check is named.

---

## 1. What this visit settles

| # | Obligation | Bundle | Class |
|---|---|---|---|
| 1 | `free_io_node` plus the `Pure` three-state atomic claim on both force and teardown paths; exact-once transfer, error ferry and evidence | **I0a**, **I0b** | live implementation (R1) |
| 2 | Preserve the structured join when a cancelled `Select` loser has an in-flight blocking `Par` bridge; retain prompt poll-only cancellation | **I0b** | live implementation (R2) |
| 3 | `consume_sexp`'s missing `Sexp::Annotated` arm | **I1** | live implementation (a real leak at HEAD) |
| 4 | The typed consume funnel and handle vocabulary — intrinsics half | **I2** | live implementation |
| 5 | `vec-len` de-slot: the intrinsics arm and the import-roster handoff | **I3** | current-state wash + handoff |
| 6 | FIXMEs 0835, 0848 and the 0928 gate records | **I3** | retirement / evidence-only |
| 7 | FIXME 0859 — the intrinsics evidence/oracle half | **I3** | retirement (unexecuted, by user disposition) |

**The one discharge mechanism.** The teardown parts of obligations 1 and 3 are
not two patches. Both node families — `Sexp` and `IO` — are torn down today by
a hand-written tag `match` with a silent `_ =>` catch-all, and the catch-all is *why* tag 7
(`SexpAnnotated`) leaks. §3 designs one structural discharge mechanism and §4
and §5 apply it to the two families. A per-arm leak patch beside a surviving
catch-all is a `/review` reject (§13.2).

### Document map

| Section | Contents |
|---|---|
| §2 | Consumed contracts, and the two source facts that bind the design |
| §3 | **The structural discharge mechanism** — the one thing this visit adds |
| §4 | Bundle I0 — `free_io_node`, R1 atomic claim/discharge and ordering |
| §5 | Bundle I1 — the `Sexp` family, including the `Annotated` arm |
| §6 | Bundle I2 — the typed consume funnel, intrinsics half |
| §7 | Bundle I3 — `vec-len`, evidence, retirement, current-state |
| §8 | Per-filing intrinsics disposition |
| §9 | R1 atomic claim and R2 cancelled-bridge join preservation |
| §10 | Bundles in order; the C4 wave collision, resolved |
| §11 | Source and module-test reservations |
| §12 | Unit-test design (intrinsics tier) |
| §13 | `/review` reject criteria |
| §14 | Public API, schema and ABI effects |
| §15 | Handoffs out; collisions; open and owned elsewhere |

---

## 2. Consumed contracts, and the two source facts that bind this design

### 2.1 Consumed, not restated

- **The `Pure` node is `[header | tag@16 | payload@24 | payload_glue@32]`.** The
  payload stays at **field 0** (offset 24); the witness is **field 1** (offset
  **32**). Backend stamps the canonical `drop<T>` address for a heap payload or
  the sentinel `0` for a non-heap payload, at a closed set of three construction
  sites. Every other IO node is byte-identical.
- **The word is the sole ownership and force state.** After publication its
  three states are `0 = Scalar`, `1 = Claimed`, and every other value =
  `Owned(glue)`. Force and teardown both claim with
  `AtomicI64::swap(1, AcqRel)`; only a force claimant that observes `0` or glue
  may read and transfer field 0, and only teardown observing glue may call it.
  A later force observes `1` and raises the existing runtime error before any
  payload access. There is no plain clear, tag-state owner or side table.
- **C1's unified lifecycle** replaces `PrimitiveBody` / `UserFnState` /
  `CtorState` with one callable machine plus `Realization`. No raw primitive
  slot survives it. This crate holds no symbol table and no slot; the lifecycle
  reaches it only through §7.1.
- **The typed-handle contract** (`Owned`/`Borrowed`, the derived shim fact, the
  counted trusted base) is the cross-pair document. This visit implements its
  intrinsics half and reconciles the document; it does not re-decide it.

### 2.2 Two source facts that bind the design, and are not in any prior record

**Fact A — there are already TWO tag-directed IO teardown tails, not one.**
`drop::consume_io_tree` (`drop.rs:354-480`) is the transitive one. But
`drop::dec_shallow_io` (`drop.rs:568-632`) — documented as "shallow" — is *also*
a tag walk on its last-ref path: it releases the `EffectPoll` state closure
(`:607-609`) and deep-frees `Par`/`Select` branch containers (`:619-621`) before
its own `dealloc`. So the crate carries two partial walkers over one node
family, with three independent copies of the `4`/`5`/`6` tag literals. Splitting
`consume_io_tree` at the dec without folding `dec_shallow_io`'s tail into the
same walk would ship a *third*. The brief's "no second teardown mechanism is
allowed" is therefore a convergence obligation, not merely a prohibition.

**Fact B — `consume_sexp`'s pre-dec field snapshot is justified by a claim that
is now false.** `drop.rs:226-231` reads field 0 before interpreting the tag, on
the stated grounds that "Every Sexp constructor that is heap-allocated is
unary". `SexpAnnotated` (tag 7, `cranelisp-types/src/marshal.rs:77`) is
`[:Sexp stype :Sexp sform]` — **two** fields
(`cranelisp-typecheck/src/builtins.rs:582`; `src/bootstrap.rs:1294-1325`
panics unless it is a two-field constructor). The unary claim was true when
written and is false at HEAD, and the `_ =>` arm (`drop.rs:252-255`) silently
treats both `Sexp` fields as scalars. That is the leak. The fix is not an arm;
it is removing the premise that made an unconditional pre-dec field-0 read look
sound.

---

## 3. The structural discharge mechanism

> **One walk per node family. Field reads happen under the arm that declares
> them, after the zero-observing dec. The tag decodes once, into a closed
> Rust enum, and the walk over that enum is exhaustive with no catch-all.**

Three properties follow, and they are the whole value:

1. **A new constructor cannot leak silently.** Adding a tag means adding an
   enum variant, and the exhaustive `match` in the walk stops compiling until
   its discharge is declared. Today it means editing nothing and getting a
   scalar read. (Principle 18 — enforce invariants structurally.)
2. **An out-of-bounds field read stops being possible by inattention.** Every
   read is inside the arm whose tag guarantees the field exists. The three
   places that today read a field *before* knowing the tag (`consume_io_tree`'s
   field-0 snapshot, its `tag == IO_TAG_BIND` field-1 guard, `consume_sexp`'s
   field-0 snapshot) all disappear. Reading after the dec is sound and is
   exactly the precondition `free_io_node` already states: the caller observed
   the count reach zero and fenced; the dec does not free, so the node is still
   allocated and solely owned.
3. **The raw→typed transition has one home.** The walk reads `i64` field words
   and must hand them to a `consume_*` that (post-I2) takes `Owned`. That is a
   genuine transfer — the node is being destroyed and its fields' references
   transfer to this frame — and it is the only construction of `Owned` in the
   crate outside the enumerated ABI shims. Confining it to the dispatcher keeps
   the §6.2 trusted base countable.

### 3.1 Shape

Three collaborating pieces, per family. Names below are illustrative; `dev`
chooses spellings.

- **A closed tag enum with one fallible decode.** One `i64 → Tag` site per
  family. The `Unknown(i64)` case is a *named* variant handled by exactly one
  arm, not a fall-through. In an ordinary build it discharges no guessed fields
  and still deallocates the outer node. Under the existing
  `CRANELISP_RC_DEC_CHECK` release gate it raises the crate's located seam
  message and hard-fails before deallocation. There is no unconditional debug
  assertion: teardown may follow an already-supervised language error, and a
  second panic across an `extern "C"` boundary would abort an otherwise
  recoverable process.
- **A per-tag declared field-discharge list.** Data, not control flow: for each
  tag, the fields it owns as `(offset, kind)`, where `kind` names *which*
  discharge the field needs (shallow, `SList`, `Sexp`, closure, IO sub-tree, an
  IO branch vector, or "none — scalar"). `Par`'s variadic branch block and
  `Select`'s carrier `Vec` are two declared kinds, not two hand-rolled loops;
  this is where today's `free_io_branches(ptr, tag)` double-dispatch goes.
- **One dispatcher** that reads a declared field and performs its discharge. It
  owns the sole raw→`Owned` mint on the teardown path.

The IO family additionally carries a **disposition** (§4.2) because two callers
reach the same walk with different ownership stories. The `Sexp` family has one
disposition and does not need the parameter.

### 3.2 What this mechanism must NOT become

- Not a cross-crate table. The tag *constants* are `cranelisp-types`' (`Sexp`)
  and `cranelisp-platform`'s (`IO`); the *discharge shape* is this crate's
  (BC §4b invariant 2 — intrinsics owns the runtime heap layout). No new
  published type, no `cranelisp-types` edit.
- Not a header type-word. R15 stands. The only self-describing word in play is
  the one arch already ruled onto `Pure`.
- Not a generic visitor. Two families, two tables, one dispatcher shape. If a
  third family wants it, that is a trigger to generalise, not a reason to
  pre-generalise now (Principle 6).

### 3.3 The honest grade

Exhaustiveness *over the declared enum* is **structural** (grade 1) — a missing
arm does not compile. Completeness *of the enum against the published tag
constants* is **measured** (grade 2): Rust cannot make a `match` on `i64`
exhaustive, so a ninth `Sexp` constructor added in `cranelisp-types` without a
matching variant here would decode as `Unknown`. The falsifier is a unit row
per family asserting the enum covers exactly the published constant set, sitting
beside the constants' own cardinality pins
(`cranelisp-types/src/marshal/tests.rs:63-70`). Stating this split is the point:
the previous record claimed a completeness it did not have.

---

## 4. Bundle I0 — the IO dependency slice

C4's B5 cannot execute without this. It is designed as an early C5 sub-step, per
arch's stated placement, and it lands in **two steps** for a reason that is a
safety property, not a convenience (§4.5).

### 4.1 `free_io_node` — the single teardown tail

```
free_io_node(p)                       # C-ABI, raw i64, no return
    # precondition: the caller has dec'd this node's count to zero and fenced.
    discharge every field p's tag declares  (§3)
    dealloc p
```

It is the tail half of `consume_io_tree`, split at the dec, and it becomes the
**only** place an IO node's fields are released and the only place an IO node is
deallocated. Its three callers:

| Caller | Contributes | Disposition (§4.2) |
|---|---|---|
| `drop::consume_io_tree` | nullary guard, dec, fence | `Structural` |
| `drop::dec_shallow_io` | nullary guard, dec, fence | `SpineTransferred` |
| backend's `drop<IO T>` (emitted) | nullary guard, dec, fence | `Structural` (the ABI entry) |

The emitted call is `call runtime/free_io_node(p)` — an ordinary intrinsic
Import. The ABI entry point takes one argument and is fixed to `Structural`;
the disposition is an in-crate parameter and never crosses the ABI.

**`free_io_node` stays raw.** It is *beneath* the handle abstraction, classified
with `atomic_dec_rc`: its precondition is a count already at zero, and `Owned`
models a live counted reference. This is FIXME 0928 item 4, and it is why the
pair's raw heap-handle declaration count gains exactly one (§6.2).

**`free_io_branches` is absorbed.** Its `(ptr, tag)` double-dispatch becomes two
declared field kinds, and its two call sites plus `dec_shallow_io`'s third
become one dispatcher arm.

### 4.2 The disposition — the caller's ownership story, as a value

`dec_shallow_io`'s contract is today a rustdoc paragraph: *"Fields at offsets
24/32/… must NOT still be owned solely through this pointer — the caller is
asserting that every heap-typed field has already been re-owned elsewhere."*
That assertion becomes a two-variant value the walk consumes (Principle 20).

Across the seven IO tags the two dispositions differ in exactly **two** cells:

| Tag | Owned fields | `Structural` | `SpineTransferred` |
|---|---|---|---|
| `Pure` (0) | payload@24 (state @32) | atomically claim; discharge only an observed `Owned(glue)` (§4.3) | **require `Claimed`**; never call it |
| `Effect` (1) | thunk@24, token@32 | none — neither is a Cranelisp allocation | none |
| `Bind` (2) | inner@24, cont@32 | discharge both | **none** — both transferred to `current` / `cont_stack` |
| `Par` (3) | count@24, branches@32.. | branch block | branch block |
| `EffectPoll` (4) | state closure@24 | closure | closure |
| `Launch` (5) | sub-tree@24, `0` = detached | sub-tree if non-zero | sub-tree if non-zero |
| `Select` (6) | carrier `Vec`@24 | branch vector | branch vector |

Two differing cells out of fourteen is what makes the convergence correct rather
than merely tidy: today the two walkers agree on twelve cells by hand, in three
copies, and the `Launch` cell is only accidentally right in the shallow walker
(it reaches the no-op fall-through and is saved by the §15.5 field-0 sentinel).

**Why the `Pure` cell must differ rather than converge.** `Structural` owns an
unforced node and competes for its one obligation; `SpineTransferred` is reached
after the run lane already won that claim and transferred the payload. The
latter therefore accepts only `Claimed`. Observing `Scalar` or `Owned(glue)`
there is a missing force claim: report it through the existing gated seam and
call nothing, so the failure direction is a leak rather than a second owner or
call. This is the natural home for the check §12 calls **A6**.

### 4.3 The `Pure` arm, exactly

Under `Structural`, at offset **32** (field 1 — not field 0):

```
old = AtomicI64[p + 32].swap(1, AcqRel)
if old is Owned(glue): call glue(payload)  # payload is the field-0 word
if old is Scalar or Claimed: call nothing
```

`Owned(glue)` carries the canonical `drop<T>` address for the payload's concrete
type — the same glue every other release site calls. `Scalar` is `0`; `Claimed`
is the reserved tombstone `1`, never a callable address. No IO-specific
releaser symbol is minted, and no new release identity is created.

Under `SpineTransferred`: an atomic load must observe `Claimed`. `Scalar` or
`Owned(glue)` means the run lane transferred the payload without first claiming
its obligation. Disposition: located hard-fail under the existing
`CRANELISP_RC_DEC_CHECK` gate plus the always-on debug twin, then **discharge
nothing** (leak, the monotone-safe direction). This observer does not mutate the
state: the run path is the only legitimate claimant before this disposition.

### 4.4 The atomic force claim — one seam, both trampoline bodies (R1)

The run lane claims a `Pure` node with
`AtomicI64::swap(Claimed, AcqRel)` at offset 32 **before** it reads field 0.
The helper is the one run-lane seam used by both trampoline bodies; it returns
the old state only to the winning caller:

- `Scalar` or `Owned(glue)` wins. The caller may then read field 0 and transfer
  that payload onward. The old glue value is not called on the force path; it
  records the obligation that has just moved.
- `Claimed` loses. The caller must not read, return, increment, decrement or
  otherwise touch field 0. It sets `Pure node forced more than once` in the
  existing runtime-error slot. A Rayon worker ferries that error through the
  existing fork/join result message; the reactor-side join re-raises it under
  the established first-error-wins rule.

The claim is tag-guarded before the offset is formed. An `Effect` node's field 1
is its resource token, so an unconditional exchange would be a wild RMW. Backend
pattern reads remain non-transferring and never touch the state word.

**Cleanup on the error path.** A worker or reactor lane that has already
produced fresh trampoline state before observing a duplicate uses the existing
`TrampolineFrame` owner to release that state. The losing claim creates no
payload owner, so cleanup must not include field 0. Any result already accepted
from an earlier winning sibling remains owned by its ordinary join/result
carrier and is discharged by that carrier if the enclosing operation aborts.
The duplicate-force error is not cancellation: it follows the structured
fork/join ferry, then the caller's normal error-abort teardown.

**Ordering and publication.** Construction and platform adoption initialise
the fresh, unpublished word non-atomically to `0` or canonical glue. Every
intrinsics access after publication is atomic. The exchange's Acquire observes
the payload and initial stamp; Release publishes `Claimed` before any later RC
release. Three existing lifetime edges carry that publication to teardown:

1. same-strand program order from claim to fresh-node shallow dec or the
   caller-tree terminal teardown;
2. the Release-dec / Acquire-fence pair when the claiming strand also performs
   the node's last dec; and
3. the structured bridge/join edge for a non-fresh `Par` branch that the worker
   never decs. R2 below repairs the one cancellation path that currently severs
   this third edge.

**Run result semantics.** A successful first force returns the same field-0 word
and preserves the same transfer. The only new result is the ruled runtime error
on a repeated force. Scalar and heap payloads follow the same once-only rule.

### 4.5 Why I0 splits, and the ordering rule that makes the split safe

`Pure` is a **one-field** allocation at HEAD (payload_size 1). Offset 32 is past
the end. So neither the claim nor the discharge can exist before C4's B5 lands
the two-field layout and the stamp — while C4's B5 cannot *execute* without
`free_io_node`. The split resolves it:

- **I0a** — the entry point, the converged walk, the disposition, the catalog
  row. The `Pure` arm is **byte-identical to today**: no field-1 access, no
  discharge. Behaviour across the whole crate is unchanged; the face-4 residual
  is unchanged. This is what unblocks C4's B5.
- **I0b** — the force claim, teardown claim/discharge, R1 observer/evidence and
  R2 join repair, together. Requires the two-field layout to be live at every
  construction site.

> **Ordering rule (safety, not preference): claim and discharge land together.**
>
> - Discharge before claim ⇒ the first forced heap-payload `Pure` is discharged
>   twice.
> - Claim before discharge ⇒ an unforced heap payload is tombstoned and leaked.
>
> Therefore I0b's state constant, force and teardown uses, error ferry, observer
> and evidence land in **one change-set**. No intermediate tree may interpret
> `1` as a callable glue address or `0` as "cleared heap payload".

C4's B5 and C5's I0b occupy the **same retained-reservation braid** (§10),
because the window between them — two-field stamped `Pure` nodes that nobody claims or discharges, with
`drop<IO T>` having already lost its own tag test and payload call — widens the
residual from "nested `Pure` in an unrun `Bind`" to "every `Pure`". Still
leak-only and still safe, but it is an avoidable regression window, and pairing
the two bundles removes it entirely.

---

## 5. Bundle I1 — the `Sexp` family and the `Annotated` arm

The same mechanism, second family. `consume_sexp` becomes: nullary guard, dec,
fence, one exhaustive walk over the closed `Sexp` tag enum, dealloc. The pre-dec
field-0 snapshot and the `_ =>` scalar arm both go.

| Tag | Constructor | Declared owned fields |
|---|---|---|
| 0/1/2 | `SexpInt` / `SexpFloat` / `SexpBool` | none — field 0 is a scalar |
| 3/4 | `SexpStr` / `SexpSym` | field 0: `HeapString`, shallow |
| 5/6 | `SexpList` / `SexpBracket` | field 0: `SList<Sexp>` |
| **7** | **`SexpAnnotated`** | **field 0 (`stype`) and field 1 (`sform`), both `Sexp`** |
| — | `Unknown(n)` | none; located, gated report (§3.1) |

Two notes that are the whole reason this is not a one-line arm:

1. **Field 1 is only readable under the tag-7 arm.** Every other heap `Sexp`
   node is a one-field, 32-byte allocation; reading offset 32 on any of them is
   out of bounds. That is the same hazard the mechanism removes for the IO
   family, and it is why the arm cannot simply be bolted beside the surviving
   pre-dec snapshot.
2. **Both halves are `Sexp`, and either may be a bare nullary tag.** The
   recursion is `consume_sexp` on both; the nullary guard at the head of
   `consume_sexp` already covers the bare-tag case, so no arm-local guard is
   added.

**Is the leak reachable?** Yes. `SexpAnnotated` is minted by the reader's
`:Type <form>` fold (`cranelisp-frontend/src/quasiquote.rs:105-108`) and is
carried through macro expansion, so any annotated form inside quoted/macro
material allocates two `Sexp` sub-references that no owner ever releases. The
per-invocation, macro-path-only, size-linear signature matches the ambient
prelude-load residue whose remaining term FIXME 0889 carries. **This design does
not claim to close 0889** — 0889's central claim is an `src/`-side marshal
boundary and its stream is C6. What it claims is narrower and testable: one
named contributor on the macro path is removed, and if the residue does not move
at all, that is evidence for 0889, not against this fix. `qa` owns the
measurement (§15.1 handoff H5).

---

## 6. Bundle I2 — the typed consume funnel, intrinsics half

The cross-pair contract is `design/runtime/s119-typed-consume-funnel.md`,
reconciled to S121 in this same change-set. This section states only what is
this crate's, and the three places live source falsified the prior record.

### 6.1 Vocabulary and obligations

`Owned` (not `Copy`, not `Clone`, `#[must_use]`, debug drop bomb) and
`Borrowed<'a>` (`Copy`, no discharge operation at all) live in a new `handle`
module, `pub` because tranche A's `consume_*` signatures force it. The closed
operation set is the funnel document's §2.1/§2.2 and is not widened here.

- **`Owned` obligations.** Discharge by consuming, storing into a structure
  whose glue will discharge it, or returning across the ABI shim. The move
  checker enforces "not twice"; the drop bomb reports "not never".
- **`Borrowed` obligations.** Read only. `to_owned()` is the single typed mint
  and delegates to `rc::rc_inc`, which stays the blessed raw mechanism
  (`rc-inc-entry-point.md` is unchanged by this visit).
- **The one honest limit that matters here.** `Borrowed::from_abi` is
  `'static`-branded and therefore unbranded in practice. Only the
  `as_borrowed`-derived form carries the escape check. This is stated in the
  funnel document §10.2 and is not softened.

### 6.2 The trusted base, recounted at S121

The funnel document's §3 count stands with **three corrections**, all found in
live source:

1. **The `mem::forget` gate as written is false at HEAD.** It requires exactly
   one occurrence in `crates/cranelisp-intrinsics/src` outside `*/tests.rs`,
   inside `Owned::into_raw`. There is already one — `reactor.rs:195`, in
   `OwnedCWaker`'s C-waker `wake`, entirely unrelated to heap handles. A gate
   that is red before its subject exists teaches `dev` to relax it, which is how
   a structural guard becomes decoration. Restated as an **enumerated
   allow-list**, the §4.4 pattern: `reactor.rs`'s waker, and `Owned::into_raw`.
   Growing the list is a `/review` reject.
2. **`into_raw` is used for two things, and the record names one.** It is the
   ABI return path *and* the typed→raw destructure each `consume_*` performs
   before handing the raw to `atomic_dec_rc`. Both are the same operation — the
   handle's obligation ends here — but a reader of the one-line description will
   not expect the second, and it is by far the more common use.
3. **The teardown walk needs a raw→`Owned` mint the gate does not allow for.**
   The walk reads `i64` field words off a node it is destroying and must hand
   them to `consume_*`. That is a transfer, and it is neither an ABI entry nor
   an existing enumerated shim. §3.1 confines it to **one site** — the field
   dispatcher — plus **one more** for `consume_vec_with`'s element loop, which
   mints an `Owned` per element for the `fn(Owned)` callback. Both are named in
   the gate; a third is a `/review` reject.

**The resulting base**: 4 definitions in `handle.rs`, 1 generator in the
primitives declaration macro, 6 hand-written intrinsics extern shims that wrap,
and 2 enumerated intrinsics field-mint sites. Thirteen items, all enumerable,
all grep-gated. That is the claim, and it is a narrowing from "every call site in
two crates", not an elimination.

### 6.3 Counts, re-derived at HEAD

| Quantity | Record | HEAD `18bca20d` | Verdict |
|---|---|---|---|
| Syntactic `i64` declaration count (funnel §6.1 command) | 136 at `5520186d` | **136** | unchanged |
| `extern "C" fn` in `cranelisp-intrinsics/src` (ex-tests) | 81 | **81** | unchanged |
| `consume_` tokens: `string.rs` / `marshal.rs` / `int.rs` | 27 / 8 / 1 | **27 / 8 / 1** | unchanged |
| `launch.rs` cross-crate call site (dispensation granted) | `:452` | **`:452`** | unchanged |
| Semantic N_heap after tranche A | 61 | **62** | corrected — `free_io_node` adds one raw declaration (0928 item 4) |

`dev` re-derives all of these in the change-set and records the enumeration, not
the arithmetic. The funnel document's §7 Class-1/2/3 rows cite line numbers that
are **not** re-verified here and must be re-derived rather than trusted; the
*files* are right, the offsets are a year of drift away from being right.

### 6.4 Ordering against I0/I1

I2 lands **after** I0 and I1, not before. I0 and I1 rewrite the exact bodies I2
retypes; retyping first would churn `drop.rs` twice and destroy the funnel
document's own Class-2 "types-only diff" acceptance property for that file.
`free_io_node` is exempt from the flip (§4.1).

---

## 7. Bundle I3 — `vec-len`, evidence, retirement, current-state

### 7.1 `vec-len` — the intrinsics arm

**The whole of it, stated first: this crate holds no `vec-len` body, gains none,
and must not gain a catalog row.** The implementation is
`cranelisp-primitives::vec::vec_len` (`vec.rs:22-25`), a single length-word
load through `cranelisp_intrinsics::vec_runtime::LEN_OFFSET`; `vec_runtime.rs:550-552`
is already an explicit "lives in primitives, no shim here" note, and
`catalog.rs:63-66` / `:310-312` already exclude it from `intrinsics_table()`
by design.

What is genuinely this crate's:

**(a) The declared representation dependency, and it is already grade 1.** The
roster's entry for `vec-len` — under either spelling — is *"the Vec `LEN` word
at a fixed offset for every element type"*. That fact is intrinsics-owned
(`vec_runtime::LEN_OFFSET = 16`) and is already locked by a
`const _: () = assert!(…)` layout pin (crate `CLAUDE.md` §"Heap layout"). The
dependency needs recording in the roster, not building.

**(b) The catalog stays closed against it.** `intrinsics_table()` is 37 entries
with a closed-set guard (`catalog/tests.rs:59
name_set_is_exactly_the_expected_37`). I0a takes it to 38 with
`runtime/free_io_node`. `vec-len` joins under **neither** spelling: as an inline
primitive it has no runtime target, and as a by-name callable its body is in
`cranelisp-primitives`, which is not this catalog's crate. A `vec-len` row in
`intrinsics_table()` is a `/review` reject (§13.7).

**(c) The spelling itself is NOT this invocation's to choose, and the choice is
narrower than the records suggest.** Arch's recorded preference is (a)
reclassify inline (`total-concreteness.md` §3.2 as amended;
`symbol-table-lifecycle.md` §5.5 — "it re-kinds to `Inline` per the 0932
preference, or to a uniform-body template"). Three source facts the primitives
pass needs, which no current record carries:

1. The **inline emission already exists and is already the live applied-call
   path**: `vec_codegen.rs:435-438` loads the length word, dispatched from
   `apply.rs:630-643` via the name-keyed `is_vec_primitive`
   (`apply.rs:2580-2582`). At ordinary call sites the extern shim and its GOT
   slot are already dead. Spelling (a) is mostly deletion.
2. The slot is load-bearing in **value position only**, and there the design
   record is wrong. `__inlwrap` is not a source name; the live family is
   `__wrap_{name}_…__` (`fn_as_value.rs:157-162`), and `vec-len` is
   **explicitly excluded** from its inline arm (`fn_as_value.rs:583-596`) —
   it takes the GOT arm at `:598-627`. So "value-position use rides the
   existing wrapper family" is false at HEAD.
3. That objection is **already dissolved by the approved lifecycle**, which is
   why it is a note and not a blocker: under `symbol-table-lifecycle.md` §5.5
   an inline primitive's value position rides *minted `Concrete { minted_from }`
   instances* through the ordinary §5.2 machinery, not the backend's bespoke
   wrapper path. The work item is C1/C3 mint machinery plus C4's `Realization`
   consumption, both already scoped — not a `fn_as_value` special case, which
   C4's closed visit did not reserve.

Recommendation carried to the primitives pass: **spelling (a)**, on the strength
of (1) and (3). Its falsifier is (3) — if the C1/C3 mint does not in fact serve
an `Inline` callable in value position, spelling (a) needs a backend reservation
C4 has already closed, and the choice must go back to `sprint` before C5's
primitives half opens. This is flagged in §15.2.

### 7.2 Evidence and oracle — the intrinsics half of 0859

**Retirement, unexecuted, by user disposition.** `diagnostic-modes.md` §9a
defined the intrinsics half of 0859 as a *use protocol*, not an artifact: the
existing M1/M2/M3 + RC/parity detector surface used as an oracle over isolated
single-declaration mutations, with three binding constraints (no new plant
spelling, no new seam, no new observation surface; the oracle may not run before
the §7 detection proofs land; the experiment protocol is `qa`'s). Live source
confirms it was never instantiated: no 0859 reference exists anywhere in
`crates/cranelisp-intrinsics/` or `tests/*.rs`.

The user's 2026-09-01 disposition — accept R-2 on the existing evidence with the
filed revival trigger — retires the protocol before it runs. §9a is rewritten in
this visit from a scheduled obligation to a closed record naming the disposition
and the revival trigger. **No intrinsics source work, and none owed.** The
revival trigger's home is `tests/plan/PLAN.md` and it is `qa`'s ([outgoing handoffs](#151-handoffs-out), H4);
this design does not duplicate primitives' ownership declarations, which are
complete and unit-pinned in `ownership_facts.rs` and witnessed by the nine
committed cells in `tests/s117_ownership_witnesses.rs`.

### 7.3 Current-state wash

Records this crate's design owns that live source has falsified:

| Record | Falsified by | Action |
|---|---|---|
| `diagnostic-modes.md:338` — "Nothing of §7 exists in source at HEAD — `grep FaultPlant\|test_fault crates/` is empty" | the whole protocol is committed (`diagnostics.rs:295-592`, `alloc.rs:217/265/341`) | rewrite to landed current-state |
| `diagnostic-modes.md:246` — §5 table, A1 row "GAP — no check today" | stale since S113; A1 is armed and triplet-proven (`diagnostics/tests.rs:1198`) | correct the row |
| `diagnostic-modes.md` §10 serial order, steps 1–4 | all landed | mark landed; steps 5–6 retain their state |
| `diagnostic-modes.md` §9a | user disposition (§7.2) | retire to a closed record |
| `intrinsics-table.md` — target-states `pub static INTRINSICS_TABLE` | source landed `pub fn intrinsics_table()` (`catalog.rs:122`), 37 entries, per the S76 `!Sync` ruling recorded at `catalog.rs:24-32` | correct to as-built; add the roster half (§7.1b) |
| crate `CLAUDE.md` §"Debug hooks" — no `free_io_node` / witness row | I0 | `dev`'s, handoff H2 |
| `drop.rs:24` rustdoc — `consume_vec_of_heap` | live names are `consume_vec_with` / `consume_vec_of_string` | `dev`'s, handoff H2 |
| `catalog.rs:310-312` — "`vec-len` … rides the GOT via `PRIMITIVES_TABLE`" | becomes false under spelling (a) | `dev`'s, conditional on §7.1c, handoff H2 |

---

## 8. Per-filing intrinsics disposition

Every C5-allocated filing, classified by its **intrinsics arm** against live
source. "An open filing is not proof that source work remains" — four of the six
have none.

| FIXME | Intrinsics arm | Class | Evidence |
|---|---|---|---|
| **0835** slist/sexp heap corruption | **none** | **retirement** | The W2b ruling itself scoped the change to `marshal.rs` and ruled `consume_slist` correct and unchanged (`s118-structural-embedding-ownership.md` §3). Live `drop.rs:156-197` matches; the RE-2 invariance fence is committed at `drop/tests.rs:486`. All three faces are closed or re-attributed away from this crate: leak fixed in `marshal.rs` (`deep_rc_inc_slist` deleted; only comment references remain), abort re-attributed to `match_codegen::dec_temporary_scrutinee` and fixed, prelude-load face re-attributed to `src/` as FIXME 0889 (C6). All seven cells in `tests/slist_sconcat_ownership_0835.rs` are green, none ignored. The file's `status: open`, its `refers_to` pointing at the deleted `deep_rc_inc_slist`, and its dead pointer to a non-existent successor are documentary residue. |
| **0848** diagnostic-mode detection proofs | **none** | **retirement** | All four clauses landed at S118 W2a. Hook: `diagnostics.rs:514` (`test_fault_event`) at the two production funnels `alloc.rs:217/265/341`. Plants: eight spellings (`diagnostics.rs:317-331`). Triplets: eight positive rows at `diagnostics/tests.rs:1032/1075/1114/1157/1198/1240/1281/1323`, each with a clean control and a detector-off negative leg. Fail-on-revert: per-row prose plus seven recorded revert experiments. E2e M3 counter→atexit→abort: `tests/intrinsics_m3_detection_s116.rs:108` with its control at `:140`. None ignored. What remains is the §7.3 wash. |
| **0857** regrade R8 | **evidence-only, and not this crate's** | **handoff** | Its precondition (0848's proofs) is met. The regrade edits `design/arch/safety-invariants.md` R8 (arch-owned) and repairs dead citations in `tests/plan/s115-instrumentation-matrix.md:55/:183` (qa-owned). This visit supplies the evidence index (§8 row above) and the two honesty limits source records: the M3 over-free row grades as report-polarity plus atexit wiring, not double-free (`diagnostics.rs:388-393`); A2/A3/A4's release face grades as header *plausibility*, not proof of basehood (`diagnostics.rs:160-176`). 0857 is a G0 allocation, not C5's — named here because C5 owns the evidence it consumes. |
| **0859** ownership facts vs production witnesses | **evidence-only → retired unexecuted** | **retirement** | §7.2. |
| **0928** S119 gate outcomes | **current-state, absorbed** | **current-state wash** | All four items absorbed into the funnel document in this change-set: `ElemConsumeFn` spelled `fn(Owned)` inline and never `pub` (the live private alias is `drop.rs:269`); the debug-profile-conditional `Drop` is accepted in the baseline; the `launch.rs:452` dispensation is confirmed still exact at HEAD; `free_io_node` joins the deliberately-not-flipped residue and the count becomes 103 + 1 − 42 = 62 with the named exclusion. |
| **0932** `vec-len` de-slot + roster pin | **partial — records and a constraint** | **current-state + handoff** | §7.1. No intrinsics source work; the catalog exclusion is pinned, the representation dependency is recorded, the spelling and the roster-membership cell go to the primitives pass and `qa`. The roster-membership pin **does not exist** in source today (the commit cited as landing it shipped only plan prose), so the silent-fifth-member hazard is live and undefended. |
| **0934** `Pure` payload glue | **live implementation** | **I0** | §4. |

---

## 9. R1 and R2 — force ownership and the cancellation join

### 9.1 R1 observer and evidence

The architecture now rules the three-state word and the always-on refusal;
there is no residual to classify and no tombstone alternative left open. The
diagnostic observer records **successful run-lane claims**, keyed by node
pointer and strand id. A second successful transition for one pointer is the
old mechanism fault; a losing `Claimed` observation is the expected new
refusal and is recorded separately so evidence cannot confuse "the second
force was rejected" with "two transfers succeeded".

`tests/plan/s121-test-plan.md` §3.1 predates the ruling and calls this a
"second clear" observer. Its evidence identity survives only as **a second
successful ownership transition**; no production clear/store remains. QA owns
that wording repair and must not reintroduce the plain-clear mechanism while
preserving the allocated plant, equal-distinct, single-lane and unarmed legs.

The planted positive bypasses or reverts the atomic exchange and presents the
same counted node reference on two lanes; two equal-but-distinct nodes prove
identity keying, and single-lane plus unarmed runs prove silence. Production
acceptance observes one successful claim, the losing runtime error before any
second field-0 read, one payload transfer and one payload discharge. The unit
plant retains two counted references to the shared node; it must not fake the
case by handing one counted reference to two teardown owners.

### 9.2 R2 source finding and owner

The cancelled-`Select` defect is the one broken edge §4.4 names. At HEAD,
`run_blocking_branch` increments `ReactorEnv.pending_bridges`, spawns a Rayon
worker, and owns the only `oneshot::Receiver`; the decrement is after
`rx.await`. Dropping the loser drops that receiver and permit, but the worker
continues its non-consuming walk and the decrement never executes.
`block_on_reactor` treats a positive count as armed yet its successful return
gate checks only top completion plus an empty supervisor. It can therefore
return to `cranelisp_run_io`, which consumes the caller tree while the worker
still reads it. The supervisor is deliberately not the owner: this is a
structured child of a cancelled branch, not a detached strand.

The owner already exists: **the caller-tree reference held across
`cranelisp_run_io` → `drive_io` → `block_on_reactor`**. R2 preserves that owner
until every bridge child acknowledges exit. It does not increment the branch,
move a branch out of the `Select` carrier, or add a side table of heap owners.
This is Principle 22's named retention owner applied to the worker publication;
the bridge lease is the function that keeps that owner live, not another owner.

### 9.3 The one bridge-lifetime mechanism

Strengthen the existing `pending_bridges` lifecycle from a reactor-thread
`Cell<usize>` into one shared join state with a worker-owned RAII lease. The
concrete shape is:

- `BridgeJoinState`, created once beside the executor waker in
  `block_on_reactor_capped`, owns an `AtomicUsize` live count and a clone of the
  existing cross-thread `mio::Waker`; `ReactorEnv` carries the same
  `Arc<BridgeJoinState>` to every blocking spawn;
- each spawn creates one `BridgeTicket` containing an `AtomicBool cancelled`
  and that shared join state. `WorkerBridgeLease` is the ticket's **only strong
  `Arc` owner** and moves into the Rayon closure; after admission, the branch
  future's armed `CancelBridgeGuard` holds only a `Weak<BridgeTicket>` and owns
  the acquired `Permit`, beside the `oneshot` receiver. A weak guard can request
  cancellation but cannot retain a completed worker or become a second tree
  owner; and
- normal receipt disarms `CancelBridgeGuard`, then releases its permit at the
  existing point after the error ferry. Dropping it while armed first upgrades
  the weak ticket, if the worker still exists, and stores `cancelled = true`
  with Release ordering, then drops its permit. Cancellation before admission
  has no ticket and remains `AcquirePermit`'s existing stale-waiter removal
  path. `WorkerBridgeLease::drop` decrements the live count with AcqRel, rejects
  an old zero as an invariant failure, and wakes through the existing bridge
  waker. The executor's armedness, backstop and return decisions read the live
  count with Acquire ordering.

There is no surviving reactor-thread counter beside this state and no second
completion waker. The `oneshot` remains the value/error carrier; the join state
is the lifetime acknowledgement when that carrier's receiver has disappeared.

1. Before `rayon::spawn`, create the ticket/lease and increment the join state.
   The worker closure, not the awaiting future, owns that lease. A panic while
   handing the closure to Rayon drops the captured lease; worker unwind does
   the same, so neither can leave an unowned positive count.
2. The reactor-side branch future keeps the existing receiver and guard. Its
   post-admission cancellation drop marks the ticket first, then releases the
   permit immediately; it does **not** release the worker lease. A pre-admission
   drop still removes the parked acquire waiter, and the poll-shaped path still
   releases its permit and reactor interest through `EffectPoll`. This preserves
   the specified drop-cancellation resource policy while closing the
   tree-lifetime hole.
3. The sync trampoline takes a borrowed cancellation probe from the lease and
   checks it with Acquire ordering before dispatching each node and immediately
   before invoking a continuation. It threads the **same probe** through nested
   sync `Par` work, including serial groups; it does not mint child tickets for
   Rayon joins that are already lexically nested beneath this worker. A call
   already entered at cancellation may return — it cannot be pre-empted — but
   its value is disposed through the branch's carried result authority and the worker starts no later IO node or
   continuation. `TrampolineFrame` extends to this cancellation exit so fresh
   in-flight state and fresh continuations are discharged, while caller-tree
   nodes remain with the root owner. This is the existing policy: invoking the
   call is the already-performed effect and is not rolled back; no later effect,
   completion value or fault reaches the cancelling context.
4. On normal or runtime-error completion the worker takes and clears its
   thread-local error slot, then sends only if the probe is still live. On a
   cancelled path it disposes the value, then clears and suppresses the error. Sender loss is
   harmless; worker unwind still drops the lease. Every lease drop performs the
   release half of the join-state transition and wakes the executor even when
   the `oneshot` receiver no longer exists.
5. `block_on_reactor` reads the join state with the acquire half and may return
   a completed top result only when the supervisor is empty **and the bridge
   join state is empty**. Only then may `cranelisp_run_io` call
   `consume_io_tree` on the caller tree.

This is one mechanism, not a counter plus a retention pool: the same join state
drives armedness, the OneShot bridge hold-off, normal completion, cancellation
retention and the return gate. A nested blocking `Par` is covered transitively:
its synchronous inner Rayon join completes before the outer worker drops its
lease. The worker→reactor release/acquire edge is also the publication edge for
R1's `Claimed` state.

### 9.4 Cleanup order, boundedness and failure direction

The required order is:

`cancel loser → mark cancelled → release reactor resources → worker stops at
its next trampoline boundary → any produced result is disposed and its error is suppressed → worker
lease drops and wakes → executor observes zero joins → caller-tree teardown`.

The bridge state retains no completed history and allocates one fixed-size
lease per spawned blocking branch. Its live size is therefore exactly
`O(in-flight blocking bridges)`, bounded by the finite branch population of the
live IO trees (and, for non-zero resource tokens, tightened by the existing
admission permits); cancellation cannot grow it after the loser is marked
because that worker begins no new node. Poll-only losers allocate no
lease and preserve their current prompt drop path. A blocking foreign call is
not pre-emptible and is already deliberately uncapped by the reactor; R2 does
not claim a wall-clock bound on that call. The bounded guarantee is structural:
after cancellation only the already-entered call may finish, then one
acknowledgement releases one lease. The QA barrier releases that call
deterministically, so the acceptance cell has no timing oracle.

If accounting disagrees, retain rather than tear down: an underflow or a return
attempt with a live worker is a located invariant failure, and the caller tree
stays live. A cancelled worker's runtime error is cleared and suppressed (the
spec says cancellation is not a fault); a non-cancelled worker's error still
uses the existing fork/join ferry. A worker panic still drops its lease, so it
cannot strand the executor or license early teardown.

### 9.5 R2 evidence and controls

The unit observer is an ordered bridge lifecycle, not elapsed time:
`Spawned → CancelRequested → WorkerExited → RootTeardown`. Hold the worker after
spawn, select a sibling winner, and assert both that the join state remains
non-empty and that `RootTeardown` is absent. Release the barrier, observe
`WorkerExited`, then exactly one root teardown. The planted negative releases
the lease at future-drop (the HEAD mechanism) and must trip the
teardown-before-worker-exit assertion; the clean leg must stay silent.

Acceptance is the QA-plan triplet: the held-worker `Select` loser, the same
blocking `Par` without cancellation, and the poll-only cancellation control.
The first observes winner-only value/fault behaviour, no post-cancel completion
side-effect, worker acknowledgement before teardown, and heap/resource counts
back at baseline. The second proves ordinary `Par` still joins both workers.
The third proves R2 did not serialize or delay the existing prompt poll path.

### 9.6 Result-handoff ownership carrier

R2's join keeps the caller tree live, but that tree does not own a value already
returned by an entered foreign call. The runtime therefore carries disposal
authority on result-handoff edges, not on platform `Effect` nodes:

- `Bind` carries the disposer for the value its inner `IO a` hands to the
  continuation;
- `Par` carries one disposer beside each branch pointer, and its result buffer
  owns every initialized slot until the buffer is transferred;
- `Select` carries the common branch-result disposer, used only for cancelled
  losers; and
- `Launch` carries the detached subtree's result disposer because the
  supervisor discards that result.

`ProducedValue` represents the only two valid runtime states: armed ownership
after production, and explicit transfer to a continuation or caller. Drop while
armed invokes the carried disposer exactly once. `TrampolineOutcome` keeps
`Completed(value)` distinct from `Stopped`, so cancellation or fault sentinels
cannot acquire disposal authority. A blocking call already entered at
cancellation remains non-interruptible; if it returns later, the worker disposes
its result before acknowledging exit.

This is a private backend↔intrinsics layout amendment. It does not change
`CLIO`, `Effect`, `cranelisp_run_io`, `ABI_VERSION = 10`, any public Rust item,
or the platform interface. The disposer words are non-owning function addresses,
so `consume_io_tree` skips them while continuing to reclaim each node's authored
heap fields.

---

## 10. Bundles in order

Dependency order, not size. Each is a reviewable change-set.

| # | Bundle | Depends on | Closes | Behaviour class |
|---|---|---|---|---|
| **I0a** | `free_io_node`, the converged walk + disposition, `free_io_branches` absorbed, catalog 37→38 | — (opens C5) | — (unblocks C4 B5) | **behaviour-identical**; `Pure` arm byte-identical to today |
| **I0b** | R1's `Pure` atomic force/teardown claim + discharge + error ferry + observer; R2's bridge lease, return gate and result-handoff ownership carrier | I0a; **C4 B5's layout + stamp**; C7's `ABI_VERSION` 9→10 | 0934 intrinsics half; R1 and R2 prerequisites | first force transfers once; repeat force refuses; cancelled blocking loser disposes any late value and joins before tree teardown |
| **I1** | The `Sexp` family on the same mechanism; the `Annotated` arm | I0a (the mechanism) | the tag-7 leak | leak removed on the macro path; no other behaviour change |
| **I2** | The typed funnel, intrinsics half: `handle` module + its detection triplet, then the A1 signature flip and its in-crate call sites | I0a, I0b, I1; **not** in a wave with C4's bundles | S119 tranche A intrinsics half; 0928 items 1–3 | behaviour-identical; signatures only |
| **I3** | `vec-len` records + roster handoff; 0835/0848/0859/0928 dispositions; §7.3 current-state wash | all | 0835, 0848, 0859, 0928 deletions; 0932 intrinsics arm | no behaviour |

**The W3 braid, consumed exactly.** `tests/plan/s121-test-plan.md` §4 is the
ordering authority. This one C5 reservation pauses and resumes; it is never
released and reopened:

1. Land I0a, then pause C5 while C7 stages the ABI-10 node and C4 completes B5
   against that widened layout.
2. After C7 closes its fixtures, resume the same C5 visit for **I0b and I1**.
   I0b lands R1 claim+discharge+observer/evidence and R2 join preservation as
   one change-set; run the R1/R2, R4 and IO/Sexp acceptance set. Keep the C5
   reservation.
3. After primitives P0 opens and C4 is no longer active, finish I2, then I3,
   and close the retained reservation with the coherent runtime-pair signature
   cut.

No `Pure` fixture executes between the C4 stamp and I0b, and no warm cache is
captured in W3. If the workflow cannot retain this reservation across pauses,
W3 stays blocked; neither a second C5 visit nor an unsafe intermediate run is a
fallback.

---

## 11. Source and module-test reservations

**Writable by C5-intrinsics**: `crates/cranelisp-intrinsics/src/` (whole tree).

**Reserved elsewhere, named so they are not touched:**

| Path | Owner |
|---|---|
| `crates/cranelisp-primitives/src/` | C5's *primitives* invocation (the next design pass, then `dev`) |
| `crates/cranelisp-backend/src/` | C4 — **except** the granted one-line dispensation at `compiler/control_flow/launch.rs:452` (the `unsafe { Owned::from_abi(cont_ptr) }` wrap inside that file's `#[cfg(test)] mod tests`, inside I2's change-set; that call expression only, assertions byte-identical) |
| `crates/cranelisp-platform/` incl. `ABI_VERSION` | C7 |
| `crates/cranelisp-types/` | C1 |
| `src/` | C6 |
| `tests/`, `tests/plan/` | `test` / `qa` |
| `design/arch/`, `design/backend/`, `design/primitives/`, and (as reserved at S121) the pre-Decision-43 combined-runtime record, retired at S122 | their owners |
| `design/arch/fixmes/` | owning roles delete |

**Design documents this invocation writes**: this file;
`design/runtime/s119-typed-consume-funnel.md` (the one cross-pair file, held by
the intrinsics pass so the two crate passes do not both rewrite it — the
primitives pass **consumes it without editing**);
`design/intrinsics/diagnostic-modes.md`; `design/intrinsics/intrinsics-table.md`;
`design/intrinsics/CLAUDE.md`.

**Module-test reservations**, per submodule, per the crate's externalized-tests
convention (crate `CLAUDE.md` §"Submodule seam map"):

| Submodule | Test module | Bundle |
|---|---|---|
| `drop` | `drop/tests.rs` — the walk, the disposition matrix, both `Sexp` and `IO` tables; `drop/rc_balance.rs` — the balance rows | I0a, I0b, I1, I2 |
| `io` | `io/tests.rs` — R1 claim/error/ferry; R2 held-worker cancellation boundary, explicit transfer/drop states, Par slot disposal and late blocking-result disposal | I0b |
| `reactor` | `reactor/tests.rs` — bridge lease, wake, return gate and lifecycle plant | I0b |
| `catalog` | `catalog/tests.rs` — the closed name set 37→38; `vec-len` still absent | I0a |
| `handle` (new) | `handle/tests.rs` — the drop-bomb triplet | I2 |
| `rc` | `rc/tests.rs` — the Class-3 re-expressions | I2 |
| `diagnostics` | `diagnostics/tests.rs` — A6 plus the R1 successful-claim observer and detection proof | I0b |

---

## 12. Unit-test design (intrinsics tier)

`dev` owns every row. E2e acceptance is `qa`'s.

| Submodule | Positive | Edge | Negative |
|---|---|---|---|
| `drop` — the IO walk (§3, §4.1) | each tag's declared fields are discharged exactly once under `Structural`; one dealloc per node | a `Launch` with the `0` sentinel discharges nothing and still deallocs; `Par` count 0; `Select` carrier empty | **no catch-all exists** — an undeclared tag reaches the named `Unknown` arm, is reported under the gate, discharges nothing and still deallocs; **no field is read outside the arm that declares it** |
| `drop` — the disposition (§4.2) | the twelve agreeing cells behave identically under both dispositions | `Bind` under `SpineTransferred` discharges neither field; under `Structural` discharges both | **A6**: `Scalar`/`Owned(glue)` reaching `SpineTransferred` is a located report and discharges **nothing** (leak, not UAF); `Claimed` is the clean leg |
| `drop` — the `Pure` arm (§4.3) | `swap(1, AcqRel)` observing `Owned(glue)` calls it exactly once with field 0, then deallocs | observing `Scalar` or `Claimed` calls nothing | state is at offset **32**, never 24; `1` is never called; concurrent force/teardown yields exactly one winner |
| `drop` — the `Sexp` walk (§5) | tags 3–6 discharge their one field; **tag 7 discharges both `stype` and `sform`** | tag 7 with one or both halves a bare nullary tag; tags 0–2 discharge nothing | field 1 is read **only** under tag 7; balance holds for a nested annotated tree; the enum covers exactly the published `TAG_SEXP_*` set (§3.3's measured leg) |
| `io` — R1 force (§4.4, §9.1) | first force in both trampoline bodies observes `Scalar`/`Owned(glue)`, claims before field-0 read and returns the unchanged value | an `Effect` node's resource token is unchanged; scalar `Pure` is still once-only | second force observes `Claimed`, reads no payload, creates no owner and ferries the existing runtime error from a worker; successful-claim observer plant/clean/unarmed legs all discriminate |
| `io`/`reactor` — R2 (§9.2–§9.6) | a held blocking worker keeps one bridge lease and prevents caller-tree teardown until its exit acknowledgement; produced values remain armed until explicit transfer | non-cancelled blocking `Par` joins normally; poll-only loser allocates no lease and cancels promptly; scalar disposer is inert | early-lease-release plant trips teardown-before-worker-exit; sender loss and worker unwind each release/wake once; cancelled worker error is suppressed and any late owning result is disposed exactly once |
| `catalog` (§7.1b) | the closed name set is exactly 38 and contains `runtime/free_io_node` with arity 1, no return | its pointer is non-null and is `is_runtime` | `vec-len` is **absent**; no second IO teardown name appears |
| `handle` (§6.1) | the drop-bomb triplet: deliberate leak fires with the located prefix; the same fixture discharged is silent **and** balances; a live `Owned` survives an unrelated unwind | — | each leg observed RED against a deliberately broken instrument before the tranche is declared landed |
| `diagnostics` (§9.1) | the observer records one successful claim per node on a healthy corpus | losing `Claimed` is classified separately | bypassing the claim permits two successes and fires; equal-distinct, single-lane and unarmed legs stay silent |

**Balance rows** (`drop/rc_balance.rs`) extend to: an annotated `Sexp` tree, a
`Pure` node with a heap payload torn down structurally, and the same node
transferred then torn down — the second must show the payload released once, not
twice and not zero times.

---

## 13. `/review` reject criteria

1. **A `_ =>` catch-all in either discharge walk.** The exhaustive match over the
   closed enum is the instrument; a catch-all is how the next constructor leaks
   silently, which is exactly what tag 7 did (§2.2 Fact B).
2. **A per-arm leak patch for `SexpAnnotated` beside a surviving catch-all.**
3. **A third IO teardown walker**, or a surviving copy of the `4`/`5`/`6` tag
   literals outside the one decode (§2.2 Fact A).
4. **A second run-lane `Pure` claim mechanism** (§4.4): a plain clear/store,
   side table, tag tombstone or a second atomic helper. Force and teardown use
   the one three-state word and `swap(1, AcqRel)`.
5. **A change-set splitting R1 claim, discharge, error ferry, observer or its
   evidence** (§4.5). Every part lands in I0b.
6. **An unguarded RMW at IO field 1.** An `Effect` node's field 1 is its
   resource token; tag selection precedes forming the `Pure` state address.
7. **A `vec-len` row in `intrinsics_table()`**, under either spelling (§7.1b).
8. **A raw→`Owned` mint outside the two enumerated field-mint sites**, or growth
   of the `mem::forget` allow-list past its two named occurrences (§6.2).
9. **A new operation added to `Owned`/`Borrowed`'s closed set** to make a Class-3
   instrument compile. That is a design gap and returns here, per the funnel
   document §7.
10. **A `cranelisp-types` or `cranelisp-platform` edit from this stream**, or an
    `ABI_VERSION`/`CACHE_SCHEMA_VERSION` touch (§14).
11. **An instrument landed without its detection proof in the same change-set** —
    A6, the R1 successful-claim observer and the R2 bridge lifecycle assertion
    each carry planted and clean legs.
12. **Releasing a bridge at receiver/future drop, or returning from
    `block_on_reactor` with a live bridge.** Either reintroduces the severed
    structured join. Moving cancelled workers into the detached-strand
    supervisor is the same reject under another name.
13. **A retention pool or per-branch RC increment for R2.** The existing caller
    tree is already the owner; the one bridge join state extends its lifetime.

---

## 14. Public API, schema and ABI effects

| Surface | Effect | Owner |
|---|---|---|
| `cranelisp-intrinsics/public-api.txt` | **I0: zero.** `free_io_node`, the R1 claim and the R2 bridge join are crate-interior; the catalog reads the entry pointer in-crate exactly as every other `runtime/*` target does. If `dev` finds a linkage reason it must return here rather than publish silently. **I2: the additive `handle` module plus nine changed public `consume_*`/`dec_shallow_io` signatures**; a tenth changed signature is the private field dispatcher, as enumerated in the funnel document §8 and approved via FIXME 0928. | C5 |
| `cranelisp-primitives/public-api.txt` | **zero**, expected byte-identical. The crate's entire public surface is `PRIMITIVES_TABLE`, `PRIMITIVES_GOT_SLAB` and seven `pub mod`; every shim is `pub(crate)`. | C5 primitives pass |
| `cranelisp-types` | **zero.** The `Sexp` tag constants are read, not changed. | C1 |
| `CACHE_SCHEMA_VERSION` | **untouched.** The single S121 window (24→25) is C1's. | C1 |
| `cranelisp_platform::ABI_VERSION` | **untouched by C5.** The 9→10 bump for the two-field `Pure` is C7's, together with the platform fixture rebuilds — but it **gates I0b**, which cannot land before the version and fixtures agree with the layout. | C7 |
| Emitted-call ABI | **one addition**: `runtime/free_io_node`, arity 1, no return. Every existing intrinsic name and arity is unchanged; the nine public and one private `consume_*`/`dec_shallow_io` signature flips are Rust-side only and every generated shim keeps `extern "C" fn(i64, …) -> i64`. | C5 |

**Baseline regeneration** uses the one canonical command settled this sprint
(`design/arch/CLAUDE.md` §"Baseline-diff discipline", the FIXME-0945
reconciliation), and C5 does not regenerate any baseline before G0 has landed
that procedure repair.

---

## 15. Handoffs, collisions, and what is open

### 15.1 Handoffs out

| # | To | Content |
|---|---|---|
| **H1** | `sprint` | Preserve the QA-plan §4 braid: I0a ahead of C4; resume the same C5 reservation for I0b after C4/C7 make the state word valid; I2 only after C4 is closed. I0b includes R1 and R2 and is not split into another visit. |
| **H2** | `dev`(intrinsics) | Crate `CLAUDE.md` and rustdoc current-state, in the implementing visit: a `free_io_node` + witness row under §"Debug hooks"/§"RC discipline"; `drop.rs:24`'s `consume_vec_of_heap` → the live `consume_vec_with`/`consume_vec_of_string`; `catalog.rs:310-312`'s `vec-len` GOT claim, conditional on §7.1c. |
| **H3** | `design`(primitives) — the next C5 invocation | Consume the reconciled funnel document **without editing it**. Its half: the A2/A3 body flips, the `abi_facts` derivation, the `shim_abi_kinds_match_declared_facts` row with its one-name `sconcat` allow-list, and the `vec-len` spelling with the three source facts at §7.1c. |
| **H4** | `qa` | (a) consume §9.1/§9.5 without strengthening it: R1 successful-claim plant/controls and R2 held-worker/non-cancelled/poll-only triplet; (b) 0859's revival trigger into the [S121 QA allocation](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/tests/plan/PLAN.md), and retirement of the dead conditional rows; (c) 0857's regrade inputs; (d) the face-4 guard as a GREEN acceptance cell with the double-discharge negative. |
| **H5** | `qa` + `test` | The `SexpAnnotated` leak's measurement question (§5): the fix removes one named contributor on the macro path; whether the ambient prelude-load residue moves is evidence *for* FIXME 0889's `src/`-side attribution either way, and must not be read as this fix failing. |
| **H6** | `design`(platform) → C7 | I0b is **gated** on `ABI_VERSION` 9→10 and the fixture rebuilds; the gate is a landing order, not a code dependency. |
| **H7** | `arch` | The result-handoff amendment changes only the private backend↔intrinsics layouts for Bind, Par, Select and Launch. The user approved that standalone wave; it changes no facade, platform ABI, cancellation policy or bounded-context dependency, and its public-api baselines must remain unchanged. |

### 15.2 Blockers

**None hard.** R1 and R2 are now fully designed inside I0b. One unrelated
conditional remains, named so it cannot be discovered late:

- **`vec-len` spelling (a) depends on the C1/C3 mint serving an `Inline`
  callable in value position** (§7.1c fact 3). If it does not, spelling (a)
  needs a `fn_as_value` reservation C4's closed visit did not take, and the
  choice returns to `sprint` before C5's primitives half opens. The check is
  cheap and belongs in C1/C3's own acceptance, not in a later discovery.

### 15.3 Collisions and findings

1. **`Pure` field numbering is reconciled.** The ruling now consistently names
   payload at field 0/offset 24 and state at field 1/offset 32. This visit uses
   the numeric offset at every RMW/call site and carries no field-0 conflict.
2. **The funnel document's `mem::forget` structural gate is false at HEAD**
   (§6.2 item 1). Corrected in the reconciliation; recorded here because a
   structural guard that is red before its subject exists is the failure mode
   the repository's assurance doctrine names.
3. **The cross-strand publication argument now includes cancellation** (§4.4,
   §9.2–§9.4). The Release-dec/Acquire-fence argument covers the fresh path;
   the `Par` branch path is published by the bridge join, which R2 preserves
   even when a `Select` drops the awaiting loser future.
4. **The roster-membership pin does not exist** (§7.1, §8/0932). The commit
   cited as landing "the roster pin cell" touched only a FIXME file and a plan
   document; no `.rs` asserts closure, so a fifth polymorphic by-name callable
   would land green today. The live roster is exactly
   {`bind`, `race`, `select`, `catch-runtime-error`}
   (`src/bootstrap.rs:893/950/958/1151`); `sleep` (`:987`) and `discover-tests`
   (`:1114`) are slot-less but monomorphic and are the two near-misses a naive
   "all `PrimitiveExtern`" enumeration over-collects. The cell's home is
   `src/bootstrap.rs`'s stream, not this crate's; routed via H3 and H4.
5. **`design/CLAUDE.md` calls `design/runtime/` "historical"**, while three live
   cross-pair contracts (S117, S118, S119) are homed there and one is being
   edited this sprint. Outside this invocation's boundary; routed to `sprint`.

### 15.4 Open, and owned elsewhere

- **`Borrowed`'s "cannot be stored" limit** — a `Copy` newtype can always be
  stored in a struct; only the `as_borrowed`-derived brand is enforceable. The
  potential extension is a callback-scoped borrow, on the `with_vec_strings`
  precedent; the trigger is a real storing hazard appearing, which none has.
- **The 81 hand-written intrinsics extern shims are not derived** — six wrap
  after I2; the rest carry their ownership facts as rustdoc. The natural second
  derivation home is `intrinsics_table()`, which is a later tranche and is not
  claimed here.
- **`rc::rc_inc` stays `pub` and raw** — the blessed mechanism;
  `Borrowed::to_owned` becomes its only typed caller. Retiring it to
  `pub(crate)` reaches `io.rs`/`trace.rs` and touches
  `rc-inc-entry-point.md`'s ruling; a later tranche.

**No user-owned, spec or architecture decision remains implicit in this design.**
Every input it consumes was ruled before this window: the `Pure` node layout and
witness semantics, the ABI and schema windows, 0934's inclusion, 0859's
acceptance, and the unified lifecycle target. The two arch-record slips at §15.3
are corrections to already-ruled substance, not new decisions.

---

## 16. Next skills

- **`sprint`** — H1, the wave shape; and §15.3 findings 1, 4 and 5.
- **`arch`** — no return for R1/R2 unless implementation discovers a real
  facade, ABI, node-layout, cancellation-policy or dependency change (H7).
- **`design`(primitives)** — H3, the next C5 invocation.
- **`design`(platform)** — H6, the `ABI_VERSION` 9→10 gate on I0b.
- **`qa`** — H4 and H5.
- **`dev`(intrinsics)** — I0a … I3 in order, each with its §12 rows, its
  declared behaviour class, and (for I0b and §9) its detection proof in the same
  change-set.
