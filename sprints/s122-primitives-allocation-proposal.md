# S122 primitives ownership boundary — approval proposal

2026-09-09; architecture assessment, source read-only. **Approved by the user on 2026-09-10; implementation pending.** No tests, production source edits, baseline generation or external service calls.

## Decision

The user approved one coherent private ownership-boundary amendment covering construction, traversal and transfer: (1) one primitives adapter adopts produced reference obligations and the existing error sentinel through existing `Owned::from_abi`; (2) one private field projection uses existing `Borrowed::from_abi` and preserves the parent borrow lifetime; (3) existing `Owned::into_raw` transfers typed children at the named ADT and String-Vec storage boundaries below. All three have explicit function-scoped bounds. This is an **architecture amendment to the closed mint-site contract**, not routine propagation and not a new public API. Approval under METHOD §1.3 authorizes propagation into the shared guard/design contract. The approved nine consuming signatures and all eight handle operations remain unchanged; their original approvals do not need repeating.

The missing case is ownership arriving from a Rust allocation/construction API, not an absence of allocation authority or a need for another runtime allocator. The current APIs already transfer a fresh counted owner to their caller. The wrapper records that owner in the approved representation without incrementing RC, copying the reference, or changing layout.

## Source and authority at the proposal checkpoint

- Archived S121 approval (2026-09-05, IO teardown/platform packet) covers the closed `Owned`/`Borrowed` vocabulary and nine typed consuming functions. Shared design §4.1 explicitly requires private heap-result bodies such as `str_concat` to return `Owned`.
- [The trusted base](../design/runtime/s119-typed-consume-funnel.md#3-the-trusted-base-counted) prohibits `Owned::from_abi`/`Borrowed::from_abi` outside the listed entry/owner seams. It expressly makes widening that set visible to architecture; primitive fresh-construction sites are absent. §2 calls `from_abi` the shim's incoming-reference assertion. No existing approved exception was located for primitive allocation results.
- `crates/cranelisp-intrinsics/src/alloc.rs::alloc_with_rc(usize) -> *mut u8` returns a base pointer with RC initialized to 1. It initializes the allocation header, not the caller's typed payload.
- `crates/cranelisp-intrinsics/src/heap_string.rs::alloc_string(&[u8]) -> *mut u8` initializes the String length/data and returns its fresh RC=1 allocation.
- `crates/cranelisp-intrinsics/src/vec_runtime.rs::vec_strings_from_owned(Vec<i64>) -> i64` takes ownership of all element references at call entry, guards incomplete construction and returns a live Vec owning them. Its existing safety contract includes the unwind case.
- `Owned`'s field is private; `from_abi` is the existing raw-to-owner constructor. `as_borrowed` requires an owner already, and `Borrowed::to_owned` increments RC, so neither solves adoption of the initial reference. An extra inc would manufacture an unbalanced second owner. The generated return shim expects an `Owned` body result; it cannot postpone adoption until after the body returns raw without weakening the approved body-signature contract.

## Exact proposed bounds

Proposed: one `pub(crate) unsafe fn adopt_produced_value(raw: i64) -> Owned` in the already-planned `crates/cranelisp-primitives/src/abi_facts.rs`, beside `AbiHandle`; no new module is introduced solely for the adapter. It calls `Owned::from_abi(raw)` exactly once and does no allocation, retain, release, layout access or validation scan.

Caller obligations:

1. `raw` is (a) a fully initialized fresh value whose initial counted reference the caller owns, produced using the three existing constructors above; (b) a canonical produced nullary `None` or `SNil`; or (c) the existing `quote_sexp_build` error branch’s `0`, only after its call to `runtime_panic`. Case (c) carries the existing no-reference error sentinel through the typed ownership boundary; it is **not** a valid initialized Sexp. No arbitrary scalar or address below the nullary threshold is admitted.
2. The obligation has not already been wrapped, moved into a parent/container, returned, or consumed. Adoption occurs once before further typed use/transfer. Shared pointers read from an existing structure and values read from a borrowed parameter are not fresh-result inputs to this helper.
3. For raw ADT allocation, tag/payload initialization finishes before the fully initialized value is adopted. The narrow pre-adoption initialization sequence must not acquire a new fallible operation without the existing owner/cleanup design accounting for it. The helper is not an automatic destructor for partially initialized memory.
4. Nullary construction and the named error sentinel use the existing nullary-safe ownership representation. `runtime_panic` currently sets the runtime error slot and returns `()`; it is not diverging. Keep its error/sentinel behavior rather than replacing the branch with `unreachable!`, an invented valid Sexp, or a new error protocol. No new handle method, public tag constructor or broad scalar-to-owner license.
5. Fresh intermediate children are ownership-bearing values too. Their later transfer into a parent or the existing Vec constructor must discharge the local typed obligation exactly once through the already-approved raw-transfer operation. This amendment does not authorize arbitrary `into_raw`/re-adoption pairs that erase ownership tracking.

Extend the guard in two layers: permit the one `Owned::from_abi` call in the named private adapter, and constrain adapter calls to the named construction seams. A whole-file or whole-primitives-directory exemption is insufficient. The guard must detect a newly introduced bypass or caller outside that set. Its claim is syntactic containment; the safety of the permitted sites depends on their actual allocation/initialization/transfer contracts and executing module evidence. One wrapper does not make the permitted raw-word provenance decisions structurally safe.

## Current producer census and consumer consequences

The current non-test source contains 19 allocation/construction calls. The final designer/arch post-conversion census is **19 functions / 20 syntactic adoption sites**. It includes the nullary results and existing error sentinel, consolidates `str_char_at`’s three allocation arms before one adoption, and names the Vec receiving helper separately. This supersedes the preliminary 17-function/19-site list, which omitted that receiver separation and error branch:

| Source | Producer functions / relevant branch |
|---|---|
| `crates/cranelisp-primitives/src/int.rs` | `int_to_string` (1); `parse_int` fresh `Some` and nullary `None` (2) |
| `crates/cranelisp-primitives/src/bool.rs` | `bool_to_string` (1) |
| `crates/cranelisp-primitives/src/float.rs` | `float_to_string` (1) |
| `crates/cranelisp-primitives/src/string.rs` | `str_concat`, `str_substring`, `str_char_at` (one adoption after three allocation arms), `str_split` (element String: 1), proposed `vec_strings_from_owned_handles` (completed Vec: 1), `str_join`, `str_replace`, `str_trim`, `str_to_upper`, `str_to_lower` (10 total) |
| `crates/cranelisp-primitives/src/marshal.rs` | `alloc_adt_2`, `alloc_adt_3`, `alloc_runtime_string`, `build_runtime_list` initial `SNil`, `quote_sexp_build` existing post-`runtime_panic` error sentinel (5 total) |

The constructor-call count and proposed adoption count measure different things; they are not interchangeable evidence. The proposed function/site set is the initial reviewable allow-list, not a demand to preserve duplicated branches. If design consolidates constructors, the guard follows the resulting exact owned construction seams and the old mint sites disappear. Do not add `sconcat`'s shared-tail branch to a produced-owner allow-list: that path must use its actual existing-reference retain/transfer protocol. Likewise `quote_sexp` reuses some child references; they are not fresh merely because the enclosing output is newly allocated.

Primitives design must cover bool/float heap-result bodies in addition to the earlier int/string/marshal consuming-call census. Intrinsics producer signatures do not change; shared design and its intrinsics-owned guard must accept the approved private primitives seam. The Binary/int macro-host exception and backend fixture remain separate already-approved consumers. No new Cargo edge, public item, generated-baseline row, C ABI, platform ABI, cache schema, heap layout or language behavior follows from this proposal.

## Borrowed child projection

The approved private `read_slist` target returns `Vec<Borrowed<'_>>`; quote traversal similarly borrows live String/SList fields. Raw field loads therefore need a typed borrow, but the current closed allow-list excludes primitive traversal sites. Adopt this additional private seam in the same amendment:

```rust
unsafe fn borrowed_field<'a>(parent: Borrowed<'a>, offset: usize) -> Borrowed<'a>;
```

It lives in `crates/cranelisp-primitives/src/marshal.rs`. It reads the indicated field of the live parent, calls existing `Borrowed::from_abi` exactly once, and narrows that operation's covariant `'static` result to the parent's `'a`. It neither increments RC nor mints an owner. The unsafe precondition is that the caller has established the parent's layout/tag and that the field is a live reference-bearing child (including a valid nullary SList tail), not a scalar payload or unrelated address.

Only two caller functions, with six syntactic projection sites, are permitted: `read_slist` for SCons head/tail after its non-nullary discrimination, and `quote_sexp_build` for String/SList payload arms after tag classification. The latter covers SexpStr/SexpSym String fields and SexpList/SexpBracket SList fields. Scalar Int/Float/Bool payloads use scalar reads and never enter this helper. `quote_slist` consumes the borrowed elements returned by `read_slist`, not another raw-borrow adapter.

This preserves the parent's borrow lifetime rather than manufacturing an independently storable static borrow at each read. A child that the output reuses acquires its own counted reference with `Borrowed::to_owned` before being stored. The helper's layout and provenance assertion remains trusted; a lifetime brand is not a runtime proof that an arbitrary raw field is a reference. No new public borrowed-field operation or broader raw-borrow permission is introduced.

## Transfer into owned storage

The shared design §2.1/§3 currently describes only ABI return and consume-destructure uses of `into_raw`. Its §10.5 already expects `Owned` fields, but that intent does not supply the missing storage-transfer use class. Approve **storage transfer as a third named use**, confined to these private receiving seams. No new public method or blanket raw escape is authorized.

| Receiving seam | Owner before transfer | Exact transfer point and owner afterwards |
|---|---|---|
| `crates/cranelisp-primitives/src/marshal.rs::alloc_adt_2` | Its typed owned field argument, when the field is reference-bearing; scalar payload stays scalar | Allocate parent and establish tag/layout first. At the owned-field store, consume that field's `Owned` with `into_raw` and write its word into the allocated parent. Complete initialization and adopt the parent before returning; the parent now owns the child reference. |
| `crates/cranelisp-primitives/src/marshal.rs::alloc_adt_3` | Its typed owned field arguments (SCons item and tail in current production use) | Allocate parent and establish tag/layout first. Transfer each owned field at its store, with no intervening operation that can unwind before the remaining stores and parent adoption complete. The initialized parent owns both reference obligations. |
| Proposed `string.rs::vec_strings_from_owned_handles`, called by `str_split` and handing off to existing `vec_strings_from_owned` | Typed owned element Strings held by the caller | Prepare a raw-word Vec with sufficient capacity while elements remain typed. Convert/move each element once into that prepared buffer with `into_raw`, without allocation, callbacks or fallible work during conversion; immediately move the complete buffer into `vec_strings_from_owned`. The existing constructor assumes every element reference at call entry, including on unwind, and returns a completed Vec owner. Adopt that returned owner once. |

ADT transfer is not permission to reinterpret a scalar field as an owner. The private constructor carries that distinction as `StoredField::{Scalar(i64), Owned(Owned)}`: `alloc_adt_2(tag: i64, field: StoredField) -> Owned` writes the scalar arm directly and calls `into_raw` only for the owned arm. `alloc_adt_3(tag: i64, field0: Owned, field1: Owned) -> Owned` receives the two SCons child owners. The private sum is part of this reviewable interior shape; neither field ownership nor scalar status is inferred from numeric magnitude. Reference ownership passes through typed intermediate constructors: `make_sexp_sym`, `build_runtime_list`, `sconcat`, `quote_sexp_build` and `quote_slist` move child owners to `alloc_adt_2`/`alloc_adt_3`; they do not add their own `into_raw` storage sites. `build_runtime_list`'s `SNil` is a typed nullary tail, not a scalar pointer heuristic. The reference-bearing ADT fields are String children of SexpStr/SexpSym, SList children of SexpList/SexpBracket, and SCons head/tail; scalar SexpInt/Float/Bool payloads stay raw scalars. Any additional shape needs explicit constructor/field classification, not admission by address threshold.

For ADT construction, allocate and perform potentially failing preparation before disarming any child. The remaining field writes and parent adoption are a bounded non-unwinding sequence under established valid-layout preconditions. If implementation needs a potentially unwinding step after the first field is transferred, it must first provide cleanup for the partially initialized parent and its transferred children; no such extra operation is implied by this proposal. The final parent cannot be exposed until all required fields are initialized.

Proposed private receiver: `string.rs::vec_strings_from_owned_handles(elements: Vec<Owned>) -> Owned`. `str_split` passes its typed element vector to this function; the raw allocation-to-adoption gap resides here, not in each caller. For Vec construction, raw-buffer preparation cannot consume any element owner. Once the first child is disarmed, sufficient capacity and the absence of user callbacks/fallible operations must make completion-to-call-entry non-unwinding. If that cannot be established in the actual implementation, retain cleanup responsibility through a private guard until the existing constructor takes ownership rather than claiming its call-entry guarantee covers an earlier gap. `Owned`'s debug `Drop` is a leak detector and supplies **no automatic release**; this proposal does not invent general unwind cleanup for every typed temporary.

These sites add no RC increment: storing an already-owned child moves its existing reference obligation. A reused child instead obtains a distinct owner via the existing borrow/retain protocol before transfer. `sconcat`'s shared tail and quote's shared String children must therefore continue to retain once where required; neither uses `adopt_produced_value` to fabricate ownership.

Extend the raw-exit guard to exactly four storage sites in three functions: `marshal::alloc_adt_2` owned arm (1), `marshal::alloc_adt_3` child fields (2), and proposed `string::vec_strings_from_owned_handles` element conversion (1), in addition to its already-approved ABI/discharge uses. Disallow extra raw exits in callers, disarm-and-re-adopt round trips, repeated conversion of the same child, or arbitrary field loads promoted into owners. Gate the adapter and exit sites independently: a legal produced-owner mint does not license an unowned raw-storage gap.

## Evidence and implementation handoff

After approval, primitives design records the named produced-value and borrowed-field helpers, exact allowed mint/borrow/exit sets, and typed transfers into Sexp/SList/Vec construction. Intrinsics design updates the shared guard contract in coordination, not by silently allowing a whole crate. QA checks the allocation-side gap is represented alongside existing consume/shim checks.

Required bounded evidence: String conversion/transformation returns the expected value and balances its one initial reference after typed discharge; initialized ADT `Some` and nullary `None` branches survive the same typed return contract; empty/nonempty String Vec construction transfers children once and retains the current unwind cleanup; a constructed macro tree with reused children preserves each child's distinct retain obligation. Existing module tests should be adapted where they already discriminate these cases rather than duplicated. The structural guard needs prohibited-mint/caller, prohibited child-borrow caller, and prohibited raw-storage-exit plants that fail for their intended rules, plus valid controls. The existing quote error path must retain its runtime-error observation and no-reference sentinel; do not grade that word as a successful Sexp result. Borrowed-child evidence preserves the parent lifetime and pins retain-before-store for reused children. Child-storage evidence observes no premature disposal while the parent is live and exactly one child discharge when that owner is released. Vec evidence retains the existing constructor-unwind witness and checks the new caller handoff boundary independently. No deliberate double-adoption UAF execution is needed to prove a source allow-list.

Public baseline verification still covers the original approved handle/funnel migration and later user confirmation; this private amendment adds zero rows. The helper must not be promoted to public visibility as an implementation convenience.

## Alternatives not selected for S122

- **Change/add public allocation-to-Owned APIs:** tracked for future sprint scoping in [ACT-0959](actions/ACT-0959-public-allocation-api-redesign.md); potentially a stronger eventual boundary, but unnecessary for these existing private consumers and would expand the exact API/consumer migration and approval scope. `alloc_with_rc` also serves raw layout initialization beneath the completed-value boundary, so blindly changing its return type conflates uninitialized allocation with an initialized owned value.
- **Scatter `from_abi` at every fresh result:** can represent the ownership but violates the current explicit guard and makes future scope growth harder to see. The bounded adapter plus caller set keeps that change reviewable; it is not a claim of automatic provenance proof.
- **Hide calls through `AbiHandle::from_abi` or a re-export:** still a raw-owner assertion with the same provenance requirement. It evades the spelling of the guard instead of satisfying its intent.
- **Leave private body results raw and wrap only at the exported return:** contradicts the approved typed-body contract, leaving intermediate ownership invisible. This is a different, narrower implementation proposal, not completion of the approved one.
- **Borrow then `to_owned`, retain extra RC, or revive leaking roots:** adds an owner without accounting for the first, or preserves the defect the migration is meant to close.

Approval recorded: **2026-09-10**. Design(primitives) and design(intrinsics)
propagate this exact amendment into their respective carriers and guard
allocation; arch propagates the private boundary into BC §4b. The full public
allocation API redesign is a separate future action. Implementation phase
approval remains pending.

## Final reconciliation and verification

This proposal incorporates the primitives designer’s complete 19-function/20-adoption-site census, the six field-borrow projections and four storage exits. QA reviewed the evidence conditions as one cohesive D8 bundle: destination readiness before transfer, the existing Vec call-entry/unwind guarantee, reused-child retain/value/balance evidence, prohibited mint/borrow/storage callers with valid controls, and no deliberate double-adoption UAF run. There are no remaining identified construction/traversal/storage cases held for a later partial checkpoint. This is a bounded source/design review, not executing proof; any actual implementation discovery outside the named set returns before broadening it.

Checked the existing allocators, primitive result/traversal constructors, nondiverging runtime-error setter, approved shared handle and shim contracts, and current ownership design. That proposal assessment changed only this carrier. The subsequent user approval authorizes standing-contract propagation; production source, tests and baselines remain pending implementation.

Targeted citation verification: 1 document, 15 citations, 0 findings. `git diff --check -- sprints/s122-primitives-allocation-proposal.md` passed. No test or compiler execution.
