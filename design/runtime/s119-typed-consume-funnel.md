# Typed consume funnel — the runtime-pair handle contract

- **Status:** adopted and delivered. The vocabulary and the nine consuming
  signatures are in the committed
  [intrinsics baseline](../../crates/cranelisp-intrinsics/public-api.txt), whose
  generated diff the user confirmed on 2026-09-11. Primitives, backend and the
  Binary/int surface consume it. Design and delivery history are in Git.
- **Scope:** the runtime pair — `cranelisp-intrinsics` owns the handle
  vocabulary and the discharge funnel; `cranelisp-primitives` owns the extern
  shim generator and the bodies it reaches.
- **Authority:** elaborates `design/arch/bounded-contexts.md` §4a/§4b; sibling
  of `design/runtime/s118-structural-embedding-ownership.md`. Changing the
  closed operation set, the trusted base or a public signature is an `arch`
  change and passes the inter-crate public-API user gate.
- **Interior homes, not restated here:**
  [intrinsics ownership §2](../intrinsics/ownership-and-disposal.md#2-the-typed-handle-vocabulary)
  and [primitives §2.4](../primitives/primitives.md#24-typed-abi-boundary).

---

## 1. The question, and the answer

The pair's heap handles cross the C ABI as raw `i64`. Whether a parameter is
consumed, borrowed or stored would otherwise be prose every caller re-derives.

**Contract: a closed two-type handle vocabulary over the discharge funnel,
with enumerated raw entry and exit sites, and each primitive extern shim's
ownership fact derived from its declaration row rather than re-asserted.**

1. **Double discharge does not compile.** `Owned` is neither `Copy` nor
   `Clone`; passing it to two consumers is a move error.
2. **An abandoned reference is a located failure.** `Owned` is `#[must_use]`
   and, in the debug profile, a drop bomb names the handle at the frame that
   dropped it.
3. **The consuming convention is checked at every call site** by `cargo
   check`, including future ones (Principles 18 and 20).

What this does not buy is stated in §7.

## 2. The vocabulary

`crates/cranelisp-intrinsics/src/handle.rs` is public because the `consume_*`
funnels are public and take these types. Intrinsics is the home because the
discharge behaviour lives there (Principle 15).

### 2.1 `Owned` — a counted reference the holder must discharge

`#[repr(transparent)]` over `i64`, `#[must_use]`, no `Copy`, `Clone` or public
field. The transparent representation keeps it layout-identical to the ABI word
(Principle 14).

The closed operation set is below. Adding an operation is an `arch`-visible
trusted-base change, not a convenience edit.

| Operation | Role |
|---|---|
| `unsafe fn from_abi(raw: i64) -> Owned` | The raw-owner adoption: asserts a transferred ABI reference, a completed produced value or a valid bare nullary tag. Sites are enumerated in §3. |
| `fn into_raw(self) -> i64` | The raw exit, for three use classes (§3). Disarms the bomb. |
| `fn as_borrowed(&self) -> Borrowed<'_>` | Read access branded to this owner's lifetime. |
| `fn raw_for_read(&self) -> i64` | Feeds raw layout accessors; cannot discharge. |
| `fn is_nullary_tag(&self) -> bool` | The single-sourced `< NULLARY_TAG_THRESHOLD` predicate. |

`Drop` exists only under `debug_assertions` and panics with the located
`LEAKED Owned heap handle …` message unless the thread is already panicking.
The `thread::panicking()` clause is load-bearing: without it, an `Owned` alive
during an unrelated unwind turns that unwind into a double-panic abort (§5,
leg 3).

### 2.2 `Borrowed<'a>` — read access with no discharge obligation

A `Copy` transparent `i64` with a lifetime brand.

| Operation | Role |
|---|---|
| `unsafe fn from_abi(raw: i64) -> Borrowed<'static>` | Raw retained-reference assertion; sites are enumerated in §3. |
| `fn to_owned(self) -> Owned` | The single typed mint; delegates to `rc::rc_inc`. |
| `fn raw_for_read(self) -> i64` | Feeds raw layout accessors. |

`Borrowed` has no discharge operation. A `Borrowed` from `as_borrowed` cannot
outlive its `Owned`, which is the hazard that actually occurs (reading a node's
fields across its own decrement). A `from_abi` borrow is `'static`-branded and
therefore unbranded in practice; the private parent-lifetime projections in §3
narrow it immediately.

### 2.3 Why a lifetime brand, not a callback-only borrow

A callback-scoped borrow cannot escape at all, but costs a closure and a
control-flow inversion at every read. It is right for a many-element view —
`vec_runtime::with_vec_strings` keeps that form — and wrong for a single field
read in the middle of a teardown walk. The brand costs one `<'_>` and checks
escape on exactly the reads the funnel performs.

## 3. The trusted base, counted

Rust cannot enforce exactly-once. The contract narrows the trusted base from
every call site in two crates to an enumerable set, and the enumeration is
executable:

- intrinsics:
  `crates/cranelisp-intrinsics/src/handle/tests.rs::typed_handle_trusted_base_matches_the_approved_intrinsics_allow_list`
  pins every `Owned::from_abi`, `Borrowed::from_abi`, parent-borrow projection,
  `.to_owned()` and `mem::forget` site by function and count, and the absence
  of `Clone`/`Copy` on `Owned` and of a public element-callback alias;
- primitives:
  `crates/cranelisp-primitives/src/abi_facts/tests.rs::typed_consume_trusted_base_matches_exact_production_callers`
  pins the shim conversion sites, the three private adapters below, and the
  conversion trait's implementing set (`i64` and `Owned` only). No shim adopts
  a `Borrowed`.

The guards are the authority for exact site sets; the table summarises them.

| Trusted item | Where | Current extent |
|---|---|---|
| Vocabulary definitions: `Owned::from_abi`, `Owned::into_raw`, `Borrowed::from_abi`, debug `Drop` | `handle.rs` | 4 definitions |
| Shim entry/exit conversion, derived per §4 | `crates/cranelisp-primitives/src/declaration_macro.rs` | 1 generator |
| Produced-value adoption | `crates/cranelisp-primitives/src/abi_facts.rs::adopt_produced_value` | 19 functions / 20 sites |
| Parent-lifetime child projection | `crates/cranelisp-primitives/src/marshal.rs::borrowed_field` | 2 functions / 6 sites |
| Owner transfer into raw storage (`into_raw`) | primitives `alloc_adt_2`, `alloc_adt_3`, `vec_strings_from_owned_handles` | 4 sites |
| Teardown field mints | `crates/cranelisp-intrinsics/src/drop.rs` — `owned_field` and `consume_vec_with`'s element loop | 2 sites |
| Intrinsics owner-seam adoptions and the IO parent-borrow projection | `io.rs`, `panic.rs`, `reactor.rs`, `trace.rs`, `vec_runtime.rs` | by function in the intrinsics guard |

**Teardown field mints.** A discharge walk reads field words off a node whose
last reference it is discharging and hands them to a consumer that takes
`Owned`. That is a genuine transfer, but neither an ABI entry nor a shim, so it
is confined to the two `drop.rs` sites above
([ownership/disposal 7](../intrinsics/ownership-and-disposal.md#7-trampoline-ownership-transitions)).
A third `drop.rs` mint is a `/review` reject.

**`into_raw` has three use classes:** ABI return; the typed-to-raw destructure
every `consume_*` performs before the raw decrement (§6); and transfer of a
typed child into an initialised ADT or Vec receiver. All end this frame's
obligation; the storage class is limited to the sites above. Disarm-and-readopt
round trips are a review rejection.

**`mem::forget`** occurs exactly twice in intrinsics production code:
`Owned::into_raw` and `reactor.rs`'s unrelated `OwnedCWaker::wake`, whose
payload `wake` consumes.

**Test instruments get no escape hatch.** A test that deliberately
double-discharges or discharges a stale pointer re-expresses through
`from_abi` (what a stale-pointer plant genuinely is) or through the legal
two-reference form `a.as_borrowed().to_owned()`. A test needing anything else
is a design gap returned to this document, not grounds for a new operation.

**Grade.** Structural for the move checker; measured for the site sets. The
site guards are lexical: they make adoption sites enumerable and detect a
moved adoption, but do not prove the provenance of a permitted raw word or
semantic correctness inside an allowed function (Principle 18).

## 4. The shim-fact derivation

A shim whose token disagreed with its declared type would mis-declare as prose
can. The shim's handle kinds are therefore generated from,
and checked against, the declaration row (Principle 7).

### 4.1 Three statements of one fact

1. **The implementation signature** — for example `fn str_concat(a: Owned, b:
   Owned) -> Owned`. rustc checks it against the body.
2. **The shim tokens** — the Rust types in the row's `shim:` clause. rustc
   checks them against (1) at the macro's call expansion; a compile-fail case
   proves a contradiction is rejected.
3. **The declared Cranelisp type** — tied to (2) by the §4.3 unit.

The rule, in `crates/cranelisp-primitives/src/abi_facts.rs`:

```text
kind(i) = Scalar       if param_type[i] is Int, Bool or Float
        = OwnedHandle  otherwise      // uniform consuming entry, BC §4a invariant 8
```

Neither `Mode` nor `ParamFlow` is an input; the summary is analysis-only.

### 4.2 One token, two manifestations

The generated shim keeps the raw `extern "C" fn(i64, …) -> i64` signature. The
same `$argty` token drives both the entry conversion
(`<$argty as AbiHandle>::from_abi`) and the row's private ABI-kind data
(`<$argty as AbiHandle>::KIND`). There is no second hand-written assertion.

### 4.3 The check

`crates/cranelisp-primitives/src/declarations/tests.rs::shim_abi_kinds_match_declared_facts`
asserts, for every user-callable extern row, that its token-derived kinds equal
those derived from its declared type. To lie at a shim, a row must contradict
its own declaration, and the row fails.

The check is not a tautology. rustc accepts an `i64` token on a String
parameter against an `i64` body, which would silently skip the discharge; the
declared type derives `OwnedHandle`, so the check rejects the row.

No shim token can be `Borrowed`: the conversion trait has no borrowed
implementation ([primitives §2.4](../primitives/primitives.md#24-typed-abi-boundary)).

### 4.4 Coverage and the named exemption

The derivation covers every user-callable primitive row. Harvest-only rows
carry no declared Cranelisp type:

- `neq-i64`, `neq-f64` and `neq-bool` are asserted all-scalar;
- `sconcat`, whose type Binary/int seeds into the synthetic `macros` module, is
  the one exemption. Its kinds are pinned to owned handles in the check and
  tied to its body by rustc.

Any other harvest-only row fails the check, mirroring
`crates/cranelisp-primitives/src/tests.rs::extern_shims_harvest_covers_full_inventory`.
A second exemption is a design decision, not a local edit.

The hand-written intrinsics externs have no declaration table and are outside
this derivation (§7).

## 5. The drop-bomb detection proof

The move checker cannot silently fail — its failure is a build failure — so it
needs no detection proof; §3's guard keeps it from being widened away. The
drop bomb can silently fail (impl removed, `cfg` inverted, the panicking clause
swallowing everything), so it carries a debug-profile triplet in
`crates/cranelisp-intrinsics/src/handle/tests.rs`:

1. **Positive detection** — `leaked_owner_trips_the_debug_drop_bomb`: a real
   `HeapString` wrapped as `Owned` and dropped must panic with the located
   `LEAKED Owned heap handle` prefix.
2. **No false positive** — `consumed_owner_is_silent_and_balanced`: the same
   fixture discharged through `rc::consume_shallow` must not panic and must
   balance allocation against deallocation.
3. **Survivable under an unrelated unwind** —
   `owner_drop_during_unrelated_unwind_does_not_double_panic`: a live `Owned`
   during an unrelated panic must yield that panic's message, not an abort.
   This leg fails on deletion of the panicking clause alone.

A change to the instrument re-arms the triplet against deliberate breakage in
the same change-set: deleting the bomb must fail leg 1, and deleting the
panicking clause must fail leg 3.

## 6. What stays raw

These are beneath or beside the abstraction permanently, not deferred:

- **`drop::free_io_node`** — the zero-count IO teardown tail and target of the
  backend's emitted IO drop. Its precondition is a count already at zero, while
  `Owned` models a live reference. It keeps a raw signature and C-ABI export.
- **`drop::atomic_dec_rc` and `rc::nonatomic_rc_rmw`** — each `consume_*`
  destructures its `Owned` and hands the raw word to the decrement; typing it
  would require an `Owned` to survive its own decrement.
- **The mechanical accessor layer** — `heap_access::{read_i64, write_i64}` and
  the local accessors in primitives `marshal.rs` and intrinsics `trace.rs` take
  a base and an offset, not a handle.
- **`rc::rc_inc`** — the public raw mechanism behind `Borrowed::to_owned`.
  `io.rs` and `trace.rs` still call it directly
  ([ownership/disposal 3](../intrinsics/ownership-and-disposal.md#3-rcinc-the-blessed-inc-entry-point)).
- **Emitted and callback ABIs** — JIT closure calls, poll functions,
  `ResultDisposer` and backend/platform emitted signatures. The typed vocabulary
  stops at the pair's Rust bodies.

## 7. Limits

- **Exactly-once is not enforced.** `mem::forget` exists, and a shim or raw
  adoption can lie. The contract delivers §3's narrowing; the guards make
  growth visible without proving raw provenance.
- **"Cannot be stored" is partial.** Enforceable: `Borrowed` cannot discharge,
  and an `as_borrowed` view cannot outlive its owner. A `from_abi` borrow can be
  stored; the parent-lifetime projections narrow it at once but add no general
  child-borrow operation.
- **Intrinsics externs are not declaration-derived.** Their ownership facts are
  asserted at the enumerated owner seams and stated in their source contracts.
- **Eventual disposer identity remains prose.** Storage transfer is typed, but
  the type does not identify which later drop glue discharges a stored field;
  that is drop-glue identity, owned by backend.
- **Declaration sensitivity is bounded.** The inline `vec-get` row has no shim,
  so §4 never reaches its `ProjectionOf` fact. The accepted evidence boundary
  and its revival trigger are in
  [primitives §5](../primitives/primitives.md#5-test-strategy).

## 8. Public surface

The committed intrinsics `public-api.txt` is the mechanical enumeration:
`pub mod handle`, `Owned` and `Borrowed<'a>` with the operations of §2, and the
nine consuming funnels — `rc::consume_shallow`;
`drop::{consume_slist, consume_sexp, consume_vec_with, consume_vec_of_string,
consume_io_tree, consume_closure, dec_shallow_io}`; `trace::consume_trace_call`
— taking `Owned`.

- `consume_vec_with` spells its element callback inline as `fn(Owned)`; no
  callback alias is public.
- The baseline is generated in the default debug profile, so it lists the
  debug-only `Drop` impl. A release-profile empty `Drop` written to stabilise
  the baseline is rejected as code for a documentation property.
- Primitives has no Rust public-API delta: implementation bodies and generated
  shims are `pub(crate)`.
- The C ABI is unchanged: shims keep `extern "C" fn(i64, …) -> i64`; handle
  types appear only inside them. `cranelisp-types` is unaffected.
- No serialized cache shape carries these types. Changing a shim's entry
  convention still moves the caller-side RC contract that cached objects bake
  in, so the change lands with backend's value-only `CACHE_SCHEMA_VERSION` bump
  ([module caching §14.2](../backend/module-caching.md#142-cache_schema_version-ownership)).

## 9. Open obligation

- **The `Drop` profile-conditionality rustdoc is absent.** The settled baseline
  ruling calls for rustdoc naming that `Owned`'s drop bomb exists only under
  `debug_assertions`; `handle.rs` does not say so. Owner: `dev` (intrinsics).
  Rustdoc only; no public-API or baseline delta.

## 10. Potential extensions, with triggers

- **Deriving intrinsics extern facts from `intrinsics_table()`**, a
  **callback-scoped `from_abi` borrow**, and **narrowing `rc_inc`** — triggers
  in [ownership/disposal 9](../intrinsics/ownership-and-disposal.md#9-potential-extensions-with-triggers).
- **Ownership-returning public allocation APIs** — assessed by `arch` under
  [ACT-0959](../../sprints/actions/ACT-0959-public-allocation-api-redesign.md).
- **Naming alignment with platform's `CLOwned<T>`**
  (`crates/cranelisp-platform/src/lib.rs`) — triggered only if one handle must
  cross between the runtime pair and platform code.

## 11. Principles applied

- **7** — one token derives both shim wrapping and ABI-kind data.
- **18 and 20** — the move checker and the `Owned` type replace the "discharge
  every heap argument you do not return" rustdoc rule; the trusted base is an
  executable enumeration; with no borrowed conversion kind, a borrowing shim
  entry is unrepresentable.
- **14 and 15** — the transparent handle keeps FFI layout; the facade types live
  with the discharge behaviour in intrinsics.
- **25** — the drop bomb accompanies the narrowing "this frame is done with
  this reference".
- **6** — two types, eight operations; the lifetime brand is the only concept
  beyond the minimal sketch (§2.3).
- **8** — the raw `i64` shim is the permanent ABI boundary, not a bridge.

## 12. References

- [Intrinsics ownership and disposal](../intrinsics/ownership-and-disposal.md)
  — the delivered funnel, teardown walks and module evidence.
- [Primitives design](../primitives/primitives.md) §2.4 and invariants 7 and
  14 — the primitives consumer.
- `design/runtime/s118-structural-embedding-ownership.md` — RE-1/RE-2/RE-3,
  which the primitives marshal interior spells in these types.
- `design/arch/ownership-stratum-options.md` — the option paper this contract
  realises as option 1.
- `design/intrinsics/diagnostic-modes.md` §7.5 — the precheck-ordering
  precedent behind §5 leg 3.
