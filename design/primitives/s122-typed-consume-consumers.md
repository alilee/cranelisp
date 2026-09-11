# S122 primitives typed-consume consumers

**Status:** Primitives declaration conversion, typed private bodies, D8 transfer
interior and module evidence delivered from source checkpoint `dc78ddbe`;
generated baseline confirmation and integrated evidence pending. The existing
typed-consume contract is consumed from
`design/runtime/s119-typed-consume-funnel.md`; this document does not amend its
public vocabulary. The user approved the exact private trusted-base amendment
in §6 on 2026-09-10; current source implements it without a public API addition.

## 1. Delivered source and approved target

Current production source now delivers the approved private boundary:

- `crates/cranelisp-primitives/src/declaration_macro.rs` keeps raw `extern "C"`
  wrapper words while converting them to the typed private body signatures.
  `PrimitiveDecl` carries the private ABI-kind projection, derived through the
  delivered `crates/cranelisp-primitives/src/abi_facts.rs`.
- The selected String, int, marshal, bool and float bodies consume `Owned` or
  `Borrowed` exactly as the table below specifies; their raw RC arithmetic and
  externally visible behavior remain unchanged.
- The generated wrapper remains the only production caller of each shim-reached
  category body; marshal's private helpers form the only additional production
  call graph in this slice.
- `vec-len` is already `UserInline`, slot-less, absent from the extern harvest,
  and has no Rust body in `crates/cranelisp-primitives/src/vec.rs`. It is not a
  typed-consume consumer.

The approved target keeps every exported symbol, arity, argument word, result
word, GOT slot, and `ModeSummary` unchanged. Generated wrappers remain raw
`extern "C" fn(i64, ...) -> i64`; they convert raw words to private body types
at entry and convert the body result back at return. The selected body
signatures are:

| Module | Exact target |
|---|---|
| `int.rs` | `int_to_string(i64) -> Owned`; `parse_int(Owned) -> Owned` |
| `string.rs` | `str_concat(Owned, Owned) -> Owned`; `str_eq(Owned, Owned) -> i64`; `neq_string(Owned, Owned) -> i64`; `str_len(Owned) -> i64`; `string_identity(Borrowed<'_>) -> Owned`; `str_substring(Owned, i64, i64) -> Owned`; `str_char_at(Owned, i64) -> Owned`; `str_split(Owned, Owned) -> Owned`; `str_join(Owned, Owned) -> Owned`; `str_replace(Owned, Owned, Owned) -> Owned`; `str_trim(Owned) -> Owned`; `str_starts_with(Owned, Owned) -> i64`; `str_ends_with(Owned, Owned) -> i64`; `str_contains(Owned, Owned) -> i64`; `str_to_upper(Owned) -> Owned`; `str_to_lower(Owned) -> Owned` |
| `marshal.rs` entry bodies | `sconcat(Owned, Owned) -> Owned`; `quote_sexp(Owned) -> Owned` |
| Other result-only bodies forced by the declaration projection | `bool_to_string(i64) -> Owned`; `float_to_string(i64) -> Owned` |

`Mode` is not the ABI axis. The six only-read String rows retain
`Mode::Borrowed` for analysis while their `ParamFlow::Consumed` still produces
an `Owned` shim argument and one body discharge. `string-identity` remains the
sole `ParamFlow::IntoResult` row: its body receives `Borrowed`, calls
`to_owned()` once, and performs no decrement.

## 2. Declaration-derived conversion

The delivered private `crates/cranelisp-primitives/src/abi_facts.rs` keeps all
conversion machinery together. `is_heap_carried(Type)` is the single
predicate used by both the ABI derivation and
`ownership_facts::{copy_fresh_for_type, uniform_for_type}`.

For parameter `i`, derive:

```text
Scalar          when the declared type is Int, Bool, or Float
BorrowedHandle  when it is heap-carried and ParamFlow[i] is IntoResult
OwnedHandle     when it is heap-carried and ParamFlow[i] is any consuming flow
```

The row's `shim:` clause writes each private Rust parameter type and the private
result type once. The macro uses those same tokens to generate raw entry/exit
conversion and `abi_param_kinds`/`abi_result_kind` data on `UserExtern` and
`HarvestExtern`. It never changes the wrapper's raw C signature. A declaration
unit compares every `UserExtern` token projection with the kinds derived from
its `Type::Fn` and `ParamFlow`; a contradictory token/body pair must fail in the
existing compile-fail harness.

`UserInline` rows have no wrapper tokens. They participate in the declared
type/flow derivation and heap predicate, while no emitted shim-kind datum is
invented for them. The three scalar `HarvestExtern` rows derive scalar tokens.
`sconcat` is the sole named harvest exemption because its Cranelisp type is
seeded by Binary/int rather than this inventory; its `Owned, Owned -> Owned`
tokens remain checked against its Rust body by rustc. Growing that exemption is
a design/review stop.

The private ABI-kind data does not enter `SymbolTable`, `cranelisp-types`, the
cache, or typecheck. Typecheck continues to consume the existing
`ModeSummary`; no primitive-call resolution, prelude fallback, alias
provenance, or `ParamFlow` value changes in this work.

## 3. Body and interior transfer

String reads take `Borrowed<'a>` and return slices tied to `'a`. A consuming
body reads through `owned.as_borrowed()`, constructs its result, then passes the
original owner once to the appropriate typed consume funnel. `str_join` keeps
the existing callback-scoped Vec-of-String read: pass the Vec owner's raw read
word to `with_vec_strings`, end the callback borrow, construct the result, then
consume separator and Vec once.

Marshal changes its nine heap-bearing helpers as one interior:

- A private `StoredField::{Scalar(i64), Owned(Owned)}` makes the second slot of
  `alloc_adt_2(tag, StoredField) -> Owned` explicit. The Int/Float/Bool Sexp
  constructors select `Scalar`; String/Sym/List/Bracket and outer-list
  constructors select `Owned`. No tag-threshold guess classifies a field.
  `alloc_adt_3(tag, field0: Owned, field1: Owned) -> Owned` is reserved for
  `SCons`, whose two fields are ownership-bearing. Allocate the raw base and
  write the scalar tag first. An `Owned` field's `into_raw()` occurs immediately
  inside its field write, after allocation is ready and with no intervening
  fallible operation. Adopt the completed base only after every field is
  initialized.
- `build_runtime_list<const N: usize>(items: [Owned; N]) -> Owned` adopts the
  canonical `SNil`, then moves each item and the current tail into
  `alloc_adt_3`. An owned array avoids a new allocating `Vec` merely to make
  non-`Copy` transfer possible.
- `read_slist<'a>(Borrowed<'a>) -> Vec<Borrowed<'a>>` returns views tied to the
  root. `quote_sexp_build(Borrowed<'_>) -> Owned` and
  `quote_slist(Borrowed<'_>) -> Owned` never consume their source views.
- `alloc_runtime_string` and `make_sexp_sym` return `Owned`.
  `shallow_rc_inc(Borrowed<'_>) -> Owned` delegates to `to_owned()`, preserving
  one increment for each copied child and one for the shared `sconcat` tail.
- `sconcat` derives borrowed views from `xs` and `ys`, mints exactly the owners
  stored in the result, and consumes both incoming owners once. `quote_sexp`
  borrows its input for construction, consumes it once, and returns the new
  owner.

Raw `read_i64`/`write_i64`, allocator outputs before complete initialization,
and the existing raw Vec construction API remain mechanical representation
seams. This work does not repeat the Vec length implementation, alter heap
layout, or add instrumentation.

For `str_split`, fresh child Strings are held as `Vec<Owned>`. A private
`vec_strings_from_owned_handles` first reserves a raw `Vec<i64>` to the exact
child count, before disarming any child. It then drains each child with
`into_raw()` into the already-sized Vec and immediately transfers that Vec to
the existing `vec_strings_from_owned`. That receiver's
`UnpublishedVecStrings` guard owns all raw children from function entry and
cleans partial Vec construction on unwind. The completed Vec word is adopted
once. No child is disarmed while a capacity allocation can still unwind.

The typed migration adds no general panic-cleanup regime. Existing operations
that can abort allocation retain that behavior; current body panics before
normal epilogue remain governed by their existing contracts. The transfer
ordering above prevents this migration from adding a new gap between child
disarm and receiver ownership.

## 4. Delivered source surface and dependencies

The delivered primitives change is confined to:

- `crates/cranelisp-primitives/src/abi_facts.rs` (new), plus
  `crates/cranelisp-primitives/src/lib.rs`,
  `crates/cranelisp-primitives/src/declaration_macro.rs`,
  `crates/cranelisp-primitives/src/declarations.rs`, and
  `crates/cranelisp-primitives/src/ownership_facts.rs`;
- `crates/cranelisp-primitives/src/int.rs`,
  `crates/cranelisp-primitives/src/string.rs`,
  `crates/cranelisp-primitives/src/marshal.rs`,
  `crates/cranelisp-primitives/src/bool.rs`, and
  `crates/cranelisp-primitives/src/float.rs`;
- their existing module tests,
  `crates/cranelisp-primitives/src/declarations/tests.rs`, its UI fixtures, and
  the declaration projection fixture;
- `crates/cranelisp-primitives/public-api.txt` only for generated confirmation.

It consumes the delivered intrinsics handle vocabulary and nine typed consume
signatures. It does not
edit intrinsics, shared runtime design, backend, typecheck, Binary/int,
platform, cache schema, language tests, or emitted baselines. Backend's
primitive-call and function-value adaptation must continue to follow declared
`ParamFlow`/Decision-24 behavior; any surviving duplicate release is attributed
and repaired in its own retained backend work, never by weakening primitives'
declarations.

## 5. Evidence and filing tails

Delivered primitives evidence stays at existing seams:

- declaration projection and compile-fail rows prove token/body agreement,
  declared type/flow agreement, raw-wrapper preservation, and the one-name
  `sconcat` exemption;
- String, int, and marshal module tests keep behavioral assertions and RC
  arithmetic unchanged while fixture helpers return typed owners;
- the existing structural-embedding cells retain one mint per copied item and
  one mint for a shared tail, including empty/nullary cases;
- structural checks constrain raw-to-owned adoption, child-field borrowing,
  and owner-to-raw storage to their exact approved allow-lists (§6);
- the public baseline must show no primitives API addition from this work; the
  checked-in file is unchanged, while generated architecture confirmation is
  pending.

Current filing dispositions are source-backed:

- **0859:** the user-approved evidence disposition remains complete on the
  existing nine production witnesses, typecheck provenance units, and direct
  inline-body guards. `tests/plan/PLAN.md` carries the revival trigger for a
  future emission-live projection consumer. Typed wrappers add no such
  consumer and require no new observer.
- **0932:** its primitives behavior is delivered: `vec-len` is a slot-less
  `UserInline`, absent from shim harvest, with the four-Vec-family table guards.
  The retained empty public `vec` module is current baseline state and supplies
  no body to this slice. Its linked production-roster obligation is also closed
  by the 0936 observation below.
- **0936:** the historical I-ABI label and a `UniformRust`-only witness are
  superseded. The real bootstrap projection observes exactly four generic,
  slot-less `HostPromised` entries: `primitives/bind`, `primitives/race`,
  `primitives/select`, and `primitives/catch-runtime-error`. Its exact-set guard
  and existing catch control pass 2/2 in run
  `cf467c35-ac84-4087-8017-f9336e3f5eb6`. The canonical closure record is
  `tests/plan/PLAN.md` §“S122 — 0936 production realization-roster closure”.
  This executing projection closes the current evidence obligation; it does
  not make primitives design the owner of the backend roster, add a primitive,
  or authorize a new API or roster member.

Focused run `8e1f35eb-d874-4dbc-84fb-b9995a1dde72` passes all 11 allocated
declaration, D8 and transfer rows; full run
`a2f68144` passes 102/102. The adoption, child-borrow and storage guard plants
each fail at the intended guard and pass after restoration. These are
primitives module results; aggregate macro/runtime D3 still
depends on the retained Binary/int host transfer and final integration review.

## 6. Approved trusted-base amendment

On 2026-09-10 the user approved the complete limited amendment recorded in
`sprints/s122-primitives-allocation-proposal.md`. The shared runtime contract
now admits these exact private uses of the existing handle operations. Current
source implements them; the approval adds no handle operation.

The only produced-result adapter is `crates/cranelisp-primitives/src/abi_facts.rs::adopt_produced_value(raw: i64) -> Owned`.
It is crate-private and unsafe. Its precondition is one fully initialized fresh
RC=1 value whose initial reference transfers to the caller; the specifically produced nullary
`None`/`SNil`; or `quote_sexp_build`'s existing raw `0` error sentinel after
`runtime_panic` has recorded an unknown tag. That sentinel is carried through
the typed result and returned by the ABI shim; it is not declared to be a valid
Sexp and the non-diverging `runtime_panic` is not treated as `!`. The adapter
calls existing `Owned::from_abi` once. It does not validate arbitrary
provenance, allocate, increment, decrement, or clean a partly initialized node.

The exact approved caller allow-list is 19 functions and 20 syntactic adoption
sites after consolidation:

| Source | Allowed sites |
|---|---|
| `bool.rs`, `float.rs` | `bool_to_string` (1), `float_to_string` (1) |
| `int.rs` | `int_to_string` (1); `parse_int` initialized `Some` and nullary `None` branches (2) |
| `string.rs` | `str_concat`, `str_substring`, one post-match site in `str_char_at`, `str_split`'s child-String site, `vec_strings_from_owned_handles`' completed-Vec site, `str_join`, `str_replace`, `str_trim`, `str_to_upper`, `str_to_lower` (10 functions/sites) |
| `marshal.rs` | completed bases in `alloc_adt_2` and `alloc_adt_3`, `alloc_runtime_string`, `build_runtime_list`'s `SNil`, and `quote_sexp_build`'s post-`runtime_panic` error sentinel (5 functions/sites) |

Fresh child transfer into a raw parent/container is the third legitimate
`Owned::into_raw` use class, alongside ABI return and typed consume
destructure. It is limited here to four syntactic storage sites in three
functions: the `StoredField::Owned` arm of `marshal::alloc_adt_2`, the two
fields of `marshal::alloc_adt_3`, and the reserved-capacity loop in
`string::vec_strings_from_owned_handles`. An `into_raw`/re-adopt round trip or
disarm before receiver readiness is a review rejection.

The delivered parent-lifetime projection is one private
`marshal::borrowed_field<'a>(parent: Borrowed<'a>, offset) -> Borrowed<'a>`.
It reads a field word from the live parent and uses existing
`Borrowed::from_abi`, narrowed to the parent's lifetime. Its exact six sites in
two functions are `read_slist`'s `SCons` head and tail, and
`quote_sexp_build`'s `SexpStr`, `SexpSym`, `SexpList`, and `SexpBracket`
payloads. Int/Float/Bool payloads stay raw. This is a retained child view,
never a fresh owner or a discharge right.

The guard must name the adapter and function-scoped caller sets. A whole-file,
whole-module, or whole-crate exemption is insufficient. These wrappers make
the assertions enumerable; they do not prove raw provenance. The approved
amendment adds no public item, C ABI, baseline row, Cargo edge, cache schema,
heap layout, or language behavior. Implementation must not substitute a new
operation or extra RC increment.
