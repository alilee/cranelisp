# cranelisp-primitives — local conventions

Entry guidance for `dev` narrow-deployed to this crate: the traps that are not
visible from one file. The interior design is
[`design/primitives/primitives.md`](../../design/primitives/primitives.md); the
boundary is the [primitives bounded context](../../design/arch/bounded-contexts.md#4a-primitives--cratescranelisp-primitives).
Do not restate either here.

## Where things are

| Concern | Source | Evidence |
|---|---|---|
| Table build, static GOT slab, public surface | `lib.rs` (crate and item rustdoc) | `src/tests.rs` |
| Sole declaration inventory and its projections | `declarations.rs`, `declaration_macro.rs` | `declarations/tests.rs`, `declarations/ui/` compile-fail cases |
| Raw-word ↔ typed-handle conversion, ABI kinds, trusted base | `abi_facts.rs` | `abi_facts/tests.rs` |
| Ownership-summary constructors for rows | `ownership_facts.rs` | `ownership_facts/tests.rs` |
| Implementation bodies | `ring0.rs`, `int.rs`, `float.rs`, `bool.rs`, `string.rs`, `marshal.rs` | sibling `*/tests.rs`; `bool.rs` keeps an inline `mod tests` |

`vec.rs` is an item-free public module: the Vec query family has no body here
(design §2.2). Do not add code to it; its removal is an `arch` public-API
question.

## Adding or changing a primitive

- Add or edit one row in the `primitive_declarations!` invocation in
  `declarations.rs`. The closed row variants (`user_extern`, `user_inline`,
  `harvest_only`) are the only legal shapes; the macro generates the exported
  wrapper, table entry, GOT population and shim harvest. Never hand-write an
  `#[unsafe(export_name)]` function; a source-structure guard rejects it.
- Category modules hold crate-private bodies only. A body's parameter and
  result types are the ABI kinds written in the row's `shim:` clause, derived
  from the declared type alone: scalar `i64` for `Int`/`Bool`/`Float`, `Owned`
  for every heap-carried position (design §2.4). Neither `Mode` nor `ParamFlow`
  selects a kind: the only-read String rows declare `Mode::Borrowed` and
  `string-identity` declares `IntoResult`, yet their bodies take `Owned`. A
  `Borrowed` token in a `shim:` clause does not compile.
- Discharge each `Owned` parameter once through the intrinsics consume funnel
  (`rc::consume_shallow`, `drop::consume_*`, which take `Owned`), or move it
  into the result as `string-identity` does. The type system rejects a double
  discharge; a missed one is a `#[must_use]` warning and a debug drop bomb.
- Every user-callable row carries a finished `ModeSummary`. A row that borrows
  a parameter and may return it declares `MayAliasOf`, never `Fresh`
  (design §3.2), and gets an `ownership_facts/tests.rs` pin.
- A new raw-handle site outside the wrapper boundary changes the trusted base;
  route it to `arch` before implementation (design §2.4).
- Re-kinding an existing primitive also touches typecheck's fixture seed and the
  types crate's rustdoc (design invariant 11); route those to their owners.

## Traps

- **Slot-less is a lifecycle state.** All four Vec ops are `Life::Inline` with
  no GOT slot; extern rows are `Life::Concrete` with an `ExternShim`
  realization. Test "is this callable?" with `is_callable_target()`, not
  `callable_got_slot().is_some()`. Slot minting refuses a polymorphic scheme,
  so a polymorphic operation cannot be an extern row.
- **No `#[used]` anchor.** Shims survive `--link` DCE through the export-name
  symbol, the declaration harvest and exe-bundle's
  `LazyLock::force(&PRIMITIVES_TABLE)` (`lib.rs` crate rustdoc). If a primitive
  vanishes from a linked binary, one of those regressed; `#[used]` does not
  apply to functions.
- **The GOT slab stays `static [AtomicPtr<u8>; _]`.** Not `static mut`, not
  `const`: the trace GOT copy-swap writes into it, so it must be writable data,
  and exactly one `GotTable` is built over it (`PRIMITIVES_GOT_SLAB` rustdoc).
- **No backend dependency.** Primitives builds a `SymbolTable<(), ()>` and never
  names `Code`; the Binary surface concretises it at session mount. A needed
  backend type is an `arch` question.
- **No local heap offsets.** String offsets come from intrinsics'
  `HeapString` consts; `marshal.rs` derives ADT field offsets from
  `HeapHeader::SIZE` behind `const` asserts. Vec layout never appears here.

## Test conventions

- **Raw-heap test helpers are `unsafe fn`.** `marshal/tests.rs`'s `rc_of` and
  `nodes_and_elements` document their real precondition (a live, unreleased
  base pointer owned across the read) and are justified at call sites. The
  nullary-threshold check is a termination test, not a validity proof; do not
  convert these back to safe functions.
- **Count RC operations in a child process, never with `set_var`.** The
  `rc_inc` tally is armed by `CRANELISP_RC_STATS` in an already-forced
  `LazyLock`, so `set_var` is a silent no-op.
  `re1_embed_inc_tally_is_one_per_call_plus_one_per_copied_item` re-executes the
  test binary for control and sized children, subtracts the arming floor, and
  reads `rc_inc=` from each child's stderr. The children are ordinary tests that
  also run unarmed. The tally counts only above-threshold increments.

## Deliberate asymmetries

- **Harvest-only rows** `neq-i64`, `neq-f64`, `neq-bool` and `sconcat` have
  wrappers but no `PRIMITIVES_TABLE` entry: the scalar `neq-*` are reached
  through `Eq.!=`, and `sconcat` belongs to the synthetic `macros` module. The
  allow-list is in `src/tests.rs::extern_shims_harvest_covers_full_inventory`.
  `neq-string` is a real table entry so it carries the same `Borrowed` facts as
  `str-eq`.
- **`div-i64` reports `i64::MIN / -1` as "division by zero"** to match the
  backend's inline `emit_checked_div` observably.
