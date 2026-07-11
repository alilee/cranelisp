# cranelisp-primitives — local conventions

The voice of the code: FFI/export-name discipline, the static-GOT-slab invariant,
the consuming convention, the declared ownership-fact leaf, and the multi-site
seams to touch when adding a primitive. Owned by `/dev` when narrow-deployed to
this crate.

This crate is the **user-callable** half of the language runtime library (kebab-case,
symbol-table-addressable ops: `add-i64`, `str-concat`, `vec-len`, …); its backend-paired
sibling `cranelisp-intrinsics` hosts the backend-emitted-call substrate (alloc/RC/drop,
IO trampoline). Canonical BC + direction: `design/arch/bounded-contexts.md` §4a and
`design/primitives/primitives.md` — do NOT restate them here.

## The public Rust surface is ONE item (Decision 0048, S68)

`PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<(), ()>>>` plus the exported static
`PRIMITIVES_GOT_SLAB` and seven `pub mod` are the entire `cargo-public-api` baseline
(`public-api.txt`). **Every extern fn is `pub(crate) extern "C"` carrying
`#[unsafe(export_name = "kebab-name")]`** — the fn is invisible to Rust callers but its
kebab symbol lands in the object/staticlib regardless of Rust visibility. Consequence: the
baseline is **stable across primitive churn** — adding/renaming/deleting a primitive does
not touch the Rust surface. Which primitives exist is governed by spec-conformance tests
and the `operator::ring{0,1,3}_primitives()` builders, NOT the Rust baseline (`lib.rs:88`).

## DCE survival of the extern shims (no `#[used]`)

There is deliberately **no `#[used] static` anchor** (`#[used]` is statics-only, does not
apply to fns). Three existing mechanisms keep the shims alive in `--link` static archives
(`lib.rs:20`): (1) the `export_name` attribute emits the linker symbol; (2) exe-bundle's
startup `LazyLock::force(&PRIMITIVES_TABLE)` (`cranelisp-exe-bundle/src/lib.rs`) anchors the
static; (3) `extern_shims()` takes every fn's address at static-init, referencing it from
live code. If a primitive silently vanishes from a `--link` binary, one of these three
regressed — do not "fix" it by adding a `#[used]` static.

## The primitives GOT is a static slab, not a heap alloc (FIXME 0280)

`PRIMITIVES_GOT_SLAB` (`lib.rs:143`) is a process-`static [AtomicPtr<u8>; GOT_TABLE_SIZE]`
exported under `__cranelisp_got_primitives`, and `build_primitives_table` replaces the
default heap GOT with `GotTable::with_static_backing(&PRIMITIVES_GOT_SLAB)` (`lib.rs:198`).
Reason: `--link`-mode dispatch emits GOT-indirect against `__cranelisp_got_primitives` in
ALL modes (`apply.rs`); a heap `GotTable::new()` can never be a link-time symbol, so `ld`
fails "symbol not found". Invariants that must hold (all in the `PRIMITIVES_GOT_SLAB`
rustdoc + `tests.rs::primitives_got_base_is_the_exported_static_slab`):
- **`AtomicPtr` not `static mut`** — interior mutability, writes via `store_slot` (atomic
  Release); no `unsafe` to mutate, no `const`/read-only static (the `(trace)` GOT copy-swap
  `memcpy`s INTO this base and needs writable `__DATA`, not `__DATA_CONST`).
- **Exactly one `GotTable`** is built over the slab (inside the `LazyLock`).

## Primitive-ness is read from `kind`, never from `code` (Decision 0048 A2-reversed, FIXME 0244)

Every entry is built with `code: None` (the `ModuleEntry::def(..).build()` default) and
`kind: DefKind::Primitive`. `code` is NOT a primitive marker — there is no `Code::Primitive`.
The GOT is the single source of truth for the `*const u8` (Decision 35), indexed by the
`PrimitiveBody::Extern.got_slot`. Guarded by `tests.rs::every_entry_is_def_kind_primitive`.

## Backend severance — this crate ⟂ cranelisp-backend (Decision 0048, S73)

Neither names the other; `cranelisp-primitives` has NO backend dep (`Cargo.toml`: only
`cranelisp-types` + `cranelisp-intrinsics` + serde). Because every entry is `code: None`,
primitives builds a `()`-flavoured table and never constructs `Code` or names it. `int`
concretizes `<(),()>`→`<Code,()>` via `SymbolTable::into_concrete` at the session mount
(the exercised cache-restore bridge — `session_v4.rs`, `worker.rs`), preserving the shared
`Arc<GotTable>`. Do NOT reach for a backend type here; cross-crate needs route to `/arch`.

## Heap-layout offsets are single-sourced from intrinsics (Principle 7)

No local copies of any heap offset. `string.rs`/`vec.rs` read `HeapString::{LEN,DATA}_OFFSET`
and `vec_runtime::{LEN,DATA_PTR}_OFFSET` from `cranelisp-intrinsics`' blessed public consts;
`marshal.rs` derives `PAYLOAD/FIELD0/FIELD1_OFFSET` from `HeapHeader::SIZE` + a local i64
stride, guarded by `const _: () = assert!(...)` (`marshal.rs:51`). A `HeapHeader` layout
change breaks the build here at compile time rather than silently corrupting `read_i64`.

## Consuming convention — every extern dec's its heap args (Decision 24)

The extern boundary is fixed for codegen uniformity: an extern fn MUST dec (consume) every
heap-typed argument it does not return, via `rc::consume_shallow` / `drop::consume_*`
(`string.rs`, `marshal.rs`, `int.rs`). Callers compile args through
`compile_consuming_arg_list` (heap Vars inc'd at the call site so the binding survives the
dec). RC inc's route through the blessed `cranelisp_intrinsics::rc::rc_inc` — the single
shallow-inc owner (never a raw `*rc += 1`; the former non-atomic path was a data race once
S85 auto-IO let a spark fork a shared value — `marshal.rs:154`).

## Declared ownership facts — the pass5 leaf (S102 CS-B, FIXME 0504/0510)

`ownership_facts::declared_mode_summary(name, ty)` attaches a hand-declared `ModeSummary`
to every `DefKind::Primitive` entry at construction (`lib.rs:251`, `:358`). pass5 reads it
as a constant leaf boundary condition. The split ruling (§9.1 of the design doc): **only-read
heap params** (`str-eq`, `neq-string`, `str-len`, the `?`-predicates, `vec-len`) are declared
`Mode::Borrowed` (the analysis fact) even though the extern body still Consumes (Decision-24
ABI unchanged). **Transforming** heap params → `Owned`/`Fresh`; **scalars** → `Copy`;
`string-identity` → `AliasOf(0)`; the inline vec trio carries projection/COW vocabulary.
`None` = the Decision-24 conservative default (⊤-on-absence), the ONLY rule for an
unclassified heap leaf. Completeness contract (no heap-param primitive may default to `None`)
guarded by `tests.rs::every_heap_param_primitive_carries_a_declared_summary`. This is a
declaration-site table, NOT a typecheck-side privileged-by-name table (Principle 19).

## The inline vec trio has NO GOT slot (S102, FIXME 0476, Principle 20)

`vec-get`/`vec-set`/`vec-push` carry `PrimitiveBody::Inline` and allocate **no slot** — the
backend inline-emits them keyed by bare name (`vec_codegen`). Only `vec-len` is `Extern` with
a real shim + populated slot. "Resolvable but not slot-callable" is a *kind*, not an
allocated-but-NULL phantom slot: use `is_callable_target()` (covers both arms) as the
predicate, NOT `callable_got_slot().is_some()`. Their polymorphic `(Vec a)` schemes over one
quantified var (`insert_vec_query_entries`, `lib.rs:291`) are load-bearing — a boundary-erased
monomorphic scheme fails to unify against a `(Vec Int)` arg (FIXME 0277).

## Adding a primitive — the seams to touch

1. `operator.rs` — add the `PrimitiveDef` row to the right `ring{0,1,3}_primitives()` (name,
   `ty`, `param_names`, `docstring` = the §A.5-MUST Description text).
2. The shim module (`ring0.rs`/`string.rs`/…) — the `#[unsafe(export_name)] pub(crate) extern "C" fn`.
3. `lib.rs::extern_shims()` — insert `name -> fn as *const u8` (the GOT-population harvest).
4. `ownership_facts.rs` — classify it if it has a heap param (else it silently defaults `None`).

Skipping (3) leaves a NULL GOT slot → `--link`/mappable dispatch faults; skipping (4) drops a
heap leaf to the conservative default. All four are cross-checked by `src/tests.rs`.

## Submodule seam map + where `#[cfg(test)]` lives

| Module | Content | Tests |
|---|---|---|
| `lib.rs` | table build, static slab, `extern_shims()`, vec-query rows | `src/tests.rs` (crate-root harness) |
| `operator.rs` | `PrimitiveDef` rows + ring builders (input data only) | `operator/tests.rs` |
| `ownership_facts.rs` | `declared_mode_summary` classifier | `ownership_facts/tests.rs` |
| `ring0.rs` | scalar arith/cmp/bool/bitwise shims | `ring0/tests.rs` |
| `string.rs` | string shims | `string/tests.rs` |
| `int.rs` / `float.rs` | conversion shims | `int/tests.rs` / `float/tests.rs` |
| `marshal.rs` | `sconcat` / `quote-sexp` SList/Sexp marshalling | `marshal/tests.rs` |
| `bool.rs` / `vec.rs` | `bool-to-string` / `vec-len` | **INLINE `mod tests {}`** (no sibling file) |

Two asymmetries a reader would misread as an oversight: (a) `bool.rs` and `vec.rs` keep their
tests inline while every other module uses the file-based `mod tests;` sibling — they are
small enough that the S101 per-submodule split left them alone; (b) the 665-line crate-root
`src/tests.rs` was **left un-split by intent** (audit-blessed, one concern: table population +
static-backing + content/behavioural/docstring/ownership harnesses) at S106 Phase 1.

## Known asymmetries (not bugs)

- **Harvest-only shims** `neq-i64`/`neq-f64`/`neq-bool`/`sconcat` appear in `extern_shims()`
  but have NO `PRIMITIVES_TABLE` entry — the scalar `neq-*` reach user code via `Eq.!=`
  trait dispatch (scalar args are `Copy`, so the Decision-24 default costs nothing), and
  `sconcat` is registered in the synthetic `macros` module. Encoded in the allow-list of
  `tests.rs::extern_shims_harvest_covers_full_inventory`.
- **`neq-string` is a real `ring1` entry** (FIXME 0510) — unlike its scalar siblings — so it
  carries the `Borrowed` facts symmetric with `str-eq`; pre-0510 it was shim-only and pass5
  chain-followed to a missing entry ⇒ asymmetric `Owned` precision loss vs `str-eq`.
- **`div-i64` overflow uses the "division by zero" message** for the `i64::MIN / -1` case
  (`ring0.rs:74`) — deliberate, to stay observable-equivalent with the inline path's
  `emit_checked_div`.
