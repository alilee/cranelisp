# S124 public-API approval packet

**Owner:** `arch`. **Reader:** the user, at the inter-crate public-API gate
(root `CLAUDE.md` §Roles). **Status:** proposed 2026-11-16; no row is
approved. **Checkpoint:** `main` at `3155f47f`. Line counts are read from the
committed `public-api.txt` files at that commit and are estimates; the
regenerated diff is the exact figure and returns to the user when non-empty.
**Retention:** working document, retired at the S124 close.

The reasoning for each row is in the
[S124 architecture review](s124-architecture-review.md). "Lines" counts every
baseline line naming the item, including the auto-trait rows the current
format prints.

## Gate status

| Row | Subject | Status |
|---|---|---|
| D1 | Backend consumes `ctor_field_types_at` | Proposed |
| D2 | Backend `compiler` module becomes crate-private | Proposed (S123 row R10-4, approved 2026-11-15, not landed) |
| D3 | Import and export entry carrier | Proposed; supersedes S123 row N1 |
| D4 | `HeapCategory::Value` removed | Proposed |
| D5 | Stack-slot tally pair removed | Proposed; exact items confirmed by `design`(intrinsics) |
| D6 | `ExternShim::borrowed_sibling` removed | Proposed (S123 row R10-8, approved 2026-11-15, not landed) |
| D7 | `ModeSummary` ABI predicates removed | Proposed; depends on the §18.1.2 ruling |
| D8 | Trace and spark seam (ACT-1038) | Not yet listable |

## Part A — deltas S124 needs

### A1. Type concreteness (item 1)

| Row | Exact delta | Producers and consumers | Compatibility, schema, ABI | `public-api.txt` |
|---|---|---|---|---|
| D1 | New consumer edge: `cranelisp-backend` calls `cranelisp_types::ctor_field_types_at(table, ctor_key, args)`. No signature change. The backend's constructor-field materialisation and `drop_glue::ctor_shapes` read field types through it; its `NotConcrete` refusal becomes a located error at the reference | Producer: types (`heap.rs`), unchanged. New consumer: backend `compiler/context.rs`, `drop_glue.rs`. No crate edge is new: the backend already depends on types | Additive in use only. No schema or ABI effect | types +0, backend +0 |

### A2. Raise-helper hardening (item 3)

| Row | Exact delta | Producers and consumers | Compatibility, schema, ABI | `public-api.txt` |
|---|---|---|---|---|
| D2 | In `cranelisp-backend`: `pub mod compiler` becomes `pub(crate)`, and with it `compiler::CompileContext` (struct, 10 fields including `panic_func_id`, `lookup_type_def`, `Clone`) | No consumer outside the crate. The typecheck and intrinsics mentions are comments; `cranelisp_types::CompileContext` is a different type | Breaking only for a consumer that does not exist. No schema or ABI effect. The private panic handle that follows is interior | backend −23 |

### A3. Import and export entries (item 5: ACT-0997, ACT-1055, ACT-1056)

| Row | Exact delta | Producers and consumers | Compatibility, schema, ABI | `public-api.txt` |
|---|---|---|---|---|
| D3 | In `cranelisp-types`: (a) add `#[non_exhaustive] pub enum ImportEntry { Name { source: Symbol, local: Symbol }, MemberGlob(Symbol) }`; (b) change `ImportNames::Specific(Vec<Symbol>)` to `ImportNames::Specific(Vec<ImportEntry>)`; (c) remove the variant `ImportNames::MemberGlob(Symbol)`; (d) add the field `pub alias: Option<ModuleName>` to `ExportSpec`. `Name.source` is the name in the source module and may be dotted; `Name.local` is the bare name bound, always present: the written name, the member of a dotted entry, or the second symbol of a rename | Producer: frontend `module_extract.rs` (names list and export module spec). Consumers, root: `src/imports.rs`, `src/save.rs`, `src/cache/dependency_record.rs`, `src/process_form/{cache_restore,dependency}.rs`, `src/session_v4/{index_worker,lifecycle}.rs`, `src/session_v4/test_runner/selection.rs`, `src/cluster.rs`; `tests/cache.rs` | Breaking for every match on `Specific` or `MemberGlob` and every `ExportSpec` literal. **`CACHE_SCHEMA_VERSION` bump**: `SymbolTable.imports` and `exports` are persisted. No ABI effect. The correction carries ACT-0997's impl-identity evidence | types about +13, −1, 1 changed (enum, 2 variants, 2 fields, 7 auto-trait rows, `ExportSpec::alias`; `MemberGlob` removed; `Specific` changed). Frontend +0 |

`ImportNames` lacks the `#[non_exhaustive]` the types policy asks of public
DTOs. Its consumers match it exhaustively on purpose, so the attribute is not
proposed.

### A4. Principle 27 retirements (item 4)

| Row | Exact delta | Producers and consumers | Compatibility, schema, ABI | `public-api.txt` |
|---|---|---|---|---|
| D4 | In `cranelisp-backend`: remove the variant `heap::HeapCategory::Value`. `HeapCategory::classify` no longer returns it; a one-word single-constructor value classifies as a heap value | Producer: backend `heap.rs`. Consumers: root `src/result_owner.rs` (two matches), and `src/display.rs`, which renders by the same layout. `cranelisp_types::value_layout` stays public as a retained fact | Breaking for exhaustive matches. Compiled layout changes: **`CACHE_SCHEMA_VERSION` bump**. Emitted-code ABI changes within one build only | backend −1 |
| D5 | In `cranelisp-intrinsics`: remove `pub fn rc::stack_slot_hits() -> u64` and `pub fn rc::tally_stack_slot()`, with any catalog row and the `[RC_STATS]` `stack_slot` field that report them | Sole consumer: backend `heap.rs`, which calls both at emission time and is deleted in the same change-set; this removes the consumer edge backend → these two items. Readers of the printed field: test helpers | Removes a diagnostic counter. No schema or emitted-code ABI effect | intrinsics −2. If `design`(intrinsics) lists other items, the row returns |
| D6 | In `cranelisp-types`: remove the field `borrowed_sibling: Option<CallableSlot>` from `Realization::ExternShim` | No producer since ACT-0974. Consumers: backend cache validation (`cache/serialize.rs`), types `lifecycle.rs` and `module.rs`, tests | **`CACHE_SCHEMA_VERSION` bump**: `Realization` is persisted | types −1, 1 changed |
| D7 | In `cranelisp-types`: remove `ModeSummary::abi_eq`, `ModeSummary::abi_eq_opt` and `ModeSummary::is_abi_conservative` | Consumers: root `src/redefine.rs` and `src/worker.rs`, whose gate is deleted with REPL §18.1.2 | Semantic change the baseline cannot show: a same-type live redefinition is no longer refused for a mode difference. Requires the user's §18.1.2 ruling first. No schema or ABI effect | types −3 |

Spark density has no public item and needs no row.

## Part B — not yet listable

| Row | Subject | What is missing |
|---|---|---|
| D8 | ACT-1038: declining sparks inside a trace's dynamic extent, and a wrapper that formats only when its thread records | `design`(intrinsics) and `design`(backend) list whether an existing intrinsic's signature changes or an export is added. A listed row returns here before implementation |

## Part C — confirmed without a delta

- Item 1: the category census, typecheck's producer corrections, the
  backend's binder-type representation, ACT-1050 and ACT-1034.
- Item 2: ACT-1052, while `CachedModuleRef::dependency_hashes` stays a map of
  opaque strings and `check_manifest` is unchanged.
- Item 4: spark density.
- Item 5: ACT-1057 and audit R1, R3, R4 and R5.
- Item 6: package convergence.
- Item 7: ACT-0973, ACT-0985, ACT-1001 P-3, ACT-1016, ACT-1018, ACT-1036 and
  ACT-1039.

A design or implementation that finds it needs a public change under any of
these stops and returns to this packet.

## Part D — S123 rows still unlanded

S123 rows B2 (K11-a to K11-d) and B3 (R10-1 to R10-9) were approved for the
S123 close and are not in source. D2 is R10-4 and D6 is R10-8. The others are
outside the S124 scope unless the user pulls them in; they are listed in the
[S123 packet](s123-api-packet.md) Part B.
