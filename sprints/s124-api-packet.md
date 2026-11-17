# S124 public-API approval packet

**Owner:** `arch`. **Reader:** the user, at the inter-crate public-API gate
(root `CLAUDE.md` §Roles). **Status:** every row is approved: D1–D7 and D9
on 2026-11-16; D8, R10-9, D10, D11, R10-10 and D12 on 2026-11-17, as written
in Parts B, B3 and B4. D12 carries one condition, stated in Part B4.
**Checkpoint:** `main` at
`4b58ab93` for Part B, `3155f47f` for Part A. Line counts are read from the
committed `public-api.txt` files and are estimates; the regenerated diff is
the exact figure and returns to the user when non-empty.
**Retention:** working document, retired at the S124 close.

The reasoning for each row is in the
[S124 architecture review](s124-architecture-review.md). "Lines" counts every
baseline line naming the item, including the auto-trait rows the current
format prints.

## Gate status

| Row | Subject | Status |
|---|---|---|
| D1 | Backend consumes `ctor_field_types_at` | Approved 2026-11-16 |
| D2 | Backend `compiler` module becomes crate-private | Approved 2026-11-16 (S123 row R10-4) |
| D3 | Import and export entry carrier | Approved 2026-11-16; supersedes S123 row N1 |
| D4 | `HeapCategory::Value` removed | Approved 2026-11-16 |
| D5 | Stack-slot tally pair removed | Approved 2026-11-16 for the two listed items; another item returns the row |
| D6 | `ExternShim::borrowed_sibling` removed | Approved 2026-11-16 (S123 row R10-8) |
| D7 | `ModeSummary` ABI predicates removed | Approved 2026-11-16; REPL §18.1.2 removed by the same ruling |
| D9 | Backend `CacheStale::SiblingSlotOutOfRange` removed | Approved 2026-11-16 (Phase 3) |
| D8 | Trace and spark seam (ACT-1038): contract of two intrinsic exports | Approved 2026-11-17 |
| R10-9 | Heap layouts defined once, in intrinsics; the backend's copies deleted | Approved 2026-11-17; supersedes S123 row R10-6 |
| D10 | Implementation identity under a renamed import (ACT-0997) | Approved 2026-11-17 |
| D11 | `runtime/rc_underflow_check` retired; `runtime/string_read` leaves the catalog (ACT-1033) | Approved 2026-11-17 |
| R10-10 | Backend and root read the Vec offsets from intrinsics once R10-9 deletes `HeapVec` | Approved 2026-11-17 |
| D12 | Root library: a missing `main` is the batch entry operations' typed outcome (S124-Q8) | Approved 2026-11-17, on the condition that the refusal keeps its error category |

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

## Part B — found in Phase 3, approved 2026-11-17

Source read at `4b58ab93` on 2026-11-16. The user approved each row as
written in the table. The notes under it record each row's basis, rejected
alternatives and accepted tradeoffs.

| Row | Exact delta | Producers and consumers | Compatibility, schema, ABI | `public-api.txt` |
|---|---|---|---|---|
| D8 | In `cranelisp-intrinsics`, two exports change contract and keep their signatures. (a) `cranelisp_spark_budget_try_reserve` (`ivar::spark_budget_try_reserve(i64) -> i64`) additionally returns `0`, reserving nothing, while the calling thread holds the trace role. (b) `cranelisp_trace_format(i64, i64) -> i64` returns `0` and allocates nothing on a thread that does not hold the trace role; on the recording thread it returns a fresh String as today. Consequence for `cranelisp_trace_enter` and `cranelisp_trace_exit`, whose contracts do not change: off the recording thread every string argument they receive is `0`. With spark statistics on, the `[SPARK_STATS]` line gains a final `trace_declines` field | Producer: intrinsics (`ivar.rs`, `trace_format.rs`), with one crate-private predicate in `trace` for "this thread records". Consumers: backend-emitted code only — the create-gate at each lenient spark site, and the trace wrapper, which passes the formatter's result to enter and exit without inspecting it. No emitted call sequence changes. The backend deletes its compile-time `in_trace_body` flag after intrinsics' change, so a trace form's own spark sites gain the ordinary create-gate. The backend's descriptor round-trip tests call (b) directly and must run as the recording thread; they change in intrinsics' change-set | Semantic change the baseline cannot show. Observable effect: no spark is admitted inside a trace's dynamic extent, so traced evaluation is sequential (user ruling 2026-11-16, review §8.4; spec §4.12.2), and a wrapper reached off the recording thread no longer leaks its formatted strings. A caller of (b) must accept `0`. The statistics field is appended, so a reader by name is unaffected. No schema effect. Emitted code changes only inside trace forms (scoped golden diff) | intrinsics +0, backend +0 |
| R10-9 | (a) Add to `cranelisp_intrinsics::alloc`: `#[repr(C)] pub struct HeapAdt { pub header: HeapHeader, pub tag: i64 }` with `TAG_OFFSET: i32`, `FIELDS_START: usize`, `const fn field_offset(usize) -> i32`, `const fn payload_size(usize) -> usize`; and `#[repr(C)] pub struct HeapClosure { pub header: HeapHeader, pub code_ptr: i64, pub drop_glue_ptr: i64 }` with `CODE_PTR_OFFSET: i32`, `DROP_GLUE_PTR_OFFSET: i32`, `CAPTURES_START: usize`, `const fn capture_offset(usize) -> i32`, `const fn payload_size(usize) -> usize`. (b) Add `pub const cranelisp_intrinsics::vec_runtime::PAYLOAD_SIZE: usize`. (c) Remove from `cranelisp_backend::heap`: `HeapAdt`, `HeapClosure` and `HeapVec` with every field and associated item. Names, values and integer types of (a) equal the backend items they replace | Producer: intrinsics `alloc.rs`, `vec_runtime.rs`. New consumer edges, all between crates that already depend on intrinsics: backend → `alloc::{HeapAdt, HeapClosure}` and `vec_runtime::PAYLOAD_SIZE`; root → `alloc::HeapAdt` (`src/display.rs`, `src/session_v4/test_runner/run.rs`) and `alloc::HeapClosure` (`src/session_v4/test_runner.rs`, which writes the closure layout as literals today); primitives → `alloc::HeapAdt` (`marshal.rs`, which restates the ADT offsets today). Removed edge: root → the three backend layout structs | No layout value changes, so emitted code is byte-identical and the golden corpus is unaffected. No schema or ABI effect. Breaking for the root's readers of the backend structs, which move in the same callee-first migration | intrinsics about +33 (`HeapAdt` 15, `HeapClosure` 17, `PAYLOAD_SIZE` 1); backend −49 (15, 17, 17). Under K11-a's format: intrinsics about +19, backend −28. Primitives and types +0 |
| D10 | In `cranelisp-types`: (a) add the field `pub authored_label: Symbol` to `WrittenTraitImpl`: the label of the `impl` head as its writer spelled it, unresolved, each reference with its written qualifier. It is opaque: compared for equality only, never split, resolved or displayed; (b) `WrittenTraitImpl::new` gains `authored_label: Symbol` as its last parameter; (c) add `pub fn TraitImpl::authored_label(&self) -> Symbol`, the one derivation of that label from an `impl` form: slot 1's `TraitRef` as written, `.`, then the written `TypeRef` of the target's head, or of the pairing's constructor argument when slot 1 echoes a higher-kinded head; `_` stands for a target with no head reference. The form as built and the form after typecheck's higher-kinded rewrite yield one label. It replaces the binary's crate-private derivation (`definition_result_symbol`'s `impl` arm with `impl_echo_type_name`), which drops both qualifiers and is not moved | Producer: typecheck `traits/impl_check.rs::register_trait_impl`, which already builds the record from the pair it resolved and takes the label from the form as received. Consumers, root: the live turn and backing-file rehydration, each of which keys an `impl` form by reading the writer's records for the form's label and takes the identity from the one matching record's settled `trait_name` and `impl_type`; save and the definition echo read the records' settled pair and never the label. A form matches only when exactly one record carries its label; none or several is no match, never a pick. Twelve `WrittenTraitImpl::new` call sites change: the one producer and eleven in test code | Breaking for every `new` caller. **`CACHE_SCHEMA_VERSION` bump**: the record is persisted in the writer's `.meta.json`; no serde default, because an empty label would silently match nothing. It rides D3's bump when it lands in D3's migration. No ABI effect. `upsert_written_trait_impl` and restore enrolment are unchanged: the label is not part of a record's key and its uniqueness is not enforced | types +3, 1 changed (the field, the method and the `impl TraitImpl` header line, which the type lacks today; `new` changed). Typecheck +0 |
| D11 | In `cranelisp-intrinsics`: (a) remove `pub extern "C-unwind" fn rc::rc_underflow_check(i64, i64) -> i64` and its catalog row `runtime/rc_underflow_check`; (b) remove the catalog row `runtime/string_read` and the `#[export_name = "runtime/string_read"]` attribute of `heap_string::string_read`, which stays a public Rust function with its signature | (a) No consumer: no backend, root or primitives source names the function or emits the symbol. (b) Sole consumer of the function: root `src/marshal.rs`, a Rust-path call, unchanged. No emitted code names either symbol; JIT registration and the generic import declaration lose two entries | Breaking only for a consumer that does not exist. A cached object or linked executable cannot reference either name, because nothing ever emitted one. No schema effect | intrinsics −1, 1 changed (the `string_read` line loses its attribute) |

### D8 — basis

`design`(intrinsics) confirms the placement
([trace runtime §6](../design/intrinsics/trace-runtime.md#6-public-surface--packet-row-d8))
that `design`(backend) proposed
([trace codegen §2](../design/backend/trace-codegen.md#2-the-trace-extent-and-the-wrappers-allocation)).
The behaviour is already ruled; the row adds only where it lives.

- **Rejected:** a new query export ("does this thread record?") that the
  wrapper branches on. It keeps `cranelisp_trace_format` total, at the cost of
  one more public item, a larger emitted wrapper and a second reader of a
  fact intrinsics owns.
- **Tradeoff accepted:** `cranelisp_trace_format` stops being a pure
  formatter, so any future caller outside a trace wrapper must handle `0`.
  The descriptor walk behind it stays pure and crate-private.
- **Residual, not closed by this row:** a force of an IVar created before the
  trace began may be claimed by a worker, whose calls are then unrecorded
  ([trace runtime §4](../design/intrinsics/trace-runtime.md#4-what-stays-concurrent-during-a-trace)).
  Nothing leaks; the tree depends on scheduling in that case.

### R10-9 — basis

Both halves are listed: intrinsics'
([heap layout owners §2](../design/intrinsics/heap-layout.md#2-the-constant-list-r10-9-intrinsics-half))
and the backend's
(backend design §9.1, in [backend.md](../design/backend/backend.md)).
Verified at source: the backend's `heap.rs` and several intrinsics modules
(`drop.rs`, `trace.rs`, `trace_format.rs`, `ivar.rs`, `io.rs`) each define ADT
or closure offsets, and two further copies sit outside both crates (`crates/cranelisp-primitives/src/marshal.rs`;
`src/session_v4/test_runner.rs`, as literals).

- **It supersedes S123 row R10-6.** R10-6 narrowed the backend `HeapClosure`
  to crate-private (−17); this row deletes the struct. R10-6 is not part of
  the backend contraction, and its 17 lines are within this row's −49.
- **Rejected:** owning the layouts in `cranelisp-types`. Bounded contexts §4b
  places representation in intrinsics; types holds the header only.
- **Tradeoff:** intrinsics' public surface grows by two layout structs so
  that four crates read one definition. The alternative is the present state,
  in which a layout change must be made in each copy across four crates and
  nothing fails if one is missed.
- **Scope note.** The root and primitives edges are in the row so their
  convergence needs no further gate. `design`(primitives) has not designed
  `marshal.rs`'s convergence; approving the edge does not schedule it.

### D10 — basis

Both designs confirm the carrier in place of the `CheckResult` field first
proposed: [typecheck §12, T7](../design/typecheck/typecheck.md#12-designed-changes-not-yet-in-source-s124)
and [int §6.13](../design/int/int.md#613-import-and-export-entries-and-export-mounts-s124).
Verified at source: `WrittenTraitImpl` is the only implementation record on a
cache-restored table, and `src/save.rs::rehydrate_introspection_from_source`
keys each backing-file `impl` form from its written head, so under
`(import [lib [(Box B)]])` it computes `Show.B` against a settled `Show.Box`
and never matches.

**What the row does.** The writer's record says what its `impl` head was
written as. The live turn and rehydration make one keyed read of that record
and take the settled pair from it; no route resolves a head name again
([Principle 24](../design/arch/principles/24-resolve-once.md)). Typecheck's
public surface does not change, and the binary needs no further public item:
it holds the settled pair through the existing `trait_impl_key`.

**Why the label keeps qualifiers.** The binary's present derivation keeps
only the bare names, so `(impl Show a/Box …)` and `(impl Show b/Box …)` in one
module would share a label. The derivation is therefore new in the types crate
and the binary's copy is deleted, not moved. The count is +3 because
`TraitImpl` has no inherent `impl` block today, so its header line is new.

- **Several records under one label.** The carrier does not make a label
  unique within a writer, and the row adds no enforcement. A consumer treats
  anything other than exactly one matching record as no match: rehydration
  leaves the form unkeyed and reports it, and the live turn raises its located
  invariant error. No fixed file scope produces the case, because one spelling
  resolves to one identity or is rejected as ambiguous (spec §8.6.4, §8.6.5).
  That argument is asserted, not measured; its falsifier is either report
  firing.
- **Rejected:** refusing a second record with an equal label at
  `upsert_written_trait_impl`. It would fail a well-typed `impl` on a rule the
  spec does not state, and a restored sidecar bypasses upsert, so the read
  would need the rule anyway.
- **Rejected:** the `CheckResult` carrier, which does not exist where nothing
  was typechecked; and a head resolution in the binary at rehydration, which
  is a second resolution of one identity (Principle 24).
- **Tradeoff:** a persisted record carries a spelling. It is an association
  key back to the authored form and never an identity source; the rustdoc
  must say so. It also costs a schema bump, shared with D3, and a changed
  constructor with twelve call sites.

### D11 — basis

ACT-1033's remaining half. Verified at source: neither symbol has an emitter,
and `string_read`'s only caller is the binary's Rust-path call.

- **(a)** The emitted inline decrement is checked before it runs, by
  `runtime/rc_dec_check`; a post-decrement check would be a new backend
  design, not a use of this row. A catalog entry nothing calls is a declared
  import whose signature nothing exercises, which is how its declared
  arity came to disagree with its function unnoticed.
- **(b)** The catalog holds targets of emitted calls
  (bounded contexts §4b invariant 1). `string_read` is a Rust-path operation
  with a named cross-crate consumer, which that invariant admits as a public
  function, not as a catalog row.
- **Rejected:** keeping either row "reserved for future use"
  ([Principle 8](../design/arch/principles/08-no-interim-implementations.md)).
- **Tradeoff:** a future emitter of either operation adds its row back
  through this gate, with its emitting site and module test.

## Part B2 — found in Phase 3, approved 2026-11-16

| Row | Exact delta | Producers and consumers | Compatibility, schema, ABI | `public-api.txt` |
|---|---|---|---|---|
| D9 | In `cranelisp-backend`: remove the variant `cache::serialize::CacheStale::SiblingSlotOutOfRange { path: PathBuf, slot: usize }` | Its only producer is the cache loader's validation of the borrowed-sibling slot, which D6 deletes with the field. No consumer outside the crate: the root and `tests/` name no `CacheStale` variant in code. In-crate: the variant's diagnostic tag and display arms and one module test | Breaking only for a consumer that does not exist. No schema or ABI effect beyond D6's | backend −3 |

D6 and R10-8 list the types field only; neither names this variant. Without
D9, D6 lands leaving a public variant nothing constructs.

## Part B3 — found in Phase 3 design, approved 2026-11-17

Source and the committed `public-api.txt` files read at `4b58ab93` on
2026-11-17.

| Row | Exact delta | Producers and consumers | Compatibility, schema, ABI | `public-api.txt` |
|---|---|---|---|---|
| R10-10 | No item is added, removed or changed. Two new consumer edges to three constants that are already public and unchanged, `cranelisp_intrinsics::vec_runtime::{LEN_OFFSET, CAP_OFFSET, DATA_PTR_OFFSET}` (each `pub const … : usize`): (a) backend → all three; (b) root → `LEN_OFFSET` and `DATA_PTR_OFFSET`. The rustdoc of the three constants names these readers in place of its present claim that primitives reads them | Producer: intrinsics `vec_runtime.rs`, unchanged apart from the rustdoc. Consumers today: none outside intrinsics; no backend, primitives or root source names any of the three. New consumers: backend `heap.rs`, which converts each to `i32` once in a constant context for `compiler/vec_codegen.rs`, replacing `HeapVec::{LEN_OFFSET, CAP_OFFSET, DATA_PTR_OFFSET}`; root `src/display.rs`, replacing `HeapVec::{LEN_OFFSET, DATA_PTR_OFFSET}`, and `src/session_v4/test_runner.rs`, replacing its literal `16` and `32`. Both crates already depend on intrinsics, and the root already calls `vec_runtime::vec_new` | Values are equal (16, 24, 32), so emitted code is byte-identical and the golden corpus is unaffected. The integer type differs from the deleted backend constants (`usize`, was `i32`): the backend converts, and the root's readers lose a cast. No schema or ABI effect | intrinsics +0, backend +0, beyond R10-9's own figures |

### R10-10 — basis

R10-9 (c) deletes the backend's `HeapVec`, and its consumer list names where
the ADT and closure readers go but not where the Vec offset readers go: it
lists backend → `vec_runtime::PAYLOAD_SIZE` only, and no root edge into
`vec_runtime`. The designs supply the missing destination
([backend design §9.1](../design/backend/backend.md),
[int §16.0](../design/int/int.md)). That destination is a consumer edge the
user did not see, so it is a row of its own and R10-9's wording is unchanged.

- **Why the gate applies with a +0 baseline.** The gate names a new
  cross-crate consumer edge, and this packet states edges per item (D1, D5,
  R10-9). Verified at source: the three constants have no reader outside
  intrinsics, and `crates/cranelisp-primitives/src/string/tests.rs` asserts
  that primitives does not name them. A public constant gains its first
  outside readers, which then constrain it.
- **Relation to R10-9.** R10-9's deletion of `HeapVec` and these edges land
  in one migration: the deleted constants' readers move to `vec_runtime` in
  the change-set that removes them.
- **Rejected:** keeping literal offsets in the readers. It needs no edge, and
  it leaves the Vec layout written in three crates, against bounded contexts
  §4b invariant 2, which R10-9 exists to make true.
- **Rejected:** new accessor functions in `vec_runtime` for length and
  element reads. More public surface than three constants that are already
  published, and the backend emits loads at offsets, so it needs the numbers.
- **Tradeoff:** the Vec layout stays three free `usize` constants while the
  ADT and closure layouts are structs with `i32` associated constants, so the
  backend carries one conversion. Reshaping `vec_runtime` to match is a
  larger public change and is not proposed.
- **Not proposed:** the test runner's module-path reader calling the public
  `vec_runtime::with_vec_strings` in place of the two offsets
  ([int §16.0](../design/int/int.md)). It would be a gate matter: a new
  root consumer edge to an item whose only outside consumer is primitives.
  It is not needed. The reader conforms on this row's constants, and the
  root keeps the offset edge for `src/display.rs` and the runner's Vec
  builder either way, so the helper would remove one of three readers.

## Part B4 — found in Phase 3 design, approved 2026-11-17

Source read at `4b58ab93` on 2026-11-17. The requirement is the user's
S124-Q8 ruling (REPL §5.5 and §5.1): in `--run` or `--link`, an existing
entry file with no `main` is refused by naming the file and the missing
`main`, without a form span.

**Approval condition.** The user approved the row's delta as written and
ruled that the refusal keeps its error category: the S124-Q8 exception lifts
the source location only, so REPL §5.1 item 1 still binds. The row as
proposed said the line would lose its category text; the observable-change
cell below states the approved outcome. The condition changes no item of
the delta: `MissingMain` has one producer and one renderer, so its category
is a constant of the binary's rendering and needs no field.

| Row | Exact delta | Producers and consumers | Compatibility, schema, ABI | `public-api.txt` |
|---|---|---|---|---|
| D12 | In the root library `cranelisp`: (a) add `#[derive(Debug)] pub enum session_v4::BatchError { MissingMain { entry_file: PathBuf }, Compiler(CranelispError) }`, a closed sum without `#[non_exhaustive]`, with `impl From<CranelispError> for BatchError` and no `Display`. `entry_file` is the entry module's source file as registration resolved it; (b) `CompilerSession::trampoline(&mut self, &str)` returns `Result<OwnedProgramResult, BatchError>`, was `Result<OwnedProgramResult, CranelispError>`; (c) `CompilerSession::link_by_name(&mut self, &str, Option<&Path>)` returns `Result<(), BatchError>`, was `Result<(), CranelispError>`. No item changes in any library crate | Producer: the root's one `main` gate (`exe::validate_main`, crate-private), reached inside (b) and (c). Sole consumer: the binary target `src/main.rs`, whose `run` propagates the sum and whose exit path matches it once, rendering `MissingMain` itself and every `Compiler` error through the existing formatter. No test, bench or other crate calls (b) or (c) | Breaking for the two call sites in `src/main.rs` only. Observable change: the stderr line for a missing `main` loses its `:1:1` and its `at 0..0` and keeps one error category (approval condition; today the four sites print `codegen error` or `module error`); the exit status stays 1. `CranelispError`, `ErrorLocation` and their `Display` are unchanged, so every other diagnostic renders as today. No schema or ABI effect | Root has no baseline. The seven library baselines +0 |

### D12 — basis

`design`(int) returned the representation
([io-integration §1](../design/int/io-integration.md#1-running-a-program);
[int §16.0](../design/int/int.md), *For `arch`*). Its reading is confirmed at
source: `ErrorLocation::span` is always present
(`crates/cranelisp-types/src/error.rs`), every `CranelispError` variant's
`Display` prints it, and the batch formatter (`src/main.rs::format_error`)
derives a line and column from it for every error, so a synthetic span
renders as `1:1` and `at 0..0`. Four root sites raise the refusal today
(`exe::validate_main`, `exe::entry_main_got_slot`, and
`read_main_entry` and `link_by_name` in `src/session_v4/lifecycle.rs`).
The decision is recorded in bounded contexts §6, known architectural
constraints, and §7, error locations.

**What the row does.** The two batch entry operations say in their return
type that they can refuse for a missing `main`, and the binary renders that
case. It is one error value through one match in the driver, not a second
channel.

- **Rejected: a file-level location in `cranelisp-types`**, which
  `design`(int) preferred.
  - The refusal's producer and renderer are both in the binary context, and
    the REPL never reaches it. No other crate would produce or read the new
    value ([Principle 15](../design/arch/principles/15-facade-types-live-with-behavior.md)).
  - REPL §5.5 makes a missing form span a defect for every compiler-stage
    diagnostic but this one. The suite detects that defect by the printed
    `0..0`, for example in `tests/spec_08_modules.rs`,
    `tests/repl_persist.rs` and `tests/spec_10_io.rs`. A types value that
    renders without a position is constructible by every producer in every
    crate, and one that adopted it would pass those guards unlocated. With
    this row the exemption has one constructor, at the gate.
  - It costs a types row, a changed `Display` contract and a serialised
    field, for one consumer.
- **Rejected: both formatters treat a synthetic span as "no position".** It
  needs no item, and it disarms the same guards for every unlocated error at
  once.
- **Rejected: a session query the driver calls before each entry
  operation.** `--run` and `--link` would each have to remember the call, and
  omitting it turns a user refusal into an invariant failure.
- **Tradeoff accepted:** the root's other refusals that name a file and have
  no position keep today's rendering, `:1:1` and `at 0..0`. Examples are a
  missing entry source file and a missing dependency file. No requirement
  asks otherwise (CLI §0.5.5 requires only that the file is named). A ruling
  that widened the exception to a class would reopen the types question.
- **Not decided here:** the line's wording and which category word it
  prints, which are `design`(int)'s under REPL §5.1 item 1 (a category must
  be printed); and the location of a `main` that is not a function, which
  `design`(int) has not yet read.

## Part C — confirmed without a delta

- Item 1: the category census, typecheck's producer corrections, the
  backend's binder-type representation, ACT-1050 and ACT-1034.
- Item 2: ACT-1052, while `CachedModuleRef::dependency_hashes` stays a map of
  opaque strings and `check_manifest` is unchanged. Its `CACHE_SCHEMA_VERSION`
  bump stays, although `design`(int) shows it is redundant for soundness: the
  rule that a persisted value's change of meaning bumps the version has no
  judgment exception, and with the bump the correctness of old records does
  not rest on the private form of the new key.
- Item 4: spark density.
- Item 5: ACT-1057 and audit R1, R3, R4 and R5; typecheck's T1 to T6.
- Item 6: package convergence.
- Item 7: ACT-0973, ACT-0985, ACT-1001 P-3, ACT-1016, ACT-1018, ACT-1036 and
  ACT-1039.

A design or implementation that finds it needs a public change under any of
these stops and returns to this packet.

## Part D — S123 rows still unlanded

S123 rows B2 (K11-a to K11-d) and B3 (R10-1 to R10-8) were approved for the
S123 close and are not in source. D2 is R10-4 and D6 is R10-8. The user ruled
on 2026-11-16 that K11-a to K11-d and R10-1 to R10-8 land in S124. R10-6 is
the exception: row R10-9 (Part B) supersedes it, so it does not land. The
other rows' deltas are in the
[S123 packet](s123-api-packet.md) Part B, and
[boundary types](../design/arch/interfaces.md#approved-changes-not-yet-in-source-s124)
indexes every approved row with its surface and order.
