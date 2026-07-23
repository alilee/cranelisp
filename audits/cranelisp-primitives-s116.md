# `cranelisp-primitives` — Sprint 116 whole-context assessment

> **Point-in-time assessment (2026-07-23).** Read-only audit at `ea649b34`
> plus this assessment file. Recommendations are proposals for the next
> sprint's Phase-1 disposition; no FIXME is filed here.
>
> **Scope.** `crates/cranelisp-primitives/`, `design/primitives/`, bounded
> context §4a, the S87 assessment, relevant ownership coverage records, and
> recent sprint history.

## 1. Verdict

| Attribute | Grade | Basis |
|---|---|---|
| Design quality (fitness) | **strong** | The crate is a small, severed, statically-built leaf with one table/GOT mount and no backend dependency. The second-time solution would keep this boundary. |
| Design realisation | **adequate** | Runtime shape matches BC §4a, but the master design is predominantly an S73/S74 migration record and does not describe the current ownership-fact surface as a target. |
| Simplicity & volume — code | **adequate** | Production modules remain focused; the principal avoidable complexity is four-way, name-keyed primitive registration. |
| Simplicity & volume — docs | **weak** | The 310-line master design is mostly completed work instructions, while live rustdoc contains falsified counts and a stale “single item” claim. |
| Simplicity & volume — tests | **strong** | 105/105 crate tests pass in 0.054s; per-module tests plus the table harness give unusually good attribution for a runtime-facing leaf. |
| Duplication | **adequate** | No broad code mirrors, but primitive identity and ownership facts are repeated across the body/export, operator row, harvest, and fact classifier. |
| Risk-weighted coverage | **adequate** | GOT/table/content and local RC behavior are strongly pinned. The highest-risk declared ownership facts are tested as declarations, not checked against production emission. |
| Maintainability | **strong** | Module seams, safety comments, consuming convention, and the inline-vs-extern representation are clear. |
| Memory freshness | **adequate** | `CLAUDE.md` is current and useful; crate rustdoc and the master design carry verified stale statements. |

**Acid-test answer.** Yes for the implementation boundary and most of the
code. A second-time solution would again use a static `SymbolTable`, a static
GOT slab, crate-private extern shims, direct dependencies on types and
intrinsics, and no backend knowledge. It would not recreate four manually
synchronised descriptions of each primitive, accept an ownership fact merely
because the fact table is internally consistent, or retain two sprints of
completed migration instructions as the active master design.

## 2. Current state

### 2.1 Architecture and implementation

BC §4a's important shape is realised:

- `PRIMITIVES_TABLE` is the sole semantic mount and is built once
  (`src/lib.rs:185-218`).
- `PRIMITIVES_GOT_SLAB` supplies stable static backing
  (`src/lib.rs:107-145`), and the table installs that backing before
  population (`:190-209`).
- `cranelisp-primitives` has no dependency on `cranelisp-backend`; runtime
  services flow inward from `cranelisp-intrinsics`.
- Inline Vec operations are represented as `PrimitiveBody::Inline` with no
  phantom slot, while `vec-len` is an extern with a real slot
  (`src/lib.rs:261-375`). This resolves the S87 null-slot concern by
  representation rather than by another guard.
- Heap-layout constants and RC entry points are imported from their owning
  crates. The S87 duplicated-offset and non-atomic-inc findings remain closed.

The crate has 2,173 raw production lines excluding test files and 105 passing
unit tests. No production function is a god function; unsafe work is
concentrated in marshalling and heap/string adapters and carries local safety
explanations.

### 2.2 Duplication

**Mirror duplication.** No material byte-near mirror remains inside the crate.
Scalar wrappers are intentionally small and independently named.

**Divergent duplication.** Primitive identity is maintained in four forms:

1. the extern body and `export_name`,
2. the `PrimitiveDef` row in `operator.rs`,
3. the `extern_shims()` name-to-pointer harvest (`src/lib.rs:378-459`),
4. for heap-bearing operations, the name-keyed ownership classifier
   (`src/ownership_facts.rs:77-153`).

The localized memory states these four required edits explicitly
(`CLAUDE.md:120-129`). That honesty is useful, but it is evidence of an
unresolved structural seam rather than a cure.

The existing harvest test checks every harvested shim is either a table entry
or one of four exceptions (`src/tests.rs:549-579`). It does not derive the
`export_name` inventory, so omission in the body-to-harvest direction remains
unguarded—the same outstanding direction identified in S87.

**Entry-point duplication.** Table construction itself is clean: ordinary
rows share `insert_primitive_entry`; the exceptional polymorphic Vec family
has one explicit builder. There is no REPL/batch/link duplicate mount in this
crate.

**Spec-surface redundancy.** None found. This crate implements the Appendix-A
surface; it does not introduce alternative language spellings.

### 2.3 Risk-weighted coverage

| Risk | Production-path evidence | Verdict |
|---|---|---|
| GOT slab and shim address population | `static_slab_slots_populated_after_force`, `got_slots_hold_extern_ptrs_for_harvested_shims`, behavior calls through loaded slots | **pinned** |
| Inline Vec operations accidentally become null-slot calls | `vec_trio_is_inline_no_slot_and_vec_len_is_extern` plus callable-target checks | **pinned** |
| Heap extern violates consuming convention | module-local RC-balance tests for string/int/marshal paths | **substantially pinned** |
| Declared ownership fact missing | `every_heap_param_primitive_carries_a_declared_summary` | **pinned for presence** |
| Declared ownership fact is false relative to emitted behavior | fact-table tests assert expected declarations; the coverage plan says the table is audited by hand when primitives change (`tests/plan/memory-safety-coverage.md:284`) | **not mechanically pinned** |
| Exported shim omitted from harvest | forward-direction harvest test only | **not pinned** |
| Vec String construction follows runtime layout/write discipline | `split`/`join` tests exercise behavior, but source directly reads/writes offsets (`src/string.rs:185-238`) | **example-tested, seam not contained** |

The ownership-fact gap is the important one. `vec-set`/`vec-push` once carried
a false `Fresh` fact and produced the vec-assoc UAF class; the current
`MayAliasOf(0)` declarations are correct and well tested
(`ownership_facts.rs:97-122`, `ownership_facts/tests.rs:142-211`). Those tests
prove the table says the intended thing, not that backend production emission
still has the behavior the declaration describes. The current standing
control is a manual table-vs-implementation audit when a primitive changes.

### 2.4 Documentation and memory

`crates/cranelisp-primitives/CLAUDE.md` is the best current entry point. It
records the consuming convention, ownership-fact contract, inline Vec
representation, four edit seams, and test layout accurately.

The canonical rustdoc is less current:

- `src/lib.rs:14-19` says “Public Rust API — single item,” but the baseline has
  two public statics (`PRIMITIVES_TABLE` and `PRIMITIVES_GOT_SLAB`) plus seven
  public modules.
- The same paragraph says “~22” extern functions; source currently has 58
  function `export_name` attributes plus the exported slab.
- `src/lib.rs:88-96` says the baseline has nine lines; it has ten.

The master design is not operating as a maintained target document.
`design/primitives/primitives.md` is 310 lines, of which §2–§8 are completed
S73/S74 work steps, retired-facade mappings, and acceptance instructions. It
still describes a nine-line baseline (`:235`, `:295-300`) and repeatedly
references retired facade files. The useful current target—static table/GOT,
extern/inline bodies, ownership declarations, consuming ABI, and boundary
invariants—is already clearer in source rustdoc, BC §4a, and `CLAUDE.md`.

## 3. Recommendations

### R-1 — Make primitive registration complete by construction

- **Evidence:** Four name-keyed edits are required (`CLAUDE.md:120-129`);
  `extern_shims()` repeats every exported function name
  (`src/lib.rs:378-459`); the harvest test checks only harvest → table
  (`src/tests.rs:549-579`).
- **Cost:** medium.
- **Proposed owner:** `/design` then `/dev` (`cranelisp-primitives`);
  `/arch` only if the chosen descriptor changes the public surface.
- **Done:** one declaration-site descriptor or generator produces the table
  row, shim harvest, and ownership-fact attachment where applicable; an
  omission of an exported shim is structurally impossible or caught by a
  mechanically derived reverse-inventory test. The four harvest-only
  exceptions remain explicit typed variants, not a string allow-list.

### R-2 — Verify ownership declarations against production behavior

- **Evidence:** False `Fresh` on the inline COW pair previously caused UAF;
  the current tests prove declaration values and completeness but do not
  compare them with backend emission. The standing plan requires a manual
  audit when a primitive changes.
- **Cost:** medium.
- **Proposed owner:** `/qa` for the verification contract, then narrow
  `/dev` owners for the production observation seam.
- **Done:** every nontrivial declaration class—Borrowed scalar-result,
  AliasOf, ProjectionOf, and MayAliasOf—has a production-path witness that
  fails if emission and declaration diverge. Adding or changing a heap
  primitive cannot pass by updating only `ownership_facts.rs` and its unit
  expectation.

### R-3 — Converge String/Vec layout access on the runtime owner

- **Evidence:** `split` writes Vec elements and length directly and `join`
  reads them directly (`src/string.rs:185-238`), despite
  `cranelisp-intrinsics::vec_runtime` owning allocation and layout. This is
  the unresolved S87 MED-2 finding.
- **Cost:** small-to-medium.
- **Proposed owner:** `/design` + `/dev` on the runtime surface; `/arch` if a
  new cross-crate accessor must be public.
- **Done:** primitives does not perform raw Vec offset arithmetic. It uses a
  runtime-owned construction/read API whose tests pin initialization order,
  bounds, and RC ownership for `Vec String`.

### R-4 — Replace the migration log with a current master design

- **Evidence:** `design/primitives/primitives.md` is 310 lines dominated by
  completed S73/S74 steps and retired-facade bookkeeping; current ownership
  facts and inline-body representation are described more accurately in
  localized memory and source.
- **Cost:** small.
- **Proposed owner:** `/design` (`cranelisp-primitives`).
- **Done:** the master design states current actors, invariants, data flow,
  risks, test strategy, and rejected alternatives; completed migration
  instructions are removed or archived. It points to source rustdoc and BC
  §4a instead of retired facades and contains no stale baseline counts.

### R-5 — Repair canonical public-surface rustdoc

- **Evidence:** `src/lib.rs:14-19` says one public item and ~22 externs;
  `:88-96` says nine baseline lines. The committed baseline has ten lines and
  source has 58 exported functions plus the GOT slab.
- **Cost:** small.
- **Proposed owner:** `/arch` approval + `/dev` (`cranelisp-primitives`) edit.
- **Done:** rustdoc describes the two public statics and seven modules without
  embedding volatile primitive counts; the baseline remains mechanically
  checked and no semantic API changes.

## 4. Disposition trail

Pending Sprint 117 Phase 1 user disposition.
