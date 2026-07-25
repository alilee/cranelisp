# `cranelisp-platform` whole-context assessment — Sprint 117

**Date:** 2026-07-25
**Scope:** `crates/cranelisp-platform/`, `design/platform/`, the platform
bounded-context and interface records, and production-path coverage that crosses
the host/DLL boundary. This is a point-in-time, read-mostly assessment. It does
not pull any memory-protection or instrumentation work into Sprint 117.

## 1. Verdict

| Attribute | Grade | Acid-test verdict |
|---|---|---|
| Design quality (fitness) | **Adequate** | The narrow C-ABI contract crate, typed `i64` wrappers, one manifest macro, generated-schema binding, and host-owned poll reactor are shapes a second implementation would retain. Hand-authored `CLAdtType::TYPE_NAME` bindings are now real repeated authoring work rather than a hypothetical deferral. |
| Design realisation | **Weak** | Source and design prose simultaneously describe retired and current architectures. An external author can read ABI v8, a retired feature gate, callback-based validation, and a future closure-callback widening even though the implementation and the architecture say ABI v9, core/ungated, layout-hash validation, and no closure capability. |
| Simplicity and volume — code | **Strong** | The production crate is about 4,041 lines across six cohesive modules. Unsafe work is concentrated at the ABI and heap-wrapper seams; there is no duplicate host-callback construction and no second manifest path. |
| Simplicity and volume — design | **Weak** | Five live platform design records total about 3,900 lines. `platform.md` contains an as-built snapshot, multiple sprint passes, a decision register, and a retired callback design; `poll-support.md` alone is 1,414 lines and includes implementation handoff material. A second-time solution would retain a much smaller current design and archive the sprint archaeology. |
| Simplicity and volume — tests | **Adequate** | Risk coverage is strong, but three integration crates reproduce essentially the same raw heap-ADT allocator/deallocator fixture. The repetition is modest today but sits on the most dangerous byte-layout seam. |
| Duplication | **Adequate** | Production operations converge well: one `declare_platform!`, one `manifest_to_descriptors`, one schema parser, one `cranelisp_intrinsics::host_callbacks()` builder, and one `PollEnv` offset seam. Test fixture mirroring and narrative duplication remain. No redundant language surface was found in this bounded context. |
| Risk-weighted coverage | **Strong** | ABI field order, vtable offsets, macro/GOT ordering, schema generator/parser agreement, allocator return conventions, RC transfer, DLL-local fault outcomes, and real poll-platform paths have production-path witnesses. |
| Maintainability | **Adequate** | Module boundaries, names, and unsafe comments are generally good. Stale contract comments are now the principal maintainability hazard because this crate is the external author facade. |
| Memory freshness | **Weak** | `CLAUDE.md` accurately documents most current traps, but it knowingly carries the stale `poll_support` banner as an “apparent bug” rather than repairing the external-facing source. It also cannot compensate for contradictory live design and rustdoc. |

**Overall.** A lean second implementation would look recognisably like the
current code: a small dependency-clean ABI crate with typed wrappers, a single
manifest emitter, generated schema lookup, and a host-reactor vtable. It would
not reproduce the current documentation stack. The implementation has
converged through ABI v9 while its live prose preserves several superseded
architectures in place. The priority is therefore not a code redesign; it is to
make the source facade and design canon describe exactly one current contract.

## 2. Current state

### 2.1 Prior-assessment trail

The Sprint 87 headline finding is resolved. Both production consumers now call
the single builder `cranelisp_intrinsics::host_callbacks()`:
`src/platform.rs:217-221` and
`crates/cranelisp-exe-bundle/src/lib.rs:124-130`; the sole literal construction
is at `crates/cranelisp-intrinsics/src/lib.rs:248-265`. This structurally closes
the JIT/REPL versus `--link` allocator-wiring divergence identified as S87 F2.

S87 F1 (ABI-number drift) was repaired in the master design:
`design/platform/platform.md:20,54,77,95,125` consistently records ABI v9.
S87 F4 was repaired: `CLAdt::construct` uses `base_ptr` at
`crates/cranelisp-platform/src/adt.rs:216-224`.

S87 F5 was deferred until the first real ADT-marshalling platform. That trigger
has now passed. `platforms/shapes/src/lib.rs:39-45` hand-writes one marker;
`exemplar/platforms/web/src/lib.rs:89-115` hand-writes four more, and
`platforms/shapes-badabi/src/lib.rs:64-67` mirrors the shapes binding. The risk
is still a runtime schema lookup failure from a string typo
(`crates/cranelisp-platform/src/adt.rs:336-365`), not a compile-time mismatch.

### 2.2 Design quality and realisation

The core representation is coherent:

- `HostCallbacks` remains the two-function allocator surface
  (`crates/cranelisp-platform/src/lib.rs:597-631`), and its construction is
  single-sourced below both host modes.
- `PlatformFn`, `PlatformManifest`, `HostCtx`, `Waker`, and `WakerVTable` are
  explicit `#[repr(C)]` contracts. `ABI_VERSION = 9` is the one compatibility
  gate (`crates/cranelisp-platform/src/lib.rs:184-298`).
- `declare_platform!` emits the manifest, GOT, and layout-hash exports from one
  macro path (`crates/cranelisp-platform/src/declare.rs:304-459`).
- ADT field access is callback-free and schema-bound by name
  (`crates/cranelisp-platform/src/adt.rs:172-224`); the schema parser remains
  dependency-clean rather than inverting the crate graph
  (`crates/cranelisp-platform/src/schema.rs:1-58`).
- The poll boundary keeps runtime cadence on the host side:
  `crates/cranelisp-platform/src/concurrency.rs:1-115` is pure ABI shape, while
  `poll_support.rs:50-247` contains only leaf-author ergonomics.

The realisation failure is documentary and directly affects the public
contract:

1. `concurrency.rs:4,21` says its core types are governed by ABI v8, while
   `lib.rs:298` and its own `host_ctx_v9_vtable_layout_is_stable` test
   (`concurrency.rs:160-171`) say v9.
2. `poll_support.rs:1` calls the module “`concurrency`-gated”; the feature was
   retired. The local memory explicitly acknowledges this stale statement
   (`crates/cranelisp-platform/CLAUDE.md:142-145`).
3. `declare.rs:132-135` says ABI is “now 8,” again contradicting v9.
4. The crate-root external-author preamble says host services include
   “validation” through `HostCallbacks` (`lib.rs:16-19`), but that callback was
   removed and layout hashes are the validation mechanism
   (`lib.rs:80-98,577-583`).
5. `HostCallbacks` rustdoc promises future `rc_inc`, `rc_dec`, and
   `invoke_closure` fields (`lib.rs:585-595`), and `CLIO` repeats the callback
   reservation (`lib.rs:893-898`). Architecture explicitly retired that model:
   `design/arch/bounded-contexts.md:567-568,597-599` says the boundary is
   poll-in/wake-out and `HostCallbacks` stays exactly two pointers.
6. The per-crate master design still has an active “Forward-commitment:
   callback support” section (`design/platform/platform.md:286-300`), repeats
   it in the decision register (`:516-523`), and calls it intentionally live at
   `:675-676`, contradicting the Sprint 98 ruling.

The architecture record also preserves superseded states as if they were still
pending. For example, `design/arch/bounded-contexts.md:519-529` labels the
generated-artifact target as pending and retains a Sprint 71 “as-built” shape,
while current source already implements the generated artifact and removed
`validate_schema`. Lines `:539-541` call concurrency landed-and-dormant behind
an off-by-default feature, despite the v8/v9 core cutover described later in
the same section (`:543-551`). Lines `:553-565` still narrate future host
wiring that landed in Sprint 76. These historical layers obscure rather than
explain the nine current invariants at `:591-609`.

### 2.3 Simplicity, volume, and duplication

Production volume is proportionate to the boundary:

- `lib.rs` 1,647 lines; `declare.rs` 637; `schema.rs` 732; `adt.rs` 385;
  `poll_support.rs` 426; `concurrency.rs` 214.
- The six modules align with six concerns. The former macro monolith is gone,
  and no function-level production mirror comparable to the historical
  JIT/`--link` callback construction remains.

The live design volume is not proportionate:

- `design/platform/platform.md` is 691 lines and still carries per-sprint pass
  logs at `:558-679`.
- `design/platform/poll-support.md` is 1,414 lines, including a detailed
  implementation order at `:1351-1414`.
- `sprint71-redesign.md` (893 lines), `host-wiring-s76.md` (200), and
  `implementation-slice-s66.md` (164) remain beside current design rather than
  under `design/platform/archive/`, even where their mechanisms are explicitly
  superseded.
- `platform.md:97-107` maintains a manual file-metrics and public-item census.
  It already understates current source (`lib.rs` recorded ~1,779 but now
  1,647, and the table omits the current production totals) and integration
  tests (`866` recorded versus 868 current lines). Counts are not design
  invariants and predictably decay.

Test duplication is narrower but occurs at a risky seam:
`tests/cl_adt_products.rs:51-71`, `tests/cl_adt_sums.rs:39-63`, and
`tests/worked_examples.rs:33-58` independently allocate the
`[total_size][rc][tag][pad][fields...]` heap shape and, in two cases, duplicate
deallocation. Separate processes are useful because each integration binary
owns a write-once schema, but the raw layout fixture itself can be shared from a
`tests/common` module without merging those processes.

### 2.4 Risk-weighted coverage

The highest platform risks are pinned on meaningful paths:

| Risk | Production-path evidence | Verdict |
|---|---|---|
| `#[repr(C)]` ABI layout drift | `concurrency.rs:137-205` pins vtable offsets, sizes, alignments, enum discriminants, and poll-fn projection; `tests/facade_pif_rows.rs:712-853` pins `PlatformFn`, `PlatformManifest`, and `HostCallbacks` order and Send/Sync projections. | **Pinned** |
| Manifest order diverges from GOT slot order | `declare.rs:576-636` expands the production macro and compares manifest order with installed GOT slots; `tests/macro_expansion.rs:83-113` exercises the exported form. | **Pinned** |
| Host allocator base/payload convention corrupts heap | `src/tests.rs:646-875` includes the exact violating offset, repeated construct/free, and the correct production constructor path; the sole builder has pointer-identity tests in `cranelisp-intrinsics`. | **Pinned** |
| Schema generator/parser grammar drift | `tests/platform_schema_roundtrip.rs:1-358` feeds backend-generated artifacts to the production `Schema::parse`; crate tests cover products, sums, recursion, and type-witness failure. | **Pinned** |
| DLL-local panic cannot cross Rust-runtime boundary | `src/tests.rs:337-431` pins `EffectOutcome`; `tests/platform_errors.rs:337-407` exercises the real faulting DLL and host composition. | **Pinned** |
| Poll ABI and leaf-authoring path diverge | ABI offsets are pinned in `concurrency.rs`; `poll_support.rs:270-420` covers env/vtable/phase mechanics; project e2e lanes exercise the real `poll-pool`, `pool-demo`, and `async-demo` DLLs (`tests/concurrency_fanout.rs`, `tests/concurrency_capacity.rs`, `tests/concurrency_reactor.rs`). | **Pinned** |
| RC transfer at the DLL boundary | `src/tests.rs:208-304` distinguishes borrowed ownership from consuming transfer; ADT integration tests exercise owned nested fields. | **Pinned** |
| Hand-authored marker name disagrees with generated schema | Positive paths exist in `platforms/shapes` and web, but no representation makes agreement structural. A negative typo would fail only at runtime lookup. | **Not structurally pinned** |

No live behavioural defect was found. No broad test command was run because
other Sprint 117 work was active; this assessment used existing focused
evidence and source inspection.

### 2.5 Maintainability and memory

Unsafe containment remains a strength. Pointer reads are localized to CL
wrappers, manifest conversion, and poll helpers, with explicit `# Safety` or
`// SAFETY:` contracts. The `concurrency.rs` layout tests make field-order
changes conspicuous. Naming is coherent, including the corrected
`CLAdt::construct` `base_ptr`.

The crate memory is unusually useful for allocator and effect-node traps
(`CLAUDE.md:9-85`) and accurately identifies the current six-module test seam
map (`:111-130`). Its weakness is that it records known stale source prose as an
asymmetry (`:142-145`). Memory should explain non-obvious truth, not normalize a
repairable contradiction in the external facade.

## 3. Recommendations

### R1 — Repair the external source facade to one ABI-v9 contract

**Kind:** design realisation / memory freshness
**Evidence:** `concurrency.rs:4,21`; `poll_support.rs:1`;
`declare.rs:132-135`; `lib.rs:16-19,585-595,893-898`;
`CLAUDE.md:142-145`, all contradicted by `lib.rs:298` and
`bounded-contexts.md:567-568,597-599`.
**Cost:** small
**Proposed owner:** `/dev` narrow-deployed to `cranelisp-platform`
**Done:** All crate-root and module rustdoc describes ABI v9, core/ungated
poll support, layout-hash validation, and the permanently two-field
`HostCallbacks`. The retired closure-callback promise is absent. The local
memory no longer needs a “known stale phrasing” warning. Add a narrow
source-text/doc guard only if the owner judges version drift likely to recur;
do not add another manually maintained surface inventory.

### R2 — Collapse the platform design canon to current design and archive sprint archaeology

**Kind:** design feedback / design realisation / volume optimality
**Evidence:** `platform.md:286-300,516-523,558-679`;
`poll-support.md:1351-1414`; live historical files
`sprint71-redesign.md`, `host-wiring-s76.md`, and
`implementation-slice-s66.md`; stale manual census at `platform.md:97-107`.
**Cost:** medium
**Proposed owner:** `/design` narrow-deployed to platform
**Done:** `design/platform/` has a concise current `platform.md`, a
right-sized DLL-authoring/interior design, and a right-sized poll-support
design. Superseded per-sprint implementation plans move under
`design/platform/archive/` with a short index. The current docs contain no
retired Decision-0031 callback commitment and no volatile LOC/public-item
census. Historical rationale remains discoverable in archive or the decision
record without being interleaved with current instructions.

### R3 — Reconcile bounded-context §5 from layered migration diary to current invariants

**Kind:** architecture-document realisation
**Evidence:** `bounded-contexts.md:515-575` simultaneously says target,
as-built, implementation pending, dormant feature, future wiring, and current
v9 cutover; the durable current invariants begin only at `:591`.
**Cost:** medium
**Proposed owner:** `/arch`
**Done:** BC §5 states the current generated-schema/layout-hash mechanism,
core v9 poll ABI, shared two-field callback builder relationship, and
poll-in/wake-out boundary once. Superseded S71/S76/v7 mechanisms are reduced to
short historical pointers. Every “pending/as-built” label agrees with source.
This is a documentation convergence only; it does not reopen settled platform
architecture.

### R4 — Decide marker binding ergonomics now that the deferred trigger has fired

**Kind:** design feedback
**Evidence:** runtime string binding at `adt.rs:72-76,336-365`; repeated manual
bindings at `platforms/shapes/src/lib.rs:39-45`,
`platforms/shapes-badabi/src/lib.rs:64-67`, and
`exemplar/platforms/web/src/lib.rs:89-115`. The S87 assessment deferred this
until a real multi-ADT platform; web now has four marker types.
**Cost:** medium
**Proposed owner:** `/design` narrow-deployed to platform, with `/arch` review
if the chosen mechanism changes public API
**Done:** A focused design compares keeping explicit marker impls, a derive,
and a macro/generated binding. It chooses the smallest shape that either makes
schema-name agreement structural or explicitly accepts runtime failure with a
production-path negative witness and clear diagnostics. If explicit impls
remain, the rationale and trigger for reconsideration are recorded; merely
adding another positive test does not cure the mismatch risk.

### R5 — Share the raw heap-ADT integration fixture without merging schema-isolated tests

**Kind:** test simplicity / mirror duplication
**Evidence:** near-identical allocation layout at
`tests/cl_adt_products.rs:51-71`, `tests/cl_adt_sums.rs:39-63`, and
`tests/worked_examples.rs:33-58`.
**Cost:** small
**Proposed owner:** `/dev` narrow-deployed to `cranelisp-platform`
**Done:** The three integration binaries remain separate so their
`GLOBAL_SCHEMA` lifetimes stay isolated, but import one private `tests/common`
heap-layout fixture. The helper has one explicit layout contract and preserves
the existing production API assertions. No new public test-support API is
introduced.

## 4. Disposition trail

To be appended by `/sprint` with the user during the next sprint's Phase 1.
Recommendations in this assessment are proposals and have not been filed as
FIXMEs.

## Next skills

- `/sprint` — process R1–R5 with the user at the next sprint's Phase 1,
  accepting each into a numbered FIXME or recording a decline rationale.
- `/dev` (platform) — if accepted, R1 and R5.
- `/design` (platform) — if accepted, R2 and R4.
- `/arch` — if accepted, R3 and any public-API consequence of R4.
