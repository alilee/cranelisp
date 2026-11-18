# design/arch/

Owned by `arch`: system boundaries, shared technical contracts, architecture
principles and sequence diagrams. Root [role ownership](../../AGENTS.md#roles)
and the shared [arch contract](../../.agents/skills/arch/SKILL.md) govern the role.
The [document map and retention rules](../../sprints/METHOD.md#31-where-things-live)
govern information placement; this memory adds architecture navigation and local
surface conventions.

## Canonical documents (the target documentation set)

Read the [overview](overview.md) first. Each document owns its detailed contract,
status and unresolved decisions; an index entry does not approve a proposal or
certify implementation. Exact Rust APIs live in source rustdoc, not this index.

| Document | Purpose |
|---|---|
| [Architecture overview](overview.md) | System vocabulary and orientation. |
| [Bounded contexts](bounded-contexts.md) | Responsibilities, dependency direction and shared guarantees, including process-ending panics, the environment supply and baked link-time switches. |
| [Boundary types](interfaces.md) | Narrative companion to the types crate and its rustdoc; its last section is the public-API batch record. |
| [Architectural principles](principles.md) | Sole membership index for principle bodies. |
| [Symbol-table lifecycle](symbol-table-lifecycle.md) | Declaration ownership, slot conservation and atomic publication. |
| [Concrete codegen boundary](concrete-boundary-type.md) | Concrete-only typed body contract. |
| [Backend keyed consumption](backend-keyed-consumer.md) | Resolved identities at the typecheck/backend boundary; the `VarRef`/`ApplyRef` carriers. |
| [Constructor keys](dotted-ctor-canonical-keys.md) | Constructor storage-key grammar and its writer, reader and codegen-transport obligations. |
| [Scoped module aliases](module-alias-scoped-lookup.md) | Referring-module lookup and shared key derivation. |
| [Resolve home before enumeration](resolve-home-enumeration.md) | Display and index enumeration rooted at the resolved home; complete source coverage. |
| [Prelude and explicit imports](prelude-import-convergence.md) | One candidate resolution for every name origin; REPL introspection's obligations to it. |
| [Annotated S-expressions](annotated-sexp-node.md) | Read-time annotation representation and transport. |
| [Macro availability](macro-availability-model.md) | Source-order availability and publication. |
| [Macro expansion ownership](macro-expansion-ownership.md) | Frontend, typecheck and integration responsibilities. |
| [Ownership inference](ownership-inference.md) | Interprocedural ownership queries and their consumers. |
| [Safety invariants](safety-invariants.md) | Maintained invariant register and enforcement limits. |
| [Total concreteness](total-concreteness.md) | End-of-typecheck concreteness invariants, the uniform-realization roster and the IO-node ownership contract. |
| [Trait-implementation persistence](trait-impl-cache-carrier.md) | Writer records, discovery shells and restoration. |
| [Platform interface](platform-interface.md) | DLL authoring, generated schemas and host boundary. |
| [Effect concurrency](effect-concurrency.md) | Ratified, delivered language-level concurrency architecture and its implementation limits. |
| [Introspection ownership](d1-introspection-repl-only.md) | REPL-only collection boundary. |
| [Embedded REPL agent](repl-embedded-agent.md) | Agent and `/search` boundary, invariants, unbuilt targets and open questions. |
| [REPL styling](repl-styling-seam.md) | Shared formatter and styling contract. |
| [Display protocol](display-protocol.md) | Type-directed rendering design and its implementation gates. |
| [Execution tracing](tracing.md) | Trace-node, backend and intrinsics responsibilities. |
| [Test discovery and the compiler test runner](test-discovery.md) | Language test discovery, the shared runner and its panic isolation by process. |
| [Uniform executable identity](s122-overload-reorder-publication.md) | Approved signature identity and implemented types key API. |
| [Shared document checker](s122-shared-document-checker.md) | Shared-tool boundary and project integration contract. |
| [Byte-backed text exploration](byte-backed-text.md) | Non-normative options; no language or implementation authority. |
| [Ownership-stratum options](ownership-stratum-options.md) | Structural option paper; option 2's target reading and decision rule for S123. Retained choices are not approval. |
| [Release-backend proposal](release-llvm-backend.md) | Unratified future proposal; no LLVM work authorized in S122. |
| [Performance backlog](backlog/performance.md) | User-approved suspended scope and future re-entry decisions. |

## Document collections

| Collection | Purpose | Navigation |
|---|---|---|
| `architecture-contracts` | Current architecture contracts and explicitly retained design proposals. | The top-level products linked above. |
| `architecture-decisions-drain` | The decision-label index resolving cited "Decision N" labels to their current homes; no decision records remain. | [Decision labels](decisions/README.md). |
| `architecture-filings` | Actionable architecture filing register, retained until its owning obligation is discharged. | [Open filings](fixmes/). |
| `architecture-sequences` | Current execution and lifecycle sequence diagrams with their navigation and rendering conventions. | [Sequence guide](sequences/README.md). |
| `architecture-archive` | Frozen superseded architecture records retained as historical reference. | [Archive](archive/); historical references retain their recorded meaning. |

The [principles memory](principles/AGENTS.md) governs principle authoring;
[the principles index](principles.md) is the membership authority. Collection
membership does not waive live references or settle a file's outstanding work.

## Archive (`archive/`)

The existing archive is historical reference, not current architecture.
Retention follows the project method: Git suffices for ordinary working history;
retain a document only for useful evidence or rationale beyond that history.
Do not move obsolete prose into the archive merely to preserve file counts.

## Decision labels

Source, tests and designs cite rulings as "Decision N". The
[label index](decisions/README.md) resolves each label to the ruling's current
home; no decision record files exist, and their original texts are Git history.
Do not create Decision files; write a new cross-context commitment into
bounded contexts or a focused contract, and add a label row only for a number
that source already cites. Open filings retain their own lifecycle.

## Where a commitment manifests

- Put current cross-context commitments in bounded contexts or the focused
  shared contract; exact public promises and necessary rationale belong in
  source rustdoc. Context interiors belong to the context design owner.
- Update the affected BC statement, linked contract, rustdoc and sequence
  diagram together. Check incoming references and the overview's affected
  claims. Repair owned contradictions; route another owner's repair rather
  than silently duplicating or overriding its contract.
- Working documents retain a clear status and completion/retention trigger in
  their own text. Fold their useful results at completion under the project
  method; the navigation table does not carry a second lifecycle register.

## Architectural Principles

[Principles](principles.md) are read before architecture/design/development/review
work. Their bodies own the rules; this memory does not repeat them. Principle
amendments remain a sprint-close activity under the governing method.

## String Newtypes

Boundary identifier fields use the appropriate newtype, never bare `String`.
The [identifier vocabulary](interfaces.md#string-newtypes) distinguishes symbols,
type/trait names, module components, module paths and linker labels. Plain
strings remain for messages, documentation, source text and descriptions.

## Conventions

Types' cache serialization rules, runtime-only exceptions and shared predicates
live in the [types memory](../../crates/cranelisp-types/AGENTS.md). Do not infer
that every runtime type serializes merely because it belongs to the types crate.
[Facade-type ownership](principles/15-facade-types-live-with-behavior.md) governs
placement; crossing one crate boundary alone does not move a type into the shared
crate. [Source conventions](../../src/AGENTS.md) apply to source work.

## Public-API discipline

`pub(crate)` is the default; each public item needs rustdoc explaining the
cross-boundary promise. The root [inter-crate public-API gate](../../AGENTS.md#roles)
owns what counts as a change, the baseline-regeneration timing and the
checkpoint report. This section owns the criteria, the escalation test and the
record.

**Criteria.** `arch` approves a batch when every change in it holds all six.
The concern is the effect on each touched module's simplicity and
maintainability.

1. **A consumer decides it.** An added item has a named consumer in another
   crate that needs it now. A removed or narrowed item has none
   ([Principle 02](principles/02-narrow-interfaces.md)).
2. **The surface does not grow without replacing something.** A module's
   surface gets smaller or stays the same size. An addition is admitted when
   it removes a consumer-side derivation, wrapper or second copy of the same
   fact ([Principle 06](principles/06-complexity-has-a-budget.md),
   [Principle 07](principles/07-single-source-of-truth.md),
   [Principle 24](principles/24-resolve-once.md)).
3. **The fact stays with its owner.** The item lives in the crate that owns
   its behaviour, and no crate dependency is added or reversed
   ([Principle 15](principles/15-facade-types-live-with-behavior.md),
   [Principle 03](principles/03-dependency-flows-toward-stability.md)).
4. **A public value has one meaning.** Every producer gives it that meaning
   and no consumer has to work out which form it holds. Where a
   representation can enforce it, the representation does
   ([Principle 20](principles/20-model-invariants-by-representation.md),
   [Principle 18](principles/18-enforce-invariants-structurally.md)). No
   change lowers an invariant's grade in the
   [safety register](safety-invariants.md).
5. **Test access stays off the default surface.** An item only tests call is
   crate-private, or sits behind the owning crate's `test-support` feature
   ([Principle 05](principles/05-testability-is-structural.md)).
6. **A persisted or ABI shape changes with its version.** The schema or ABI
   version moves in the change-set that changes the shape
   ([Principle 14](principles/14-ffi-layout-discipline.md)).

**Escalation.** `arch` sends a change to the user with a brief, and does not
approve it, when any of these holds:

- it moves a responsibility or the ownership of a datum between modules, so
  a [bounded-context](bounded-contexts.md) statement changes;
- it adds a crate dependency, or a mechanism new to a facade: a public
  type, trait or entry point that replaces nothing;
- it changes behaviour the specification does not already require, or needs
  a specification change;
- it changes what an out-of-tree platform author compiles against;
- it fails a criterion and `arch` still recommends it.

The brief states the delta, the modules whose surface or contract steps, the
criterion at issue, the alternatives and `arch`'s recommendation.

**Batch record.** The last section of
[boundary types](interfaces.md#approved-changes-not-yet-in-source-s124) holds
one row per decided change until a phase checkpoint reports it: the exact
delta or a link to it, producers and consumers, schema or ABI effect, expected
baseline effect, who decided it and when, and the build order. A declined or
escalated change is a line there too, with the observation that would reopen
it or the decision it waits on.

- The implementing crate regenerates its baseline. Independent review
  compares source, rustdoc and the actual diff with the row.
- A design or change-set that needs a public change outside the record stops
  and returns to `arch`.
- At the phase checkpoint `arch` compares each regenerated diff with the
  record, reports it to the user and removes the reported rows.

Source rustdoc and BC statements replace retired facade-spec files.

## Facade convention — `lib.rs` mechanics

- `lib.rs` is the facade; there is no separate `facade.rs`. Arch reviews changes
  to its exports and crate-root documentation.
- Crate-root `//!` states the context in one to three paragraphs and links its
  BC statement. The facade re-exports implementation items and carries no logic.
- Consumers import types from their owning crate. Implementation facades do not
  re-export shared types, except the justified external-audience exception in
  Principle 15 (such as out-of-tree platform authors).
- Public DTOs use `#[non_exhaustive]` except explicit ABI layouts and closed sums
  whose exhaustive consumers are the safety contract. The precise exception
  set lives in [types public-surface mechanics](../../crates/cranelisp-types/AGENTS.md#public-surface-mechanics).
- Keep the existing sealed-marker-trait convention for cross-crate `CodeStore`
  and `LinkerStore` contracts; only arch extends that boundary.

## Baseline-diff discipline (Sprint 67 close)

The seven guarded library baselines are enumerated by
[the public-API guard](../../tests/public_api_relocations.rs). Root and
`cranelisp-exe-bundle` lack these baselines. Their public changes take the same
[gate](#public-api-discipline) with the source diff as the evidence.

Regenerate an affected baseline in the implementing change-set with the
canonical command:

```text
cargo +nightly public-api -s --omit auto-derived-impls -p <crate> > crates/<crate>/public-api.txt
```

- Use cargo-public-api 0.52 or newer. The guard enforces the version floor and
  fails on missing tooling or drift; it does not skip.
- The flags match the guard: one `-s` (`--simplified`) omits blanket impls;
  `--omit auto-derived-impls` removes derived implementations. Generated
  auto-trait implementations remain in the current format.
- Generate the production/default-feature surface, never with `test-support`.
- Co-land changed source, corresponding rustdoc/BC contracts and the generated
  diff. Review checks the approved and actual surfaces; `arch` compares the
  diff with the [batch record](#public-api-discipline) and reports it to the
  user at the phase checkpoint. A baseline is not a substitute for rustdoc
  currentness review.

**Approved format change, not yet implemented:**
[ACT-0955](../../sprints/actions/ACT-0955-omit-auto-traits-from-public-api-baselines.md)
owns the coordinated addition of `--omit auto-trait-impls` to this command and
the guard, with all seven baselines regenerated together. Until that migration,
use the command above. Its order:

1. A compile fence lands first, in the platform crate's module tests. It is
   test-only, changes no public item and leaves the platform baseline at +0.
   It asserts the promise exactly as the generated rows state it today:
   - `CLInt`, `CLBool`, `CLFloat` and `CLString` are `Send` and `Sync`.
   - `CLAdt<T>`, `CLIO<CL>` and `CLOwned<T>` are `Send` when their parameter
     is `Send`, and `Sync` when it is `Sync`. Each of the six implications is
     a generic assertion over every parameter the type's own bound admits
     (`CLAdtType`, `CLType`, `CLHeap`), not only over one instantiation.
   - The instantiations a platform author writes hold both: `CLAdt<M>` for a
     unit-struct marker `M`, `CLIO` over each scalar and over `CLAdt<M>`, and
     `CLOwned` over `CLString` and over `CLAdt<M>`.

   The promise is conditional because `CLAdtType` and `CLType` are public and
   unsealed, and the parametric types carry their parameter as a field or a
   `PhantomData`. Making it unconditional would be a new public bound or
   explicit impl; no consumer needs one, since a marker is a unit struct and
   every in-crate `CLType` is `Send + Sync`. A platform author's effect
   closure must be `Send + Sync`, so it may capture these values only while
   they are; no workspace crate is obliged to capture each of them. No other
   generated auto-trait row is a cross-crate promise: the negative rows
   follow from raw-pointer fields and no contract states them.
2. The seven baselines are regenerated in the present format on the final
   source tree. That diff carries the functional rows and is compared with
   the batch record and the sprint's approval packets.
3. The guard, `tests/AGENTS.md` and this section take the new flag together,
   and the baselines are regenerated again from the same tree. This diff must
   contain removals only, each a generated auto-trait row. Explicit
   `unsafe impl Send` and `Sync` rows remain; the `PlatformFn` row test in
   `tests/facade_pif_rows.rs` fails if they do not.
4. The guard's detection proof is repeated in the new format: a planted
   public item fails it and the clean tree passes.

The format choice is approved. `arch` reports the step 2 diff and the step 3
contraction to the user separately.
