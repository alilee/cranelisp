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
| [Core and library boundary](core-library-boundary.md) | Technical determinations for spec S124-Q16; awaiting the user's confirmation, approves nothing. |
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
checkpoint report. This section owns the criteria, the obligations, the
escalation test and the record.

**Criteria.** `arch` asks three questions of each change, for every module
whose surface or contract it touches. It approves the change when the honest
answer to each is yes. The bullets name evidence `arch` looks at, for example;
they are not further criteria.

1. **Bounded context** — does the module maintain its cohesive and coherent
   intent?
   - The item lives with the behaviour that owns its fact, and no datum or
     responsibility changes owner
     ([bounded contexts](bounded-contexts.md),
     [Principle 15](principles/15-facade-types-live-with-behavior.md)).
   - No crate dependency is added or reversed
     ([Principle 03](principles/03-dependency-flows-toward-stability.md)).
   - An added item serves a consumer in another crate that needs it now; a
     removed item has none
     ([Principle 02](principles/02-narrow-interfaces.md)).
2. **Simple API** — does the public API simply and clearly align with and
   express the module's intent, for example by one obvious path to each
   outcome?
   - An addition replaces a consumer-side derivation, wrapper or second copy
     and does not add a second path
     ([Principle 06](principles/06-complexity-has-a-budget.md),
     [Principle 07](principles/07-single-source-of-truth.md),
     [Principle 24](principles/24-resolve-once.md)).
   - A consumer uses what it is given without naming, wrapping, narrowing or
     discarding it.
   - Test-only access is off the default surface
     ([Principle 05](principles/05-testability-is-structural.md)).
3. **Strongly typed** — do the definitions use type representation so that
   invalid states cannot be expressed?
   - A public value has one meaning from every producer, and no consumer
     works out which form it holds.
   - A distinction or invariant a representation can carry is carried by it,
     not by a convention, an unconstrained collection or an option with one
     inhabitant in use
     ([Principle 20](principles/20-model-invariants-by-representation.md),
     [Principle 18](principles/18-enforce-invariants-structurally.md)).
   - No invariant's grade in the [safety register](safety-invariants.md)
     drops.

Where a better-typed or simpler realisation exists at similar cost, `arch`
states it exactly and approves that one. Where it would be a larger change,
`arch` says so in the record and does not widen the row.

**Obligations.** These are mechanical and hold whatever the answers.

- A persisted or ABI shape changes with its schema or ABI version, in the
  same change-set
  ([Principle 14](principles/14-ffi-layout-discipline.md)).
- A change that needs a specification change, or behaviour the specification
  does not already require, waits for the user's ruling
  ([root delivery rule](../../AGENTS.md#delivery)).

**Escalation.** `arch` sends a change to the user with a brief, and does not
approve it, when:

- after the change the honest answer to one of the three questions is no for
  a touched module, and `arch` still recommends it; or
- the change alters a module's intent: its
  [bounded-context](bounded-contexts.md) statement changes, including what an
  out-of-tree platform author compiles against.

The brief states the delta, the modules whose surface or contract steps, the
question at issue, the alternatives and `arch`'s recommendation.

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
cargo +nightly public-api -s --omit auto-derived-impls --omit auto-trait-impls -p <crate> > crates/<crate>/public-api.txt
```

- Use cargo-public-api 0.52 or newer. The guard enforces the version floor and
  fails on missing tooling or drift; it does not skip.
- The flags match the guard: one `-s` (`--simplified`) omits blanket impls;
  `--omit auto-derived-impls` removes derived implementations;
  `--omit auto-trait-impls` removes generated auto-trait implementations.
  Explicit `unsafe impl Send` and `Sync` rows remain.
- Generate the production/default-feature surface, never with `test-support`.
- Co-land changed source, corresponding rustdoc/BC contracts and the generated
  diff. Review checks the approved and actual surfaces; `arch` compares the
  diff with the [batch record](#public-api-discipline) and reports it to the
  user at the phase checkpoint. A baseline is not a substitute for rustdoc
  currentness review.

**Auto-trait promises the baselines do not show.** No baseline holds a
generated auto-trait row, so an auto-trait property that is a cross-crate
promise has its own check.

- The platform crate's value types: the compile fence
  `crates/cranelisp-platform/src/tests.rs::marshalling_types_are_send_and_sync_compile_fence`.
  - `CLInt`, `CLBool`, `CLFloat` and `CLString` are `Send` and `Sync`.
  - `CLAdt<T>`, `CLIO<CL>` and `CLOwned<T>` are `Send` when their parameter
    is `Send`, and `Sync` when it is `Sync`, for every parameter the type's
    own bound admits.
  - The promise is conditional because `CLAdtType` and `CLType` are public
    and unsealed, and the parametric types carry their parameter as a field
    or a `PhantomData`. An unconditional promise would be a new public bound
    or explicit impl, which no consumer needs: a platform author's effect
    closure must be `Send + Sync`, so it captures these values only while
    they are.
- `PlatformFn`'s explicit `Send` and `Sync` rows:
  `tests/facade_pif_rows.rs::platform_send_sync_claims_match_invariants`.
- No other generated auto-trait row is a cross-crate promise. The negative
  rows follow from raw-pointer fields and no contract states them. A change
  that makes one a promise adds its check in the same change-set.
