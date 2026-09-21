# design/arch/

Owned by `arch`: system boundaries, shared technical contracts, architecture
principles and sequence diagrams. Root [role ownership](../../CLAUDE.md#roles)
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
| [Bounded contexts](bounded-contexts.md) | Responsibilities, dependency direction and shared guarantees. |
| [Boundary types](interfaces.md) | Narrative companion to the types crate and its rustdoc. |
| [Architectural principles](principles.md) | Sole membership index for principle bodies. |
| [Symbol-table lifecycle](symbol-table-lifecycle.md) | Declaration ownership, slot conservation and atomic publication. |
| [Concrete codegen boundary](concrete-boundary-type.md) | Concrete-only typed body contract. |
| [Backend keyed consumption](backend-keyed-consumer.md) | Resolved identities at the typecheck/backend boundary. |
| [Typed resolution carriers](typed-resolution-carrier.md) | VarRef and ApplyRef transport contract. |
| [Constructor keys](dotted-ctor-canonical-keys.md) | Constructor storage-key grammar and its writer, reader and codegen-transport obligations. |
| [Scoped module aliases](module-alias-scoped-lookup.md) | Referring-module lookup and shared key derivation. |
| [Resolve home before enumeration](resolve-home-enumeration.md) | Display and index enumeration rooted at the resolved home; complete source coverage. |
| [Prelude and explicit imports](prelude-import-convergence.md) | One candidate resolution for every name origin; REPL introspection's obligations to it. |
| [Annotated S-expressions](annotated-sexp-node.md) | Read-time annotation representation and transport. |
| [Macro availability](macro-availability-model.md) | Source-order availability and publication. |
| [Macro expansion ownership](macro-expansion-ownership.md) | Frontend, typecheck and integration responsibilities. |
| [Ownership inference](ownership-inference.md) | Interprocedural ownership queries and their consumers. |
| [Safety invariants](safety-invariants.md) | Maintained invariant register and enforcement limits. |
| [Total concreteness](total-concreteness.md) | Approved invariants and retained rationale. |
| [Types-first concreteness reasoning](concreteness-types-first.md) | Retained design reasoning and forty-row dispositions. |
| [Trait-implementation persistence](trait-impl-cache-carrier.md) | Writer records, discovery shells and restoration. |
| [Platform interface](platform-interface.md) | DLL authoring, generated schemas and host boundary. |
| [Effect concurrency](effect-concurrency.md) | Ratified, delivered language-level concurrency architecture and its implementation limits. |
| [Introspection ownership](d1-introspection-repl-only.md) | REPL-only collection boundary. |
| [Embedded REPL agent](repl-embedded-agent.md) | Ratified architecture and staged capability scope. |
| [REPL styling](repl-styling-seam.md) | Shared formatter and styling contract. |
| [Display protocol](display-protocol.md) | Type-directed rendering design and its implementation gates. |
| [Execution tracing](tracing.md) | Trace-node, backend and intrinsics responsibilities. |
| [Test discovery and error capture](test-discovery.md) | Language test discovery, invocation and runtime capture. |
| [Uniform executable identity](s122-overload-reorder-publication.md) | Approved signature identity and implemented types key API. |
| [Shared document checker](s122-shared-document-checker.md) | Shared-tool boundary and project integration contract. |
| [Byte-backed text exploration](byte-backed-text.md) | Non-normative options; no language or implementation authority. |
| [Ownership-stratum options](ownership-stratum-options.md) | Structural option paper; retained choices are not approval. |
| [Release-backend proposal](release-llvm-backend.md) | Unratified future proposal; no LLVM work authorized in S122. |
| [Performance backlog](backlog/performance.md) | User-approved suspended scope and future re-entry decisions. |

## Document collections

| Collection | Purpose | Navigation |
|---|---|---|
| `architecture-contracts` | Current architecture contracts and explicitly retained design proposals. | The top-level products linked above. |
| `architecture-decisions-drain` | The decision-label index, and the five decision records that tests still cite by section. | [Decision labels](decisions/README.md). |
| `architecture-filings` | Actionable architecture filing register, retained until its owning obligation is discharged. | [Open filings](fixmes/). |
| `architecture-sequences` | Current execution and lifecycle sequence diagrams with their navigation and rendering conventions. | [Sequence guide](sequences/README.md). |
| `architecture-archive` | Frozen superseded architecture records retained as historical reference. | [Archive](archive/); historical references retain their recorded meaning. |

The [principles memory](principles/CLAUDE.md) governs principle authoring;
[the principles index](principles.md) is the membership authority. Collection
membership does not waive live references or settle a file's outstanding work.

## Archive (`archive/`)

The existing archive is historical reference, not current architecture. Its
bounded historical-reference policy does not cover `decisions/`.
Retention follows the project method: Git suffices for ordinary working history;
retain a document only for useful evidence or rationale beyond that history.
Do not move obsolete prose into the archive merely to preserve file counts.

## Decision labels

Source, tests and designs cite rulings as "Decision N". The
[label index](decisions/README.md) resolves each label to the ruling's current
home. Do not create Decision files; write a new cross-context commitment into
bounded contexts or a focused contract. A remaining record retires when its
contract is restated in that home and `test` repoints the `// spec:` citations
in the same change. Open filings retain their own lifecycle.

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
live in the [types memory](../../crates/cranelisp-types/CLAUDE.md). Do not infer
that every runtime type serializes merely because it belongs to the types crate.
[Facade-type ownership](principles/15-facade-types-live-with-behavior.md) governs
placement; crossing one crate boundary alone does not move a type into the shared
crate. [Source conventions](../../src/CLAUDE.md) apply to source work.

## Public-API discipline

`pub(crate)` is the default; each public item needs rustdoc explaining the
cross-boundary promise. Root [API approval rules](../../CLAUDE.md#roles) require
exact pre-implementation approval for public surface and consumer-edge changes,
then confirmation of the generated delta before the wave passes. Phase or wave
approval does not replace either gate.

`arch` owns the contract and approval packet; the implementing crate regenerates
its baseline, and independent review compares the source, rustdoc and actual
diff against the approval. A new or mismatching item or consumer edge returns to
that gate. Source rustdoc and BC statements replace retired facade-spec files.

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
  set lives in [types public-surface mechanics](../../crates/cranelisp-types/CLAUDE.md#public-surface-mechanics).
- Keep the existing sealed-marker-trait convention for cross-crate `CodeStore`
  and `LinkerStore` contracts; only arch extends that boundary.

## Baseline-diff discipline (Sprint 67 close)

The seven guarded library baselines are enumerated by
[the public-API guard](../../tests/public_api_relocations.rs). Root and
`cranelisp-exe-bundle` lack these baselines; their public changes still require
contract review and the applicable user approval.

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
  diff. Review checks the approved and actual surfaces; the user confirms the
  actual diff before promotion. A baseline is not a substitute for rustdoc
  currentness review.

**Approved format change, not yet implemented:**
[ACT-0955](../../sprints/actions/ACT-0955-omit-auto-traits-from-public-api-baselines.md)
owns the coordinated addition of `--omit auto-trait-impls` to this command and
the guard, with all seven baselines regenerated together. Preserve required
Send/Sync and other auto-trait obligations with direct fences where omission
would remove their only check. The format choice is already approved; its
actual generated contraction still requires user confirmation separately from
functional API changes. Until that migration, use the command above.
