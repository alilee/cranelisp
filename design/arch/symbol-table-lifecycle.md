# Symbol-table lifecycle

Current architecture contract owned by `arch`. This document explains the
shared lifecycle and publication responsibilities; exact signatures, error
variants and field layouts live in
[types source rustdoc](../../crates/cranelisp-types/src/module.rs) and
[the lifecycle records](../../crates/cranelisp-types/src/lifecycle.rs).
[BC §7](bounded-contexts.md) places this contract in the system.

The S121 implementation and API approvals are delivery history in
[the closed sprint](../../sprints/archive/sprint-121.md). The current
[executable-identity contract](s122-overload-reorder-publication.md) includes
S122's scheme-bearing key derivation and cross-class publication clarification.
Neither history nor this consolidation accepts outstanding sprint work.

## 1. Governing constraints

- One authored declaration has one canonical binding. Name exposures refer to
  that binding; they do not copy its lifecycle or compiled owner.
- A callable's scheme, lifecycle, slot and realization agree at settlement and
  publication. Non-concrete templates cannot supply executable slots or bodies.
- Types owns lifecycle and slot mutation. Integration owns language/ABI
  classification, transaction scheduling and executable-memory retention.
- Persisted indices survive cache restoration; process pointers and compiled
  owners do not serialize. Published indices cannot silently become fresh slots.

These are the operative outcomes of the earlier clean-sheet exercise. Its
incumbent-model comparisons, rejected migration waypoints and source censuses
remain in Git, not as instructions for another implementation wash.

## 2. Actors and responsibilities

| Actor | Responsibility |
|---|---|
| Typecheck | Read a staging-first declaration view; settle checked bodies, generic demands, callee facts and ownership summaries in unpublished tables. |
| Types | Validate declaration/lifecycle combinations; derive keys and slots; perform atomic table transitions; return displaced owners. |
| Backend | Compile concrete typed targets and populate their prepared GOT slots; consume the shared value-layout answer. |
| Binary/int | Select publication policy, hold code owners through commit or rollback, restore cache state and settle dependent redefinition effects. |
| Primitives/platform | Supply their declared origin, signature and realization through the appropriate registration funnels. |

Context interiors remain in their owning `design/` documents. This contract
does not prescribe their work queues or duplicate their test plans.

## 3. Resolution and canonical bindings

Each private `SymbolEntry` holds an optional canonical `Binding` and terminal
`NameCandidate` references for one spelling. There is no parallel trait-method
name map. The binding owns a `Decl`: a direct callable, overload family, macro,
trait-method declaration, type, trait, implementation shell or special form.

Candidate references carry canonical source identity and local visibility, not
copied schemes or lifecycle payloads. Same-source exposure deduplicates with
public visibility dominating private; distinct sources remain candidates.
`all_name_candidates` exposes both visibilities for dependency discovery;
`public_name_candidates` is the public projection.

Types supplies keyed, scope-aware resolution. Typecheck owns selection from
viable candidates without contaminating shared inference state with rejected
alternatives. Qualification and import behavior remain governed by
[the module specification](../../spec/08-modules.md) and
[the typecheck boundary](bounded-contexts.md).

## 4. Callable state and publication

### 4.1 The record

A directly named `Callable` owns its origin, documentation, source order and
one `CallableArm`. An arm owns its scheme, parameter names and `Life`.
Overloaded and macro declarations own their complete arm rosters (§5.3–§5.4).
There is no family-level dummy scheme and no separately indexed child binding.

### 4.2 The state machine

| State | Capability |
|---|---|
| `Declared` | Unsettled body; may retain a prior slot claim but is not callable. |
| `Template` | Checked generic source or synthesis recipe; no executable slot or concrete view. |
| `Concrete` | Checked concrete scheme and slot, with its realization and optional instance link. |
| `Inline` | Backend lowering at concrete use sites; no table slot. |
| `HostPromised` | Host-provided by-name realization; no table slot. |
| `Broken` | Retained slot and failure provenance; excluded from ordinary body compilation. |

Origin/state legality is validated by the table; the Rust enums alone do not
prove every combination legal. `Concrete` body realizations carry their view;
compiled owners are runtime-only and may be absent before compilation.

### 4.3 Slot identity

Slot claims live in concrete or broken arms, retained declaration priors, and
private retirement tombstones. Allocation derives its unavailable set from
these claims; a separate stored allocation cursor is not another authority.
The GOT is the single runtime home of callable pointers.

A staged table is an unpublished alternative world. Its provisional slot
numbers do not authorize live reuse. Integration supplies the semantic decision
and types derives the final slot plan. Published retirement preserves the old
index in tombstones; code-page retention is the separate integration half of
that same lifetime obligation. Manifest-backed platform slots share this index
space and remain tied to descriptor order.

### 4.4 Enforcement and publication boundary

**Authoring.** Checked settlement updates the final scheme, AST/view and callee
facts together. A body change clears obsolete compiled, value-use and ownership
facts. `publish_body_ownership` accepts an uncompiled concrete target and updates
its annotated view and persisted summary together. Family installers take
slot-free drafts, validate the complete roster and mint its slots atomically;
callers cannot bypass slot ownership by constructing pre-slotted drafts.

Non-callable installation/removal and prior-free declaration discard remain
narrow operations. Metadata-only `set_plain_callable_docstring` accepts a
canonical local Plain callable in any legal lifecycle state. It changes only
its docstring and normal mutation revision, not its slot, owner or state;
candidate-only spellings are not mutable aliases.

Unpublished constructor/accessor replacement preserves candidate exposures.
The dedicated template/concrete operations require the same synthetic identity,
a null provisional GOT row and no compiled owner. They record no tombstone for
that unpublished displacement. Live replacement instead uses publication below.
Opaque retained-callable and staged-impl-shell tokens support unpublished
rollback; they cannot reclaim published code or overwrite an intervening change.
Trait-registration ordering is in §5.7.

**Publication.** Integration classifies the complete old/staged declaration;
types validates the requested decision and candidate before changing live state.
`publish_staged` accepts owner-free staging. `publish_compiled_staged` additionally
requires an exact `CallableTarget`-keyed owner for every staged concrete backend
body and no extra owners. Success publishes the complete module candidate in
one swap; failure preserves live state and returns all submitted owners through
`CompiledPublicationRejection::into_parts`.

- `PreserveAbi` reuses compatible slotted generations; overload matching follows
  complete language signatures, not generation-local ordinals.
- `ChangeAbi` retires prior slotted generations and gives slotted replacements
  fresh slots. An explicit decision can retire a live slotted binding to
  absence only when its key is wholly absent from staging.
- Omission alone never removes a live binding. Missing or incompatible targets,
  duplicate/incomplete decisions and invalid resulting candidates refuse the
  whole transaction.
- One `PublicationRecord` describes each affected binding. Its nested body
  records carry old/new targets, slots and every displaced owner, including
  removed family arms. Non-callable records have no body movements.

The types planner checks structural pairing and slot eligibility. Integration
owns language/ownership ABI comparison; types does not repeat that comparison
as a second policy engine. Caller-free language-type changes, including
Plain/overloaded transitions, follow the existing retirement rule; they do not
qualify for cross-class `PreserveAbi` merely because machine arities match.
See the [identity contract](s122-overload-reorder-publication.md).

**Pointers and owners.** Backend writes the prepared GOT cells after batch
finalization. Integration snapshots touched cells before codegen. If subsequent
compiled publication refuses, integration recovers and holds every submitted
owner while restoring old pointers and nulling fresh cells. Only after pointer
compensation may those owners be released or retained for the session.
Successful publication transfers new owners into live bodies and displaced
owners into integration's retention pool. A fallible per-symbol owner loop
following a visible owner-free commit is not equivalent to this transaction.

`publish_compiled_owner` serves an already-concrete body and returns its previous
owner, or the submitted owner on refusal. `mark_broken` returns the displaced
owner and retained slot; integration owns the trap code and message lifetime.
Types never chooses executable-memory retention policy. Existing module cadence
serializes preparation/publication; this boundary adds no revision-token protocol.

### 4.5 Origins

Origin identifies declaration semantics such as a plain function, constructor,
accessor, trait implementation, Rust primitive or platform effect. It is
orthogonal to lifecycle. Overload arms and macro clauses obtain their parent
identity through nesting, not duplicated `group` fields.

### 4.6 Realization

A concrete realization identifies who populates its slot: backend body, Rust
extern shim, DLL or a facade over a uniform body. `codegen_targets` projects
concrete backend bodies and their typed targets. By-name host promises and
inline lowering are not mistaken for such bodies. A backend-native label is an
implementation artifact, not a second language or realization identity.

## 5. Declaration populations

### 5.1 Single-signature definitions

Checked source definitions settle through the common template/concrete funnels.
Their authoritative final scheme determines settlement; wrapping a residual
type in an unquantified scheme does not make it concrete.

### 5.2 Templates and instances

An instance is a new concrete realization with an `InstanceLink` to its selected
template. `MonoDemand` carries the same complete substitutions plus a diagnostic
site. The substitution and replay contract is
[the instance identity funnel](interfaces.md#instance-identity-funnel);
S122's [uniform executable identity](s122-overload-reorder-publication.md) owns
the scheme-bearing key derivation.

Typecheck rechecks in the defining scope and installs in the demanding module.
`install_instance` derives the storage key from the settled instance signature
and authored owner, stores the link, and returns the key and slot. Ordinary
concrete birth cannot inject an instance link. Install and restored-table
validation reject a key/signature mismatch. No consumer recovers this relation
from a written alias or a private backend label.

### 5.3 Declaration families

One authored overloaded declaration owns documentation, source order and its
whole ordered arm roster. Each arm has a checked generation-local ordinal and
its own scheme/lifecycle. Typecheck selects a `CallableTarget::OverloadArm`;
backend consumes that target rather than resolving a generated child name.

The entire family validates and publishes atomically. ABI-preserving overload
publication pairs complete alpha-normalized schemes and conserves their slots
and owners across reorder. Generic instance replay additionally remaps the old
selector to the corresponding new arm while retaining stable executable keys;
the S122 identity contract specifies that boundary. Declining a removed demand
does not silently preserve an incompatible old realization.

### 5.4 Macros

A macro declaration owns its source, documentation, patterns and compiled clause
roster. Macro order is semantic: matching uses pattern and ordinal rather than
overload signature correspondence. Clauses have no independent language names.
Shrinking or growing the roster publishes one aggregate and returns removed
owners through the same body records.

Only committed clauses may execute. A successful source-ordered checkpoint is
not undone by a later form, and dependency modules remain separate transactions.
The architecture is [macro availability](macro-availability-model.md); private
checkpoint-effect custody and dependent cure belong to Binary/int, with the
boundary recorded in [BC §6](bounded-contexts.md).
No receipt, temporary execution table or retry continuation crosses this types API.

### 5.5 Primitives

Primitives use the common born-settled registration funnels. Extern shims carry
concrete slots; inline and host-promised entries do not. Declared ownership
summaries survive extern/inline registration. Inline value-position wrappers
remain backend-local emission artifacts, not template instances or table entries.

`TemplateBody::UniformRust`/`Realization::FacadeOf` express an available generic
realization mechanism, not a claim about the current production roster. The
actual roster and its obligations belong to
[the primitives design](../primitives/primitives.md) and
[the backend release contract](../backend/non-concrete-release-contract.md).

### 5.6 Platform effects

Platform registration validates concrete signatures and claims descriptor-order
slots against the DLL's GOT. Origin records scheduling and polling facts;
`Realization::Dll` records pointer production. The platform ABI and IO layouts
are owned by [the platform interface](platform-interface.md) and platform source,
not by symbol-table cache migration history.

### 5.7 Trait declarations and implementations

A `TraitMethodRecord` is an unslotted resolution/type-inference terminal at the
canonical `Trait.method` key. Installing it atomically exposes the bare-name
candidate; it is not a permanently declared executable body. Its trait home is
read directly rather than reconstructed by scanning trait declarations.

Implementation bodies are ordinary callable entries in the writer module;
the trait-home discovery shell and writer-side `WrittenTraitImpl` persistence
remain distinct responsibilities. Their current contract is
[the trait-impl carrier](trait-impl-cache-carrier.md).

Fresh registration retains method priors, stages the shell, checks every method,
then upserts the writer record as its final fallible table act before committing
the tokens. Failure restores methods and then the shell; the old writer record
has not been changed. Cache restoration uses conflict-checked enrollment instead
of the provisional staging operation. Mono bodies settle concrete; generic/HKT
bodies remain templates until their concrete demand settles.

### 5.8 Constructors and accessors

ADT synthesis supplies slot-free recipes or non-callable bindings through the
shared types builder. Concrete synthesized bodies use real concrete node types;
generic constructors/accessors retain synthesis recipes, not fabricated concrete
views. Product-type facets remain origin metadata; bare member exposures refer
to canonical constructor/accessor bindings. The types-owned field/layout
projections prevent backend or typecheck from rebuilding declaration policy.

### 5.9 Imports and candidates

Imports/re-exports expose resolved terminal identities through the same
per-spelling entry. They copy no lifecycle state and cannot orphan a callable's
slot merely by making a name ambiguous. Local candidate shape is validated by
types; cross-module terminal validation requires restored dependencies before
publication. Language collision/visibility policy remains with resolution and
its specification, not a second import-specific symbol map.

## 6. Enforcement

Private table mutation and slot construction prevent ordinary consumers from
bypassing settlement/publication. Complete candidate validation protects atomic
updates. These mechanisms do not make every illegal combination unrepresentable:
source rustdoc states each public operation's accepted states and refusals.
Historical impossibility tables and planned falsifiers are not current evidence.
Current assurance belongs to [the QA plan](../../tests/plan/PLAN.md).

## 7. Residual responsibilities

- Clone/serde can reproduce values without passing authoring funnels. Load and
  publication validation recheck lifecycle, key, slot and candidate consistency.
- `CallableSlot` is Copy; Rust does not prove conservation of a copied claim.
  Table transitions and claim/tombstone validation enforce conservation.
- Origin/state legality is a checked table invariant, not a per-origin enum.
- Unpublished rollback checks that a fresh slot has not acquired code or a
  non-null pointer; its token alone cannot prove transaction timing.
- Demander-local instances may exist in several modules. Their links preserve
  common provenance without introducing a global instance registry.

These are limits of the representation, not new debt waivers or a claim that
all concreteness and ownership findings are closed.

## 8. Boundary rationale

Keeping lifecycle beside its scheme avoids a second serialized symbol-to-slot
map. Separating pointer storage from persisted claims allows cache restoration
without serializing process addresses. Returning owners preserves integration's
retention authority while keeping live mutation inside types. Slot-free family
drafts avoid exporting an allocator merely to make public records constructible.

## 9. Migration provenance

The unified lifecycle replaced fragmented per-kind states and the public symbol
map. Completed source inventories, API forecasts, phase ordering and schema-window
instructions live in Git and the closed S121 outcome. They do not schedule a
second wash or override later schema versions. Source rustdoc and generated
baselines describe the implemented APIs; exact future API changes retain the
repository's two user gates. Active S122 identity work has its own retained
contract linked above.
