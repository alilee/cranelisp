# Sprint 121 inter-crate public-API review

> **Owner:** `sprint` coordinates; `arch` owns the technical packet; the user
> decides.
>
> **Status:** HOLD — EXACT API PACKET PREPARATION. The user approved the
> staged/live architecture in `design/arch/s121-lifecycle-public-api-review.md`
> on 2026-09-02. No method, signature, carrier or baseline line below is
> approved unless its decision row records the user's explicit approval. The
> generated post-implementation diff is a separate approval.

The user approved the layered `Binding -> Decl -> Callable -> Life`
representation, table-owned enforcement of lifecycle/slot transitions, and
module-atomic staged/live publication on 2026-09-02. Those decisions do **not**
approve the method inventory below or any exact API line. Architecture is now
deriving the minimum exact facade from concrete consumer workflows: integration
chooses commit policy; types validates and applies the complete transaction and
returns displaced compiled-code owners.

This record separates the public changes already present in the worktree by
delivery wave. The literal as-built evidence is:

```text
git diff -- crates/cranelisp-types/public-api.txt
git diff -- crates/cranelisp-typecheck/public-api.txt
```

The current generated diffs are not themselves an approved package: the types
baseline contains W1 lifecycle work and W3 name-candidate work together.

## Packet A — W1 lifecycle foundation (being re-derived)

**No API decision is currently requested.** This inventory is being revised to
match the approved publication boundary before returning as the line-level
public-API packet. It does not include the W3 general candidate API or the
W4 typecheck entry point listed under “Excluded from Packet A”.

### Boundary outcome

The public symbol-table datum changes from an openly constructible
`ModuleEntry` sum with lifecycle state spread across `DefKind`,
`UserFnState`, `CtorState` and `PrimitiveBody` to a lifecycle binding nested
inside one entry for each visible spelling. The following is conceptual; the
exact `SymbolEntry`/candidate carrier and the indicated `BindingBody` variants
are not yet approved public API:

```rust
SymbolTable.symbols = HashMap<Symbol, SymbolEntry<C>>
SymbolEntry<C> = { canonical: Option<Binding<C>>, candidates: Vec<CandidateRef> }
CandidateRef = { source: FQSymbol, visibility: Visibility }
Binding<C> { visibility, body: BindingBody<C> }
BindingBody<C> = Alias { source } | Ambiguous | Decl(Decl<C>) // under review
Decl<C> = Callable(Callable<C>) | TraitMethod(TraitMethodRecord)
        | Group(Group) | Type(TypeRecord) | Trait(TraitRecord)
        | ImplShell(ImplShell) | SpecialForm(SpecialFormRecord)
Callable<C> { scheme, param_names, docstring, seq, origin, life: Life<C> }
Life<C> = Declared { prior } | Template { ... } | Concrete { ... }
        | Inline | HostPromised | Broken { ... }
```

There is one name index, not a parallel trait-method map. Imports, re-exports,
derived members and declarations expose their canonical identities through the
same per-spelling candidate entry. W3 must decide the exact carrier and whether
`BindingBody::Alias` and `BindingBody::Ambiguous` survive. In particular, a
call-site ambiguity cannot be represented only by a sentinel that has already
discarded the candidate identities needed for contextual or type-directed
selection.

Consumers may inspect the binding, declaration facet and lifecycle state, but
they may no longer construct arbitrary symbol-table entries, mutate the symbol
map, allocate a raw next slot, or independently combine a scheme, state, slot,
realization and ownership facts. Those changes go through role-specific
`SymbolTable` operations.

### Packet A1 — live publication and compiled-owner conservation

**Status: REALIZED, INDEPENDENTLY REVIEWED, AND BASELINED.** The exact A1
surface is implemented and its focused types suite
is green. Independent review found one unruled transition inside
`publish_staged`: a slotted `RustPrimitive` could be replaced by slotless
`Inline` or `HostPromised` despite the only available retirement provenance
being `TemplateFlip`. The user ruled on 2026-09-02 that both transitions are
rejected; only an actual `Template` replacement may take that retirement arm.
Both refusals are pinned and the finding-scoped independent re-review passed
with no residuals. The user accepted the exact generated combined A1/Packet-B
baseline on 2026-09-02 and the canonical `cargo-public-api` 0.52 output was
committed to `crates/cranelisp-types/public-api.txt`. This packet adds no
overload/candidate API and does not approve the staged-authoring or
born-settled method families below.

The caller supplies a decision only where two slotted callable generations
create a genuine ABI choice. New, prior-slotless, newly-slotless and
non-callable cases are determined by the table from the old and staged states;
making integration restate those facts would add disagreement paths without
adding policy.

```rust
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StagedPublicationDecision {
    PreserveAbi { symbol: Symbol },
    ChangeAbi { symbol: Symbol },
}

#[non_exhaustive]
#[must_use = "displaced compiled owners must be retained before publication completes"]
pub struct PublicationRecord<C: CodeStore = ()> {
    pub symbol: Symbol,
    pub prior_was_callable: bool,
    pub prior_slot: Option<CallableSlot>,
    pub published_slot: Option<CallableSlot>,
    pub displaced_owner: Option<C>,
}

#[must_use = "the rejected compiled owner must be recovered with into_parts"]
pub struct CompiledOwnerRejection<C: CodeStore = ()> { /* private fields */ }

impl<C: CodeStore> CompiledOwnerRejection<C> {
    pub fn reason(&self) -> &LifecycleError;
    pub fn into_parts(self) -> (LifecycleError, C);
}

#[non_exhaustive]
#[must_use = "the displaced compiled owner and retained slot must be handled"]
pub struct BrokenTransition<C: CodeStore = ()> {
    pub slot: CallableSlot,
    pub displaced_owner: Option<C>,
}

// New variant on the existing non-exhaustive error enum.
pub enum LifecycleError {
    // existing variants ...
    WrongModule {
        expected: ModuleFullPath,
        actual: ModuleFullPath,
    },
}

impl<C: CodeStore> SymbolTable<C, ()> {
    pub fn publish_staged(
        &mut self,
        staging: SymbolTable<C, ()>,
        decisions: &[StagedPublicationDecision],
    ) -> Result<Vec<PublicationRecord<C>>, LifecycleError>;
}

impl<C: CodeStore, L: LinkerStore> SymbolTable<C, L> {
    pub fn publish_compiled_owner(
        &mut self,
        name: &Symbol,
        owner: C,
    ) -> Result<Option<C>, CompiledOwnerRejection<C>>;

    // Existing method; return type changes from Result<(), LifecycleError>.
    pub fn mark_broken(
        &mut self,
        name: &Symbol,
        error: BrokenProvenance,
    ) -> Result<BrokenTransition<C>, LifecycleError>;
}
```

`publish_staged` consumes an unpublished table for the same module. Before any
live mutation it validates the staging lifecycle, absence of compiled owners,
decision uniqueness and exact decision coverage at ABI-choice points, binding
collision rules, and the complete resulting slot map. Rejection consumes the
discarded staging table but leaves live state unchanged. Success publishes the
whole cluster and returns one record per staged binding.

The method is intentionally available on `SymbolTable<C, ()>`, matching its
only production consumer. The reserved `L` parameter has no current live-
publication consumer or settled displacement semantics; claiming a generic
`L` transaction now would create an untested owner-drop contract. If a real
module-level linker owner appears, its publication/retention requirements
return to architecture before this bound is widened.

`PublicationRecord` contains only facts owned by types. It deliberately does
not repeat integration's `RedefKind`, per-symbol precision or dependent-
recompilation policy. Integration joins those existing decisions to the
returned symbol/slot facts and moves every `displaced_owner` into its retention
pool before codegen. All ownership-bearing carriers are `#[must_use]`; Rust
cannot make retention logically unskippable across this dependency boundary,
so integration tests additionally assert that every returned owner enters the
session retention pool before a slot is patched.

`publish_compiled_owner` accepts only `Life::Concrete` with
`Realization::Body`, replaces no other lifecycle field, and returns the prior
owner. On rejection, `CompiledOwnerRejection::into_parts` returns both the
reason and submitted owner; ownership cannot disappear through an error path.
The same method serves fresh JIT output, recompilation and cache-hit linker
restoration.

`mark_broken` keeps the existing slot on `Life::Broken` and returns both that
slot and any body owner it displaced. Integration retains the owner, patches
the slot to its retained trap stub and records provenance.

**Producer and consumers.** `cranelisp-types` owns all four carriers and three
methods. The binary integration layer is the sole production consumer. Backend
continues to write the finalized pointer to the GOT and returns its compilation
artefacts; it neither constructs `Code` nor gains a dependency edge. Typecheck
continues to author staging and gains no A1 dependency.

**Compatibility and persistence.** A1 is an intentional source-breaking
addition/change inside the already-open W1 public-surface migration. Its
runtime-only carriers add no serde field and therefore no cache-schema change
beyond W1's approved 24 -> 25 transition. It changes no platform C ABI.

**Forecast `public-api.txt` effect.** Add the four named carriers and their
listed variants/fields/methods; add `LifecycleError::WrongModule`; add the two
`SymbolTable` methods (with `publish_staged` on the `L = ()` impl); replace the
one `mark_broken` return line. Derived auto-trait lines follow mechanically. No
other crate baseline changes in A1 because the binary integration layer has no
`public-api.txt`.

### Provisional W1 vocabulary inventory — held

This is the vocabulary generated by the superseded one-binding-per-spelling
implementation. It is retained to account for work already present, not as an
exact API proposal. The one-entry/many-candidates decision requires W1/W3 to
re-derive the affected types, reads and mutation facade before they return for
review. Packet A1 above and Packet B below are the accepted exact subsets; this
provisional remainder is not approved by either decision.

W1 removes these public types:

```text
ModuleEntry       DefKind          UserFnState      PrimitiveBody
CtorState         DefBuilder       ConstrainedFn    ParametricFn
```

W1 adds these lifecycle and declaration types:

```text
Binding                 BindingBody            Decl
Callable                Life                   CallableOrigin
Realization             TemplateBody           TemplateKind
ConstrainedMeta         BrokenProvenance       LifecycleError
RetiredSlot             RetireReason           InstanceLink
MonoDemand              Group                  GroupKind
TypeRecord              TraitRecord            TraitMethodRecord
ImplShell               SpecialFormRecord      SynthSpec
RetainedCallables       StagedImplShell
```

The superseded implementation changed the following boundary reads from
`ModuleEntry<C>` to `Binding<C>`. Their target result is now held because some
reads may need to expose the general per-spelling entry or a narrower
projection rather than a bare binding:

```text
Resolved::entry
SymbolTable::{get, all_symbols, public_symbols, defined_symbols}
View::{lookup, iter}
for_each_in_module
resolve_terminal_entry_and_home
```

The superseded `Binding` supplied this construction/read facade; its alias and
ambiguity operations are specifically reopened:

```text
alias, ambiguous, declaration, is_public, callable, trait_method,
callable_got_slot, is_callable_target, type_def_info, mode_summary,
value_use, codegen_view, callees
```

The new records expose their documented data fields and only these additional
constructors/derivations:

```text
BrokenProvenance::new       ConstrainedMeta::new
Group::{macro_group, overload}
InstanceLink::{new, instance_key}
MonoDemand::{new, instance_link, instance_key}
SpecialFormRecord::new      SynthSpec::new
TraitMethodRecord::new      TraitRecord::new
```

`SymbolTable::symbols` and `SymbolTable::next_got_slot` cease to be public.
The old `ModuleEntry` construction/read helpers and raw
`SymbolTable::{insert, allocate_got_slot, mint_callable_slot}` facade retire.

The replacement mutation facade is grouped by responsibility:

```text
Birth/install:
  declare, install_binding, install_template, install_concrete,
  install_instance, install_extern, install_inline,
  install_host_promised, install_platform, install_trait_method

Checked settlement and publication:
  update_declared_scheme, settle_template, settle_concrete,
  settle_checked_template, settle_checked_concrete,
  replace_callees, publish_body_ownership, set_value_use

Transaction/redefinition:
  discard_declared, remove_non_callable, retain_callables,
  rollback_callables, stage_trait_impl_shell,
  rollback_trait_impl_shell, upsert_written_trait_impl,
  retire_abi_changing, mark_broken

Validation/read:
  retired_slots, validate_lifecycle
```

The generated signatures and fields in
`crates/cranelisp-types/public-api.txt` and the public definitions in
`crates/cranelisp-types/src/lifecycle.rs` and
`crates/cranelisp-types/src/module.rs` are implementation evidence, not an
approved API. The replacement list must return as an exact user-review packet,
and any additional public method remains a new user decision.

### Associated W1 boundary changes

The ADT builder stops accepting a caller-allocated GOT slot and returns
declarative specs for installation through the lifecycle facade:

```rust
// removed argument: got_slot: usize
AdtCtorSpec::new(name, fields, docstring, internal)

build_adt_entries<C>(...) -> Vec<(Symbol, AdtEntrySpec<C>)>
AdtEntrySpec<C> = Binding(Binding<C>) | Callable(AdtCallableSpec)
```

Two previously planned, independently useful types-owned helpers are included
in this Packet A decision and share the one types baseline regeneration without
changing lifecycle semantics:

```rust
quote_head(&[Sexp]) -> Option<QuoteHead>
QuoteHead = Quote | Quasiquote | Unquote | UnquoteSplicing

module_alias_key(&ModuleFullPath, &str) -> ModuleFullPath
substitute_module_alias(
    &ModuleAliases,
    &ModuleFullPath, // referring module: added
    &ModuleFullPath,
) -> ModuleFullPath
```

`member_key` generalizes its parent argument from `&TypeName` to `&str`, so the
same canonical key mint serves type and trait members:

```rust
member_key(&str, &str) -> Symbol
```

### Consumers and compatibility

| Producer | Consumers | Consequence |
|---|---|---|
| lifecycle/declaration facade | typecheck, backend, primitives, platform and `src/` | breaking source migration; each consumer changes once in dependency order |
| `InstanceLink` / `MonoDemand` | typecheck producer, `src/` reload driver | typed monomorphisation identity replaces source-form replay |
| ADT specs | typecheck and `src/` bootstrap | callers install through the same lifecycle funnels |
| quote classifier | frontend now; `src/` in W6 | removes duplicated structural recognition |
| scoped alias helpers | typecheck now; `src/` in W6 | aliases are keyed by referring-module scope |

There is no Cargo dependency-edge change. The serialized symbol-table shape is
wholly incompatible, so `CACHE_SCHEMA_VERSION` changes 24 → 25 and pre-25
sidecars are refused. There is no platform ABI change in Packet A.

This is intentionally a breaking internal facade replacement. Retaining the
old `ModuleEntry` facade beside it would create two representations and make
the migration—and later maintenance—less safe.

### Excluded from Packet A

The following currently generated types API belongs to W3 and is **not
approved** as part of W1:

```text
TraitMethodRef
SymbolTable::project_trait_method
SymbolTable::trait_method_candidates
SymbolTable::trait_method_projections
SymbolTable::validate_trait_method_projections
View::trait_method_candidates
```

The private serialized `SymbolTable::trait_methods` candidate index is
rejected and must not be retained. W3 must instead propose one general
per-spelling entry/candidate carrier and the associated
creation/import/selection/qualification rules. That exact review also decides
whether `TraitMethodRef`, `BindingBody::Alias` and `BindingBody::Ambiguous`
survive in the public vocabulary.

The following typecheck facade addition belongs to W4 and is **not approved**
as part of W1:

```rust
pub fn instantiate_demands<C, L>(
    demands: Vec<MonoDemand>,
    ctx: &mut SymbolTableAccess<'_, C, L>,
    symbol_tables: &SymbolTables<C, L>,
    module_aliases: &ModuleAliases,
    prelude_fallback: &PreludeFallback,
) -> Result<CheckResult, CheckError>
```

### Current gate position

Packet A1 and Packet B are accepted and represented by the current generated
types baseline. The broad Packet A remainder is still not approved; any
additional lifecycle-foundation surface returns as its own exact proposal.

| Packet | User decision | Actual-diff confirmation |
|---|---|---|
| A1 — live publication | approved exact surface; realized; independent re-review PASS | accepted and baselined 2026-09-02 |
| A remainder — W1 lifecycle foundation | held for regeneration | pending |
| B — W3 name-candidate convergence | approved 2026-09-02, “yes”; realization corrections approved 2026-09-02, “approved” | accepted combined baseline 2026-09-02 |
| C — W4 `instantiate_demands` | not yet presented | pending |

## Packet B — W3 one-map name candidates

**Status: APPROVED FOR REALIZATION 2026-09-02, “yes”. The prerequisite
specification clarification was approved and applied on 2026-09-02.** Packet B
is its own wave. It replaces the temporary
trait-method-specific repair and every remaining one-binding-per-spelling
escape in one pass.

### Proposed representation

`SymbolEntry` is private implementation structure, not public API:

```rust
struct SymbolEntry<C> {
    binding: Option<Binding<C>>,       // canonical declaration at this exact key
    references: Vec<NameCandidate>,   // other canonical declarations exposed here
}

#[non_exhaustive]
pub struct NameCandidate {
    pub source: FQSymbol,              // terminal canonical identity
    pub visibility: Visibility,        // visibility of this local exposure
}

#[non_exhaustive]
pub struct Binding<C: CodeStore = ()> {
    pub visibility: Visibility,
    pub declaration: Decl<C>,
}
```

The canonical binding is an implicit candidate of its own spelling. The
stored `references` therefore contain only additional terminals; the public
candidate reads merge the binding and references and deduplicate by
`FQSymbol`. This avoids storing the canonical declaration's visibility twice.

For the collision which reopened the stream:

```text
symbols["v"]
  binding:    none
  references: Box.v, HasV.v

symbols["Box.v"]
  binding:    accessor declaration

symbols["HasV.v"]
  binding:    trait-method declaration
```

A local declaration may coexist with imported declarations in the same entry:

```text
symbols["convert"]
  binding:    local convert declaration
  references: math/convert, text/convert
```

Canonical qualification probes the exact binding key. An unqualified use
reads the binding plus references, filters them by syntactic context, and then
lets typecheck apply ordinary HM constraints independently to each remaining
typed candidate. Nothing in the table selects by category or insertion order.

### Allowed and disallowed states

- Distinct terminal identities coexist under one spelling. Registration is
  not an ambiguity error.
- Repeated exposure of the same terminal deduplicates; public visibility
  dominates private visibility within one settled table.
- A canonical binding and additional references coexist without overwriting
  one another.
- Every stored reference already names a terminal canonical declaration.
  Candidate resolution direct-probes it; there is no alias chain.
- A use with several surviving candidates is an error carrying those
  canonical identities. The table never stores an `Ambiguous` poison value.
- Module-routing aliases and mounts remain outside this mechanism and retain
  their existing uniqueness rules.
- `SymbolEntry` and the raw map remain private. Consumers receive canonical
  bindings or resolved candidates, not mutable representation access.

### Exact proposed public API

The generalized read-only candidate DTO replaces `TraitMethodRef`:

```rust
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct NameCandidate {
    pub source: FQSymbol,
    pub visibility: Visibility,
}
```

Only `SymbolTable` authors candidate exposure. Selective imports use
`name_candidates`; globs use `public_name_candidates`; cache/session restore
uses the generalized validator:

```rust
impl<C: CodeStore, L: LinkerStore> SymbolTable<C, L> {
    pub fn expose_candidate(
        &mut self,
        local_name: Symbol,
        source: FQSymbol,
        visibility: Visibility,
    ) -> Result<(), LifecycleError>;

    pub fn name_candidates(&self, name: &Symbol) -> Vec<NameCandidate>;

    pub fn all_name_candidates(
        &self,
    ) -> impl Iterator<Item = (&Symbol, NameCandidate)>;

    pub fn public_name_candidates(
        &self,
    ) -> impl Iterator<Item = (&Symbol, NameCandidate)>;

    pub fn validate_name_candidates(
        &self,
        tables: &SymbolTables<C, L>,
    ) -> Result<(), LifecycleError>;
}
```

The all-candidate iterator is the read-only cache-dependency projection;
`public_name_candidates` is its visibility filter. Neither exposes the private
`SymbolEntry` or a mutation capability.

`install_trait_method` keeps its approved shape and performs two atomic acts:
install the canonical `Trait.method` binding and expose that terminal under
the bare method spelling. ADT synthesis similarly installs `Type.member` and
then calls `expose_candidate` for the bare spelling. Imports and re-exports
resolve to a terminal first and call the same method.

The types-owned resolver exposes the complete candidate set. Its existing
`resolve` method remains the unique-candidate convenience and returns the new
ambiguity error when pre-type context does not leave one:

```rust
impl<'a, C: CodeStore, L: LinkerStore> ResolutionScope<'a, C, L> {
    pub fn resolve_candidates(
        &self,
        name: &str,
        span: Span,
    ) -> Result<Vec<Resolved<C>>, ResolveError>;

    // Existing signature retained.
    pub fn resolve(
        &self,
        name: &str,
        span: Span,
    ) -> Result<Resolved<C>, ResolveError>;
}

#[non_exhaustive]
pub enum ResolveError {
    // existing variants retained
    Ambiguous {
        name: Symbol,
        from_module: ModuleFullPath,
        candidates: Vec<FQSymbol>,
        span: Span,
    },
}
```

Because candidate references are terminal, `Resolved` no longer needs a
written-reference identity beside a storage identity. One canonical identity
is sufficient and prevents consumers choosing the wrong one:

```rust
#[non_exhaustive]
pub struct Resolved<C: CodeStore = ()> {
    pub entry: Binding<C>,
    pub canonical: FQSymbol,
}
```

`BindingBody` is removed rather than retained as a one-variant enum. The
binding constructor becomes:

```rust
impl<C: CodeStore> Binding<C> {
    pub fn new(declaration: Decl<C>, visibility: Visibility) -> Self;
    // Existing declaration/lifecycle read methods remain unchanged.
}
```

The following signatures remain unchanged and return canonical bindings only:

```text
SymbolTable::{get, all_symbols, public_symbols, defined_symbols}
View::{lookup, iter}
```

`public_name_candidates`, not `public_symbols`, is the import/export exposure
enumeration. No public `SymbolEntry` or public `View` candidate method is
added.

### Approved realization corrections

Two facade omissions found by the downstream compile were approved on
2026-09-02 with “approved”:

```rust
Life::Inline {
    mode_summary: Option<ModeSummary>,
}

install_extern(..., mode_summary: Option<ModeSummary>, visibility: Visibility)
install_inline(..., mode_summary: Option<ModeSummary>, visibility: Visibility)
```

The ownership argument is immediately before `visibility` in both installers.
`Binding::mode_summary()` projects the existing `Life::Concrete` field and the
new `Life::Inline` field. This preserves the prior primitive ownership facts
without adding a general mutation escape.

The same approval adds `SymbolTable::all_name_candidates` as shown above so
cache dependency discovery can see private and public terminal references.
The resolver's union of current-module and public implicit-prelude candidates
is not a new API or semantic choice: it corrects the implementation to the
already-approved §8.6.1 rule. Qualified resolution is unchanged.

### Exact removals

```text
BindingBody
Binding::{alias, ambiguous, declaration}
BindingProvenance
check_binding_addition
reject_def_over_binding
resolve_terminal_entry_and_home

TraitMethodRef
SymbolTable::project_trait_method
SymbolTable::trait_method_candidates
SymbolTable::trait_method_projections
SymbolTable::validate_trait_method_projections
View::trait_method_candidates

Resolved::{home, fq, storage_key, storage_fq}
```

The definition-over-import/prelude APIs are removed because approved spec
§8.6.4 now permits those distinct canonical declarations to coexist. Keeping
the rejection seam would contradict the language. Direct keyed consumers use
`Resolved::canonical`; scope-sensitive consumers use `ResolutionScope`.

### Specification clarification — approved and applied

The approved candidate rules at §8.6.4–§8.6.5 compare and report terminal
canonical identities, but four older passages still prescribe the retired
`ModuleEntry::{Import, Reexport}` representation and mandatory alias-chain
storage:

```text
§8.3.5  renamed import stored as ModuleEntry::Import
§8.4.0  visibility stamped on the resulting ModuleEntry
§8.4.5  renamed re-export stored as ModuleEntry::Reexport
§8.6.2  candidates partitioned into Def/Import/Reexport entry forms
```

The approved clarification changes no language-visible import, rename,
visibility, candidate, or qualification behavior. It removes the obsolete
Rust representation from the specification and permits either immediate
references or already-terminal references:

```text
§8.3.5
  Maybe-Just exposes under its local spelling every public terminal candidate
  reached through core.option/Some. The rename changes only the local spelling.

§8.4.0
  Import and export differ only in the visibility attached to each resulting
  local candidate exposure: private for import, public for export.

§8.4.5
  Just publicly exposes the terminal candidate set reached through
  core.option/Some. A downstream import preserves that set.

§8.6.2
  A module-scope spelling denotes the terminal canonical candidates exposed
  by local declarations, imports, exports, derived members, and the prelude.
  An implementation may retain immediate references and follow them, or store
  terminal references directly. Before deduplication or use-site selection it
  must reach terminal identities; any implementation that follows chains must
  bound pathological cycles.
```

This clarification authorizes Packet B's terminal `NameCandidate::source`
without prescribing the private storage representation. The exact public-API
delta above was approved on 2026-09-02 and is now the realization boundary.

### Producer, consumers, and compatibility

| Surface | Producer | Consumers and change |
|---|---|---|
| `NameCandidate` and candidate funnels | `cranelisp-types` | `src/imports.rs` authors/selects exposures; typecheck and types resolution read them |
| `ResolutionScope::resolve_candidates` | `cranelisp-types` | typecheck performs syntactic and isolated-HM filtering; int macro recognition retains unique pre-type selection |
| simplified `Binding` | `cranelisp-types` | typecheck changes its declaration matches once; backend/runtime/int keep lifecycle accessors |
| canonical `Resolved` | `cranelisp-types` | typecheck and int use the one terminal identity; backend receives already-keyed carriers as before |

This is intentionally source-breaking. There is no Cargo dependency-edge or
platform ABI change. The private `symbols` value shape changes and the
parallel `trait_methods` field disappears, so the serialized table is
incompatible; it uses the already-open S121 `CACHE_SCHEMA_VERSION` 24 → 25
window rather than creating a second bump. Pre-25 sidecars remain wholesale
invalid.

### Forecast `public-api.txt` effect

- Add `NameCandidate` and its two public fields.
- Add the five general `SymbolTable` methods above.
- Preserve primitive ownership through the approved installer arguments and
  `Life::Inline { mode_summary }`.
- Add `ResolutionScope::resolve_candidates`.
- Add `ResolveError::Ambiguous` and its four fields.
- Replace `Binding::body: BindingBody<C>` with
  `Binding::declaration: Decl<C>`; replace `Binding::declaration` with
  `Binding::new`.
- Replace `Resolved::{home, fq, storage_key}` plus `storage_fq` with
  `Resolved::canonical`.
- Remove every type, variant, function, and method listed under “Exact
  removals”. Derived marker-trait lines change mechanically with the carrier
  additions/removals.

No other crate baseline changes are forecast: the downstream typecheck and
binary changes consume the types facade without changing their own public
surface.

### Wave position

Packet B realizes before Packet A1 or any downstream lifecycle wash. It is a
separate wave because it changes name identity and resolution across the
solution. Its crate streams are ordered `cranelisp-types` →
`cranelisp-typecheck` → binary integration/imports, followed by candidate
evidence and independent review. The prior downstream wave plan is not
discarded, but its typecheck and integration work is rebased onto this
candidate facade so those crates are each visited once after B settles.
