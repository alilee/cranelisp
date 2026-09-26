# cranelisp-types — local conventions

Contract gotchas for consumers of the cross-crate substrate. Owned by `arch`;
other roles file shape changes to `arch`. The boundary narrative is
[interfaces](../../design/arch/interfaces.md) and
[bounded contexts](../../design/arch/bounded-contexts.md) §7; exact promises
are the rustdoc. This memory records only what rustdoc does not say, or says
in a place a contributor would not look first.

## The serde shape is the cache contract

`SymbolTable` and its `Binding`/`Decl`/`Callable`/`Life` tree serialise into
the backend's `.meta.json` sidecars.

- **Any serde-visible change — a field added, deleted or retyped, or a change
  to what an existing field means — bumps `CACHE_SCHEMA_VERSION` in
  `crates/cranelisp-backend/src/cache/mod.rs` in the same change-set.** The
  constant lives in the backend, so an edit here is incomplete without that
  cross-crate bump. Read the constant for its current value.
- The one exempt class is a `#[serde(default)]` addition whose default equals
  the fresh-build value; the rule is stated on `CACHE_SCHEMA_VERSION` and on
  `SymbolTable.schema_version`.
- `SymbolTable.lookup_dependencies` is not in that exempt class although a
  fresh table's set is empty: a defaulted pre-carrier sidecar would under-key
  cache validity, so absence is a decode error. The set is insert-only; write
  it only through `record_lookup_dependency` into staging, which both publish
  funnels union into the live table
  ([qualified lookup dependencies](../../design/arch/interfaces.md#qualified-lookup-dependencies)).
- `#[serde(skip)]` runtime fields: `got`, `linker` and `Realization::Body.code`.
  Caches deserialise as `SymbolTable<(), ()>`; int rehydrates through
  `SymbolTable::into_concrete`, which leaves every `code` as `None`.
- The `#[serde(bound = "")]` on `SymbolTable` and the generic lifecycle
  carriers is load-bearing: without it the derives demand `C: Serialize` even
  for skipped fields, and the `()` instantiation stops compiling.
- **`GotTable::clone()` returns a fresh, all-null table**, matching
  `#[serde(default)]`. Sharing happens only through the `Arc` on
  `SymbolTable.got`; cloning never copies pointers.
- `MethodResolutions` derives `Serialize` but is not JSON-safe: its maps are
  `Span`-keyed. Never serialise it to JSON.

## Callability is structural — read through the accessors

The GOT slot exists only on `Life::Concrete` and `Life::Broken` beneath a
`Decl::Callable`; templates, inline primitives and host-promised callables
have no slot field
([Principle 20](../../design/arch/principles/20-model-invariants-by-representation.md)).
Use the read-throughs; never re-pattern the lifecycle set:

- `Binding::callable_got_slot()` is the one callable-address read.
- `Binding::is_callable_target()` is the resolution stop condition. It covers
  slot-less inline and host-promised callables and the unslotted
  `Decl::TraitMethod`. Probing `callable_got_slot().is_some()` at a resolution
  seam instead lets a slotless callable be shadowed.
- `SymbolTable::codegen_targets()` is the codegen projection: directly named
  callables, overload arms and macro clauses whose lifecycle is exactly
  `Life::Concrete` with `Realization::Body`. `Binding::codegen_view()` uses
  the same shape, so a codegen target cannot exist without its view.
- `Binding::type_def_info()` is the one "does this binding answer as a type"
  reader: `Decl::Type(TypeRecord::Defined)` or a product constructor
  carrying `CallableOrigin::Ctor { type_def: Some(..) }`. Matching only
  `Decl::Type` silently skips product types. `type_ctor_names` is the
  constructor-name projection over the same switch.
- `CallableOrigin::PlatformEffect.poll_shape` is inverted from the C-ABI
  `blocking` flag: `false` means blocking.

## Lifecycle writes go through funnels

- **The `SymbolTable` lifecycle funnels are the only fresh-slot authority.**
  `declare` + `settle_concrete` and the born-settled installers pair a concrete
  scheme with the opaque `CallableSlot` in one act; raw allocation and
  publication are private. `CallableSlot::rebind` is the checked reuse path.
  `validate_lifecycle` re-derives every live and retired claim after
  construction, clone or deserialisation. The reasons are the
  [symbol-table lifecycle](../../design/arch/symbol-table-lifecycle.md).
- **Instance identity is authored once.** `install_instance(link, …)` derives
  the storage key from the settled scheme and the link's owner through
  `concrete_callable_key`, and returns `(key, slot)`. A key inconsistent with
  that derivation is `LifecycleError::InstanceKeyMismatch`, both at install
  and after deserialisation, where it reads as cache-stale. Ordinary
  `settle_concrete`/`install_concrete` do not accept `minted_from`.
- **`callees`, `ast`, the concrete view, realization and slot enter together.**
  Checked bodies use `settle_checked_template`/`settle_checked_concrete`;
  a later callee harvest uses `replace_callees`. Ownership publishes its
  annotated view through `publish_body_ownership`, which stamps the view and
  its summary twin in one act; there is no one-sided summary setter.
  `value_use` is written only through `SymbolTable::set_value_use`.
- **`callees` completeness is consumed silently.** The redefinition reverse
  index starves without error when a body-check seam omits the harvest; the
  completeness contract is in the
  [typecheck memory](../cranelisp-typecheck/CLAUDE.md).
- **Public non-exhaustive lifecycle records have explicit authoring paths.**
  Construct `Callable`, `CallableArm`, `OverloadedCallable`,
  `MacroDeclaration`, `MacroClause`, `TraitRecord`, `TraitMethodRecord`,
  `SpecialFormRecord`, `SynthSpec`, `ConstrainedMeta` and `BrokenProvenance`
  through their role-specific `new` functions or the `SymbolTable` installers.
  Do not add raw field-literal or lifecycle-state escape hatches. `RetiredSlot`
  stays private; `ImplShell` is authored only through
  `enrol_written_trait_impl`. `NameCandidate` is read-only to consumers; only
  the exposure funnels construct it. The external compile-pass under
  `crates/cranelisp-types/tests/` constructs every published record, because
  in-crate unit tests cannot detect E0639.
- **Trait method declarations are not executable entries.** A `deftrait`
  member is `Decl::TraitMethod(TraitMethodRecord)` at canonical
  `member_key(Trait, method)`, installed by `install_trait_method` and read by
  `Binding::trait_method`. Bare reachability is a `NameCandidate` exposure of
  that FQ through `expose_candidate`. Never leave it `Life::Declared`, store it
  only at the bare key, keep a parallel map, scan `TraitRecord`s by method
  name, fabricate an impl-method origin or invent a body.
- **Trait-implementation persistence.** `SymbolTable.written_trait_impls`,
  `WrittenTraitImpl`, `enrol_written_trait_impl` and `trait_impl_key` are the
  writer-side carrier ([trait-implementation persistence](../../design/arch/trait-impl-cache-carrier.md)).
  The field deliberately has no `#[serde(default)]`: absence is a hard serde
  error. `trait_impl_key` is the one `impl$` key mint. Fresh registration uses
  `stage_trait_impl_shell` with `RetainedCallables`, upserting the writer
  record only after every method settles; failure leaves the prior record
  untouched.
- **ADT construction is slotless until settlement.** `build_adt_entries`
  returns `AdtCallableSpec` recipes and `Binding<C>` values; callers submit
  each recipe to the table funnel.
- **Cleanup is state-specific.** `remove_non_callable` is the ADT pre-seed
  rollback; `discard_declared` accepts only `Declared { prior: None }`. There
  is no generic callable remove, rename, mutable binding projection or
  caller-side slot reclamation.

## Resolution primitive traps

- **`Resolved` carries one identity.** `canonical` is the terminal `FQSymbol`
  that direct-probes its table; `entry` is that binding. Never compose a
  storage identity from the written spelling. `lookup_module` is provenance:
  the table probed after alias substitution, possibly a re-exporter rather
  than `canonical.module`. Never key storage on it.
  `ResolutionScope::resolve_candidates` returns the complete set; `resolve` is
  the unique-candidate convenience and the sole public resolution entry.
- **The prelude fallback is decided at scope construction.** `resolve` retries
  the prelude only on the not-found class; `PrivateInaccessible` and
  `QualifiedModuleUnknown` return as-is. The retry admits only a **public
  prelude head binding** — the entry in prelude's own table — and a private
  head or terminal reports the original current-module not-found. Controls:
  `prelude_fallback_remains_public_head_only` and
  `prelude_alias_head_visibility_controls_public_terminal_fallback` in
  `crates/cranelisp-types/src/resolve/tests.rs`.
- `split_qualified` requires both `/`-parts non-empty: `/`, `//`, `foo/` and
  `/bar` are literal names
  ([Principle 16](../../design/arch/principles/16-punctuation-symbols-are-not-special.md)).
  Fix a mis-resolving `/`-named operator here, never with a checker-side
  literal shortcut.
- `member_key` is the one mint for canonical dotted `Parent.member` keys:
  field accessors, constructor keys and trait-method terminals.
  `bare_member_name` is its inverse projection, the one terminal-segment
  grammar for comparing storage keys with bare display names. Never hand-roll
  either.
- `chain_follow_committed`'s same-module alias arm and the scoped module-alias
  walk share `CHAIN_FOLLOW_DEPTH_LIMIT`: a degenerate alias cycle is a
  not-found miss, never a stack overflow
  (`alias_walk_refuses_more_than_the_shared_depth_limit` in
  `crates/cranelisp-types/src/resolve/tests.rs`).
- The generic miss from `not_found` in `crates/cranelisp-types/src/resolve.rs`
  is `TypeNotFound`-shaped whatever the entry kind; never infer entry kind
  from the error variant.

## Single-source predicates coupled to soundness

- `value_layout`/`value_layout_with_lookup` (`heap.rs`) is the Copy and
  value-flattening verdict that typecheck's `Copy` classifier and backend's
  `HeapCategory::Value` arm both delegate to; divergence is a use-after-free.
  Single-field-only is a soundness rule, not a size bound; changing
  `VALUE_LAYOUT_MAX_WORDS` is a cache-schema bump. Each lookup releases its
  table or staging guard before returning, and the walk drops metadata before
  recursing: two guards on one shard deadlock.
- `heap::ctor_field_types_at` is the only legal derivation of constructor
  field types at a concrete instantiation
  ([total concreteness](../../design/arch/total-concreteness.md) §2.1).
  It has no production consumer yet; backend adoption is designed in
  [non-concrete release](../../design/backend/non-concrete-release-contract.md).
- `ConcreteType::result_root()` is the one IO-head strip (one hop,
  `primitives/IO` only), shared by backend `result_roots` and int's release
  key.
- `is_strict_type_concrete` (`mono_expr.rs`) is the pure-type half of the
  `from_expr` gate and the ownership fixpoint's universe pin. Ask it rather
  than re-walking the gate; probing through `from_expr` with empty maps
  answers `Unresolved`, not the type question.
- `Type::is_concrete()` is the GOT-slot eligibility gate: strictly stronger
  than "no constraints", and `TyConApp` counts as non-concrete.
- `render_type` is the single `Type`-to-string walk. `apply` carries a direct
  self-map cycle guard that debug-asserts and treats the variable as unbound
  in release.
- `got_data_symbol_name` is injective, and alphanumeric paths are fixed points
  (`__cranelisp_got_primitives` is a link-time ABI literal). Changing the
  scheme renames every cached object's relocations, so it is a schema event.

## Ownership vocabulary

- **Never index `ModeSummary` vectors.** `param_mode`, `param_flow` and
  `spark_op` are the one home for ⊤-on-absence; compare ABI only with
  `abi_eq`/`abi_eq_opt` (`None` is all-conservative).
- **`ResultMode::Fresh` is the `Default` but the result axis's strongest
  claim**, not its conservative point: backend elides the return protect on a
  present `Fresh`. The axis's ⊤ is `MayAliasAny`, and the conservative whole
  summary is `None`. `ModeSummary::default()` and `is_abi_conservative()` are
  caller-side ABI statements, not substitutes for absence, and no producer may
  mint a summary as a fallback. `ownership.rs` module rustdoc §Monotone
  defaults is the one home; read it before touching a `result` arm.
- `ownership_analysis_off()` is read once per process and is a backend cache
  global key.
- **`ViewBuildError` routing is load-bearing.** `NotConcrete` may fall back to
  `lenient_from_expr`; `Unresolved` — a real-span `Var`/`Apply` with no typed
  verdict — is a located typecheck error and must never enter the fallback.
  `lenient_from_expr` tolerates types only; a real-span verdict miss panics.
  `MonoExpr::synthetic_local_from_expr` is the one all-local builder for
  `Span::SYNTHETIC` bodies, and asserts that span; never widen it for a real
  body.

## Known asymmetries that look like bugs

- `Pattern::Constructor.name` is a `SymbolRef` holding the qualified spelling
  verbatim (`option/Some` has `module: None`); the resolved FQ lives in the
  span-keyed `MethodResolutions.pattern_ctors` sidecar.
- `PlatformSpec.name` is still a bare `String`; its rustdoc records the
  `ModuleName` narrowing target and its trigger.
- The marshal tags' constructor order is authored by typecheck's
  `builtins::register_macros_module`, which this crate cannot assert
  (dependency direction). The local marshal tests guard only the constants.

## Public-surface mechanics

- Submodules are `pub(crate)`; the crate-root re-export list in `lib.rs` is the
  sole surface. Any surface change regenerates `public-api.txt` with the
  [canonical command](../../design/arch/CLAUDE.md#baseline-diff-discipline-sprint-67-close)
  and without `--features test-support`, which keeps the `test_support`
  builder off the frozen surface.
- Every public lifecycle item, constructor, enum variant and public field has
  its own `///` contract; a type-level summary does not substitute for
  variant and field documentation.
- `#[non_exhaustive]` is policy on every public struct and enum except:
  - string newtypes and `View` (private fields);
  - the `#[repr(C)]`/`#[repr(u32)]` ABI types `SchedulingClass`,
    `ConcurrencyDescriptor`, `Poll` and `HeapHeader`, governed by
    `cranelisp_platform::ABI_VERSION` bumps
    ([Principle 14](../../design/arch/principles/14-ffi-layout-discipline.md))
    and pinned by const asserts and layout tests;
  - closed sums whose exhaustive consumer matches are the safety contract, so
    a new variant must break every match rather than hide behind `_`
    ([Principle 18](../../design/arch/principles/18-enforce-invariants-structurally.md)):
    the ownership vocabulary (`Mode`, `ResultMode`, `ParamFlow`, and the
    literally constructed `ModeSummary`); the lifecycle sums (`Decl`,
    `TypeRecord`, `Life`, `TemplateBody`, `TemplateKind`, `CallableOrigin`,
    `Realization`, `RetireReason`); `AdtEntrySpec`; `QuoteHead`; the typed
    resolution sums `VarRef`/`ApplyRef`, for which "unresolved" has no
    constructor; and `ViewBuildError`.
- Payload structs of those sums remain non-exhaustive, and cross-crate
  construction goes through the sanctioned constructors and funnels.
- A variant added to `ResultMode` re-runs the `_ =>` and `== Fresh` escape
  search (`ownership.rs` rustdoc §Exhaustiveness discipline).

## Tests

- Unit tests sit beside their module as `{module}/tests.rs` or an inline
  `#[cfg(test)]` module
  ([Principle 23](../../design/arch/principles/23-tests-mirror-module-composition.md)).
  Modules without local tests are pinned by consumer-crate suites.
- The external compile-pass under `crates/cranelisp-types/tests/` is the only
  place a non-exhaustive construction bug is observable.
