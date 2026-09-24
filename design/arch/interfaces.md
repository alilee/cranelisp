# Interfaces — boundary types

**Owner:** `arch`. A family-by-family guide to the values that cross a crate boundary.

- **Authority.** Source rustdoc is the exact contract; each crate's `public-api.txt` is the
  surface evidence. This guide copies no Rust definitions. It states what each family is for,
  who produces and consumes it, and the cross-boundary rules a signature cannot express.
- **Scope.** Boundary types live in `cranelisp-types` unless a section says otherwise.
  [Bounded contexts](bounded-contexts.md) owns each context's responsibilities and
  invariants; the focused contracts linked below own their subjects. The crate-root rustdoc in
  `crates/cranelisp-types/src/lib.rs` lists every exported family.
- **Data flow.** Source text → `Sexp` → extracted module declarations plus remaining forms →
  expanded `Sexp` → `ParsedEntry` → checked declarations on `SymbolTable` → executable code.
- **Audit rule** ([Principle 13](principles/13-interfaces-md-is-auditable.md), with
  Principles 11 and 12). No two structurally identical types exist at a pipeline boundary. No
  adapter function converts one boundary type into another. Each stage has one entry point
  per crate. A mode difference is a parameter, never a second type or function.
- A proposal is labelled as one where it appears. Everything else describes delivered source.

---

## Foundation Types

### Source Location

`Span` is a byte range carried on every AST node and every error. `Span::SYNTHETIC` marks
compiler-synthesised nodes; span-keyed carriers treat it as outside their transport (see
[Method Resolutions](#method-resolutions)).

### String Newtypes

- Every identifier crossing a boundary uses a newtype, never a bare `String`: `Symbol` (local
  name), `ModuleName` (one path component), `ModuleFullPath` (dotted path), `TypeName`,
  `TraitName`, `JitSymbol` (mangled JIT name) and `LinkerSymbol` (linker-level name).
- Syntactic-stage references keep as-written qualification: `SymbolRef`, `TypeRef` and
  `TraitRef`. Resolved-stage references are fully qualified: `FQSymbol`, `FQTypeName` and
  `FQTraitName`. [Type System](#type-system) states where the lift happens.
- Plain strings remain for messages, documentation, source text and descriptions.

### Errors

`CranelispError` is the one error sum; every variant carries a `Span`. `Warning` and
`WarningKind` are the non-fatal diagnostics. A context must not export an error a consumer
can only forward.

---

## Reader Output

`Sexp` is produced by the frontend reader, consumed by the frontend AST builder and the
binary's expander, and retained for introspection.

- `Sexp::Annotated` is the one Rust carrier for read-time annotation folding. Its named slots
  prevent annotation/subject transposition, and `span()` returns the outer binding span while
  each child keeps its own. The macro-visible `macros/Sexp` ADT appends the annotated case at
  `TAG_SEXP_ANNOTATED`; earlier tags are stable.
  [Annotated S-expressions](annotated-sexp-node.md) owns folding, printing, quasiquote and
  persistence; it defines no second carrier.

### Reader-quote structural predicate

- `QuoteHead` and `quote_head` live beside `Sexp` (`crates/cranelisp-types/src/sexp.rs`). The
  test is purely syntactic — a bare-symbol head and two children — and consults no shadow set
  or resolver, which is why it belongs with the datum rather than in a consumer
  (Principles 7 and 15).
- The frontend quasiquote fold and the binary's scope-aware expansion and qualification
  shields classify quotes through this one predicate. If their notions of "is a quote"
  diverged, a quoted subtree would be double-desugared or mis-qualified.
- The reader still lowers the quote sugars to list forms; the predicate only classifies them.
- FIXME 0789 is the open filing that asked for this home; its disposition against source is
  owed.

---

## Module Declarations

The frontend's `extract_module_declarations` separates module-structure forms from the
remaining forms. The extracted `ImportSpec`, `ExportSpec`, platform and submodule
declarations live on the module's `SymbolTable` in its public structural vectors. Those
vectors are the append contract: direct push, source order, no deduplication.

---

## AST

Produced by the frontend, annotated in place by typecheck. The backend does not read it; it
reads the typed view ([Concrete codegen boundary](#concrete-codegen-boundary)).

- **`TopLevel` is the sole top-level input type.** It includes a bare-expression case, so
  there is no separate REPL input type. `Defn` holds one or more `DefnVariant`s; single- and
  multi-signature functions share one shape.
- **`TypeExpr::Bounds`.** A parameter annotation is either a concrete type or a set of trait
  bounds, never both. The binder's single optional `TypeExpr` slot holds one or the other, so
  the exclusion holds by construction; a sidecar carrying both would model a state that
  cannot exist. The `TraitRef`s keep as-written qualification and typecheck accumulates them
  onto the variable's scheme constraints (spec §3.9.2, §3.9.3).
- **Trait-method tails are phase-separated.** The frontend builds `UnresolvedTraitMethodSig`
  and preserves the trailing form verbatim. Typecheck is the only classifier: it completes
  the transactional type-resolution probe before producing `TraitMethodSig`, and an
  unresolved method is never published. `TraitMethodKind` is the one closed sum. For an
  annotated default, the annotation is stored once as the result constraint and is not also
  kept as an outer annotation node.

---

## Type System

- `Type`, `Scheme`, `Subst` and `TypeId` are typecheck's resolved type vocabulary.
- `render_type`, configured by `PrimitiveNaming` and `VarNaming`, is the single `Type`-to-text
  walk. Every renderer in the workspace delegates to it ([Type rendering](#type-rendering)).
- `Type::is_concrete` is the one concreteness verdict
  ([Concrete codegen boundary](#concrete-codegen-boundary)).

### Type rendering

`render_type(ty, PrimitiveNaming, VarNaming)` (`crates/cranelisp-types/src/types.rs`) is the
one structural walk; the two enums are output conventions, not separate renderers. `Display`
for `Type` is `Bare` + `Numbered`; typecheck diagnostics are `Qualified` + `Numbered`; the
binary's REPL and value display is `Qualified` + `Lettered` over a `type_var_names` map, with
the `:Trait var` constraint decoration layered in `src/display.rs` and deliberately outside
this crate. The cells below are the byte-for-byte contract that
`crates/cranelisp-types/src/types/tests.rs` pins; a rendering change edits this table and
those tests together.

| Variant | `PrimitiveNaming::Bare` | `PrimitiveNaming::Qualified` |
|---|---|---|
| `Int`, `Bool`, `String`, `Float` | `Int`, … | `primitives/Int`, … |

| Variant | `VarNaming::Numbered` | `VarNaming::Lettered(m)` |
|---|---|---|
| `Var(id)` | `t{id}` | `m[id]`, or `t{id}` when absent |
| `TyConApp(id, [])` | `(TyCon t{id})` | `{head}` — bare, no parens |
| `TyConApp(id, args)` | `(TyCon t{id} {a…})` | `({head} {a…})` |

| Variant | Both conventions (arguments recurse with the same configuration) |
|---|---|
| `Fn(params, ret)` | `(Fn [{p…}] {ret})`; empty params render `(Fn [] {ret})` |
| `ADT(fqtn, [])` | `{fqtn}` (`module/Name`) |
| `ADT(fqtn, args)` | `({fqtn} {a…})` |

`{head}` is `m[id]` with the same `t{id}` fallback. `TyConApp` is the one variant whose shape
follows `VarNaming` rather than `PrimitiveNaming`: `Numbered` always emits the `TyCon` prefix
and parentheses, `Lettered` never does. A shared arm that only substituted the head name would
regress one path or the other, which is why the walk branches on the discriminant.

**Resolved-stage type identity is module-qualified (Decision 47).**

- Every API past the frontend's resolution stage names a type or trait as `FQTypeName` or
  `FQTraitName` (`crates/cranelisp-types/src/newtype.rs`). Bare `TypeName` and `TraitName`
  are syntactic-stage values.
- The lift happens once, in typecheck's resolver. Unification compares the whole
  `FQTypeName`, so a `Point` defined in two modules yields two distinct types.
- There are exactly two exceptions, neither extendable without `arch` review: recognising or
  emitting the built-in non-ADT primitive types by bare name, which is unique workspace-wide;
  and receiver-pinned lookups, where the table already supplies the module.
- Why: a boundary value carries its full identity, so no consumer needs caller-side module
  context to disambiguate ([Principle 02](principles/02-narrow-interfaces.md)), and a type
  has exactly one qualified name workspace-wide
  ([Principle 07](principles/07-single-source-of-truth.md)). The cross-module guard is
  `tests/spec_fqtypename_boundary.rs`.
- Consequences. The primitive types keep dedicated `Type` variants: they need no tag,
  constructor or heap layout, and `primitives/Int` is a rendering convention, not a
  type-system fact. No derived name-to-module map exists; an ADT type carries its module, so
  display and codegen never reverse-look it up. Constructor names stay `Symbol` because their
  table is already module-pinned.

---

## Pipeline Configuration

- `CodegenBehaviour`, `ModuleStrategy` and `CompileContext`
  (`crates/cranelisp-types/src/pipeline.rs`) parameterise one pipeline. `ModuleStrategy` is a
  call parameter, not a context field, because one context serves both strategies.
- The REPL / `--run` / `--link` session axis is the binary-internal `RunMode`. It gates
  REPL-only introspection and the platform layout-hash policy, and is orthogonal to
  `CodegenBehaviour`. They must not be conflated
  ([introspection ownership](d1-introspection-repl-only.md)).
- `GOT_TABLE_SIZE` and `NULLARY_TAG_THRESHOLD` are single-sourced here for every crate that
  needs them.

---

## Typecheck Outputs

Typecheck deposits codegen inputs on symbol-table declarations. Its returned `CheckResult`
is a typecheck-owned transient carrying diagnostics and REPL display (`DisplayInfo`). It is
not a backend input and no function converts it into one. The backend's input is
`SymbolTable::codegen_targets()`.

### Method Resolutions

- `MethodResolutions` holds span-keyed sidecars for one check run. `var_refs` and
  `apply_refs` are total over that run's references: locals record `VarRef::Local` and
  dispatch-less applications record `ApplyRef::ViaCallee`. "No entry means local" is retired.
- `VarRef::Local` carries the binder identity — the bound name plus the span of the binding
  form that introduced it, because the AST has no per-binder span for parameters. It is a
  resolution verdict, not a storage locator: the backend's scope stack owns the slot, and a
  binder absent from it is a producer breach that fails hard naming the binder.
  `ApplyRef::ViaCallee` is a positive verdict that no dispatch was selected at the
  application: the identity rides the callee expression.
- `MonoExpr::from_expr` transports them onto the typed view as non-optional fields. A
  real-span reference with no verdict is `ViewBuildError::Unresolved`, read before the node
  type so it cannot degrade into the type error. `VarRef` and `ApplyRef` are closed sums with
  no unresolved case and no `#[non_exhaustive]`: a new variant must break every consumer
  match.
- `Span::SYNTHETIC` is one shared key, so the sidecars cannot address synthetic nodes
  individually. In both builders a synthetic-span node with no entry takes the all-local
  verdict (`VarRef::Local` at the synthetic span, `ApplyRef::ViaCallee`); an entry recorded
  under that key still wins. Compiler-synthesised all-local bodies enter through
  `MonoExpr::synthetic_local_from_expr`, which asserts every node is synthetic. The standing
  invariant this rests on, and its falsifier, are in
  [backend keyed consumption §4](backend-keyed-consumer.md#4-view-production--typecheck-is-the-sole-producer-w0b).
- The `FQSymbol` inside `Global` and `Dispatch` is the storage identity: the module plus the
  exact table key at which resolution terminated. It is neither the written name nor a
  display name.
- `resolved_calls` (`ResolvedCall`) is supplementary dispatch metadata — built-in intercepts,
  auto-curry counts and trait resolution for the as-value wrapper. It is never the
  keyed-lookup carrier. `ResolvedCall::TraitMethod.impl_module` names the impl writer's
  module, where the selected method body is stored.
- `pattern_ctors` carries each constructor pattern's storage identity to the view's
  `resolved_ctor`.
- Contracts: [backend keyed consumption](backend-keyed-consumer.md),
  [constructor keys](dotted-ctor-canonical-keys.md) and
  [Principle 24](principles/24-resolve-once.md). Exact promises: the rustdoc in
  `crates/cranelisp-types/src/mono_expr.rs` and `crates/cranelisp-types/src/check.rs`.

### Ownership-inference carriers

- `Mode`, `ModeSummary`, `ResultMode` and `ParamFlow` are the typecheck→backend memory-model
  carrier. A summary rides `Life::Concrete` or `Life::Inline` and is read through
  `Binding::mode_summary`; absence reads as the conservative top.
- `ResultMode` is a closed sum without `#[non_exhaustive]`, so a new variant forces each
  consumer match to be revisited. Two equality reads against `Fresh` — the backend's
  fresh-return test and `ModeSummary::is_abi_conservative` — escape that forcing by design
  and fail safe: any non-`Fresh` value is treated as non-fresh and non-conservative. Re-run
  the wildcard and equality census when adding a variant.
- Every variant is serde-visible on persisted summaries, so a change takes a
  `CACHE_SCHEMA_VERSION` bump.
- Ruling and semantics: [ownership inference](ownership-inference.md).

### Written-impl cache carrier

`WrittenTraitImpl`, `enrol_written_trait_impl` and `trait_impl_key` persist the writer-side
record of a trait implementation. A sidecar without the carrier fails to parse and is
rebuilt. Contract: [trait-implementation persistence](trait-impl-cache-carrier.md).

---

## Parse-to-Check Handoff

### `ParsedEntry`

- `ParsedEntry` bridges the frontend's `build_form` to typecheck's `check_forms`. It carries
  only what the parser knows and never lands in a `SymbolTable`, which preserves the table
  invariant "if it is in the table, it is checked". It is not serialised.
- `build_form` returns a vector because one source form can yield several entries, such as a
  macro's clauses or a type plus its constructors. `DefmacroInfo` lives in `cranelisp-types`
  so the binary can name it after `build_form`.

### `check_forms`

- `check_forms` consumes a whole cluster and runs registration then checking internally
  (spec §5.13.1), so forward references and mutual recursion resolve without working state
  crossing the facade. An earlier two-function split exposed that state and was withdrawn
  (Decision 44).
- It is pure with respect to live state. It writes only the orchestrator's staging table,
  through the same accessor used for committed tables, so typecheck cannot tell staging from
  live. The binary commits staging atomically on whole-cluster success; on a gap or type
  error the live table is byte-identical to its prior state.
- Staging is a per-cluster frame, not a second write surface on the canonical store: nothing
  publishes it ([Principle 07](principles/07-single-source-of-truth.md)).
- The caller-supplied `SymbolTableAccess` has two modes, and its two accessors are the only
  place they differ. `Live` reads and writes the committed per-module table. `Cluster` sends
  current-module writes to the binary's staging table and reads through the types-owned
  `View`, which consults staging before live. Staging starts empty, reads union staging over
  live, and publication drains staging into live; no table is cloned per cluster. Two rules
  this pins, each with a regression in `tests/regression.rs`: a cluster-mode read of live
  alone loses an intra-cluster forward reference to a sibling staged in the same cluster
  (FIXME 0179), and cross-form working state lives in the `check_forms` frame and nowhere
  else (FIXME 0177). Cloning live into staging and replacing it on publish was not adopted:
  it costs a clone per cluster for an initial-equal-to-live staging no workload needs, and
  adopting it would be an orchestration change for `arch` and the user, not an accessor
  change.
- Rejected shapes, each returning only with a new ruling: two public pass functions (working
  state could not cross two free-function calls without a public accumulator); one function
  with a pass-discriminator parameter (every consumer would dispatch on the pass —
  [Principle 02](principles/02-narrow-interfaces.md)); staging as a mode of `SymbolTable` (a
  second write surface and a mode-qualified live invariant); a read-view trait implemented
  by `&SymbolTable` (one caller pattern does not earn a trait, so `View` is a concrete
  types-owned value); a cluster-wide macro transaction
  ([macro availability](macro-availability-model.md) §7).
- A cluster is the fully expanded non-macro entry set: one REPL form, the contents of an
  explicit `begin`, or a file's non-structural forms, all on one path
  ([Principle 11](principles/11-single-pipeline-mode-parameters.md)). A source-ordered `defmacro` publishes
  its parent, clauses and generated realizations as a module-local checkpoint once its
  expansion-time closure has typechecked and compiled; a later failure does not roll it
  back. A macro replacement with fewer clauses supplies explicit absent-key ABI-change
  decisions in that publication; omission alone never deletes.
- `instantiate_demands` is the sibling entry point that replays `MonoDemand`s on reload.
- Contracts: [BC 2](bounded-contexts.md#2-typecheck-cratescranelisp-typecheck) (the cluster
  definition and invariants 2, 3a, 7, 10 and 11),
  [BC 6](bounded-contexts.md#6-binary-int-src-cratescranelisp-exe-bundle) and
  [macro availability](macro-availability-model.md). Exact signatures are the rustdoc on
  `check_forms` and `SymbolTableAccess` in `crates/cranelisp-typecheck/src/`.

---

## ADT Support Types

`TypeDefInfo`, `TraitDeclInfo` and `FieldInfo` are the persisted type and trait metadata.
Constructor facts live on `CallableOrigin::Ctor`, not in a parallel record.

### ADT recipes — `AdtCtorSpec` + `build_adt_entries`

- `build_adt_entries` (`crates/cranelisp-types/src/adt_build.rs`) is the one pure derivation
  shared by user `deftype` registration and synthetic bootstrap seeds
  ([Principle 24](principles/24-resolve-once.md)).
- It owns the product/sum split, constructor schemes, synthesised bodies, positional tags,
  canonical `member_key` keys, bare-name candidate exposures and the single `TypeDefInfo`
  derivation.
- It returns slot-free recipes. Callers keep only stateful policy: resolve field types,
  submit each recipe to `install_template` or `install_concrete`, and run the bare-alias
  contest policy. No raw slot crosses this boundary and the builder never constructs a
  callable `Binding`.
- The result is generic over the target table's `CodeStore`; consumers must not unwrap and
  rebuild bindings.
- Pin:
  `crates/cranelisp-types/src/adt_build/tests.rs::generic_constructor_recipe_has_no_slot_or_lifecycle_state`.

---

## Module System

[Symbol-table lifecycle](symbol-table-lifecycle.md) is the contract for declaration
ownership, slot conservation and atomic publication. This section maps the facade onto it.

### Symbol table and binding tree

- `SymbolTables` is a concurrent map from module path to `SymbolTable`. Each table owns a
  private ordinary map mutated under its guard. There is no per-symbol concurrent map and no
  shared-pointer wrapper; that distinction is load-bearing.
- The shape is `Binding` → `Decl` → `Callable` → `Life`. Visibility is stored once on
  `Binding`. Metadata lives on the facet that owns it. A product constructor's type facet is
  `CallableOrigin::Ctor { type_def }`, and `Binding::type_def_info` is the single read-through.
- One symbol map holds, per spelling, an optional canonical binding and its visible
  `NameCandidate` references. An accessor and a trait method can share a spelling without
  either gaining a second storage identity.
- Reads go through `get`, `public_symbols`, `all_symbols`, `codegen_targets`, the candidate
  iterators and typed projections. No public iterator has write capability.
- `codegen_targets` is exactly the concrete body realization projection over direct
  callables, overload arms and macro clauses. Templates, inline and host-promised callables,
  extern, platform and facade realizations, and broken entries are excluded by lifecycle
  shape.
- `CodeStore` and `LinkerStore` are sealed marker traits; only `arch` extends that boundary.

### Lifecycle authoring facade

- Born-settled callables enter through `install_template`, `install_concrete`,
  `install_extern`, `install_inline`, `install_host_promised`, `install_platform`,
  `install_overloaded`, `install_macro` and `install_instance`. `install_binding` accepts
  only aliases, ambiguity sentinels and non-callable declarations.
- Checked source bodies settle through `settle_checked_template` and
  `settle_checked_concrete`, atomically across scheme, source body, view, callees and slot.
- `publish_body_ownership` stamps an annotated view together with its summary; there is no
  one-sided summary setter.
- `mark_broken` owns the concrete-to-broken transition and returns the displaced compiled
  owner.
- `remove_non_callable` and `discard_declared` are the only cleanup surfaces.
- All slot minting, rebinding, displacement and retirement stays inside `SymbolTable`. There
  is no public allocator and no raw callable insertion.
- Live publication is module-atomic. The binary supplies the complete decision set for a
  staging table; the table publishes every binding and slot move or none, records retired
  slots, and returns displaced compiled owners for the binary to retain.
- `install_trait_method` stores a `TraitMethodRecord` at its canonical member key and adds a
  candidate under the bare spelling. The record is a resolution terminal only: it never
  enters `Life`, owns a slot or view, or appears in `codegen_targets`.
- Public declaration records are `#[non_exhaustive]` and are authored across crates only
  through role-specific constructors. The external-consumer test
  `crates/cranelisp-types/tests/lifecycle_facade.rs` exercises them, because an in-crate test
  cannot detect a constructor missing from such a record.

**Proposed, not presented for approval.** `settle_template` and `settle_concrete` have no
cross-crate production caller (source census, 2026-09-21), so they would become
types-private. This is an inter-crate public-API removal and needs the user's approval
before any change.

### Checked-registration transaction facade

`RetainedCallables` and `StagedImplShell` are opaque, non-`Clone`, non-serde rollback tokens
for trait-implementation registration.

- Callable rollback restores or removes the named unpublished method entries with their
  prior claims. It refuses to reclaim a fresh non-null GOT row or a code-bearing body.
- Shell rollback verifies the staged occupant before restoring it.
- The writer record is upserted as the final fallible act, so the previous record is
  untouched until success.
- Fresh registration may stage a divergent same-key re-implementation. Cache restore uses
  `enrol_written_trait_impl`, where divergence is a hard error.

### Instance identity funnel

- `InstanceLink` and `MonoDemand` carry the selected template (`CallableTarget`) and one
  `ConcreteType` per generalised variable. The order is first structural occurrence in the
  template scheme: parameters before result, repeated variables once, higher-kinded heads
  before their arguments. It is neither value-parameter order nor numeric variable order.
- `instance_key` applies those substitutions to the template scheme and delegates to
  `concrete_callable_key`, which encodes the authored owner and the complete concrete
  signature including the result, with no arm ordinal. Contract:
  [uniform executable identity](s122-overload-reorder-publication.md).
- `install_instance` derives the storage key from the settled instance scheme and records the
  link. One private validator compares every concrete binding's key with that derivation,
  before install mutation and again in `validate_lifecycle` after restore. A mismatch is
  `LifecycleError::InstanceKeyMismatch`, which cache load treats as stale.
- Macro-clause demands are rejected. There is no ordinal or substitution-key compatibility
  constructor.
- Producer and replay rules:
  [BC 2](bounded-contexts.md#2-typecheck-cratescranelisp-typecheck).

### Slot and cache authority

- Slots occur only in `Life::Concrete`, `Life::Broken`, a declared callable's prior claim and
  the private retired-slot tombstones. Allocation derives its unavailable set from live
  claims plus tombstones; no counter is stored. `CallableSlot` is an opaque newtype, so no
  other crate can mint one.
- The per-module `GotTable` is the runtime pointer source and is rebuilt on restore.
- `validate_lifecycle` checks slot range and uniqueness, concrete schemes, legal origin, state
  and realization pairings, and instance-key identity.
- A serde-visible change to this tree takes a `CACHE_SCHEMA_VERSION` bump
  (`crates/cranelisp-backend/src/cache/mod.rs`); older sidecars are rejected and rebuilt.

### Module aliases

`ModuleAliases` is a separate session-level namespace keyed only by `module_alias_key`. It
is session-live and not serialised. Lookup rules:
[scoped module aliases](module-alias-scoped-lookup.md).

### Macro Support Types

`MacroDeclaration` and `MacroClause` are the lifecycle-side macro records; `DefmacroInfo` and
`MacroParam` are the parse-side ones. Contracts:
[macro availability](macro-availability-model.md) and
[macro expansion ownership](macro-expansion-ownership.md).

---

## Resolution

`ResolutionScope` is the one public name query. Resolving a name is a keyed query over
symbol-table data; nothing scans.

- **Fallback is intrinsic to the scope.** The prelude is an ordinary import (spec §8.8.1).
  The prelude decision is fixed once at scope construction and no fallback-less resolution
  entry point is public. The earlier per-call opt-in flag was forgotten at several sites,
  each a silent accept or skip.
- **Primitive versus view.** The search primitive is types-owned. The caller supplies the
  first-hop `View`: the binary's macro recognition searches committed tables, and typecheck's
  body resolution searches staging over live. Cross-module hops always land in committed
  modules, because staging only ever holds the current cluster's module.
- **One identity on `Resolved`.** It carries the terminal binding and `canonical`, the one
  terminal storage identity. Codegen carriers, `callees` and diagnostics all derive from it;
  a written spelling is never an identity.
- `resolve_macro_head` is the typed macro projection of the one query. Typecheck's
  kind-specific resolvers are crate-side projections of it.
- The prelude retry requires the prelude's own head binding to be public, not merely the
  chain-followed terminal.
- `member_key` is the one mint point for canonical `Type.member` keys, and `bare_member_name`
  is its inverse projection. No site hand-rolls either half of that grammar.
- A bare `/` operator is not a qualified name
  ([Principle 16](principles/16-punctuation-symbols-are-not-special.md)); the split guards
  live inside the resolver.
- `substitute_module_alias` takes the alias table, the referring module and the path. The
  leading segment may use the referring module's alias at either visibility; later segments
  traverse public mounts only. Every step is a keyed probe under the shared chain-depth cap.
  FIXME 0798 is the open filing behind this signature; its disposition against source is
  owed.
- Contracts: [prelude and explicit imports](prelude-import-convergence.md),
  [scoped module aliases](module-alias-scoped-lookup.md) and
  [resolve home before enumeration](resolve-home-enumeration.md).

**Evidence gaps recorded for `qa`.**

- `crates/cranelisp-types/src/resolve/tests.rs::prelude_fallback_remains_public_head_only`
  pins the public leg only. No types test preserves the discriminating case of a private
  prelude head chaining to a public terminal.
- `crates/cranelisp-types/src/resolve/tests.rs::alias_walk_refuses_more_than_the_shared_depth_limit`
  pins the alias walker's cap. The same-module chain-follow arm has no dedicated unit pin.

---

## Macro execution callback — `MacroExpander`

- `MacroExpander` and `MacroInvokeError` are the capability through which one compiled macro
  invocation is executed: (identity, argument `Sexp`s, call span) in, one raw `Sexp` out.
- Recognition is the types resolution query (`resolve_macro_head`); execution — marshalling
  and the signal-protected call — is the binary's, behind the trait. The binary's expand loop
  calls both and re-classifies the result before `check_forms` runs; typecheck holds no
  expander.
- The trait lives in `cranelisp-types` as the named boundary contract, and it adds no
  dependency edge. It is `Send + Sync` because workers may expand concurrently. There is no
  frontend macro trait.
- Contract: [macro expansion ownership](macro-expansion-ownership.md).

---

## Concrete codegen boundary

`ConcreteType`, `MonoExpr`, `MonoDefnVariant`, `NotConcrete` and `ViewBuildError` are the
typed-body boundary. A generic is unrepresentable on a view node, the view is non-optional
state of `Realization::Body`, and heap classification is total over `ConcreteType`.

- Contract: [concrete codegen boundary](concrete-boundary-type.md).
- End-of-typecheck invariant: [total concreteness](total-concreteness.md).

---

## Backend Entry Point

- `compile_to_module` in `cranelisp-backend` is the sole compilation function
  ([Principle 11](principles/11-single-pipeline-mode-parameters.md)). It takes the module, the
  `CallableTarget`s to compile, the session tables and a Cranelift module, and returns
  `CompilationArtifacts`. It is module-type-agnostic: the caller extracts an entry point for
  the JIT or the full map for object emission.
- Backend-owned runtime carriers such as `Jit` and `Code` stay in the backend because they
  hold runtime state. `Realization::Body.code` is the serde-skipped lifecycle owner of
  compiled code; the GOT remains the runtime address source.
- Interior design: `design/backend/compile-to-module.md` and `design/backend/per-module-got.md`.

---

## Heap Classification

`HeapCategory` is backend-owned (`crates/cranelisp-backend/src/heap.rs`); `classify` is its
single source of truth and takes `&ConcreteType`.

## Heap Object Layouts

- `HeapHeader` lives in `cranelisp-types` and is shared by every heap object. `HeapString`
  lives in `cranelisp-intrinsics`; `HeapAdt`, `HeapClosure` and `HeapVec` live in the
  backend. Offsets are associated constants beside each `#[repr(C)]` layout
  ([Principle 14](principles/14-ffi-layout-discipline.md)).
- Spec §12.1 describes these layouts as the current reference representation, not as a
  mandate.

### R5 value-representation flattening

- The types-owned layout predicate (`crates/cranelisp-types/src/heap.rs`) is shared by
  typecheck's copy and uniqueness classification and by the backend's value lowering. A
  disagreement could bit-copy a heap pointer without retaining it, so neither consumer
  derives eligibility independently.
- `value_layout` yields a layout for a scalar, or for a single-constructor ADT with exactly
  one transitively value-eligible field, within `VALUE_LAYOUT_MAX_WORDS`. Multiple
  constructors, heap collections, non-concrete stored field types and cycles are ineligible.
- The walk performs no generic substitution; `ctor_field_types_at` is the distinct
  substituting projection.
- `value_layout_with_lookup` takes the caller's coherent declaration lookup. Typecheck
  supplies a staging-first lookup in which a present staged binding wins even when
  ineligible; the backend uses the same algorithm over its codegen tables.

### Resource scheduling — the `ctx` vtable handle model

- Scheduling state never rides on a value. There is no resource-descriptor header slot and
  no resource-handle layout marking.
- A resource handle is an ordinary ADT carrying the platform's own data in a genuine field.
  It is opaque to the trampoline, not to the user, who may destructure it.
- Runtime scheduling flows through the trampoline-owned `HostCtx` vtable, using
  `ResourceRole` and `Acquire`. `acquire` takes the waker so a parked return can re-poll, and
  is idempotent per in-flight effect. The host releases permits on completion or
  cancellation.
- Contract: [platform interface](platform-interface.md).

### Type-drop glue identity and address boundary

- `drop_glue_symbol_name(module, ConcreteType)` is the one naming authority for a type's drop
  glue. The release symbol for a program result is minted over
  `ConcreteType::result_root`, which strips one `primitives/IO` head.
- The backend result-root enumeration and binary release key both call that rule.
- The binary's result-owner design is `design/int/result-owner.md`.

---

## IO Tag Constants

- `IO_TAG_PURE`, `IO_TAG_EFFECT`, `IO_TAG_BIND` and `IO_TAG_PAR` live in `cranelisp-platform`.
  The IO-node family is a layout contract governed by `cranelisp_platform::ABI_VERSION`
  ([Principle 14](principles/14-ffi-layout-discipline.md)).
- **The `Pure` payload-glue word.** A `Pure` node carries a hidden word after its payload: the
  canonical drop-glue address for the payload's concrete type, or `0` when no discharge is
  owed. The backend stamps it at each construction site, once, before publication. IO values
  are reusable: a force retains the payload and never writes to the node, and teardown alone
  calls through the word.
- **Platform-return stamps are tag-dispatched.** At the backend's one platform-call
  chokepoint the stamp is selected by the returned node's tag, never by the callee's kind.
  An `Effect` node receives the function-name pointer, a `Pure` node receives the
  payload-glue word, and any other tag receives no write. A kind-keyed unconditional store
  would be an out-of-bounds write for a `Pure`-returning platform function. The platform's
  only legal glue-word write is `0`; the backend is the sole stamp authority.
- Contract: [total concreteness](total-concreteness.md) (the payload-glue section) and
  [safety invariants](safety-invariants.md) rows R19 and R20.
