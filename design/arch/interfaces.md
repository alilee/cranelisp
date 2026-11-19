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
- Every consumer classifies quotes through this one predicate: the frontend quasiquote fold,
  and the binary's scope-aware expansion shields (`src/expander.rs`), qualification shields
  (`src/process_form/macro_resolution.rs`) and written-qualifier dependency walk
  (`src/process_form/dependency.rs`). No consumer keeps a local classifier. If their notions
  of "is a quote" diverged, a quoted subtree would be double-desugared, mis-qualified or
  mis-recorded as a dependency.
- The reader still lowers the quote sugars to list forms; the predicate only classifies them.

---

## Module Declarations

The frontend's `extract_module_declarations` separates module-structure forms from the
remaining forms. The extracted `ImportSpec`, `ExportSpec`, platform and submodule
declarations live on the module's `SymbolTable` in its public structural vectors. Those
vectors are the append contract: direct push, source order, no deduplication.

### Import and export entries

Spec §8.3 and §8.3.11 classify each entry of a names list independently, and §8.4 applies the
same grammar to exports with a mount alias. Exact promises: the rustdoc on `ImportEntry`,
`ImportNames` and `ExportSpec` (`crates/cranelisp-types/src/module.rs`).

- **One entry type serves imports and exports.** `ImportEntry` is `Name { source, local }`
  or `MemberGlob(parent)`, and `ImportNames::Specific` holds a vector of entries. A mixed
  list is representable; a list-level member glob is not.
- **`source`** is the name in the source module and may be dotted. **`local`** is the bare
  name the entry binds and is always present: the written name of a plain entry, the member
  of a dotted entry, or the second symbol of a rename.
- **The frontend derives `local` once; no consumer re-derives it**
  ([Principle 24](principles/24-resolve-once.md)). The installer binds `local` to `source`
  and never reads a written spelling, so binding a dotted entry under its dotted spelling
  has no representation.
- **The member of a dotted entry is read by the frontend's own dotted splitter.** The
  frontend must split a written entry to classify and validate it, so the member falls out
  of that one read. `cranelisp_types::bare_member_name` is not called there: it also strips
  a `/` qualifier, which an entry source may not carry. The installer's member-glob
  projection keeps `bare_member_name`, over canonical member keys. *Falsifier:* a dotted
  entry and the member glob of its parent binding different local names for one member.
- **`ExportSpec::alias`** is the §8.4.4 mount, mirroring `ImportSpec::alias`. Its storage,
  writer and lookup are the [alias contract](module-alias-scoped-lookup.md) §2.1 and §5.1.
- **`ImportNames` carries no `#[non_exhaustive]`.** Its consumers match it exhaustively on
  purpose, so a new list shape forces every installer, regenerator and selector to be
  revisited.
- **Persistence.** `SymbolTable::imports` and `exports` are persisted, so a change to either
  shape takes a `CACHE_SCHEMA_VERSION` bump.
- **Surfaces.** Types carries the type; the frontend's module extraction is the only
  producer; the binary's import installation, source regeneration, dependency recording,
  cache restore, indexing, lifecycle and test selection are the consumers. Typecheck does not
  read the carrier.

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
- A summary on a `Realization::ExternShim` callable is analysis input only: the primary entry
  follows the uniform consuming convention and no call site adapts to the declared facts
  ([safety invariants](safety-invariants.md) row R22).
- No dev-tier emission reads a summary: every call position consumes its arguments whatever
  the callee's summary ([safety invariants](safety-invariants.md) rows R1 and R22). The facts
  stay produced, published and persisted for the release tier
  ([Principle 27](principles/27-dev-tier-optimises-only-against-blow-up.md)).
- `ResultMode` is a closed sum without `#[non_exhaustive]`, so a new variant forces each
  consumer match to be revisited. An equality read against `Fresh` would escape that
  forcing; none exists in production. Re-run the wildcard and equality census when adding a
  variant.
- **The surface offers no ABI comparison of summaries.** A compiled slot's contract does not
  depend on its summary, so a same-type live redefinition publishes whatever its inferred
  modes
  ([ownership inference §5](ownership-inference.md#5-mode-summaries-module-caching-and-the-r3-redefinition-model-part-4)).
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
- `instantiate_demands` is the sibling entry point that replays `MonoDemand`s when a REPL
  turn redefines a generic base or overload family. A module reload replays no demands.
- Contracts: [BC 2](bounded-contexts.md#2-typecheck-cratescranelisp-typecheck) (the cluster
  definition and invariants 2, 3a, 7, 10 and 11),
  [BC 6](bounded-contexts.md#6-binary-int-src-cratescranelisp-exe-bundle) and
  [macro availability](macro-availability-model.md). Exact signatures are the rustdoc on
  `check_forms` and `SymbolTableAccess` in `crates/cranelisp-typecheck/src/`.

### Resolution gaps

`ResolutionGap` is the recoverable "this dependency is not ready" value inside
`CheckError::Gap`. It carries no span and is never persisted.

- **Producer.** Typecheck alone: value position's qualified walk
  (`resolve_qualified`, `SymbolTypechecked`), type position (`Type`) and
  `instantiate_demands` (`SymbolTypechecked` on a demand owner's absent home).
- **Consumer.** The binary alone. It reads the gap's module to choose what to load or park
  on, and the module and member to word and place the diagnostic (`gap_target_module`,
  `gap_member`, the gap arm of cluster finalization, the macro checkpoint, and
  `GapReference`). The worker's validation paths print a surviving gap in an error.
- **Macro recognition raises no gap.** Frontend raises none. The binary's macro-head
  recognition substitutes the alias itself and drives the module without a gap value; a head
  whose module is present and lacks the member is not a macro and reaches typecheck as a
  value reference. The sum has no macro variant
  ([batch record](#approved-changes-not-yet-in-source-s124), row ACT-1084).
- **The module a gap names, in source.** An absent module is named after alias substitution
  (spec §8.6.6), because the resolver's error supplies it. A member absent from a present
  module is named by the qualifier as written, so an alias-spelled reference names a module
  that does not exist.
- **Approved by `arch` 2026-11-19, not in source, not scheduled.** Every gap names the
  module resolution probed: the written qualifier after one alias substitution from the
  referring module. A gap's module is then an identity like every other resolved-stage
  `FQSymbol` ([Principle 24](principles/24-resolve-once.md)), and the binary substitutes
  nothing. The specification already requires the behaviour (§8.6.6, §8.5.4 edge 4).
  ACT-1082's four failing cells carry it.
  - Typecheck applies `substitute_module_alias` to the written qualifier in the
    member-absent arm, with the alias table and referring module its scope resolve used.
    Typecheck already calls that function, so no consumer edge is added.
  - Substitution is applied to a written qualifier only, and once. It is not idempotent:
    with aliases `a → b.c` and `b → q`, substituting `a` twice yields `q.c`. This is why the
    consumer cannot repair the gap, which does not say which form it carries.
  - The resolver's `*NotFound` errors are not the source. Their `from_module` has no one
    meaning: typecheck's own projections set it to the current module, the name or the
    empty path.
  - Grade once built: measured, by a typecheck module test at `resolve_qualified` and the
    alias cells of `tests/spec_08_modules.rs`. A written qualifier and a resolved module
    share the type `ModuleFullPath`, so the rule is not structural.

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
  extern, platform and facade realizations are excluded by lifecycle shape.
- `CodeStore` and `LinkerStore` are sealed marker traits; only `arch` extends that boundary.

### Lifecycle authoring facade

- Born-settled callables enter through `install_template`, `install_concrete`,
  `install_extern`, `install_inline`, `install_host_promised`, `install_platform`,
  `install_overloaded`, `install_macro` and `install_instance`. `install_binding` accepts
  only aliases, ambiguity sentinels and non-callable declarations.
- Checked source bodies settle through `settle_checked_template` and
  `settle_checked_concrete`, atomically across scheme, source body, view, callees and slot.
  They are the only public settle entries; the unchecked `settle_template` and
  `settle_concrete` compile for the types crate's module tests alone.
- `publish_body_ownership` stamps an annotated view together with its summary; there is no
  one-sided summary setter.
- `remove_non_callable` and `discard_declared` are the only live-table cleanup surfaces.
  `release_callable` is offered only on a decoded `SymbolTable<(), ()>`
  ([symbol-table lifecycle §4.3](symbol-table-lifecycle.md#43-slot-identity)).
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

- Slots occur only in `Life::Concrete`, a declared callable's prior claim and the private
  retired-slot tombstones. Allocation derives its unavailable set from live
  claims plus tombstones; no counter is stored. `CallableSlot` is an opaque newtype, so no
  other crate can mint one.
- The per-module `GotTable` is the runtime pointer source and is rebuilt on restore. A
  whole-file rebuild keeps it under a new table
  ([symbol-table lifecycle §4.3](symbol-table-lifecycle.md#43-slot-identity)).
- `validate_lifecycle` checks slot range and uniqueness, concrete schemes, legal origin, state
  and realization pairings, and instance-key identity.
- A serde-visible change to this tree takes a `CACHE_SCHEMA_VERSION` bump
  (`crates/cranelisp-backend/src/cache/mod.rs`); older sidecars are rejected and rebuilt.

### Qualified lookup dependencies

**Status: implemented at `56e4d2e1` (2026-09-26); QA evidence adequate; phase acceptance pending.**
- The exact three-entry types API and cache schema 30 match the user's approval
  (`sprints/archive/sprint-122.md` §"Lookup dependency implementation approval — 2026-09-26").
  The user confirmed the generated types baseline diff (+3/−0) on 2026-09-26.
- One full suite passed on the delivered source (6,144 of 6,144). Independent types
  and int reviews leave no open blocking or required finding, and QA's evidence
  adequacy is recorded in the [evidence plan](../../tests/plan/s122-evidence-delta.md#adequacy-2026-09-26).
- LD-9, the empty-expansion dependency loss, is corrected and independently
  reviewed in the uncommitted tree ([int §7.6.2.1](../int/int.md#7621-empty-publication-correction));
  its regression and allocated module evidence pass.
- This realizes the user's conservative module-hash direction. Selective reuse and
  optimisation-aware invalidation are [ACT-0992](../../sprints/actions/ACT-0992-optimisation-aware-cache-invalidation.md).

- **Fact.** A module's lookup dependencies are the modules whose tables answered a qualified
  reference while that module compiled, after spec §8.6.6 alias substitution. They cover every
  reference kind, including constructors, patterns, accessors, types, traits and macro heads.
  Terminal `callees` keep their meaning.
- **Carriers.** `Resolved.lookup_module` names the answering module for a qualified spelling
  resolved outside the current module. It is provenance, not an identity. Each `SymbolTable`
  persists its set, read through `lookup_dependencies` and written only through
  `record_lookup_dependency`.
- **Maintenance.** Producers record into the cluster's staging table, and staged publication
  unions the set into the live table. A gap or failure discards staging, and restore
  installs the persisted set. No removal exists: the set is rebuilt only when the module is
  recompiled from source into a new table, as a whole-file rebuild does
  ([symbol-table lifecycle §4.3](symbol-table-lifecycle.md#43-slot-identity)). A stale member
  after a REPL redefinition costs a cache miss or an extra reload recompile, never a stale
  restore.
- **Use.** The dependency record's edges include the set, so it governs cache validity.
  It is not a load edge. Restore does not load these modules; a later compilation that needs
  one loads it on demand (spec §8.5.4). Object loading and `--link` contents still follow
  declared and callee edges ([dependency record](../int/int.md#76-dependency-record-and-validity)).
- **Reload selection and ordering (approved 2026-09-29; implementation in progress).** The
  same recorded edges, callee modules and this set, make a module a reload dependent of each
  module they name, alongside imports, exports and the prelude (REPL spec §14.2 step 4).
  They also order the plan: a whole-file rebuild reuses GOT slot indices, so a dependent must
  rebuild after every module it names that the same plan rebuilds. A failed compile records
  nothing, so Binary/int must keep a failed dependent selectable by the module whose repair
  releases it (§14.6). Mechanism:
  [REPL lifecycle §1.2](../int/repl-lifecycle.md#12-poll-and-reload) and
  [session transaction §7.3](../int/session-transaction.md#73-the-watcher-and-reload-path).
- **Schema.** The field has no `#[serde(default)]`, and its addition bumps
  `CACHE_SCHEMA_VERSION`.

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
  `module_alias_key` is the one alias-key mint.
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
  `CodegenTarget`s to compile, the session tables and a Cranelift module, and returns
  `CompilationArtifacts`. A `CodegenTarget` pairs one `CallableTarget` with the modules a
  trace form in its body covers
  ([tracing §5.1.1](tracing.md#511-how-the-set-reaches-the-backend)). It is module-type-agnostic: the caller extracts an entry point for
  the JIT or the full map for object emission.
- Backend-owned runtime carriers such as `Jit` and `Code` stay in the backend because they
  hold runtime state. `Realization::Body.code` is the serde-skipped lifecycle owner of
  compiled code; the GOT remains the runtime address source.
- Interior design: `design/backend/compile-to-module.md` and `design/backend/per-module-got.md`.

---

## Heap Classification

`HeapCategory` is backend-owned (`crates/cranelisp-backend/src/heap.rs`); `classify` is its
single source of truth and takes `&ConcreteType`. It is public because the binary's result
exit (`src/result_owner.rs`) classifies through it.

It has no flattened-value category: S124 removed `HeapCategory::Value` and the lowering
behind it (packet row D4, `441e31ea`;
[Principle 27](principles/27-dev-tier-optimises-only-against-blow-up.md)), so a one-word
single-constructor value classifies as a heap value. The binary's display walk
(`src/display.rs`) renders by the same layout and follows the backend's classification.

## Heap Object Layouts

- `HeapHeader` lives in `cranelisp-types` and is shared by every heap object. `HeapString`,
  `HeapAdt` and `HeapClosure` live in `cranelisp-intrinsics`; the ADT and closure layouts
  are `cranelisp_intrinsics::alloc` items. The Vec layout's offsets are
  `cranelisp_intrinsics::vec_runtime::{LEN_OFFSET, CAP_OFFSET, DATA_PTR_OFFSET}`. The backend
  and the binary read all of them from intrinsics and define none. Primitives' `marshal.rs`
  still restates the ADT offsets; its edge to `alloc::HeapAdt` is approved (S124 packet row
  R10-9) and not built. Offsets are associated constants beside each `#[repr(C)]` layout
  ([Principle 14](principles/14-ffi-layout-discipline.md)).
- Spec §12.1 describes these layouts as the current reference representation, not as a
  mandate.

### R5 value-representation flattening

- The types-owned layout predicate (`crates/cranelisp-types/src/heap.rs`) is shared by
  typecheck's copy and uniqueness classification and by the backend's value lowering. A
  disagreement could bit-copy a heap pointer without retaining it, so neither consumer
  derives eligibility independently.
- After the approved removal above the backend reads the predicate nowhere. It stays public,
  typecheck keeps classifying through it, and its producer tests stay: it is a retained
  release-tier fact. The coupling hazard returns with any future backend reader, which must
  delegate to it.
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

---

## Approved changes not yet in source (S124)

The public-API batch record ([discipline](AGENTS.md#public-api-discipline)). A row is a
decided change that no phase checkpoint has reported yet; a row that names a commit is in
source and stays until the Phase 5 checkpoint reports it. Source was read at `f8c55626`, and
at `518489c2` for the rows dated 2026-11-20. The user approved the rows marked
*user*; `arch` approved the rows dated 2026-11-19 and 2026-11-20 against the three questions
(bounded context, simple API, strongly typed), with a yes to each for every module the row
touches. The exact delta of a
*user* row is in the [S124 packet](../../sprints/s124-api-packet.md) (D rows, R10-9 and
R10-10) or the [S123 packet](../../sprints/s123-api-packet.md) Part B (K11 and R10-1 to
R10-8), and is not restated. S123 row R10-6 is superseded by R10-9 and does not land. A
design that needs a public change outside these rows stops and returns to `arch`.

| Row | Change | Owning surface | Other surfaces that change | Baseline | Decided | Contract |
|---|---|---|---|---|---|---|
| D6 (R10-8) | `Realization::ExternShim::borrowed_sibling` removed; `CACHE_SCHEMA_VERSION` goes up by one | types | backend cache validation; test fixtures in typecheck | types −1: the field line. The variant line is unchanged, because a unit variant and a struct variant print alike. In source at `07bb8e84` | user, 2026-11-16 | [safety invariants](safety-invariants.md) row R5 |
| D13 | `SymbolTable::install_extern` loses its sixth parameter, `borrowed_sibling: Option<CallableSlot>`. Every caller passes `None`. No schema effect beyond D6's | types | primitives (the one production caller); test callers in backend, typecheck and the binary | types 1 changed. In source at `07bb8e84` | `arch`, 2026-11-19 | [safety invariants](safety-invariants.md) row R5 |
| D9 | `CacheStale::SiblingSlotOutOfRange` removed | backend | — | backend −3. In source at `07bb8e84` | user, 2026-11-16 | [safety invariants](safety-invariants.md) row R5 |
| K11-c | `SymbolTable::{settle_template, settle_concrete}` leave the public surface. Their only callers are the types crate's module tests, so they compile under `#[cfg(test)]` as `pub(crate)`. In source at `cc04b162` | types | — | types −2 | user, 2026-11-16; this realisation `arch`, 2026-11-19 | [lifecycle authoring facade](#lifecycle-authoring-facade) |
| K11-d | `MonoExpr::lenient_from_expr` becomes `pub(crate)`. `cranelisp_types::test_support::lenient_from_expr`, a free function with the same parameters and result, forwards to it under the `test-support` feature. In source: the forwarding function at `bf15e0d6`, the narrowing at `0b5d9dc6` | types | test code only: two calls in the backend's `test_support.rs` (`994137dd`) and nineteen in the binary's test modules (`0478d340`). Both crates' dev-dependencies on `cranelisp-types` enable `test-support` | types −1 | user, 2026-11-16; this realisation `arch`, 2026-11-19 | [concrete codegen boundary §3.1.1](concrete-boundary-type.md#311-signature-driven-targets) |
| R10-2 | The backend's `artefact` module, `LinkerArtefact`, `ObjectArtefact` and their root re-exports are deleted. The row approved narrowing; with `load_object` gone (R10-1) the types have no producer. The public effect is the row's. In source at `06210347` | backend | — | backend −42 | user, 2026-11-16; deletion `arch`, 2026-11-19 | — |
| Gap module | `ResolutionGap::SymbolTypechecked` names the module resolution probed: the written qualifier after one alias substitution. No item changes | types (meaning); typecheck (producer) | the binary stops reading the module as a written qualifier | +0 | `arch`, 2026-11-19; not scheduled (ACT-1082) | [resolution gaps](#resolution-gaps) |
| ACT-1084 | `ResolutionGap::MacroInMem` removed. It had no producer. In source from step 4's one commit, which holds the types and binary halves | types | the binary's two match arms in `src/process_form/dependency.rs` and one module test; a stale comment in `tests/process_form_dispatch.rs` | types −1 | `arch`, 2026-11-19 | [resolution gaps](#resolution-gaps) |
| Trace reader | `cranelisp_intrinsics::trace::cranelisp_trace_first_child_nanos` removed with its catalog entry. It has no caller. The export is still in source (step 3b) | intrinsics | backend dropped the name from `is_extern_primitive` (`717dd3a1`); the [BC §4b](bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics) conventions table and [tracing §4.1](tracing.md#41-the-trace-bodies-and-the-catalog) no longer list it | intrinsics −1 | `arch`, 2026-11-19 | [tracing §4.1](tracing.md#41-the-trace-bodies-and-the-catalog) |
| B13 (ACT-1070) | `Jit::jit_module` returns `&mut (impl cranelift_module::Module + CodeFinalizer)`, not `&mut JITModule`. `impl CodeFinalizer for cranelift_jit::JITModule` is removed. The returned module is a crate-private wrapper that compiles every call far. No public type is added. The method's rustdoc states the promise: no call in a function defined through this module depends on where the JIT places code. In source at `790f4c9a` as `jit::FarCallModule` | backend | none; the binary's four callers pass the value straight to `compile_to_module` and do not name its type | backend −4, 1 changed, +0; measured at the build | `arch`, 2026-11-19 | [JIT/object convergence §3](../backend/jit-object-convergence.md#3-call-reach-in-the-jit-act-1070) |
| B10 (ACT-1039, ACT-1078) | `compile_to_module` gains `trace_modules: &BTreeSet<ModuleFullPath>` after `symbol_tables`: the modules a trace form in `module_path` covers besides `module_path`. Passed at every call | backend | the binary's two production callers, from int's one reference-edge enumerator; test callers in backend and the binary | backend 1 changed; no persisted shape. In source at `69cd9c18` and `f8c55626` | `arch`, 2026-11-19, after the user's ruling on the covered set the same day | [tracing §5.1.1](tracing.md#511-how-the-set-reaches-the-backend) |
| B10-C2 (ACT-1086) | The covered set travels with each target. New `cranelisp_backend::CodegenTarget<'a>`, with private fields and `new(&'a CallableTarget, &'a BTreeSet<ModuleFullPath>)`. `compile_to_module` takes `targets: &[CodegenTarget<'_>]` and loses `trace_modules`. A target's set is every module a form in its body covers, including the module whose source holds the body; the backend adds none, and reads from `module_path`'s table only the instances whose template module is listed when `module_path` is not. In source at `94749709` | backend | the binary's two production callers derive one set per module of origin and pair each target with its set; test callers in backend and the binary | backend +9 in the present format (the type, `new`, seven generated auto-trait rows); `compile_to_module` changed again. No persisted shape, schema or ABI; an object holding a form in an instance changes content and the build identity separates it | `arch`, 2026-11-20, under the user's ruling of 2026-11-19 (spec §4.12.3) | [tracing §5.1.1](tracing.md#511-how-the-set-reaches-the-backend) |
| Template module (ACT-1086) | `CallableArm::<C>::template_module(&self) -> Option<&ModuleFullPath>`: the module defining the template of a minted instance, read from `Life::Concrete::minted_from`; `None` otherwise. One reading of the fact for the two crates that need it. In source at `bb217cdc` | types | the binary (which module holds a target's body) and the backend (which instances in `module_path`'s table a form covers) | types +1; no persisted shape | `arch`, 2026-11-20 | [tracing §5.1.1](tracing.md#511-how-the-set-reaches-the-backend) |
| B15 (FIXME 0915) | A codegen failure with no failing member is its own variant. `CompilationError` gains `ModuleFailed { module: ModuleFullPath, cause: String, location: ErrorLocation }`. `impl From<CranelispError> for CompilationError` is removed: it is the conversion that fills `module` and `symbol` with empty strings, and the backend converts through a crate-private function that takes the module. `CompilationError::ModuleError` is removed; it has no producer. `CodegenFailed` keeps its fields and always names a failing target. In source at `9bee5930` | backend | none in production: the binary reaches the type only through `From<CompilationError> for CranelispError`, which stays and gains the new arm. `src/worker/tests.rs` matches `CodegenFailed` and is unchanged | backend +8, −12: the enum is listed at two paths (the new variant and its three fields; `ModuleError` and its three fields) and the conversion at two (the impl and its function). `dev`(backend) read the same +8, −12 from source against the committed listing at the build; the generator has not run. No persisted shape | `arch`, 2026-11-20 | [the unattributed failure](#the-unattributed-codegen-failure-row-b15) |
| K11-a | Baseline format omits generated auto-trait rows; seven baselines regenerate together | all seven guarded crates | the public-API guard; `tests/AGENTS.md`; a compile fence in the platform crate's module tests | removals only | user, 2026-11-16 | [baseline-diff discipline](AGENTS.md#baseline-diff-discipline-sprint-67-close) |

In source and awaiting the checkpoint report: D6, D13 and D9 (`07bb8e84`), R10-2
(`06210347`), B13 (`790f4c9a`), B10 (`69cd9c18`, `f8c55626`), B10-C2 (`94749709`), B15
(`9bee5930`), the template module (`bb217cdc`), K11-c (`cc04b162`) and K11-d (`bf15e0d6`,
`994137dd`, `0478d340`, `0b5d9dc6`). The trace-reader row is part built: the backend half
is in source (`717dd3a1`) and the export's removal is step 3b. ACT-1084 is in source from
step 4's commit. The gap-module row is not scheduled.

### The unattributed codegen failure (row B15)

- **The state it removed.** A failure outside any one target, such as a missing module
  table, a missing intrinsic, the glue fence or GOT emission, has a module and no symbol.
  `CodegenFailed::symbol` is a `Symbol`, so the generic conversion filled it, and `module`,
  with an empty string, and the failure rendered `codegen failed for /`
  ([release contract](../backend/non-concrete-release-contract.md) §7.2.1,
  *Unattributed*).
- **Contract.** `CodegenFailed` is a failing target: `module` and `symbol` name it and
  neither is empty. `ModuleFailed` is a failure of the module's compilation with no failing
  target, and renders the module as its only subject. The backend has no conversion that
  produces either without a module, so a site that forgets the module does not compile.
- **The three questions.**
  - *Bounded context:* yes. The error type stays with the crate that raises it
    ([Principle 15](principles/15-facade-types-live-with-behavior.md)); both removed items
    have no consumer in another crate
    ([Principle 02](principles/02-narrow-interfaces.md)).
  - *Simple API:* yes. One variant per subject; the binary still renders through the one
    outward conversion and tests no field for emptiness.
  - *Strongly typed:* yes. The absent subject is a variant, not an empty string
    ([Principle 20](principles/20-model-invariants-by-representation.md)).
- **Not chosen.** `symbol: Option<Symbol>` on `CodegenFailed` leaves every reader of a
  failing target handling an absence that target never has.
- **Rendering.** The message text of both variants is `design`(backend)'s, under Rule 3
  of the same section. No specification text names it.

**Remaining build order.** The rows land one after another, in this order, when the build is
free. `arch` builds the types changes; `dev` builds each other surface, one surface per
invocation; `test` owns files under `tests/`. No row changes a persisted shape or a schema
version. Built and removed from this table: A1 (row B15, `9bee5930`), A2 (the object pass
waits for an unpublished covered member,
[int §7.6.4](../int/int.md#764-reference-edges-and-the-covered-trace-set-row-b10) C1,
`fe385164`; no public item), A3a (`bb217cdc`), A3b and A3c (`94749709`), step 1
(`cc04b162`), steps 2a to 2d (`bf15e0d6`, `994137dd`, `0478d340`, `0b5d9dc6`), step 3a
(`717dd3a1`) and step 3c (the documents, written to hold before and after 3b).

| # | Row and step | Role | Builds alone | Commit |
|---|---|---|---|---|
| 3b | Intrinsics removes the function, its catalog entry, the catalog and handle-census test rows and its two module tests | `dev`(intrinsics) | yes | one |
| 4c | **ACT-1084.** The comment in `tests/process_form_dispatch.rs` that names a frontend `MacroInMem` producer | `test` | comment only | one |
| 5 | **Checkpoint, present format.** The seven baselines are regenerated on the final tree and compared with the table below. `arch` deletes ACT-1033 here: row D11 is in source and its last completion condition is this baseline. `qa` drops its two links to the file in the same wave | `arch` | — | one |
| 6 | **K11-a.** The guard, `tests/AGENTS.md` and the [canonical command](AGENTS.md#baseline-diff-discipline-sprint-67-close) take `--omit auto-trait-impls`; the seven baselines are regenerated again; the guard's detection proof is repeated | `test` (guard and `tests/AGENTS.md`), then `arch` | the guard fails between the halves | one commit, from one uncommitted tree |

- Step 3b builds alone. Nothing names the reader outside intrinsics, so it changes no
  generated code. When it lands, the trace-reader row and the sentence about the reader in
  [tracing §4.1](tracing.md#41-the-trace-bodies-and-the-catalog) state it as removed.
- Steps 4a and 4b (types removes the variant; the binary removes its two arms, the comment
  above them and the module test) are one commit, built callee-first from one tree.
- `arch` deletes ACT-1084 at step 5, after 4c. `qa` drops its link to the file in
  `tests/plan/s124-evidence-delta.md` in the same wave. Two design documents still name a
  frontend producer and are their owners' to correct: `design/typecheck/typecheck.md` §7.3
  and `design/int/int.md` §6.3.1.
- Step 6 follows the user's confirmation of step 5's diff. Its diff holds removals only.

**Expected regenerated diff at the Phase 5 checkpoint (step 5).** Counted against the
committed baselines, which predate every S124 row, and against source after step 4. Removed
lines are counted in the committed files. Added and changed lines are read from source and
are estimates; the regenerated diff is the exact figure. The table includes the rows that
left this record when they were built, whose deltas are in the
[S124 packet](../../sprints/s124-api-packet.md) and the
[S123 packet](../../sprints/s123-api-packet.md) Part B. A line outside this table returns
to the user. The figures at the checkpoint are unchanged since the table was first counted
at `f8c55626`; rows have moved from *remaining* to *in source*.

| Crate | In source after step 4 | Remaining rows | At the checkpoint |
|---|---|---|---|
| types | +17, −9, 3 changed. D3: +13, −1, `ImportNames::Specific` changed. D10: +3, `WrittenTraitImpl::new` changed. D7: −3. D6: −1. D13: `install_extern` changed. Template module +1. K11-c −2. K11-d −1. ACT-1084 −1 | none | **+17, −9, 3 changed** |
| backend | +17, −182, 2 changed. R10-1 −1; R10-2 −42; R10-3 −41; D2 −23; R10-5 −1; R10-7 −6; R10-9 −49; D4 −1; D9 −3; B13 −4 and `Jit::jit_module` changed; B10 `compile_to_module` changed, and changed again by B10-C2 (the same line); B10-C2 +9; B15 +8, −12. The removal figures of the rows before B15 sum to 171 and share one line | none | **+17, −182, 2 changed** |
| intrinsics | +33, −5, 1 changed. R10-9: +33. D5 −2; K11-b −2; D11 −1 and `string_read` changed | Trace reader −1 | **+33, −6, 1 changed** |
| typecheck, frontend, primitives, platform | +0 | none | **+0** |

K11-a's contraction (step 6) is every generated auto-trait row left after step 5. Counted by
pattern, with the rows this table adds and removes: types about −973, backend about −147,
intrinsics about −91, typecheck about −70, frontend −14, platform about −196, primitives 0.

Declined, `arch`, 2026-11-19:

- **`CallableOrigin::TraitMethod` carrying its member** (`member: Symbol`; types +1,
  schema bump). Typecheck writes the origin and is the only reader that wants the member,
  so the field would grow a shared persisted type for one crate's interior (bounded
  context). The field would not remove an invalid state: a member the trait lacks is as
  expressible as an entry no member names (strongly typed). Typecheck recovers the member by matching each of the trait's members' mangled entry
  name, and refuses an entry no member names. Grade: asserted. Reopened by a second reader
  in another crate, or by two members of one trait mangling to one entry.

- **A public `jit::FarJitModule`** with public `Module` and `CodeFinalizer` implementations,
  as [JIT/object convergence §3](../backend/jit-object-convergence.md#3-call-reach-in-the-jit-act-1070)
  proposed for row B13. No crate outside the backend names the JIT's module type, so the
  name has no consumer (bounded context), and the binary's one path is to pass the value
  to `compile_to_module`, which an opaque return expresses and a nameable `Module` does
  not (simple API). The opaque wrapper carries the same type guarantee: with the
  `JITModule` implementation removed, a module that compiles near calls cannot be passed
  to `compile_to_module` (strongly typed). The wrapper itself is approved as row
  B13's crate-private mechanism. Reopened by a consumer in another crate that must name
  the type, for example to store the module or to pass it as an explicit type argument.
- **A Cranelift upgrade for a contiguous JIT code arena**, as the remedy for ACT-1070. Row
  B13 makes call reach independent of placement on the selected version, and its cost is a
  constant per local call in the dev tier
  ([Principle 27](principles/27-dev-tier-optimises-only-against-blow-up.md)). No later
  version was assessed. Reopened by a second fault that follows from allocator-placed JIT
  code, or by an upgrade selected for another reason.

- **A constructor pattern that carries its resolved constructor** (2026-11-20; from
  `design`(backend), ACT-0968 item 1). `MonoMatchArm` holds `pattern: Pattern` beside
  `resolved_ctor: Option<FQSymbol>`, so a constructor pattern with no carrier is
  expressible and consumers treat it as invalid. The answer to *strongly typed* is no for
  the type as it stands. Two repairs were weighed and neither is taken now.
  - *The structural form* is a mono-view pattern type whose constructor variant holds the
    key. It changes a persisted type and the schema version, the two view builders in
    types, the backend's reader and typecheck's ownership readers.
  - *A gate at the view builder*, refusing a constructor pattern with no `pattern_ctors`
    entry as `ViewBuildError::Unresolved`, changes no item. It repeats a control that
    exists: typecheck is the sole producer, and the backend's one reader refuses a
    carrier-less arm with a located error
    (`match_codegen::a_constructor_pattern_with_no_carrier_is_a_codegen_error`, `9bb1f0aa`).
  - Residual: the refusal is raised by the reader, not at the producer's seam. Grade:
    measured at the one reader. Reopened by a second reader of an arm's constructor
    identity, which would have to repeat the refusal, or by a carrier-less arm from a
    production producer. The structural form is then the repair, taken with the next
    schema change to the mono view.

Better-typed realisations that are larger changes, `arch`, 2026-11-19 and 2026-11-20. Each
row stands as approved; none is widened.

- **B10-C2.** That a target's set lists the module holding its body is the producer's
  obligation. The structural form is a set type that only the binary's enumerator can
  build, which moves the enumeration's result type into a crate both sides see.
- **B15.** `Symbol` admits an empty string, so an empty subject stays constructible by
  hand. The structural form is a non-empty symbol type across the workspace.

- **ACT-1084.** With the variant gone, typecheck is the sole producer of `ResolutionGap`
  and the binary its sole consumer, and the binary depends on typecheck. Under
  [Principle 15](principles/15-facade-types-live-with-behavior.md) the sum could live in
  typecheck beside `CheckError`. That moves a public type between two baselines and
  changes every import of it.
- **Gap module.** A written qualifier and a resolved module share `ModuleFullPath`, so a gap
  naming an alias stays expressible and the rule is measured. The structural form is a
  distinct type for a written qualifier wherever source text carries one, which changes
  the AST in types and its readers in frontend, typecheck and the binary.
- **D13, `install_extern`.** Seven positional parameters remain, and `param_names` can
  disagree in length with the scheme's arity. The structural form is one extern spec
  value shared with the sibling `install_*` entries.

Escalated to the user, 2026-11-19:

- **A typed batch outcome for a `--link` refusal with no position**
  ([int §7.7](../int/int.md#77-one-generation-beside-an-entry-act-1083)). The delta is one
  variant of the root library's `BatchError` beside `MissingMain`, with one new arm in the
  binary's formatter. The answer to each of the three questions is yes. It is escalated because the rendering it
  serves needs a specification change: REPL §5.1 and §5.5 except only the missing-`main`
  refusal from the location requirement. The variant is approved when the user rules for
  that exception and is not built before.
