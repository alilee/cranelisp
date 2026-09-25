# cranelisp-typecheck — local conventions

Entry guidance for `dev` narrow-deployed to this crate: constraints a locally
reasonable edit would break, and where their canonical account lives. The
crate design is [`design/typecheck/typecheck.md`](../../design/typecheck/typecheck.md)
(document map §10); the public contract is the crate-root rustdoc in
`src/lib.rs`.

## Written type variables

Required behaviour: `spec/03-types.md` §3.3.1–§3.3.5. Canonical design:
[`inference.md`](../../design/typecheck/inference.md) §"Written type
variables".

- A **bare** written var (`:a`) is a flexible inference variable with a display
  name. `written_var_scope` threads only lexical co-reference; nested `fn`
  closures share the enclosing frame. Do not add rigidity to the bare path.
- `BodyFrame.rigid_vars` holds only parameter vars that already carry an
  asserted constraint (`:C x`) at Pass-2 entry. A bare param that accrues a
  constraint from body use stays flexible.
- `unify::unify_with_rigid` is the one unification seam (the free `unify` is
  `#[cfg(test)]`). A rigid var must not bind to a concrete type; two rigid vars
  merge.
- A value annotation naming a trait (`:Num2 5`) is a satisfaction check only:
  it neither unifies nor disambiguates return-type dispatch. A concrete
  non-nominal type (`Fn`) implements nothing and is rejected.
- There is no eager "polymorphic value escapes" check; rank-1 polymorphic
  returns are legitimate. Multi-type use and rank-2 fail in unification;
  a result-only var is caught by the §3.11 ambiguity gate.
- `resolve::resolve_type_expr` is the sole `TypeExpr -> Type` walk, driven by
  `TypeExprCtx`. Extend the context; do not add a local mint-on-miss resolver.
  A `/`-qualified name never mints a type var.

## Codegen views

Canonical: `program/support.rs::build_concrete_codegen_view` rustdoc and
[`non-concrete-producer-obligations.md`](../../design/typecheck/non-concrete-producer-obligations.md).

- Concrete source bodies get their view through that one helper; only a
  `Life::Concrete` callable gets one. Synthesised constructor and accessor
  bodies build theirs at the synthesis site; templates carry none.
- The helper returns `Result<Option<MonoDefnVariant>, _>` and its two
  `ViewBuildError` arms differ deliberately. `NotConcrete` gets bounded
  defaulting then a located ambiguity error. `Unresolved` (a real-span
  `Var`/`Apply` with no recorded verdict) **propagates**. Never `.ok()` it:
  swallowing it ships an unresolved body to the backend, where it resurfaces
  as an unlocated codegen error.

## `callees` completeness

Canonical: [`checked-body-publication.md`](../../design/typecheck/checked-body-publication.md)
and `design/int/session-transaction.md` §3.2.

- A checked body's `callees` names every statically resolved user-function
  reference, call and value position alike. It is harvested by the one
  `crates/cranelisp-typecheck/src/program/callees.rs::harvest_callees` projection from the resolution delta
  plus `BodyFrame.user_fn_refs`.
- A new body-check seam uses the shared `BodyFrame` wrapper and routes through
  `harvest_callees` before publication. Do not publish a body and mutate its
  callees afterward; missing edges silently starve the session transaction's
  affected-set closure.
- Self-edges, non-`UserFn` kinds, dotted member references and mono-instance
  rechecks record no edge.
- Changing what `callees` records changes `.meta.json` meaning: bump
  `CACHE_SCHEMA_VERSION` in the same change-set.

## Name resolution

Canonical: spec §8.6; [`use-site-candidate-selection.md`](../../design/typecheck/use-site-candidate-selection.md);
`design/arch/symbol-table-lifecycle.md` §3, §5.8–§5.9.

- The prelude is an implicit `(import [prelude [*]])`. Its fallback is a
  resolution mechanism, not an outer scope. It is decided once per module
  (`PreludeFallback`) and applied inside `cranelisp_types::ResolutionScope`.
- Route every bare-name reference through `scope_resolve` / `scope_resolve_in`
  (one terminal, rejecting a multi-candidate spelling) or
  `scope_resolve_candidates` (the full candidate set, for selection). Do not
  re-thread `prelude_fallback_target` at a new call site or add a name-key
  shortcut to primitives.
- A local definition, import, export, prelude binding or derived member may
  share a spelling with distinct canonical identities; the spelling then
  denotes a candidate set resolved at each use (spec §8.6.4–§8.6.5). Nothing
  is rejected, shadowed or chosen by declaration order at registration.
- The raw current-module `probe_module_entry_owned` answers same-module
  identity (idempotent re-registration, REPL redefinition), never scope.
- An internal constructor (`IO`'s `Bind`) is rejected by its `internal: true`
  flag on `CallableOrigin::Ctor`, read through the fallback — not by
  visibility. It is Public, so the public-only filter must not hide it.
- A bare `/` or `//` is a value name, not a qualified reference. The
  non-empty-parts guard lives in `cranelisp-types`; file against `arch`
  rather than short-circuiting it here.

## Members: accessors and constructors

Canonical: [`fixme-0365-field-accessor-dotted.md`](../../design/typecheck/fixme-0365-field-accessor-dotted.md)
(accessors), [`dotted-ctor-registration.md`](../../design/typecheck/dotted-ctor-registration.md)
and `design/arch/dotted-ctor-canonical-keys.md` (constructors).

- Each product field and each sum constructor has exactly one binding, keyed
  `Type.member` in the type's home module. The bare spelling is a
  `NameCandidate` onto it, not a second binding. No sentinel, alias or
  poisoned entry exists.
- A product constructor keeps its type-name key and carries the type facet
  on `CallableOrigin::Ctor { type_def: Some(..) }`. Read an entry as a type
  only through `checker::type_def_view_of`. Constructors do not auto-curry.
- `checker.rs::resolve_dotted_member_entry` is the one member resolver for
  value and pattern positions; `adt::committed_member_owner` is the one
  owner recogniser.
- A constructor-key change reaches every crate's raw key probe, not just this
  one; audit readers workspace-wide (`dotted-ctor-canonical-keys.md` §3).
- **Known divergences:**
  - `traits/impl_check.rs::check_impl_method_accessor_collisions` still
    rejects an impl method named like a field accessor, which
    `spec/07-traits.md` §7.3.1 permits. It and its tests stay until `qa`
    intake under [`ACT-0983`](../../sprints/actions/ACT-0983-accessor-impl-collision-intake.md).
  - Pattern-position selection in `infer.rs::check_constructor_pattern` is not
    yet the approved lifecycle (`dotted-ctor-registration.md`
    §"Unresolved obligations").

## Cross-module monomorphisation

Canonical: [`monomorphisation.md`](../../design/typecheck/monomorphisation.md) §3.7.

A constrained function called from another module is monomorphised into the
caller's module as an ordinary concrete binding. Get any of these wrong and
the symptom is a spurious `no impl of trait T for type X`:

1. The body recheck switches `state.current_module` to the defining module.
2. Constraint verification maps through the instantiation's original→fresh
   var mapping, never raw scheme var ids.
3. Impl lookup roots at the trait's home (`traits/dispatch.rs::has_impl_in_home`).
   `has_impl_with_state` is test-only; it re-resolves the bare trait name in
   the caller's scope.

## Ownership inference seams

Canonical: [`ownership-inference.md`](../../design/typecheck/ownership-inference.md).

- `ownership/transfer.rs::join_origin` is commutative: the parameter reach is a
  sorted set of parameter indices and the join is union. Do not reintroduce a
  representative parameter; it made memory-safety verdicts depend on `if` arm
  order.
- Reach is resolved at the mint, never re-derived from a binding name;
  macro-generated `(let [a a] …)` shadowing makes names unreliable.
  `bind_pattern`'s `shadow` flag gates only the symbol-keyed provenance fact,
  never the reach.
- When touching a join, merge or fold seam, extend the algebraic property
  cells (`src/ownership/transfer/tests.rs`, `join_lattice_*`), not only
  example cells.
- `mono_collect.rs::resolve_auto_curry` takes a required `AutoCurryDrain`.
  `Final` is the dangerous polarity; never give a new seam a default. Its seam
  census is in the function's rustdoc.

## Testing

- Unit tests live in-crate, driven by `TestFixture` (`checker/test_support.rs`).
  `TestFixture::new()` seeds a synthetic world from `cranelisp-types` only (no
  `cranelisp-primitives`). Seed the prelude-fallback bit directly
  (`tf.prelude_fallback.insert(module, true)`).
- Registering a type with typed fields in a bare module needs the field types
  in scope there; prefer nullary constructors for prelude-resident test ADTs.
- Each `program/` production submodule has a sibling test file
  (`program/<unit>/tests.rs`); put a test in the home of the unit it
  exercises. Shared fixtures and the common type re-exports live once in
  `program/test_support.rs`, so a test file needs only:

  ```rust
  use super::*;
  use crate::program::test_support::*;
  ```
