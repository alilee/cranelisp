# cranelisp-typecheck — local conventions

The voice of the code: API gotchas, data-structure invariants, debugging hooks
for the inference engine, traits, monomorphisation, and module-locality
resolution. Owned by `/dev` when narrow-deployed to this crate.

## Rigid written type variables (spec §3.3 [S109], S109 W6.2)

A **written free lowercase type variable** (`:a`, or one nested in `:(Box a)`)
is a RIGID skolem — a *fixed-but-unknown* type within its definition body. The
body may not choose what it is (assert-not-acquire); it is quantified at the
definition boundary and instantiated at the call site. Three coupled pieces
realize this; break any one and the model silently reverts to the flexible
"acquire" bug (F1/0588):

1. **`unify::unify_with_rigid(subst, rigid, t1, t2)` + `unify_var`** are the ONE
   unification seam (the free 3-arg `unify` is a test-only helper). The `rigid`
   set is `CheckState::rigid_vars`. Asymmetry (MUST-4): a flexible var MAY bind
   to a rigid one (param acquisition); a rigid var MUST NOT unify with a
   concrete type nor a *distinct* rigid var (skolem-escape). `self.unify` always
   threads `state.rigid_vars`. **Do not add a unify path that ignores the rigid
   set** — a symmetric-in-flexibility unify is the defect.

2. **`rigid_vars` is scoped to the OWNING body, never global.** `check_defn_body`
   seeds it from the definition's Pass-1 written-var scope and tears it down on
   return. This is load-bearing: outside its own body a written var must behave
   as an ordinary *quantifiable* var (MUST-1) so a forward-referencing sibling
   instantiates it flexibly. A global rigid set would skolem-escape every
   forward call.

3. **`written_var_scope` threads the name→rigid-`TypeId` map** from Pass-1
   (`register_defn_signature`, returned via `accumulator.defn_var_scopes`)
   through Pass-2 body checking and INTO nested `fn` closures (`infer_lambda`
   SHARES it, never resets — SCOPE-5 co-reference). `infer_annotate` extends
   `rigid_vars` for body/value annotations (rigid); `infer_lambda` does NOT (a
   lambda's own fresh param vars are flexible — a lambda is not a rank-1
   generalization boundary; only names co-referring to an already-rigid
   enclosing var stay rigid — FV-15 vs FV-20).

**`suppress_rigid_annotations`** turns rigidity OFF while re-checking a body
against ALREADY-CONCRETE types (`check_defn_body_with_types` — mono instances +
trait-impl methods): the caller has chosen the types (MUST-1), so re-minting a
rigid var and pinning it to the instance's concrete type would be a spurious
skolem-escape. This flag is why a body annotation (`(defn id [:a x] :a x)`) did
not break monomorphisation.

**Minting stays in `resolve::resolve_type_expr`** (rigidity is applied by the
caller, not the resolver). A `/`-qualified name never mints (F2/0589 — a type
var is a BARE lowercase identifier). The frontend still mis-tags `:user/int` as
a `TypeVar` carrying the qualified string; the in-crate `!contains('/')` guard
is the backstop — the frontend routing half is a separate `/dev`-on-frontend
item. FIXME 0590 records four MIRROR resolvers (`traits/type_resolve.rs` ×3 +
`form.rs`) that hand-roll their own mint-on-miss; the S110 convergence folds
them onto this canonical resolver.

## Concrete-boundary `codegen_view` population (S84 Phase-3, FIXME 0392)

Every codegen-bound `ModuleEntry::Def` carries a `codegen_view:
Option<MonoDefnVariant>` — the concrete-boundary `MonoExpr` body view the backend
will consume (`design/arch/concrete-boundary-type.md` §3.0). It is populated at
the symbol-table registration sites, NOT a side `Vec` (the transitional
`CheckState.mono_variants` was retired — the entry is the single source of truth,
Principle 7):

- **Mono instances** — built at the `monomorphise_call` seam (`traits.rs:~1508`,
  `MonoExpr::from_expr` over the subst-resolved instance body) and set via
  `builder.codegen_view(..)` at `register_mono_entry`. **Hard-errors** on a
  non-concrete body (a minted mono instance MUST be concrete post-Phase-4-A) —
  the §3.11.1 ambiguity message.
- **Ordinary concrete defns** — single-sig (`program.rs` `check_form_body_single_defn`,
  next to the `ast` writeback), multi-sig mangled variants (`register_mangled_variants`),
  trait-impl methods (`traits.rs::check_impl_method`), test-fn mono roots
  (`register_test_fn_mono_roots`). All route through the shared
  `program::build_concrete_codegen_view(name, variant)` helper. It is
  **best-effort**: `Some` on `from_expr` success (the universal real-program
  case), `None` on failure. Only a `UserFnState::Concrete` entry gets a view —
  guard on the kind before calling the helper.

**Why best-effort (NOT hard-error) for concrete defns.** `defined_symbols()` also
yields `DefKind::Constructor` (ctor + accessor) entries whose synthetic bodies are
`inferred_type: None` (`adt.rs`), and `f$Var` multi-sig variants whose param is a
genuine `Type::Var` — neither converts via `from_expr`, yet the current `ast`-path
codegen compiles them fine (ctor codegen reads field types from the signature, not
node `inferred_type`). Hard-erroring would reject valid programs. The
`None`-vs-hard-error asymmetry + the ctor/accessor gap is recorded in **FIXME 0393**
(the Phase-3/0391 backend backstop must scope its `expect` to `Concrete` entries,
not the whole `defined_symbols()` set). The `--workspace` e2e suite produced ZERO
`from_expr`-fail on a real concrete defn — the validation payoff holds.

## `Def.callees` completeness contract (S101, FIXME 0470 + 0472)

A checked entry's `callees` names **every statically-resolved user-fn
reference** in its body — call-position AND value-position (HOF arg, returned,
stored, curried, nested-lambda), same-module and imported alike — recorded
uniformly as `Vec<FQSymbol>` (value vs call edges indistinguishable to
consumers; `design/int/session-transaction.md` §3.2). The feed is two-channel:

- `ResolvedCall`-derived edges (`extract_call_graph_edges` — trait methods,
  sig-dispatch, auto-curry), unchanged;
- `CheckState.user_fn_refs` — recorded at the `infer_var` chokepoint by
  `checker::record_user_fn_ref` for every successfully-typed `Var` whose name
  is NOT locally shadowed and resolves (chain-follow to home,
  prelude-fallback-aware, `lookup`-mirroring qualified candidate order) to a
  `DefKind::UserFn` `Def`.

Both channels are combined by the ONE shared **`harvest_callee_edges`** helper
(the `codegen_view` all-seams precedent — FIXME 0472) at every body-check
seam:

- **Pass-2 per-form** — `check_form_body_single_defn` / `_multi_sig`
  (span-set snapshot deltas like `form_mr`; edges ride
  `FormCheckResult.call_graph_edges` into the merge/finalize sinks, attributed
  to the enclosing defn — nested-lambda refs included, the L-R2 carrier);
- **Pass-1 impl-method writeback** — `finalize_impl_method_writeback`
  (impl-provided, default, AND HKT trait-method bodies; these are checked
  outside every per-form delta, so the edges are written DIRECTLY to the
  mangled entry, mirroring its `ast`/`codegen_view` direct writes; default
  bodies harvest under the D1 trait-home module switch, so their edge FQs
  resolve in the defining module's context).

When adding a NEW body-check seam, snapshot `state.user_fn_refs` before the
body check and route the delta through `harvest_callee_edges` — a seam that
skips the harvest silently starves the S101 transaction's reverse index (the
0472 defect class).

Dispositions: **self-edges are skipped** (the recursion name is a local
binding in `check_defn_body`, so the shadow gate filters it); non-`UserFn`
kinds (primitives, constructors, macros, overloaded bases) record no edge —
their redefinition falls back to module grain (session-transaction §10 T1);
dotted `Type.member` accessor references are un-recorded residue (T1 covers
deftype redefinition); **mono-instance bodies (`recheck_body_for_mono`) are a
deliberate exclusion** — the constrained TEMPLATE's entry carries the complete
edge set from its own defn-form check, the call-site recorder gives the
caller→template edge, and mono instances are re-minted whenever their minting
caller re-typechecks, so the reverse closure is preserved through the template
chain. Consumers: `save.rs::dependency_sort` (emission order; filters
self-edges, Kahn's + alphabetical cycle fallback) and the S101 R3
transaction's reverse index — **silently dropping edges starves its
affected-set closure**. Changing what `callees` records is a `.meta.json`
meaning change: bump `CACHE_SCHEMA_VERSION` in the same change-set (the 0472
seam cure landed inside the S101 v10→v11 window — no re-bump). Guarded by
`program::tests::callees_*` (`tests/plan/s101-coverage-postmortem.md` §2.1).

## Bare-name resolution & the prelude fallback (S108 Wave-G convergence)

The prelude is **just an implicit `(import [prelude [*]])`** — a
prelude-provided name is in a module's scope on identical terms to an explicit
import (spec §8.6.1–§8.6.5, §8.8.1). Whether the implementation materialises
prelude bindings into each table or consults the prelude on an inner miss is a
**resolution-mechanism detail with ZERO semantic weight — there is no "outer
scope" as a language concept**. Design/rustdoc/CLAUDE.md under this ruling say
"the prelude **fallback**" (a mechanism), never "the outer scope" as a scoping
level with its own rules.

**Exactly two semantic operations exist, and BOTH consult the prelude:**

1. **resolve-a-reference** — `cranelisp_types::ResolutionScope::resolve`. The
   fallback is **intrinsic to the scope**, decided ONCE at scope construction
   (from the `PreludeFallback` role bit), never at a call site. There is no
   public fallback-less resolution entry point and no per-call fallback flag
   (Principles 18/20 — the forgettable decision is unrepresentable). Typecheck
   constructs the scope at the ONE seam `TypeCheckEnv::scope_resolve` (current
   module) / `scope_resolve_in` (arbitrary root); every bare-name resolution
   routes through it. The I-1 public-only filter (a private prelude binding must
   NOT leak / shadow) and the qualified-name-never-retries guard are intrinsic
   to `ResolutionScope::resolve`.
2. **may-this-name-be-defined** — the §8.6.4 seam
   `cranelisp_types::reject_def_over_binding(scope, name, span)`, derived from
   the SAME resolve walk (typecheck's `reject_def_over_binding` is a 3-line
   adapter constructing the scope). A binding **consults the prelude to REJECT**:
   a definition over ANY name in scope — explicit import, export, or
   prelude-provided — is a §8.6.4 compile-time conflict, **never a shadow**
   (`home == current_module` ⇒ the module's own prior def ⇒ redefinition
   allowed; otherwise reject). This is the correction of the former
   spec-inverted rule of thumb ("pick the non-fallback variant to decide whether
   a name is *free*", "a user `(deftrait Display …)` may legitimately SHADOW a
   prelude-globbed one") — a name is NOT free merely because the prelude
   provides it (§8.6.4); that rule of thumb produced the S14 deftrait
   silent-accept. Every definition form routes through this ONE seam:
   `defn`/`deftype` at the `program.rs` `check_form_register` arms, `deftrait`
   (trait name + each method name) at the `TraitDecl` arm, `defmacro` in int.

**The ONE legitimate fallback-less probe** is the *idempotent re-registration
check* — "does THIS module already carry this exact declaration?" (retry-from-top
re-submission, S86 D3; REPL own-redefinition). That is a raw current-module
`probe_module_entry_owned` probe, named as a probe: it answers same-module
IDENTITY, **not** name-freedom, and must never be reachable under a name that
reads like reference resolution. `registry::register_trait_decl`'s duplicate
check is exactly this probe (the §8.6.4 name-freedom question already ran at the
`TraitDecl` arm seam before it).

- **`PreludeFallback`** = `DashMap<ModuleFullPath, bool>` on
  `TypeCheckEnv.prelude_fallback` (absence-is-OFF, §2.7.1), read ONLY at the two
  scope constructors via `prelude_fallback_target(current_module) ->
  Option<prelude_path>` (ON **and** `current_module != prelude`), plus the bulk
  trait-method-declaring scan `find_trait_method_decl` (an enumeration reader,
  not the resolve walk). The former per-site prelude-fallback resolver family
  (the six bare-name chokepoints of the S78 census) is retired — collapsed onto
  the single scope resolve.
- **`is_internal_constructor_check_with_state`** — the internal-ctor reject gate
  (used by `infer.rs` value position + `check_constructor_pattern`). After the
  current-module gate misses, it re-resolves via the fallback-aware
  `resolve_entry_in_current_module` (now a projection over `scope_resolve`) and
  reads `internal` off the **terminal** `DefKind::Constructor`. **GOTCHA**:
  `Bind`/`Pure`/`Effect` are registered `Visibility::Public` in `primitives` —
  the I-1 public filter must NOT hide `Bind`. What rejects `Bind` is its
  `internal: true` Constructor discriminator, reached *through* the fallback,
  NOT its visibility.

Rule of thumb when adding a new bare-name path: route it through
`scope_resolve` / `scope_resolve_in` (reference) or `reject_def_over_binding`
(definition) — never re-thread `prelude_fallback_target` at a new call site, and
never add a name-key shortcut to primitives (primitives reach user code only
*via* prelude's `(export [primitives [*]])` re-export, chain-followed through the
fallback — the structural-not-skip guarantee).

- **GOTCHA — bare punctuation operators and the `/`-split (FIXME 0328/0331).** The
  shared `cranelisp_types::ResolutionScope::resolve` primitive (the sole public
  resolution entry point since S108 Wave-G — the free `resolve`/`resolve_with_fallback`
  are now private internals) treats a `module/symbol` reference by splitting on `/`
  (`split_qualified`). The division
  operator `/` (and `//`) is a legitimate BARE value name (Principle 16). The split
  is guarded to require BOTH module and symbol parts non-empty, so a standalone `/`,
  `//`, leading `/bar`, or trailing `foo/` is a literal bare name — NOT qualified.
  `canonical_symbol` carries the same non-empty-remainder guard so a bare `/`'s
  `Resolved.fq.symbol` is `/`, not empty. If you ever see a trait operator whose name
  contains `/` mis-resolving as `undefined variable: /`, the `/`-split lost the guard.
  (The fix lives in `cranelisp-types::resolve`, `/arch`-owned — file a FIXME, don't
  add a checker-side literal-lookup short-circuit that re-fragments the chokepoints.)

## Cross-module monomorphisation of constrained fns

A constrained (trait-bound) fn defined in an imported module and called
cross-module is monomorphised by `pass4_monomorphise`
(`program.rs::collect_imported_constrained_calls`) → `monomorphise_call`
(`traits.rs`). The mono variant (`cmp$Int+Int`) is an ordinary concrete
`UserFn` `Def` registered in the **caller's** module with its own GOT slot — the
backend's existing concrete-mono codegen path wires it; **no backend special-case**.

The mono path threads `home: Option<&ModuleFullPath>` (the DEFINING module) into
`get_constrained_fn`, `recheck_body_for_mono`, `resolve_inner_constrained_calls`,
and `verify_constraints`. Three scoping facts are load-bearing — get any one wrong
and the call mis-typechecks (symptom: a spurious `no impl of trait T for type X`):

1. **Body re-check switches `state.current_module` to `home`** so the body's bare
   references resolve in the defining module's import context, not the caller's.
2. **Constraint verification resolves through the instantiation map**
   (`instantiate_and_resolve`'s original→fresh `var_mapping`), **not the raw
   scheme var_ids** — cross-module the original var_ids are stale and may COLLIDE
   with a caller var.
3. **Impl lookup for verification roots in `home` too** (`has_impl_with_state`
   runs under the `home` switch, finding a defining-module-local trait impl).

The full rationale, the var-collision walkthrough, and the sketch/backend
comparison now live in **`design/typecheck/monomorphisation.md` §3.7
"Cross-module body-recheck scoping"**. Guarded by
`program::tests::cross_module_imported_constrained_fn_monomorphises_in_defining_scope`.

## Product-ctor dual facet

A **single-ctor product** type (`(deftype Rectangle [:Int w :Int h])`) has
type-name == ctor-name, so type and ctor collide on one symbol-table key. The
surviving entry is the **got-slotted ctor `Def`** (like a sum ctor) carrying a
**type facet**: `DefKind::Constructor { type_def: Some(Box<TypeDefInfo>), .. }`;
a **sum/enum** registers a separate `ModuleEntry::TypeDef` with `type_def: None`
ctors. The product ctor's scheme lives on its own `Def.scheme`, its field names
on `Def.param_names`. Full design in **`design/typecheck/adt.md` §"Product Type
Handling"**.

Code-site invariants:

- **`checker::type_def_view_of(&ModuleEntry) -> Option<&TypeDefInfo>`** is the
  single "entry as a type" reader (`Some` for `TypeDef` OR a product ctor's
  `type_def: Some(td)`). Every site needing an entry *as a type* routes through
  it — `ModuleReadView::lookup_type_def`, `resolve_type`,
  `concrete_type_for_impl_target`, AND `resolve.rs::resolve_named`/`resolve_applied`
  (the source-annotation `TypeExpr::Named`/`Applied` resolvers). Do NOT re-pattern
  `TypeDef` directly when a product type must also answer; use the accessor.
- **Product ctors do NOT auto-curry.** `infer.rs::try_auto_curry` guards at its
  top: when the `Expr::Var` callee resolves to a `DefKind::Constructor` Def (via
  `resolve_constructor_entry`), it returns an arity `TypeError` rather than
  currying (spec §5.2.7). Sum ctors hit the same guard; over-application is
  rejected by the normal arity check.
- **`adt.rs::register_type_def_with_ctor_infos`** computes `is_product`
  (`ctors.len()==1 && ctor-name==type-name`) and registers either a separate
  `TypeDef` (sum/enum) OR the facet on the lone ctor `Def` (product) — never
  both. `register_constructors` takes `product_type_def: Option<&...>` and the
  deftype docstring (product ctor falls back to it, having no `TypeDef`).
- **Ctor → parent-type** lookups and **pattern-ctor resolution** (`infer.rs`)
  read the `Def { kind: Constructor }.type_name` arm for products too — no
  product special-case.

## Module-locality (Principle 17)

Short-name lookup is current-module-only, with per-symbol chain-follow on
`Import`/`Reexport` entries (`source.module` references). No closure walk, no
universe scan. `resolve_terminal_entry_and_home` / `chain_follow_to_home` are
the navigation primitives; staging-aware via `probe_module_entry_owned`
(FIXME 0179 — staging shadows live when `module_path == staging.module`).

## Testing

Unit tests live in-crate (`#[cfg(test)]`), driven by `TestFixture`
(`checker/test_support.rs`). `TestFixture::new()` seeds the full synthetic world
(`FixtureBuilder::full()` — special forms, builtin type names, macros Sexp/SList,
the `IO` ADT with `Pure`/`Effect`/`Bind`-internal, Ring 0/1/3 primitives) built
on `cranelisp-types` only (no `cranelisp-primitives` dep). Seed the
`prelude_fallback` bit directly (`tf.prelude_fallback.insert(module, true)`) to
exercise the outer-scope fallback. Registering a type def with typed fields in a
bare module needs the field types reachable there — use **nullary** ctors in
prelude-resident test ADTs to avoid an `Int`-not-in-scope setup failure.
