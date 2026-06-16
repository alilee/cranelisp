# cranelisp-typecheck — local conventions

The voice of the code: API gotchas, data-structure invariants, debugging hooks
for the inference engine, traits, monomorphisation, and module-locality
resolution. Owned by `/dev` when narrow-deployed to this crate.

## Bare-name resolution & the implicit-prelude OUTER SCOPE (S78 §2)

The prelude is an **outer scope**, not flattened into each module's table
(`memory/project_prelude_outer_scope.md`). Every bare-name chokepoint roots at
`state.current_module` first and, on an inner miss, retries against the
`prelude` module **iff** the module's `PreludeFallback` bit is ON.

- **`PreludeFallback`** = `DashMap<ModuleFullPath, bool>` carried on
  `TypeCheckEnv.prelude_fallback`. Absence-is-OFF (`§2.7.1`). The single gate is
  `prelude_fallback_target(current_module) -> Option<prelude_path>`: returns the
  prelude path only when the bit is ON **and** `current_module != prelude` (a
  module never falls back onto itself).
- **I-1 public-only discipline**: a private prelude binding must NOT leak as a
  bare name. Reachability is judged relative to the *original* user
  `current_module` (never in prelude's subtree), so the rule reduces to
  `is_public()` on the prelude **head** entry. Filter the prelude-hop head on
  `prelude_terminal_visible` (== `is_public()`) BEFORE chain-following.

The chokepoint family (all in `checker.rs`):
`resolve_current_or_prelude` (the `resolve`-based value/type/trait/ctor family),
`probe_current_or_prelude` (chain-follow value/scheme + entry family),
`resolve_entry_in_current_module`, `resolve_terminal_entry_or_prelude`
(trait-method/impl-discovery), plus the two **constructor** chokepoints
threaded for FIXME 0317:

- **`lookup_constructor_type_with_state`** — the pattern-ctor `exists` gate (used
  by `infer.rs::lookup_constructor_scheme`). Falls back to prelude; filters the
  prelude head on `prelude_terminal_visible` before reading the parent type.
- **`is_internal_constructor_check_with_state`** — the internal-ctor reject gate
  (used by `infer.rs` value position + `check_constructor_pattern`). After the
  current-module gate misses, it re-resolves via the already-fallback-aware
  `resolve_entry_in_current_module` and reads `internal` off the **terminal**
  `DefKind::Constructor`. **GOTCHA**: `Bind`/`Pure`/`Effect` are registered
  `Visibility::Public` in `primitives` — the I-1 public filter must NOT hide
  `Bind`. What rejects `Bind` is its `internal: true` Constructor discriminator,
  reached *through* the fallback, NOT its visibility.

Rule of thumb when adding a new bare-name path: root at `current_module`, and on
an inner miss consult `prelude_fallback_target` + the public-head filter. Never
add a name-key shortcut to primitives; primitives reach user code only *via*
prelude's `(export [primitives [*]])` re-export, chain-followed through the
fallback (the §2 structural-not-skip guarantee).

- **GOTCHA — bare punctuation operators and the `/`-split (FIXME 0328/0331).** The
  shared `cranelisp_types::resolve`/`resolve_with_fallback` primitive treats a
  `module/symbol` reference by splitting on `/` (`split_qualified`). The division
  operator `/` (and `//`) is a legitimate BARE value name (Principle 16). The split
  is guarded to require BOTH module and symbol parts non-empty, so a standalone `/`,
  `//`, leading `/bar`, or trailing `foo/` is a literal bare name — NOT qualified.
  `canonical_symbol` carries the same non-empty-remainder guard so a bare `/`'s
  `Resolved.fq.symbol` is `/`, not empty. If you ever see a trait operator whose name
  contains `/` mis-resolving as `undefined variable: /`, the `/`-split lost the guard.
  (The fix lives in `cranelisp-types::resolve`, `/arch`-owned — file a FIXME, don't
  add a checker-side literal-lookup short-circuit that re-fragments the chokepoints.)

## Cross-module monomorphisation of constrained fns (S83, FIXME 0355)

A constrained (trait-bound) fn defined in an imported module and called
cross-module is monomorphised by `pass4_monomorphise`
(`program.rs::collect_imported_constrained_calls`) → `monomorphise_call`
(`traits.rs`). The mono variant (`cmp$Int+Int`) is an ordinary concrete
`UserFn` `Def` registered in the **caller's** module with its own GOT slot; the
backend's existing concrete-mono codegen path wires it (and its trait-method
callees) — **no backend special-case**.

The mono path threads `home: Option<&ModuleFullPath>` (the DEFINING module) into
`get_constrained_fn`, `recheck_body_for_mono`, `resolve_inner_constrained_calls`,
and `verify_constraints`. Three scoping facts are load-bearing — get any one wrong
and the call mis-typechecks (the symptom is a spurious `no impl of trait T for
type X`):

1. **Body re-check switches `state.current_module` to `home`** so the body's bare
   references (`show`, `str-concat`, trait methods) resolve in the defining
   module's import context, not the caller's.
2. **Constraint verification resolves through the instantiation map, not the raw
   scheme var_ids.** `scheme.constraints` are keyed by the scheme's ORIGINAL
   quantified var_ids; only the FRESH instantiated vars are unified into
   `state.subst`. Cross-module the original var_ids are stale **and may COLLIDE**
   with a caller var (observed: `cmp`'s constraint var resolving to the caller's
   `IO` from `main`'s `Pure` → "no impl of Eq/Display for IO"). `instantiate_and_resolve`
   returns the original→fresh `var_mapping`; `verify_constraints` resolves each
   constrained var through it first. The local same-module path masked this — the
   original var_id happened to stay live in `state.subst`.
3. **Impl lookup for verification roots in `home` too.** `verify_constraints`
   runs with `current_module` switched to `home`, so `has_impl_with_state` finds a
   defining-module-local (non-prelude) trait impl. The exit-2 e2e passed via the
   prelude outer scope before this was added; a `helper`-local trait/impl exposes
   the gap (the unit test
   `program::tests::cross_module_imported_constrained_fn_monomorphises_in_defining_scope`).

## Product-ctor dual facet (S79 Option 3a, FIXME 0319)

A **single-ctor product** type (`(deftype Rectangle [:Int w :Int h])`) has
type-name == ctor-name, so type and ctor collide on one symbol-table key. The
surviving `"Rectangle"` entry is the **got-slotted ctor `Def`** (exactly like a
sum ctor) carrying a **type facet**: `DefKind::Constructor { type_def:
Some(Box<TypeDefInfo>), .. }`. A **sum/enum** type registers a separate
`ModuleEntry::TypeDef` and its ctors carry `type_def: None`. The retired
`ModuleEntry::TypeDef.constructor_scheme` smuggling field (and the six bespoke
fallback legs that keyed on it) are gone — a product ctor's scheme lives
canonically on its own `Def.scheme`, its field names on `Def.param_names`.

- **`checker::type_def_view_of(&ModuleEntry) -> Option<&TypeDefInfo>`** is the
  single "entry as a type" reader: `Some` for `TypeDef`, OR for a product ctor's
  `type_def: Some(td)`. Every site needing an entry *as a type* routes through
  it — `ModuleReadView::lookup_type_def`, `resolve_type`,
  `concrete_type_for_impl_target`, AND `resolve.rs::resolve_named` /
  `resolve_applied` (the source-annotation `TypeExpr::Named`/`Applied`
  resolvers — S79 follow-up, FIXME 0321 Root A). `resolve.rs` imports the
  accessor from `checker` and matches `IntrinsicType` first, then routes every
  other terminal entry through `type_def_view_of` so a product type used in
  TYPE position (`:Box`, `(Box Int)`) answers. Do NOT re-pattern `TypeDef`
  directly when a product type must also answer; use the accessor.
- **Product ctors do NOT auto-curry.** Because a product ctor's `Def.scheme` is
  curry-shaped (`Fn([Int,Int], Point)`), an under-applied `(Point 1)` would
  otherwise fall into `infer.rs::try_auto_curry` and silently return a closure
  instead of an arity error. The guard: at the top of `try_auto_curry`, when the
  `Expr::Var` callee resolves to a `DefKind::Constructor` Def (via
  `resolve_constructor_entry`), return a `TypeError` ("constructor X expects N
  arguments but got M") rather than currying (spec §5.2.7). Sum ctors hit the
  same guard. Over-application is still rejected by the normal arity check (the
  `arg_types.len() < params.len()` curry-precondition fails, so the unify error
  propagates).
- **`adt.rs::register_type_def_with_ctor_infos`** computes `is_product`
  (`ctors.len()==1 && ctor-name==type-name`) and either registers a separate
  `TypeDef` (sum/enum) OR attaches the facet to the lone ctor `Def` (product) —
  never both. `register_constructors` takes `product_type_def: Option<&...>` and
  the deftype docstring (product ctor falls back to it, having no `TypeDef`).
- **Ctor → parent-type** lookups (`lookup_constructor_type_in_module`,
  `resolve_constructor`) and **pattern-ctor resolution** (`infer.rs`) read the
  `Def { kind: Constructor }.type_name` arm for products too — no product
  special-case. `infer.rs::lookup_constructor_scheme` (the old product-fallback
  leg) is deleted.

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
