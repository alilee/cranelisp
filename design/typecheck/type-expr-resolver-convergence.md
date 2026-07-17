# TypeExpr resolver convergence — the four-mirror single-source refactor (FIXME 0590)

**Status:** SUBSTANTIALLY LANDED (verified S111 Phase 3, 2026-07-17) — with an S111
residual carry (below). Subordinate to `inference.md` (the `resolve::resolve_type_expr`
core) and `traits.md` (the trait/HKT sig-registration callers). Where this note and
`traits.md` disagree on the trait-sig resolution shape, this note wins for the convergence
target.

**What has landed (source-verified):** the three named mirror resolvers
`resolve_trait_type_expr` / `resolve_type_expr_hkt` / `resolve_type_expr_hkt_impl` are GONE,
replaced by the converged `checker.rs::resolve_hkt_sig_type_expr` (`:2696`) +
`resolve_hkt_impl_type_expr` (`:2722`) that route through the canonical resolver's
head-resolution environment (§2 target shape); `form.rs::check_type_expr` (`:356`) now
mints-on-miss directly, **`collect_type_var_ids` is removed** (the "immediate mechanical" leg,
§4); the **never-error `Named` fabrication arms are DELETED** (`traits/type_resolve.rs:160`;
§3 ruling). The four-mirror class is closed onto one resolver (Principle 24, type-var axis).

**S111 residual carry — 0590 R1/I2 (SPRINT.md §5): the "0349 3rd-instance safe-direction
wrong-reject".** The named-miss tightening (§3 — a genuinely-unknown `Named` now ERRORS where
mirrors 2/3 fabricated) is the correct hardening in the anti-conservative direction, but
`/review` flagged a residual in the SAFE direction: a `Named`/`TypeVar` that the pre-convergence
mirrors *resolved or fabricated-benignly* and that is a LEGITIMATELY-resolvable name must not,
post-convergence, become a **spurious wrong-reject** (the recurring 0349 safe-direction class,
3rd instance). **Binding design guard (§3 addendum):** the never-error-arm deletion tightens
ONLY genuinely-unknown names — every name that is in scope (same-module, explicit import, or
prelude fallback) MUST still resolve through the canonical resolver's `Named` leaf; the
convergence must not convert an in-scope-resolvable head into `TypeNotFound`. **This carry needs
its specific `/review` R1/I2 repro** (the exact `Named`/`TypeVar` shape that regressed) from
`/sprint`//`/review` to pin the fix and the guard test — it is a `/dev` (typecheck) correctness
item on this crate's resolver, serial on the typecheck adjacent-carries track; the design
constraint above is the acceptance criterion, the repro is the trigger.

A Principle-24 ("Resolve once") instance on the **type-var axis**: one operation
— "resolve a source `TypeExpr` to a `Type`, minting a fresh var for each free
lowercase name and co-referencing repeats" — is currently re-derived at FOUR
sites, each hand-rolling its own mint-on-miss and its own structural recursion.
The convergence collapses the four onto the ONE resolver `resolve::resolve_type_expr`.

## 1. The four mirrors and what each varies

The canonical resolver is `crate::resolve::resolve_type_expr<C>` (`resolve.rs:63`):

```
fn resolve_type_expr<C: CodeStore>(
    texpr: &TypeExpr,
    var_map: &mut HashMap<Symbol, TypeId>,
    resolve_terminal: &dyn Fn(&TypeRef) -> Option<ModuleEntry<C>>,
    mint_free_var: Option<&dyn Fn() -> TypeId>,
    span: Span,
) -> Result<Type, ResolveError>
```

It already externalises TWO head-resolution concerns as closures: **Named-leaf
resolution** (`resolve_terminal` → symbol table) and **free-var minting**
(`mint_free_var`). Its structural recursion (FnType/Applied walk, ADT arity
validation via `resolve_applied`, the `/`-guarded mint, the co-reference
`var_map` threading) is the single-source core we want the mirrors to reuse.

The four sites, and the axis on which each departs from the canonical core:

| # | Site | var_map | Named leaf | free-var mint | Self | HKT con-vars |
|---|---|---|---|---|---|---|
| 0 | `resolve::resolve_type_expr` (**canonical**) | `TypeId` | `resolve_terminal` → symbol table; **errors on miss** | `Option` (deftype=None / annotation=Some) | `SelfType` → error | — |
| 1 | `resolve_trait_type_expr` (trait method sigs) | `Type` | intrinsic-scalar OR qualified-only; **bare user type errors** | unconditional (`fresh_var`) | `SelfType` → substitute `self_type` | — |
| 2 | `resolve_type_expr_hkt` (HKT trait sigs) | `TypeId` | intrinsic OR **fabricate empty-module ADT (never errors)** | on miss | `SelfType` → error | `con_var_map`: bare → `Var`; `(f a)` → `TyConApp(id,args)` |
| 3 | `resolve_type_expr_hkt_impl` (HKT impl methods) | `TypeId` | intrinsic OR **fabricate target-module ADT (never errors)** | on miss | `SelfType` → error | `con_var_names` + `target_fqtn`: `(f a)` → target ADT |
| 4 | `form.rs::check_type_expr` (platform sigs) | `TypeId` | canonical `resolve_terminal` | **pre-walk pre-mint** (`collect_type_var_ids`) then `None` | canonical | — |

Two departures are **eliminable noise**, three are **irreducible head-resolution
policy**:

**Eliminable (fold away):**
- **var_map value type (`Type` vs `TypeId`).** Mirror 1 stores `Type`; the
  canonical stores `TypeId` and produces `Type::Var(id)`. The trait-sig
  pre-seed (`var_map.insert(param, self_type)` in `registry.rs:326`) seeds trait
  type params to `self_type`, which in the decl context IS `Type::Var(self_id)`
  — a var under the hood. The `TypeId` model expresses it (seed `param → self_id`).
- **Mirror 4's pre-walk.** `collect_type_var_ids` pre-mints every free var so the
  canonical resolver can then run with `mint_free_var: None`. A pre-walk allocator
  and a mint-on-miss allocator are two mechanisms for one concept — and if
  `collect_type_var_ids`'s walk ever diverges from `resolve_type_expr`'s
  traversal (a future `TypeExpr` variant), they disagree silently. This mirror
  is the **immediate, mechanical** collapse (§4 step A).

**Irreducible head-resolution policy (must be parameterised, not deleted):**
- **Self substitution.** Trait/impl-method sig contexts bind `Self` to a
  `Type` (a var `Type::Var(self_id)` in the decl; a **concrete** ADT
  `concrete_self` in `impl_check.rs:465`). All other contexts reject `Self`.
- **HKT constructor-variable interception.** HKT contexts carry a set of
  higher-kinded constructor-variable names whose Applied head produces a
  `TyConApp` (decl) or substitutes the impl target ADT (impl), not an ordinary
  ADT application.
- **Named-miss policy.** The canonical resolver errors on an unresolved Named;
  mirrors 2/3 silently fabricate ADTs — the FIXME-flagged latent defect (§3).

## 2. The convergence target — ONE resolver, a head-resolution environment

**The four collapse onto `resolve::resolve_type_expr`.** The structural recursion,
the `/`-guarded mint, the co-reference `var_map` threading, and the ADT arity
validation are written ONCE. What varies per call site is bundled into a single
head-resolution **context object** that generalises the two closures the resolver
already takes — it is NOT a set of pipeline "modes" (Principle 11 is not in
tension: these are the head-binding *environment*, the natural completion of the
`resolve_terminal`/`mint_free_var` externalisation the resolver already commits
to). Sketch (typecheck-internal; names illustrative, `/dev` finalises):

```
struct TypeExprCtx<'a, C: CodeStore> {
    resolve_terminal: &'a dyn Fn(&TypeRef) -> Option<ModuleEntry<C>>,
    mint_free_var:    Option<&'a dyn Fn() -> TypeId>,
    self_type:        Option<Type>,          // Some in trait/impl-sig contexts
    con_vars:         ConVars<'a>,           // HKT interception; None elsewhere
}

enum ConVars<'a> {
    None,
    Decl(&'a HashMap<Symbol, TypeId>),               // bare → Var(id); (f a) → TyConApp(id, args)
    Impl { names: &'a [Symbol], target: &'a FQTypeName }, // (f a) → target ADT
}

fn resolve_type_expr<C>(texpr, var_map, ctx: &TypeExprCtx<C>, span) -> Result<Type, ResolveError>
```

Head-arm dispatch inside the ONE resolver:

- **`SelfType`** → `ctx.self_type.clone()` when `Some`; the existing
  `TypeNotFound("Self")` error when `None`. The `None` arm is byte-behaviour
  identical to today's canonical resolver → zero regression on the
  deftype/annotation/platform paths.
- **`TypeVar(name)`** → (1) `ConVars::Decl` con-var hit → `Type::Var(con_id)`;
  (2) `var_map` hit → `Type::Var(id)`; (3) `ctx.mint_free_var` + `/`-guard →
  mint + record; (4) else `TypeNotFound`. The con-var check precedes the mint
  (an HKT con-var is never a free var).
- **`Applied(name, args)`** → (1) `ConVars::Decl` and head ∈ con-var-map →
  `TyConApp(con_id, resolved_args)`; (2) `ConVars::Impl` and head ∈ con-var-names
  → `Type::ADT(target_fqtn, resolved_args)`; (3) else the canonical
  `resolve_applied` (symbol-table resolution + arity validation). Args recurse
  through the ONE resolver.
- **`Named`** → the canonical `resolve_named` (via `resolve_terminal`), errors
  on miss. This is the §3 ruling: the fabrication arms are deleted.
- **`FnType` / `Bounds`** → unchanged from canonical.

Each of the four call sites constructs a `TypeExprCtx` and calls the ONE
resolver; the three free-function mirrors in `traits/type_resolve.rs` are
**deleted**. The wrappers `resolve_type_expr_in_module` (`ctx.self_type = None`,
`con_vars = None`, `mint = None`) and `resolve_annotation_type_expr_in_module`
(`mint = Some`) stay as the thin sugar they already are; the trait/HKT contexts
gain sibling wrappers (`resolve_trait_sig_type_expr` with
`self_type = Some(..)`, `resolve_hkt_sig_type_expr` with `con_vars = Decl(..)`,
`resolve_hkt_impl_type_expr` with `con_vars = Impl{..}`).

## 3. Ruling — the never-error `Named` fabrication arms are DELETED

Mirrors 2 and 3 fabricate `Type::ADT` with an empty (mirror 2) or target-module
(mirror 3) path for ANY unknown Named, never erroring. This is over-broad — an
unknown type name in an HKT signature is a source error, not a fact to
fabricate. Post-convergence, `Named` in every context routes through
`resolve_terminal`, resolving against the symbol table exactly as the
`defn`/`deftype`-field paths do (spec §8.5; the FIXME-0436 framing the trait-sig
qualified arm already adopted). Concrete-scalar names keep the intrinsic
fast-path inside `resolve_terminal`'s leaf (or, equivalently, a pre-check
retained for `Int`/`Bool`/`Float`/`String`).

**Behaviour change / test target (flag to `/qa` + `/dev`).** This tightens two
paths that today accept silently:
1. A **bare user type name in a trait/HKT method sig** (`(m [MyType] Self)`,
   `MyType` in scope) currently errors in mirror 1 (bare user Named → "unknown
   type") and fabricates in mirrors 2/3. Post-convergence it RESOLVES against the
   symbol table — the spec-aligned behaviour (§8.5: a bare type ref == the
   qualified ref resolved in scope). This is a *fix*, but it is a behaviour
   change: a `/qa` matrix row (bare / qualified / unknown × {trait-sig, HKT-sig,
   HKT-impl}) pins it, and the FV-13/FV-14 over-broadening guards (S109 W6
   matrix — "uppercase-unknown still errors", "trait-path unaffected") MUST stay
   green.
2. A genuinely unknown Named now **errors** where mirrors 2/3 fabricated. Any
   test/stdlib/example that leaned on the silent fabrication surfaces here — the
   blast radius must be scouted by `/dev` before the flip (grep HKT trait/impl
   sigs referencing non-intrinsic bare Named heads).

If the fabrication was load-bearing anywhere (a legitimately-forward-referenced
type inside an HKT sig checked before its `deftype` commits), that is a *staging*
question, not a reason to keep silent fabrication — resolve it with the same
cluster-staging view the canonical `resolve_terminal` already threads
(`scope_resolve_in`, FIXME 0362), not a fabricated placeholder.

## 4. Staging — the `/dev` wave

**Step A (immediate, mechanical — mirror 4).** `form.rs::check_type_expr` drops
`collect_type_var_ids` and calls `resolve_annotation_type_expr_in_module` (the
env is already in hand; the pre-walk exists only because the old resolver could
not mint). Independent of steps B/C; lands first, shrinks the file. Pin: the
platform-sig unit tests already exercising `check_type_expr` stay green; add a
row for a multi-occurrence free var co-referencing (proving the mint-on-miss
matches the old pre-walk's shared ids).

**Step B (the convergence — mirrors 1/2/3).** Introduce `TypeExprCtx` +
`ConVars`, route `resolve_type_expr`'s arms through it, add the three sig
wrappers, rewrite the four callers (`registry.rs` trait-decl + HKT-decl,
`impl_check.rs` trait-impl + HKT-impl) as thin `TypeExprCtx` constructions, and
**delete** `resolve_trait_type_expr` / `resolve_type_expr_hkt` /
`resolve_type_expr_hkt_impl` and their `traits/type_resolve/tests.rs` unit
suite (re-home the cases onto the canonical resolver's tests, now covering the
Self and con-var arms).

**Step C (rustdoc correction — do regardless of B's timing, but B lands it for
free).** The `resolve::resolve_type_expr` + `checker.rs::resolve_type_expr_in_module`
rustdoc names "trait-method sig" as a `mint_free_var: None` context whose free-var
miss "still errors" (`resolve.rs:53`, the `#[S109]` band). That was doubly wrong:
trait sigs did NOT route through this function (they routed through the deleted
mirror) AND they minted unconditionally. Post-convergence trait sigs DO route
here, with `mint_free_var: Some` — so the corrected rustdoc states: trait/HKT sig
contexts mint (Some); only the deftype-field / platform-sig contexts pass `None`
(a free-var miss there is `TypeNotFound`, §3.9.3).

## 5. The invariant that prevents a fifth mirror

`resolve::resolve_type_expr` is the **sole** `TypeExpr → Type` walk that mints and
threads a co-reference `var_map` in the crate. There is no second recursion to
hand-roll a divergent mint. A new resolution context (a future sig shape, a new
annotation position) is expressed as a **new `TypeExprCtx` construction** — it
CANNOT re-derive the mint or the structural recursion, because those live behind
the one function and the context object carries only head-binding *data*, no
recursion of its own. This is the structural enforcement (Principle 18): the
forgettable "roll your own mint" is unrepresentable once the free functions are
gone. Grep-criterion for `/review`: zero `fresh_var`/`fresh_var_id` calls inside
any `TypeExpr`-matching function other than `resolve_type_expr`'s `mint_free_var`
closure sites; zero `HashMap<Symbol, Type>`-or-`TypeId` mint-on-miss outside the
one resolver.

## 6. Cross-crate / public-API impact — none to `cranelisp-types`

`TypeExpr`, `Type` (incl. `TyConApp`), `FQTypeName`, `ModuleEntry` all already
live in `cranelisp-types`; `TypeExprCtx`/`ConVars` hold closures and borrows —
typecheck-internal, un-serdeable, correctly NOT in the types crate. **No
`cranelisp-types` edit, no `CACHE_SCHEMA_VERSION` bump.** `resolve_type_expr` is
`mod resolve` = private (`lib.rs:228`, not re-exported) — it is NOT on
typecheck's frozen `public-api.txt` (confirmed: zero hits), so the signature
change is fully internal; `/dev` regenerates the baseline only if a wrapper's
visibility changes. **The FIXME-0590 `/arch` escalation path stays open but is
NOT triggered** by this design — the convergence is typecheck-internal, matching
the S110 Phase-2 impact table ("0590 — none expected; typecheck only").

## 7. Principles

- **Principle 24 "Resolve once"** (authored S110 Phase 3) — the type-var-axis
  instance: one derivation of "resolve a TypeExpr, mint free vars, co-reference."
- **Principle 7 (single source of truth)** — one `TypeExpr → Type` walk.
- **Principle 18 (enforce invariants structurally)** — deleting the free-function
  mirrors makes a divergent mint unconstructable (§5).
- **Principle 6 (complexity has a budget)** — the `TypeExprCtx` generalises the
  two closures the resolver already carries; net line count falls (three
  free-function mirrors + their tests deleted).
- **Principle 20 (model invariants by representation)** — `ConVars`'s three-arm
  enum makes "this context has no con-vars" (`None`) vs decl-`TyConApp` vs
  impl-target-substitution explicit and exhaustive, no boolean-flag drift.
