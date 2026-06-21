# S87 — FQ Type-rendering walk consolidation (one parameterized `Type` walk in `cranelisp-types`)

> **Status.** Design (S87 Stage-B → Wave-5+ hygiene). Resolves the FQ-rendering
> proliferation finding from `audits/cranelisp-types-s87.md` Finding 1+2 and
> `design/arch/fixmes/0420-arch-fq-type-rendering-consolidation.md`.
>
> **Manifestation site (why here).** The shared walk *lives in* `cranelisp-types`,
> which is `/arch`-owned — a `/design` doc cannot author that surface, only propose
> it (the actual authoring vehicle is FIXME 0420, `target: /arch`). This doc lives
> in `design/typecheck/` because typecheck is the consumer crate whose own
> re-implementation (`format_type_fq` in `unify.rs`) is the load-bearing
> cross-crate duplication being eliminated — the design's most concrete deliverable
> is "typecheck stops re-walking `Type` and calls the types-crate walk." The
> `src/display.rs` re-pointing is a sibling `/design int` concern, cross-referenced
> here; the parameterized walk + config enum live with `Type`'s definition and
> its `Display` impl (Principle 15 — facade types live with behavior: the canonical
> renderer belongs where the type is defined, beside its `Display`).
>
> This is the **one** S87 Wave-5+ hygiene item that legitimately **changes a public
> API** (`cranelisp-types`'s surface), unlike the byte-identical internal
> decompositions. The change is gated on byte-for-byte output preservation at every
> existing call site (§4) — a rendering change would be a user-visible regression.

---

## 1. The problem (recap)

The 7-variant `Type` enum is walked by **five** copy-pasted renderers across three
crates, with **two** primitive-naming conventions and **two** type-variable-naming
conventions — and, the audit under-counted, **two** divergent `TyConApp` renderings
that do NOT line up with either of those axes:

| # | Function | Crate / location | Primitive | `Var` | `TyConApp` |
|---|---|---|---|---|---|
| 1 | `impl Display for Type::fmt` | `cranelisp-types/src/types.rs:108` | **Bare** (`Int`) | `t{id}` | `(TyCon t{id} …)` |
| 2 | `format_type_with_vars` (via `format_type_display`) | `cranelisp-types/src/types.rs:182,188` | **Bare** | lettered (`a,b,c…`) | `name` / `(name …)` |
| 3 | `format_type_fq` | `cranelisp-typecheck/src/unify.rs:141` | **FQ** (`primitives/Int`) | `t{id}` | `(TyCon t{id} …)` |
| 4 | `format_type_qualified_inner` | `src/display.rs:181` | **FQ** | lettered | `name` / `(name …)` |
| 5 | `format_type_with_inline_constraints` | `src/display.rs:239` | **FQ** | lettered | `name` / `(name …)` |

`type_var_names` (`types.rs:163`) is **live** (it supplies the lettered mapping to
#2/#4/#5; `src/display.rs:116,150` call it) and is NOT being removed.

The consolidation honours the Wave-0 /arch "keep-distinct" advisory **at the
output-convention level**: the conventions stay distinct (they become config
*values*); only the structural walk unifies (Principle 7, single source of truth).

---

## 2. The parameterized walk — signature, config, location

### 2.1 Location

`cranelisp-types/src/types.rs`, beside `Type`'s `Display` impl and
`type_var_names`. `Type` is defined here; both other crates already depend on
`cranelisp-types`, so a shared helper here is **dependency-free** for them and is
the single point all renderers reach (audit §"Why types"). Placing it elsewhere
either creates a new dependency or leaves `Display` (which MUST stay in types) as a
sixth copy.

### 2.2 Config enums

```rust
/// How primitive variants (Int/Bool/String/Float) render.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum PrimitiveNaming {
    /// Bare keyword: `Int`, `Bool`, `String`, `Float`. Debug / `Display` / internal.
    Bare,
    /// Module-qualified: `primitives/Int`, … . User-facing (repl/spec.md §5.3).
    Qualified,
}

/// How `Type::Var` / `Type::TyConApp` head ids render.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum VarNaming<'a> {
    /// Raw internal id: `t{id}`. Debug / `Display` / type-error messages.
    Numbered,
    /// User-friendly letters via a precomputed `type_var_names` map: `a`, `b`, …
    /// (`t{id}` fallback when a var id is absent from the map, e.g. >26 vars).
    Lettered(&'a HashMap<TypeId, String>),
}
```

`VarNaming` carries the var-name map by borrow on its `Lettered` arm, so the walk
needs no separate `var_names` parameter and `Numbered` callers pass nothing.

### 2.3 The walk

```rust
/// The single structural walk over `Type`, parameterized by output convention.
/// Every renderer in the workspace delegates here; `Display`, the typecheck
/// type-error renderer, and the REPL/value-display renderers differ ONLY in the
/// `PrimitiveNaming` / `VarNaming` values they pass.
pub fn render_type(ty: &Type, prim: PrimitiveNaming, vars: VarNaming<'_>) -> String
```

The constrained (`:TraitName var`) variant of #5 is **NOT** folded into
`render_type` — see §4.4. `render_type` is the *unconstrained* walk that #5 calls
recursively, with the constraint decoration layered in `src/display.rs`. This keeps
`cranelisp-types` free of REPL-display concerns (`:`-prefix, trait-name lookup) it
has no business knowing (Principle 1 — decoupling over convenience).

### 2.4 Variant-by-variant rendering (the byte-for-byte contract)

For each `Type` variant, under each axis value. **This table is the regression
contract**: the implementing change-set MUST reproduce every cell, verified against
the existing renderers.

| Variant | `PrimitiveNaming::Bare` | `PrimitiveNaming::Qualified` |
|---|---|---|
| `Int` | `Int` | `primitives/Int` |
| `Bool` | `Bool` | `primitives/Bool` |
| `String` | `String` | `primitives/String` |
| `Float` | `Float` | `primitives/Float` |

| Variant | `VarNaming::Numbered` | `VarNaming::Lettered(m)` |
|---|---|---|
| `Var(id)` | `t{id}` | `m.get(id)` or `t{id}` fallback |

| Variant | Rendering (both axes recurse with the **same** config) |
|---|---|
| `Fn(params, ret)` | `(Fn [{p0} {p1} …] {ret})` — params space-joined inside `[...]`; empty params → `(Fn [] {ret})` |
| `ADT(fqtn, [])` | `{fqtn}` (the `FQTypeName` Display — `module/name`) |
| `ADT(fqtn, args)` | `({fqtn} {a0} {a1} …)` |

`TyConApp` is the one variant whose rendering is **coupled to `VarNaming`**, not to
`PrimitiveNaming`, and the two existing renderings genuinely differ (this is the
audit's under-count):

| Variant | `VarNaming::Numbered` (the `Display`/`fq` shape) | `VarNaming::Lettered(m)` (the value-display shape) |
|---|---|---|
| `TyConApp(id, [])` | `(TyCon t{id})` | `{head}` (bare head, no parens, no `TyCon`) |
| `TyConApp(id, args)` | `(TyCon t{id} {a0} …)` | `({head} {a0} …)` |

where `{head}` = `m.get(id)` or `t{id}` fallback.

> **Load-bearing subtlety.** `Numbered` always wraps with the literal `TyCon`
> prefix even for the empty-args case (`(TyCon t{id})` — see #1 `types.rs:137` and
> #3 `unify.rs:174-178`); `Lettered` NEVER emits `TyCon` and drops the parens when
> args are empty (#2 `types.rs:219-233`, #4 `display.rs:216-230`, #5
> `display.rs:300-318`). The walk MUST branch `TyConApp` on the `VarNaming`
> discriminant, NOT just substitute the head name. This is the single place the
> "config values are orthogonal" framing breaks — flagged for /dev so the
> implementation does not naively share one `TyConApp` arm.

`Display`'s current `Var` is `t{id}` and `format_type_fq`'s `Var` is `t{id}`; both
map to `Numbered`. `format_type_with_vars`/#4/#5 map to `Lettered`. So the
`TyConApp` Numbered-vs-Lettered split is **exactly** the existing-renderer split —
no new behavior is introduced; the table just records that the split was always
two-valued.

---

## 3. Delegation plan per site

### 3.1 `cranelisp-types` (`/arch` — the authoring crate, FIXME 0420)

- **#1 `impl Display for Type`** → body becomes
  `write!(f, "{}", render_type(self, PrimitiveNaming::Bare, VarNaming::Numbered))`.
  Verified against §2.4: Bare primitives, `t{id}` vars, `(TyCon t{id} …)` — matches
  the current `Display` byte-for-byte (incl. the empty-args `(TyCon t{id})`).
- **#2 `format_type_display` + `format_type_with_vars`** → **deleted** (Finding 2;
  zero production consumers — confirmed: the only `format_type_display` hits in
  `src/repl.rs` are an unrelated `pub(crate) fn (&self, &str, &ModuleFullPath)`
  method, not the free fn). Their lettered-var capability is preserved as
  `VarNaming::Lettered`. **Keep** `type_var_names` (live; supplies the map).
- The `Display` body's TyConApp `Numbered` arm and the deleted `format_type_*`
  bodies' `Lettered` arm both fold into the single `render_type` `TyConApp` match.

### 3.2 `cranelisp-typecheck` (`/dev typecheck` — re-point)

- **#3 `format_type_fq`** (`unify.rs:141`, crate-private `fn`) → **deleted**; its
  three call sites re-point to
  `cranelisp_types::render_type(ty, PrimitiveNaming::Qualified, VarNaming::Numbered)`:
  - `unify.rs:119-120` — the type-mismatch message (`expected … found …`).
  - `unify.rs:195` — the occurs-check `infinite type:` message.
  - Verified against the Wave-0 behavior: `format_type_fq` emits FQ primitives
    (`primitives/Int`) and `t{id}` vars and `(TyCon t{id} …)` — i.e. `Qualified` +
    `Numbered` in §2.4, byte-for-byte. **The cross-crate re-implementation
    disappears**: typecheck calls a types-crate fn instead of re-walking `Type`.
- `format_type_fq`'s rustdoc (the one that *documents* the duplication as a
  deliberate keep-distinct) is removed with the function; the keep-distinct
  rationale now lives once, at `render_type` / this doc.
- **Finding 4 / no-impl message (`concrete_type_name`, `traits.rs:2202`,
  `:1156`, `:1803`)** is **out of scope for this change-set** but named here as the
  same root-cause family: those sites consume `concrete_type_name`'s *strip-to-bare*
  (a third convention) and produce a half-FQ message (`no impl of Eq for Color`
  instead of `user/Color`). Once `render_type` exists, the no-impl renderers should
  consume it with `Qualified` rather than the strip — but **do NOT change
  `concrete_type_name` itself**: its mangled-name call sites (`build_mangled_name`)
  need the bare local name. That is a follow-up (FIXME 0420 names it; `/qa` owes a
  narrow repro — two same-named ADTs in different modules, missing impl, assert the
  FQ name appears). Tracking it separately keeps THIS change-set a pure byte-for-byte
  decomposition.

### 3.3 `src/` (Binary — `/dev int` / `/design int` — re-point)

- **#4 `format_type_qualified_inner`** (`display.rs:181`) → **deleted**; its caller
  `format_type_qualified` (`display.rs:112`) and `format_scheme_type`'s
  unconstrained branch (`display.rs:155`) call
  `cranelisp_types::render_type(ty, PrimitiveNaming::Qualified, VarNaming::Lettered(&var_names))`.
  The `var_names` are already computed via `cranelisp_types::type_var_names`
  (`display.rs:116,150`) — unchanged. Verified against §2.4: FQ primitives, lettered
  vars, `({head} …)` / bare-head TyConApp — matches #4 byte-for-byte.
- **#5 `format_type_with_inline_constraints`** (`display.rs:239`) → **kept in
  `src/display.rs`, restructured to layer over `render_type`** — see §4.4. It is the
  only renderer with REPL-display-specific behavior (`:TraitName var` decoration in
  param position, spec §3.5.1) that `cranelisp-types` must not absorb.

---

## 4. Behavior-preserving invariant + risk notes for /dev

### 4.1 The whole point: byte-identical output at every call site

This is a maintainability decomposition of correct-as-shipped code (audit: "no
behavioural bug except the half-FQ no-impl message" — and that one is out of scope
here). **Every** current call site MUST produce byte-identical output. A rendering
change is a user-visible regression (type-error messages, REPL `:Type` display,
`/sig`/`/list` output all feed from these). The §2.4 table is the contract; the
implementing change-set verifies each cell.

### 4.2 Landing order (suite green per step — Principle 8, no interim half-states)

1. **types first** — add `render_type` + the two config enums; re-point `Display`
   (#1) to delegate; delete the dead `format_type_*` exports (#2). Regenerate
   `cranelisp-types/public-api.txt`. Suite green. (This step alone is a complete,
   shippable change: the new surface is added, `Display` delegates, dead exports
   retire. No consumer crate has changed yet — they still compile against the
   unchanged `Display` and the now-removed-but-unused free fns.)
2. **typecheck** — delete `format_type_fq` (#3), re-point its 3 call sites to
   `render_type(.., Qualified, Numbered)`. Suite green (the existing
   type-error unit tests in `unify.rs::tests` are the byte-for-byte guard).
3. **src/** — delete `format_type_qualified_inner` (#4), re-point; restructure #5
   over `render_type` (§4.4). Suite green (REPL display tests are the guard).

Each step is independently revertable and leaves the suite green; the dead-export
deletion in step 1 is safe precisely because it has zero consumers.

### 4.3 Risk: the `TyConApp` two-shape coupling (§2.4)

The single non-mechanical risk. A naive "substitute the head name, share one arm"
implementation would regress either `Display` (losing the `TyCon` prefix) or the
value-display path (gaining a spurious `TyCon` / parens). The arm MUST branch on
`VarNaming`. `TyConApp` is exercised only on Ring-2+ HKT paths, so its test
coverage is thinner than the first-order fragment — /dev should add a unit test in
`cranelisp-types` covering all four `TyConApp` cells of §2.4 (empty/non-empty ×
Numbered/Lettered) as part of step 1, since no integration test reliably hits the
empty-args `(TyCon t{id})` shape.

### 4.4 Risk: #5's inline constraints do NOT fold into `render_type`

`format_type_with_inline_constraints` decorates each constrained var occurrence *in
param position* as `:TraitName var` (spec §3.5.1), needs the constraint map and an
`in_params` flag, and is REPL-display-specific. Folding it into `cranelisp-types`
would drag `:`-prefix + trait-display concerns into the boundary crate (Principle 1
violation). **Resolution:** #5 stays in `src/display.rs` and calls `render_type`
for the *unconstrained* sub-renderings (the non-`Var` recursion: `Fn` structure,
`ADT`, `TyConApp`, primitives), keeping ONLY the `Var`-in-params constraint
decoration local. Concretely, #5 keeps its own recursion shape but each non-`Var`,
non-recursive leaf and each "no constraints apply here" var routes through the
shared convention. Two acceptable implementations, /dev's call:
- **(a)** #5 keeps its full recursion (it must, to thread `in_params`), but its
  *primitive/ADT/TyConApp leaves* call a small shared `render_type` for those
  variants. Minimal sharing, but the `Fn`/recursion structure stays duplicated.
- **(b)** Add an optional third config to `render_type`
  (`constraints: Option<(&HashMap<TypeId, Vec<&str>>, bool /*in_params*/)>`) so #5
  becomes a pure delegation. This pulls the `:TraitName` decoration into
  `cranelisp-types` — **rejected** on Principle 1 grounds (the boundary crate would
  own a REPL-display spec detail).

**Recommendation: (a).** The constraint-decoration walk is genuinely a different
walk (it threads `in_params` and emits a non-`Type`-structural `:Trait` token); it
is correctly REPL-local. The shared `render_type` eliminates the FOUR fully-shared
walks (#1/#2/#3/#4) and the leaf-level convention duplication in #5; the residual
`in_params` recursion in #5 is the one genuinely-distinct concern and stays where
its spec (§3.5.1) is owned. This keeps the keep-distinct advisory honoured AND the
boundary crate clean. (Net: 5 walks → 1 shared walk + 1 constraint-decoration walk
that delegates its leaves, vs. the current 5 fully-independent walks.)

---

## 5. public-api.txt delta — `cranelisp-types`

Per the baseline-diff discipline (`design/arch/CLAUDE.md` §"Baseline-diff
discipline"): `/dev` regenerates `crates/cranelisp-types/public-api.txt` in the same
change-set via
`cargo public-api --omit blanket-impls,auto-derived-impls -p cranelisp-types > crates/cranelisp-types/public-api.txt`,
and this design names each delta. The facade for this crate is **retired** (types
facade retired S69 → BC §7 + source rustdoc), so the canonical surface record is the
per-item `///` rustdoc on `render_type` + the config enums; `/arch` confirms the
delta at review.

**Removed (2 lines):**

```
- pub fn cranelisp_types::format_type_display(&cranelisp_types::Type) -> alloc::string::String              # public-api.txt:1526
- pub fn cranelisp_types::format_type_with_vars(&cranelisp_types::Type, &std::collections::hash::map::HashMap<cranelisp_types::TypeId, alloc::string::String>) -> alloc::string::String   # public-api.txt:1527
```

…and the corresponding names drop from the `lib.rs:228` re-export
(`pub use types::{… format_type_display, format_type_with_vars, …}` — both removed;
`type_var_names`, `Scheme`, `Subst`, `Type`, `TypeId`, `apply`, `free_vars`,
`max_type_var_id` all **kept**).

**Added:**

```
+ pub fn cranelisp_types::render_type(&cranelisp_types::Type, cranelisp_types::PrimitiveNaming, cranelisp_types::VarNaming<'_>) -> alloc::string::String
+ pub enum cranelisp_types::PrimitiveNaming
+ pub cranelisp_types::PrimitiveNaming::Bare
+ pub cranelisp_types::PrimitiveNaming::Qualified
+ pub enum cranelisp_types::VarNaming<'a>
+ pub cranelisp_types::VarNaming::Numbered
+ pub cranelisp_types::VarNaming::Lettered(&'a std::collections::hash::map::HashMap<cranelisp_types::TypeId, alloc::string::String>)
```

(Exact rendered lines — incl. auto-derived `impl Copy/Clone/Debug/PartialEq/Eq`
rows and the `#[non_exhaustive]` markers — are whatever `cargo public-api`
emits with the canonical `--omit blanket-impls,auto-derived-impls` flags; the
above is the semantic set `/arch` reviews. `lib.rs:228`'s `pub use` adds
`render_type, PrimitiveNaming, VarNaming`.)

**Net:** −2 dead free fns, +1 free fn, +2 enums. This is the one S87 hygiene item
that changes a public API; the change is a strict surface improvement (a dead pair
retires, a single shared renderer + its config types are introduced).

---

## 6. Quality-attribute stewardship (this change)

| Attribute | Disposition |
|---|---|
| Simplicity (P6) | 5 walks → 1 shared walk + 1 constraint-decoration walk. Net complexity down. |
| Maintainability | A new `Type` variant or an `Fn`/`ADT` rendering change now edits ONE walk, not 5 across 3 crates. The two-convention "fixed one, others wrong" drift class (S86 campaign) is structurally eliminated for the four fully-shared walks. |
| Single source of truth (P7) | The headline. The structural walk is single-sourced; conventions are values, not copies. |
| Decoupling (P1) | typecheck stops reaching past the crate boundary to re-implement a `Type` walk; the `:TraitName` REPL-display concern stays out of `cranelisp-types` (§4.4). |
| Testability (P5) | `render_type` is a pure `(Type, config) → String` fn — directly unit-testable in `cranelisp-types` against the §2.4 contract table (the four `TyConApp` cells especially). |
| Observability | Unchanged — outputs are byte-identical; existing type-error / REPL-display tests remain the guards. |

Untouched: concurrency (no shared state), performance (rendering is not hot; allocation profile unchanged — same `String` building). RC-symmetry N/A (this crate holds no RC sites).

---

## 7. Cross-references

- `design/arch/fixmes/0420-arch-fq-type-rendering-consolidation.md` — the `/arch`
  authoring vehicle (the walk + config enums in `cranelisp-types` are `/arch`'s to
  author; this doc is the consumer-side design + the byte-for-byte contract).
- `audits/cranelisp-types-s87.md` Finding 1 (the five-walk headline), Finding 2
  (the dead `format_type_*` exports), Finding 4 (`concrete_type_name` strip — the
  out-of-scope sixth site).
- `repl/spec.md` §5.3 (FQ primitive naming in user-facing display), §3.5.1
  (`:TraitName var` inline-constraint notation — the #5-local concern).
- `design/arch/CLAUDE.md` §"Baseline-diff discipline" (the public-api.txt + facade
  two-update obligation; for this retired-facade crate the rustdoc is the surface
  record).
- Principle 7 (single source of truth), Principle 1 (decoupling over convenience),
  Principle 15 (facade types live with behavior — the renderer beside `Type`),
  Principle 8 (no interim implementations — the §4.2 suite-green-per-step landing).

## 8. Next skills

- `/arch` — authors `render_type` + `PrimitiveNaming`/`VarNaming` in
  `cranelisp-types`, re-points `Display` (#1), deletes the dead `format_type_*`
  exports (#2), regenerates `public-api.txt` (resolves FIXME 0420's types-side half).
- `/dev typecheck` — deletes `format_type_fq` (#3), re-points its 3 `unify.rs` call
  sites; lands the §2.4 byte-for-byte guard if not already covered.
- `/dev int` (`/design int` for the doc) — re-points `display.rs` #4, restructures
  #5 per §4.4(a).
- `/qa` — the no-impl FQ-message repro (Finding 4 follow-up) once `render_type`
  exists: two same-named ADTs in different modules, missing impl, assert the FQ
  name appears in the message.
