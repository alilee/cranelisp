# Dotted `Type.Ctor` constructor capability — canonical-key registration + one member resolver

**Sprint 109 bucket 2 design (S109 Phase 3, `/design` typecheck).** Subordinate
to `design/typecheck/adt.md` (constructor registration + the product dual-facet)
and the exact sibling of `design/typecheck/fixme-0365-field-accessor-dotted.md`
(the *field-accessor* inverted-model). This doc designs the **constructor** half
of the same inverted member model: same-named constructors across in-scope types
(`Maybe.Some`/`Option.Some`, `Network.Address`/`Customer.Address`) coexist,
disambiguated by the dotted canonical form in **value AND pattern position**,
exactly as same-named fields already coexist.

Binding inputs:

- **Spec (landed):** `spec/08-modules.md §8.5.2` ("Constructor members are the
  CANONICAL constructor name" + "Product dual-facet corner"), `§8.6.5`
  ("Duplicate constructor names contest the bare ALIAS"); `spec/06-pattern-matching.md
  §6.2.1/§6.2.2/§6.2.4` + the §6.2 EBNF (dotted constructor patterns).
- **Arch (binding):** `design/arch/dotted-ctor-canonical-keys.md` — Obligation A
  (`type_ctor_names` walk to canonical keys), Obligation B (`CACHE_SCHEMA_VERSION`
  16→17), the `member_key` sweep, the read-side delegations. This design conforms
  to it.
- **Machinery to mirror:** `crates/cranelisp-typecheck/src/adt.rs`
  `synthesise_one_accessor` (canonical-key + bare-alias + `Ambiguous`-poison) and
  `committed_accessor_kind`; `checker.rs::resolve_dotted_field_accessor`;
  `cranelisp_types::member_key` (landed, commit `9c69b203`).

The mechanism is **arch-ruled** (SPRINT.md Phase 2): the field inverted-model
mirror — a real got-slotted ctor `Def` under the canonical `Type.Ctor` key + a
poisoning bare alias — **NOT** a resolver-only bare-key probe (staging resolve-only
first is a forbidden Principle-8 interim). Size = MEDIUM, one registration-led
change; the single-type case (`Color.Red`) falls out for free once the canonical
key exists.

---

## 0. The unifying insight — the ctor is *already* a got-slotted `Def`; only its key moves

The field-accessor path had to **synthesise** a fresh `UserFn` `Def` (scheme +
match body + GOT slot) per field. The constructor path is **strictly simpler**:
`register_constructors` (`adt.rs:299`) already builds the real got-slotted
`DefKind::Constructor` `Def` — with its `got_slot`, `tag`, `field_count`,
`internal`, `type_def`, ctor `scheme` (via `build_constructor_scheme`), and
`param_names`. Today it inserts that `Def` under the **bare** ctor key
(`adt.rs:382` `insert(ctor.name.clone(), builder.build())`). The whole change is:

> **Insert the real ctor `Def` under the canonical key `member_key(Type, Ctor)`
> and register the bare ctor name as an `Import` alias onto it — poisoning the
> bare name to `ModuleEntry::Ambiguous` when a second in-scope type contests it.**

This is the exact mirror of `synthesise_one_accessor` (`adt.rs:595–702`), with two
genuine differences and one deletion of complexity:

| Aspect | Field accessor (`synthesise_one_accessor`) | Constructor (`register_constructors`) |
|---|---|---|
| The canonical `Def` | *synthesised* here (scheme + match body + fresh slot) | **already built** — reuse the `builder.build()` value verbatim; only change its key |
| Recognizer of a committed member | `committed_accessor_kind` (`self$accessor` marker + `Fn[ADT]` scheme) | `DefKind::Constructor.type_name` **directly names the owner** — no marker needed |
| Visibility of the bare alias | Private-for-listing (§1.6.5, to avoid `/list` double-count) | **deftype `visibility` (Public)** — preserves established bare-ctor cross-module import reach (`(import [m [Some]])`); see §2.4 |
| Poison re-mint helper | deleted (`remint_first_accessor_under_qualified_key`) | never existed — nothing to delete |

Both members share the **one resolver** (§3): a `Type.member` reference resolves
head→`FQTypeName`, probes `member_key(fqtn.name, member)` in the type's home
module, and accepts the terminal entry if it is a member of that exact type. Under
Principle 7 the canonical `Def.scheme` / `DefKind::Constructor` is the single
source; under Principle 6 the ctor path adds no new data structure and no
`cranelisp-types` shape (the `Ambiguous` sentinel, `Import` alias, `FQSymbol`,
`member_key`, and `DefKind::Constructor.type_name` all exist).

---

## 1. Registration — `adt.rs::register_constructors`

### 1.1 The canonical key + bare alias (sum ctors)

In `register_constructors` (`adt.rs:299`), the per-ctor loop currently ends with
`self.current_symbol_table_mut(state).insert(ctor.name.clone(), builder.build())`
(`adt.rs:382`). For a **sum/enum ctor** (`product_type_def` filter did NOT attach
a `type_def` — i.e. `ctor_type_def.is_none()`, the existing `is_product_ctor`
flag is `false`) replace that with:

1. **Canonical key.** `let canonical_key = member_key(&fqtn.name, ctor.name.as_ref());`
   (the ONE mint point — `cranelisp_types::member_key`, `resolve.rs:825`; kills the
   hand-rolled `format!`). Insert the **already-built real ctor `Def`** under
   `canonical_key`. Its `got_slot`/`tag`/`field_count`/`internal`/`scheme`/
   `param_names`/`visibility` are unchanged — the ctor `Def` is uniformly the real
   entry, keyed `Maybe.Some`. It stays `defined_symbols()`-visible (codegen emits
   it under the canonical key, exactly as `Box.v` accessors are emitted).

2. **Bare alias + collision.** Probe the current bare ctor name (union view,
   staging-then-live) via `probe_module_entry_owned(&fqtn.module, ctor.name)`:
   - **absent** → insert `ModuleEntry::Import { source: FQSymbol { module:
     fqtn.module, symbol: canonical_key }, visibility }` (deftype visibility — §2.4).
     Bare `Some` now resolves via chain-follow to `Maybe.Some`.
   - **present and its terminal is a `DefKind::Constructor` owned by a DIFFERENT
     `FQTypeName`** (§8.6.5 distinct-terminal) → replace the bare key with
     `ModuleEntry::Ambiguous { visibility }`. Bare `Some` is poisoned; `Maybe.Some`
     and `Option.Some` (the canonical `Def`s) stay valid. Record both owners for the
     alternatives hint (see §1.3).
   - **present and its terminal is a `DefKind::Constructor` owned by the SAME
     `FQTypeName`** (a redefinition of this one deftype — the REPL re-run case) →
     re-install the bare `Import` alias afresh; NOT a cross-type contest.
   - **present as a non-ctor binding** (a user `defn`, an import of an unrelated
     symbol) → do NOT clobber it; the canonical `Maybe.Some` is still minted and
     reachable (mirrors the accessor `NonAccessor` arm, `adt.rs:689`). Constructors
     are uppercase, so this is rare; §8.6.4 governs a genuine definition-over-a-name
     conflict at the `deftype` register seam, not here.

### 1.2 The committed-member recognizer — read `type_name` directly, follow bare aliases

The accessor path needed `committed_accessor_kind` (`adt.rs:818`) because a
synthesised accessor has no intrinsic "I am an accessor of `Box`" field — it is
inferred from the `self$accessor` param + `Fn[ADT]` scheme. **A ctor needs no such
inference**: `DefKind::Constructor.type_name` *is* the owning `FQTypeName`. The
recognizer is therefore a 3-line read:

```
committed_ctor_owner(entry) -> Option<FQTypeName>:
  ModuleEntry::Def { kind: DefKind::Constructor { type_name, .. }, .. } => Some(type_name)
  _ => None
```

with the same **bare-alias follow** the accessor path added inline (`adt.rs:550–562`):
when the probed bare entry is `ModuleEntry::Import { source, .. }` whose
`source.module == fqtn.module`, follow one edge to the canonical `Def` and read
*its* `type_name`. This is what distinguishes "bare `Some` already aliases
`Maybe.Some`" (a cross-type contest against `Option`) from "bare `Some` is free."

**Recommendation (Principle 7, `/dev`'s call on exact factoring):** generalize
`committed_accessor_kind` into a member recognizer that answers "owning type of the
member under this key" for **both** accessors and ctors (an accessor's owner comes
from the `Fn[ADT]` scheme; a ctor's from `type_name`), so the bare-alias poison
logic is one shared shape rather than two mirrors. The `Ambiguous` sentinel arm is
already common. If the mirror is cheaper to land, a parallel `committed_ctor_owner`
is acceptable — but the **resolver** (§3) MUST be shared (the arch directive), not
the registration collision classifier.

### 1.3 Ambiguity diagnostic alternatives (cross-cluster)

Reuse the accessor bookkeeping verbatim: `state.accessor_owning_types`
(`adt.rs:629`) and `reconstruct_accessor_alternatives` (`adt.rs:769`) already map a
contested bare member name → its owning `FQTypeName`s by walking the module's union
view for canonical `Type.member` `Def`s whose terminal segment equals the bare name.
That walk keys off `committed_accessor_kind` today; extended to recognize ctor
`Def`s (§1.2) it yields `Maybe`/`Option` for a contested bare `Some`, so the
poison diagnostic reads *"ambiguous bare name `Some`; use `Maybe.Some` or
`Option.Some`"* — including the cross-cluster (REPL) case where the first owner was
committed in a now-discarded prior cluster. **Recommendation:** rename these to
member-neutral names (`member_owning_types`, `reconstruct_member_alternatives`) as
part of the generalization; not load-bearing for correctness.

### 1.4 What genuinely differs from the accessor path (summary for `/dev`)

- No synthesis — reuse the built ctor `Def`; only its **key** changes (bare →
  canonical) and a bare **alias** is added.
- Owner is read from `type_name`, not inferred from a param marker.
- Bare alias is **Public** (deftype visibility), not Private-for-listing (§2.4).
- No poison re-mint helper to delete (ctors never had one).

---

## 2. Product dual-facet corner (spec §8.5.2 "Product dual-facet corner")

A **product** ctor has type-name == ctor-name (`(deftype Point [:Int x :Int y])`);
its `Def` carries `type_def: Some(..)` and is the surviving single entry under the
type-name key `Point` (the S79 dual facet, `adt.md §"Product Type Handling"`,
`crates/cranelisp-typecheck/CLAUDE.md §"Product-ctor dual facet"`). The canonical
dotted form `member_key("Point","Point") = "Point.Point"` is **degenerate**.

**Registration ruling (settling the arch note's deferral to `/design`):** a product
ctor keeps its **single key at the type name** and is **NOT** re-keyed and gets
**NO** bare alias and **NO** poison. Concretely, gate the §1.1 canonical-key
rewrite on the existing `is_product_ctor` flag (`adt.rs:358`):

- `is_product_ctor == true` → keep the current `insert(ctor.name, builder.build())`
  (i.e. `insert("Point", ..)`) verbatim. The type-name key already carries both the
  type facet (`type_def: Some`) and the ctor `Def`; splitting it into a
  `Point.Point` canonical + `Point` alias would break `type_def_view_of`'s "entry as
  a type" read and double-register the facet. No dotted form is minted; no bare alias
  (the bare name *is* the canonical single key).
- `is_product_ctor == false` (sum/enum) → the §1.1 canonical-key + bare-alias path.

**Why no spurious poison.** Two distinct product types cannot share a ctor name
without sharing a *type* name (ctor-name == type-name for products), which is a
§8.6.4 type-name collision governed at the `deftype` register seam, not §8.6.5
alias-poison. So the product arm never contests a bare alias — there is none. The
degenerate `Point.Point` reference simply does not resolve (the resolver §3 probes
`member_key("Point","Point")`, finds no such key, returns `None`); `Point` (bare,
the canonical single key) is the reference, matching spec ("reached by its type
name, never a dotted form").

---

## 3. The one member resolver — value AND pattern position (arch: "one codepath")

Today two ctor-resolution seams exist and neither probes the canonical ctor key:

- **Value position** — `checker.rs::lookup` (`:1200`) calls
  `resolve_dotted_field_accessor` (`:1404`), which resolves head→`fqtn`, probes
  `member_key(fqtn.name, member)`, but **accepts only accessors**
  (`committed_accessor_kind == Concrete(fqtn)`). For `Color.Red` it returns `None`,
  falls through the `/`-split, and dies "undefined variable: Color.Red" — the
  committed RED `dotted_constructor_in_value_position_resolves`.
- **Pattern position + auto-curry guard** — `infer.rs::check_constructor_pattern`
  (`:970`) and `try_auto_curry` (`:657`) call
  `checker.rs::resolve_constructor_entry` (`:1593`), which handles `/`-qualified
  and bare, but has **no dotted `Type.Ctor` arm**: a dotted `Maybe.Some` with no
  `/` routes to `resolve_entry_in_current_module`, which finds the canonical key
  only when the type is *same-module* (literal-key hit) and **misses for imported
  types** (the canonical key lives in the type's home, not the current module).

### 3.1 Shared core — `resolve_dotted_member_entry`

Extract the value resolver's head→fqtn→`member_key` core into ONE helper that
returns the terminal entry (both seams consume it — the arch "one member-resolution
codepath" requirement):

```
resolve_dotted_member_entry(state, name) -> Option<ModuleEntry<C>>:
  // exactly one '.', both sides non-empty, no '/' (that is the qualified path's) —
  // the existing guard in resolve_dotted_field_accessor (:1409-1419)
  split name at first '.' into (type_part, member_part)
  fqtn = type_def_view_of(scope_resolve(state, type_part)?.entry)?.name   // head → owner
  entry = probe_module_entry_owned(fqtn.module, member_key(fqtn.name, member_part))?
  // accept only a member OWNED BY THIS EXACT type (accessor of fqtn OR ctor of fqtn)
  if owner_of_member(entry) == Some(fqtn) { Some(entry) } else { None }
```

`owner_of_member` is the generalized recognizer of §1.2 (accessor via
`committed_accessor_kind`, ctor via `type_name`). Rooting the member probe in
`fqtn.module` is what makes the dotted form work **cross-module** — the head
resolves through the type import to its home, and the canonical member key lives
there.

### 3.2 Value position — generalize `resolve_dotted_field_accessor`

`resolve_dotted_field_accessor` becomes `resolve_dotted_member`: call
`resolve_dotted_member_entry`, then `extract_scheme_from_entry_owned(&entry, 0)`.
Because `extract_scheme_from_entry_owned` reads `ModuleEntry::Def.scheme` for **any**
`Def` (`:1547`), a ctor `Def`'s scheme (`(Fn [a] (Maybe a))` for data, `(Maybe a)`
for nullary) returns unchanged; `lookup` instantiates it with fresh vars exactly as
for the accessor. `Color.Red` now types as `Color`; `Maybe.Some` as `(Fn [a] (Maybe
a))`. First-classness is automatic (the canonical ctor `Def` is an ordinary
got-slotted callable). No new value-position branch — the same `lookup` seam, one
generalized helper. **This flips the committed RED.**

The `infer_var` pre-checks (`is_internal_constructor`, constrained/overloaded
value-use guards, `infer.rs:265–309`) already resolve through
`resolve_constructor_entry`/`resolve_entry_in_current_module`, which gain the dotted
arm (§3.3) — a dotted `Maybe.Some` reads `internal: false` off the canonical ctor
`Def` and is admitted (not rejected). Internal ctors (`Bind`) are never written
dotted by users, so the dotted internal-ctor path is vacuously correct.

### 3.3 Pattern position + auto-curry guard — add the dotted arm to `resolve_constructor_entry`

`resolve_constructor_entry` (`checker.rs:1593`) gains a **dotted arm before** the
bare/`/`-split dispatch: when `name` contains `.` and no `/`, return
`resolve_dotted_member_entry(state, name)` (the caller already filters the returned
entry to `DefKind::Constructor`). This is the SAME core the value seam uses — one
codepath. It makes `(Maybe.Some x)` and dotted nullary `Maybe.None` resolve to the
canonical ctor `Def` for both same-module and imported types (the current
`resolve_entry_in_current_module` literal-key hit worked only same-module).

`check_constructor_pattern` (`infer.rs:1009`) then reads `type_name`/`tag` off the
resolved Constructor `Def` and instantiates via `instantiate_ctor` exactly as for a
bare or `/`-qualified ctor — no pattern-specific change beyond the resolver arm. The
`instantiate_ctor` helper (`infer.rs:137`) is tag-and-`TypeDefInfo`-driven and
unaffected by keying. **Value and pattern agree by construction — both reach the
identical canonical `Def` through the shared core** (spec §6.2.1 "mirrors value
position exactly").

### 3.4 Frontend — dotted `Pattern::Constructor` is ALREADY produced (confirmed, no change)

The parser lands `Pattern::Constructor.name` **unsplit**, in both pattern shapes —
verified in `crates/cranelisp-frontend/src/ast_builder.rs::build_pattern` (`:1437`):

- **Parenthesized data pattern** `(Maybe.Some x)` → `children[0]` symbol `"Maybe.Some"`
  becomes `Pattern::Constructor { name: SymbolRef { module: None, name: "Maybe.Some" },
  bindings: [x] }` (`:1474`).
- **Bare nullary dotted** `Maybe.None` → `is_uppercase_start("Maybe.None")` is `true`
  (leading `M`), so it is classified `Pattern::Constructor { name: SymbolRef { module:
  None, name: "Maybe.None" }, bindings: [] }` (`:1442`), NOT `Pattern::Var` — exactly
  §6.2.4 ("a dotted symbol in head position is always a constructor pattern").

So `check_constructor_pattern`'s `ctor_sym` = `"Maybe.None"`/`"Maybe.Some"` (the `.`
stays in `.name`) flows to the dotted arm (§3.3) with **zero frontend change** — the
capability is entirely pattern-*resolution* work in typecheck, matching SPRINT.md's
"frontend lands `Pattern::Constructor.name` unsplit; ~nil reader work."

---

## 4. Exhaustiveness — REQUIRED same-change-set fixes (blast radius, confirmed)

`check_exhaustiveness_in_module` (`adt.rs:915`) is a **hard** coupling that breaks
silently without two edits landing in the SAME change-set as registration:

1. **Covered-ctor normalization (`adt.rs:964–970`).** The `covered` set strips a
   `/` prefix (`macros/SCons` → `SCons`) but NOT a `.`: a dotted-covered
   `Maybe.Some` would compare as `"Maybe.Some"` against the bare `"Some"` in
   `all_ctors` → **false non-exhaustive**. Extend the normalizer to take the
   terminal segment after BOTH separators:
   `s.rsplit('/').next().unwrap_or(s)` then `.rsplit('.').next()`. (A `match` over a
   dotted `Maybe.Some` pattern is otherwise reported non-exhaustive even when total.)

2. **Internal-flag probe (`adt.rs:940–950`).** `all_ctors` is built from
   `type_def.constructors` (bare names — arch note §2: `TypeDefInfo.constructors`
   keeps bare display names), and per-ctor `internal` is read by
   `probe_module_entry_owned(&fq_type_name.module, ctor_sym)` matching
   `ModuleEntry::Def{Constructor}`. Post-change the bare key is an **`Import` alias**
   (or `Ambiguous`), so the raw probe no longer matches `Def{Constructor}` → every
   ctor defaults `internal: false`. Benign for user ADTs, but **breaks IO-style
   types with `internal` ctors** (`Bind`/`Pure`/`Effect`): they would stop being
   excluded and user `match`es on `IO` would be forced to cover them. Fix: chain-follow
   the bare name to its terminal before reading `internal` — replace the raw
   `probe_module_entry_owned` with `resolve_terminal_entry_and_home(&fq_type_name.module,
   ctor_sym)` (or probe `member_key(&fq_type_name.name, ctor_sym)` directly). Robust
   whether the ctor is canonically-keyed (bare alias → canonical `Def`) or
   bare-seeded (internal primitives, if seeded outside `register_constructors`).

Both are inside `adt.rs`, in the exhaustiveness helper, one change-set with
registration — no new type, no cache impact beyond Obligation B.

---

## 5. Obligations A + B coordination (arch-binding, SAME change-set)

Per `design/arch/dotted-ctor-canonical-keys.md`, these land in the SAME `/dev`
change-set as the `register_constructors` keying change (Principle 8 — no interim
state where reader and writer disagree on the key grammar):

- **Obligation A — `type_ctor_names` walks to canonical keys** (`cranelisp-types`,
  `heap.rs:269`, `/arch`/`/dev`-types coordination). Its three consumers use the
  returned `Vec<Symbol>` as storage keys (`table.get(key)`) to reach each ctor's
  `Def`. Sum arm returns `member_key(&fqtn.name, c)` per bare `c` in
  `TypeDefInfo.constructors`; product-facet arm returns the surviving type-name key.
  The mapping happens in the ONE reader; consumers unchanged. **Landing either the
  keying change or this walk alone breaks the `get(returned)` round-trip.**
- **Obligation B — `CACHE_SCHEMA_VERSION` 16→17** (`cranelisp-backend/src/cache/mod.rs`).
  The serde shape is unchanged but the **meaning** of a ctor `Def`'s storage key
  changes (bare → canonical) — a `.meta.json` content-meaning change per the cache
  contract (`crates/cranelisp-types/CLAUDE.md §"The serde shape IS the cache
  contract"`). Bump in the same change-set; owned by the Phase-5 registration wave.

Read-side delegations riding along (decoupled — any order, but this is the wave that
motivates them):

- `member_key` sweep — the new ctor registration site, `checker.rs::resolve_dotted_field_accessor`'s
  `format!` (`:1434`), `adt.rs`'s accessor `format!` (`:599`), and the diagnostic
  hint at `infer.rs:235` all call `member_key` (kills 4 hand-rolled `format!("{}.{}")`).
- `type_def_view_of` (`checker.rs:91`) reduces to `entry.type_def_info()` (the 0573
  read-side cure; not itself keying-coupled, but same-vicinity cleanup).

---

## 6. Blast radius — everything that keys on bare ctor names (CORRECTED to the landed coordinate model)

> **This §6 was empirically wrong** (FIXME 0582, filed by `/arch`). Its original
> table scoped the audit to **typecheck** consumers of bare ctor keys and marked
> the int/backend rows "unaffected / covered-by-construction". The W1.1a landing
> attempt measured **73 regressions** — the "unaffected" rows were the failures.
> The **cross-crate authority is `design/arch/dotted-ctor-canonical-keys.md`**
> (the W1.1a COORDINATE re-ruling, user-ruled P5): §3 (reader inventory), §1
> (uniform writers), §10 (DC-11 sidecar cure). This §6 is the typecheck-surface
> census pointing at that authority for the int/backend rows; where they overlap,
> the arch note wins.

**The audit lesson (record it, it is the durable takeaway).** A symbol-table
**keying change's blast radius is every crate's raw `table.get` probe, not the
owning crate's**. The failure was the §6 audit *method* — grepping typecheck —
not any individual row. A bare→canonical key flip is a cross-crate contract:
every reader that probes a ctor `Def` by bare key or follows aliases only one hop
must be found and widened in the **same change-set** as the writers, or the
readers and writers disagree on one name grammar (the Principle-8 "no landing
where they disagree" violation).

**Writer inventory — the uniformity the first landing missed (arch note §1).**
Keying is **uniform across every constructor writer**, not just `adt.rs`. All
writers mint the canonical `member_key(Type, Ctor)` `Def` + a same-module bare
`Import` alias (a **product** ctor keeps its single type-name key, no dotted key,
no alias):

| Writer | Site |
|---|---|
| User `deftype` | `cranelisp-typecheck/src/adt.rs::register_constructors` |
| Typecheck fixture seeds | `cranelisp-typecheck/src/builtins.rs::register_{slist,sexp}_type` (via `register_constructors`) — the fixture MUST mirror the live `bootstrap.rs` shape it stands in for |
| Int session seeds | `src/bootstrap.rs::register_synth_adt` — `Option`, `Result`, `IO` (`Pure`/`Effect`), `Trace`, the `macros` `SList`/`Sexp` families (`Pair` is product, unchanged) |
| The hand-appended `IO.Bind` | `src/bootstrap.rs::register_io_type` — canonical `IO.Bind` + bare alias like every sum ctor; `internal: true` rides the `Def` |

A seeded/user keying split is exactly the "100 such decisions would be chaos"
the user ruled out — no writer may keep bare-keyed sum-ctor `Def`s.

**The cross-crate census** (each row: handled here, or the cross-crate row the
original table got wrong / omitted — see arch note §3 for the fix mechanism):

| Site | Reads bare ctor how | Disposition |
|---|---|---|
| **`defined_symbols()` / codegen emission** | ctor `Def` under bare key → compiled | **Handled by construction.** Canonical `Def` is `defined_symbols()`-visible (only `Import`/`Ambiguous` are excluded); the bare alias adds no compiled fn. Ctor emitted once under `Maybe.Some` — proven by the `Box.v` accessor precedent. |
| **Backend tag dispatch — pattern position** (`match_codegen.rs::compile_constructor_pattern`) | ~~metadata rides the `Def`, dotted and bare reach the identical `Def`/GOT slot~~ | **WAS WRONG — the row that broke.** Backend `CompileContext::lookup_constructor` (`context.rs:146`) followed the import chain **exactly ONE hop** and its global fallback probed **bare keys**, so an imported bare ctor (`user.Nil → home.Nil-alias → home."List.Nil"`, 2 hops) MISSED → `unknown constructor: Nil` — the **root of the entire prelude cascade** (~30 regressions via `collections.list.test`). **Cure (LANDED, arch §10 DC-11):** typecheck records the canonical **storage key** in `MethodResolutions.pattern_ctors`, transported to codegen on a new `MonoMatchArm.resolved_ctor: Option<FQSymbol>` (populated via a **required** `MonoExpr::from_expr` `pattern_ctors` param — unforgettable, P18). Pattern codegen now does a **direct keyed read** `CompileContext::ctor_meta_at(&FQSymbol)` and **hard-errors** on a miss — no context-free re-resolution, no DashMap-order global fallback (the run-to-run wrong-tag nondeterminism class). `CACHE_SCHEMA_VERSION` 17→18. `lookup_constructor` is no longer called from pattern position. |
| **Backend ctor-as-value — nullary tag path** (`lookup_constructor` value position) | tag path misses on the 2-hop chain, falls through to fn-as-value closure wrap | **WAS WRONG — the silent class.** A cross-module bare nullary ctor value missed the tag path and compiled as a **fn-value closure** (CLIF-verified) → runtime "match failed", **silent wrong value**. **Cure (LANDED):** `lookup_constructor` collapsed onto the ONE backend resolution driver (`resolution.rs::resolve_driven`, multi-hop + alias-substitution + global fallback) with a ctor-extracting closure, and the driver's qualified/global arms made canonical-key-aware. Do NOT widen the one-hop copy in place (the P7 two-resolvers-one-name defect). |
| **Int value display** (`src/display.rs::ctor_field_types` :521) | raw `table.get(bare_ctor)` for `Def{scheme}` → alias → `None` | **WAS MISSING.** Data ctors rendered with **fields dropped** (`(Cons 2 …)` shows `List.Cons`; the `display_*` class). **Cure (LANDED):** probe `member_key(fqtn.name, ctor)` **canonical-first**, bare fallback for the product facet. |
| **Int member-glob import** (`src/imports.rs::collect_member_glob`) | scans `public_symbols()` for `Def{Constructor}` matching the parent type | **WAS MISSING.** Post-change it collects the CANONICAL (dotted) names, but bare aliases are `Import` edges and are **skipped**, so a member-glob importer loses bare ctor references. **Cure:** for each matched canonical member also install the bare-alias edge (mirroring the home module's binding shape; §8.6.5 ambiguity handling at the importer unchanged). |
| **SEEDED constructor writers** (`src/bootstrap.rs::register_synth_adt` + `IO.Bind`; `builtins.rs` fixture) | keep bare keys → seeded/user keying split | **WAS MISSING.** A seeded-vs-user split is a third keying. **Cure (LANDED):** every writer mints canonical + alias uniformly (writer inventory above). |
| **`match` exhaustiveness** | `type_def.constructors` (bare) vs covered patterns; per-ctor `internal` probe | **§4 — two REQUIRED edits, same change-set.** |
| **`instantiate_ctor`** (`infer.rs:137`) | `info.constructors[tag]`, tag-indexed on `TypeDefInfo` | **Unaffected** — bare-name list, tag-driven; no key probe. Note the sidecar single-mint point IS `instantiate_ctor` (arch §10.1): it probes canonical-then-bare and records **whichever key HIT** into `pattern_ctors`. |
| **`type_ctor_names` + backend heap classifiers** (`value_layout`, `is_mixed_adt`, `classify_adt`) | `type_ctor_names` → `table.get(key)` | **Obligation A** (§5) — walk returns canonical keys; soundness-coupled (`value_layout`), so must land together. |
| **Sparkability ctor-exclusion** (`let_if.rs::collect_module_constructors` vs `sparkability.rs::is_worth_sparking`) | storage keys vs source-written callee names | **Heuristic-only** (arch §10.4). Sum-ctor calls silently dropped from the exclusion set (spark-heuristic noise, not correctness). **Cure (LANDED):** both sides go through the ONE grammar `cranelisp_types::bare_member_name`. |
| **Mono collection** | mono keys on *fn* names / mangled variants | **Unaffected** — ctors are not monomorphised (concrete-per-instantiation via `ConstrADT`); `callees` explicitly does not record dotted member refs (typecheck CLAUDE.md). |
| **`public_symbols()` → `/list`/`/exports`/glob-import/agent harvest/`/search`** | surfaces Public entries | **Behaviourally preserved, DISPLAY flagged.** Canonical `Maybe.Some` (Public) + bare `Some` alias (Public, §2.4) both surface; bare-import reach (`(import [m [Some]])`) preserved. `/list` would show BOTH (double-count) — a REPL-experience call, **flag to `/repl`** (FIXME 0438 / `fixme-0365 §1.6.5`; E4 unified-display seam, bucket 6 / 0572). Not a typecheck correctness item. |
| **`instantiate_ctor` / `is_internal_constructor`** dotted input | strips `/` prefix, not `.` | Dotted `Maybe.Some` resolves through the `resolve_constructor_entry` arm (§3.3); `is_internal_constructor` reads `internal: false` off the terminal ctor `Def` — admitted, not rejected. **Unaffected** (internal ctors never written dotted). |

**Sites that silently break without the coordinate edits:** the two backend
resolvers (pattern position → `unknown constructor` cascade; nullary value → the
silent wrong-value class), int value display (fields dropped), member-glob
(lost bare refs), the seeded-writer split, exhaustiveness (§4), and the
`type_ctor_names`/`value_layout` heap classifiers (§5, Obligation A —
soundness-coupled, a UAF class). The landing is ONE `/dev` deployment, two
commits: **reader-widening (behaviour-invariant)** then **writer-flip + cache
bump + RED flips** (arch note §4).

---

## 7. Public-API + quality attributes

- **Zero `cranelisp-typecheck` public-API movement** — the ctor `Def`, `Import`
  alias, `Ambiguous` sentinel, `member_key`, and `DefKind::Constructor.type_name`
  are all existing internal concepts; the resolver generalization and the dotted
  `resolve_constructor_entry` arm are `pub(crate)`/private. `cranelisp-types`
  touches are the Phase-3 `/arch` change-set (already landed: `member_key`) +
  Obligation A's in-place `type_ctor_names` walk (no signature change). Cache bump
  is Obligation B.
- **Simplicity (P6).** The ctor path is *simpler* than the accessor mirror it
  copies — no synthesis, no poison re-mint helper, owner read directly from
  `type_name`. Recommend collapsing the accessor + ctor collision classifiers into
  one member recognizer (§1.2) rather than growing a second mirror.
- **Single source of truth (P7).** One `member_key` mint point; one shared
  `resolve_dotted_member_entry` for value + pattern; the canonical `Def` is the sole
  scheme/metadata source; the bare alias is a pure `Import` edge (one compiled ctor
  per type, no duplicate GOT slot).
- **Enforce invariants structurally (P18).** "`Maybe.Some` names exactly one thing"
  is structural — the canonical ctor `Def` is unconditionally the real entry;
  ambiguity is confined to the bare alias and never touches the canonical form (no
  cross-module cliff — the canonical `Def` is uniformly Public, so `m/Maybe.Some`
  resolves in every case, contested or not).
- **Testability (P5).** Value: read the inferred type of a resolved dotted ctor
  (`Color.Red : Color`; `Maybe.Some : (Fn [a] (Maybe a))`). Pattern: `(Maybe.Some
  x)` binds and type-checks; bare `(Some x)` with two owners is a resolution error
  listing `Maybe.Some`/`Option.Some`. Poison: assert the bare key becomes
  `Ambiguous` and both canonical `Def`s stay valid. Product: `Point.Point` does not
  resolve; `Point` does; no spurious poison. All with `TestFixture`, no full
  pipeline. (Tests are `/dev`'s per the mandatory unit-per-fix; the committed RED
  `dotted_constructor_in_value_position_resolves` + `/testing`'s same-named-ctor twin
  — value + pattern — are the e2e acceptance.)

---

## 8. Under-specification / dependencies to raise (no guessing)

The landed spec and the arch note are **sufficient** for the typecheck
implementation — no `target: /spec` or `target: /arch` FIXME is warranted from this
design pass. The product corner (§2), the value/pattern agreement (§3), and the
alias-poison direction (§8.6.5 not §8.6.4) are all explicit in the landed §8.5.2 /
§8.6.5 / §6.2. The one potential cross-crate dependency (frontend pattern
classification, §3.4) is **confirmed already satisfied** — no frontend change. One
coordination item to record for Phase 4 (a dependency, not a gap):

1. **`/repl` — `/list`/`/exports`/`/search` display of the bare alias (§6 display
   row).** The canonical + bare-alias double-listing is a REPL-experience call to
   mirror the accessor listing ruling (FIXME 0438) under the E4 unified-display seam
   (bucket 6 / 0572). Recorded here so `/repl`'s bucket-6 dispatch picks it up; no
   typecheck action.

---

## 9. Cross-references

- `spec/08-modules.md §8.5.2` (canonical constructor + product dual-facet corner),
  `§8.6.5` (duplicate ctor names contest the bare alias); `spec/06-pattern-matching.md
  §6.2.1/§6.2.2/§6.2.4` + §6.2 EBNF (dotted constructor patterns).
- `design/arch/dotted-ctor-canonical-keys.md` — Obligations A + B, `member_key`
  sweep, read-side delegations.
- `design/typecheck/fixme-0365-field-accessor-dotted.md` — the field-accessor
  inverted-model this mirrors (§0/§1.6 = the accessor canonical-key + bare-alias
  precedent; §1.6.5 = the listing ruling `/repl` mirrors for ctors).
- `design/typecheck/adt.md` §"Product Type Handling", §"Constructor Scheme
  Generation" — the ctor `Def` this re-keys; the dual-facet the product corner (§2)
  preserves.
- `crates/cranelisp-typecheck/src/adt.rs` — `register_constructors` (`:299`, the
  keying change + product gate), `synthesise_one_accessor` (`:450`, the mirror),
  `committed_accessor_kind`/`CommittedAccessor` (`:818`/`:798`, the recognizer to
  generalize), `accessor_owning_types`/`reconstruct_accessor_alternatives`
  (`:629`/`:769`, the alternatives bookkeeping), `check_exhaustiveness_in_module`
  (`:915`, the §4 edits).
- `crates/cranelisp-typecheck/src/checker.rs` — `lookup` (`:1200`),
  `resolve_dotted_field_accessor` (`:1404`, generalize to `resolve_dotted_member`),
  `resolve_constructor_entry` (`:1593`, add the dotted arm),
  `resolve_terminal_entry_and_home` (`:1675`, the exhaustiveness internal-flag
  chain-follow), `type_def_view_of` (`:91`).
- `crates/cranelisp-typecheck/src/infer.rs` — `check_constructor_pattern` (`:970`),
  `try_auto_curry` (`:657`), `instantiate_ctor` (`:137`), `infer_var` guards
  (`:265`).
- `cranelisp_types::member_key` (`resolve.rs:825`), `DefKind::Constructor`
  (`module.rs`), `type_ctor_names` (`heap.rs:269`, Obligation A),
  `CACHE_SCHEMA_VERSION` (`cranelisp-backend/src/cache/mod.rs`, Obligation B).
