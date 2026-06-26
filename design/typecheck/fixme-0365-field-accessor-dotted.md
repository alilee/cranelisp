# FIXME 0365 — `Type.member` field-accessor typing + impl-time collision rule

Owner: `/design` (typecheck triad). Subordinate to `design/typecheck/typecheck.md` §9.4
(ADT typing) and §9.1 (trait dispatch). Sprint 91, Thread C (FIXME burn-down — user
pulled 0365 forward from its Phase-H-opener slot; it is a language feature, not
release-tier).

Spec of record (S91 — **reframe pending** under the inversion; see the INVERSION BOX below):

- `spec/08-modules.md §8.5.2` — `Type.member` resolves a **field accessor** of `Type`, typed
  `(Fn [Type] FieldType)`. **Currently framed bare-primary / dotted-as-escape-hatch; the
  inversion makes `Type.field` the CANONICAL accessor + bare `field` a convenience alias —
  reframe filed `target: /spec` as FIXME 0439.**
- `spec/05-definitions.md §5.2.6` — generated accessors. **Same reframe (FIXME 0439): canonical
  is `Type.field`; bare is the alias, ambiguous when contested.**
- `spec/07-traits.md §7.3.1` — a trait `impl` whose method name collides with an existing
  field-accessor name of the target type **MUST be rejected at impl time** — **rule unchanged
  in substance** under the inversion (it now fires against the canonical `Type.field` key;
  FIXME 0439 only adjusts any "escape hatch" wording).
- `spec/08-modules.md §8.6.5` — duplicate-field-accessor note. **Reframe (FIXME 0439): the
  ambiguous name is the bare alias, not a "poisoned accessor"; canonical dotted forms stay
  reachable.**

Cascade (S91 Phase-5 `/dev`, per `/arch` ruling `sprints/SPRINT.md §"3. FIXME 0365"`;
**reframed under the inversion**): `/frontend` (resolution: canonical `Type.field` direct +
bare `field` alias → canonical, ambiguous when contested) → `/typecheck` *or* `/frontend`
(impl-time collision check against the canonical key) → `/typecheck` (types the canonical
accessor `(Fn [Type] FieldType)`) → `/qa` (contested-field ambiguity-in-the-alias guard +
canonical-always-reachable guard **+ a `_neg` guard that a colliding impl is rejected**).

This doc designs the two **typecheck-side** halves: **Item 1** — typing the
field-accessor `(Fn [Type] FieldType)`; **Item 2** — the impl-time collision check. (The
dotted-name *resolution* — splitting `Box.v` and locating the `Box` accessor `v` — is
`/design (cranelisp-frontend)`'s half. This doc consumes the resolved referent.)

---

> ## INVERSION BOX — canonical/alias direction INVERTED (S91 Phase-5, Wave-3 design review)
>
> **User ruling (relayed via coordinator, 2026-06-26; design-only — coordinator brings this
> back to the user for confirmation before any `/dev` rework, so treated as the settled
> design *premise*, not yet user-confirmed for landing).** The 0365 storage direction is
> **inverted** from the as-built model. This SUPERSEDES the §1.5 visibility-by-arm ruling
> (kept below, banner-marked SUPERSEDED, for the audit trail). The new design of record is
> **§0 / §1 / §1.6 / §2 below as rewritten for the inverted model.**
>
> **The inverted model (settled premise):**
>
> - **`Type.field` (e.g. `Box.v`) is the CANONICAL field accessor — ALWAYS.** A real
>   compiled function, **uniformly Public**, and the **listed/displayed** name (consistent
>   with the language's qualified-display convention `:primitives/Int`, `:(Fn [a] a) user/id`).
>   It does NOT change behaviour, visibility, or storage shape by case. One compiled function
>   per `(type, field)`, keyed `Type.field`.
> - **Bare `field` (e.g. `v`) is a CONVENIENCE ALIAS → `Type.field`.** **Ambiguity lives in
>   the alias, naturally.** One type with field `v` → bare `v` resolves to `Box.v`. Two types
>   sharing `v` → bare `v` has two candidate targets → the *alias* is ambiguous/error. The
>   canonical `Box.v`/`Cup.v` keep working throughout — there is **no cliff** where a contested
>   field becomes unreachable.
> - **This RETIRES the visibility-by-arm rule entirely.** No per-case visibility flip; no
>   re-minting; no poison-arm/non-poison-arm fork in the canonical storage. `Type.field` is
>   uniformly the real Public canonical `Def`; bare `field` is uniformly an alias (resolves
>   when unambiguous; ambiguous when contested). Deleting the special-case is the whole point.
>
> **Why (user reasoning, confirmed).** The as-built made bare `v` primary and `Box.v` a
> secondary alias whose visibility had to flip Public/Private by case (§1.5) — confusing and
> asymmetric, and it created a cliff (a contested field's only handle silently changed shape).
> Inverting puts ambiguity where it belongs (the short alias) and makes `Box.v` uniformly the
> canonical, always-reachable, always-listed handle — strictly better cross-module (no
> visibility cliff). Principle 6 (complexity has a budget — deletes a special-case),
> Principle 18 (enforce invariants structurally — the canonical entry is unconditionally real,
> so "`Box.v` names exactly one thing" needs no per-case reconstruction), Principle 16
> (qualified display is the canonical form, not a fallback).

---

## 0. The unifying insight — canonical `Type.field` `Def`, bare `field` is its alias

The crate already has the exact machinery 0365 needs, in `adt.rs`; the inverted model
**reuses the same `Def`/`Import` shapes, only swapping which key is the real `Def` and which
is the alias**:

- **Accessor synthesis** (`synthesise_one_accessor`, `adt.rs:449`) builds, per field, the
  accessor scheme `(Fn [ADT] FieldType)` (`adt.rs:467-475`) and a body
  (`(fn [self] (match self [(Ctor …) field]))`, `adt.rs:477-498`). **Inverted storage:** that
  real `DefKind::UserFn` `Def` (own GOT slot + body) is registered under the **canonical key
  `Type.field`** (e.g. `Box.v`), uniformly Public; the **bare key `field`** is registered as a
  **`ModuleEntry::Import { source: <module>/Type.field }` alias** pointing at the canonical
  key. (As-built does the reverse — real `Def` under bare `v`, `Import` alias under `Box.v`,
  `adt.rs:582-626`. The inversion swaps the two registrations.)
- **A structural recognizer already exists** — `committed_accessor_kind` (`adt.rs:677`) — that
  reads a `ModuleEntry` and answers: is this a synthesised accessor, and which `FQTypeName`
  owns it? It keys on the `self$accessor` param marker + the `(Fn [ADT] _)` scheme shape (no
  user `(defn …)` mints that signature). **Under inversion it recognizes the canonical
  `Type.field` `Def`** (the real entry still carries the `self$accessor`/`Fn[ADT]` marker) —
  the recognizer is unchanged; only the key it lives under moves.

Both typecheck halves still reduce to **reading the canonical accessor entry's scheme**:

- **Item 1 (typing)** — `FieldType` is the *return type of the canonical accessor's scheme*
  (`scheme.ty == Type::Fn([Type], FieldType)`). Whether `/frontend` hands typecheck the
  canonical `Box.v` `Def` directly (dotted form) or the bare-`v` `Import` alias (which
  chain-follows to `Box.v`), typing reads the same `Scheme` (§1.2). No new boundary type, no
  new algorithm.
- **Item 2 (collision)** — enumerating a type's field-accessor names is enumerating the
  canonical entries `committed_accessor_kind` classifies as `Concrete(target_fqtn)` —
  now keyed `Type.field` (§2.3). The impl collision check intersects the impl's method names
  with the type's field names; under inversion the field name is the *terminal* segment of the
  canonical key (`Box.v` → field `v`).

Principle 7 (single source of truth): both halves reuse `committed_accessor_kind` / the
canonical accessor `Def.scheme`, not a parallel field-walk. Principle 6 (complexity has a
budget): no new data structure, no `cranelisp-types` change, no `public-api.txt` movement (the
accessor `Def`, its `Scheme`, and the `Import` alias are existing internal concepts; `/arch`
confirmed 0365 is **zero baseline movement** — `sprints/SPRINT.md §"0365 … no new boundary
type"` — and the inversion does not change that: it relabels which key is `Def` vs `Import`).

---

## 1. Item 1 — typing the field accessor (canonical `Type.field`)

### 1.1 What `/frontend` hands typecheck (inverted model)

Two resolution paths, both reaching the **canonical `Type.field` `Def`**:

- **Dotted `Type.field` (canonical, always works).** `/frontend` splits `Box.v` and resolves
  it **directly to the canonical `Box.v` `Def`** in `Box`'s home module — the real accessor
  entry. This path is unconditional (no ambiguity ever, in any case): `Box.v` always names
  exactly the `Box`-`v` accessor.
- **Bare `field` (convenience alias → canonical).** `/frontend` resolves bare `v` via the
  **`Import` alias** `v → <module>/Box.v` to the canonical `Def`. When exactly one type owns a
  field named `v`, the alias is unambiguous and resolves. When two types share `v`, the bare
  alias has two candidate targets → **the alias is ambiguous** (resolution error on bare `v`,
  §8.6.5-shaped) — but the canonical `Box.v`/`Cup.v` `Def`s are unaffected.

So at the typecheck boundary, a resolved `Box.v` (whether via the dotted form or via an
unambiguous bare-`v` alias chain-follow) is **the canonical accessor `Def` whose scheme is
`(Fn [Box] Int)`** — exactly the entry `synthesise_one_accessor` registered under the
canonical key. There is no new "dotted accessor" AST node and no new entry kind: it is the
ordinary accessor `Def`, reached by either resolution path. The ambiguity is a *resolution*
concern on the bare alias (frontend-owned), not a typing concern — by the time typecheck sees
a referent, it is one canonical `Def`.

### 1.2 Typing rule — read the canonical accessor scheme

```
Γ ⊢ Type bound-in-scope     canonical accessor `Type.field` has scheme  Σ = ∀ᾱ. (Fn [Type] FieldType)
──────────────────────────────────────────────────────────────────────────────────────────────────
Γ ⊢ Type.field : instantiate(Σ)              (≡ (Fn [Type] FieldType) after fresh-var instantiation)

Γ ⊢ field resolves (alias, unambiguous) to canonical `Type.field`     Type.field : instantiate(Σ)
──────────────────────────────────────────────────────────────────────────────────────────────────
Γ ⊢ field : instantiate(Σ)                   (bare alias inherits the canonical scheme via chain-follow)
```

The accessor scheme is `Scheme { type_vars, constraints: ∅, ty: Fn([adt_type], field_ty) }`
(`adt.rs:467-475`), quantified over the type's params so a polymorphic product yields
`(Fn [(Box a)] a)`. Typing either form is **value-position scheme instantiation** — the same
path any callable goes through (`infer.rs` var-lookup → instantiate the scheme with fresh
vars). `FieldType` is the **return arm of the canonical accessor scheme's `Fn`** — no separate
field-table read; the scheme already carries it (Principle 7: the canonical accessor
`Def.scheme` is the single source of the accessor's type). For the bare alias, the typer
chain-follows the `Import` edge to the canonical `Def` and reads *its* scheme
(`extract_scheme_from_entry_owned` already follows `Import` edges, `adt.rs:610-611` comment) —
so both forms read one identical scheme.

First-classness (§8.5.2 — `Box.v` MAY be passed as an argument or bound to a variable) is
automatic: both forms resolve to the same canonical got-slotted `UserFn` `Def`, an ordinary
first-class callable; no special-casing in value position.

### 1.3 Why no new typecheck mechanism is required

The canonical accessor `Def` is **already** typed by the crate's existing machinery — it is
born with its `Scheme` and GOT slot at synthesis (`adt.rs:583-598`, under the canonical key
in the inverted model). Typing `Box.v` (or bare `v`) is not "type a new construct"; it is
"instantiate the scheme of an already-typed canonical accessor `Def`." The only typecheck
obligation is that the resolved entry's scheme is read in value position exactly as for any
callable — which the existing var-lookup/instantiate path already does. **The typecheck half
of Item 1 is effectively a no-op beyond confirming both resolution paths (dotted-direct and
bare-alias-chain-follow) type through the existing instantiation seam** — provided `/frontend`
hands typecheck the canonical `Def` reference (directly for the dotted form; via the `Import`
alias chain-follow for the bare form).

The inverted model makes this *cleaner* than the as-built: there is no per-case "is this the
poison arm" branch in typing — the canonical `Def` is unconditionally real and Public, so
typing is the same single path in every case (Principle 6 — the special-case is deleted).

### 1.4 `/dev` acceptance — Item 1 (inverted model)

Unit tests, typecheck in-crate (`TestFixture`, `crates/cranelisp-typecheck/src/.../tests.rs`):

- **Positive (canonical dotted, monomorphic)** — `(deftype Box [:Int v])`: the canonical
  `Box.v` types as `(Fn [Box] Int)`; with a second `(deftype Cup [:Bool v])` in the same
  module, `Cup.v` types as `(Fn [Cup] Bool)` — distinct canonical denotations, **always
  reachable regardless of the shared field name** (no poison cliff on the canonical form).
- **Positive (bare alias, unambiguous)** — `(deftype Box [:Int v])` alone: bare `v` resolves
  via the alias to canonical `Box.v` and types as `(Fn [Box] Int)`.
- **Negative (bare alias, contested)** — `(deftype Box [:Int v])` + `(deftype Cup [:Bool v])`:
  using **bare `v`** is a resolution error (the alias has two targets, ambiguous — §8.6.5
  shape), while `Box.v` and `Cup.v` both type fine. (This is the inverted ambiguity: error on
  the alias, not on the canonical form.)
- **Positive (polymorphic)** — `(deftype (Box a) [:a v])`: `Box.v` types as `(Fn [(Box a)] a)`
  (fresh-var-instantiated), confirming the quantified scheme reads correctly through the
  canonical key.
- **Positive (sum accessor)** — `(deftype (Option a) None (Some [:a unwrap]))`: `Option.unwrap`
  types as `(Fn [(Option a)] a)` (partial accessor — typing is unaffected by partiality;
  partiality is a runtime panic, §5.2.6).
- **Positive (first-class)** — `Box.v` bound to a let or passed as an argument type-checks as
  the accessor function value (not eagerly applied).
- **Negative / boundary** — `Box.nonfield` (a member that is not a field accessor of `Box`,
  nor a constructor, nor a trait method) is a resolution error (frontend-owned; typecheck
  sees no entry — assert the resolve error surfaces, not a spurious type error).

The end-to-end "contested bare `v` errors, `Box.v`/`Cup.v` both work, `/list` shows the
canonical qualified names" path is `/qa`'s integration guard (cascade step 4); the unit tests
above pin the typing at the scheme-read seam.

---

## 1.5 RULING — dotted-accessor key visibility (Wave-3 `/review` leak fix, S91) — **SUPERSEDED**

> **⚠️ SUPERSEDED by the INVERSION BOX (top of doc) + §0/§1.6, S91 Phase-5 user ruling
> 2026-06-26.** The visibility-by-arm rule below was the fix for the *as-built* model (bare
> `v` primary, `Box.v` a secondary alias whose visibility flipped Public/Private by case). The
> inverted model **retires it entirely**: `Type.field` is uniformly the Public canonical `Def`;
> bare `field` is uniformly an `Import` alias (ambiguous when contested). There is no per-arm
> visibility flip, no poison re-mint, no special-case. The replacement design — uniform
> canonical storage + ambiguity-in-the-alias — is **§1.6 below**. This section is retained
> (not deleted) for the audit trail of how the leak was found and why the inversion is the
> better structural fix (it deletes the special-case the §1.5 fix had to manage).

**Context (`/review` Wave-3 re-review finding).** `/dev` implemented the dotted accessor
storage in two arms inside `synthesise_one_accessor` (`adt.rs`):

- **Non-poison arm** (`adt.rs:617-626`): the dotted `Box.v` key is registered as
  `ModuleEntry::Import { source: <module>/v, visibility }` — a **pure internal dispatch/typing
  alias** onto the still-live bare `v` accessor. This is the correct zero-cost shape (no second
  compiled function, no second GOT slot; the alias's `Import` edge is followed for both
  dispatch and typing — §0/§1.3, the design's "typecheck half is a no-op"). **BUG:** the alias
  inherited the deftype's `visibility` (Public for a public type), so `is_public()` admits it
  and it leaks via `public_symbols()` (`module.rs:639-641`) into `/list`, `/exports`,
  glob-import re-export (`src/imports.rs::collect_glob:178`, `collect_member_glob:245`), and
  agent harvest (`src/agent/harvest.rs:140`) — a spurious top-level/exported/importable symbol
  **for every accessor in every program**. Consumers filter `$`-mangled names but NOT the
  `.`-dotted-key shape.
- **Poison arm** (`adt.rs:658-672` current type + `remint_first_accessor_under_qualified_key`
  for the first type): the dotted `Box.v`/`Cup.v` keys are **real `Def`s** (own slot + body)
  with `.visibility(visibility)` (Public), minted *because* bare `v` is poisoned to
  `ModuleEntry::Ambiguous` (`adt.rs:678-681`) and is unusable.

**The ruling — visibility-by-arm.** The two arms have genuinely different reachability roles,
so they get genuinely different visibility:

| Arm | Bare-name status | Dotted `Box.v` role | Ruling |
|---|---|---|---|
| **Non-poison** | bare `v` unambiguous + Public (the public surface) | redundant internal dispatch/typing alias | **`Visibility::Private`** — NOT in `public_symbols()`; absent from `/list`/`/exports`/glob/harvest |
| **Poison** | bare `v` `Ambiguous` (unusable) | the **ONLY reachable handle** to the field, incl. cross-module | **`Visibility::Public`** — in `public_symbols()`; listed/exported (the self-documenting escape hatch) |

**Non-poison → Private is safe (verified).** The public surface of the field is the bare
accessor `v`, which stays Public and listed; cross-module access is `(import [m [v]])` →
bare `v` (Public, reachable). Same-module dotted access still works because the dotted-name
resolver probes the bare key first (`adt.rs:614-616` comment) — typing never depends on the
alias's listing. The dotted `m/Box.v` qualified form is *redundant* in the non-poison case
(bare `v` already reaches the field unambiguously), so making the alias Private removes **zero**
reach. This exactly parallels the established `$`-mangled "internal, not listed" convention
(`src/CLAUDE.md §JIT Symbol Names`, the `$`-shape consumers already filter): an internal
dispatch handle is not part of the module's public API.

**Poison → Public is required (cross-module reachability — coordinator reasoning CONFIRMED).**
For a poisoned field, bare `v` is `Ambiguous` and unusable, so the dotted `Box.v`/`Cup.v`
`Def` is the *sole* handle to the field — and §5.2.6/§8.5.2 promise it works **cross-module**
too (the qualified `m/Box.v`). Cross-module qualified resolution enforces visibility:
`cranelisp_types::resolve.rs:578` gates a canonical entry on `entry.is_public() ||
in_subtree(from_module, home)` (the §8.7.3 filter). **Therefore if the poison re-mint were
Private, a poisoned field would be inaccessible from any module outside its home subtree** —
the escape hatch would silently fail cross-module, contradicting §5.2.6 ("cross-module, via
module-qualified names … `m/v` resolves directly") and §8.5.2 ("first-class … MAY be passed
as an argument"). The poison re-mint MUST stay Public + listed. The coordinator's
cross-module reasoning is correct and is hereby ruled load-bearing.

**Why listed (not merely Public) in the poison arm.** Self-documentation (root `CLAUDE.md`
§Design Principles — "every symbol should produce useful feedback"): when bare `v` is poisoned,
the only way a user discovers the reachable form is to *see* `Box.v`/`Cup.v` in `/list`/
`/exports`. A Public-but-hidden poison handle would be reachable-if-known-but-undiscoverable —
the opposite of the escape hatch's purpose. So in the poison arm the dotted key is both Public
*and* surfaced by the listing consumers.

### 1.5.1 `/dev` change — the precise edit

Both edits are in `crates/cranelisp-typecheck/src/adt.rs::synthesise_one_accessor` (the two
arms of the `match existing_kind`):

1. **Non-poison alias → Private.** At `adt.rs:617-626`, set the `ModuleEntry::Import`'s
   `visibility` field to `Visibility::Private` (NOT the deftype `visibility`). The alias is an
   internal dispatch/typing edge; its listing visibility is independent of the bare accessor's
   public visibility (the bare `v` accessor entry, registered separately, keeps the deftype
   `visibility`). One-line change: the `Import { source, visibility }` literal's `visibility`
   becomes `Visibility::Private`.
2. **Poison re-mint → stays Public.** No change required — the current type's re-minted `Def`
   (`adt.rs:664` `.visibility(visibility)`) and `remint_first_accessor_under_qualified_key`'s
   re-mint already carry the deftype `visibility` (Public for a public type). **Confirm** both
   re-mint sites keep `.visibility(visibility)` (do NOT let a blanket "make dotted keys private"
   sweep touch the poison arm — that is the trap this ruling guards against). The
   `ModuleEntry::Ambiguous` sentinel for bare `v` (`adt.rs:680`) is irrelevant to listing (a
   poisoned bare name is not a usable export; its `Public` mark is the lossless-mark
   convention, `module.rs:1217`, and consumers already special-case `Ambiguous`).

No `cranelisp-types` change (the `Visibility` enum + `Import`/`Def` visibility fields exist);
no `public-api.txt` movement (this is an internal entry-construction detail). **Zero baseline
movement holds** (§3) — this is a visibility-flag correction on an existing internal entry,
not a surface change.

### 1.5.2 `/qa` guards — the visibility-by-arm acceptance

Unit tests (typecheck in-crate, `TestFixture`) + the e2e listing/glob guards (`/qa`,
`tests/`):

- **Non-poison `_neg` (the leak guard — load-bearing).** `(deftype Box [:Int v])` (bare `v`
  unambiguous): assert the dotted key `Box.v` is **NOT** in the module's `public_symbols()`
  (the `Import` alias is Private). E2e: `Box.v` does **NOT** appear in `/list` / `/exports`,
  is **NOT** brought in by a glob `(import [m [*]])` into a consumer module, and is **NOT** in
  the agent-harvest symbol set. Bare `v` **IS** present (Public, listed) — the public surface
  is unaffected. Assert this holds **for every accessor** (a second product `(deftype Pt [:Int
  x :Int y])` → neither `Pt.x` nor `Pt.y` leaks).
- **Non-poison positive (typing unaffected).** `Box.v` still types as `(Fn [Box] Int)` and is
  callable/first-class (the Item-1 §1.4 tests) — Private listing does not break same-module
  dotted dispatch/typing (the resolver probes the bare key first).
- **Poison positive (cross-module reachability — load-bearing).** `(deftype Box [:Int v])` +
  `(deftype Cup [:Bool v])` in module `m` (bare `v` poisoned): from a *different* module,
  `m/Box.v` and `m/Cup.v` resolve and type (`(Fn [Box] Int)` / `(Fn [Cup] Bool)`) — the
  cross-module escape hatch works. Assert `Box.v`/`Cup.v` **ARE** in `m`'s `public_symbols()`
  and **DO** appear in `/list`/`/exports` for `m` (discoverable). Bare `m/v` is **rejected**
  as ambiguous (the poison holds).
- **Poison `_neg` (Private would break it — the regression the ruling prevents).** Pin the
  cross-module resolution of `m/Box.v` succeeding; were the re-mint Private, this test RED via
  the §8.7.3 visibility filter (`resolve.rs:578`) — it is the guard that a future "hide dotted
  keys" change does not silently re-break the escape hatch.

These join the Item-1/Item-2 suites; the non-poison `_neg` (no leak) and the poison positive
(cross-module reach + listed) are the two the Wave-3 finding specifically requires.

### 1.5.3 Normative anchor for the listing behavior — FIXME 0438 (filed `/repl`) — **UPDATED for inversion**

The §1.5 visibility-by-arm framing (and the original FIXME 0438 question, "show a dotted key
only when the bare name is poisoned") is **superseded by the inverted model** (§1.6.5): under
inversion the canonical qualified `Type.field` is **always** the listed accessor (every case),
and bare `field` is the convenience alias. FIXME 0438 has been **updated** to the inverted
question — "qualified `Type.field` is the canonical listed accessor; bare is the alias" — see
§1.6.5 for the listing ruling and the updated FIXME.

---

## 1.6 INVERTED-MODEL DESIGN (design of record) — canonical `Type.field`, bare alias

This section is the replacement for §1.5 under the user-ruled inversion (INVERSION BOX). It
covers the five redesign deliverables: synthesis storage (§1.6.1), ambiguity-in-the-alias
(§1.6.2), resolution + dispatch across modes (§1.6.3), `/dev` rework (§1.6.4), and
`/list`/`/exports` display (§1.6.5). The Item-2 collision check re-expressed against the
inverted storage is §2 (rewritten).

### 1.6.1 Accessor synthesis — canonical `Type.field` is the real `Def`; bare `field` is the alias

In `synthesise_one_accessor` (`adt.rs:449`), **invert the two registrations**:

- **Canonical key `Type.field`** (e.g. `Box.v`) → the **real `DefKind::UserFn` `Def`**: the
  existing scheme `(Fn [ADT] FieldType)` (`adt.rs:467-475`) + the existing match-body
  (`adt.rs:477-498`) + a fresh GOT slot, **uniformly `Visibility::Public`**, with the
  `self$accessor` param marker (so `committed_accessor_kind` still recognizes it). This is the
  one compiled function per `(type, field)`. The docstring names it the canonical accessor
  (e.g. ``"Canonical field accessor `Box.v` of type `Box`."``).
- **Bare key `field`** (e.g. `v`) → a **`ModuleEntry::Import { source: <module>/Type.field,
  visibility }` alias** pointing at the canonical key. The alias carries the deftype
  `visibility` (so an unambiguous bare `v` of a public type is a public convenience name).
  **No second compiled function, no second GOT slot** — the alias's `Import` edge is followed
  by `resolve_got_target`'s `resolve_chain` for dispatch and by `extract_scheme_from_entry_owned`
  for typing (the existing alias-follow machinery, `adt.rs:608-611` comment). The
  duplicate-codegen fix is **preserved** (still one function; the alias is free).

This is exactly the mirror image of the as-built (`adt.rs:582-626`, which registers the real
`Def` under bare `v` and the `Import` alias under `Box.v`). The swap is symmetric — the same
two entry shapes, opposite keys.

**One canonical entry, unconditionally.** Because the canonical `Box.v` `Def` is *always*
minted (not conditionally re-minted on poison), the as-built poison-arm machinery
**simplifies away**: `remint_first_accessor_under_qualified_key` (`adt.rs:729`) is **deleted**
(its whole job — reconstruct `Box.v` as a real `Def` when bare `v` poisons — is now
unconditional at synthesis, so there is nothing to reconstruct), and the
`AccessorCollision::Accessor` re-mint arm (`adt.rs:637-699`) collapses into the bare-alias
ambiguity handling (§1.6.2). Principle 6 (delete the special-case); Principle 8 (no interim
shape the follow-up unwinds — the canonical entry is the final shape from synthesis).

### 1.6.2 Ambiguity lives in the bare alias

When a **single** type owns field `v`: bare `v`'s `Import` alias has one target (`Box.v`) →
resolves cleanly. When **two** types in the same module own field `v` (`Box.v` and `Cup.v`):
the bare `v` key would need two `Import` targets → it is **ambiguous**. The bare key is set to
the existing `ModuleEntry::Ambiguous { visibility }` sentinel (`adt.rs:674-681`, the same
sentinel an import collision installs, §8.6.4) — listing the qualified canonical alternatives
`Box.v` / `Cup.v` in the diagnostic. Using bare `v` is then a compile-time error naming those
alternatives; **`Box.v` and `Cup.v` (the canonical `Def`s) remain valid and unchanged** — no
cliff, no re-mint, because they were always real.

Mechanically: the second-type synthesis sees a bare `v` already aliased to the first type's
`Box.v`. Instead of the as-built re-mint dance, it **replaces the bare `v` `Import` with the
`Ambiguous` sentinel** and records both owning types in `state.accessor_owning_types`
(`adt.rs:682-698`, already maintained) for the alternatives list. A third colliding type
leaves bare `v` `Ambiguous` and extends the alternatives. The `synthesised_accessor_names` /
`accessor_owning_types` bookkeeping and the FIXME-0366 cross-cluster union-view (staging-then-
live via `probe_module_entry_owned`, `checker.rs:1277`) **carry over unchanged** — they
already track "which types own this field name," which is exactly what the bare-alias ambiguity
needs. The cross-cluster REPL correctness the as-built handled (a prior-cluster `Box.v`) is the
same here: the second type's bare-`v` ambiguity must see the first type's canonical `Box.v`
committed to live, via the union-view probe.

**`NonAccessor` collision unchanged.** A pre-existing *non-accessor* binding under bare `v` (a
user `(defn v …)`, a ctor, an import) still refuses the synthesis with a deferred diagnostic
(`adt.rs:700-708`, `AccessorCollision::NonAccessor`) — the canonical `Box.v` is still minted
(it is unconditional), but the bare alias is not installed over a conflicting user binding.
(The canonical `Box.v` always existing is strictly better here: even when bare `v` is taken by
a user defn, the field stays reachable via `Box.v`.)

### 1.6.3 Resolution + dispatch — all modes (value / call / cross-module)

- **Dotted `Type.field`** resolves **directly** to the canonical `Def` (frontend splits on the
  last `.`, looks up `Type` in scope, resolves `field` as a field accessor of `Type` → the
  canonical key in `Type`'s home module). Always unambiguous. Value-position and call-position
  both work because the canonical entry is an ordinary got-slotted `UserFn` `Def`.
- **Bare `field`** resolves via the `Import` alias → canonical `Def` (chain-follow). The
  backend's `resolve_got_target` `resolve_chain` follows the `Import` edge to the canonical
  slot for **both call and value-position dispatch** (the same alias-follow the as-built used,
  `adt.rs:608-611`, only the direction of the edge is flipped — now bare→canonical rather than
  `Box.v`→bare). When ambiguous, bare `field` fails at resolution (the `Ambiguous` sentinel)
  before reaching dispatch.
- **Cross-module** is **strictly better under inversion** (the user's "no cliff" point,
  confirmed against `resolve.rs:578`): the canonical `Box.v` `Def` is **uniformly Public** in
  `Box`'s home module, so `m/Box.v` resolves cross-module in **every** case — including a
  contested field — because the §8.7.3 visibility filter (`entry.is_public() || in_subtree`,
  `crates/cranelisp-types/src/resolve.rs:578`) sees a Public canonical `Def`. There is no case
  where a field becomes cross-module-unreachable (the as-built's poison-arm-must-be-Public
  worry, §1.5, *disappears* — the canonical form is unconditionally Public, so there is no
  visibility cliff to guard against). Bare `m/v` cross-module resolves when unambiguous in `m`;
  when contested in `m`, the bare cross-module name is ambiguous, but `m/Box.v` always works.

All these are the **same modes `/dev` validated for the as-built** — the inversion does not add
a mode; it relabels which key is canonical. `/dev`'s existing value/call/cross-module/REPL test
coverage retargets to assert the canonical `Box.v` shape.

### 1.6.4 `/dev` rework — the precise edits

All in `crates/cranelisp-typecheck/src/adt.rs::synthesise_one_accessor` and its helpers:

1. **Swap the two registrations (§1.6.1).** The real `DefKind::UserFn` `Def` (scheme + body +
   fresh slot, `.visibility(Public)`) registers under `qualified_key` (`Box.v`, already built
   at `adt.rs:582`); the bare `accessor_name` key registers as `ModuleEntry::Import { source:
   FQSymbol { module: fqtn.module, symbol: qualified_key }, visibility }`. (As-built: bare =
   `Def`, `Box.v` = `Import`; this flips both.)
2. **Delete the poison re-mint path.** Remove `remint_first_accessor_under_qualified_key`
   (`adt.rs:729`) and the `AccessorCollision::Accessor` re-mint arm's `Def`-minting
   (`adt.rs:657-672`); the canonical `Box.v` already exists from step 1. The
   `AccessorCollision::Accessor` case now only: (a) replaces the **bare** `v` key with
   `Ambiguous` (§1.6.2), (b) extends `accessor_owning_types`. The current type's canonical
   `Cup.v` `Def` is minted by step 1 the same as any other (no special path).
3. **Uniform Public on the canonical `Def`.** The canonical `Def` is always
   `.visibility(visibility)` where `visibility` is the deftype's (Public for a public type) —
   no per-case flip (the §1.5.1 Private-flip is **removed**; it applied to the now-deleted
   alias-on-`Box.v` shape).
4. **`committed_accessor_kind` unchanged** — it recognizes the canonical `Def` by the
   `self$accessor`/`Fn[ADT]` marker, which now lives under `Box.v` instead of bare `v`. The
   enumeration helper (§2.3) keys off it the same way.

**Zero `cranelisp-types` change, zero `public-api.txt` movement.** The `Visibility` enum,
`ModuleEntry::Def`/`Import`, `FQSymbol`, and `Ambiguous` all exist; the inversion is an
internal relabeling of which key holds which existing entry shape. (Same zero-baseline
disposition as the as-built and §1.5; §3.) The change **net-deletes** code (the re-mint helper
+ the poison-arm `Def` minting), a Principle-6 simplification.

### 1.6.5 `/list` + `/exports` display — qualified `Type.field` is canonical and listed

**Ruling (inverted-model listing).** The **canonical qualified `Type.field` is the displayed/
listed accessor name — in every case** (not poison-only). This is consistent with the
language's qualified-display convention (root `CLAUDE.md` §Design Principles — `:primitives/Int`,
`:(Fn [a] a) user/id`; Principle 16 — qualified display is the canonical form, not a fallback).
`Box.v` appears in `/list` and `/exports` as the accessor for every field of every type.

The **bare `field` alias**: rule it **not separately listed as a distinct symbol** — it is a
convenience alias, not an independent accessor, and listing both `v` and `Box.v` would
double-count every field. Two sub-options for `/repl` to choose (this is a REPL-experience
call, deferred to `/repl` via the updated FIXME 0438):

- **(A) Show canonical only.** `/list` shows `Box.v`; bare `v` is reachable but not separately
  listed (it is "the alias for `Box.v`"). Cleanest; matches qualified-display convention.
- **(B) Show canonical, annotate alias.** `/list` shows `Box.v` and notes "(bare alias: `v`)"
  when `v` is unambiguous — more discoverable that bare works, at some verbosity cost.

This doc **recommends (A)** (Principle 6 / qualified-display convention) but the final
`/list`/`/exports` surface wording is `/repl`'s. The mechanical hook: under inversion the
canonical `Box.v` `Def` is uniformly Public → it is in `public_symbols()` (`module.rs:639`)
in every case, so `/list`/`/exports`/glob/harvest see it. The **bare alias** is an `Import`
entry; whether it surfaces depends on its visibility — to avoid the double-count, set the bare
alias `Visibility::Private` *for listing purposes* (it stays resolvable — visibility gates
*listing/export*, not same-module bare-name resolution, which goes through the alias edge
regardless). This is the one visibility nuance that survives inversion, and it is the
**opposite polarity** of §1.5: there the dotted key was hidden; here the **bare alias** is the
hidden/internal one and the **canonical dotted key** is the listed one. (No per-*case* flip —
the bare alias is uniformly not-separately-listed; the canonical is uniformly listed.)

**The agent-harvest / glob leak that motivated §1.5 is resolved more cleanly under inversion:**
`public_symbols()` surfaces exactly one entry per field — the canonical `Box.v` — which is the
*intended* discoverable accessor, not noise. The as-built leaked a redundant `Box.v` *on top
of* bare `v`; inversion makes `Box.v` the single canonical surface and bare `v` the hidden
alias, so there is no redundant double-listing in any case.

### 1.6.6 `/qa` guards — inverted-model acceptance

Unit (typecheck in-crate, `TestFixture`) + e2e listing/glob (`/qa`, `tests/`):

- **Canonical always Public + cross-module-reachable (load-bearing).** `(deftype Box [:Int
  v])`: `Box.v` is in `public_symbols()` and resolves cross-module (`m/Box.v`). **With a
  contested field** (`Box.v` + `Cup.v`, bare `v` ambiguous): `m/Box.v` and `m/Cup.v` **still**
  resolve cross-module (no cliff) — the inverted-model regression guard that a contested field
  never becomes unreachable.
- **Bare resolves when unique; errors-ambiguous when contested.** `(deftype Box [:Int v])`
  alone: bare `v` resolves (via alias) and types `(Fn [Box] Int)`. `Box.v` + `Cup.v`: bare
  `v` is a resolution error (ambiguous, alternatives `Box.v`/`Cup.v` listed); `Box.v`/`Cup.v`
  both type fine.
- **No duplicate codegen.** Assert one compiled function per `(type, field)` (the canonical
  key); the bare alias adds no GOT slot / no second function (CLIF inspection or the
  defined-symbols count, the same guard the as-built used for the duplicate-codegen fix).
- **`/list` shows qualified canonical; bare not double-listed.** E2e: `/list`/`/exports` show
  `Box.v` (every field, every case); bare `v` is **not** a separate listed symbol (option A) —
  exactly one accessor entry surfaces per field, no per-field noise, no double-count.
- **Trait-method-vs-accessor collision (Item 2, §2) fires against the canonical key.** A
  colliding `impl` is rejected (the §2.7 negative), re-expressed against the canonical
  `Box.v` storage.

These **replace** the §1.5.2 visibility-by-arm guards (which guarded the now-retired
poison/non-poison visibility flip).

---

## 2. Item 2 — impl-time field-accessor collision check

### 2.1 The rule (spec §7.3.1)

A trait `impl` whose method name equals an existing **field-accessor** name of the impl
target type MUST be **rejected at impl time**, with a diagnostic naming the colliding name
and both definition sites (the `deftype` field and the `impl` method). Casing makes the
scope exact and complete: constructors are uppercase (§1.4), accessors and trait methods are
both lowercase, so a field-accessor name can collide *only* with a trait-method name — exactly
the case this check covers. This is the no-silent-overload-consistent resolution: it
guarantees `Box.v` (§8.5.2) always names exactly one thing and never has to disambiguate
field-accessor-vs-trait-method, because the collision is prevented at the definition site.

### 2.2 Where the check goes — `register_trait_impl` / `check_impl_methods_present`

Impl registration and validation is `impl_check.rs::register_trait_impl` (`impl_check.rs:18`).
It already validates impl coherence — HKT arity (`:33`), method-presence (`check_impl_methods_present`,
`:196`), and per-method signature matching (`check_impl_method`, `:227`). The collision check
belongs **alongside `check_impl_methods_present`** (run from the same point, `impl_check.rs:79`),
as a new sibling validation `check_impl_method_accessor_collisions` — it is the same *class*
of pre-flight impl-coherence gate (reject the impl before type-checking its bodies), raising
the same `CranelispError::TypeError` shape with an `impl_`-span location.

Placing it next to `check_impl_methods_present` (and before the impl entry is registered at
`:119` and bodies are checked at `:182`) ensures the impl is **rejected before any side
effect** — no `ModuleEntry::TraitImpl` written, no mangled method `Def`s minted. Principle
18 (enforce invariants structurally): the bad impl never enters the symbol table.

### 2.3 How it enumerates the target type's field-accessor names

The check needs the target type's `FQTypeName`, then the set of field-accessor names owned
by that type, then an intersection with the impl's method names.

1. **Resolve the impl target to its `FQTypeName`.** `register_trait_impl` already resolves
   the target type: `resolve_type(state, impl_target_name_or_panic(&impl_.target), span)`
   (`impl_check.rs:107`) and `concrete_type_for_impl_target` (`checker.rs:1023`) yield the
   target's `Type::ADT(fqtn, _)`. Read `fqtn` (the owning `FQTypeName`) from there. Primitive
   targets (`Int`/`Bool`/…, `IntrinsicType`) have **no field accessors** — the collision set
   is empty, the check trivially passes (and parameterized/HKT targets resolve to an ADT
   `fqtn` the same way).

2. **Enumerate the type's field-accessor names (inverted-storage form)** — reuse
   `committed_accessor_kind` (`adt.rs:677`). Under inversion the **canonical** field accessors
   of `fqtn` live in `fqtn.module` under keys `Type.field` (e.g. `Box.v`), each a real Public
   `Def` the recognizer classifies as `CommittedAccessor::Concrete(owner)` with `owner == fqtn`
   (§1.6.1 — the `self$accessor`/`Fn[ADT]` marker now lives under the canonical key). Enumerate
   that module's entries, keep the `Concrete(fqtn)` ones, and extract the **field name as the
   terminal segment of the canonical key after the last `.`** (`Box.v` → `v`). (Equivalently,
   read it off the constructor's `param_names`; but the recognizer walk is the single source —
   §below.)

   Recommended (the design *recommends*; `/dev` decides the exact accessor): a small
   `field_accessor_names_of(&self, state, fqtn) -> HashSet<Symbol>` helper in `adt.rs` (next to
   `committed_accessor_kind`, its natural home) that walks `fqtn.module`'s entries, keeps the
   `Concrete(fqtn)` canonical accessor `Def`s, and returns their **post-dot field names**. This
   is the **single enumeration point** both the collision check and the `/list` "this type's
   accessors" display (§1.6.5) reuse (Principle 7). It reuses `committed_accessor_kind` rather
   than re-deriving the `self$accessor`/`Fn[ADT]` shape.

   **Inverted-model simplification of the edge cases.** Under inversion the field accessor is
   **always** a canonical `Concrete(fqtn)` `Def` — there is no `Poisoned` *canonical* entry
   (poison lives in the bare alias, §1.6.2, not in `Box.v`). So the §2.6 "consult
   `accessor_owning_types` for a poisoned accessor name" branch **simplifies**: the canonical
   `Box.v` is unconditionally a `Concrete` entry whether or not bare `v` is contested, so the
   `Concrete(fqtn)` walk alone is complete (the poisoned-bare-alias state is irrelevant to the
   *canonical* enumeration). The cross-cluster union-view (staging-then-live) still applies so
   a prior-REPL-cluster `Box.v` is seen (§2.6, FIXME-0366), but the poison consult drops out —
   another special-case the inversion deletes.

   Alternative considered: read field names off the constructor's `param_names`
   (`Def.param_names` for a product ctor, `adt.rs` migration map `check.rs:241`). The
   recognizer-walk is preferred (single source of "what is an accessor"); but under inversion
   the two agree exactly (every field has a canonical `Type.field` `Def`), so `/dev` may use
   `param_names` if simpler — the recognizer walk remains the canonical enumeration.

3. **Intersect with impl method names.** `impl_.methods.iter().map(|m| &m.name)` (the same
   set `check_impl_methods_present` builds at `:202`). Any name in both sets is a collision.

### 2.4 The error

On collision, raise `CranelispError::TypeError` (the impl-validation error type, used
throughout `register_trait_impl`), with a message naming **the colliding name and both
sites** per §7.3.1:

```
impl <Trait> for <Type>: method `<name>` collides with the field accessor `<name>`
generated by the field `<name>` of type `<Type>` (see deftype). A trait method
must not shadow an existing field accessor — rename the method or the field.
```

Location: `impl_.span` (or, finer, the colliding `method_defn.span` — the spec asks for
*both* sites; the message text carries the deftype site, the `location` points at the impl
method). Prefer the colliding method's span for the primary `ErrorLocation` so the diagnostic
underlines the offending `(defn <name> …)`; name the deftype field in the message body.
First collision found is sufficient to reject (no need to accumulate — the impl is invalid).

### 2.5 Ordering relative to other impl checks

Run the collision check **after** trait-decl lookup (so the trait exists) and HKT-arity
validation, and **before** `check_impl_methods_present` body validation is moot — i.e. at
`impl_check.rs:79`, either folded into `check_impl_methods_present` or as the immediately-
following sibling call. It does not depend on method-presence (a *colliding* method may not
even be a declared trait method — but §7.3.1's rule is about the **name**, independent of
whether the method is required), so it can run first among the name-level checks. Order
within the name checks is not load-bearing; placing collision-reject early gives the
clearest diagnostic (the user sees "collides with accessor" rather than a downstream
signature-mismatch on a method that should not have existed).

### 2.6 Edge cases (inverted model)

- **Contested field name (was "already-poisoned") — SIMPLER under inversion.** When a field
  name `v` is contested across `Box` and `Cup`, the *bare* `v` alias is `Ambiguous` (§1.6.2),
  but the **canonical** `Box.v` and `Cup.v` are unconditionally real `Concrete(fqtn)` `Def`s.
  So an impl method `v` for `Box` still collides — with `Box`'s canonical field accessor `v`
  (the `Box.v` `Def`) — and the `Concrete(fqtn)`-arm enumeration (§2.3) **alone** catches it:
  `v ∈ field_accessor_names_of(Box)` whether or not `v` is contested. The as-built's separate
  "consult `accessor_owning_types` for the poisoned case" branch (§1.5-era) **drops out** — the
  canonical entry is always present, so there is no poisoned-canonical case to special-case
  (another deletion the inversion buys; Principle 6). `accessor_owning_types` is still
  maintained for the *bare-alias* ambiguity diagnostic (§1.6.2), but the collision check no
  longer needs to read it.
- **Cross-cluster (REPL).** Canonical accessors of `fqtn` may have been committed to **live**
  in a prior REPL cluster (FIXME 0366). The enumeration must read the **union view** (staging
  then live) — `probe_module_entry_owned` (`checker.rs:1277`) is staging-then-live aware, and
  `committed_accessor_kind` works on a committed live entry by design. So enumerate via the
  staging-aware module read, not staging-only — otherwise a REPL `impl` colliding with a
  canonical accessor defined in an earlier input would slip through.
- **Cross-cluster (REPL).** Accessors of `fqtn` may have been committed to **live** in a
  prior REPL cluster (the same FIXME 0366 cross-cluster issue the synthesis path handles).
  The enumeration must read the **union view** (staging then live) — `probe_module_entry_owned`
  (`checker.rs:1277`) is staging-then-live aware, and the `committed_accessor_kind` recognizer
  works on a committed live entry by design (`adt.rs:668` rustdoc, FIXME 0366). So enumerate
  via the staging-aware module read, not staging-only — otherwise a REPL `impl` colliding with
  an accessor defined in an earlier input would slip through (the exact cross-cluster footgun
  FIXME 0366 documents for the synthesis side).
- **Default methods.** A trait method *with a default* that the impl does **not** provide is
  not in `impl_.methods`, so it cannot collide via the impl. But a generated default-method
  `Def` is mangled (`Trait.method$Type`, `impl_check.rs:144`) and never aliases a bare
  accessor name — defaults are out of scope for this collision (the collision is about the
  *bare* method name the user wrote in the impl block, which §7.3.1 scopes to the impl's own
  methods).
- **Impl method that is also a declared trait method** — the normal case. The collision rule
  fires regardless of whether the impl method is a valid trait method: a trait `Show` with a
  method `v` impl'd for `Box` (which has field `v`) is rejected, because `Box.v` (the canonical
  field accessor) and a `Box`-`Show`-`v` method would be two `(Fn [Box] …)` denotations for the
  same dotted name — exactly what §7.3.1 forbids so `Box.v` names one thing. Casing guarantees
  this is the *only* collision class (§7.3.1).

### 2.7 `/dev` acceptance — Item 2

Unit tests, typecheck in-crate (`TestFixture`; impl-validation tests live near
`crates/cranelisp-typecheck/src/traits/tests.rs`):

- **Negative (the load-bearing `_neg`, mirrors `/qa`'s cascade obligation)** — `(deftype Box
  [:Int v])` then `(impl SomeTrait Box (defn v [x] …))` is **rejected** with a `TypeError`
  whose message names the colliding name `v`, the trait, the target `Box`, and references the
  deftype field. Assert the impl did **not** register (no `ModuleEntry::TraitImpl`, no mangled
  method `Def`) — the structural rejection (§2.2 / Principle 18).
- **Positive (no collision)** — `(deftype Box [:Int v])` then `(impl SomeTrait Box (defn show
  [x] …))` (method name `show` ≠ field name `v`) registers normally.
- **Positive (primitive target)** — `(impl Display Int (defn show …))` is unaffected (Int has
  no field accessors; collision set empty).
- **Boundary (polymorphic / parameterized target)** — `(deftype (Box a) [:a v])` then
  `(impl T (Box a) (defn v …))` is rejected (the `fqtn` resolves through
  `concrete_type_for_impl_target` for the parameterized target the same way).
- **Cross-cluster (REPL) negative** — field `v` deftype'd in one cluster, the colliding impl
  in a later cluster, is still rejected (the union-view enumeration, §2.6) — pin the
  FIXME-0366-shaped cross-cluster behavior so the REPL matches `--run`/`--link`.
- **Contested-field negative (inverted form)** — `Box.v` and `Cup.v` both defined (bare `v`
  contested → bare alias ambiguous, but canonical `Box.v`/`Cup.v` real), then `(impl T Box
  (defn v …))` is rejected — the `Concrete(Box)` enumeration catches the canonical `Box.v`
  collision regardless of the bare contest (§2.6, simplified — no `accessor_owning_types`
  consult needed under inversion).

The `/qa` cascade obligation (`sprints/SPRINT.md §"3. FIXME 0365"`) is the **e2e `_neg`
guard that a colliding impl is rejected**; these unit tests pin it at the impl-validation
seam (the mandatory unit-per-fix, `CLAUDE.md §Testing`).

---

## 3. Public-API + interface disposition

- **Zero `public-api.txt` movement.** `/arch` confirmed 0365 carries **no baseline movement**
  (`sprints/SPRINT.md §"0365 … no `public-api.txt` movement"`): the accessor `Def`, its
  `Scheme`, and the impl-validation path are all existing internal concepts. Item 1 reads an
  existing scheme through the existing instantiation path; Item 2 adds an internal
  `pub(crate)`/private validation sibling and an internal enumeration helper — neither crosses
  the crate boundary. The two additive `cranelisp-typecheck/public-api.txt` lines this sprint
  are **only** the Pillar-3 match predicates (`signature-match.md`), not 0365.
- **No `cranelisp-types` change.** No new boundary type; `FieldInfo`/`TypeDefInfo`/`Scheme`/
  `committed_accessor_kind`/`ModuleEntry::{Def,Import,Ambiguous}`/`Visibility` (all existing,
  internal) suffice.
- **The inverted model (§1.6) is also zero baseline.** Swapping which key holds the `Def` vs
  the `Import` alias, deleting the poison re-mint helper, and the bare-alias `Ambiguous`
  handling are all internal entry-construction changes in `adt.rs`; no enum/field is added. No
  `public-api.txt` movement, no `cranelisp-types` change. The inversion **net-deletes** code
  (the re-mint helper + the poison-arm `Def`-minting) — a Principle-6 simplification, not a
  surface change. (The §1.5 visibility-by-arm fix it supersedes was likewise zero baseline.)

---

## 4. Quality attributes (this design pass — inverted model)

- **Simplicity (Principle 6) — the inversion is a net deletion.** The canonical `Type.field`
  `Def` is unconditionally real + Public, so the as-built's poison re-mint helper
  (`remint_first_accessor_under_qualified_key`) and the per-case visibility flip (§1.5) are
  **deleted**, not added to. Both halves still reuse `committed_accessor_kind` + the canonical
  `Def.scheme`; no new data structure, no `cranelisp-types` change, no new entry kind.
- **Single source of truth (Principle 7).** The canonical accessor `Def.scheme` is the sole
  source of `FieldType` (Item 1) and the `committed_accessor_kind` recognizer is the sole "is
  this an accessor, which type owns it" judgment (Item 2). Bare `field` is a pure alias edge
  onto the canonical — one definition, one scheme, one compiled function.
- **Enforce invariants structurally (Principle 18) — stronger under inversion.** The "`Box.v`
  names exactly one thing" invariant (§8.5.2) is now structural *by construction*: the
  canonical `Box.v` `Def` is always the single real entry; ambiguity is confined to the bare
  alias and never reconstructs the canonical. The impl collision is still rejected before the
  impl enters the symbol table (no `TraitImpl`/mangled `Def` on a colliding impl).
- **Testability (Principle 5).** Item 1 unit-testable by reading a resolved canonical
  accessor's inferred type; Item 2 by asserting a `TypeError` + no side effect; the inverted
  storage by asserting canonical-Public/cross-module-reachable + bare-ambiguous-when-contested
  — all with `TestFixture`, no full pipeline.
- **Observability + self-documentation (Principle 16 qualified-display).** `/list`/`/exports`
  surface exactly **one** entry per field — the canonical qualified `Box.v` — in every case
  (not poison-only), matching the language's `:module/name` qualified-display convention. No
  per-field double-listing, no redundant noise. This is *cleaner* than the §1.5 model, which
  had to hide a redundant dotted key that was layered on top of the bare name.
- **No-cliff cross-module reachability (the user's load-bearing point).** Because the canonical
  `Box.v` is uniformly Public, a field is **always** reachable cross-module as `m/Box.v` —
  including a contested field. The as-built's worry (a poisoned field's only handle must be kept
  Public, §1.5, gated on `resolve.rs:578`) **disappears**: there is no case where the canonical
  form is non-Public, so no visibility cliff to guard. The inversion removes the failure mode
  rather than guarding it.
- **Concurrency / performance — untouched.** No change to the crate's concurrency model or
  perf-sensitive paths; the enumeration is over one module's entries at impl-registration time
  (rare, small).

## 5. Cross-references

- `spec/08-modules.md §8.5.2/§8.6.5`, `spec/05-definitions.md §5.2.6`, `spec/07-traits.md
  §7.3.1` — the spec rulings this designs against. **Reframe under the inversion filed
  `design/arch/fixmes/0439-spec-reframe-type-field-canonical-bare-alias.md` (`target: /spec`)**
  — canonical `Type.field` / bare alias; §7.3.1 substance unchanged.
- `design/arch/fixmes/0438-repl-list-exports-dotted-accessor-visibility-normative.md`
  (`target: /repl`, **updated for the inverted model**) — `/list`/`/exports` display the
  canonical qualified `Type.field`; bare alias not separately listed.
- `crates/cranelisp-typecheck/src/adt.rs` — `synthesise_one_accessor` (`:449`); **inverted
  model (§1.6):** real `Def` moves to the canonical key `qualified_key` (`Box.v`, built at
  `:582`), bare `accessor_name` becomes the `Import` alias (the as-built `:582-626` registers
  these reversed); **delete** `remint_first_accessor_under_qualified_key` (`:729`) and the
  poison-arm `Def`-minting (`:657-672` collapses into bare-alias `Ambiguous` handling);
  bare-name `Ambiguous` sentinel (`:674-681`); `committed_accessor_kind` (`:677`) — unchanged,
  now recognizes the canonical `Box.v` `Def`; `CommittedAccessor` enum (`:658`),
  `state.accessor_owning_types` / `synthesised_accessor_names` (kept for the bare-alias
  ambiguity diagnostic).
- `crates/cranelisp-types/src/module.rs` — `public_symbols` (`:639`), `is_public` (`:1220-1231`,
  `Import`/`Def`/`Ambiguous` arms), `ModuleEntry::Import` (`:910`) visibility field. Under
  inversion the canonical `Def` is uniformly Public (surfaces in `public_symbols()`); the bare
  alias is the not-separately-listed one (§1.6.5).
- `crates/cranelisp-types/src/resolve.rs:578` — the §8.7.3 cross-module visibility filter
  (`entry.is_public() || in_subtree(from_module, home)`). Under inversion the canonical
  `Box.v` is uniformly Public, so cross-module `m/Box.v` resolves in every case — the
  no-cliff property (§1.6.3); the as-built's "poison re-mint must be Public" worry disappears.
- `src/imports.rs` — `collect_glob` (`:178`), `collect_specific` (`:206`), `collect_member_glob`
  (`:245`) — the glob/re-export consumers of `public_symbols()`. Under inversion they see exactly
  one canonical accessor per field (no redundant double-listing, §1.6.5).
- `src/agent/harvest.rs:140` — the agent-harvest `public_symbols()` consumer (sees the canonical
  `Box.v`).
- `crates/cranelisp-typecheck/src/traits/impl_check.rs` — `register_trait_impl` (`:18`),
  `check_impl_methods_present` (`:196`), `check_impl_method` (`:227`).
- `crates/cranelisp-typecheck/src/checker.rs` — `concrete_type_for_impl_target` (`:1023`),
  `type_def_view_of` (`:91`), `probe_module_entry_owned` (`:1277`).
- `crates/cranelisp-types/src/check.rs` — `Scheme`, `FieldInfo` (`:253`), `TypeDefInfo`
  (`:195`), the ctor→Def migration map (`:238`).
- `sprints/SPRINT.md §"3. FIXME 0365"` + §"Thread C 0365" — the ruling + zero-baseline
  disposition.
