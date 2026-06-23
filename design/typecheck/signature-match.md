# Type-signature match predicate — design intent (Pillar 3 importable-symbol search)

Owner: `/design` (typecheck triad). Subordinate to `design/typecheck/typecheck.md` §9.
Sprint 90 — the agentic-REPL fluency phase, **Pillar 3** (importable-symbol search by
name and/or type signature). **Design-only this sprint** (R1 — Pillar 3 implementation
is gated on the FIXME 0432 root fix, `monomorphisation.md §9`; this doc pins the
match-predicate interface the `int` indexer will call).

Contract this designs against:

- `design/arch/repl-embedded-agent.md §11.4` (R6) — **the binding interface ruling.**
  *Interface is `/arch`'s; the algorithm is `/typecheck`'s.* MVP = **name-fragment
  match + exact-structural-shape match** (alpha-renaming of type vars, **NO unifier
  call**). Hoogle-style subsumption/unification is a `/typecheck`-owned **follow-up**,
  NOT this sprint. The query-pattern *syntax* (holes/wildcards) is a **`/spec`
  consult**, flagged only if Hoogle is later pursued — **not designed here**.
- `design/arch/repl-embedded-agent.md §11.2` (R3) — the one shared DTO
  `{ name, signature, docstring, module }`; **`signature` is the existing
  `cranelisp-types` `Scheme`** (the index stores each symbol's type as its scheme; no
  new boundary type, §11.8 confirms zero `cranelisp-types`/public-API impact).
- `crates/cranelisp-types/src/types.rs` — `Type`, `Scheme`, `TypeId`,
  `collect_var_ids_ordered` (the canonical first-occurrence var ordering this design
  reuses for alpha-canonicalisation).
- `design/arch/principles/02-narrow-interfaces.md` (the predicate is one pure free
  function), `06-complexity-has-a-budget.md` (exact-shape first; no unifier),
  `07-single-source-of-truth.md` (reuse `collect_var_ids_ordered`, not a parallel
  walk).

This doc pins the *design intent* and the *function signature* the `int` indexer
calls. It authors no code (design only). **The algorithm is deliberately the simplest
thing that clears the acceptance criterion** — a structural equality up to consistent
renaming of type variables. No unification, no occurs-check, no ranking.

---

## 1. What "match" means at MVP — two independent predicates

Pillar 3 search is **name-fragment AND/OR type-signature**. Two independent match
predicates, combined by the `int` indexer (an OR over a candidate set, or an AND when
both a name fragment and a type query are supplied):

1. **Name-fragment match** — a substring/fragment test over the symbol's bare name.
   This is an ordinary string predicate; it is **not typecheck's** to design (it lives
   in the `int` indexer over the DTO's `name` field). Named here only to scope it OUT.
2. **Type-signature match** — the predicate this doc designs: given a **query
   signature** and an **indexed symbol's signature**, decide whether they are
   **structurally equal up to alpha-renaming of type variables**. This is the
   `/typecheck`-owned algorithm.

The acceptance criterion (`sprints/SPRINT.md` §"Acceptance (implementation)"): *search
by exact-shape type signature → name + sig + originating module*. Exact-structural-shape
clears it. Subsumption (`(Fn [Int] ?)` matching `(Fn [Int] Bool)`) is the §3 follow-up.

## 2. Exact-structural-shape — the precise definition

Two type signatures **match** iff they are **alpha-equivalent**: identical in
structure with a **consistent bijective renaming** of their type variables. Precisely,
over the `Type` algebra (`crates/cranelisp-types/src/types.rs`):

- **Concrete heads must be identical.** `Int`/`Bool`/`String`/`Float` match only the
  same primitive. `Type::Fn(p, r)` matches `Type::Fn(p', r')` iff arities match and
  each positional pair matches. `Type::ADT(fqtn, args)` matches `Type::ADT(fqtn',
  args')` iff `fqtn == fqtn'` (**fully-qualified** type name — module + name; same
  ADT) and `args` match positionally. `Type::TyConApp(head, args)` — see §2.3 (HKT).
- **Type variables match positionally under a consistent renaming.** A `Type::Var(a)`
  in the query matches a `Type::Var(b)` in the candidate iff the renaming established
  so far is consistent: the **first** time query-var `a` is seen it binds to
  candidate-var `b`; every **subsequent** occurrence of `a` must align with the same
  `b`, AND no other query var may bind to that same `b` (**bijective** — a one-to-one
  renaming, so `(Fn [a a] a)` does NOT match `(Fn [a b] a)`, and vice-versa). This is
  exactly alpha-equivalence: the variable *names* (TypeIds) are irrelevant; the
  **pattern of sharing** is what must coincide.
- **Arity is structural.** Different parameter counts, different ADT arg counts,
  different `Fn` arities never match. (Auto-curry is a call-site concern, not a
  signature-identity concern; the stored scheme is the declared shape.)

**Worked equivalences (MATCH):**

| Query | Candidate | Match? |
|---|---|---|
| `(Fn [a] a)` | `(Fn [b] b)` | ✅ (same sharing pattern: param-var == ret-var) |
| `(Fn [a b] a)` | `(Fn [x y] x)` | ✅ |
| `(Fn [Int a] (Vec a))` | `(Fn [Int b] (Vec b))` | ✅ |
| `(Fn [a] (Option a))` | `(Fn [z] (Option z))` | ✅ |

**Worked non-equivalences (NO MATCH):**

| Query | Candidate | Why |
|---|---|---|
| `(Fn [a] a)` | `(Fn [a b] a)` | arity differs (1 vs 2 params) |
| `(Fn [a a] a)` | `(Fn [a b] a)` | sharing pattern differs (params shared vs distinct) |
| `(Fn [Int] Int)` | `(Fn [a] a)` | concrete head ≠ variable (exact-shape, NOT subsumption) |
| `(Fn [a] (Option a))` | `(Fn [a] (Vec a))` | ADT heads differ (`Option` ≠ `Vec`) |
| `(Fn [a] (Box a))` from module `m` | `(Fn [a] (Box a))`, `Box` from `n` | `FQTypeName` differs (different ADT) |

The last row is the load-bearing **FQ** discipline: `Type::ADT` carries an
`FQTypeName` (module + name), so two same-named-but-different-module ADTs are
**distinct** and must not match (mirrors the mono mangler's FQ grounding, and
`adt.rs`'s nominal resolution). The MVP predicate compares the full `FQTypeName`.

### 2.1 Canonicalisation — reuse `collect_var_ids_ordered`

Rather than thread a growing bijection map through a structural walk, the cleanest
implementation (the design *recommends*, /dev decides) is **canonicalise then compare
for structural equality**:

1. Walk each signature's `Type` collecting its `Type::Var` TypeIds **in order of
   first occurrence** — this is exactly `cranelisp_types::collect_var_ids_ordered`
   (`types.rs:251`, already used by `type_var_names` for display; Principle 7 — reuse,
   do not fork the walk).
2. Build a renaming `{ original_id → canonical_index }` from that order (first-seen var
   → 0, second distinct var → 1, …).
3. Apply the renaming to produce a **canonical `Type`** (vars renumbered to
   `0,1,2,…` by first occurrence).
4. Two signatures match iff their canonical `Type`s are **`==`** (the derived
   `PartialEq` on `Type` — `types.rs:13`).

Canonicalisation makes alpha-equivalence a **plain `==`** and is **bijective by
construction** (the first-occurrence numbering is injective, and equal canonical forms
force the same sharing pattern). It is also the obvious key for an *index bucket* (§4)
if the indexer wants to pre-group by canonical shape. This is strictly an
implementation convenience; the *contract* is alpha-equivalence (§2).

### 2.2 Scope: the function part of the scheme, not the constraints

The signature compared is the scheme's **`ty` (the `Type`)** — the function shape.
**MVP ignores `Scheme.constraints`** (the trait bounds): an exact-shape search for
`(Fn [a] a)` matches `id` whether or not `a` is `Num`-constrained. Rationale: the
query a human/agent types is a *shape* (`(Fn [Int] Bool)`), and constraints are not
part of the surface syntax the agent has to express. Constraint-aware matching (find
`(Fn [a] a) where a: Num`) is a precision upgrade folded into the §3 subsumption
follow-up, not an MVP gate. The predicate takes the `Type`; the indexer reads it off
`Scheme.ty`. (`type_vars` is likewise irrelevant under canonicalisation — the free
vars of `ty` ARE the schematic vars for a stored top-level scheme.)

### 2.3 HKT / `TyConApp` — match by structure, head-var renamed like any var

`Type::TyConApp(head: TypeId, args)` (HKT, `hkt.md`) is handled uniformly: the `head`
TypeId is a type **variable** (a type-constructor variable), so it participates in the
**same** first-occurrence renaming as any `Type::Var` — two `TyConApp`s match iff their
heads align under the consistent renaming AND their args match positionally. A
`TyConApp` never matches a concrete `ADT` head at MVP (exact shape: a constructor
*variable* `f a` is a different shape from a concrete `(Option a)`; unifying them is
subsumption, §3). This is a low-frequency case for an MVP library search; it is defined
for completeness and costs nothing extra under the canonicalise-then-`==` model
(`collect_var_ids_ordered` already visits `TyConApp` args; the head id is folded into
the same numbering — a one-line extension /dev notes, since the existing
`collect_var_ids_ordered` does NOT currently number the `TyConApp` head, only its args;
the canonicalisation walk must include the head to keep HKT alpha-equivalence correct).

## 3. The match predicate interface — the function signature `int` calls

The indexer (`int`, Pillar 3) holds an index of `{ name, signature: Scheme, docstring,
module }` records. For a type-signature query it calls a **pure typecheck free
function**:

```rust
// crates/cranelisp-typecheck/src/<module>.rs  (e.g. signature_match.rs)
// Sprint 90 — exact-structural-shape match (alpha-equivalence). NO unifier.
//
// Returns true iff `query` and `candidate` are alpha-equivalent: structurally
// identical up to a consistent bijective renaming of their type variables
// (see design/typecheck/signature-match.md §2). Pure; no state, no &mut, no
// CheckState — it reads only the two Types.
pub fn signature_matches_exact(query: &Type, candidate: &Type) -> bool;
```

Design commitments on this signature:

- **Takes `&Type`, not `&Scheme`.** The shape lives in `Scheme.ty` (§2.2). The indexer
  passes `&record.signature.ty` and `&query.ty`. Keeping the predicate on `Type` keeps
  it a pure structural function with no constraint/`type_vars` coupling — the narrowest
  interface (Principle 2). (If a future constraint-aware variant is wanted, it is a
  *new* `signature_matches_exact_with_constraints(&Scheme, &Scheme)` overload, not a
  widening of this one.)
- **Pure, no `CheckState`, no `&mut`, no `TypeCheckEnv`.** Exact-shape match needs no
  inference context — it is a structural comparison of two finished types. This is the
  **whole point** of the MVP choice over subsumption: subsumption needs the unifier
  (which needs fresh-var minting + a `Subst`), and that pulls `CheckState`/`&mut` in.
  Exact-shape is context-free → trivially callable from `int` with zero new
  cross-crate state coupling (Principle 5 — testability is structural; the predicate is
  unit-testable in isolation with two hand-built `Type`s, no fixture).
- **Where it lives.** A new small typecheck module (`signature_match.rs`) or an arm of
  an existing utility module — /dev's placement call. It is a *typecheck* function (it
  encodes the type-equivalence semantics the crate owns), exported `pub` for `int` to
  call. **Public-API note:** this is the one Pillar-3 item that *could* touch
  `cranelisp-typecheck/public-api.txt` — a single new `pub fn` line. Per the
  baseline-diff discipline (`design/arch/CLAUDE.md`), /dev regenerates the baseline in
  the implementing change-set. (`/arch §11.8` states zero public-API impact treating
  the predicate as int-private over the scheme; if /dev instead exposes it from
  typecheck, that is one additive `pub fn` line — confirm with `/arch` whether the
  predicate is exported from typecheck or inlined int-side. **Flagged for `/arch`** —
  see §6.)

### 3.1 Optional: a canonical-form helper for index bucketing

If the indexer wants to bucket the index by shape (so a type query is an O(1) bucket
lookup rather than an O(n) scan), typecheck can additionally expose:

```rust
// Renumber a Type's vars to 0,1,2,… by first occurrence (design §2.1). Two
// alpha-equivalent types produce `==` canonical forms. Suitable as an index key.
pub fn canonical_signature_shape(ty: &Type) -> Type;
```

`signature_matches_exact(a, b)` is then **definitionally** `canonical_signature_shape(a)
== canonical_signature_shape(b)`. This is an optional performance affordance for the
indexer; the MVP only *requires* the boolean predicate. Whether to ship the helper too
is /dev + `/design (int)`'s call based on the index's access pattern (a session-scoped
library index is small; a linear scan is likely fine for MVP — Principle 6).

## 4. Future follow-up — Hoogle-style subsumption (NOT this sprint)

Recorded explicitly per R6 as a **`/typecheck`-owned follow-up**, deferred:

- **Subsumption/unification match** — a query `(Fn [Int] ?)` matching a candidate
  `(Fn [Int] Bool)`, or a query `(Fn [a] a)` matching `id`/`negate`/any
  same-shape-or-more-specific. This needs the **real unifier** (fresh-var instantiation
  of both sides + a `Subst` + occurs-check) and a **ranking model** (exact > more
  general > unifiable-with-substitution), which is materially more surface than the MVP
  and pulls `CheckState` into the predicate. It is a **precision upgrade, not an MVP
  gate** (§11.4).
- **Query-pattern syntax (holes/wildcards)** — the `?` in `(Fn [Int] ?)`, or named
  holes — is a **language-surface question** (`/spec` consult, `/arch §11.4` flags it).
  **NOT designed here, NOT a `/typecheck` call.** Until Hoogle is pursued, the MVP query
  is a fully-formed type expression (no holes) compared by exact shape. When/if Hoogle
  is pursued, `/spec` owns whether/how holes enter the type-query surface, and
  `/typecheck` owns the subsumption algorithm against whatever surface `/spec` settles.

The MVP predicate (§3) is the floor; the subsumption predicate is a *sibling* free
function added later, not a modification of `signature_matches_exact` (Principle 8 — no
interim shape that the follow-up has to unwind).

## 5. Test seams (Phase-5 authoring by /qa + /dev)

Unit tests (typecheck, in-crate — the predicate is pure, no fixture needed):

- **Positive alpha-equivalence** — each §2 MATCH row: `(Fn [a] a)` ~ `(Fn [b] b)`;
  `(Fn [Int a] (Vec a))` ~ same with renamed var; `(Fn [a b] a)` ~ `(Fn [x y] x)`.
- **Negative (the load-bearing +neg coverage)** — each §2 NO-MATCH row: arity differs;
  **sharing pattern differs** (`(Fn [a a] a)` ✗ `(Fn [a b] a)` — the bijectivity guard,
  the subtle one); concrete ≠ var (the exact-shape-NOT-subsumption boundary); ADT head
  differs; **FQ module differs** (same-named ADT from two modules ✗).
- **Canonicalisation** (if §3.1 helper ships) — `canonical_signature_shape` produces
  `==` for an alpha-equivalent pair and `!=` for a sharing-pattern-different pair;
  idempotent (canon of canon == canon).
- **HKT** (§2.3) — two `TyConApp` shapes match under head renaming; a `TyConApp` head
  does NOT match a concrete `ADT` head.

The predicate's purity makes these table-driven unit tests over hand-built `Type`s —
no `check_forms`, no `TestFixture`. (The end-to-end "agent searches importable symbols
by exact-shape signature" path is `/qa`'s integration test and is **gated on Pillar 3
implementation**, which is gated on the 0432 fix — not this sprint unless pulled
forward.)

## 6. Flags / open items for `/arch` (interface ownership)

- **Predicate export site (confirm).** `/arch §11.8` treats Pillar 3's type matching as
  int-private over the stored scheme (zero public-API). This design places the
  *algorithm* in typecheck (it is type-equivalence semantics the crate owns) as a
  `pub fn` over `&Type`. If exported from typecheck, that is **one additive
  `cranelisp-typecheck/public-api.txt` line** (a new `pub fn`), which /dev regenerates
  per the baseline-diff discipline. **Confirm with `/arch`:** is the exact-shape
  predicate (a) exported from `cranelisp-typecheck` for `int` to call (one new pub-api
  line — the §3 signature), or (b) inlined int-side over `Type` (zero typecheck
  pub-api, but the type-equivalence logic lives outside the crate that owns type
  semantics — a Principle-7/17 tension)? This design **recommends (a)** — type
  equivalence is typecheck's semantics (module-locality of typecheck logic, Principle
  17) — and notes the one-line baseline cost. `/arch`'s call.
- **No `cranelisp-types` change either way** — the predicate consumes the existing
  `Type`/`Scheme`; no new boundary type (R3/§11.8 hold).

## 7. Cross-references

- `design/arch/repl-embedded-agent.md §11.2/§11.4` (R3/R6) — the DTO + match-semantics
  ruling this doc implements.
- `design/typecheck/monomorphisation.md §9` — the FIXME 0432 root fix; Pillar 3
  implementation (this predicate's consumer) is gated on it (R1/R2).
- `design/typecheck/hkt.md` — `Type::TyConApp` / HKT (§2.3 head-renaming).
- `crates/cranelisp-types/src/types.rs` — `Type`, `Scheme`, `TypeId`,
  `collect_var_ids_ordered` (`:251`, reused for canonicalisation), the derived
  `PartialEq` on `Type`.
- `sprints/SPRINT.md` §"Pillar 3" + §"Architecture review" Q5/R6 — scope.
