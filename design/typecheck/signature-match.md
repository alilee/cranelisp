# Type-signature match predicates

Owner: `design` narrow-deployed to `cranelisp-typecheck`. Subordinate to
[`typecheck.md`](typecheck.md) §2. Reader: anyone changing how `/search`
matches a query type against indexed symbols.

`design/arch/repl-embedded-agent.md` owns the interface and boundary: §11.4
the match semantics and §11.8 the export ruling. Its §11.2 makes the index a
derived index separate from the context harvest; the index's signatures use
the existing `cranelisp-types` `Scheme`, and no shared harvest/index DTO or
new boundary type is required. This document owns the algorithm.

| Subject | Authority |
|---|---|
| `/search` behaviour | `repl/spec/17a-agent-language-awareness.md` |
| Index worker and match tiers | `design/int/agent.md` §25; caller `src/session_v4/index_worker.rs::search_by_scheme` |
| `Type`, `Scheme`, `collect_var_ids_ordered` | `crates/cranelisp-types/src/types.rs` |
| `Type::TyConApp` | [`hkt.md`](hkt.md) |

Section numbers are cited from source, tests and sibling designs.

## 1. Scope

- Name matching is an int-side string predicate over the symbol name; it is
  not typecheck's.
- Scheme matching uses two independent typecheck predicates: exact
  (alpha-equivalence, §2–§3) and partial (structural containment, §4). The
  indexer calls them per candidate and records the tier; exact wins.
- Neither predicate uses a unifier. Subsumption is the deferred upgrade in §5.

## 2. Exact — alpha-equivalence

Two types match iff they are structurally identical under a consistent
**bijective** renaming of their type variables:

- **Concrete heads must be identical.** Primitives match only themselves.
  `Fn` requires equal arity and positional matches. `ADT` requires equal
  `FQTypeName` (module and name) and positional argument matches.
- **Variables match by sharing pattern.** A query variable binds to the first
  candidate variable it meets. Every later occurrence must meet the same
  variable, and no other query variable may bind to it. So `(Fn [a a] a)` does
  not match `(Fn [a b] a)`, in either direction.
- **Arity is structural.** Auto-curry is a call-site concern, not part of
  signature identity.

| Query | Candidate | Match |
|---|---|---|
| `(Fn [a] a)` | `(Fn [b] b)` | yes |
| `(Fn [a b] a)` | `(Fn [x y] x)` | yes |
| `(Fn [Int a] (Vec a))` | `(Fn [Int b] (Vec b))` | yes |
| `(Fn [a] a)` | `(Fn [a b] a)` | no: arity |
| `(Fn [a a] a)` | `(Fn [a b] a)` | no: sharing pattern |
| `(Fn [Int] Int)` | `(Fn [a] a)` | no: concrete is not a variable (not subsumption) |
| `(Fn [a] (Option a))` | `(Fn [a] (Vec a))` | no: ADT head |
| `(Fn [a] (Box a))`, `Box` from `m` | same, `Box` from `n` | no: `FQTypeName` differs |

The last row is load-bearing: same-named types from different modules are
distinct types and must never match.

### 2.1 Canonicalise, then compare

1. Collect the type's variable ids in first-occurrence order with
   `cranelisp_types::collect_var_ids_ordered`.
2. Renumber them `0, 1, 2, …` in that order, producing a canonical `Type`.
3. Compare the canonical forms with the derived `PartialEq` on `Type`.

First-occurrence numbering is injective, so equal canonical forms force the
same sharing pattern. Bijectivity therefore holds by construction, and
canonicalisation is idempotent. Reusing the shared walk rather than a local
copy keeps one definition of variable order, the same one the display code
uses.

### 2.2 The compared type is `Scheme.ty`

The predicates compare the scheme's `ty` and ignore `constraints` and
`type_vars`. A query is a shape. Trait bounds are not part of what a user
writes, and a stored top-level scheme's free variables are its schematic
variables. Constraint-aware matching belongs to the §5 upgrade.

### 2.3 Higher-kinded heads

A `TyConApp` head is a type-constructor variable. It joins the same
first-occurrence numbering as every other variable, so two `TyConApp`s match
iff their heads align under the renaming and their arguments match. A
`TyConApp` never matches a concrete `ADT` head. Unifying a constructor variable
with a concrete constructor is subsumption. `collect_var_ids_ordered` numbers
the head (FIXME 0437), and the renaming applies to it.

## 3. Interface

```rust
pub fn signature_matches_exact(query: &Type, candidate: &Type) -> bool;
```

- **It takes `&Type`, not `&Scheme`.** Taking only the type keeps the
  predicate structural, with no coupling to constraints or `type_vars`. A
  constraint-aware form would be a new sibling, not a widening.
- **It is pure.** It needs no `CheckState`, no `TypeCheckEnv` and no `&mut`.
  This is what keeps the predicates callable from int without new state
  coupling, and why a unifier-based match (§5) is a separate function.
- **It lives in** `crates/cranelisp-typecheck/src/signature_match.rs` and is
  re-exported at the crate root.

### 3.1 Canonical-shape helper

`canonical_signature_shape(&Type) -> Type` is the §2.1 canonicaliser. It is
`pub(crate)`. The indexer scans its small session-scoped index linearly, so it
needs no bucket key. Exporting the helper as a bucket key would be an additive
public-API change through the root user gate. It would be triggered only by a
measured need for bucketed lookup.

## 4. Partial — structural containment

### 4.1 Meaning

`signature_matches_partial(query, candidate)` holds iff some subtree of
`candidate`, the whole tree included, is alpha-equivalent (§2) to `query`:

- `(Vec Int)` matches `(Fn [(Vec Int)] Bool)`, where it is the parameter
  subtree;
- `Int` matches any candidate that mentions `Int`;
- `(Fn [a a] a)` does not match `(Fn [a b] a)`, because the sharing-pattern
  guard applies per subtree.

A query variable never matches a concrete subtree. Query `a` against
`(Fn [Int] Bool)` would be subsumption (§5), not containment.

### 4.2 The containment walk

```
signature_matches_partial(q, c) := ∃ subtree t of c . signature_matches_exact(q, t)
```

Subtrees are `c` itself plus, recursively:

- each parameter and the result of `Fn`;
- each argument of `ADT` and `TyConApp`, whose head is part of the node and
  not a separate subtree.

Primitives and `Var` have no children. The query is canonicalised once. Each
visited subtree is canonicalised independently, because a sub-shape's
alpha-equivalence depends only on the sharing pattern within it. No second
equivalence judgment exists: containment reuses §2.

### 4.3 `_exact ⟹ _partial`

The whole candidate is one of its subtrees, so every exact match is a partial
match; the converse does not hold. Both predicates are needed. `_partial`
alone cannot express "exactly this shape". The indexer records an exact hit in
the higher tier.

### 4.4 Interface

```rust
pub fn signature_matches_partial(query: &Type, candidate: &Type) -> bool;
```

The §3 commitments carry over unchanged: it takes `&Type`, is pure and is
defined in the same module.

### 4.5 No query wildcard

A containment query is a complete type expression and has no hole to
instantiate. The predicates therefore add no query surface and depend on no
`spec` decision. A hole token arises only with §5.

## 5. Deferred — subsumption with holes and ranking

This is a typecheck-owned upgrade. It is listed as unbuilt in
`design/arch/repl-embedded-agent.md` §9 and is not a requirement until `spec`
records one. Its shape is:

- **A third sibling predicate.** It would not widen `_exact` or `_partial`.
- **Matches that need the unifier.** For example, `(Fn [Int] ?)` would match
  `(Fn [Int] Bool)`, and `(Fn [a] a)` would match more specific shapes. These
  need fresh instantiation, a substitution and an occurs check, so the
  predicate would need inference state.
- **Ranking.** Results would rank exact, then more general, then unifiable.
- **Constraint-aware matching**, as described in §2.2.
- **Owner split for the query syntax.** Whether and how a hole token enters
  queries is a `spec` question first. Typecheck designs the algorithm against
  whatever surface `spec` settles.

## 6. Evidence

Both predicates are pure, so the unit tests are table-driven over hand-built
`Type`s in `signature_match.rs`, with no fixture:

- **`_exact`:** the §2 matching and non-matching rows, bijectivity in both
  directions, HKT head renaming and idempotent canonicalisation;
- **`_partial`:** positive containment, `_exact ⟹ _partial`, and the
  non-matching rows, including a lone query variable against a concrete
  subtree.

End-to-end `/search` evidence is allocated by
`tests/plan/agent-testing-strategy.md`.

## 7. Export

Both predicates export from `cranelisp-typecheck` and appear in its
`public-api.txt` (`design/arch/repl-embedded-agent.md` §11.8). Type
equivalence is typecheck's semantics. An int-side copy would silently diverge
when a `Type` variant is added. Neither predicate changes `cranelisp-types`.
