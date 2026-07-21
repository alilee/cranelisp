---
number: 0845
target: /spec
filed_by: /testing
filed_at: 2026-07-21
sprint_filed: 115
refers_to: spec/05-definitions.md §5.2.2, §5.2.3, §5.2.6, §5.1;
  spec/08-modules.md §8.5.2, §8.6.5;
  tests/deftype_duplicate_constructor.rs (3 REDs + 1 green control)
status: open
---

# Duplicate constructor names within ONE `deftype` have no spec rule — and the invariant they break is stated elsewhere

## What was found

At HEAD a `deftype` that declares the SAME constructor name twice is accepted in
silence — no error, no warning, no ambiguity diagnostic. Measured in a fresh cwd
with `CRANELISP_LIB` pinned:

```
(deftype Flag (Flag) (Flag))    ->  :user/Flag ; deftype
                                     ; match:
                                     ;  Flag Flag

(deftype Color Red Red Green)   ->  accepted; `(match c [Red 1 Red 2 Green 3])`
                                     returns 1, no unreachable-arm error

(deftype T (P [:Int a]) (P [:String b]))
                                ->  accepted; then `(P 1)` reports
                                    "type mismatch: expected primitives/String,
                                     got primitives/Int"
```

The last cell is the sharpest: the two arms contend for ONE module-level binder,
the LATER arm wins, and the variant declared FIRST becomes unconstructible and
unmatchable while still occupying a tag. Nothing said so at the definition.

## The spec does not state the rule

`spec/05-definitions.md` §5.2 nowhere requires constructor names within a
`deftype` to be distinct. What the spec does state:

- **§5.2.2** — "each introduces a **distinct** variant"; a constructor name is a
  **binder** minting a module-level callable. Suggestive, not a stated rule.
- **`spec/08-modules.md` §8.5.2** — `Type.Ctor` is the CANONICAL constructor
  name, and "`Type.member` always denotes exactly one thing … leaving the
  canonical `Type.member` a **unique referent in every case**." This IS a stated
  invariant, and the duplicate-arm forms break it (`T.P` denotes two distinct
  variants). But §8.5.2 reaches that conclusion by enumerating the possible
  same-name collisions as **accessor-vs-method only** — ctor-vs-ctor within one
  type was never considered.
- **§8.6.5** rules on the CROSS-type duplicate constructor (permitted;
  bare alias poisoned) and reasons explicitly that it is permitted because "each
  is a derived member of a **distinct** in-scope type". That reasoning does not
  extend to two arms of one type, and the alias-poison remedy is unavailable
  here: there is no second canonical form to disambiguate to.

So rejection is the only disposition consistent with §8.5.2 — but that is a
derivation, not a scribed rule, and the spec should not be left implying the
rule from an enumeration that predates the case.

## What is asked of `/spec`

1. **Scribe the rule** in §5.2.2 (reaching §5.2.3's enum spelling and §5.2.5's
   documented-nullary spelling): constructor names within a single `deftype`
   MUST be distinct; a duplicate is a compile-time error with the span on the
   second occurrence. Prior art for the shape: §5.1 already requires parameter
   names to be unique within a parameter list, and HEAD enforces it —
   `(defn f [x x] x)` => `parse error: duplicate parameter name 'x'`.
2. **Repair §8.5.2's supporting argument** — its "the only possible same-name
   collision is accessor-vs-method" enumeration is now incomplete; the
   ctor-vs-ctor case is prevented by (1), not by uppercase/lowercase separation.
3. **Rule on the sibling: duplicate FIELD names.** `(deftype T [:Int a :Int a])`
   is likewise accepted silently at HEAD, and it breaks the SAME §8.5.2
   invariant through §5.2.6 (two accessors keyed `T.a`). It is deliberately NOT
   pinned by a test yet — the rule is `/spec`'s to state first, and one FIXME
   should not spawn an unowned RED. If the ruling is symmetric, `/testing` will
   add the cell on request.

The three duplicate-constructor cells are pinned as failing-not-ignored REDs in
`tests/deftype_duplicate_constructor.rs`, with a green distinct-name control.
Per root `CLAUDE.md` the tests are the defect record and trigger (owner `/dev`);
this FIXME is the **spec gap** only.
