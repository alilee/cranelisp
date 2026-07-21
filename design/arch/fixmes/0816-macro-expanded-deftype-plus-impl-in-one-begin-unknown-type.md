---
number: 0816
target: /qa
filed_by: /stdlib
filed_at: 2026-07-21
sprint_filed: 115
refers_to: stdlib/derive.cl:46 (derive-Display), :33 (derive-Eq);
  spec/09-macros.md §9.3 (expansion staging); spec/07-traits.md §7.2 (impl);
  spec/08-modules.md §8.2 (definition registration order)
status: open
---

# A macro that expands to `(begin (deftype T …) (impl Trait T …))` fails with `unknown type T` — and the SAME shape succeeds for a different trait

## Issue

`derive-Display`'s documented and only usage form is
`(derive-Display (deftype T …))`, which expands to
`(begin (deftype T …) (impl Display T (defn show …)))`. At the REPL the `impl`
does not see the `deftype` that precedes it in its own `begin`.

Probed at HEAD (2026-07-21, `target/release/cranelisp`, **pristine dir**: fresh
directory, no persisted `user.cl`, no `.cranelisp-cache`,
`CRANELISP_LIB=/home/alilee/cranelisp/stdlib`).

**Fails — type defined by the expansion itself:**

```
(import [derive [derive-Display]])
(import [text.display [Display show]])
(derive-Display (deftype T A B C))
⇒ Error: type error at 0..34: unknown type `T` (from module `user`)
     in expansion of `(derive-Display (deftype T A B C))`
(show B)
⇒ Error: type error at 6..7: undefined variable: B
```

**Succeeds — same expansion, but `T` already exists from a previous turn:**

```
(import [derive [derive-Display]])
(import [text.display [Display show]])
(deftype T A B C)
(derive-Display (deftype T A B C))
⇒ impl text.display/Display for user/T
(show B)
⇒ :primitives/String "B"
```

So the generated `impl` body is CORRECT; only the one-turn
define-then-implement sequencing fails.

## The inconsistency that makes this a defect rather than a documented limit

`derive-Eq` expands to the structurally identical
`(begin (deftype T …) (impl Eq T (defn = …)))` — and on the same input, in a
pristine dir, it does **not** report `unknown type`. It gets all the way to the
trait-conformance check:

```
(import [derive [derive-Eq]])
(import [compare.eq [Eq =]])
(derive-Eq (deftype T A B C))
⇒ Error: type error at 0..29: impl Eq for T: missing required method !=
```

`T` is plainly registered for the `Eq` impl and plainly not registered for the
`Display` impl, from the same `begin` shape in the same session state. Two
resolution paths through `impl` disagree about whether a same-`begin` `deftype`
is visible. That is the coverage-by-definition-variants shape: an operation
that must behave uniformly across a family (here: `impl` against any trait)
has each variant on its own codepath.

(The `missing required method !=` reject is a separate **stdlib-side** gap —
`derive-Eq` emits only `=`. `/stdlib` owns it and fixes it in 6b. It appears
here only because it is the evidence that `T` resolved.)

## Request

1. `/qa` attributes and routes — the question is which of the two `impl`
   resolution paths is right, i.e. whether a `deftype` earlier in the same
   expanded `begin` MUST be visible to a later `impl` in that `begin`.
   If the answer is "not required", then `derive-Display`'s documented usage is
   invalid and `/stdlib` changes the macro contract instead — but the two paths
   still must not disagree.
2. `/testing`: a trait × `begin`-position matrix — `{Display, Eq, Ord, Num,
   Default} × {type defined in the same begin, type pre-defined}` — with both
   polarities. Four one-liners, no fixtures. The uniformity is the thing under
   test, not any single cell.
3. If a user ruling is needed on `begin` staging semantics, `/spec` frames it.

## Context

Found by `/stdlib` during the S115 Phase-6a assessment, sweeping the 12 stdlib
modules that carry **no self-tests**. `derive.cl` is one of them; `plan-stdlib.md`
§26.4 records that its self-test home must be a downstream consumer module, which
was never built. See 0815 for the sibling `derive-Ord` finding from the same
sweep. `/stdlib` builds the missing consumer test module in 6b, which turns both
of these into standing guards.
