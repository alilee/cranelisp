---
number: 0624
target: /design
filed_by: /repl
filed_at: 2026-07-16
sprint_filed: 110
sprint: S111
refers_to: crates/cranelisp-typecheck HKT impl-target validation (the §7.2 "primitive is not a type constructor" rejection) — the bare-constructor-var-in-method-type variant escapes it; sibling coverage-matrix hole for /qa
status: open
---

# HKT trait impl'd on a primitive leaks `undefined function` when the method
# type uses the constructor var BARE (`:a`) instead of applied (`(f a)`)

## Summary (self-documenting-REPL violation)

An ill-formed program — a higher-kinded `deftrait` implemented on a **primitive**
type — is **silently accepted** and then leaks an **opaque backend codegen
error** at the first use, instead of being rejected check-side with the clean
§7.2 "not a type constructor" diagnostic. This violates the self-documenting-REPL
principle ("no valid construct produces an opaque error"; an invalid one must
produce an actionable message, not a backend leak).

Found while assessing the S110 R16/R17 error-quality lift (Phase-6 /repl). It is
**pre-existing, NOT an S110 regression** — the R16/R17 §3.11 lift is correct for
the well-formed `self`-spelled return-poly trait (see "Not this" below).

## Minimal repro (primitives-only prelude)

```
(deftrait (Zeroable a) (zed [] :a))     ; (Name var) ⇒ higher-kinded trait (grammar §7 L12; `a` is a con_var, kind *->*)
(impl Zeroable Int (defn zed [] 0))     ; SILENTLY ACCEPTED — prints `impl user/Zeroable for user/Int`
:Int (zed)                              ; → Error: codegen error at 6..9: codegen failed for /: codegen error at 6..9: undefined function: zed
```

`(zed)` (unannotated) leaks the identical `undefined function: zed` codegen
error, and so does `(add-i64 (zed) 5)` (argument-context) — the leak is
independent of how the use tries to pin the type.

A companion type-display defect on the same path: when the constructor var is used
BARE in **argument** position, the impl is likewise wrongly accepted and the
result type displays as the unresolved var —
`(deftrait (Container a) (unwrap [:a x] :a))` + `(impl Container Int ...)` +
`(unwrap 7)` prints `:a 7` instead of `:primitives/Int 7`.

## Why it's a coverage hole (the load-bearing detail)

`tests/spec_07_traits.rs::hkt_impl_on_primitive_type_is_rejected_neg` already
guards HKT-impl-on-primitive rejection — but only for the **applied**
constructor-var shape (`Functor` with `:(f a) x` and `(f b)` return). That test
is GREEN: the rejection fires when the con_var appears APPLIED (`(f a)`). It does
NOT fire when the con_var appears **bare** in a method's type position (`:a` as a
return or argument type). So the §7.2 "primitive MUST be rejected as an HKT impl
target" gate has a variant hole:

| con_var use in method sig | impl-on-primitive | disposition |
|---|---|---|
| applied — `:(f a) x`, ret `(f b)` | `(impl Functor Int)` | REJECTED cleanly (covered, GREEN) |
| bare — `zed [] :a` (ret) | `(impl Zeroable Int)` | silently accepted → codegen leak (THIS) |
| bare — `unwrap [:a x] :a` (arg+ret) | `(impl Container Int)` | accepted → runs, but result type shows `:a` (THIS) |

This is the standing "coverage by definition variants" lens (tests/CLAUDE.md):
one operation (HKT impl-target validation) that must behave uniformly across a
variant family, where the covered variant works and the uncovered variant grew a
divergent path. A variant × {applied, bare} matrix for the §7.2 rejection would
have caught it.

## Not this (what is correct and in-scope-verified)

The S110 R16/R17 lift is CORRECT for the well-formed `*`-kind return-poly trait —
the `self` spelling, which is the language's actual way to write "returns the
implementing type" for a `*`-kind trait (spec §7.1.1; there is no `*`-kind
*parametric* trait syntax — `(deftrait Name var ...)` is unavoidably HKT):

```
(deftrait Zeroable (zed [] self))
(impl Zeroable Int   (defn zed [] 0))
(impl Zeroable Float (defn zed [] 0.0))
(zed)      ; → clean §3.11: "ambiguous type: the return-type-polymorphic call to `zed`
           ;    selects no impl … add a `:Type` annotation to disambiguate (spec §3.11)"
:Int (zed) ; → :primitives/Int 0
```

The `:a` fixture in the repro is genuinely ill-formed (HKT trait on a primitive).
The defect is the DIAGNOSTIC QUALITY on that ill-formed input, not that it is
rejected — it should be rejected with the §7.2 message, not an opaque backend
`undefined function` leak.

## Suggested disposition (S111 Phase-1 input)

Route the bare-constructor-var method-type shape through the same §7.2
impl-target validation as the applied shape, so `(impl <HKT> <primitive>)` is
rejected check-side with "not a type constructor" regardless of how the con_var
appears in the method signatures. `/qa` extends the rejection matrix with the
applied/bare variant rows. Ideal target diagnostic: name the higher-kinded trait
and point at `self` for `*`-kind intent.

`class` for the eventual repro: `check-gate-leak` (a source fault typecheck must
decide leaks past the check boundary and surfaces as a backend codegen error) —
sibling of the S108 0571 D1 generic-value leak.
