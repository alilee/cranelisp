# Field accessors

When you define a type with named fields, Cranelisp generates an **accessor
function** for each field — a function that pulls that field out of a value.

```clojure
(deftype Point [:Int x :Int y])
```

This gives you accessors for `x` and `y`. There are two ways to name an accessor,
and knowing which is which saves you a confusing error later.

## The canonical name is `Type.field`

The accessor's real, canonical name is the **qualified** `Type.field` form —
`Point.x`, `Point.y`. This is the name the language displays when it reports an
accessor, and it is **always** valid wherever the type is in scope:

```
user> (Point.x (Point 3 4))
:primitives/Int 3
```

`Point.x` has type `(Fn [Point] Int)`. Like any function it is first-class — you can
pass it as an argument or bind it to a variable. Constructors follow the same
canonical-vs-alias pattern — see [`constructors.md`](constructors.md).

## The bare name is a convenience alias

Writing the bare field name — `x` — is a convenience shorthand for the canonical
`Point.x`. It resolves to the same accessor, and it is the natural way to write code
when there is no ambiguity:

```
user> (x (Point 3 4))
:primitives/Int 3
```

So `(x p)` and `(Point.x p)` are the same call. Use the bare form for readability;
reach for the qualified form when you need it.

## When two types share a field name

Two product types may use the same field name:

```clojure
(deftype Box [:Int v])
(deftype Cup [:Int v])
```

Their canonical accessors `Box.v` and `Cup.v` are distinct functions, and each
always works. Bare `v` now has two candidates, and Cranelisp picks one from the
types at each use. Here the argument decides:

```
user> (v (Box 5))
:primitives/Int 5
user> (v (Cup 9))
:primitives/Int 9
```

When nothing at the use site narrows the choice to one candidate, the bare name is
ambiguous. Passing bare `v` as a value with no expected type is one example. The
compiler reports an ambiguity error that lists both canonical names, and never
picks one by declaration or import order. **Use the qualified `Type.field` form**
to say which one you mean:

```
user> (Box.v (Box 5))
:primitives/Int 5
user> (Cup.v (Cup 9))
:primitives/Int 9
```

The rule of thumb: bare `field` is the convenient form, and `Type.field` is the
form that *always* works. The precise selection rules are in the specification
(see below).

## Only product fields get accessors

Accessors come from **product** types. A product has a single constructor with the
same name as the type. You can write its fields at the `deftype` level, as every
example above does, or in an arm named after the type. Either spelling mints
`Pair.fst`, `Pair.snd` and their bare forms:

```clojure
(deftype (Pair a b) [:a fst :b snd])
; or, equivalently
(deftype (Pair a b) (Pair [:a fst :b snd]))
```

A constructor arm with **any other name** makes a sum type, even when it is the
only arm. The labels in a sum arm document its positional payloads and mint no
accessor, bare or dotted. A sum value might hold a different variant at runtime,
so a total accessor cannot exist. Extract the payload with `match`:

```
user> (deftype Trio (MkTrio [:primitives/Int t1 :primitives/Int t2]))
user> (match (MkTrio 1 2) [(MkTrio a _) a])
:primitives/Int 1
```

Here `t1` and `Trio.t1` are undefined names.

## See also

- [`spec/05-definitions.md §5.2.6`](../../spec/05-definitions.md) — generated
  accessors, the product-only rule, and bare names shared between types.
- [`spec/08-modules.md §8.6.5`](../../spec/08-modules.md) — how a bare name with
  several candidates is resolved at each use.
- [`spec/08-modules.md §8.5.2`](../../spec/08-modules.md) — dotted names; the
  canonical `Type.field` accessor as a member of the type.
