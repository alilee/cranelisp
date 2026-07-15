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

## Gotcha — bare names are ambiguous when two types share a field

The bare alias only works when **exactly one** in-scope type owns a field of that
name. The moment two types share a field name, the bare name has no single target:

```clojure
(deftype Box [:Int  v])
(deftype Cup [:Bool v])
```

Now bare `v` is ambiguous — does it mean `Box.v` or `Cup.v`? Cranelisp rejects the
bare use rather than guessing:

```
user> (v (Box 7))
error: ... v
```

The fix is always the same: **use the qualified `Type.field` form.** The canonical
accessors are never ambiguous — each names exactly one function — so they keep
working regardless of how many types share the field name:

```
user> (Box.v (Box 7))
:primitives/Int 7
user> (Cup.v (Cup true))
:primitives/Bool true
```

So the rule of thumb: bare `field` is the convenient form; `Type.field` is the form
that *always* works. If a bare field name ever stops resolving because another type
introduced the same field, qualify it.

(The field also stays reachable through `match` pattern destructuring, which is never
affected by bare-name contention.)

## See also

- [`spec/05-definitions.md §5.2.6`](../../spec/05-definitions.md) — generated
  accessors, total vs partial accessors, the bare-alias rule.
- [`spec/08-modules.md §8.5.2`](../../spec/08-modules.md) — dotted names; the
  canonical `Type.field` accessor as a member of the type.
