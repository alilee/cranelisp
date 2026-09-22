# Constructors

When you define a sum type, each variant introduces a **constructor** — the
function (or, for a variant with no fields, the value) you use to build that
variant. Just like field accessors, a constructor has two names, and knowing
which is which saves you a confusing error later.

```clojure
(deftype (Maybe a)
  None
  (Some [:a v]))
```

This gives you the constructors `Some` and `None`. There are two ways to name each
one.

## The canonical name is `Type.Ctor`

A constructor's real, canonical name is the **qualified** `Type.Ctor` form —
`Maybe.Some`, `Maybe.None`. This is the name the language displays when it reports
a constructed value, and it is **always** valid wherever the type is in scope:

```
user> (Maybe.Some 5)
:(user/Maybe primitives/Int) (Maybe.Some 5)
```

`Maybe.Some` has type `(Fn [a] (Maybe a))`. Like any function it is first-class —
you can pass it as an argument or bind it to a variable. A nullary constructor
(one with no fields) is a value rather than a function, and its canonical name
works the same way:

```
user> Maybe.None
:(user/Maybe a) Maybe.None
```

The dotted form is **not** a fallback reached only under contention — it is the
constructor's name, and it works exactly like the canonical `Type.field` accessor
(see [`field-accessors.md`](field-accessors.md)).

## The bare name is a convenience alias

Writing the bare constructor name — `Some` — is a convenience shorthand for the
canonical `Maybe.Some`. It resolves to the same constructor, and it is the natural
way to write code when there is no ambiguity:

```
user> (Some 5)
:(user/Maybe primitives/Int) (Maybe.Some 5)
```

So `(Some 5)` and `(Maybe.Some 5)` are the same call. Use the bare form for
readability; reach for the qualified form when you need it.

## When two types share a constructor name

Two in-scope types may each own a constructor with the same name. This is
**permitted** and is not a name collision:

```clojure
(deftype (Maybe a)  None (Some [:a v]))
(deftype (Choice a) None (Some [:a v]))
```

Each `Some` is a derived member of a distinct type, so each keeps its own
canonical name. `Maybe.Some` and `Choice.Some` name one constructor each and
always work. The bare spelling `Some` now has two candidates, and so does
`None`.

The compiler decides each bare use on its own, using only the type information
the program already gives it. It never picks by declaration order or import
order. A use that type information narrows to one candidate resolves to that
candidate. A use it cannot narrow is an **ambiguity error**, and the error lists
the canonical alternatives, such as `Maybe.Some` and `Choice.Some`.

### Constructing a value: qualify it

Suppose nothing around a bare construction fixes its type. For example, a bare
`(Some 7)` is used as the scrutinee of a `match` whose patterns are also bare.
That construction is ambiguous, because `7` fits either type. Write the
constructor you mean:

```
user> (Maybe.Some 5)
:(user/Maybe primitives/Int) (Maybe.Some 5)
user> (Choice.Some 5)
:(user/Choice primitives/Int) (Choice.Some 5)
```

The nullary constructors work the same way: write `Maybe.None` or `Choice.None`.

### Matching: the scrutinee's type selects the pattern

In a `match`, a bare constructor pattern resolves against the type of the value
being matched. When that type is known, the bare patterns read as naturally as
in unambiguous code, even though `Choice` also owns `Some` and `None`:

```
user> (match (Maybe.Some 7) [(Some x) x None 0])
:primitives/Int 7
```

Here the scrutinee is a `Maybe`, so `(Some x)` means `Maybe.Some` and `None`
means `Maybe.None`.

When the scrutinee's type is not known, the bare pattern is ambiguous. In the
function below, the parameter `m` has no annotation and nothing else constrains
it:

```clojure
(defn f [m] (match m [(Some x) x None 0]))   ; ambiguous: Maybe.Some or Choice.Some?
```

Use a dotted pattern to say which type you mean. A data-constructor pattern is
parenthesised with its field bindings (`(Maybe.Some x)`). A nullary pattern is
the bare dotted name (`Maybe.None`). The dotted pattern always resolves,
whatever the scrutinee:

```clojure
(defn f [m] (match m [(Maybe.Some x) x Maybe.None 0]))
```

## Rule of thumb

Bare `Ctor` is the convenient form. `Type.Ctor` always works, in both value and
pattern position. When another type shares a constructor name, a `match` on a
value whose type is known can keep its bare patterns. Qualify a construction,
or a pattern whose scrutinee type is not known.

## See also

- [`spec/05-definitions.md §5.2.2`](../../spec/05-definitions.md) — sum types and
  their constructors (nullary vs data constructors, their types).
- [`spec/08-modules.md §8.5.2`](../../spec/08-modules.md) — dotted names; the
  canonical `Type.Ctor` constructor as a member of the type, always valid wherever
  the type is in bare scope.
- [`spec/06-pattern-matching.md §6.2.1`](../../spec/06-pattern-matching.md) —
  constructor patterns, including how the scrutinee type selects a contested
  bare pattern.
- [`spec/08-modules.md §8.6.5`](../../spec/08-modules.md) — how a bare name with
  several candidates resolves at each use, and when it is ambiguous.
- [`field-accessors.md`](field-accessors.md) — the same canonical-vs-alias story
  for field accessors.
