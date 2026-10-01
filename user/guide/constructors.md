# Constructors

When you define a sum type, each variant introduces a **constructor** — the
function (or, for a variant with no fields, the value) you use to build that
variant. Just like field accessors, a constructor has two names, and knowing
which is which saves you a confusing error later.

```clojure
(deftype Shape
  Dot
  (Circle [:Int r]))
```

This gives you the constructors `Circle` and `Dot`. There are two ways to name
each one.

> **About the transcripts.** They were checked against the real binary with the
> standard prelude loaded, as in [getting started](../getting-started.md#start-the-repl).
> The prompt's timing prefix is elided to `user>`.

## The canonical name is `Type.Ctor`

A constructor's real, canonical name is the **qualified** `Type.Ctor` form —
`Shape.Circle`, `Shape.Dot`. This is the name the language displays when it
reports a constructed value, and it is **always** valid wherever the type is in
scope:

```
user> (Shape.Circle 5)
:user/Shape (Shape.Circle 5)
```

`Shape.Circle` has type `(Fn [Int] Shape)`. Like any function it is first-class —
you can pass it as an argument or bind it to a variable. A nullary constructor
(one with no fields) is a value rather than a function, and its canonical name
works the same way:

```
user> Shape.Dot
:user/Shape user/Shape.Dot ; deftype
```

The dotted form is **not** a fallback reached only under contention — it is the
constructor's name, and it works exactly like the canonical `Type.field` accessor
(see [`field-accessors.md`](field-accessors.md)).

## The bare name is a convenience alias

Writing the bare constructor name — `Circle` — is a convenience shorthand for the
canonical `Shape.Circle`. It resolves to the same constructor, and it is the
natural way to write code when no other type in scope owns a constructor of the
same name:

```
user> (Circle 5)
:user/Shape (Shape.Circle 5)
```

So `(Circle 5)` and `(Shape.Circle 5)` are the same call. Use the bare form for
readability; reach for the qualified form when you need it.

## When two types share a constructor name

Two in-scope types may each own a constructor with the same name. You meet this
as soon as you define your own optional type, because the standard prelude's
`Option` already owns `Some` and `None`:

```clojure
(deftype (Maybe a) None (Some [:a v]))
```

Each `Some` is a member of a distinct type, so each keeps its own canonical name.
`Maybe.Some` and `Option.Some` name one constructor each and always work. The
bare spelling `Some` now has two candidates, and so does `None`. Typing the bare
name at the prompt lists every candidate; looking a name up never reports an
ambiguity:

```
user> Some
:(Fn [a] (primitives/Option a)) primitives/Option.Some ; deftype
:(Fn [a] (user/Maybe a)) user/Maybe.Some ; deftype
```

`/sig`, `/info` and `/doc` list every candidate the same way
([`repl/spec/04-self-documentation.md` §4.1.11](../../repl/spec/04-self-documentation.md#4111-spellings-with-several-candidates)).

The compiler decides each bare *use* on its own, using only the type information
the program already gives it. It never picks by declaration order or import
order. A use that type information narrows to one candidate resolves to that
candidate. A use it cannot narrow is an **ambiguity error**, and the error lists
the canonical alternatives.

### Constructing a value: qualify it or pin its type

A bare construction whose type nothing fixes is ambiguous, because `7` fits
either type:

```
user> (Some 7)
Error: type error at 1..5: ambiguous bare name 'Some'; surviving declarations: primitives/Option.Some, user/Maybe.Some; qualify the name or add an annotation
```

Write the constructor you mean:

```
user> (Maybe.Some 5)
:(user/Maybe primitives/Int) (Maybe.Some 5)
user> (Option.Some 5)
:(primitives/Option primitives/Int) (Option.Some 5)
```

Or let a type annotation choose. Here the declared return type selects
`Maybe.Some`:

```
user> (defn g [] :(Maybe Int) (Some 7))
:(Fn [] (user/Maybe primitives/Int)) user/g ; defn
user> (g)
:(user/Maybe primitives/Int) (Maybe.Some 7)
```

The nullary constructors work the same way: write `Maybe.None` or `Option.None`.

### Matching: the scrutinee's type selects the pattern

In a `match`, a bare constructor pattern resolves against the type of the value
being matched. When that type is known, the bare patterns read as naturally as
in unambiguous code:

```
user> (match (Maybe.Some 7) [(Some x) x None 0])
:primitives/Int 7
```

Here the scrutinee is a `Maybe`, so `(Some x)` means `Maybe.Some` and `None`
means `Maybe.None`.

When the scrutinee's type is not known, the bare pattern is ambiguous. In the
function below, the parameter `m` has no annotation and nothing else constrains
it:

```
user> (defn f [m] (match m [(Some x) x None 0]))
Error: type error at 22..30: ambiguous constructor 'Some'; surviving declarations: primitives/Option.Some, user/Maybe.Some; qualify the constructor or add an annotation
```

Use a dotted pattern to say which type you mean. A data-constructor pattern is
parenthesised with its field bindings (`(Maybe.Some x)`). A nullary pattern is
the bare dotted name (`Maybe.None`). The dotted pattern always resolves,
whatever the scrutinee:

```
user> (defn f [m] (match m [(Maybe.Some x) x Maybe.None 0]))
:(Fn [(user/Maybe primitives/Int)] primitives/Int) user/f ; defn
user> (f (Maybe.Some 3))
:primitives/Int 3
```

## Rule of thumb

Bare `Ctor` is the convenient form. `Type.Ctor` always works, in both value and
pattern position. When another type shares a constructor name, a `match` on a
value whose type is known can keep its bare patterns. Qualify a construction
(or annotate its type), and qualify a pattern whose scrutinee type is not known.

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
