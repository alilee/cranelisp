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

## Gotcha — bare names are ambiguous when two types share a constructor

The bare alias only works when **exactly one** in-scope type owns a constructor of
that name. The moment two in-scope types share a constructor name, the bare name
has no single target:

```clojure
(deftype (Maybe a)  None (Some [:a v]))
(deftype (Choice a) None (Some [:a v]))
```

Now bare `Some` is ambiguous — does it mean `Maybe.Some` or `Choice.Some`?
Cranelisp rejects the bare use rather than guessing, and the error names the
canonical alternatives:

```
user> (Some 5)
Error: type error at 1..5: ambiguous bare name 'Some' — use a qualified member (Choice.Some or Maybe.Some)
```

The same happens to the nullary `None`, since both types own one:

```
user> None
Error: type error at 0..4: ambiguous bare name 'None' — use a qualified member (Choice.None or Maybe.None)
```

The fix is always the same: **use the qualified `Type.Ctor` form.** The canonical
constructors are never ambiguous — each names exactly one constructor — so they
keep working regardless of how many types share the name:

```
user> (Maybe.Some 5)
:(user/Maybe primitives/Int) (Maybe.Some 5)
user> (Choice.Some 5)
:(user/Choice primitives/Int) (Choice.Some 5)
```

Bringing two types that share a constructor name into scope is **permitted** — it
is not a name collision. Neither `Some` is a standalone definition; each is a
derived member of a distinct type, so the two types coexist happily and only the
bare alias is poisoned.

## It holds in pattern position too

The dotted form works in `match` patterns exactly as it does in value position.
When a scrutinee could belong to either of two same-named-constructor types, the
dotted pattern says which one you mean:

```clojure
(defn unwrap [:(Maybe Int) m]
  (match m
    [(Maybe.Some x) x
     Maybe.None     0]))
```

```
user> (unwrap (Maybe.Some 7))
:primitives/Int 7
user> (unwrap Maybe.None)
:primitives/Int 0
```

A data-constructor pattern is parenthesised with its field bindings
(`(Maybe.Some x)`); a nullary pattern is the bare dotted name (`Maybe.None`). Both
sit inside the `match`'s square-bracketed arm list. In unambiguous code the bare
pattern (`(Some x)`, `None`) is resolved against the scrutinee's type and reads
just as well — reach for the dotted pattern when two same-named constructors are
in scope.

## Rule of thumb

Bare `Ctor` is the convenient form; `Type.Ctor` is the form that *always* works,
in both value and pattern position. If a bare constructor name ever stops
resolving because another type introduced the same name, qualify it.

## See also

- [`spec/05-definitions.md §5.2.2`](../../spec/05-definitions.md) — sum types and
  their constructors (nullary vs data constructors, their types).
- [`spec/08-modules.md §8.5.2`](../../spec/08-modules.md) — dotted names; the
  canonical `Type.Ctor` constructor as a member of the type, always valid wherever
  the type is in bare scope.
- [`spec/08-modules.md §8.6.5`](../../spec/08-modules.md) — how two same-named
  constructors coexist (alias-poison) and how the dotted form disambiguates.
- [`field-accessors.md`](field-accessors.md) — the same canonical-vs-alias story
  for field accessors.
