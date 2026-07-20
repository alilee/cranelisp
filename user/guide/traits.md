# Traits and impls

A **trait** names a set of methods a type can support; an **impl** supplies those
methods for one concrete type (or type constructor). Calls to a trait method
**dispatch** on the type at the call site — the compiler picks the right impl.
This is Cranelisp's mechanism for ad-hoc polymorphism (the `Num`, `Eq`, `Ord`,
`Display` operators in the prelude are all trait methods).

This guide teaches the shapes you write and verifies each against the compiler.
The normative rules live in [`spec/07-traits.md`](../../spec/07-traits.md) and
[`spec/05-definitions.md §5.3`–`§5.4`](../../spec/05-definitions.md); reach for
them at the edges.

## Declaring a trait — `deftrait`

A trait is a bare (uppercase) name followed by one or more **method signatures**.
Each signature is `(name [params] ReturnType)`:

```clojure
(deftrait Describe
  (describe [self] String))
```

Two things to know about the parameter list:

- A **bare** parameter name has the **implementing type**. In `[self]` above,
  `self` is the conventional spelling for "the type this trait is implemented
  for". Writing `(describe [self] String)` means: for each impl, `describe` takes
  one value of the implementing type and returns a `String`.
- Every signature must mention the implementing type **somewhere** — a bare
  parameter, or the lowercase token `self` in the return type. A method that
  mentions it nowhere has nothing to dispatch on and is rejected. There is no
  capitalized `Self`; the keyword is the lowercase `self`
  ([spec §7.1.1](../../spec/07-traits.md#711-the-self-type)).

A trait may declare several methods:

```clojure
(deftrait Eq
  (= [a b] Bool)
  (!= [a b] Bool))
```

Here the bare params `a` and `b` both take the implementing type, so for
`(impl Eq Int …)` the methods are `Int -> Int -> Bool`.

## Implementing a trait — `impl`

An `impl` block names the trait, then the target type, then a `defn` for each
method. The `defn` parameter counts must match the trait's signatures:

```clojure
(deftype Dog [:Int age])

(impl Describe Dog
  (defn describe [self] "a dog"))
```

Now `describe` dispatches on `Dog`:

```
user> (describe (Dog 3))
:primitives/String "a dog"
```

An impl MUST provide every method the trait declares (that has no default body).
A method's name may not collide with an existing **field accessor** of the target
type — see [spec §7.3.1](../../spec/07-traits.md#731-concrete-implementation).

### Impl declaration needs the trait in scope

Writing `(impl Trait Type …)` requires the **trait** to resolve at the impl site
(slot 1 is a reference to the trait). Importing only a *method* of the trait is
**not** enough to *declare* an impl — declaration reaches the trait; dispatch
reaches the method (see [Importing trait methods](#importing-trait-methods-a-method-reference-is-enough)
below, and [spec §7.11.2(d)](../../spec/07-traits.md#7112-method-import-dispatch--a-method-reference-suffices)).

## Return-type dispatch and the `:Type` remedy

A method can be dispatched purely on its **return** type — an empty parameter
list with `self` in return position:

```clojure
(deftrait Zeroable
  (zed [] self))
```

There is no argument to dispatch on, so the call site must pin the return type.
The `:Type` annotation is the disambiguator. The prelude's `Default` trait works
this way — `(default)` returns "the default value of the expected type":

```
user> (import [default [default]])
user> :Int (default)
:primitives/Int 0
user> :String (default)
:primitives/String ""
```

`:Int (default)` reads as "the annotation `:Int` binds the following form
`(default)`" — the annotation both *asks for* an `Int` and *selects* the `Int`
impl. A `:Type` annotation binds the single form that immediately follows it,
in any position ([spec §3.3.3](../../spec/03-types.md#333-a-value-position-annotation-is-a-check-or-a-resolution-not-an-abstraction)).

If nothing — no argument, annotation, or surrounding context — pins the return
type, the call is ambiguous and the compiler says so (the
[errors catalogue](../errors/trait-impl-diagnostics.md#return-type-polymorphic-ambiguity)
covers the exact message and remedy).

## Higher-kinded traits — `(Trait f)`

A trait can range over a **type constructor** rather than a plain type. The head
is parenthesised with a lowercase **constructor variable**, applied in the method
signatures as `(f a)`:

```clojure
(deftrait (Functor f)
  (fmap [:(Fn [a] b) g :(f a) x] (f b)))
```

`f` ranges over one-argument constructors (kind `* -> *`), like `Option` or
`List`. `fmap` takes a function `(Fn [a] b)` and a container `(f a)`, returning
`(f b)`.

An HKT impl **echoes the declared head** `(Functor f)` in slot 1, and names a
**trait-constructor pairing** `(Functor Option)` in slot 2 — the trait applied to
the concrete constructor being implemented:

```clojure
(impl (Functor f) (Functor Option)
  (defn fmap [g x]
    (match x
      [None      None
       (Some v)  (Some (g v))])))
```

```
user> (fmap (fn [n] (+ n 1)) (Some 4))
:(primitives/Option primitives/Int) (Option.Some 5)
```

The rules that shape the two slots:

- **Slot 1 is fixed** — it reproduces the `deftrait` head verbatim, the same
  constructor-variable spelling `(Functor f)`. It is neither renamed nor omitted.
- **Slot 2's head names the trait** — `(Functor Option)`, not some other name;
  it is matched to slot 1 by resolved trait identity.
- **The constructor's arity must match** the trait's constructor variable
  (`Option` is `* -> *`, matching `f`'s single application `(f a)`).

See [spec §7.2](../../spec/07-traits.md#72-higher-kinded-traits) and
[§7.3.4](../../spec/07-traits.md#734-higher-kinded-implementation). The
[errors catalogue](../errors/trait-impl-diagnostics.md) explains the diagnostics
when a slot is malformed.

## Importing trait methods — a method reference is enough

You do **not** have to import a trait to call its methods. Importing the
**method** alone is sufficient for dispatch. Given a module `shapes` that declares
`(deftrait Area (area [self] Int))` with an impl for `Circle`:

```clojure
(import [shapes [area Circle]])   ; the method `area`, not the trait `Area`
```

```
user> (area (Circle 3))
:primitives/Int 9
```

This works because a method reference carries the method's full identity, which
already names its owning trait and that trait's home module — reaching the method
reaches everything dispatch needs ([spec §7.11.2](../../spec/07-traits.md#7112-method-import-dispatch--a-method-reference-suffices)).
Two consequences worth knowing:

- **Diagnostics still name the trait.** If there is no impl for the dispatch type,
  the error names the owning trait even though you never imported it — e.g.
  `no impl of trait shapes/Area for type Int`.
- **Two same-named method imports conflict.** Importing an `area` from two
  different traits is a duplicate-name conflict (rejected), not a silent shadow.
  Choosing which module's `area` you import *is* how you disambiguate.

Remember the one asymmetry from above: this covers **dispatch**. To **declare**
an `(impl Area …)` you still need the trait `Area` itself in scope.

## Definition heads are bare names

Every definition head — `deftrait`, `deftype`, `defn`, a trait method name, an
impl method — is a **binder**, so it must be a **bare, unqualified** name. A
qualified spelling like `(deftrait fmt/Foo …)` or `(deftype user/Circle …)` is a
compile-time error: you can only *define* a name into the current module, never
into another.

The rule is not limited to definition heads. **Every** binder is bare — including
the *value-level* ones: a `defn`/`fn` parameter, a `let` name, and a `match`
variable pattern all reject a qualified spelling too (only a `match` pattern's
constructor *name* stays a reference and may be qualified). And a name is malformed
outright if either half around a `/` is empty — `foo/` or `/bar` are *dangling
qualifiers*, rejected in any position. The
[errors catalogue](../errors/trait-impl-diagnostics.md#qualified-name-in-a-binder-position)
covers the qualified-binder messages and the
[dangling-qualifier](../errors/trait-impl-diagnostics.md#dangling-qualifier--an-empty-module-or-local-half)
ones; the rule is [spec §5](../../spec/05-definitions.md)'s binder-positions table.

## See also

- [`spec/07-traits.md`](../../spec/07-traits.md) — traits, `self`, HKT, impl
  kind-checking, method-import dispatch, deriving.
- [`spec/05-definitions.md §5.3`–`§5.4`](../../spec/05-definitions.md) —
  `deftrait`/`impl` as definition forms; the binder-positions table (§5).
- [Errors catalogue — trait/impl diagnostics](../errors/trait-impl-diagnostics.md)
  — every rejection message this guide points at, with its remedy.
- [Functions](functions.md) — multi-arity `defn` and dispatch, which trait
  methods build on.
