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

> **About the transcripts.** Every `user>` transcript on this page was checked
> against the real binary; the prompt's timing prefix (`3+0ms; user>`) is elided
> to `user>` for readability. The examples import primitives explicitly
> (`add-i64`, `str-len`) so they run in any directory, with or without the
> standard prelude on the search path.

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
- Every signature must mention the implementing type **somewhere** — see
  [the occurrence rule](#every-method-must-mention-the-implementing-type) below.
  There is no capitalized `Self`; the keyword is the lowercase `self`
  ([spec §7.1.1](../../spec/07-traits.md#711-the-self-type)).

A trait may declare several methods:

```clojure
(deftrait Eq
  (= [a b] Bool)
  (!= [a b] Bool))
```

Here the bare params `a` and `b` both take the implementing type, so for
`(impl Eq Int …)` the methods are `Int -> Int -> Bool`.

### The return type is written without a colon

Inside the parameter bracket, `:Type name` is how you annotate a parameter. In
the **return** position there is no colon: you write the type bare.

```clojure
(deftrait Describe
  (describe [self] String))     ; String — not :String
```

This looks like an inconsistency with `defn`, and it is worth understanding why
it is not. A `defn` has a **body**:

```clojure
(defn area [:Int r] :Int (mul-i64 r r))
```

That `:Int` is not a "return type slot" at all — it is the ordinary value-position
annotation, and it binds **the form that follows it**, which is the body
expression. It says "this expression is an `Int`", the same thing `:Int` means
anywhere else ([spec §3.3.3](../../spec/03-types.md#333-a-value-position-annotation-is-a-check-or-a-resolution-not-an-abstraction)).

A trait method signature has **no body**. There is no following form for a `:` to
bind, so its trailing element *is* the return type itself — a plain type
expression, colon-free. `(zed [] self)`, never `(zed [] :self)`;
`(show [x] String)`, never `(show [x] :String)`.

The same reading explains the one place a colon *does* appear after the bracket:
a [default method](#default-methods--a-body-instead-of-a-return-type) has a body,
so it may annotate that body just like a `defn` does. Normative:
[spec §7.1.1](../../spec/07-traits.md#711-the-self-type).

### Every method must mention the implementing type

A trait exists to be dispatched on. Cranelisp has no way to say "call *this*
impl's version" explicitly — there is no `<Foo as Trait>::method` spelling — so
the compiler must be able to work out the impl from the types at the call site.
That means **every method signature must mention the implementing type at least
once**, in a parameter or in the return type. Three spellings satisfy it:

- a **bare** parameter — `(size [x] Int)`;
- an explicit **`:self`** annotation — `(cmp [:self a :self b] Bool)`;
- **`self` in the return type** — `(zed [] self)`.

A signature with none of them has nothing to dispatch on and is rejected. It is
an **occurrence** rule, not a rule about parameter counts — a non-empty parameter
list does not rescue a signature if every parameter is annotated with some *other*
type:

```
user> (deftrait Zeroable (zed [] Int))
Error: type error at 19..31: trait `Zeroable` method `zed`: no occurrence of the implementing type to dispatch on — a trait method MUST mention the implementing type at least once: either a parameter carries it (a bare name `[x …]` or a `:self` annotation), or the return type is `self`

user> (deftrait Conv (cvt [:String s] Int))
Error: type error at 15..36: trait `Conv` method `cvt`: no occurrence of the implementing type to dispatch on — a trait method MUST mention the implementing type at least once: either a parameter carries it (a bare name `[x …]` or a `:self` annotation), or the return type is `self`
```

Both are the same mistake: `Zeroable`'s `zed` returns `Int` where it meant `self`,
and `Conv`'s `cvt` describes a `String -> Int` function that has nothing to do
with the type being implemented — that is a plain `defn`, not a trait method.

**The rule bites only on the *absence* of the implementing type.** It places no
restriction on any other type variables a method wants to introduce, so a method
may be generic in its own right as long as the implementing type also occurs:

```
user> (deftrait Mappable (map-val [:(Fn [a] b) f x] self))
:user/Mappable ; deftrait
; defn:
;  map-val
```

Here `a` and `b` are the method's own type variables, `x` is bare (the
implementing type) and the return is `self` — accepted. Higher-kinded traits are
exempt from the rule entirely: an HKT method dispatches on its applied
constructor variable `(f a)` instead ([below](#higher-kinded-traits--trait-f)).
Normative: [spec §7.1.1](../../spec/07-traits.md#711-the-self-type).

### Marker traits are not available

A **marker trait** — a trait with no methods at all, existing only to be asserted
by an impl and required as a bound, like other languages' `Send` or `Sized` — has
**no form in Cranelisp today**. A trait must declare at least one method:

```
user> (deftrait Marker)
Error: parse error at 0..17: deftrait requires a trait head and at least one method
```

The honest answer is that there is no workaround, and in particular the obvious
one does not work. Declaring a dummy method that ignores the implementing type —
`(deftrait Marker (mark [:Int x] Int))` — is rejected by the
[occurrence rule](#every-method-must-mention-the-implementing-type) above, and it
would be a different thing anyway: an undispatchable method, not a marker.

This is a **parked boundary, not a principle**. Nothing in the design forecloses
marker traits, and the machinery that would consume one (inline trait constraints,
[spec §7.3.6](../../spec/07-traits.md#736-inline-constraints-on-type-arguments))
already exists; the capability may be specified in a future revision if a real
program shows its absence limiting. Until then the answer is a clear "not
specified" rather than a hedge — see
[spec §7.1.1](../../spec/07-traits.md#711-the-self-type) and
[§7.12.1](../../spec/07-traits.md#7121-current-restrictions).

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

An impl MUST provide every method the trait declares, except those with a
[default body](#default-methods--a-body-instead-of-a-return-type).
Re-entering an `impl` for the same (trait, type) pair **replaces** it — see
[live development](live-development.md#redefining-an-impl).
A method's name may not collide with an existing **field accessor** of the target
type — see [spec §7.3.1](../../spec/07-traits.md#731-concrete-implementation).

### Impl declaration needs the trait in scope

Writing `(impl Trait Type …)` requires the **trait** to resolve at the impl site
(slot 1 is a reference to the trait). Importing only a *method* of the trait is
**not** enough to *declare* an impl — declaration reaches the trait; dispatch
reaches the method (see [Importing trait methods](#importing-trait-methods-a-method-reference-is-enough)
below, and [spec §7.11.2(d)](../../spec/07-traits.md#7112-method-import-dispatch--a-method-reference-suffices)).

## Default methods — a body instead of a return type

Most trait methods are **required**: the trait declares the signature and every
impl must supply the body. But a method can carry a body of its own in the
`deftrait`, and then impls get it for free. That is a **default method**.

The distinction is made by the single element after the parameter bracket:

- a **type** there (`Int`, `String`, `self`) means "no implementation here" — the
  method is **required**;
- anything else is an **expression**, and it is the method's **default body**.

```clojure
(deftrait Sized
  (size [x] Int)                            ; required — impls must define it
  (tag  [x] (add-i64 (size x) 1000)))       ; default — a body, so impls need not
```

A default method's type is **inferred** from its body in the context of its
parameters, exactly like any other expression's type. There is no return-type
slot to fill in — and if you want to pin the type, you annotate the *body* with
the ordinary `:Type` annotation, the same one you would use anywhere else:

```clojure
(<= [a b] :Bool (not (> a b)))
```

That is the governing idea, and it is worth carrying around: **types are
inferred; annotations add constraints.** A default method is not a special form
of signature — it is a parameter list and an expression.

> **The compiler has not caught up with this spelling yet.** At the current build,
> `(tag [x] (add-i64 (size x) 1000))` is rejected — `parse error: invalid type
> expression` — because the parser still commits the element after the bracket to
> a return-type slot before it can tell a type from an expression. Today you must
> write the return type **and** the body, `(tag [x] Int (add-i64 (size x) 1000))`,
> which the settled [spec §7.1](../../spec/07-traits.md#71-trait-declaration)
> no longer has a production for. The transcripts below use the spelling that
> works today; the *model* they teach — inference, override, per-impl templates —
> is the settled one and does not change. (FIXME 0838.)

### An impl inherits the default, or overrides it

```
user> (import [primitives [add-i64]])
user> (deftrait Sized (size [x] Int) (tag [x] Int (add-i64 (size x) 1000)))
:user/Sized ; deftrait
; defn:
;  size tag

user> (deftype Box [:Int n])
:(Fn [primitives/Int] user/Box) user/Box ; deftype

user> (impl Sized Box (defn size [b] (match b [(Box v) v])))
impl user/Sized for user/Box

user> (tag (Box 5))
:primitives/Int 1005
```

The impl defined only `size`; `tag` came from the trait, and the default body's
call to `size` reached *this impl's* `size`. Supply your own `tag` in the impl
and yours wins instead — the default is simply not used for that type.

### A default is a per-impl template, not a trait-level promise

This is the part worth being precise about, because it is easy to assume the
wrong thing. When a default body calls something — a method of *another* trait,
say — that requirement belongs to **the method, and only for impls that actually
use the default**. It does **not** become a requirement of the trait.

So a type that cannot satisfy what the default body needs can still implement the
trait perfectly well, by overriding the method:

```
user> (import [primitives [str-len]])
user> (deftrait Display2 (show2 [x] String))
:user/Display2 ; deftrait
; defn:
;  show2

user> (deftrait Named (nm [x] String) (label [x] String (show2 x)))
:user/Named ; deftrait
; defn:
;  label nm

user> (deftype A [:Int n])
:(Fn [primitives/Int] user/A) user/A ; deftype

user> (impl Display2 A (defn show2 [a] "an A"))
impl user/Display2 for user/A

user> (impl Named A (defn nm [a] "A"))       ; no label — takes the default
impl user/Named for user/A

user> (str-len (label (A 1)))
:primitives/Int 4                            ; "an A" — the default called show2

user> (deftype B [:Int n])
:(Fn [primitives/Int] user/B) user/B ; deftype

user> (impl Named B (defn nm [b] "B") (defn label [b] "own label"))
impl user/Named for user/B                   ; B is not Display2 — and needn't be

user> (str-len (label (B 1)))
:primitives/Int 9
```

`A` instantiates the default, so `A` owes a `Display2` impl. `B` overrides
`label`, so **`B` owes nothing** — and the `Named` trait itself never required
`Display2` of anybody.

**This is not a supertrait.** Cranelisp has no supertraits, and default methods
do not sneak one in: a constraint induced by a default body is per-impl, never a
trait-level obligation
([spec §7.12.1](../../spec/07-traits.md#7121-current-restrictions),
[§7.1.5](../../spec/07-traits.md#715-default-method-implementations)).

> **One combination is broken today.** A default method whose body calls a
> sibling method does **not** survive re-`impl`ing that trait for the type: the
> sibling call fails to link, and the error points inside the `deftrait` — a
> place you did not edit. Each half works alone; only the combination fails. See
> [Redefining an impl](live-development.md#redefining-an-impl) and FIXME 0832.

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
qualifiers*, rejected in any position.

A **dotted** spelling is rejected in a binder too — `(deftype A.B …)`,
`(defn a.b [x] x)`, `(let [a.b 5] …)`. In Cranelisp `.` is *type/trait
qualification*: a way of **reaching** an existing name (`Maybe.Just` in a
pattern, `Pt.x` as an accessor, `platform.posix` in an import), never a way of
introducing one. The
[errors catalogue](../errors/trait-impl-diagnostics.md#qualified-name-in-a-binder-position)
covers the qualified-binder messages, the
[dotted-binder](../errors/trait-impl-diagnostics.md#dotted-name-in-a-binder-position)
ones, and the
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
- [Live development](live-development.md#redefining-an-impl) — what happens when
  you re-enter an `impl` in a running session.
