# Errors: traits, impls, and definition binders

This page catalogues the compiler diagnostics you meet when declaring traits and
impls, dispatching trait methods, and defining names. Each entry shows the
message (verified against the compiler), why it fires, and the fix it names. The
normative rules are in [`spec/07-traits.md`](../../spec/07-traits.md) and
[`spec/05-definitions.md`](../../spec/05-definitions.md); a companion teaching
guide is [Traits and impls](../guide/traits.md).

> Spans and exact wording can shift slightly between releases; the **remedy** each
> message names is the stable part.

## Qualified name in a binder position

Every definition head is a **binder** — it introduces a name into the current
module — so it must be a **bare, unqualified** symbol. A qualified spelling in a
head position is rejected, and the message names the bare form to write.

**A `defn` head:**

```
user> (defn user/foo [n] n)
Error: parse error: 'user/foo' is a qualified name, but a definition head is a binder and must be a bare (unqualified) name — write 'foo' (a definition binds into the current module; use an import/qualified reference to reach another module)
```

**A `deftype` constructor head** — same rule, the message names the constructor:

```
user> (deftype Shape (user/Circle [:Int r]))
Error: parse error: 'user/Circle' is a qualified name, but a definition head is a binder and must be a bare (unqualified) name — write 'Circle' (…)
```

The rule applies uniformly to **every** binder head: `defn`/`defn-`,
`deftype`/`deftype-`, `deftrait`/`deftrait-`, `defmacro`/`defmacro-`, trait
method-signature names, impl method names, and the constructor and field names a
`deftype` introduces. It also fires when the definition is produced by a macro
(e.g. the prelude `def`/`const` forms expanding to `defn`) — the reject applies to
the expanded head.

**Why:** there is no mechanism for declaring a name into another module; a
definition always binds where it is written. Qualification is a *reference* form
(reaching across modules), never a *binder* form. **Fix:** drop the module prefix
from the head; if you meant to reference a name in another module, do that in
value position, not in a definition head.

Normative: [spec §5](../../spec/05-definitions.md) (binder-positions table),
[spec §8.5](../../spec/08-modules.md) (references carry qualifiers; binders do not).

## `deftrait` and `impl` declaration diagnostics

### Never-applied constructor variable in a parenthesized head

A parenthesized trait head `(Trait f)` is the higher-kinded form **only if** its
variable `f` is applied — `(f a)` — in a method signature. A head whose variable
is never applied is malformed; the message points you at the conventional
bare-head + `self` form:

```
user> (deftrait (Boxy f) (make [:Int n] Int))
Error: type error: trait `Boxy`'s type parameter `f` is never applied `(f …)`; a trait that returns the implementing type uses the bare head and `self`: `(deftrait Boxy (make [] self))`.
```

**Fix:** if you meant a conventional trait, use the bare head `(deftrait Boxy …)`
and write `self` where the implementing type appears. If you meant a higher-kinded
trait, apply `f` in a signature, e.g. `[:(f a) x]`.

### Pairing-head does not name the trait (HKT impl)

A higher-kinded impl's slot 2 is a trait-constructor pairing `(Trait Constructor)`
whose **head must be the trait** being implemented:

```
user> (impl (Functor f) (Foo Option) (defn fmap [g x] x))
Error: type error: impl of trait `Functor` (slot 1) pairs slot 2 with head `Foo`: a trait-constructor pairing's head must name the trait being implemented — write `(Functor Option)`, not `(Foo Option)`.
```

**Fix:** make slot 2's head the same trait as slot 1 — the message shows the
corrected form. (The match is by resolved trait identity, so an alias that
resolves to the same trait is accepted.)

### Impl target has the wrong kind / arity

A higher-kinded impl target must be a type **constructor** of the arity the
trait's variable expects. Naming a plain type (kind `*`) where a `* -> *`
constructor is required is rejected:

```
user> (impl (Functor f) (Functor Int) (defn fmap [g x] x))
Error: type error: Int is not a type constructor (trait Functor expects arity 1)
```

**Fix:** target a constructor of the right arity (`Option`, `List`, a user
`deftype` constructor), not a fully-applied or nullary type.

### Same-arity `defn` clauses that cannot be told apart

Not trait-specific, but adjacent: two `defn` clauses of the **same arity** whose
written parameter types could both match one argument tuple are a
dispatch-ambiguity error, reported at the definition:

```
user> (defn amb ([:Num x] x) ([:Num y] y))
Error: type error: ambiguous dispatch for 'amb': the 1-arg arity clauses #1 and #2 have unifiable (overlapping) parameter types — a call matching one matches both signatures (spec §5.1.1 dispatch coherence); make their parameter types disjoint
```

**Fix:** annotate a clause so the written signatures no longer overlap — see the
[functions guide](../guide/functions.md#same-arity-clauses-must-be-distinguishable-for-dispatch).

## Dispatch diagnostics

### No impl of the trait for the dispatch type

Calling a trait method on a type that has no impl is a clean typecheck error that
**names the owning trait** — even when you imported only the method and never the
trait:

```
user> (import [shapes [area]])
user> (area 7)
Error: type error: no impl of trait shapes/Area for type Int
```

**Fix:** provide an `(impl Area Int …)`, or call on a type that has one. This is
the diagnostic side of [method-import dispatch](../guide/traits.md#importing-trait-methods-a-method-reference-is-enough)
— the trait is always named so you can find where to add the impl.

### Return-type-polymorphic ambiguity

A method dispatched on its **return** type (an empty parameter list, `self` in
return position — like the prelude `Default`'s `default`) needs the return type
pinned by an argument, an annotation, or surrounding context. When nothing pins
it, the call is ambiguous:

```
user> (import [default [default]])
user> (default)
Error: type error: ambiguous type: the return-type-polymorphic call to `default` selects no impl — no argument, annotation, or context pins its return type; add a `:Type` annotation to disambiguate (spec §3.11)
```

**Fix:** add a `:Type` annotation to the call so the compiler can select the
impl — the annotation binds the following form:

```
user> :Int (default)
:primitives/Int 0
```

A surrounding context that forces the type works too (e.g. passing `(default)`
where an `Int` is expected). Normative:
[spec §3.11](../../spec/03-types.md#311-ambiguous-types) and
[§3.3.3](../../spec/03-types.md#333-a-value-position-annotation-is-a-check-or-a-resolution-not-an-abstraction).

## See also

- [Traits and impls](../guide/traits.md) — the teaching guide these diagnostics
  accompany.
- [`guide/constructors.md`](../guide/constructors.md) — ambiguous **bare
  constructor name** diagnostics (a different ambiguity family: two in-scope types
  share a constructor name; remedy = qualify with `Type.Ctor`).
- [`spec/07-traits.md`](../../spec/07-traits.md),
  [`spec/05-definitions.md`](../../spec/05-definitions.md) — the normative rules.
