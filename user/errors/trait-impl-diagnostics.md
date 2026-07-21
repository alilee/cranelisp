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
Error: parse error at 6..14: 'user/foo' is a qualified name, but a binder must be a bare (unqualified) name — write 'foo' (a binder introduces a name into the current module or scope; use an import or qualified reference to reach another module)
```

**A `deftype` constructor head** — same rule, the message names the constructor:

```
user> (deftype Shape (user/Circle [:Int r]))
Error: parse error at 16..27: 'user/Circle' is a qualified name, but a binder must be a bare (unqualified) name — write 'Circle' (…)
```

The message is **position-neutral** — it says "a binder", not "a definition
head", because the same rule reaches local binders (`let`, parameters, `match`)
where "definition head" would be wrong.

The rule applies uniformly to **every** binder head: `defn`/`defn-`,
`deftype`/`deftype-`, `deftrait`/`deftrait-`, `defmacro`/`defmacro-`, trait
method-signature names, impl method names, and the constructor and field names a
`deftype` introduces. It also fires when the definition is produced by a macro
(e.g. the prelude `def`/`const` forms expanding to `defn`) — the reject applies to
the expanded head.

The same rule reaches **value-level binders**, not just definition heads. A
qualified spelling in a `defn`/`fn` **parameter**, a `let` **name**, or a `match`
**variable pattern** is rejected too — these positions *introduce* a name into a
local scope, so they are binders and must be bare:

```
user> (defn f [user/x] x)
user> (let [user/y 5] y)
user> (match v [(Some user/w) w])
```

each rejects the qualified binder, with the **same** message as a definition
head — one rule, one wording, every position. (In a `match` constructor pattern
only the *bindings* are binders — the constructor name itself, e.g. `Some` above,
is a reference and may be qualified.)

**Why:** there is no mechanism for declaring a name into another module; a
definition always binds where it is written. Qualification is a *reference* form
(reaching across modules), never a *binder* form. **Fix:** drop the module prefix
from the head; if you meant to reference a name in another module, do that in
value position, not in a definition head.

Normative: [spec §5](../../spec/05-definitions.md) (binder-positions table),
[spec §8.5](../../spec/08-modules.md) (references carry qualifiers; binders do not).

## Dotted name in a binder position

A **dotted** spelling (`a.b`) in a binder position is rejected on exactly the
same footing as a qualified one, with its own message:

```
user> (defn a.b [x] x)
Error: parse error at 6..9: 'a.b' is a dotted name, but a binder must be a bare (unqualified) name — write 'b' ('.' is reserved for type/trait qualification)
```

It fires at **every** binder position the `/` rule covers — definition heads,
variant-constructor names, field names, type parameters, trait method-signature
names and constructor variables, `defmacro` heads, and the value-level `let`,
parameter and `match` binders:

```
user> (deftype A.B [:Int r])          ; head
user> (deftype P [:Int a.b])          ; field name
user> (let [a.b 5] a.b)               ; let binding
user> (defn g [a.b] 1)                ; parameter
user> (match 1 [a.b a.b])             ; variable pattern
```

**The line worth remembering is binder vs reference.** `.` in Cranelisp is
**type/trait qualification syntax** — a *reference* device, never a
name-introducing one. So dots stay perfectly legal wherever you are *reaching*
for something that already exists:

| Dotted **reference** — legal | What it is |
|---|---|
| `(Maybe.Just x)` in a `match` pattern head | qualified constructor pattern ([constructors guide](../guide/constructors.md)) |
| `(Pt.x p)` | field accessor ([field accessors](../guide/field-accessors.md)) |
| `:(Option Int)` / a dotted type or trait reference | type-position qualification |
| `(import [platform.posix [*]])` | dotted module path ([using platforms](../guide/using-platforms.md)) |

**Fix:** in a binder, write the bare last segment (`b`). If you meant to *reach*
an existing name, you are in a reference position and the dot is fine there.

Normative: [spec §5](../../spec/05-definitions.md) (*Dotted binders reject
exactly as qualified ones do*), [spec §1.4.4](../../spec/01-lexical.md) (`.` is
type/trait qualification).

## Dangling qualifier — an empty module or local half

A qualified name has two halves around the `/`: a **module** and a **local
name**, and **both must be non-empty**. A `/` with nothing on one side is a
*dangling qualifier* — a malformed name caught at read time, in **every** position
(value, operand, annotation, and binder alike). The check is purely lexical, so it
does not depend on what the name would have meant, and the message differs by
*which* half is empty.

**Empty module half — `/bar`** (nothing before the `/`):

```
user> (add-i64 /bar 1)
Error: parse error at 9..10: `/` here has no module name before it — a qualified name needs a non-empty module (`mod/name`); a bare `/` division must be separated (`(/ a b)`)
```

The message deliberately separates this from the **division operator**: a lone `/`
with whitespace around it (`(/ 6 2)`) is arithmetic and stays legal — only a `/`
*immediately* followed by a name is the dangling-qualifier error.

> At the bare REPL prompt, `/bar` is read as a REPL **slash-command** (you get
> `unknown command '/bar'`); the located reader reject above is what you see when
> the token appears inside a form.

**Empty local half — `foo/`** (nothing after the `/`):

```
user> foo/
Error: parse error at 4..4: `/` here has no local name after it — a qualified name needs a non-empty local (`mod/name`); drop the trailing `/` to write a bare name
```

This is the same rule from the other side, at the same level of detail as the
empty-module half, and it fires in a binder slot too — `(defn f [foo/] …)`,
`(let [foo/ 5] …)` — with the same message.

**Fix:** write both halves (`mod/name`), or remove the stray `/`. If you meant
division, separate the `/` with spaces (`(/ a b)`).

Normative: [spec §8.5.1](../../spec/08-modules.md) (both halves non-empty; a lone
`/` is division) and [spec §1.4.5](../../spec/01-lexical.md) (a dangling qualifier
is a located reader error).

## The form after `:` must be a type

A `:` annotation binds the single form that immediately follows it, and that form
**must be a type**. Pointing `:` at a value — an integer literal, say — is a
compile-time error that names what it found:

```
user> :3 5
Error: parse error at 0..1: the form bound by `:` must be a type expression; found `3`
```

**Fix:** put a type after the `:` (`:Int`, `:String`, `:(Fn [Int] Int)`), or drop
the annotation if you did not mean to ascribe one. Because the annotation binds the
*next* form, `:Int 3` reads as "the `Int`-typed value `3`", whereas `:3` tries to
use `3` itself as a type.

Normative: [spec §1.4.5](../../spec/01-lexical.md) (`:` is a reader macro that
binds the following form) and [spec §2.8.3](../../spec/02-grammar.md) (the bound
form is a type expression).

## A type parameter must be lowercase

In a parameterised `deftype` or `deftrait` head, the parameters are **type
variables**, written **lowercase**. An uppercase name in a parameter slot reads as
a *named-type reference*, not a fresh parameter binder, so it is rejected:

```
user> (deftype (Box A) (Box [:A x]))
Error: parse error at 14..15: type parameter `A` must be a lowercase symbol (a type variable); an uppercase name is a named-type reference, not a parameter (spec §2.2.2)
```

**Fix:** spell the parameter lowercase — `(deftype (Box a) (Box [:a x]))`. The same
rule governs a `deftrait` constructor variable `(Functor f)` and every other
type-parameter binder.

Normative: [spec §2.2.2](../../spec/02-grammar.md) (a type parameter is a lowercase
symbol).

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
