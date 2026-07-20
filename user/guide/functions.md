# Functions: `fn` and multi-arity `defn`

Cranelisp has two ways to write a function: the anonymous lambda `fn`, and the
named definition `defn`. They differ in one place that trips up newcomers —
**multiple arities** — so it is worth pinning down which form supports what.

## `fn` is single-arity

A lambda takes **exactly one** parameter list and one body:

```clojure
(fn [x] (+ x 1))
(fn [:Int x :Bool y] (if y x 0))
```

That is the whole shape: one `[params]` bracket, one body expression. There is no
multi-clause `fn`. If you try to write one — several `([params] body)` clauses
inside a single `fn` — you get a parse error that tells you exactly what to reach
for instead:

```
user> (fn ([x] x) ([x y] y))
Error: parse error at 0..22: fn is single-arity: it takes one [params] bracket and a body. The parenthesised multi-arity clause form `(fn ([p] …) ([p q] …))` is defn-only — use defn for multiple arities (spec §4.5)
```

The asymmetry is deliberate: multi-arity dispatch is a *named*-function feature —
the compiler picks the matching clause using the definition's name at each call
site — and an anonymous value has no name to dispatch on. When you want more than
one arity, give the function a name with `defn`.

## `defn` supports multiple arities

A `defn` may provide several **variants**, each a parenthesised `([params] body)`
clause with a different parameter list. The compiler dispatches to the matching
variant by the argument types at each call site:

```clojure
(defn rp
  ([:Position p :Rotation rot]          (rp p rot 0))
  ([:Position p :Rotation rot :Int idx] idx))
```

```
user> (defn rp ([:Position p :Rotation rot] (rp p rot 0)) ([:Position p :Rotation rot :Int idx] idx))
:(Fn [user/Position user/Rotation] primitives/Int) user/rp ; defn
:(Fn [user/Position user/Rotation primitives/Int] primitives/Int) user/rp
```

The REPL confirms it by reporting **both** arity signatures.

A multi-signature `defn` carries any **constraints** into every signature it
reports. A constrained parameter is written with a trait annotation — `:Num x` is
one parameter `x` bound to `Num` (the `:Num` annotation binds the single following
form). Both signatures echo the constraint:

```
user> (defn h ([:Num x] (+ x x)) ([:Num x :Num y] (+ x y)))
:(Fn [:Num a] a) user/h ; defn
:(Fn [:Num a :Num a] a) user/h
```

### Clauses infer like separate mutually-recursive functions

Here is the rule that governs inference across the clauses: **a multi-signature
`defn` type-checks exactly as if its clauses were written as separate,
mutually-recursive functions that happen to share one dispatched name.** Type
flows across clauses through ordinary call resolution, not through a barrier.

A **self-call from one clause to a sibling is an ordinary call.** It resolves —
by arity, then among same-arity clauses by argument type — to a specific sibling
clause, and unifies its argument types with that clause's parameters, exactly as
a call to any other function would. So types *do* flow across clauses: a
delegating call from one clause into another carries the callee clause's
parameter types back into the caller. You do **not** have to re-annotate a
parameter that a sibling self-call already pins.

```clojure
(defn rp4
  ([p rot]     (let [q (rp4 p rot 0)] p))        ; => (Fn [Int Int] Int)
  ([p rot idx] (add-i64 p (add-i64 rot idx))))   ; => (Fn [Int Int Int] Int)
```

`add-i64` fixes the 3-arg clause to `(Fn [Int Int Int] Int)`; the 2-arg clause's
`(rp4 p rot 0)` resolves to that sibling and pins `p` and `rot` to `Int` — even
though the 2-arg clause carries no annotations. This type-checks and runs;
`(rp4 7 4)` is `7`.

A clause parameter is an ambiguous-type error **only when the same code written
as a standalone function would also fail to infer it** (genuine [`§3.11`](../../spec/03-types.md)
ambiguity) — never merely because it belongs to a multi-signature form. A clause
left genuinely polymorphic — e.g. `([:a x] x)` — is admissible on the same terms
as any standalone polymorphic function.

### Same-arity clauses must be distinguishable for dispatch

Two clauses of **different arity** always dispatch by argument count. Two clauses
of the **same arity** dispatch by the concrete argument types. Two same-arity
clauses whose signatures — **as written**, i.e. their pre-inference parameter
annotations — *could* both match one concrete argument tuple are a
**dispatch-ambiguity error, reported at the definition** (both colliding clauses
named), not silently resolved by clause order. The remedy is to annotate a clause
so the written signatures no longer overlap. This constrains dispatch
*ambiguity*, not the presence of polymorphism.

## See also

- [`spec/04-expressions.md §4.5`](../../spec/04-expressions.md) — the lambda `fn`:
  single-arity, parameter annotations, capture, and why the multi-arity clause
  form is a parse error for `fn`.
- [`spec/05-definitions.md §5.1.2`](../../spec/05-definitions.md) — multi-signature
  `defn`: variant dispatch, and the inference rule (clauses are inference-equivalent
  to separate mutually-recursive functions — sibling self-calls carry types across
  clauses; the same-arity dispatch-ambiguity rule is judged on the written
  signatures).
