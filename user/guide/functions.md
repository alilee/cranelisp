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

### Each clause is type-checked independently

This is the subtle rule, and the one that produces a surprising error if you miss
it. **Each variant is type-checked on its own.** A clause carries no type
information into or out of its sibling clauses:

- Matching parameter names across clauses (a `p` in two clauses) are **not**
  evidence that the two `p`s share a type.
- A delegating call from one clause into another — the 2-arg clause calling the
  3-arg clause above — does **not** back-flow the callee clause's parameter types
  into the caller clause's parameters.

So every clause **must carry its own annotations** wherever inference cannot pin
its parameters from that clause's own body. Drop the annotations from the 2-arg
clause, expecting the annotated 3-arg sibling to rescue it, and you get an
ambiguous-type error that names the exact clause and parameter:

```clojure
(defn rp
  ([p rot]                              (rp p rot 0))   ; p, rot unannotated
  ([:Position p :Rotation rot :Int idx] idx))
```

```
user> (defn rp ([p rot] (rp p rot 0)) ([:Position p :Rotation rot :Int idx] idx))
Error: type error at 22..23: ambiguous type: the parameter `p` in the 2-arg arity clause of `rp` is not pinned — each arity clause is type-checked independently (spec §5.1.2), so add a `:Type` annotation to `p` in that clause
```

The fix is to annotate the under-constrained clause too — the first `rp` above,
where both clauses are fully annotated, is the correct form. The sibling clause's
annotations never do the work for you.

## See also

- [`spec/04-expressions.md §4.5`](../../spec/04-expressions.md) — the lambda `fn`:
  single-arity, parameter annotations, capture, and why the multi-arity clause
  form is a parse error for `fn`.
- [`spec/05-definitions.md §5.1.2`](../../spec/05-definitions.md) — multi-signature
  `defn`: variant dispatch and the independent-type-checking rule (with the same
  worked example).
