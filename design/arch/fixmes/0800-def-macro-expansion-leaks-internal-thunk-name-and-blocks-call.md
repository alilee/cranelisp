---
number: 0800
target: /qa
filed_by: /repl
filed_at: 2026-07-21
sprint_filed: 115
refers_to: repl/spec.md §1.3 (Definition Results), §4.1 (Self-Documentation
  Contract — no per-class row for `def`), §1.1 (Universal Output Format);
  stdlib/defs.cl:24-31 (the `def` macro expansion);
  repl/demos/08-sudoku.demo:62/67/82 (the leak on display in the flagship demo)
status: open
---

# `def` leaks its expansion at the prompt: internal `-def` name in the echo, `defmacro` in introspection, and a `def`-bound function value cannot be called

## Issue

`def` is a stdlib macro (`stdlib/defs.cl:24`) that expands `(def n v)` into a
`defn n-def` thunk **plus** a zero-arg macro `n` that expands to `(n-def)`. That
mechanism is invisible in the source the user typed, but it is fully visible in
every REPL response. Three faces, one root — probed at HEAD (2026-07-21,
`target/debug/cranelisp`, clean session):

**Face 1 — the definition echo names a symbol the user never wrote (§1.3).**

```
user> (def n 42)
:(Fn [] primitives/Int) user/n-def ; defn
```

§1.3 requires the definition confirmation to be the definition's own lookup
display. The user defined `n`, a value of type `Int`; the REPL confirms `n-def`,
a thunk of type `(Fn [] Int)`. Both halves of the universal format (§1.1) are
wrong for the form entered. **This is live in the showcase**: `08-sudoku.demo`
— the centrepiece of the guided arc — prints `user/puzzle-def`,
`user/answer-def`, `user/contradiction-def` (replay of 2026-07-21).

**Face 2 — introspection classifies a `def`-bound value as a macro (§4.1).**

```
user> /info n
:user/n ; defmacro
; [] -> Sexp
  (def n 42)

user> /sig n
:user/n ; defmacro
; [] -> Sexp
```

`/sig` and `/info` on a name the user bound to `42` answer "macro, `[] -> Sexp`".
Bare `n` at the prompt is correct (`:primitives/Int 42`), so the value-display
path and the introspection path disagree about the same name. §4.1 has **no
per-class row for `def`** at all, which is the spec-side half of this.

**Face 3 — a `def`-bound function value cannot be called or curried.**

```
user> (defn mk [n] (fn [a b] (+ n (+ a b))))
:(Fn [:Num a] (Fn [:Num a :Num a] a)) user/mk ; defn

user> (def k (mk 10))
:(Fn [] (Fn [primitives/Int primitives/Int] primitives/Int)) user/k-def ; defn

user> k
:(Fn [primitives/Int primitives/Int] primitives/Int) <closure>

user> (k 1 2)
Error: macro error at 0..7: macro `user/k` returned malformed sexp at 0..7: no
matching clause for macro `user/k` with 2 argument(s); clauses accept 0 argument(s)
```

Bare `k` displays a two-argument closure; applying it to two arguments is an
opaque internal macro-arity error. This is a **functional** gap, not a cosmetic
one, and it is reached by the guidance the compiler itself gives elsewhere:
`(((h) 1) 2)` (where `h` returns a closure) is rejected with *"auto-curry
requires a named function; bind this expression to a variable first"* — and
`def` is the binding form a user reaches for, which then produces face 3. The
S115 auto-curry-over-a-local-closure fix works correctly **inside** a function
body (`(defn t1 [] (let [g (mk 10)] ((g 1) 2)))` → `13`, verified), so the gap
is specific to the top-level `def` route.

## Why `/repl` cannot resolve this

The mechanism is a stdlib macro (`/stdlib`), the echo and introspection routing
are int-side display concerns (`/dev(src)`), and the face-3 message comes from
the macro-expansion arity check (`/dev(frontend)`). Which layer should change is
an attribution question, and the fix is not obviously one-sided: options span
suppressing the synthesized `-def` `defn` from the turn echo and routing
`/info`/`/sig`/call through the `def`-macro to its impl thunk, versus changing
the expansion so `def` binds a value directly. `/repl` owns the contract that is
violated, not the seam.

## Proposed resolution

1. `/qa` attributes and routes; a minimal repro exists above (three independent
   one-liners, no imports beyond the prelude).
2. **Face 1 and face 2 are the highest-value pair** — they are what the
   self-documenting-REPL principle promises, and face 1 ships in the flagship
   demo today.
3. Face 3 needs the ruling first: is a `def`-bound name callable when its value
   is a function? If yes, the expansion or the call seam changes; if no, the
   diagnostic must say so in the user's vocabulary (naming `def`, not
   "clauses accept 0 argument(s)"), never leak the macro-arity internal.
4. `/repl` owns the spec-side follow-through once the ruling lands: a `def`
   per-class row in `repl/spec.md` §4.1 and a §1.3 row pinning the echo. Filed
   as a `/repl` 6b/next-sprint item, gated on 1–3.

## Context

Found by `/repl` during the S115 Phase-6a delta-surface probe (the auto-curry
item), then confirmed against the committed demo replay. Not new in S115 — the
expansion shape predates it — but it was invisible until the auto-curry work
made "bind it to a variable first" the compiler's own advice.
