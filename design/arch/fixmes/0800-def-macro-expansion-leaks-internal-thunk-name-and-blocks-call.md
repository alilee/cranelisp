---
number: 0800
target: /stdlib
filed_by: /repl
filed_at: 2026-07-21
sprint_filed: 115
refers_to: repl/spec.md §1.3 (Definition Results), §4.1 (Self-Documentation
  Contract — no per-class row for `def`), §1.1 (Universal Output Format);
  stdlib/defs.cl:24-31 (the `def` macro expansion);
  repl/demos/08-sudoku.demo:62/67/82 (the leak on display in the flagship demo)
status: open
---

# `def`: report both emitted definitions; function-valued application remains open

## Issue

`def` is a stdlib macro (`stdlib/defs.cl:24`) that expands `(def n v)` into a
`defn n-def` thunk **plus** a zero-arg macro `n` that expands to `(n-def)`.
Three faces were probed; a shared implementation root is not established
(2026-07-21,
`target/debug/cranelisp`, clean session):

**Face 1 — the singular definition result drops one emitted definition
(§1.3).**

```
user> (def n 42)
:(Fn [] primitives/Int) user/n-def ; defn
```

The original report treated one emitted definition as an internal leak and
tried to select `n` instead. The 2026-09-05 user ruling corrected that premise:
the statement produces two definitions and the REPL should list both, in
emitted order. The defect is therefore the singular carrier, not the presence
of `n-def`:

```text
:(Fn [] primitives/Int) user/n-def ; defn
:user/n ; defmacro
; [] -> Sexp
```

**Face 2 — confirmed correct: introspection describes the macro binding
(§4.1).**

```
user> /info n
:user/n ; defmacro
; [] -> Sexp
  (def n 42)

user> /sig n
:user/n ; defmacro
; [] -> Sexp
```

`n` is a `defmacro`, so `/sig` and `/info` must report `defmacro` and its clause
signature. Bare `n` is an invocation position: macro expansion produces
`(n-def)`, whose evaluation yields `:primitives/Int 42`. These surfaces describe
different operations and do not require a projected presentation scheme.

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

## Ownership split

Face 1 is an int-side result-carrier defect: the compiler already knows the
exact emitted definitions, and the REPL must render all published identities
without a name-shape rule or symbol-table scan. Face 2 requires no change. Face
3 remains a stdlib API choice because the current `def` expansion intentionally
introduces a zero-argument macro.

## Proposed resolution

1. Face 1 uses an ordered `EvalResult::Definitions` batch. Each symbol renders
   through its ordinary `ModuleEntry` classification.
2. Face 2 stays unchanged: `/info n` and `/sig n` report `defmacro`; bare `n`
   expands and evaluates.
3. Face 3 is a stdlib API/usability decision. `def` is the zero-argument macro
   specified by §5.7/§9.10 and implemented in `stdlib/defs.cl`, not a core
   special form. `/stdlib` decides whether and how its API supports a
   function-valued binding. `/qa` attributes and specifies the behavioral test
   after that design choice.

## QA disposition (Sprint 117)

Face 1 is allocated to the Sprint-121 ordered-definition result work. Face 2 is
not a defect under the binding semantics in `spec/09-macros.md` §§9.5, 9.10.2,
and 9.13. Face 3 remains retargeted to `/stdlib`; `/qa` plans its coverage only
after the user-proxy design exists.

## Context

Found by `/repl` during the S115 Phase-6a delta-surface probe (the auto-curry
item), then confirmed against the committed demo replay. Not new in S115 — the
expansion shape predates it — but it was invisible until the auto-curry work
made "bind it to a variable first" the compiler's own advice.
