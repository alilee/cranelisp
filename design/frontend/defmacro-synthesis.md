# `defmacro` Shape Parse and Clause Synthesis

Interior design for `crates/cranelisp-frontend/src/defmacro.rs` — the frontend's
macro-definition surface. Spec: `spec/09-macros.md`.

This is **shape recognition and synthesis, not execution**. The frontend parses
the written `defmacro` form into a structural description and, on request,
synthesises an ordinary function definition for one clause. It never looks a
macro head up against a symbol table, never dispatches, and never calls compiled
code. Recognition belongs to typecheck and int; execution belongs to int.

## 1. Shape parse

`parse_defmacro(sexp) -> DefmacroInfo` extracts the name, the optional docstring,
and the clause list, accepting both spellings the spec defines: the single-clause
shorthand `[params] body` and the multi-clause `([params] body)+`. Private
`defmacro-` sets the visibility bit. `DefmacroInfo` and `MacroClause` live in
`cranelisp-types` so int can name them uniformly after `build_form`; each clause
carries its fixed parameters, an optional rest parameter, and its raw
`body_sexp`.

A parameter bracket recognises `&` for a rest parameter and a nested bracket for
destructuring. The macro name is a binder and rejects a qualified or dotted
spelling through the shared helper (`binder-head-reject.md`).

`is_defmacro`, `is_begin` and `flatten_begin` are the recognition helpers the
orchestrator uses to decide what it is holding before it calls a builder. They
are shape predicates over `Sexp`, with no symbol-table knowledge.

## 2. Clause synthesis

`synthesize_macro_clause_defn(name, clause_idx, clause, span)` builds the `Sexp`
for one clause as an ordinary private function:

```clojure
(defn- __macro_<name>_clause_<N> [: (macros/SList macros/Sexp) __args__] <body>)
```

Three properties of that shape are load-bearing.

**The parameter type is fully qualified.** `macros/SList` and `macros/Sexp` are
written qualified because the synthesised `defn` lands in the *user's* module,
where short-name resolution is current-module-only (Principle 17). A bare `SList`
would require an explicit `(import [macros …])` in the user's scope; the
qualified form bypasses short-name lookup entirely and works regardless of what
the user imported.

**The parameter is a constructed `Sexp::Annotated`.** A synthetic tree bypasses
the reader, so the synthesiser must build the same structural node that reading
`: type name` would produce. If the annotation representation changes, this is
the site that has to change with it — there is no second spelling that the AST
builder also accepts.

**The outer span is the originating clause's user-source span,** so a
diagnostic raised while checking the synthesised function traces back to the
clause the user wrote rather than to a synthetic offset.

### 2.1 Argument destructuring

The compiled clause receives one value: the argument list as an
`(SList Sexp)`. `build_macro_param_chain` destructures it with nested matches,
one `(macros/SCons head tail)` peel per fixed parameter:

```clojure
(match __args__
  [(macros/SCons p1 __t2__)
    (match __t2__
      [(macros/SCons p2 __t1__)
        (match __t1__
          [(macros/SCons p3 rest-or-tail) <body>])])])
```

A rest parameter binds the final tail directly; without one, the last peel binds
a discardable tail. Each match carries a wildcard arm returning a dead value:
arity is validated before invocation so the arm is unreachable, but the
typechecker requires exhaustive coverage of `SList` and the alternative would be
a synthesised program that does not typecheck.

A bracket-destructuring parameter adds an inner peel of `SexpBracket` and then
walks its inner `SList`. Inner tail bindings are named distinctly from outer ones
(`__inner_t{N}__` versus `__t{N}__`); reusing the outer scheme shadows the outer
chain's bindings and silently mis-destructures.

### 2.2 Shared construction

Both this module and `quasiquote.rs` build synthetic `Sexp` trees, and both draw
their primitives from `synth` rather than hand-rolling the
`Sexp::{Symbol,List,Bracket}` plus `next_synthetic_span()` shape. The
destructuring *pattern* `(macros/SCons head tail)` is built by the same
`synth::cons` that construction uses, so the pattern and the value it must match
cannot drift apart.

## 3. What this surface does not decide

- **Whether a clause matches a call.** Arity and structural clause matching
  happen at invocation, in int.
- **When clauses are compiled.** The orchestrator compiles each synthesised
  clause definition through the normal pipeline and registers the results; the
  frontend hands back an `Sexp` and stops.
- **Macro availability.** A macro is available only to forms after its own
  `defmacro`, in source order. That is the architecture's rule
  ([macro availability decision](../arch/macro-availability-model.md#1-the-rule)), and the frontend neither
  enforces nor depends on it.

## Cross-references

- `spec/09-macros.md` — the `defmacro` form, the `Sexp`/`SList` ADTs, and the quasiquote rules.
- [macro availability decision](../arch/macro-availability-model.md), `design/arch/macro-expansion-ownership.md` — where recognition and execution live.
- `design/frontend/quasiquote-fold.md` — the sibling synthetic surface and the desugar contract.
- `design/frontend/binder-head-reject.md` — the macro-name binder reject.
