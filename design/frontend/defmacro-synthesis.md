# `defmacro` Shape Parse and Clause Synthesis

Interior design for `crates/cranelisp-frontend/src/defmacro.rs` — the frontend's
macro-definition surface. Spec: `spec/09-macros.md`.

This is **shape recognition and synthesis, not execution**. The frontend parses
the written `defmacro` form into a structural description and, on request,
synthesises an ordinary function definition for one clause. It never looks a
macro head up against a symbol table, never dispatches, and never calls compiled
code. Recognition and execution belong to the binary.

## 1. Shape parse

`parse_defmacro(sexp) -> DefmacroInfo` extracts the name, the optional docstring,
and the clause list, accepting both spellings §9.2.1 defines: the single-clause
shorthand `[params] body` and the multi-clause `([params] body)+`. Private
`defmacro-` sets the visibility bit. `DefmacroInfo` and `MacroClause` live in
`cranelisp-types` so the binary can name them uniformly after `build_form`; each
clause carries its fixed parameters, an optional rest parameter, and its raw
`body_sexp`.

The macro name and every parameter are binders and reject a qualified or dotted
spelling through the shared helper (`binder-head-reject.md`).

`is_defmacro`, `is_begin` and `flatten_begin` are the recognition helpers the
orchestrator uses to decide what it is holding before it calls a builder. They
are shape predicates over `Sexp`, with no symbol-table knowledge.

### 1.1 Every clause has exactly one body and at most one rest parameter, last

Both clause spellings produce a clause through the same rules, so neither can
accept a shape the other rejects:

- **One body.** The explicit clause already requires exactly two elements. The
  shorthand requires the body to be the last element of the form; a form after
  it is a located error at that form, as at the AST builder's body seam
  (`enforcement-matrices.md` §1). Keeping the first body and dropping the rest is
  the silent-drop class.
- **Rest last, at most once.** One parameter-sequence rule serves both the
  top-level parameter list and a bracket-destructuring pattern: it splits the
  written items into fixed items and an optional rest name, and rejects any item
  after a rest marker, at that item's span (§9.2.2: "exactly one … MUST be the
  last"). The two callers differ only in what a fixed item may be — a symbol or a
  nested bracket at top level, a symbol inside a bracket. A per-caller rest loop
  is how the overwrite and the accepted trailing parameter arose; the shared rule
  closes them for both callers at once.

A rest parameter is a simple symbol only (§9.2.1, S124-Q2), so `[& [a b]]` is
rejected. The reader carries that reject: it reads `&` only when a name follows
(§1.4.8), so `& [a b]` fails at the `&` and never reaches this parser. The
parameter-sequence rule therefore needs no rest-shape check of its own.
*Falsifier:* a reader that accepts `&` before a bracket.

## 2. Clause synthesis

`synthesize_macro_clause_defn(name, clause_idx, clause, span)` builds the `Sexp`
for one clause as an ordinary private function:

```clojure
(defn- __macro_<name>_clause_<N> [: (macros/SList macros/Sexp) __args__] <chain>)
```

where `<chain>` destructures the arguments (§2.1) and ends in the clause body,
constrained to `Sexp` (§2.2). Three properties of the outer shape are
load-bearing.

**The parameter type is fully qualified.** `macros/SList` and `macros/Sexp` are
written qualified because the synthesised `defn` lands in the *user's* module,
where short-name resolution is current-module-only (Principle 17). A bare `SList`
would require an explicit `(import [macros …])` in the user's scope; the
qualified form bypasses short-name lookup entirely and works regardless of what
the user imported.

**Annotations are constructed `Sexp::Annotated` nodes.** A synthetic tree bypasses
the reader, so the synthesiser builds the same structural node that reading
`:type form` would produce. If the annotation representation changes, these are
the sites that change with it — there is no second spelling that the AST builder
also accepts.

**The outer span is the span the caller supplies**, the whole `defmacro` form,
so a diagnostic raised against the synthesised function as a whole traces to the
form the user wrote.

### 2.1 Argument destructuring

The compiled clause receives one value: the argument list as an
`(SList Sexp)`. The chain destructures it with nested matches, one
`(macros/SCons head tail)` peel per fixed parameter:

```clojure
(match __args__
  [(macros/SCons p1 __t2__)
    (match __t2__
      [(macros/SCons p2 __t1__)
        (match __t1__
          [(macros/SCons p3 rest-or-tail) <body>])])])
```

A rest parameter binds the final tail directly; without one, the last peel binds
a discardable tail. Each peel carries a wildcard arm returning a dead `Sexp`
value: arity is validated before invocation so the arm is unreachable, but the
typechecker requires exhaustive coverage of `SList`.

A bracket-destructuring parameter adds an inner peel of `SexpBracket` and then
walks its inner `SList`. Inner tail bindings are named distinctly from outer ones
(`__inner_t{N}__` versus `__t{N}__`); reusing the outer scheme shadows the outer
chain's bindings and silently mis-destructures.

### 2.2 The body is constrained to `Sexp` in every clause shape

§9.2.3 requires a macro body to have type `Sexp`, and §9.9.1 requires the
mismatch to be reported at the offending clause body within the `defmacro` form
(S124-Q3). The synthesiser wraps the clause
body itself in a `:macros/Sexp` annotation node. That one node:

- **constrains every shape alike.** A nullary clause returns its body bare and a
  rest-only clause binds with no dead arm, so a constraint that comes from the
  dead arms reaches neither (ACT-1057). The annotation does not depend on the
  parameter shape.
- **locates the mismatch.** The annotation node carries the body's own source
  span, so typecheck's annotation check reports a non-`Sexp` body at that body,
  inside the `defmacro` form, and names the offending clause of a multi-clause
  macro. The dead arms keep synthetic spans; once the body is annotated they
  agree with it and never decide the error.

Rejected alternatives:

- **A dead arm, or a `Sexp`-typed wrapper, for the parameterless shapes.** It
  constrains the body only through a synthetic span, which is the second half of
  ACT-1057's defect.
- **Annotating the whole chain or the function's return.** The chain's innermost
  arms unify with each other before the outer annotation is checked, so the
  mismatch is still raised at a dead arm's synthetic span.
- **The `defmacro` form's span on the annotation.** It equals the synthesised
  function's own span. Typecheck records expression types by span, so two nodes
  of different type sharing one span is a collision this design avoids.

*Falsifiers:* a nullary or rest-only clause whose body is not `Sexp` that
compiles; a mismatch located outside the source span of the `defmacro` form. The
second depends on typecheck reporting an annotation mismatch at the annotation
node's span, as it does today; a change there moves this location.

### 2.3 Shared construction

Both this module and `quasiquote.rs` build synthetic `Sexp` trees, and both draw
their primitives from `synth` rather than hand-rolling the
`Sexp::{Symbol,List,Bracket}` plus `next_synthetic_span()` shape. The
destructuring *pattern* `(macros/SCons head tail)` is built by the same
`synth::cons` that construction uses, so the pattern and the value it must match
cannot drift apart. The §2.2 annotation is the one synthetic node that carries a
source span instead of a synthetic one.

## 3. What this surface does not decide

- **Whether a clause matches a call.** Arity and structural clause matching
  happen at invocation, in the binary.
- **When clauses are compiled.** The orchestrator compiles each synthesised
  clause definition through the normal pipeline and registers the results; the
  frontend hands back an `Sexp` and stops.
- **The mismatch text.** Typecheck words the annotation mismatch; the frontend
  supplies only the constraint and its span.
- **Macro availability.** A macro is available only to forms after its own
  `defmacro`, in source order. That is the architecture's rule
  ([macro availability decision](../arch/macro-availability-model.md#1-the-rule)), and the frontend neither
  enforces nor depends on it.

## 4. Unit scenarios

| Mechanism | Positive | Negative |
|---|---|---|
| Shorthand body | `(defmacro m [x] x)` keeps one body | `(defmacro m [] 1 2)` rejects at `2` |
| Rest placement | `[& r]`, `[x & r]`, `[[a & r] b]`, `[[a & r] & s]` | `[& r x]`, `[& r & s]`, `[[& r a]]`, `[[& r & s]]`, each at the item after the rest; `[& [a b]]` at the `&`, by the reader |
| Body constraint | the synthesised clause for `[]`, `[& r]`, `[x]` and `[[a] & r]` wraps the body in one `macros/Sexp` annotation carrying the body's span | — |

## Cross-references

- `spec/09-macros.md` §9.2 and §9.9.1 — the `defmacro` form, its parameters and its return-type constraint; `spec/01-lexical.md` §1.4.8 — the rest marker.
- [macro availability decision](../arch/macro-availability-model.md), `design/arch/macro-expansion-ownership.md` — where recognition and execution live.
- `design/frontend/quasiquote-fold.md` — the sibling synthetic surface and the desugar contract.
- `design/frontend/binder-head-reject.md` — the macro-name and parameter binder reject.
- `design/frontend/enforcement-matrices.md` §1 — the body seam the shorthand mirrors.
