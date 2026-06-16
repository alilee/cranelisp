---
number: 0385
target: /dev
filed_by: /qa
filed_at: 2026-06-16
sprint_filed: 84
refers_to: spec/03-types.md §3.11.1 (worked example `(id :(Vec Int) [])`), spec/03-types.md §3.9 (annotation syntax), spec/03-types.md §3.2.7 (Vec type), tests/regression.rs::mono_vec_empty_annotation_pins_and_compiles_pos, tests/regression.rs::mono_bare_annotated_value_pins_and_compiles_pos
status: open
---

# Builtin `Vec` is unresolvable in type-annotation position — `:(Vec Int)` fails with "unknown type 'Vec'"

## Issue

The tightened §3.11.1 (commit `2290aa9`) rejects an unpinned `(Vec a)` value at a
codegen-reaching position and directs the user to disambiguate with the worked
example `(id :(Vec Int) [])`. But the `:(Vec Int)` annotation **does not resolve**:
the type-annotation type-expression resolver reports the builtin `Vec` as an
unknown type, even when `Vec` is explicitly imported.

Reproduced at HEAD (target/debug/cranelisp --run), `Vec` imported:

```clojure
(import [primitives [IO Pure Int Vec vec-len]])
(defn id [x] x)
(defn main [] :(IO Int)
  (Pure (vec-len (id :(Vec Int) []))))
```

→ `error: ... type error at ...: unknown type 'Vec' (from module '')`

The same gap fires for `:(Vec Int)` in **every** annotation position tried —
value-annotation `(id :(Vec Int) [])`, bare `:(Vec Int) []`, AND parameter
annotation `(defn f [:(Vec Int) v] ...)`. By contrast:

- `:(Option Int) None` **works** (user-declared parameterised ADT resolves).
- `:(Box Int) (Wrap 7)` **works** (user-declared parameterised ADT).
- `:Int`, `:(IO Int)` **work** (primitive / seeded ADT).

So the gap is specifically the **builtin `Vec`** type constructor: it is registered
as a built-in type (`spec/03-types.md §3.2.7`, `primitives` module) and resolves
fine for inference of vec literals `[1 2 3]`, but the type-annotation **type-expr
resolver** does not find `Vec` as an applicable type constructor — it reports
"unknown type 'Vec' (from module '')" (note the empty module — the resolution path
isn't qualifying it to `primitives`).

## Proposed resolution

Make the builtin `Vec` resolvable as an applied type constructor in
type-annotation type-expression position (the path that resolves `:(T args...)`),
matching how user-declared parameterised ADTs (`Option`, `Box`) resolve. The
"(from module '')" empty-module signature suggests the annotation type-expr
resolver is not qualifying `Vec` to its `primitives`-module registration the way
the inference path does. Likely a frontend/typecheck type-expr-resolution seam
(the same resolver that handles `:(Option Int)`), missing the builtin `Vec`
registration.

## Operational implication / Context

- **This blocks the §3.11.1 disambiguation path for `Vec`.** The spec's own worked
  example `(id :(Vec Int) [])` does not compile. Without this fix, a user who hits
  the tightened "unpinned `(Vec a)`" ambiguity error has **no working annotation**
  to fix it with — the directed remedy fails. (The `(Option a)` remedy
  `:(Option Int) None` works; only `Vec` is broken.)
- Two /qa acceptance guards are FAILING-FIRST against this gap:
  `mono_vec_empty_annotation_pins_and_compiles_pos` and the Vec leg of
  `mono_bare_annotated_value_pins_and_compiles_pos` (both
  `tests/regression.rs`). They assert no "unknown type" error + clean exit; they
  flip GREEN when `Vec` resolves in annotation position.
- This is **distinct from** the §3.11.1 rejection work (FIXME 0379→tightened): that
  work makes unpinned `(Vec a)`/`(Fn a)` an *error*; THIS gap makes the *fix* for
  that error work. Both are needed for the tightened spec to be coherent — reject
  the ambiguous form AND accept the annotated form.
- Cross-check `(Fn ...)` annotation resolution while here — the `Fn` type
  constructor in annotation position may have the same or an adjacent gap (not
  yet witnessed RED by a guard; the §3.11.1 `(Fn a)` rejection guard
  `mono_fn_free_var_value_rejected_neg` is independent of this).
