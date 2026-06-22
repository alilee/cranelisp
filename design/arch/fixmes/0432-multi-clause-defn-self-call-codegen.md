---
number: 0432
target: /qa
filed_by: /dev
filed_at: 2026-06-22
sprint_filed: 89
refers_to: spec/05-definitions.md §5.1.2, spec/12-runtime.md §12.5
status: open
---

# Multi-clause `defn`: any self-call inside a variant body fails codegen

## Issue

A multi-signature (multi-clause) `defn` whose body recursively calls the
function itself — whether cross-variant or same-arity self-recursion — fails at
**codegen** with `undefined function: <name>`. Typecheck succeeds; codegen does
not resolve the bare in-body name to the mangled variant symbol (`<name>$Params`).

Reproduces in REPL **and** `--run` (so it is mode-independent, not a REPL-eval
quirk). Minimal shapes, all `undefined function: sum-to` at codegen:

Cross-variant self-call (the §5.1.2 + §12.5 tail-accumulator combined idiom):
```lisp
(defn sum-to
  ([:Int n] (sum-to n 0))
  ([:Int n :Int acc] (if (= n 0) acc (sum-to (- n 1) (+ acc n)))))
```

Same-arity self-recursion inside one variant of a multi-clause defn:
```lisp
(defn sum-to
  ([:Int n :Int acc] (if (= n 0) acc (sum-to (- n 1) (+ acc n))))
  ([:Int n] 0))
```

Contrast — these WORK (verified S89 Phase-6 via `--run`, stdlib prelude):
- Single-clause tail-recursive accumulator: `(defn sum-to [n acc] (if (= n 0)
  acc (sum-to (- n 1) (+ acc n))))` → `(sum-to 5 0) = 15`.
- Multi-clause defn with NO self-call (`(defn add ([:Int x] x) ([:Int x :Int y]
  (add-i64 x y)))`) → `(add 3 4) = 7`. (Matches the passing e2e
  `tests/spec_05_definitions::defn_multi_clause_arity`, whose variants are all
  called from OUTSIDE, never from each other.)

So the defect is specifically: **a self-reference appearing inside a multi-clause
variant body is not lowered to the dispatched mangled symbol at codegen.** The
existing positive test does not exercise this because none of its variants call
the function.

## Proposed resolution

`/qa` authors a narrow failing (un-ignored) e2e repro reproducing
`undefined function: sum-to` (codegen) for a self-calling multi-clause defn, with
a `// spec:` annotation citing spec/05-definitions.md §5.1.2 and a
`// FIXME(/dev or /backend)` pointing at the resolver. Likely owner is the
multi-sig dispatch/mangling lowering at the `src/` codegen boundary (bare in-body
name → variant symbol) or the backend variant-symbol registration; the narrow
repro + `CRANELISP_CODEGEN_TRACE=1` on the shrunk form should localize it.

## Operational implication / Context

Surfaced while authoring the S89 Phase-6 agent primer (the combined
multi-signature + tail-recursive accumulator idiom the task requested). Because
the combined idiom does NOT compile, the primer documents the two refinements
separately with verified-compiling forms: the multi-signature special-form line
(non-self-calling) and a single-clause tail-recursive `sum-to` accumulator
(verified `(sum-to 5 0) = 15`). The combined idiom can be added to the primer
once this defect is fixed. This blocks a self-recursive multi-clause function —
a common shape (a public 1-arg entry variant delegating to a private
accumulator-carrying variant).
