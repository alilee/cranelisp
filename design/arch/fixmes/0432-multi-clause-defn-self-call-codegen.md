---
number: 0432
target: /qa
filed_by: /dev
filed_at: 2026-06-22
sprint_filed: 89
refers_to: spec/05-definitions.md §5.1.2, spec/12-runtime.md §12.5, memory/s84-concrete-types-ambiguity-ruling.md
status: open
---

# Multi-clause `defn` with a self-call: two faces (codegen undefined-function + typecheck PANIC)

## Issue

A multi-signature (multi-clause) `defn` whose body recursively calls the
function itself — cross-variant or same-arity self-recursion — fails. **There are
TWO faces, distinguished by whether the variant params are `:Type`-annotated**
(both verified S89 Phase-6; symptom corrected from the original "undefined
function only" filing after `/sprint` reproduced the unannotated face):

**Face A — params `:Type`-annotated → CODEGEN `undefined function: <name>`.**
Typecheck succeeds (types pinned by the annotations); codegen does not resolve
the bare in-body name to the mangled variant symbol (`<name>$Params`). REPL and
`--run` both. Owner candidate: backend / `src/` codegen lowering (bare in-body
name → variant symbol) or backend variant-symbol registration.
```lisp
(defn sum-to
  ([:Int n] (sum-to n 0))
  ([:Int n :Int acc] (if (= n 0) acc (sum-to (- n 1) (+ acc n)))))
```

**Face B — params UNannotated → TYPECHECK `ambiguous type` + a monomorphiser PANIC (SEVERE).**
Without annotations the recursion's type can't be pinned → `type error:
ambiguous type … add an annotation to pin the type of the polymorphic value
bound in sum-to`, AND in the REPL this escapes into a **panic**:
`monomorphise.rs:1016 build_mangled_name(sum-to) saw a non-concrete param type
(lossy-name hazard — a spurious partial mono instance reached the mangler):
[Int, Var(62)]`. `--run` reports the ambiguous-type error cleanly (no panic).
A non-concrete type reaches the name-mangler instead of being caught as a clean
type error (relates to `s84-concrete-types-ambiguity-ruling`: typecheck must
produce ONLY concrete types; residual vars in codegen-reaching forms are clean
type errors, never a mangler panic). Owner candidate: typecheck monomorphisation.
```lisp
(defn sum-to ([n] (sum-to n 0))
             ([n acc] (if (primitives/eq-i64 n 0) acc
                          (sum-to (primitives/sub-i64 n 1) (primitives/add-i64 acc n)))))
```

Contrast — these WORK (verified S89 Phase-6):
- Single-clause tail-recursive accumulator: `(defn sum-to [n acc] (if (= n 0)
  acc (sum-to (- n 1) (+ acc n))))` → `(sum-to 5 0) = 15`.
- Multi-clause defn with NO self-call (`(defn add ([:Int x] x) ([:Int x :Int y]
  (add-i64 x y)))`) → `(add 3 4) = 7`. (Matches the passing e2e
  `tests/spec_05_definitions::defn_multi_clause_arity`, whose variants are all
  called from OUTSIDE, never from each other.)

So the defect class is: **a self-reference inside a multi-clause variant body is
mishandled** — either not lowered to the dispatched mangled symbol (codegen, Face
A) or allowed to escape ambiguity into a mangler panic (typecheck, Face B). The
existing positive test does not exercise it because none of its variants call the
function.

## Proposed resolution

`/qa` authors narrow failing (un-ignored) repros for BOTH faces, with `// spec:`
annotations citing spec/05-definitions.md §5.1.2 and `// FIXME(...)` pointing at
the resolver(s). **Face B's PANIC is the priority** — a typecheck panic on user
input is a robustness defect, and the agent's pre-flight validator (`--features
agent`) typechecks staged forms, so a model-proposed multi-clause self-call could
**panic-crash the REPL via the agent** (verify whether the S18/S19 REPL
panic-boundary contains it, or whether the agent validator needs a catch). Face A
likely localizes with `CRANELISP_CODEGEN_TRACE=1` on the shrunk form; Face B with
the monomorphiser assertion at `monomorphise.rs:1016`. Owners likely differ
(typecheck for B, backend/codegen for A) — the repros disambiguate.

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
