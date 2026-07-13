---
number: 0576
target: /spec
filed_by: /repl
filed_at: 2026-07-13
sprint_filed: 108
refers_to: multi-arity `defn` type inference across arity clauses. NORMATIVE
  ANSWER SETTLED (user, S108): alternative arities are type-checked
  INDEPENDENTLY; matching param identifiers across clauses are NO signal. So an
  unannotated clause is NOT inferred from a sibling annotated clause — the
  "ambiguous type" error is CORRECT. Remaining work is spec documentation +
  ambiguous-type diagnostic quality. Observed post-S108.
status: open
---

# Multi-arity `defn` arities are type-checked independently — SETTLED: not a defect; error-message quality only

## Issue

Two separate functions — an annotated indexed form and an unannotated natural
form delegating to it — compile. Merging them into one multi-arity `defn` (the
2-arg clause delegating to the 3-arg clause of the same name) fails in **both**
clause orders:

```
agent> /type (defn rp ([p rot] (rp p rot 0))
                     ([:Position p :Rotation rot :Int idx] (match rot …)))
Error: type error at 22..23: ambiguous type; add an annotation to pin the type of the polymorphic value bound in `rp`
```

The unannotated 2-arg clause's `p`/`rot` stay polymorphic.

## Resolution (SETTLED — no open normative question, NOT a defect)

**User ruling (S108): alternative arities must be type-checked INDEPENDENTLY;
similar param identifiers across clauses are NO signal.** The compiler does not
(and by design must not) propagate the annotated 3-arg clause's param types into
the unannotated 2-arg clause — matching the names `p`/`rot` is not evidence, and
the delegating call `(rp p rot 0)` does not back-flow types into the enclosing
clause's params. Therefore **the "ambiguous type" error is CORRECT behaviour**:
the 2-arg clause genuinely needs its own annotations. This is **not** an inference
defect — there is nothing to fix in typecheck.

Two follow-on tasks:

1. **/spec** — document that each arity clause of a multi-arity `defn` is
   type-checked independently and must carry its own annotations where inference
   can't pin its params; matching param identifiers across clauses carry no type
   information. This closes the expectation gap that made the agent (and user)
   read the error as a bug.
2. **/dev (typecheck, ambiguous-type diagnostic quality)** — the message points
   at `rp` (a 1-char span) and says "the polymorphic value bound in `rp`". It
   should instead name **which param** (`p`? `rot`?) in **which arity clause** is
   unpinned, and hint that that clause needs annotations. Same message family as
   **0568** (ambiguous-type / synthetic-binder wording) — fix together. This IS a
   defect (error quality) and warrants a `/testing` repro on the improved message.

## Notes

- This is the failure that **exhausted the agent's step budget** in **0577**
  (context tuning) — a clearer diagnostic (task 2) would have let the agent recover
  (annotate the clause, or fall back to two functions) instead of reordering
  clauses blindly.
- The correct authored form is: annotate the 2-arg clause too, e.g.
  `([:Position p :Rotation rot] (rp p rot 0))`. Worth a primer example (0577 C).
- Not a normative question anymore — the answer is recorded above; do not route to
  the user again.
