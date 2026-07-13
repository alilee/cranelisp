---
number: 0575
target: /spec
filed_by: /repl
filed_at: 2026-07-13
sprint_filed: 108
refers_to: `fn` special-form syntax — the parenthesised multi-arity clause form
  `(fn ([params] body) …)`. NORMATIVE ANSWER SETTLED (user, S108): anonymous
  `fn` does NOT support multiple arities; multi-arity is `defn`-only. Remaining
  work is spec documentation + parse-error quality. Observed post-S108.
status: open
---

# `fn` rejects the parenthesised (multi-arity) clause form — SETTLED: `fn` is single-arity by design

## Issue

An anonymous function written in the parenthesised-clause (multi-arity) shape
fails to parse, while `defn` accepts that shape:

```
agent> /type (fn ([:Position p :Rotation rot] (rotate-position p rot 0)))
Error: parse error at 0..60: fn requires param list and body
agent> /type (fn [p rot idx] (match rot …))         ; bare single-arity — OK
:(Fn [user/Position user/Rotation primitives/Int] user/Position)
```

## Resolution (SETTLED — no open normative question)

**User ruling (S108): anonymous `fn` does NOT support multiple arities.**
Multi-arity is a `defn`-only feature. The current behaviour (reject the
parenthesised multi-arity form for `fn`, accept it for `defn`) is **intended**,
not a defect. So the fn/defn asymmetry is by design.

Two follow-on tasks, both now unambiguous:

1. **/spec** — pin the rule in the `fn`/`defn` spec: `fn` takes a single
   `[params] body`; multi-arity (multiple `([params] body)` clauses dispatched by
   arity) is `defn`-only. Removes the ambiguity that let the agent probe this.
2. **/dev (frontend, parse-error quality)** — improve the diagnostic. "fn
   requires param list and body" misleads: it reads as if `fn` got no params,
   when the real issue is the *parenthesised multi-arity* form specifically. A
   better message names the constraint, e.g. "`fn` takes a single `[params]
   body`; use `defn` for multiple arities." This is a genuine error-quality
   defect and warrants a narrow `/testing` repro on the message.

## Notes

- One of the probes that made the agent flail in **0577** (context tuning) — a
  spec line in the primer (`fn` single-arity) would have prevented the probe
  entirely (0577 thread C: static syntax facts belong in the primer).
- Not a normative question anymore — do not route to the user again; the answer
  is recorded above.
