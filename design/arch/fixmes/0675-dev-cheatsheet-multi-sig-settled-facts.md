---
number: 0675
target: /dev
filed_by: /repl
filed_at: 2026-07-19
sprint_filed: 113
refers_to: src/syntax/cheatsheet.txt (src/-owned) — the `defn-multi-sig` topic
  (currently ~lines 24-44); folds FIXME 0577 thread C (settled facts 0575/0576)
  into the static primer per the static-syntax→primer home rule
status: open
---

# Fold two settled multi-sig facts into the `defn-multi-sig` cheatsheet topic

FIXME 0577 thread C: the static language primer should pre-answer the agent's
syntax needs so it does not burn probe calls on settled facts. Two settled facts
are absent from the `defn-multi-sig` cheatsheet topic — `/repl` specifies the
exact lines (per the static-syntax→primer home rule); `/dev` applies the src/
edit.

**Facts** (both settled, cited):
- **0575** — `fn` is single-arity; multi-arity is `defn`-only.
- **0576** — multi-arity `defn` clauses type-check **independently**; each needs
  its own annotations, and a param name shared across clauses is **no signal**
  (matching names carry no shared type).

**Exact insertion** — add this block to the `=== topic: defn-multi-sig ===`
entry, immediately **after** the `EXAMPLE` block and **before** the `NOT` block:

```
  INDEPENDENT
    Each variant type-checks ON ITS OWN — a variant needs its own annotations.
    A param NAME shared across variants carries no shared type (matching names
    are not a signal). `fn` is SINGLE-ARITY; multi-arity lives only in `defn`.
```

Leave the existing `FORM`, `EXAMPLE`, `NOT` (`... wrap in (fn ...)`), and
`SPEC 05 §5.1.2; 04 §4.7` lines unchanged — the new block is consistent with
them (the `NOT` line's single-value `fn` wrap now reads correctly against
"`fn` is single-arity"). The primer one-liner (`src/agent/primer.txt`
"multi-signature: variants dispatched on arg types/arity") needs no change.

Closure: the block lands in `cheatsheet.txt` → delete this file. (No test owed —
this is static primer content; the thread-D per-sprint gap loop, spec §17.20.3c,
continues to mine the `question` log for further gaps.)
