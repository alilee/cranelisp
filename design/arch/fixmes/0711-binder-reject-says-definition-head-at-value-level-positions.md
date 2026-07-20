---
number: 0711
target: /dev
filed_by: /docs
filed_at: 2026-07-20
sprint_filed: 114
refers_to: crates/cranelisp-frontend (qualified-binder reject message) + spec §5 wording (accuracy rider)
status: open
---

# Qualified-binder reject says "a definition head is a binder" even at value-level `let`/`match`/param positions

## Severity
Minor (usability finding — message accuracy)

## Issue

S114 (0670 / IQ-N) extended the qualified-name binder reject to **value-level**
binder positions — `let` bindings, `match` pattern binders, `fn`/`defn`
parameters. Probed at HEAD (`3cdd285c`):

```
user> (let [user/x 1] x)
Error: parse error at 6..12: 'user/x' is a qualified name, but a definition head is a binder and must be a bare (unqualified) name — write 'x' (a definition binds into the current module; use an import/qualified reference to reach another module)

user> (defn f [:Int m] (match m [user/x x]))
Error: parse error at 27..33: 'user/x' is a qualified name, but a definition head is a binder and must be a bare (unqualified) name — write 'x' (…)
```

The **remedy is correct** ("write `x`") and the reject is right. The wording is
what drifts: a `let`/`match`/param binder is **not** a "definition head", so a
newcomer who wrote `(let [user/x 1] …)` is told about a "definition head" that
does not match what they typed. The single message string is shared across all
binder positions but reads as head-specific.

## Suggested resolution

Generalise the message from "a definition **head** is a binder" to "this is a
**binder position** and a binder must be a bare (unqualified) name" (or branch the
noun by position: "definition head" / "let binding" / "pattern binder" /
"parameter"). Wording only — no semantic change. This pairs with the spec §5
binder-positions table (already aligned to the 0670 ruling in S114); a /spec
accuracy rider may be warranted if §5's prose still frames the reject as
head-specific.

## Why this reaches /docs

`user/errors/trait-impl-diagnostics.md` §"Qualified name in a binder position"
currently teaches the rule for **heads** only. Phase 6b widens it to state the
value-level positions (params/let/match) also reject. If the emitted message keeps
saying "definition head", the catalogue prose has to caveat the mismatch. A
generalised message lets the catalogue quote it cleanly for every position.

## Priority
Low. Does not block the Phase 6b catalogue widening (the catalogue can note the
wording). Polish for whenever the frontend touches the binder reject.
