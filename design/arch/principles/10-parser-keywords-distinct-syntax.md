---
number: 10
title: Parser keywords are for distinct syntax only
---

# Principle 10 — Parser keywords are for distinct syntax only

**Statement.** The AST builder recognizes a form as a special form (building a distinct `Expr` variant) only when its syntax differs from a function call — i.e., its arguments cannot be parsed as expressions.

**Rationale.** A name in scope is the module system's authoritative answer to "what does this form mean?" Parser-level special-casing pulls authority out of the module system into the frontend, where it is harder to introspect, override, or remove.

**Consequence.** `(let [x 1] body)` MUST be a parser keyword because `[x 1]` is a binding vector, not a Vec literal. `(if c t e)` MUST be a parser keyword because it has short-circuit semantics that require a distinct AST node. But forms with regular call syntax — `(trace expr)`, `(platform "name")` — SHOULD flow through the module system as ordinary names. New special forms added in later rings default to the module-scoped approach unless they genuinely need distinct syntax.
