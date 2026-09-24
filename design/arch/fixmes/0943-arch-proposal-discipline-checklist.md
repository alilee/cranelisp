---
number: 0943
target: /arch
filed_by: /sprint
filed_at: 2026-08-29
sprint_filed: 119
refers_to: design/arch/principles/21-actors-and-functions-before-mechanism.md;
  .agents/skills/arch/SKILL.md;
  .agents/skills/quality-standards/SKILL.md
status: open
---

# Proposal discipline: receiver-level checks before a proposal reaches the user

## The user's checklist (S69 Phase 3)

Run before an API-shaping proposal reaches the user:

1. **Data ownership.** A method belongs on the type holding its data. A
   parameter logically required to answer the question means the receiver is
   wrong: `Type::do_thing(&self, extra: &OtherType)` is really a question of
   the pair.
2. **Derive before adding.** Check whether existing receivers already answer
   the question before adding a field, accessor or layer. A proposed
   `param_names: Vec<Symbol>` duplicated `scheme.ty.fn_arity()`.
3. **Single responsibility.** An accessor answers one question from receiver
   data alone.
4. **Minimum mechanism.** A layer that carries no information is removed:
   `ModuleEntry::arity() → DefKind::arity(scheme)` added nothing over
   `scheme.ty.fn_arity()`.
5. **Trace consumer paths.** Two consumers reading `.len()` and `.is_empty()`
   want one `arity() -> Option<usize>`, not a `Vec` exposure. Derive the
   contract from read sites, not a field name.
6. **The spec owns language-level shapes.** For an AST, type, pattern or
   declaration shape, read `spec/` before source or design. A pattern-enum
   proposal once listed kinds §6.6.1–2 forbid.

The test: if a colleague reading cold asks "why does X take Y when Y is
already known?", each parameter needs an answer.

## Current state (verified 2026-09-24)

Principle 21 covers modelling actors and functions before a mechanism. The
shared `arch` contract covers callers, single data ownership, narrow consumer
facades and preferring an existing boundary over a new mechanism; the shared
quality standards cover cohesion and minimum mechanism. Items 1, 2, 5 and 6
are not stated at receiver level in any carrier.

## Remaining obligation

`arch` decides at the Phase 7 principle review whether the residual items
belong in Principle 21, a project procedural carrier or a shared-package
contribution. The examples illustrate the rule; they do not create a blanket
prohibition on methods taking other data. The user's local memory entry
"Proposal discipline" retires when this lands.

## Closure

The residual items are in their chosen carrier; this filing and the memory
retire.
