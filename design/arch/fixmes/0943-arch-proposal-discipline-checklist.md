---
number: 0943
target: /arch
filed_by: /sprint
filed_at: 2026-08-29
sprint_filed: 119
refers_to: design/arch/principles/21-actors-and-functions-before-mechanism.md —
  covers modelling actors before synthesising a mechanism, but not the
  receiver-level checks that shape the resulting API
status: open
---

# Proposal discipline: data ownership, derive-before-add, minimum mechanism

## Issue

Principle 21 requires an actor/function model before a mechanism is synthesised. It says
nothing about the shape of the API that comes out the other side, and that is where a
recurring class of sticking-plaster proposals lives. A grep over `design/arch/principles/`,
`sprints/METHOD.md` and `.claude/commands/` for "receiver", "data owner", "minimum
mechanism", and "single responsibility" finds nothing on point.

The checklist (user, S69 Phase 3), to be run before a proposal reaches the user:

1. **Data ownership.** Methods belong on the type that holds the data. If a method needs
   data passed in from outside, the receiver is wrong. The smell is
   `Type::do_thing(&self, extra: &OtherType)` where `extra` is logically required to
   answer the question — that is `(Type, OtherType)::do_thing()`, not `Type::do_thing()`.
2. **Derive before adding.** Check whether the answer is already reachable from existing
   receivers before adding a field, accessor, or layer. A `param_names: Vec<Symbol>`
   addition was proposed when `scheme.ty.fn_arity()` already had the answer.
3. **Single responsibility.** An accessor answers one question from receiver data alone.
   If it answers several, or needs threading, decompose.
4. **Minimum mechanism.** Don't add layers that carry no information. The delegation
   chain `ModuleEntry::arity() → DefKind::arity(scheme)` adds nothing over
   `ModuleEntry::arity() → scheme.ty.fn_arity()`; the middle layer is mechanism without
   payload.
5. **Trace the actual consumer paths.** Two consumers reading `.len()` and `.is_empty()`
   on a `Vec<Symbol>` want one `arity() -> Option<usize>`, not a Vec exposure. Don't
   infer the contract from a field's name — trace it from the read sites.
6. **The spec is the data owner for any language-level construct.** For an AST type,
   type-system type, pattern, or declaration shape, check `spec/NN-*.md` before source or
   design doc. A pattern-enum proposal once listed "literal / var / wildcard / constructor
   / nested" when §6.6.1–2 explicitly forbid literal and nested patterns and §6.2
   normatively lists three kinds — the source matched the spec and the design doc was
   wishful thinking about a forbidden feature.

The triggering exchange:

> "I'm not getting enough discipline from the recommendations — so many sticking-plaster
> solutions that don't bear much scrutiny. It's like the suggestions aren't considering
> the solution context but also aren't considering basic technical disciplines. E.g. why
> is scheme passed in to DefKind::arity?" — user, S69

That parameter was the tell that `DefKind` did not own the arity data. The general test:
does the proposal still hold if a colleague reads it cold and asks "why does X take Y as
a parameter when Y is already known?" If you cannot justify each parameter, the shape is
wrong — and if the discipline check produces a smaller proposal than the pattern-matched
first draft, the first draft was the sticking plaster.

## Proposed resolution

`/arch` to rule on the home. Candidates: an extension to Principle 21 (same axis —
Principle 21 governs whether the mechanism is right, this governs whether its API shape
is), or a new Principle, or a checklist section in `.claude/commands/arch.md` §Workflow
if `/arch` judges it procedural rather than architectural. If it lands as a Principle,
`design/arch/principles/CLAUDE.md` steps 1–3 apply: index entry plus the four import blocks (arch
and the three triad skill defs) — that skill-def edit is the user's, so flag it in the
resolution commit for `/sprint` to chase.
