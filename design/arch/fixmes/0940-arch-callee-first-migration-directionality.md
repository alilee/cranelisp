---
number: 0940
target: /arch
filed_by: /sprint
filed_at: 2026-08-29
sprint_filed: 119
refers_to: .claude/commands/dev.md §Reporting ("Do not hand off to /sprint or
  /review with a broken build") — states the local rule with no cross-crate
  migration carve-out; no Principle covers migration directionality
status: open
---

# Migration directionality: callee → caller, and the broken build IS the checklist

## Issue

Nothing in `CLAUDE.md`, `sprints/METHOD.md`, `sprints/artefacts.md`,
`tests/CLAUDE.md`, `design/arch/principles/`, or any skill definition records how a
cross-crate migration is forced through the stack. The one adjacent statement —
`dev.md` §Reporting, "do not hand off with a broken build" — reads as the *opposite*
rule when applied to a migration wave, and there is no carve-out.

The discipline (user, S69, restated and enforced twice more in S73): push the **callee**
crate to its target surface FIRST, accept the broken build, and repair callers wave by
wave. Compilation errors are the migration checklist. There is no "should we?" question
when the target is grounded in a ratified decision — the migration IS the work; waves
exist for manageability, not re-litigation.

> "I am happy to push the public interfaces to the target state, see a broken build, and
> then have the consumers adapt to working. Previously, too much negotiation has resulted
> in the back-sliding we are seeing." — user, S69

The negotiation pattern looks innocent ("here are the options, which is right?") but
surfaces costs that justify deferral, lets each consumer crate argue for its preferred
shape, and compounds debt because each negotiation defers the same migration.

**The trap form** (S73 typecheck purge, corrected by the user twice in one sprint). A
recon agent inventorying `cranelisp-typecheck` flagged "deleting `register_builtins` is
BLOCKED — `int` still calls it." `int`'s call sites reached *around* typecheck's facade
to a severed legacy body. The user: *"the agent is getting confused by the fact that
callers of the crate are trying to reach around the public facade. Needs clear guidance
that we are forcing change through the stack from the callee then the caller."*
Separately, on holding `ensure_module_exists` and then `snapshot`/`restore` public
because `int` called them: *"int's use is not justification because we are rationalising
from callee to caller (bottom up). int not working is expected."*

The consequences worth stating explicitly, because each was gotten wrong at least once:

- A callee API with **no in-crate use**, kept only because a downstream caller calls it,
  is not justified by that caller. Dead-code warnings from the demotion are the SIGNAL
  that the API is purely caller-facing — proceed; do not revert to `pub` to silence them.
- A caller reaching around the callee's facade is not a blocker on the purge; it is
  precisely what the migration is forcing to change, and its repair is its own wave.
- Escalate to the user only a genuine shared-crate (`cranelisp-types`) structural
  requirement — never "the caller still needs the old surface."
- Don't conflate callee and caller responsibilities: typecheck-state rollback and
  codegen-failure rollback are separate concerns that don't fall together.

## Proposed resolution

`/arch` to decide the home. Two candidates: a new Principle (the content is a
directionality invariant on cross-crate change, sibling to Principle 8's
no-interim-implementations), or a section in `design/arch/bounded-contexts.md` on how a
boundary change propagates. Whichever home, `dev.md` §Reporting needs the carve-out
naming it, so a `/dev` agent in a migration wave is not blocked by the local
broken-build rule — that skill-def edit is the user's, so flag it for them if `/arch`
agrees the carve-out is needed.

Pairs with FIXME 0941 (the exit gate for the same cascade: `cargo check` green is not
the done-signal).
