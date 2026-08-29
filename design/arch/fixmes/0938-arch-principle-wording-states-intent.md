---
number: 0938
target: /arch
filed_by: /sprint
filed_at: 2026-08-29
sprint_filed: 119
refers_to: design/arch/principles/CLAUDE.md — covers filing/import/retirement
  mechanics for a Principle but says nothing about how its wording is derived
status: open
---

# Principle-authoring convention: the wording states INTENT, never verified against the implementation

## Issue

`design/arch/principles/CLAUDE.md` is complete on the *mechanics* of a Principle —
how to file one, the four import blocks that must carry it, how to retire it. It is
silent on the one rule that determines whether the wording is any good.

The rule (user, S110, at the Principle 24 "Resolve once" ratification): a Principle's
wording is a statement of **intent**. Decide what the architecture SHOULD guarantee,
then state it. Do **not** verify the proposed wording against the current
implementation first — any place the code violates the Principle is probably one of
the mistakes the Principle exists to eliminate, so an implementation deviation is an
instance of the defect class the Principle NAMES, never counter-evidence against the
wording. Enforcement (sweeping for violations) is a stated follow-up consequence, done
later, not an input to the wording.

The generalising move from the same session, worth recording as the method: the user
pushed Principle 24 from a backend-scoped "keyed read vs search" to a compiler-wide
invariant by asking **"all searches are suspect — can we name one search that is
valid?"** For compile-necessary identity the answer is none; what looks like the
exception (the import chain) is a bounded, deterministic sequence of keyed lookups
following explicit pointers, not a search. The resulting acid test — **does the answer
depend on incidental order (hash, insertion, directory)? then it is a scan, and it is
a defect** — plus the two carve-outs (enumeration, and human-facing REPL discovery)
is already in Principle 24's own text, but the *move that produced it* is not
recorded anywhere as a repeatable technique.

Why this matters beyond one Principle: a Principle checked against the code inherits
the code's mistakes; a Principle derived from intent becomes the yardstick that
condemns them. This survives only as a cross-workstation memory today.

## Proposed resolution

Add a short section to `design/arch/principles/CLAUDE.md` — "How a Principle's wording
is derived", alongside the existing "When you author a new Principle" mechanics —
stating: (1) the wording states intent, and is not checked against the current
implementation; (2) an implementation deviation is an instance of the class the
Principle names, and the compliance sweep is a follow-up, not an input; (3) the
strengthening question to ask at a ratification gate ("can we name one valid instance
of the thing we are calling suspect?"), with the Principle 24 derivation as the
worked example.

`/arch` owns the judgement of where exactly this sits — the alternative home is
`.claude/commands/arch.md` §Sprint participation, where the Phase 7 principle review
happens. One home, not both.
