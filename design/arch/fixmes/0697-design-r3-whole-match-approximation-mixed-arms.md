---
number: 0697
target: /design
filed_by: /review
filed_at: 2026-07-20
sprint_filed: 114
refers_to: design/backend/binding-indirection-consume.md §2 (match-forward row) vs fn_compiler.rs::match_forwards_scrutinee
status: open
---

# R3 classifies forwarding whole-match, but §2 defines it per SELECTED arm: mixed ctor+var matches leak on the non-forwarding path (undocumented approximation)

## Severity
Suggestion

## Issue

The contract's §2 table keys forwarding on "the **selected** arm" — a runtime
notion. The implementation (`match_forwards_scrutinee`, `fn_compiler.rs:298`)
is a static whole-match predicate (ANY var-pattern arm that forwards its
binder), and the R3 suppression is emitted once in the merge block
(`match_codegen.rs:180-183`). For a **mixed** constructor+var match whose
var-default arm forwards the scrutinee — a legal, idiomatic shape, e.g.
`(match (norm o) [(None) (mk-default)] [x x])` — the suppression applies on
ALL paths, so a run that selects the ctor arm never decs the genuinely
consumed temp scrutinee: leak. The same any-arm approximation feeds
`operand_live_binding_root`'s Match row, whose consumers (R1/R2) also err
leak-direction on the non-forwarding path (analyzed, not probed). Both errors
are leak-safe (never a dec added), which is the right polarity — but:

- the code comment ("a mixed constructor+var match is out of the acceptance
  set") is the only record; the design doc does not state the approximation,
  its polarity argument, or the mechanism-complete alternative (per-arm dec
  placement — move the temp-dec into the non-forwarding arms before the merge
  jump);
- no /qa matrix row covers the mixed-arm cell, so the leak is invisible to
  the both-polarity fence.

## Proposed resolution

/design: record the whole-match approximation in
`binding-indirection-consume.md` (with the leak-safe polarity argument) and
name per-arm dec placement as the follow-on if a real shape forces it —
"document movable boundaries decisively, then park." Coordinate a /qa row for
the mixed-arm × {ctor-path, var-path} × toggle cells so the parked boundary
has a tripwire.

## Context

Found by /review W4 (dispatch priorities 1/5). Pre-W4 the same mixed shape
was UAF-direction on the var-arm path (the dec fired on a forwarded value),
so the approximation is a strict improvement; this FIXME is about recording
it and fencing it, not reverting it.
