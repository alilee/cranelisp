---
number: 0726
target: /qa
filed_by: /design (cranelisp-backend, S115 Phase 3)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: design/backend/binding-indirection-consume.md §2 (whole-match approximation); crates/cranelisp-backend/src/compiler/fn_compiler.rs::match_forwards_scrutinee; match_codegen.rs merge-block R3 suppression
status: open
---

# /qa matrix row for the mixed ctor+var match whole-match approximation (0697 follow-on)

## Issue

The R3 forwarding-suppresses-dec accounting uses a STATIC whole-match predicate
(`match_forwards_scrutinee` = ANY var-pattern arm forwards its binder) and emits
the scrutinee-dec suppression ONCE in the merge block. For a MIXED
constructor+var match whose var-default arm forwards the scrutinee —
`(match (norm o) [(None) (mk-default)] [x x])` — the suppression applies on ALL
paths, so a run that selects the CTOR arm never decs the consumed temp
scrutinee: a leak-safe (never UAF) residue. Recorded and polarity-argued in
`binding-indirection-consume.md` §2 (S115); the mechanism-complete alternative
(per-arm dec placement) is NAMED and PARKED. The parked boundary has NO test
fence — the leak is invisible to the both-polarity oracle.

## Proposed resolution

Add a /qa matrix row (and the /testing cells) over the mixed-arm shape:
mixed constructor+var match × {ctor-path selected, var-path selected} ×
{toggle-on, toggle-off}, asserting `allocs == deallocs` on each cell. This is
the tripwire the parked per-arm-dec-placement boundary needs: a future shape
whose ctor-path residue turns observable trips the fence and un-parks the
follow-on. No fix is owed now (the residue is O(depth), leak-safe); this is a
coverage fence only.

## Context

Filed to discharge FIXME 0697's second ask ("coordinate a /qa row for the
mixed-arm × {ctor-path, var-path} × toggle cells so the parked boundary has a
tripwire"). 0697's first ask (record the approximation in the design doc) is
DONE (`binding-indirection-consume.md` §2); 0697 deleted with the S115 design
touch.
