---
number: 0904
target: /dev (backend)
filed_by: /review (backend)
filed_at: 2026-07-26
sprint_filed: 118
refers_to: crates/cranelisp-backend/src/compiler/rc_emission.rs::signature_heap_category (rustdoc)
status: open
---

# `signature_heap_category` rustdoc repeats the falsified one-case premise and calls the live gate FRAME-keyed

## Severity
Important

## Issue

Commit `ee324bc4` re-pointed this rustdoc's stale FIXME-0394 citation at
`transitive-drop-glue.md` §4.1 — correct — but left (and in one place added)
two claims the SAME commit's own census falsifies:

1. **"a `Var` legitimately survives there in ONE case: a constructor `Def`'s
   own template codegen"** (and the `Err`-arm gloss "a ctor-template field
   param"). The 0903 measurement establishes at least THREE families of
   residual signature types reach this classification: the ctor template's
   parameter (sanctioned, I-CT), synthetic field accessors of a
   generic/undeclared-field product (`Box.v`'s `self: ADT(user/Box,
   [Var(0)])`), and generic trait-method instances
   (`Functor.fmap$primitives/Option`'s `Fn([Var(9)], Var(8))`). Unlike the
   `emit_heap_binding_decs` rustdoc and the crate `CLAUDE.md` — which carry
   the full census with the do-not-re-run warning — this rustdoc gives a
   reader the falsified premise as current fact, with no nearby correction.

2. **The new closing paragraph says the release-legality question is "a
   separate, FRAME-keyed question answered once at
   `fn_compiler::emit_heap_binding_decs`."** The live gate at that seam is
   TYPE-keyed — knowingly, per the same commit (FIXME 0903; 0891 deferred).
   "FRAME-keyed" describes the §4.1 design intent, not the shipped state; a
   reader of only this rustdoc would believe the frame gate landed.

Principle 7 (Single source of truth): the census's authoritative home is the
`emit_heap_binding_decs` rustdoc + crate `CLAUDE.md`; this rustdoc contradicts
rather than defers to it. Principle 26 (Record from settled state): the "ONE
case" premise was measured false before this text shipped.

## Proposed resolution

Doc-only edit, no emission change: (a) restate the ctor template as the only
*sanctioned* family while acknowledging the helper currently classifies all
three measured families (or simply defer to the census at
`emit_heap_binding_decs`); (b) replace "FRAME-keyed" with wording true at
HEAD — the legality question is answered once at `emit_heap_binding_decs`,
whose gate is knowingly type-keyed pending FIXME 0903's ruling.

## Context

- Surfaced by the delegated Codex review of `ee324bc4` (S118); finding 1
  verified by the adjudicator; the FRAME-keyed misstatement (point 2) is an
  adjudicator addition found during verification.
- If the 0903 ruling lands in S119 and the frame key is re-landed, point 2
  self-heals — but point 1's family census stays wrong under any ruling that
  doesn't make the signature path concrete.
