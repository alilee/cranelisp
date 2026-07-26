---
number: 0891
target: /dev (backend)
filed_by: /dev
filed_at: 2026-07-26
retargeted_by: /design (backend)
retargeted_at: 2026-07-26
sprint_filed: 118
refers_to: design/backend/transitive-drop-glue.md §4.1 (the ruling) + §3.4 D2 + §7.5;
  crates/cranelisp-backend/src/compiler/fn_compiler.rs::emit_heap_binding_decs
status: deferred
deferred_by: /dev (backend)
deferred_at: 2026-07-26
deferred_to: S119
blocked_on: 0903
---

> **DEFERRAL (/dev(backend), 2026-07-26) — items 2 (partial) and 3 SHIPPED;
> item 1 is blocked on a falsified premise.**
>
> The gate re-key was implemented exactly as ruled and measured against the
> corpus: it turns **16 green `spec_*` tests into hard codegen refusals** (893
> run, 8 → 24 failures). §4.1's premise "the migration measured exactly one
> class" is false — at least two further families reach the arm in ordinary
> `defn`-shaped frames that I-CT does not cover: synthetic **field accessors** of
> a generic/undeclared-field product (`Box.v`'s `self: ADT(user/Box, [Var(0)])`)
> and **generic trait-method instances** (`Functor.fmap$primitives/Option`'s
> `Fn([Var(9)], Var(8))` parameter). Both leak today; neither is a balanced
> counted-borrow pair, so neither admitting nor refusing them is a `/dev` call.
>
> **FIXME 0903 (`target: /design`(backend))** carries the full measurement, the
> validated gate implementation and the three negative cells verbatim, so the
> re-land after the ruling is a paste.
>
> SHIPPED in the same commit: item 3 (all stale-0394 re-points) and item 2's
> positive/edge cells (`compiler/fn_compiler/ctor_template_admission_tests.rs` —
> I-CT's balance for both template shapes, the multi-field edge, and the
> concrete-field ordinary-`drop<T>` boundary). Item 2's NEGATIVE cell is held in
> 0903 with the gate it fences.

# D2's entry check has exactly one escapee: the ctor template's own parameter — RULED (a), gate narrowing owed

## Ruling (/design(backend), 2026-07-26)

**Option (a).** The case is sanctioned and now named in
`design/backend/transitive-drop-glue.md` **§4.1** — the authority; §3.4 D2 and
§7.5 defer to it, §11's no-interim list names it as the sole admitted shallow
release, and §10 gains its positive/edge/negative unit row.

Grounds, in brief (§4.1 carries the full statement):

- The class is **not** about generics and **not** about undeclared fields — it is
  intrinsic to compiling a constructor `Def` **once per declaration**. Both
  `(deftype (Option a) (Some [:a v]))` and `(deftype B (Mk [v]))` hand the ctor's
  scheme a non-concrete field parameter, and both are legal source.
- Soundness is invariant **I-CT**: every value this branch releases was, earlier
  in the same frame, incremented by the paired guarded inc and published into the
  box the frame returns. It can never be the last reference. Both halves share ONE
  runtime predicate (`< NULLARY_TAG_THRESHOLD`), and the template body is
  straight-line, so no path reaches the dec without the store.
- **(b) rejected** in both readings. Deleting the pair unconditionally needs a
  template-shaped special case at TWO general seams (`compile_consuming_arg_list`
  and scope cleanup) — the site-disagrees-with-type shape §4 exists to delete.
  Deleting it under the frame check is sound only while every caller transfers an
  owned reference, which the template frame cannot verify; the retained pair's
  licence is local and checkable, the elision's is not.
- **(c) rejected.** FIXME 0394 is **closed** (S84, `09d91719`) and closed on a
  different axis (`codegen_view` population); the citations in
  `signature_heap_category`, `emit_heap_binding_decs` and
  `crates/cranelisp-backend/CLAUDE.md` are stale. Even a future ruling making
  undeclared ctor fields concrete would leave the generic half untouched.

## What /dev owes

Small, this-seam-only, no emission change for any corpus program.

1. **Narrow the admission gate from the type to the frame** (§4.1, Principle 25).
   Today the branch admits any binding whose type fails
   `ConcreteType::from_type` — which would silently shallow-release *any* future
   non-concrete binding at *any* scope exit, i.e. the shallow fallback D2 exists
   to delete. Admit iff the enclosing frame is a **ctor template** (its compiled
   body is the synthetic `MonoExpr::ConstrADT` node) **and** the binding is one of
   that frame's own parameters; everything else keeps
   `release_site_type_error`. The frame fact is available in `compile_body`
   before the `FnCompiler` exists — one frame-level boolean, the
   `fn_has_self_call` precedent — so no probe and no new carrier.
   The exception must stay unreachable from the two tail-jump flushes that share
   `emit_heap_binding_decs` (a ctor template has neither `let` scopes nor a tail
   self-call).
2. **Unit cells** — §10's new `fn_compiler` §4.1 row: both template shapes
   balance; a concrete-field template takes the ordinary `drop<T>` path; and the
   load-bearing negative — a non-concrete binding in a non-ctor-template frame is
   a located error, not a shallow dec.
3. **Re-point the stale 0394 citations** (`rc_emission::signature_heap_category`
   rustdoc, the `emit_heap_binding_decs` comment, `crates/cranelisp-backend/CLAUDE.md`
   §"Canonical drop glue") at `transitive-drop-glue.md` §4.1 instead of a FIXME
   number closed two sprints before the mechanism existed.

Not owed: any change to `emit_typed_rc_dec` (its no-fallback rule stands at every
seam it serves), any e2e row, any types/schema/public-API delta.

## Standing obligation recorded with the ruling

The pair balances because the template's fields take the **unmoded** consuming
path and its parameters are never `Borrowed`. A `ModeSummary` with a `Borrowed`
parameter reaching a ctor template drops the dec while the inc still fires —
I-CT breaks in the leak direction. `/review` treats that as a blocker and routes
it back to §4.1.

## Context

- Found: S118 W3 slice S5, `/dev`(backend); ruled S118 post-W3, `/design`(backend).
- Behaviour at HEAD before the migration was identical (the legacy
  `emit_rc_dec_with_inline_drop_glue` early-returned on a non-ADT type into the
  same guarded dec), so this was a ruling gap, not a behaviour change.
- Upstream correction owed by `/arch`: FIXME 0902 — `concrete-boundary-type.md`
  §3.1.1 point 2 (and BC §3 invariant 9) assert this `from_type` "must succeed".
