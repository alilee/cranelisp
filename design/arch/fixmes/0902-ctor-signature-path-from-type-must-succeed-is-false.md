---
number: 0902
target: /arch
filed_by: /design (backend)
filed_at: 2026-07-26
sprint_filed: 118
refers_to: design/arch/concrete-boundary-type.md §3.1.1 point 2;
  design/arch/bounded-contexts.md §3 invariant 9 (the STRUCTURAL END-STATE block);
  crates/cranelisp-backend/src/compiler/rc_emission.rs::signature_heap_category
status: open
---

# The ctor/accessor signature path's "`from_type` must succeed" premise is false — and the as-built has diverged since S84

## Issue

`concrete-boundary-type.md` §3.1.1 point 2 (FIXME 0393's resolution) rules that
the signature-driven ctor/accessor codegen path converts each field `Type` to a
`ConcreteType` and that the conversion

> **must succeed**: a codegen-reached ctor instance has fully concrete field
> types … A `from_type` failure here is therefore a compiler bug — the relocated
> `expect`/compiler-bug.

BC §3 invariant 9 restates it ("their field types convert via
`ConcreteType::from_type` at the `classify` call site, the `from_type` failure
being the relocated compiler-bug `expect`").

The premise does not hold, because **there is no such thing as a codegen-reached
ctor *instance***. A constructor `Def` is compiled **once per declaration** — the
generic template body itself is a codegen target — where a `UserFn` reaches
codegen only as a monomorphised concrete instance. Two legal declaration shapes
give that template a non-concrete field parameter:

- `(deftype (Option a) (Some [:a v]))` — the field parameter is the declared type
  parameter (this is the case `signature_heap_category`'s own rustdoc documents);
- `(deftype B (Mk [v]))` — an undeclared field, which typecheck leaves a free
  type variable; `B` is monomorphic, so no instantiation ever pins it.

Both are valid source, so an `expect` on this path would be a compiler-bug abort
on a legal program.

The as-built already diverges from the ruling and has since S84:
`rc_emission::signature_heap_category` maps the `from_type` `Err` arm to
`HeapCategory::Mixed` (the uniform-i64 category) rather than `expect`ing, and its
rustdoc attributes the gap to FIXME 0394 — which was **closed at S84**
(`09d91719`) on a different axis (the `codegen_view` population). So the
divergence has never been reconciled with the doc, and the number the code cites
as its owner no longer exists.

This surfaced concretely in S118 W3: making `emit_heap_binding_decs`
type-directed produced `release site in 'B.Mk' reached a non-concrete type
Var(0)` on the 0810 control program. `/design`(backend) ruled the release side in
`design/backend/transitive-drop-glue.md` §4.1 (the case is sanctioned, with an
invariant and a frame-scoped check; FIXME 0891 carries the `/dev` residual). The
*classification* side is upstream of that ruling and is `/arch`'s.

## Proposed resolution

`/arch` reconciles §3.1.1 point 2 and BC §3 invariant 9 with what the model
actually is:

1. Distinguish the ctor **template** (compiled once per declaration,
   signature-typed, may carry a non-concrete field type) from a ctor **use site**
   (`(Some 1)`, inlined in the caller's frame with `a := Int` pinned, always
   concrete). The current text conflates them under "instance".
2. Replace the "must succeed / compiler-bug `expect`" clause for the template
   path with the as-built and now-ruled position: a residual field type on the
   ctor template classifies `Mixed` (uniform i64) for RC purposes, and the ONE
   release site this reaches is bounded by `transitive-drop-glue.md` §4.1's
   frame-checked admission. The "no `Var` reaches `classify`" totality claim
   needs the same amendment — on the template path the conversion is total by
   *classification*, not by concreteness.
3. Decide whether §3.11.1's full-concreteness verdict is intended to reject an
   undeclared `deftype` field at declaration time. If yes, that is a `/spec` +
   typecheck question and would remove one of the two shapes (never the generic
   one); if no, say so, because the current text reads as though it already does.
4. Give the residual a live owner. `signature_heap_category`'s rustdoc, the
   `emit_heap_binding_decs` comment and `crates/cranelisp-backend/CLAUDE.md` all
   cite closed FIXME 0394; FIXME 0891 re-points them at §4.1, but the
   *classification* rule needs a canonical home in the arch set, not a backend
   comment.

No implementation is requested by this FIXME — the backend's behaviour is
unchanged and ruled. What is requested is that the arch set stop asserting a
premise the compiler falsifies, since `/dev` and `/review` read §3.1.1 and BC §3
invariant 9 as binding.

## Context

- Filed at the S118 0891 ruling by `/design`(backend); narrow-deployment forbids
  editing `design/arch/`.
- Numbering: max existing file was 0900; 0901 was drained earlier this sprint, so
  this takes 0902 rather than reusing a just-deleted number.
