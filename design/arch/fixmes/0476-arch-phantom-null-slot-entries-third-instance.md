---
number: 0476
target: /arch
filed_by: /review
filed_at: 2026-07-03
sprint_filed: 101
refers_to: crates/cranelisp-backend/src/compiler/resolution.rs (resolve_vec_query_primitive), cranelisp-primitives::insert_vec_query_entries, design/backend/ownership-codegen.md §12.7, design/arch/principles/20-model-invariants-by-representation.md
status: deferred
deferred_to: increment I (ownership) — first change-sets, alongside the ModeSummary `cranelisp-types` surface
ruled: S101 Wave 5 (/arch, 2026-07-03) — see §Ruling below; cure shape settled, implementation pinned
---

# Allocated-but-NULL GOT slots are a recurring class — third instance; consider a representation-level cure

## Severity
Suggestion

## Issue

The S100/S101 vec-query NULL-slot SIGSEGV is the **third** instance of the
same structural class: an entry that participates in *name resolution* but
has no callable body reachable through its slot, dispatched through a
value-use path that assumes slot ⇒ callable.

1. FIXME 0354 — constrained templates holding phantom slots → cured
   *structurally* at S83 (kind⇔slot pairing: the template variant carries no
   slot field; the illegal pairing became unrepresentable — Principle 20).
2. Primitive constructors (`Some`/`None` bootstrap) → cured with an inline
   arm in `emit_wrapper_call` (the ctor precedent the §12.7 fix cites).
3. S101 — `vec-get`/`vec-set`/`vec-push`: `DefKind::Primitive { got_slot }`
   entries whose slot is allocated but **never stored** (no monomorphic
   extern body can exist), cured with a name-list resolver
   (`matches!(bare, "vec-get" | "vec-set" | "vec-push")`) + inline-emission
   arms at both wrapper seams.

Instance 3 reintroduces, one level down, exactly what S83 made
unrepresentable one level up: the *kind* says "slot-carrying callable", the
*representation* says NULL. Every consumer that learns
`callable_got_slot().is_some()` must now also know the name-list exemption
(currently: `emit_wrapper_call`, `emit_curry_target_call`; increment I adds
R2 wrappers + `str-len$borrowed` sibling targeting on the same seam). The
name-list is also stringly-typed dispatch (the `sketch/audits/module.md`
HIGH pattern) — correct today because it is single-sourced in
`resolve_vec_query_primitive`, but growth-prone.

## Proposed resolution

When increment I touches this seam anyway, evaluate a representation cure:
a `DefKind` shape for inline-only primitives that carries **no slot** (e.g.
`DefKind::PrimitiveInline`) or an explicit body-kind discriminator, so
"resolvable but not slot-callable" is a kind, not a name-list, and
`callable_got_slot()` returns `None` for them by construction (the S83
precedent applied one level down). Requires reconciling the reason the slots
were allocated at all (arity/name-resolution plumbing in
`insert_vec_query_entries`) and the persistence pins (slot numbers in
`.meta.json` — a removed slot allocation shifts none if these entries are
never persisted with meaning). If the survey shows the slot allocation is
load-bearing elsewhere, record the name-list as the settled convention in a
decision-log entry instead.

## Operational implication / Context

Filed per `memory/feedback_review_root_cause_and_duplication` (recurring
defect classes escalate to /arch). No urgency: the S101 fix is correct,
single-sourced, and green; this is about not paying a fourth instance when
increment I widens the seam. Natural slot: the increment-I `/arch`
change-set that already owns the ModeSummary/fact-table surface.

## Ruling (S101 Wave 5, /arch — cure shape settled; implementation pinned to increment I)

**The representation cure is ruled IN, not the decision-log fallback.** The
survey performed at ruling time confirms the NULL slots are NOT load-bearing:

1. **Why the slots exist**: `insert_vec_query_entries` allocates a slot for
   all four family members purely for shape-uniformity with
   `insert_primitive_entry` and so `callable_got_slot()` is `Some` — which is
   the **stop predicate** `resolve_driven`'s precedence walk uses. Only
   `vec-len`'s slot is ever stored (its extern shim). The slot's only real
   function for the other three is "participate in name-resolution
   precedence" — a *callability* fact being proxied through *slot presence*.
2. **Persistence pins**: none. The primitives table is statically
   reconstructed at every session start and never persisted; cached user
   `.o`s that embed primitives slot indices are guarded by the
   `compiler_mtime` wholesale-invalidation key, so a slot-numbering change
   across compiler builds is already covered. Removing three allocations
   shifts nothing that survives a session.

**Ruled shape** (Principle 20 applied one level down, the S83 precedent):

- `DefKind::Primitive`'s slot field becomes a two-armed **body/dispatch
  discriminator** in `cranelisp-types` (exact naming at the change-set; e.g.
  `PrimitiveBody::Extern { got_slot: usize }` vs `PrimitiveBody::Inline`).
  "Resolvable but not slot-callable" becomes a *kind*, not a name-list.
- `callable_got_slot()` returns `None` for the inline arm **by
  construction** — no consumer can dispatch GOT-indirect through a body that
  cannot exist. The inline arm still keys the backend's emitter choice by
  canonical bare name (that part of the S101 fix is sound — the defect class
  was slot⇒callable, never name-keyed emitter selection).
- The resolution **stop predicate moves from slot-presence to
  kind-callability**: a sibling accessor (e.g. `is_callable_target()`)
  covering slot-dispatched AND inline-dispatched kinds replaces
  `callable_got_slot().is_some()` at the `resolve_driven` stop condition, so
  shadowing precedence is unchanged. This is the one seam that must be
  reconciled carefully — the S101 `resolve_vec_query_primitive` name-list
  and both inline-emission exemption arms (`emit_wrapper_call`,
  `emit_curry_target_call`) then retire.
- Session-transaction knock-on (verified benign): `src/redefine.rs`'s §4.1
  slot-less pass-through keys off `callable_got_slot()` — an inline
  primitive correctly reads as slot-less there, and primitives are not
  redefinition targets, so no transaction-path change.

**Why pinned, not immediate**: the change is a `cranelisp-types` `DefKind`
reshape (baseline + `CACHE_SCHEMA_VERSION` cascade) touching the exact
wrapper/curry seams increment I's R2-wrapper + `str-len$borrowed` work
rebuilds anyway — landing it separately would pay the cascade twice
(Principle 8). `/arch` authors the types edit; `/dev` (backend, primitives
paired) consumes. This FIXME is the tracking item; it deletes when the
reshape lands.
