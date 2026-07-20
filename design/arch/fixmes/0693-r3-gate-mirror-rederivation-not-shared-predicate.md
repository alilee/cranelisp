---
number: 0693
target: /dev
filed_by: /review
filed_at: 2026-07-20
sprint_filed: 114
refers_to: crates/cranelisp-backend/src/compiler/fn_compiler.rs::scrutinee_cow_retains_reused vs vec_codegen.rs::cow_source_ownership
status: open
---

# The R3 gate mirror re-derives the COW escape gate from the syntactic callee name instead of sharing the producer's discriminator (P7 mirror; latent UAF channel)

## Severity
Important

## Issue

`scrutinee_cow_retains_reused` (`fn_compiler.rs:1427-1450`) is documented as
"the dec side of the SAME escape gate" as `cow_source_ownership`'s
`retain_reused` (`vec_codegen.rs:648-665`) — and semantically it is (it is NOT
an MS-P7 compensation: no pointer-equality guard, no unconditional single-dec;
the fence-a discipline is honored). But implementation-wise it is a
**re-derivation, not a derivation**:

- The producer decides "this is the COW builtin" via the resolution carrier
  (`ResolvedCall::BuiltinFn` routing, `apply.rs:469` → `is_vec_primitive`) and
  reads the stashed `pending_cow_escapes`. The mirror re-derives it from the
  **syntactic callee name** (`matches!(callee_name.as_ref(), "vec-set" | "vec-push")`)
  and the raw `escapes` field — stringly-typed dispatch at a resolution seam,
  the `resolver-mirror` class, and contrary to the S110 keyed-consumer rule
  (backend consumes carriers, never re-resolves from names).
- The mirror adds a `self.variables.contains_key(src)` liveness condition the
  producer does not have (unreachable divergence today — there are no
  top-level heap value defs — but it is drift already).
- Concrete latent divergence: a user-defined fn literally named `vec-set`
  (legal under `PreludeVariant::None`; probed:
  `(defn vec-set [v i x] v)` + `(defn f [v] (match (vec-set v 0 5) [r r]))`)
  makes the mirror's name test TRUE while the producer never ran the COW gate.
  Today the observable behavior is identical to a differently-named control
  ONLY because typecheck records `escapes=Some(false)` on that scrutinee, so
  the mirror declines anyway. **When W7 corrects the escape-fact family
  (MS-P7/B-2 work), that mask can lift** — the mirror would then emit a
  balancing dec for a producer inc that never happened: spurious dec of a
  forwarded alias, the UAF direction.
- No unit fence pins producer/mirror agreement; the only fences are the
  committed family e2e twins, which cover only the enumerated shapes.

`design/backend/ownership-codegen.md` §13.7 records that /arch REJECTED
re-deriving the escape fact per-consumer (the R14 P7 ruling) — this mirror is
the same move one level up (re-deriving the *site classification* per
consumer).

## Proposed resolution

Make the pair structurally one gate: either extract ONE shared predicate both
sites call (parameterized by the operand + the escape fact), or have the
producer record its retain decision (beside `pending_cow_escapes` /
keyed by the Apply span) and have the match seam read THAT. Add a unit
disagreement fence: for each row of the §13.5-style matrix (builtin/user-named,
live/non-live source, escapes true/false/absent, return-source y/n, both
toggles) assert `mirror == producer-emitted-inc?`. Land with W-B5 or earlier;
must land before or with the W7 escape-fact correction, which is the event
that opens the masked channel.

## Context

Found by /review W4 (dispatch priority 2). Cite Principle 7 (single source of
truth) and Principle 24 (resolve once — name is trigger, carrier is identity).
