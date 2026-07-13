---
number: 0583
target: /arch
filed_by: /sprint
filed_at: 2026-07-13
sprint_filed: 109
scheduled: S110 (CENTREPIECE — user directive, S109 P5)
refers_to: the compiler-wide resolution boundary — the backend (`cranelisp-backend`)
  runs a full name resolver (`resolution.rs::resolve_driven` + ~10 `resolve_*`
  entry points) instead of receiving fully-qualified symbols from typecheck. Root
  of the recurring "two resolvers, one name" mirror class (3× in S109 alone).
status: open
---

# S110 CENTREPIECE — backend is a pure keyed-lookup consumer; typecheck emits FQ SYMBOLS and FQ TYPES on all mono-view references; ZERO backend name/type resolution

## The principle (user, S109 P5)

**The backend should receive fully-qualified SYMBOLS *and* fully-qualified TYPES,
and do keyed lookups only — zero ambiguity, no resolver, no scan, no precedence
walk, no bare-type-name resolution in the backend.** Resolution (of both names and
type identity) is typecheck's job; the backend re-deriving either is a
bounded-context boundary violation and the structural cause of the recurring mirror
class.

**Two axes, same boundary:**
- **FQ symbols** — values / functions / constructors / effects / externs. Covered by
  the `resolve_driven` evidence below.
- **FQ types** — type identity is nominal and fully-qualified (spec §3.8.4:
  `primitives/Option` ≠ `fn.option/Option` though they share the bare name). The
  backend consumes type identity for heap layout, ADT tags, drop-glue, and the
  schema layout-hash (`schema.rs`); wherever it resolves or keys on a **bare** type
  name instead of an `FQTypeName` carried from typecheck, it is the SAME mirror class
  on the type axis. The `FQTypeName` type already exists in `cranelisp-types` — the
  initiative makes it the ONLY form the backend ever sees (audit the mono view +
  backend for any bare-type-name resolution/keying and FQ-ize it).

## Evidence (gathered S109 P5, `/sprint`)

The backend exposes **ten resolver functions** in
`crates/cranelisp-backend/src/compiler/resolution.rs`, all routing through
`resolve_driven` (current-module → qualified → **arbitrary-order global
`symbol_tables.iter()` scan**, first-hit-wins, no multi-hit guard):
`resolve_got_target`, `lookup_constructor`, `resolve_func_arity`,
`resolve_is_callable_target`, `resolve_callee_summary`,
`resolve_platform_effect_target`, `resolve_poll_effect_target`,
`resolve_extern_target`, `resolve_vec_query_primitive` (+ `resolve_chain`).
Callers across `apply.rs`, `literals.rs`, `match_codegen.rs`, `context.rs`. Each
takes a **source-written `name`** off the mono/codegen view and **re-resolves it**
— the backend runs its OWN precedence rules that must agree with typecheck's.

**The mirror class has surfaced 3× in S109**, all this root: (1) backend one-hop
`lookup_constructor` vs multi-hop `resolve_driven` (W1 commit-1 cure); (2) the
silent nullary-ctor closure-alloc-vs-tag split (W1); (3) DC-11 scrutinee-directed
patterns — typecheck resolves canonically, backend re-resolves the bare name
context-free via the arbitrary-order scan → silent wrong-ctor codegen + run-to-run
NONDETERMINISM (W1.2 / §10 cure).

## Why it's tractable (not new logic — plumbing)

Typecheck **already computes** the FQ resolution for every reference (it must, to
type the call/ctor/effect). The FQ symbol is KNOWN at typecheck time; the backend
re-derives it only because the mono view records the SOURCE name, not the RESOLVED
FQ. So the fix is: record the already-computed FQ on the mono node, backend does
`tables.get(fq.module).get(fq.symbol)`, delete `resolve_driven` + the scan.

**S109 `§10` (`design/arch/dotted-ctor-canonical-keys.md`) is the worked TEMPLATE**
for one reference kind (patterns): `resolved_ctor: Option<FQSymbol>` on the mono
arm → keyed read → hard-`CodegenError` on miss (Principle 18, no fallback).

## The initiative (for `/arch` to design + phase, S110)

1. **Principle**: record in `design/arch/` — "the backend is a pure keyed-lookup
   consumer; typecheck emits FQ SYMBOLS and FQ TYPES on every mono-view reference;
   the backend performs ZERO name resolution and ZERO bare-type-name resolution."
   (Realizes the backend's own stated aspiration — its CLAUDE.md claims "no trait
   knowledge, one dispatch path," contradicted by the live resolver.)
2. **Phased execution**, one reference-kind per wave, each following the `§10`
   template (resolved-FQ on the mono node → keyed read → loud-miss):
   - *Symbol axis*: call targets (highest-traffic, `resolve_got_target` — start
     here), constructors (ctor construction — patterns done in `§10`), effect/extern
     targets, arity/callable/callee-summary, vec-query. Each wave deletes one
     resolver and its scan reach.
   - *Type axis*: audit the mono view + backend (`schema.rs` layout-hash, ADT
     tag/layout, drop-glue, `heap.rs`) for any bare-type-name resolution or keying;
     ensure every type reference carries `FQTypeName` from typecheck and the backend
     keys on it directly.
3. **End state**: `resolve_driven` + the `symbol_tables.iter()` scan DELETED;
   backend name-resolution AND bare-type-resolution surface is zero; `FQSymbol` /
   `FQTypeName` are the only reference forms the backend ever sees.

## Notes — `/audit` calibration finding (user, S109 P5)

**This boundary violation was MISSED by `/audit`** — the whole-context assessments
(incl. `cranelisp-typecheck-s108`, `cranelisp-backend-s107`) never surfaced that
the backend runs a full name resolver duplicating typecheck. A major bounded-
context boundary issue invisible to the rolling audit is an audit-coverage gap:
whole-context assessment should flag cross-context responsibility leaks (resolution
living in the wrong crate), not only within-crate state. Recommend: (a) pull
`cranelisp-backend` + the resolution seam forward in the audit rotation for S110;
(b) `/audit` process adds a "bounded-context responsibility boundary" lens (does
this crate do work that belongs to another context?). Recorded in the S109
outcome for the Phase-7 audit-calibration review.

## S109 disposition (interim)

`§10` (pattern FQ-ization) lands in S109 as the first increment + the Blocker fix.
The residual value-position scan stays (currently safe by the typecheck-poison
invariant — contested bare names poisoned upstream before backend); it is
subsumed and DELETED by this initiative. No interim guard added (the path is
currently safe and the initiative removes it wholesale next sprint).
