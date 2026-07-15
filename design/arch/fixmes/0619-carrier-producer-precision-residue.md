---
number: 0619
target: /dev
filed_by: /review
filed_at: 2026-07-15
sprint_filed: 110
refers_to: crates/cranelisp-typecheck/src/program/callees.rs (builtin_storage_fq, resolved_call_to_fqsymbol), crates/cranelisp-typecheck/src/checker.rs (record_reference_target), crates/cranelisp-typecheck/CLAUDE.md
status: open
---

# 0583 carrier producer — three precision residues + one doc drift (typecheck)

## Resolution status (S110 W0.b, /dev)

- **Item 1 (Important) — LANDED.** `builtin_storage_fq` (`callees.rs`) now
  kind-gates the scope probe: it grounds the builtin FQ only when the terminal
  `Def` is `Primitive`/`PrimitiveExtern`, else falls through to the `primitives`
  default. Pin: `program::tests::resolved_target_builtin_fq_ignores_shadowing_user_fn`.
- **Item 3 (Minor) — LANDED.** The AutoCurry plain-arm callees edge in
  `resolved_call_to_fqsymbol` no longer records `{current_module, target}`
  (wrong home for an imported target); it records NO edge from that path —
  the correct edge lands via `user_fn_refs` (the callee `Var` recorded at
  `infer_var` with the terminal storage home, in agreement with the carrier's
  callee-span transport). Guarded by the existing `callees_*` suite (all green).
- **Item 4 (Minor) — LANDED.** `crates/cranelisp-typecheck/CLAUDE.md`
  §"`Def.callees` completeness contract" updated: `record_user_fn_ref` →
  `record_reference_target` (the W0.1 resolve-once consolidation).

## Remaining — item 2 (Minor), DEFERRED to W1

**Self-recursion carve-out over-matches a same-named local.**
`checker.rs::record_reference_target`'s carve-out fires on `current_defn == name`
whenever the name is env-shadowed — including a USER local of the same name
(`(defn f [] (let [f (fn [x] x)] (f 3)))`, or a param named `f`). The Var span
then carries the enclosing fn's storage FQ for what is actually a LOCAL
reference (§1.1 "whichever storage key HIT": nothing hit). **Harmless ONLY
while the backend's local-`variables` check precedes the keyed read** (§1.1
local row). This is a **W1 invariant**, not a W0.b fix: the W1 brief must keep
the backend locals-check BEFORE the `entry_at` keyed read, and MAY additionally
tighten the carve-out to gate on the shadowing binding being the recursion
binding (scope-depth / binding-provenance) rather than merely name-equal.

## Severity
Important (item 1, LANDED); Minor (items 2–4). None gates W1 — see the `/review`
(producer W0.1+W0.1b) SPRINT note for the gating analysis.

## Issue

Four residues found reviewing `635f364b` + `144828d1`:

1. **`builtin_storage_fq` user-scope name-capture (Important).**
   `callees.rs::builtin_storage_fq` resolves the BuiltinFn JIT name (e.g.
   `add-i64`) through USER scope via `def_resolved`, falling back to
   `primitives`. A jit name is not a source-level reference; resolving it in
   user scope can capture a same-named user fn. Reachable shape: a
   prelude-suppressed module with `(import [primitives [+]])` (only `+`) plus
   a local `(defn add-i64 [a b] ...)` (legal — `add-i64` is not in scope, so
   §8.6.4 does not fire). `(+ 1 2)` short-circuits to
   `BuiltinFn { add-i64 }` (FIXME 0185 static table), but the carrier records
   `{mymod, add-i64}` — the USER fn — while the backend's BuiltinFn arm will
   emit the primitive. Post-W1 a keyed read off that carrier dispatches the
   wrong function on a valid program. Prelude-ON modules are safe (§8.6.4
   def-over-prelude conflict forecloses the collision), so the reach is
   narrow — but the guard is one line.

2. **Self-recursion carve-out over-matches a same-named local (Minor).**
   `checker.rs::record_reference_target`: the carve-out fires on
   `current_defn == name` whenever the name is env-shadowed — including a
   USER local of the same name (`(defn f [] (let [f (fn [x] x)] (f 3)))`, or
   a param named `f`). The Var span then carries the enclosing fn's storage
   FQ for what is actually a LOCAL reference — semantically wrong under §1.1
   ("whichever storage key HIT": nothing hit). Harmless ONLY because the
   design pins the backend's local-`variables` check BEFORE the keyed read
   (§1.1 local row); it is a standing landmine if W1 ever reorders.

3. **AutoCurry plain-arm `callees` edge still caller-module (Minor,
   pre-existing).** `resolved_call_to_fqsymbol`'s AutoCurry no-inner arm
   derives `{current_module, target_name}` — wrong home for an imported curry
   target (the exact class W0.1b fixed on the carrier via callee-span
   transport). Benign today (the correct edge also lands via `user_fn_refs`
   at the callee Var; the wrong-module edge names a nonexistent key), but it
   contradicts `dispatch_target_fq`'s rustdoc claim that "the carrier and the
   `callees` edge agree on the mangled entry's home". A `callees` meaning
   change rides the schema-19 window if fixed this sprint (0472 precedent).

4. **`crates/cranelisp-typecheck/CLAUDE.md` drift (Minor).** The
   §"`Def.callees` completeness contract" section still names
   `checker::record_user_fn_ref`, deleted by W0.1 (`635f364b`); the seam is
   now `record_reference_target` (resolve-once + UserFn projection).

## Proposed resolution

1. In `builtin_storage_fq`, accept the scope probe only when the terminal
   `DefKind` is `Primitive { .. } | PrimitiveExtern` (mirroring
   `resolve_primitive_jit_name`'s own kind gate); else fall through to the
   `primitives` default. Unit pin: prelude-suppressed module + local `add-i64`
   + `(+ 1 2)` ⇒ carrier `primitives/add-i64`.
2. Gate the carve-out on the shadowing binding being the RECURSION binding,
   not merely name-equal (scope-depth or binding-provenance check), or record
   nothing when a nested user binding shadows; at minimum add the landmine
   comment to the W1 brief (backend locals-check MUST precede the keyed read).
3. Fold the plain-arm edge onto the same resolution the carrier uses (the
   span is available in `extract_call_graph_edges`' map iteration — read
   `resolved_targets` at the callee span), or update the rustdoc claim.
4. Reword the CLAUDE.md section to the landed seam names.

## Context

Filed by `/review` (producer W0.1+W0.1b gate review, S110). Items 1–3 are
carrier-precision residue inside the otherwise-verified §1.1.1 completeness
table; none reproduces on the standard corpus, so no failing e2e exists (this
FIXME is the testless-change-request record per METHOD §3.3).
