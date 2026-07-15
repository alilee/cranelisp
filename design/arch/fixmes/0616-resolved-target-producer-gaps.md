---
number: 0616
target: /dev
filed_by: /review
filed_at: 2026-07-15
sprint_filed: 110
refers_to: crates/cranelisp-typecheck/src/checker.rs::record_resolved_target (S110 W0, 41fab350)
status: open
---

# 0583 producer records only a subset of the resolutions `lookup` performs — three kinds silently carrier-less

## Severity
Blocker (gates W1 — each leg becomes a hard `CodegenError` on a VALID program the
moment W1 flips the call seam onto the carrier; `backend-keyed-consumer.md` §1.2
forbids any fallback that would mask it).

## Issue

W0 (`41fab350`) landed the `resolved_targets` writer at ONE of the §1.1 chokepoint
groups (`infer_var`, Var-span). The design pins THREE groups
(`design/arch/backend-keyed-consumer.md` §1.1 "Producer chokepoints"), and the
landed writer re-resolves through a probe (`resolved_target_fq` → `scope_resolve`)
that is NARROWER than the resolution `lookup` actually performed. Three concrete
reference kinds end up with `resolved_target: None` on the mono view:

1. **Dispatch-leg selections (Apply-span) — no writer exists at all.** Every
   `resolved_calls` writeback seam (`traits/monomorphise.rs:384/806/941`,
   `infer.rs:655/845/912`, `program/register.rs:510`, `program/mono_collect.rs:267`)
   writes only `ResolvedCall`; nothing ever inserts an Apply-span key, so
   `MonoExpr::Apply.resolved_target` is structurally always `None`. A trait-method
   / sig-dispatch / auto-curry call is compiled today by resolving the ResolvedCall
   *mangled name* through `resolve_got_target` (apply.rs S7); post-W1 the keyed
   read needs the SELECTED entry's module-bearing FQ at the Apply span (§1.1 table,
   "Trait-method / sig-dispatch leg") — `ResolvedCall` has no module leg by design.
   Failure scenario: `(+ 1 2)` (operators are trait methods) hard-fails at W1.

2. **Self-recursive references — filtered by the env-shadow gate.**
   `program/body.rs:652` binds the defn's own name as a LOCAL for recursion
   typing; `checker.rs:1403`'s `state.env.lookup(name)` gate skips it. That
   disposition is CORRECT for the `callees` feed (self-edges unwanted,
   documented) and WRONG for the carrier: the backend compiles a non-tail
   self-call through `compile_direct_call` → `resolve_got_target` (the fn's own
   name is not a backend local). Failure scenario: `(defn fact [n] (if ... (fact
   (- n 1))))` — every recursive function hard-fails at W1.

3. **Dotted `Type.member` references resolved via the dotted core.** `lookup`
   resolves `Maybe.Some` / `Box.v` through `resolve_dotted_member_entry`
   (head type in bare scope → canonical-key probe in the type's HOME module);
   `record_resolved_target` re-probes `scope_resolve("Maybe.Some")` in the
   CURRENT scope, which only hits when a literal `Type.Ctor` key exists there
   (home module, or a member-glob import — `src/imports.rs:collect_member_glob`
   installs canonical edges). A specific type-only import + dotted member
   reference type-checks via the dotted core but records no carrier. Failure
   scenario: `(import [m [Maybe]])` then `(Maybe.Some 3)` — hard-fails at W1;
   dotted is the spec's always-works spelling (S109).

## Proposed resolution

Apply the design's own binding property — "recording happens where resolution
happens" (§1.1) — instead of a parallel re-probe:

- capture the FQ at the seams that actually resolve: the dispatch-selection
  writeback seams insert the selected entry's module-bearing FQ at the Apply
  span alongside their `resolved_calls` insert; the dotted-member leg records
  `(fqtn.module, member_key)` inside the `lookup` dotted arm (the identity is
  already in hand at `checker.rs:1581`);
- give the self-reference a carve-out (the recursion local is not a backend
  local; record the enclosing defn's own storage FQ), explicitly diverging from
  `record_user_fn_ref`'s self-edge skip — the two feeds' gates are semantically
  different;
- land in the SAME schema-19 window (value-only change, the 0472 two-commits-
  one-window precedent) BEFORE W1; extend the KC unit rows with one pin per leg
  (recursive fn, trait-dispatch call, type-only-import dotted ctor).

Consolidation opportunity (fold in or file to follow): `resolved_target_fq`/
`def_terminal_fq` duplicates `resolve_user_fn_ref_fq`/`user_fn_fq_of` verbatim
except the kind filter, and `infer_var` now resolves the same name up to three
times (`lookup`, `record_user_fn_ref`, `record_resolved_target`) — under the
"Resolve once" initiative itself (Principles 7/24). Resolve once, record
`resolved_targets`, derive the `callees` edge as a `UserFn`-filtered projection.

## Context

Found by `/review` (W0 change-set review, S110). The commit/SPRINT note claims
"EVERY table-resolved reference kind" — true for kinds reached at `infer_var`'s
Var position, but kind coverage at one chokepoint is not chokepoint coverage;
none of the three legs was declared deferred. W1 is backend-internal by plan
(§4/§8: "W1–W3: no types/public-API/cache impact"), so it cannot absorb these
typecheck-side writers mid-wave.
