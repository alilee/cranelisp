---
number: 0595
target: /dev
filed_by: /review
filed_at: 2026-07-14
sprint_filed: 109
refers_to: crates/cranelisp-typecheck/src/unify.rs::unify_with_rigid (TyConApp arms, lines ~109/~131) + program.rs::check_defn_body / infer.rs error-path teardown
status: open
---

# Rigid-model hardening: TyConApp head binds bypass `unify_var`; body-state teardown is Ok-path-only

## Severity
Suggestion (two Principle-18 hardening items; neither is live-reachable today
— both verified against current construction sites and error flow).

## Issue

Two places where the rigid model's invariants hold by convention rather than
by structure (Principle 18: enforce invariants structurally; Principle 20):

1. **`unify_with_rigid`'s TyConApp arms call `bind_var` directly** (head →
   bare-ADT at ~:109, head → head at ~:131), bypassing the rigid guard, on
   the comment's claim "HKT constructor variables are never written skolems".
   True today: `Type::TyConApp` is constructed ONLY in
   `traits/type_resolve.rs` (trait-sig resolution — those ids are never in
   `rigid_vars`), and the canonical annotation resolver cannot produce a
   lowercase applied head (`:(f a)` → `TypeNotFound`). But
   `cranelisp_types::apply` REWRITES a head id along the substitution
   (`subst[f] = Var(g)` ⇒ `TyConApp(g, …)`), and `unify_var`'s rigid arm
   binds flexible vars TO rigid ids — so a kind-confused sig (a var used both
   as head and in plain position; no kind checker prevents it) could smuggle
   a rigid id into head position, after which :109/:131 bind it silently
   (acquire). Routing both head-binds through `unify_var` closes the
   convention gap for the cost of two call edits.

2. **Ok-path-only teardown**: `check_defn_body` (program.rs ~3311→3335),
   `infer_annotate`, and `infer_lambda` install `rigid_vars` /
   `written_var_scope` and restore them only past the `?`s; an inference
   error leaves the state polluted. Benign today — verified that every Pass-2
   error aborts the whole `check_forms` call and `CheckState` is
   function-local (form.rs:185), so leaked state dies with the aborted check
   — but `traits/impl_check.rs::check_defn_body_with_types` already does the
   closure-capture save/restore correctly, and the asymmetry is a trap for
   any future continue-after-form-error mode. Match the impl_check
   discipline (closure or RAII guard) at the other three sites.

## Proposed resolution

`/dev` (typecheck), opportunistically or riding the 0590 S110 convergence:
(1) route the two TyConApp head binds through `unify_var`; (2) unify the
save/restore discipline. A `debug_assert!(!rigid.contains(&f_id))` at the
TyConApp arms would be an acceptable minimal alternative to (1).

## Context

Filed by `/review` on b2bfb760 (S109 W6.2) while adversarially searching for
unify paths that bypass the rigid guard (dispatch priority 1). These are the
only two bypass-shaped residues found; all other unification routes through
`TypeCheckEnv::unify` → `unify_with_rigid` → `unify_var`, and instantiation
sites (`scheme.rs`, `checker.rs:1973`, `monomorphise.rs`) only insert into
local instantiation maps keyed by scheme-owned ids.
