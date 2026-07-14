---
number: 0590
target: /design
filed_by: /review
filed_at: 2026-07-14
sprint_filed: 109
refers_to: crates/cranelisp-typecheck/src/traits/type_resolve.rs (resolve_trait_type_expr, resolve_type_expr_hkt, resolve_type_expr_hkt_impl) + src/form.rs (check_type_expr + collect_type_var_ids) vs resolve.rs::resolve_type_expr
status: open
---

# Resolver-mirror family: four parallel TypeExpr resolvers each hand-roll the mint-on-miss the canonical resolver just gained

## Severity
Important — P7 (single source of truth). This is the sprint's named recurring
class (`resolver-mirror` vocab minted at P5-S2); the W6 change makes the
canonical resolver capable of subsuming the mirrors, so the convergence lever
now exists.

## Issue

e401cce9 added `mint_free_var: Option<&dyn Fn() -> TypeId>` to the canonical
`resolve::resolve_type_expr` — mint a fresh quantified var on a `TypeVar`
var_map miss. But the crate already carries FOUR other resolvers that
independently implement exactly this behaviour (mint-on-miss + record for
co-reference), each with its own `TypeVar`/`FnType`/`Applied` recursion:

1. `traits/type_resolve.rs::resolve_trait_type_expr` — trait method sigs;
   mints unconditionally (`fresh_var` + insert on miss).
2. `traits/type_resolve.rs::resolve_type_expr_hkt` — HKT trait sigs; mints
   into `type_var_map` on double miss. Its `Named` arm never errors at all —
   an unknown name fabricates `Type::ADT` with an EMPTY module path.
3. `traits/type_resolve.rs::resolve_type_expr_hkt_impl` — HKT impl methods;
   same mint-on-miss; same never-error `Named` fabrication.
4. `form.rs::check_type_expr` (platform sigs, FIXME 0231/0233) — pre-walks
   with `collect_type_var_ids` to pre-mint every free var, then resolves via
   the mint=None path. A pre-walk allocator and a mint-on-miss allocator are
   two mechanisms for one concept; if `collect_type_var_ids`'s walk ever
   diverges from `resolve_type_expr`'s traversal (e.g. a future TypeExpr
   variant), they disagree silently.

Two resolvers disagreeing on one concept is the defect class that recurred
3× this sprint. None of these were introduced by e401cce9 — but e401cce9 is
the moment the canonical resolver became ABLE to express what the mirrors
hand-roll, and the change's own rustdoc is already wrong about them:

**Doc inaccuracy (fix with the convergence or sooner, `/dev`):** the new
rustdoc on `resolve::resolve_type_expr` and
`checker.rs::resolve_type_expr_in_module` names "trait-method sig" as a
`mint_free_var: None` context whose free-var miss "still errors". Trait
method sigs do NOT route through this function — they route through
`resolve_trait_type_expr`, which MINTS unconditionally. The described
over-broadening guard for trait sigs does not exist in shipped routing.

## Proposed resolution

`/design` (typecheck) produces a convergence note:

- **Immediate, mechanical**: `form.rs::check_type_expr` drops
  `collect_type_var_ids` and calls `resolve_annotation_type_expr_in_module`
  (env is already in hand; the pre-walk exists only because the old resolver
  could not mint).
- **Designed**: fold `resolve_trait_type_expr` / `_hkt` / `_hkt_impl` onto the
  canonical resolver — needs a shape for Self-substitution and HKT con-var
  interception (likely a pre-pass or an extended terminal-resolver closure),
  and a ruling on the `_hkt`/`_hkt_impl` never-error `Named` arms (unknown
  types silently fabricated — over-broad, likely its own latent defect).
- `/dev` corrects the resolve.rs/checker.rs rustdoc claim about trait-method
  sigs regardless of when convergence lands.

## Context

Found by `/review` on e401cce9 (S109 W6) applying the mirror-class lens (is
there a SECOND resolver of annotation/type-expr TypeVars?). Answer: four.
Escalate to `/arch` if `/design` judges the convergence to need a cross-crate
or decision-log treatment (recurrence rule per
memory/feedback_review_root_cause_and_duplication.md).
