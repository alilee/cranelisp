---
number: 0752
target: /dev
filed_by: /review (cranelisp-backend, S115 W3)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: crates/cranelisp-backend/src/compiler/fn_compiler.rs::{arg_is_inplace_cow_on:1613, return_cow_source_in_scope:2456}; crates/cranelisp-backend/src/compiler/vec_codegen.rs::is_cow_vec_op; crates/cranelisp-backend/CLAUDE.md §"RC-emission gates that are ONE predicate"
status: open
---

# 0693 consolidated ONE of three consumers of "is this a COW site" — the two survivors are still name-keyed, and one of them FEEDS the consolidated predicate

## Severity
Important — the P24 "resolve once" claim recorded in `CLAUDE.md` and in the
change-set's rustdoc is not true of the crate as it now stands.

## Issue

0693's cure keyed COW-site identity on the RESOLUTION CARRIER
(`ResolvedCall::BuiltinFn`) via `vec_codegen::cow_site_retain_verdict` /
`is_cow_vec_op`. Two other sites ask the same question and still answer it from
the callee's written spelling:

1. **`fn_compiler.rs:1620` — `arg_is_inplace_cow_on`**
   (`if !matches!(c.as_ref(), "vec-set" | "vec-push")`), the predicate behind
   `param_flush_exempts_inplace_cow` — i.e. the 0691/0695 in-place-COW exemption
   that the new `tco_owned_params` promotion now interacts with directly.
2. **`fn_compiler.rs:2466` — `return_cow_source_in_scope`**
   (same `matches!`), the producer of `FnCompiler::return_cow_source`.

Survivor 2 is the sharper problem: `return_cow_source` is an INPUT to the
consolidated predicate (`cow_source_is_borrowed(source, return_cow_source, …)`).
So the exact latent channel 0693 named — a user fn literally spelled `vec-set`
under `PreludeVariant::None` — still perturbs the consolidated gate, just one
level upstream. Its rustdoc defends the spelling read ("the vec-query primitive
names are canonical and never aliased at a value site"), which is the claim 0693
falsified for the sibling seam; the two rationales are now inconsistent.

Polarity: both survivors' false-positive direction is a suppressed dec (leak),
not a spurious dec, so neither is unsafe today. That is why this is Important
and not a Blocker — but the durable point is the recurring class, not this
instance: three consumers of one identity question, one converted.

A third, milder duplicate: `vec_codegen.rs::cow_source_needs_toggle_off_count`
re-expresses "a `Var` source that is not the return-COW-source" inline rather
than sharing the `cow_source_is_borrowed` body under the toggle inversion.

## Proposed resolution

`/dev`(backend): route survivors 1 and 2 through `is_cow_vec_op` at minimum, and
through the `ResolvedCall::BuiltinFn` carrier where the node carries one (both
sites match on an `Apply`, so the carrier is in hand). Factor the "Var source
that is not the return-COW-source" test so `cow_source_needs_toggle_off_count`
and `cow_source_is_borrowed` share it. Then update
`crates/cranelisp-backend/CLAUDE.md` §"RC-emission gates that are ONE predicate"
— as written it reads as if the consolidation is complete.

If any survivor is deliberately kept name-keyed, say so at the site with the
reason the carrier is unavailable there, rather than with the
"names are canonical" claim.

## Context

`/review`(backend), S115 W3 recurring-class check (mirrors / name-keyed identity
/ third-instance duplication). Escalate to `/arch` if a third sprint finds a new
instance of this class — that would be the recurrence threshold.
